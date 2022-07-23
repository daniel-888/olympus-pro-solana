use anchor_lang::prelude::*;
use anchor_lang::AccountsClose;
use anchor_spl::token::{
    self, CloseAccount, Mint, MintTo, SetAuthority, Token, TokenAccount, Transfer,
};
use rust_decimal::prelude::*;
use rust_decimal_macros::dec;
use spl_token::instruction::AuthorityType;
use std::convert::TryInto;

declare_id!("61ZYzDJWf1KXdU6aEm6JEyE1z5Vjp3KHRSiKw9GAZaXp");

const OLYMPUS_AUTHORITY_PDA_SEED: &[u8] = b"olympusAuthority";

#[program]
pub mod olympuspro_sol {
    use super::*;

    /// Initialize the OlympusPro instructions so that they are ready to create custom treasuries.
    ///
    /// # Arguments
    /// * `ctx` - The calling context
    pub fn initialize(ctx: Context<Initialize>) -> Result<()> {
        let data = &mut ctx.accounts.olympus_data;
        data.olympus_dao = ctx.accounts.olympus_dao.key();
        Ok(())
    }

    /// Create a new treasury.
    ///
    /// The treasury holds payout tokens to be redeemed.
    ///
    /// # Arguments
    /// * `ctx` - The calling context
    pub fn create_treasury(ctx: Context<CreateTreasury>) -> Result<()> {
        let treasury = &mut ctx.accounts.treasury.load_init()?;
        treasury.payout_token = ctx.accounts.payout_account.key();
        treasury.payout_mint = ctx.accounts.payout_mint.key();
        treasury.authority = ctx.accounts.authority.key();
        treasury.payout_account_bump = *ctx.bumps.get("payout_account").unwrap();
        treasury.dao_payout_account_bump = *ctx.bumps.get("dao_payout_account").unwrap();

        let (token_authority, _token_authority_bump) =
            get_token_authority(ctx.accounts.treasury.key());

        // Take over the authority for the payout account so only the program can withdraw
        token::set_authority(
            ctx.accounts.into_set_payout_authority_context(),
            AuthorityType::AccountOwner,
            Some(token_authority),
        )?;

        Ok(())
    }

    /// Withdraw tokens from the treasury.
    ///
    /// No limit is required because the tokens in the account are fully owned
    /// by the partner. Fees are collected into Olympus' account and bonds cannot
    /// be created without sufficient tokens present. Note that this means
    /// bond creation will fail if there are insufficient payout tokens.
    ///
    ///
    /// # Arguments
    /// `ctx` - The calling context
    /// `amount` - The amount to transfer
    pub fn treasury_withdraw(ctx: Context<TreasuryWithdraw>, amount: u64) -> Result<()> {
        // Get the PDA for the token authority so we can sign
        let (_token_authority, token_authority_bump) =
            get_token_authority(ctx.accounts.treasury.key());
        let treasury_key = ctx.accounts.treasury.key();
        let authority_seeds = &[
            &OLYMPUS_AUTHORITY_PDA_SEED[..],
            &treasury_key.as_ref(),
            &[token_authority_bump],
        ];

        // Sign using the token authority
        token::transfer(
            ctx.accounts
                .into_transfer_context()
                .with_signer(&[&authority_seeds[..]]),
            amount,
        )?;
        Ok(())
    }

    /// Create a new bonder.
    ///
    /// A bonder issues bonds in exchange for principal tokens.
    /// As bonds mature, they can be redeemed for payout tokens.
    ///
    /// The DAO collects a fee as bonds are issued, which can be
    /// tiered based on the number of principal tokens issued.
    ///
    /// The fee can also be collected either from payout tokens
    /// or principal tokens.
    ///
    /// # Arguments
    /// `ctx` - The calling context
    /// `amount` - The amount to transfer
    /// `fee_in_payout` - Whether or not to collect the fee in payout tokens.
    /// `fee_percent` - An array of fee percentages (in ten-thousands (i.e. 33300 = 3.3%).
    ///                 The first element is the default tier, and the tokens required to
    ///                 move up each tier is specified in the `fee_tiers` parameter.
    /// `fee_tiers` - An array indicating the number of principal tokens required to move up
    ///               each tier.
    pub fn create_bonder(
        ctx: Context<CreateBonder>,
        fee_in_payout: bool,
        fee_percent: [u64; 5],
        fee_tiers: [u64; 4],
    ) -> Result<()> {
        // Set the authority for the principal token account to our PDA,
        // So only the program can withdraw
        let (token_authority, _token_authority_bump) =
            get_token_authority(ctx.accounts.treasury.key());

        token::set_authority(
            ctx.accounts.into_set_principal_authority_context(),
            AuthorityType::AccountOwner,
            Some(token_authority),
        )?;

        // validate that the fee_levels are incrementing
        for i in 1..fee_tiers.len() {
            if fee_tiers[i] < fee_tiers[i - 1] {
                return Err(ErrorCode::FeeLevelsNotIncrementing.into());
            }
        }

        // Set the variables for bonding.
        let bonder = &mut ctx.accounts.bonder.load_init()?;
        bonder.authority = ctx.accounts.authority.key();
        bonder.mint = ctx.accounts.principal_mint.key();
        bonder.treasury = ctx.accounts.treasury.key();
        bonder.principal_bump = *ctx.bumps.get("principal_account").unwrap();
        bonder.dao_principal_account_bump = *ctx.bumps.get("dao_principal_account").unwrap();
        bonder.vesting_term = 0;
        bonder.control_variable = 1;
        bonder.minimum_price = 1;
        bonder.max_debt = u64::MAX;
        bonder.max_payout_percent = 100000; // 100%
        bonder.fee_in_payout = fee_in_payout;
        bonder.fee_percentages = fee_percent;
        bonder.fee_tiers = fee_tiers;
        bonder.last_slot = ctx.accounts.clock.slot;
        bonder.last_time = ctx.accounts.clock.unix_timestamp;
        bonder.bcv_adjust_rate = 0;
        bonder.bcv_adjust_target = 0;
        bonder.bcv_adjust_last = ctx.accounts.clock.unix_timestamp;

        Ok(())
    }

    /// Configure the bonder settings.
    ///
    /// NB: anchor doesn't support tuple enums, which would be a nicer way of implementing this.
    ///
    /// # Arguments
    /// `ctx` - The calling context
    /// `settings` - The new settings to set.
    pub fn bonder_setting(ctx: Context<BonderSetting>, settings: BonderSettings) -> Result<()> {
        let bonder = &mut ctx.accounts.bonder.load_mut()?;
        settings
            .bcv_adjust_target
            .map(|x| bonder.bcv_adjust_target = x);
        settings.max_debt.map(|x| bonder.max_debt = x);
        settings.vesting.map(|x| bonder.vesting_term = x);
        settings.bcv_adjust_rate.map(|x| bonder.bcv_adjust_rate = x);
        settings
            .bcv_adjust_buffer
            .map(|x| bonder.bcv_adjust_buffer = x);
        Ok(())
    }

    /// Deposit the principal token and issue a new bond from the bonder.
    ///
    /// If the bonder has enough capacity `maxDebt < totalDebt`, and the price
    /// of the bond is less than `maxPrice`, a new bond is issued with the
    /// terms specified by the bonder.
    ///
    /// # Arguments
    /// * `amount` - The number of principal tokens to deposit
    /// * `max_price` - The maximum premium/discount to pay in terms of principal/payout.
    pub fn bonder_deposit(ctx: Context<BonderDeposit>, amount: u64, max_price: u64) -> Result<()> {
        let bonder = &mut ctx.accounts.bonder.load_mut()?;

        // first, adjust any BCV variables, as necessary
        if bonder.bcv_adjust_rate != 0
        // we use wall clock time to control the the adjustment frequency.
        // this is ok *if* the clock is monotonically increasing. we don't 
        // require precision time, and the frequncy of adjustment doesn't 
        // need more than tens of second of precision.
            && bonder.bcv_adjust_last != ctx.accounts.clock.unix_timestamp
        {
            let adjusted_bcv = get_adjusted_bcv(
                bonder.control_variable,
                bonder.bcv_adjust_rate,
                bonder.bcv_adjust_target,
                bonder.bcv_adjust_buffer,
                bonder.bcv_adjust_last,
                ctx.accounts.clock.unix_timestamp,
            )?;

            if adjusted_bcv != bonder.control_variable {
                bonder.control_variable = adjusted_bcv;
                bonder.bcv_adjust_last = ctx.accounts.clock.unix_timestamp;

                if adjusted_bcv == bonder.bcv_adjust_target {
                    bonder.bcv_adjust_rate = 0;
                }
            }
        }

        // To calculate the bond price, first we calculate the "value" of the principal token.
        let principal_value = get_principal_value(
            amount,
            ctx.accounts.payout_mint.decimals,
            ctx.accounts.principal_mint.decimals,
        )?;

        // Calculate the debt ratio.
        let debt_ratio = get_debt_ratio(bonder.total_debt, ctx.accounts.payout_mint.supply)?;

        // Then calculate the bond price.
        let bond_price = get_bond_price(bonder.control_variable, debt_ratio, bonder.minimum_price)?;

        // Error out if the bond_price is > max_price
        if bond_price > max_price {
            return Err(ErrorCode::BondPriceOverLimitPrice.into());
        }

        // The bond price must be at least 1 or the minimum price
        if bond_price < 1 || bond_price < bonder.minimum_price {
            return Err(ErrorCode::BondPriceUnderMinimum.into());
        }

        // decay by the decay rate (once per slot)
        // we use the slot to protect against non-monotonic time
        if bonder.last_slot != ctx.accounts.clock.slot {
            // we simply decay by dividing the time
            let time_since_last = ctx
                .accounts
                .clock
                .unix_timestamp
                .checked_sub(bonder.last_time)
                .ok_or(ErrorCode::MathOverflow)?
                .to_u64()
                .ok_or(ErrorCode::BackwardsTime)?;
            let time_slice = if bonder.vesting_term == 0 {
                0
            } else {
                time_since_last
                    .checked_div(bonder.vesting_term)
                    .ok_or(ErrorCode::MathOverflow)?
            };
            let decay = bonder
                .total_debt
                .checked_mul(time_slice)
                .ok_or(ErrorCode::MathOverflow)?;

            if decay > bonder.total_debt {
                bonder.total_debt = 0;
            } else {
                bonder.total_debt = bonder
                    .total_debt
                    .checked_sub(decay)
                    .ok_or(ErrorCode::MathOverflow)?;
            }

            // update the last slot/time values.
            bonder.last_slot = ctx.accounts.clock.slot;
            bonder.last_time = ctx.accounts.clock.unix_timestamp;
        }

        // Increase our debt by the adjusted principal value
        bonder.total_debt = bonder
            .total_debt
            .checked_add(principal_value)
            .ok_or(ErrorCode::MathOverflow)?;

        // Calculate the payout amount
        let mut payout = get_payout(amount, bond_price)?;

        // Make sure we don't exceed the maximum bond size
        if payout > get_max_payout(bonder.max_payout_percent, ctx.accounts.payout_mint.supply)? {
            return Err(ErrorCode::BondExceedsMaxPayout.into());
        }

        // Mutable principal, because we might have to subtract the fee.
        let mut principal = amount;

        // increment the bonded, with any amount taken for fees removed.
        bonder.total_bonded = bonder
            .total_bonded
            .checked_add(amount)
            .ok_or(ErrorCode::MathOverflow)?;

        // Make sure total debt is equal to or less than max debt.
        if bonder.total_debt > bonder.max_debt {
            return Err(ErrorCode::MaxDebtExceeded.into());
        }

        // Get the PDA for the token authority so we can sign
        let (_token_authority, token_authority_bump) =
            get_token_authority(ctx.accounts.treasury.key());
        let treasury_key = ctx.accounts.treasury.key();
        let authority_seeds = &[
            &OLYMPUS_AUTHORITY_PDA_SEED[..],
            &treasury_key.as_ref(),
            &[token_authority_bump],
        ];

        // calculate olympus taker amount, vesting based on policy
        if bonder.fee_in_payout {
            // take the fee from the payout token.
            let fee = get_bond_fee(
                bonder.fee_percentages,
                bonder.fee_tiers,
                bonder.total_bonded,
                payout,
            )?;

            payout = payout.checked_sub(fee).ok_or(ErrorCode::MathOverflow)?;

            // transfer the fee to olympus dao account
            // the transfer will error and prevent the bond from being
            // created if there are insufficient payout tokens.
            if fee > 0 {
                token::transfer(
                    ctx.accounts
                        .into_transfer_to_payout_dao_context()
                        .with_signer(&[&authority_seeds[..]]),
                    fee,
                )?;
            }
        } else {
            // take the fee from the principal token
            let fee = get_bond_fee(
                bonder.fee_percentages,
                bonder.fee_tiers,
                bonder.total_bonded,
                principal,
            )?;

            principal = principal.checked_sub(fee).ok_or(ErrorCode::MathOverflow)?;

            // transfer the fee to olympus dao account
            if fee > 0 {
                token::transfer(ctx.accounts.into_transfer_to_principal_dao_context(), fee)?;
            }
        }

        token::transfer(ctx.accounts.into_transfer_from_user_context(), principal)?;

        let mut bond = ctx.accounts.bond.load_init()?;
        bond.nft_mint = ctx.accounts.nft_mint.key();
        bond.bonder = ctx.accounts.bonder.key();
        bond.vesting_term = bonder.vesting_term;
        bond.vesting_start = ctx.accounts.clock.unix_timestamp;
        bond.bond_account_bump = *ctx.bumps.get("bond_account").unwrap();

        // "bond" the payout by transferring it into the bond account
        token::transfer(
            ctx.accounts
                .into_transfer_to_bond_context()
                .with_signer(&[&authority_seeds[..]]),
            payout,
        )?;

        // handle the NFT generation
        token::mint_to(
            ctx.accounts
                .into_mint_nft_context()
                .with_signer(&[&authority_seeds[..]]),
            1,
        )?;

        // Disable further minting
        token::set_authority(
            ctx.accounts
                .into_disable_mint_authority_context()
                .with_signer(&[&authority_seeds[..]]),
            AuthorityType::MintTokens,
            None,
        )?;

        Ok(())
    }

    /// Redeem a bond.
    ///
    /// This instruction deposits the payout in the given `token_account` account.
    /// If the vesting term for the bond has not yet elapsed, a partial payout is given.
    /// If the bond is completely paid out, then the bond account is closed.
    ///
    /// # Arguments
    /// * `ctx` - The calling context
    pub fn bond_redeem(ctx: Context<BondRedeem>) -> Result<()> {
        let (_token_authority, token_authority_bump) =
            get_token_authority(ctx.accounts.treasury.key());
        let treasury_key = ctx.accounts.treasury.key();
        let authority_seeds = &[
            &OLYMPUS_AUTHORITY_PDA_SEED[..],
            &treasury_key.as_ref(),
            &[token_authority_bump],
        ];

        // Scope to keep the mutable borrow so we can close the account.
        {
            let bond = &mut ctx.accounts.bond.load_mut()?;
            // calculate vesting percentage
            let current_time = ctx.accounts.clock.unix_timestamp;
            let elapsed_time = current_time
                .checked_sub(bond.vesting_start)
                .ok_or(ErrorCode::MathOverflow)?;
            // use fp here for simplicity.
            let percentage = if bond.vesting_term > 0 {
                Decimal::from_i64(elapsed_time)
                    .ok_or(ErrorCode::MathOverflow)?
                    .checked_div(
                        Decimal::from_u64(bond.vesting_term).ok_or(ErrorCode::MathOverflow)?,
                    )
                    .ok_or(ErrorCode::MathOverflow)?
            } else {
                dec!(1.0)
            };
            // calculate the payout
            let payout = if percentage >= dec!(1.0) {
                ctx.accounts.bond_account.amount
            } else {
                percentage
                    .checked_mul(ctx.accounts.bond_account.amount.into())
                    .ok_or(ErrorCode::MathOverflow)?
                    .round()
                    .to_u64()
                    .ok_or(ErrorCode::MathOverflow)?
            };

            // transfer the payout token
            token::transfer(
                ctx.accounts
                    .into_transfer_context()
                    .with_signer(&[&authority_seeds[..]]),
                payout,
            )?;

            // reload the account the reflect the new balance
            ctx.accounts.bond_account.reload()?;

            // update the vesting terms if something still needs to be paid out
            if ctx.accounts.bond_account.amount > 0 {
                bond.vesting_start = current_time;
                bond.vesting_term = bond
                    .vesting_term
                    .checked_sub(elapsed_time.try_into().unwrap())
                    .ok_or(ErrorCode::MathOverflow)?;
            }
        }

        if ctx.accounts.bond_account.amount == 0 {
            // For some reason, the token account needs to be closed *first* otherwise you get an unbalanced error
            token::close_account(
                ctx.accounts
                    .into_close_context()
                    .with_signer(&[&authority_seeds[..]]),
            )?;

            // Close the bond account
            ctx.accounts
                .bond
                .close(ctx.accounts.payer.to_account_info())?;
        }

        Ok(())
    }
}

/// Calculate the debt ratio.
///
/// The debt ratio is expressed as the ratio of debt to the total payout token supply.
///
/// # Arguments
/// `total_debt` - The total amount of debt
/// `payout_token_supply` - The amount of payout tokens currently in circulation
fn get_debt_ratio(total_debt: u64, payout_token_supply: u64) -> Result<Decimal> {
    let decimal_debt = Decimal::from_u64(total_debt).ok_or(ErrorCode::MathOverflow)?;
    let decimal_supply = Decimal::from_u64(payout_token_supply).ok_or(ErrorCode::MathOverflow)?;
    if decimal_supply.is_zero() {
        return Ok(Decimal::ZERO);
    }
    Ok(decimal_debt
        .checked_div(decimal_supply)
        .ok_or(ErrorCode::MathOverflow)?)
}

mod debt_ratio_tests {
    #[allow(unused)]
    use super::*; // allow unused necessary because cfg(test) doesn't work in anchor (yet)

    #[test]
    fn debt_ratio_is_zero_if_supply_is_zero() {
        assert_eq!(get_debt_ratio(0, 0).unwrap(), Decimal::ZERO);
    }

    #[test]
    fn debt_ratio_is_one_if_supply_and_debt_are_equal() {
        assert_eq!(get_debt_ratio(100, 100).unwrap(), Decimal::ONE);
    }
}

/// Calculate the bond price, expressed in terms of principal tokens for a single payout token
///
/// The bond price is expressed as the bond control variable (BCV) * debt ratio.
/// Fully expanded, we can express bond price as:
/// $$ bond_price = bond_control_variable \times \frac{debt}{payout_token_supply} $$
///
/// # Arguments
/// `bond_control_variable` - The control variable for bonding
/// `debt_ratio` - The ratio of principal to payout debt, calculated by calling `get_debt_ratio`. Should be positive.
/// `minimum_price` - The minimum price for the bond.
fn get_bond_price(
    bond_control_variable: u64,
    debt_ratio: Decimal,
    minimum_price: u64,
) -> Result<u64> {
    let bcv_decimal = Decimal::from_u64(bond_control_variable).ok_or(ErrorCode::MathOverflow)?;
    let price = bcv_decimal
        .checked_mul(debt_ratio)
        .ok_or(ErrorCode::MathOverflow)?;
    let rounded_price = price.round().to_u64().ok_or(ErrorCode::MathOverflow)?;
    if rounded_price > minimum_price {
        Ok(rounded_price)
    } else {
        Ok(minimum_price)
    }
}

mod get_bond_price_tests {
    #[allow(unused)]
    use super::*; // allow unused necessary because cfg(test) doesn't work in anchor (yet)

    #[test]
    fn negative_debt_ratio_results_in_error() {
        assert!(get_bond_price(1, dec!(-1), 1).is_err());
    }

    #[test]
    fn price_floor_is_hit() {
        assert_eq!(get_bond_price(1, dec!(1), 1000).unwrap(), 1000);
    }
}

/// Get the token authority.
///
/// Each treasury has its own token authority, which is a combination of the
/// `OLYMPUS_AUTHORITY_PDA_SEED` and the `treasury_pubkey`.
///
/// # Arguments
/// `treasury_pubkey` - The pubkey of the treasury
fn get_token_authority(treasury_pubkey: Pubkey) -> (Pubkey, u8) {
    let (token_authority, token_authority_bump) = Pubkey::find_program_address(
        &[OLYMPUS_AUTHORITY_PDA_SEED, treasury_pubkey.as_ref()],
        &id(),
    );
    (token_authority, token_authority_bump)
}

/// Get the fee (to go to the DAO) for the bond.
///
/// The fee can be tiered (currently, max 5) based on the total amount of principal
/// tokens bonded.
///
/// # Arguments
/// `fee_percentages` - An array of percentages, in ten-thousands (i.e. 33300 = 3.33%) The first element is the default tier, and every element after
///                     that is the fee percentage used as the `principal_bonded` exceeds the `fee_tier`.
/// `fee_tiers` - An array of fee tiers, in terms of principal tokens bonded.
/// `total_bonded` - The total number of principal tokens bonded.
/// `base_amount` - The "base" amount to calculate the fee for.
fn get_bond_fee(
    fee_percentages: [u64; 5],
    fee_tiers: [u64; 4],
    total_bonded: u64,
    base_amount: u64,
) -> Result<u64> {
    let tier = get_bond_fee_tier(fee_tiers, total_bonded);
    let percent = Decimal::from_u64(fee_percentages[tier])
        .ok_or(ErrorCode::MathOverflow)?
        .checked_div(dec!(1000000))
        .ok_or(ErrorCode::MathOverflow)?;
    if percent >= Decimal::ONE {
        return Ok(base_amount);
    }
    Ok(percent
        .checked_mul(base_amount.into())
        .ok_or(ErrorCode::MathOverflow)?
        .round()
        .to_u64()
        .ok_or(ErrorCode::MathOverflow)?)
}

mod get_bond_fee_tests {
    #[allow(unused)]
    use super::*; // allow unused necessary because cfg(test) doesn't work in anchor (yet)

    #[test]
    fn zero_percent_fee_results_in_zero_fee() {
        assert_eq!(
            get_bond_fee([0, 0, 0, 0, 0], [0, 0, 0, 0], 0, 0).unwrap(),
            0
        );
    }

    #[test]
    fn tier_one_fee_is_selected() {
        assert_eq!(
            get_bond_fee([0, 33300, 0, 0, 0], [100, 200, 300, 400], 100, 100).unwrap(),
            3
        );
    }

    #[test]
    fn tier_zero_fee_is_selected() {
        assert_eq!(
            get_bond_fee([666000, 33300, 0, 0, 0], [100, 200, 300, 400], 0, 100).unwrap(),
            67
        );
    }

    #[test]
    fn fee_is_not_more_than_base_amount() {
        assert_eq!(
            get_bond_fee([66600000, 33300, 0, 0, 0], [100, 200, 300, 400], 0, 100).unwrap(),
            100
        );
    }

    #[test]
    fn max_tier_fee_is_selected() {
        assert_eq!(
            get_bond_fee(
                [666000, 33300, 0, 0, 100000],
                [100, 200, 300, 400],
                10000,
                10000
            )
            .unwrap(),
            1000
        );
    }
}

/// Get the payout for a given bond price and principal.
///
/// # Arguments
/// `principal_amount` - the amount of principal tokens to be deposited.
/// `bond_price` - The price of the bond, in principal tokens for 1 payout token
fn get_payout(principal_amount: u64, bond_price: u64) -> Result<u64> {
    let decimal_principal_amount =
        Decimal::from_u64(principal_amount).ok_or(ErrorCode::MathOverflow)?;
    let decimal_bond_price = Decimal::from_u64(bond_price).ok_or(ErrorCode::MathOverflow)?;
    Ok(decimal_principal_amount
        .checked_div(decimal_bond_price)
        .ok_or(ErrorCode::MathOverflow)?
        .to_u64()
        .ok_or(ErrorCode::MathOverflow)?)
}

mod get_payout_tests {
    #[allow(unused)]
    use super::*; // allow unused necessary because cfg(test) doesn't work in anchor (yet)

    #[test]
    fn zero_principal_equals_no_payout() {
        assert_eq!(get_payout(0, 1).unwrap(), 0);
    }

    #[test]
    fn zero_bond_price_is_error() {
        assert!(get_payout(100, 0).is_err());
    }
}

/// Get the maximum allowed payout for the given tokens in circulation.
///
/// # Arguments
/// `max_payout_percent` - the maximum payout percent
/// `payout_supply` - the total number of payout tokens in circulation
fn get_max_payout(max_payout_percent: u64, payout_supply: u64) -> Result<u64> {
    if payout_supply == 0 {
        return Ok(0);
    }
    let max_payout_percent_decimal = Decimal::from_u64(max_payout_percent)
        .ok_or(ErrorCode::MathOverflow)?
        .checked_div(dec!(100000))
        .ok_or(ErrorCode::MathOverflow)?;
    if max_payout_percent_decimal > dec!(1.0) {
        return Ok(payout_supply);
    }
    Ok(max_payout_percent_decimal
        .checked_mul(payout_supply.into())
        .ok_or(ErrorCode::MathOverflow)?
        .to_u64()
        .ok_or(ErrorCode::MathOverflow)?)
}

mod get_max_payout_tests {
    #[allow(unused)]
    use super::*; // allow unused necessary because cfg(test) doesn't work in anchor (yet)

    #[test]
    fn max_payout_is_zero_when_supply_is_zero() {
        assert_eq!(get_max_payout(1000000, 0).unwrap(), 0);
    }

    #[test]
    fn large_payout_max_is_supply() {
        assert_eq!(get_max_payout(u64::MAX, 1000000).unwrap(), 1000000);
    }
}

/// Get the bond control variable (BCV) adjustment for a given time frame.
///        
/// # Arguments
/// `control_variable` - The current value of the BCV
/// `bcv_adjust_rate` - How much the BCV should be adjusted, per second
/// `bcv_adjust_target` - The target for the BCV. What the BCV should be at the end of the adjustment.
/// `bcv_adjust_buffer` - The buffer, or the minimum amount of time that must pass before the BCV is adjusted.
/// `bcv_adjust_last` - The last time the BCV was adjusted (UNIX timestamp)
/// `current_time` - The current UNIX timestamp
fn get_adjusted_bcv(
    control_variable: u64,
    bcv_adjust_rate: u64,
    bcv_adjust_target: u64,
    bcv_adjust_buffer: u64,
    bcv_adjust_last: i64,
    current_time: i64,
) -> Result<u64> {
    let mut bcv_adjust_rate_decimal = Decimal::from_u64(bcv_adjust_rate)
        .ok_or(ErrorCode::MathOverflow)?
        .checked_div(dec!(100000))
        .ok_or(ErrorCode::MathOverflow)?;
    // If we need to decrement, make the adjust rate negative
    if bcv_adjust_target < control_variable {
        bcv_adjust_rate_decimal.set_sign_negative(true);
    }

    let time_since_last = current_time
        .checked_sub(bcv_adjust_last)
        .ok_or(ErrorCode::MathOverflow)?;

    // If we went backwards in time, error out
    if time_since_last.is_negative() {
        return Err(ErrorCode::BackwardsTime.into());
    }

    // if the last adjustment is less than the buffer, do nothing
    if time_since_last < bcv_adjust_buffer.try_into().unwrap() {
        return Ok(control_variable);
    }

    let bcv_adjust_amount = bcv_adjust_rate_decimal
        .checked_mul(Decimal::from_i64(time_since_last).ok_or(ErrorCode::MathOverflow)?)
        .ok_or(ErrorCode::MathOverflow)?
        .floor();

    let adjusted = Decimal::from_u64(control_variable)
        .ok_or(ErrorCode::MathOverflow)?
        .checked_add(bcv_adjust_amount)
        .ok_or(ErrorCode::MathOverflow)?
        .to_u64()
        .ok_or(ErrorCode::MathOverflow)?;

    if (bcv_adjust_rate_decimal.is_sign_negative() && adjusted < bcv_adjust_target)
        || (bcv_adjust_rate_decimal.is_sign_positive() && adjusted > bcv_adjust_target)
    {
        return Ok(bcv_adjust_target);
    }

    Ok(adjusted)
}

/// Get the bond fee "tier", given the amount of currently bonded principal
///
/// # Arguments
/// `fee_tiers` - An array representing the number of principal tokens required to reach the next tier.
/// `bonded_principal` - The amount of principal tokens currently bonded.
fn get_bond_fee_tier(fee_tiers: [u64; 4], bonded_principal: u64) -> usize {
    for i in 0..fee_tiers.len() {
        if fee_tiers[i] > bonded_principal {
            return i;
        }
    }
    if fee_tiers[fee_tiers.len() - 1] == 0 {
        0
    } else {
        fee_tiers.len()
    }
}

mod get_bond_fee_tier_tests {
    #[allow(unused)]
    use super::*; // allow unused necessary because cfg(test) doesn't work in anchor (yet)

    #[test]
    fn zero_principal_is_fee_tier_0() {
        assert_eq!(get_bond_fee_tier([1, 2, 3, 4], 0), 0);
    }

    #[test]
    fn no_tiers_is_tier_0() {
        assert_eq!(get_bond_fee_tier([0, 0, 0, 0], 0), 0);
    }

    #[test]
    fn principal_is_fee_tier_1() {
        assert_eq!(get_bond_fee_tier([1, 2, 3, 4], 1), 1);
    }

    #[test]
    fn principal_is_fee_tier_1_100s() {
        assert_eq!(get_bond_fee_tier([100, 200, 300, 400], 101), 1);
    }

    #[test]
    fn principal_is_fee_tier_3() {
        assert_eq!(get_bond_fee_tier([1, 2, 3, 4], 3), 3);
    }

    #[test]
    fn max_principal_is_fee_tier_4() {
        assert_eq!(get_bond_fee_tier([1, 2, 3, 4], u64::MAX), 4);
    }
}

/// Get the value of the principal tokens, accounting for differences in decimal
///
/// # Arguments
/// `amount` - The value of principal tokens to convert
/// `payout_mint_decimals` - The decimals of the payout mint
/// `principal_mint_decimals` - The decimals of the principal mint
fn get_principal_value(
    amount: u64,
    payout_mint_decimals: u8,
    principal_mint_decimals: u8,
) -> Result<u64> {
    Ok(amount
        .checked_mul(
            u64::pow(10, payout_mint_decimals.into())
                .checked_div(u64::pow(10, principal_mint_decimals.into()))
                .ok_or(ErrorCode::MathOverflow)?,
        )
        .ok_or(ErrorCode::MathOverflow)?)
}

#[derive(Accounts)]
pub struct Initialize<'info> {
    #[account(init, seeds=[b"olympus".as_ref()], bump, payer = payer)]
    pub olympus_data: Account<'info, OlympusData>,
    #[account(mut)]
    pub olympus_dao: Signer<'info>,
    pub system_program: Program<'info, System>,
    #[account(mut)]
    pub payer: Signer<'info>,
}

#[derive(Accounts)]
pub struct CreateTreasury<'info> {
    #[account(seeds=[b"olympus".as_ref()], bump, has_one = olympus_dao)]
    pub olympus_data: Account<'info, OlympusData>,
    #[account(mut)]
    pub olympus_dao: Signer<'info>,
    /// CHECK: The authority is a partner account set by the olympus DAO, which is a required signer.
    pub authority: UncheckedAccount<'info>,
    #[account(init, seeds=[b"treasury".as_ref(), payout_mint.key().as_ref(), authority.key().as_ref()], bump, payer = payer)]
    pub treasury: AccountLoader<'info, Treasury>,
    pub payout_mint: Account<'info, Mint>,
    #[account(
        init,
        seeds = [b"account".as_ref(), treasury.key().as_ref(), payout_mint.key().as_ref()],
        bump,
        payer = payer,
        token::mint = payout_mint,
        token::authority = olympus_dao
    )]
    pub payout_account: Account<'info, TokenAccount>,
    #[account(init_if_needed,
        seeds = [b"daoAccount".as_ref(), payout_mint.key().as_ref()],
        bump,
        payer = payer,
        token::mint = payout_mint,
        token::authority = olympus_dao
    )]
    pub dao_payout_account: Account<'info, TokenAccount>,
    #[account(mut)]
    pub payer: Signer<'info>,
    pub system_program: Program<'info, System>,
    pub token_program: Program<'info, Token>,
    pub rent: Sysvar<'info, Rent>,
}

#[derive(Accounts)]
pub struct TreasuryWithdraw<'info> {
    pub authority: Signer<'info>,
    #[account(constraint=treasury.load()?.authority == authority.key())]
    pub treasury: AccountLoader<'info, Treasury>,
    #[account(mut, seeds=[b"account".as_ref(), treasury.key().as_ref(), source_account.mint.as_ref()], bump)]
    pub source_account: Account<'info, TokenAccount>,
    #[account(mut, constraint=source_account.mint == destination_account.mint)]
    pub destination_account: Account<'info, TokenAccount>,
    /// CHECK: token_authority is safe because it is a PDA
    pub token_authority: AccountInfo<'info>,
    pub system_program: Program<'info, System>,
    pub token_program: Program<'info, Token>,
}

#[derive(Accounts)]
pub struct BonderSetting<'info> {
    pub olympus_dao: Signer<'info>,
    #[account(seeds=[b"olympus".as_ref()], bump=254, has_one = olympus_dao)]
    pub olympus_data: Account<'info, OlympusData>,
    pub bonder: AccountLoader<'info, Bonder>,
    pub treasury: AccountLoader<'info, Treasury>,
    pub system_program: Program<'info, System>,
    pub token_program: Program<'info, Token>,
    pub rent: Sysvar<'info, Rent>,
}

#[derive(Accounts)]
pub struct CreateBonder<'info> {
    #[account(seeds=[b"olympus".as_ref()], bump, has_one = olympus_dao)]
    pub olympus_data: Account<'info, OlympusData>,
    #[account(mut)]
    pub olympus_dao: Signer<'info>,
    /// CHECK: authority is safe because it is set by the DAO
    pub authority: AccountInfo<'info>,
    pub principal_mint: Account<'info, Mint>,
    #[account(
        init,
        seeds = [b"account".as_ref(), treasury.key().as_ref(), principal_mint.key().as_ref()],
        bump,
        payer = payer,
        token::mint = principal_mint,
        token::authority = olympus_dao
    )]
    pub principal_account: Account<'info, TokenAccount>,
    #[account(init_if_needed,
        seeds = [b"daoAccount".as_ref(), principal_mint.key().as_ref()],
        bump,
        payer = payer,
        token::mint = principal_mint,
        token::authority = olympus_dao
    )]
    pub dao_principal_account: Account<'info, TokenAccount>,
    #[account(init, seeds=[b"bonder".as_ref(), treasury.key().as_ref(), principal_mint.key().as_ref()], bump, payer = olympus_dao)]
    pub bonder: AccountLoader<'info, Bonder>,
    #[account(has_one=authority)]
    pub treasury: AccountLoader<'info, Treasury>,
    #[account(mut)]
    pub payer: Signer<'info>,
    pub system_program: Program<'info, System>,
    pub token_program: Program<'info, Token>,
    pub clock: Sysvar<'info, Clock>,
    pub rent: Sysvar<'info, Rent>,
}

#[derive(Accounts)]
pub struct BonderDeposit<'info> {
    #[account(mut)]
    pub bonder: AccountLoader<'info, Bonder>,
    #[account(init, payer = payer)]
    pub bond: AccountLoader<'info, Bond>,
    #[account(mut)]
    pub authority: Signer<'info>,
    #[account(mut)]
    pub token_account: Box<Account<'info, TokenAccount>>,
    /// CHECK: this is safe because it is a PDA
    pub token_authority: AccountInfo<'info>,
    #[account(mut,
        seeds = [b"account".as_ref(), treasury.key().as_ref(), bonder.load()?.mint.as_ref()],
        bump = bonder.load()?.principal_bump
    )]
    /// CHECK: this is safe because it is constrained above
    pub principal_account: AccountInfo<'info>,
    #[account(
        init,
        seeds = [b"bond".as_ref(), bond.key().as_ref()],
        bump,
        payer = payer,
        token::mint = payout_mint,
        token::authority = token_authority
    )]
    pub bond_account: Box<Account<'info, TokenAccount>>,
    #[account(constraint=principal_mint.key() == bonder.load()?.mint @ ErrorCode::WrongPrincipalMint)]
    pub principal_mint: Account<'info, Mint>,
    #[account(constraint=payout_mint.key() == treasury.load()?.payout_mint @ ErrorCode::WrongPayoutMint)]
    pub payout_mint: Account<'info, Mint>,
    #[account(
        mut,
        seeds = [b"account".as_ref(), treasury.key().as_ref(), payout_mint.key().as_ref()],
        bump = treasury.load()?.payout_account_bump,
    )]
    /// CHECK: this is safe because it is constrained above
    pub payout_account: AccountInfo<'info>,
    #[account(mut,
        seeds = [b"daoAccount".as_ref(), bonder.load()?.mint.as_ref()],
        bump = bonder.load()?.dao_principal_account_bump
    )]
    /// CHECK: this is safe because it is constrained above
    pub dao_principal_account: AccountInfo<'info>,
    #[account(mut)]
    pub payer: Signer<'info>,
    #[account(mut,
        seeds = [b"daoAccount".as_ref(), payout_mint.key().as_ref()],
        bump = treasury.load()?.dao_payout_account_bump
    )]
    /// CHECK: this is safe because it is constrained above
    pub dao_payout_account: AccountInfo<'info>,
    #[account(
        init,
        payer = payer,
        mint::authority = token_authority,
        mint::decimals = 0
    )]
    pub nft_mint: Box<Account<'info, Mint>>,
    #[account(
        init,
        payer = payer,
        token::mint = nft_mint,
        token::authority = authority
    )]
    pub nft_token: Box<Account<'info, TokenAccount>>,
    #[account(mut, constraint=bonder.load()?.treasury == treasury.key() @ ErrorCode::WrongTreasury)]
    pub treasury: AccountLoader<'info, Treasury>,
    pub system_program: Program<'info, System>,
    pub token_program: Program<'info, Token>,
    pub clock: Sysvar<'info, Clock>,
    pub rent: Sysvar<'info, Rent>,
}

#[derive(Accounts)]
pub struct BondRedeem<'info> {
    pub bonder: AccountLoader<'info, Bonder>,
    #[account(mut, constraint=bond.load()?.bonder == bonder.key() @ ErrorCode::WrongBonder)]
    pub bond: AccountLoader<'info, Bond>,
    #[account(mut, constraint=bonder.load()?.treasury == treasury.key() @ ErrorCode::WrongTreasury)]
    pub treasury: AccountLoader<'info, Treasury>,
    #[account(mut)]
    pub authority: Signer<'info>,
    #[account(constraint=nft_token.mint == bond.load()?.nft_mint @ ErrorCode::WrongNFTMint,
              constraint=nft_token.amount == 1 @ ErrorCode::NoTokensInNFTAccount,
              constraint=(nft_token.delegate.is_some() && nft_token.delegate.unwrap() == authority.key() && nft_token.delegated_amount >= 1) ||
                          nft_token.owner == authority.key() @ ErrorCode::Unauthorized)]
    pub nft_token: Box<Account<'info, TokenAccount>>,
    #[account(mut)]
    pub token_account: Account<'info, TokenAccount>,
    pub payer: Signer<'info>,
    #[account(
        mut,
        seeds = [b"bond".as_ref(), bond.key().as_ref()],
        bump = bond.load()?.bond_account_bump,
    )]
    pub bond_account: Account<'info, TokenAccount>,
    /// CHECK: this is safe because it is a PDA
    pub token_authority: AccountInfo<'info>,
    pub system_program: Program<'info, System>,
    pub token_program: Program<'info, Token>,
    pub clock: Sysvar<'info, Clock>,
}

#[account(zero_copy)]
#[derive(Default)]
pub struct Bonder {
    /// The mint for the principal token
    pub mint: Pubkey,
    /// The bump for locating the principal token account
    pub principal_bump: u8,
    // The bump for locating the DAO principal token account
    pub dao_principal_account_bump: u8,
    /// The treasury this bonder makes deposits to
    pub treasury: Pubkey,
    /// The authority that is allowed to manipulate the control variables of this bonder
    pub authority: Pubkey,

    /// The total amount of principal tokens bonded
    pub total_bonded: u64,
    /// The total amount of payout redeemed by bond holders.
    pub total_payout: u64,
    /// The total value of the debt. The `value` is expressed as the ratio of payout to principal tokens in circulation.
    pub total_debt: u64,

    /// A scaling variable for the price.
    pub control_variable: u64,
    /// The vesting term, in seconds.
    pub vesting_term: u64,
    /// The minimum price versus principal value
    pub principal_value: u64,
    /// The maximum payout in thousandths of a %. i.e. 500 = 0.5%
    pub max_payout_percent: u64,
    /// The maximum allowable debt
    pub max_debt: u64,
    // The minimum price to pay
    pub minimum_price: u64,

    /// True, if the fee should be in payout tokens. Otherwise, the fee will be deducted from principal tokens.
    pub fee_in_payout: bool,

    // Array of fees. Currently up to 5 fee tiers supported. Each tier is specified in `fee_tiers`, and percentages are expressed in ten-thousands (i.e. 33300 = 3.3%)
    // The first element is the default (principal bonded = 0) fee. Once the principal bonded is greater than an element in fee_tiers, we move to the next fee tier.
    pub fee_percentages: [u64; 5],

    // Array of fee "tiers".
    pub fee_tiers: [u64; 4],

    // The last slot the bonder was updated for decaying the debt.
    pub last_slot: u64,

    // The last time the bonder was updated for decaying the debt.
    pub last_time: i64,

    // The rate to adjust the BCV, until the target `bcv_adjust_target` is hit, in thousandths per second. i.e. 5000 = 0.005 / s
    pub bcv_adjust_rate: u64,
    // The target for the BCV.
    pub bcv_adjust_target: u64,
    // The minimum to adjust the BCV buffer by.
    pub bcv_adjust_buffer: u64,
    // The last time the BCV was adjusted
    pub bcv_adjust_last: i64,
}

#[account(zero_copy)]
#[derive(Default)]
pub struct Bond {
    /// The total amount of time in seconds from `vesting_start` before 100% of the payout is accessible.
    pub vesting_term: u64,
    /// When the `vesting_term` starts, as a unix timestamp.
    pub vesting_start: i64,
    /// The `bonder` that issued this bond.
    pub bonder: Pubkey,
    /// The public key of the NFT mint that must be owned in order to redeem the bond
    pub nft_mint: Pubkey,
    // The bump for the bond account
    pub bond_account_bump: u8,
}

#[account(zero_copy)]
#[derive(Default)]
pub struct Treasury {
    // The key of the payout token account
    pub payout_token: Pubkey,
    // The key of the mint for the payout token
    pub payout_mint: Pubkey,
    /// Partner's public key
    pub authority: Pubkey,
    /// The bump for the payout account
    pub payout_account_bump: u8,
    /// The bump for the DAO's payout account (for collecting fees)
    pub dao_payout_account_bump: u8,
}

#[account]
#[derive(Default)]
pub struct OlympusData {
    /// The key of the DAO
    pub olympus_dao: Pubkey,
}

impl<'info> CreateTreasury<'info> {
    fn into_set_payout_authority_context(
        &self,
    ) -> CpiContext<'_, '_, '_, 'info, SetAuthority<'info>> {
        let cpi_accounts = SetAuthority {
            account_or_mint: self.payout_account.to_account_info().clone(),
            current_authority: self.olympus_dao.to_account_info().clone(),
        };
        CpiContext::new(self.token_program.to_account_info().clone(), cpi_accounts)
    }
}

impl<'info> TreasuryWithdraw<'info> {
    fn into_transfer_context(&self) -> CpiContext<'_, '_, '_, 'info, Transfer<'info>> {
        let cpi_accounts = Transfer {
            authority: self.token_authority.to_account_info().clone(),
            from: self.source_account.to_account_info().clone(),
            to: self.destination_account.to_account_info().clone(),
        };
        CpiContext::new(self.token_program.to_account_info().clone(), cpi_accounts)
    }
}

impl<'info> CreateBonder<'info> {
    fn into_set_principal_authority_context(
        &self,
    ) -> CpiContext<'_, '_, '_, 'info, SetAuthority<'info>> {
        let cpi_accounts = SetAuthority {
            account_or_mint: self.principal_account.to_account_info().clone(),
            current_authority: self.olympus_dao.to_account_info().clone(),
        };
        CpiContext::new(self.token_program.to_account_info().clone(), cpi_accounts)
    }
}

impl<'info> BonderDeposit<'info> {
    fn into_transfer_from_user_context(&self) -> CpiContext<'_, '_, '_, 'info, Transfer<'info>> {
        let cpi_accounts = Transfer {
            authority: self.authority.to_account_info().clone(),
            from: self.token_account.to_account_info().clone(),
            to: self.principal_account.to_account_info().clone(),
        };
        CpiContext::new(self.token_program.to_account_info().clone(), cpi_accounts)
    }

    fn into_transfer_to_bond_context(&self) -> CpiContext<'_, '_, '_, 'info, Transfer<'info>> {
        let cpi_accounts = Transfer {
            authority: self.token_authority.to_account_info().clone(),
            from: self.payout_account.to_account_info().clone(),
            to: self.bond_account.to_account_info().clone(),
        };
        CpiContext::new(self.token_program.to_account_info().clone(), cpi_accounts)
    }

    fn into_transfer_to_payout_dao_context(
        &self,
    ) -> CpiContext<'_, '_, '_, 'info, Transfer<'info>> {
        let cpi_accounts = Transfer {
            authority: self.token_authority.to_account_info().clone(),
            from: self.payout_account.to_account_info().clone(),
            to: self.dao_payout_account.to_account_info().clone(),
        };
        CpiContext::new(self.token_program.to_account_info().clone(), cpi_accounts)
    }

    fn into_transfer_to_principal_dao_context(
        &self,
    ) -> CpiContext<'_, '_, '_, 'info, Transfer<'info>> {
        let cpi_accounts = Transfer {
            authority: self.authority.to_account_info().clone(),
            from: self.token_account.to_account_info().clone(),
            to: self.dao_principal_account.to_account_info().clone(),
        };
        CpiContext::new(self.token_program.to_account_info().clone(), cpi_accounts)
    }

    fn into_disable_mint_authority_context(
        &self,
    ) -> CpiContext<'_, '_, '_, 'info, SetAuthority<'info>> {
        let cpi_accounts = SetAuthority {
            account_or_mint: self.nft_mint.to_account_info().clone(),
            current_authority: self.token_authority.to_account_info().clone(),
        };
        CpiContext::new(self.token_program.to_account_info().clone(), cpi_accounts)
    }

    fn into_mint_nft_context(&self) -> CpiContext<'_, '_, '_, 'info, MintTo<'info>> {
        let cpi_accounts = MintTo {
            mint: self.nft_mint.to_account_info().clone(),
            to: self.nft_token.to_account_info().clone(),
            authority: self.token_authority.to_account_info().clone(),
        };
        CpiContext::new(self.token_program.to_account_info().clone(), cpi_accounts)
    }
}

impl<'info> BondRedeem<'info> {
    fn into_transfer_context(&self) -> CpiContext<'_, '_, '_, 'info, Transfer<'info>> {
        let cpi_accounts = Transfer {
            authority: self.token_authority.to_account_info().clone(),
            from: self.bond_account.to_account_info().clone(),
            to: self.token_account.to_account_info().clone(),
        };
        CpiContext::new(self.token_program.to_account_info().clone(), cpi_accounts)
    }

    fn into_close_context(&self) -> CpiContext<'_, '_, '_, 'info, CloseAccount<'info>> {
        let cpi_accounts = CloseAccount {
            authority: self.token_authority.clone(),
            account: self.bond_account.to_account_info().clone(),
            destination: self.payer.to_account_info().clone(),
        };
        CpiContext::new(self.token_program.to_account_info().clone(), cpi_accounts)
    }
}

#[error_code]
pub enum ErrorCode {
    #[msg("You are not authorized to perform this action.")]
    Unauthorized,
    #[msg("Unexpected math over/underflow.")]
    MathOverflow,
    #[msg("Bond price greater than limit (max) price.")]
    BondPriceOverLimitPrice,
    #[msg("Maximum allowable debt exceeded.")]
    MaxDebtExceeded,
    #[msg("The fee levels provided were not incrementing.")]
    FeeLevelsNotIncrementing,
    #[msg("Backwards time was computed.")]
    BackwardsTime,
    #[msg("The bond price is under the minimum price.")]
    BondPriceUnderMinimum,
    #[msg("The bonds size exceeds the maximum payout.")]
    BondExceedsMaxPayout,
    #[msg("The NFT Token account contains no tokens.")]
    NoTokensInNFTAccount,
    #[msg("The wrong NFT token mint was supplied.")]
    WrongNFTMint,
    #[msg("The wrong treasury was supplied.")]
    WrongTreasury,
    #[msg("The wrong bonder was supplied.")]
    WrongBonder,
    #[msg("The wrong principal mint was supplied.")]
    WrongPrincipalMint,
    #[msg("The wrong payout mint was supplied.")]
    WrongPayoutMint,
}

#[derive(AnchorDeserialize, AnchorSerialize)]
pub struct BonderSettings {
    pub max_debt: Option<u64>,
    pub vesting: Option<u64>,
    pub max_payout_percent: Option<u64>,
    pub bcv_adjust_target: Option<u64>,
    pub bcv_adjust_rate: Option<u64>,
    pub bcv_adjust_buffer: Option<u64>,
}
