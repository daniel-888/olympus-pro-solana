# Olympus Pro - Solana Repo

This repo stores the Solana version of Olympus Pro (**O**lympus **P**ro **S**olana, or *OPS*).

## General Architecture

Due to differences in how Solana manages state, the architecture of the OPS is
significantly different than the original Olympus Pro. Despite the differences in
architecture, the OPS does try to faithfully reproduce the mechanics of the original
Solidity version.

OPS works with `spl_tokens` as defined in the Solana program library (SPL). 

The Olympus DAO ("DAO") works with partners to deploy protocol owned liquidity.

For each partner, the DAO deploys a *treasury*, which holds liquidity (Tokens) and
a *bonder*, which issues *bond*s to users that deposit *principal tokens*. As a
bond matures, the user can redeem the bond for *payout tokens*. The partner
can control the amount of bonds issued and their pricing through a *bond control variable* 
(BCV) and the total debt (the ratio of minted principal tokens to payout tokens).
Users are assured that the bond will pay out because the payout token is locked
contractually by the protocol to the bond, and they can purchase the bonds at
a discount when the BCV and total debt in the treasury produce favorable prices.

## Basic Provisioning For Partners

The DAO provisions OPS for partners. OPS is a single program which is shared by all partners.

First, the DAO will call the `create_treasury` instruction with the mint account of the
partners' payout token. This instruction will create both a treasury account and a corresponding
token account with the payout token mint. The partner needs to seed the treasury with payout tokens by
either calling the `treasury_deposit` instruction with a token account, or by manually
minting or transferring to the treasury's payout token account, which is a program derived address (PDA).

Next, for each principal token the partner will issue bonds in, the DAO will call the `create_bonder`
instruction with the principal token mint that will be accepted. This instruction will create a
bonder account and a corresponding token account with the principal token mint. The principal token
account is attached to the treasury, not the bonder, and can be found using a PDA with the 
treasury address and principal token mint address. In order for the bonder to issue bonds, the 
partner must configure the bonder using the `bonder_setting` instruction, setting the maximum
allowable debt, BCV adjustment variables and vesting periods. 

Once the treasury and bonders are setup, the partner can collect principal tokens exchanged for
bonds by calling the `treasury_withdraw` instruction. Only the program has the authority to
manipulate the treasury accounts directly, so all withdrawals must go through this call.

## Usage by Users

Users can calculate the current bond price using the client library which reads the bonder
account. To obtain a bond, a user calls the `bonder_deposit` instruction with the number
of tokens to be deposited, and the maximum price they are willing to pay. The price of a bond
is expressed in principal tokens to payout tokens. For instance, a bond price of 1 means that
depositing 1 principal token will yield 1 payout token at maturity, whereas a bond price of
10 means that 10 principal tokens must be deposited to yield 1 payout token. Users can 
use the client library to check the terms of the bond they are issued (time to maturity). 
As the bond matures, users can redeem payout tokens held by the bond by calling `bond_redeem`,
with the token account to move tokens the redeemed tokens into. If the bond is not fully
mature, the bond will be partially redeemed.

