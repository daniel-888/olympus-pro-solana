import * as anchor from '@project-serum/anchor';
import { Program } from '@project-serum/anchor';
import { OlympusproSol } from '../target/types/olympuspro_sol';
import { TOKEN_PROGRAM_ID, Token } from "@solana/spl-token";
import { expect } from 'chai';
import assert from 'assert/strict';

describe('olympuspro-sol', () => {

  // Configure the client to use the local cluster.
  anchor.setProvider(anchor.Provider.env());

  const program = anchor.workspace.OlympusproSol as Program<OlympusproSol>;

  let olympusData : anchor.web3.PublicKey;
  let olympusDataBump : number;
  let principalAccountBump : number;
  let principalAccount : anchor.web3.PublicKey;
  let payoutAccountBump : number;
  let payoutAccount : anchor.web3.PublicKey;
  let payoutAccount2Bump : number;
  let payoutAccount2 : anchor.web3.PublicKey;
  let treasury : anchor.web3.PublicKey;
  let treasuryBump : number;
  let treasury2 : anchor.web3.PublicKey;
  let treasury2Bump : number;
  let bonder : anchor.web3.PublicKey;
  let bonderBump : number;
  let tokenAMint : Token;
  let tokenBMint : Token;
  let daoPayoutAccount : anchor.web3.PublicKey;
  let daoPayoutAccountBump : number;
  let daoPrincipalAccount : anchor.web3.PublicKey;
  let daoPrincipalAccountBump : number;

  // These accounts belong to the partner
  let partnerAuthority = anchor.web3.Keypair.generate();
  let partnerTokenA : anchor.web3.PublicKey;
  let partnerTokenB : anchor.web3.PublicKey;

  // These accounts belong to a user ("bond owner"/bonder)
  let bonderAuthority = anchor.web3.Keypair.generate();
  let bonderTokenA : anchor.web3.PublicKey;
  let bonderTokenB : anchor.web3.PublicKey;

  let tokenMinter = anchor.web3.Keypair.generate();
  let authority = anchor.web3.Keypair.generate();

  // These accounts belong to the DAO
  const olympusDao = anchor.web3.Keypair.generate();
  let olympusDaoTokenA : anchor.web3.PublicKey;
  let olympusDaoTokenB : anchor.web3.PublicKey;

  let minRent = 0;

  // This should eventually go into a library
  const getBondAccount = async (bondKey : anchor.web3.PublicKey) => {
    return await anchor.web3.PublicKey.findProgramAddress([Buffer.from("bond"), bondKey.toBuffer()], program.programId);
  };

  const getTokenAuthority = async (treasuryAccount : anchor.web3.PublicKey) => {
    const [authority, bump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("olympusAuthority"), treasuryAccount.toBuffer()], program.programId);
    return authority;
  }

  before(async () => {
    minRent = await Token.getMinBalanceRentForExemptAccount(anchor.getProvider().connection);
    const AIRDROP_AMOUNT = 10000000000;
    await anchor.getProvider().connection.confirmTransaction(await anchor.getProvider().connection.requestAirdrop(olympusDao.publicKey, AIRDROP_AMOUNT), "confirmed");
    await anchor.getProvider().connection.confirmTransaction(await anchor.getProvider().connection.requestAirdrop(authority.publicKey, AIRDROP_AMOUNT), "confirmed");
    await anchor.getProvider().connection.confirmTransaction(await anchor.getProvider().connection.requestAirdrop(tokenMinter.publicKey, AIRDROP_AMOUNT), "confirmed");
    await anchor.getProvider().connection.confirmTransaction(await anchor.getProvider().connection.requestAirdrop(partnerAuthority.publicKey, AIRDROP_AMOUNT), "confirmed");
    await anchor.getProvider().connection.confirmTransaction(await anchor.getProvider().connection.requestAirdrop(bonderAuthority.publicKey, AIRDROP_AMOUNT), "confirmed");

    // Token A is the *payout* token
    tokenAMint = await Token.createMint(
      anchor.getProvider().connection,
      tokenMinter,
      tokenMinter.publicKey,
      null,
      0,
      TOKEN_PROGRAM_ID
    );

    // Token B is the *principal* token
    tokenBMint = await Token.createMint(
      anchor.getProvider().connection,
      tokenMinter,
      tokenMinter.publicKey,
      null,
      0,
      TOKEN_PROGRAM_ID
    );

    partnerTokenA = await tokenAMint.createAccount(partnerAuthority.publicKey);
    partnerTokenB = await tokenBMint.createAccount(partnerAuthority.publicKey);

    olympusDaoTokenA = await tokenAMint.createAccount(olympusDao.publicKey);
    olympusDaoTokenB = await tokenBMint.createAccount(olympusDao.publicKey);

    bonderTokenA = await tokenAMint.createAccount(bonderAuthority.publicKey);
    bonderTokenB = await tokenBMint.createAccount(bonderAuthority.publicKey);


    await tokenAMint.mintTo(partnerTokenA, tokenMinter, [], 1000);
    await tokenBMint.mintTo(bonderTokenB, tokenMinter, [], 1000);

    [treasury, treasuryBump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("treasury"), tokenAMint.publicKey.toBuffer(), partnerAuthority.publicKey.toBuffer()], program.programId);
    [daoPayoutAccount, daoPayoutAccountBump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("daoAccount"), tokenAMint.publicKey.toBuffer()], program.programId);
    [daoPrincipalAccount, daoPrincipalAccountBump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("daoAccount"), tokenBMint.publicKey.toBuffer()], program.programId);
    [treasury2, treasury2Bump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("treasury"), tokenAMint.publicKey.toBuffer(), olympusDao.publicKey.toBuffer()], program.programId);
    [payoutAccount, payoutAccountBump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("account"), treasury.toBuffer(), tokenAMint.publicKey.toBuffer()], program.programId);
    [payoutAccount2, payoutAccount2Bump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("account"), treasury2.toBuffer(), tokenAMint.publicKey.toBuffer()], program.programId);
    [olympusData, olympusDataBump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("olympus")], program.programId);
    [bonder, bonderBump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("bonder"), treasury.toBuffer(), tokenBMint.publicKey.toBuffer()], program.programId);
    [principalAccount, principalAccountBump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("account"), treasury.toBuffer(), tokenBMint.publicKey.toBuffer()], program.programId);
  });

  it('Can be initialized.', async () => {
    await program.rpc.initialize({
      accounts : {
        olympusData,
        olympusDao : olympusDao.publicKey,
        systemProgram: anchor.web3.SystemProgram.programId,
        payer : olympusDao.publicKey
      },
      signers: [olympusDao],
    })
  });

  describe('Treasury tests', () => {
    it('Can create treasury.', async () => {
      await program.rpc.createTreasury({
        accounts : {
          olympusData,
          treasury,
          payoutAccount,
          daoPayoutAccount,
          authority: partnerAuthority.publicKey,
          payoutMint : tokenAMint.publicKey,
          olympusDao : olympusDao.publicKey,
          systemProgram: anchor.web3.SystemProgram.programId,
          payer : olympusDao.publicKey,
          tokenProgram: TOKEN_PROGRAM_ID,
          rent : anchor.web3.SYSVAR_RENT_PUBKEY
        },
        signers: [olympusDao],
      })
    });

    it('Can create 2nd treasury with different authority but same payout token', async () => {
      await program.rpc.createTreasury({
        accounts : {
          olympusData,
          treasury: treasury2,
          daoPayoutAccount : daoPayoutAccount,
          payoutAccount: payoutAccount2,
          authority: olympusDao.publicKey,
          payoutMint : tokenAMint.publicKey,
          olympusDao : olympusDao.publicKey,
          systemProgram: anchor.web3.SystemProgram.programId,
          payer : olympusDao.publicKey,
          tokenProgram: TOKEN_PROGRAM_ID,
          rent : anchor.web3.SYSVAR_RENT_PUBKEY
        },
        signers: [olympusDao],
      })
    });

    it('Can send 1000 tokens to treasury', async () => {
      let tx = new anchor.web3.Transaction().add(
        Token.createTransferInstruction(TOKEN_PROGRAM_ID, partnerTokenA, payoutAccount, partnerAuthority.publicKey, [], 1000)
      );
  
      await anchor.web3.sendAndConfirmTransaction(
        anchor.getProvider().connection,
        tx,
        [partnerAuthority]
      );
  
      let payoutAccountInfo = await tokenAMint.getAccountInfo(payoutAccount);
      expect(payoutAccountInfo.amount.toNumber()).to.equal(1000);
    });

    it('Cannot manually withdraw 100 tokens from treasury', async () => {
      let tx = new anchor.web3.Transaction().add(
        Token.createTransferInstruction(TOKEN_PROGRAM_ID, payoutAccount, partnerTokenA, partnerAuthority.publicKey, [], 1000)
      );
  
      await assert.rejects(anchor.web3.sendAndConfirmTransaction(
        anchor.getProvider().connection,
        tx,
        [partnerAuthority]
      ));
    });

    it('Can withdraw 10 payout tokens from treasury', async () => {
      await program.rpc.treasuryWithdraw(new anchor.BN(10), {
        accounts : {
          treasury,
          sourceAccount: payoutAccount,
          destinationAccount: partnerTokenA,
          authority: partnerAuthority.publicKey,
          tokenAuthority : await getTokenAuthority(treasury),
          systemProgram: anchor.web3.SystemProgram.programId,
          tokenProgram: TOKEN_PROGRAM_ID
        },
        signers: [partnerAuthority],
      })

      expect((await tokenAMint.getAccountInfo(partnerTokenA)).amount.toNumber()).to.equal(10);
    });

    it('Cannot withdraw 10 payout tokens from treasury to incompatible token', async () => {
      await assert.rejects(program.rpc.treasuryWithdraw(new anchor.BN(10), {
        accounts : {
          treasury,
          sourceAccount: payoutAccount,
          destinationAccount: partnerTokenB,
          authority: partnerAuthority.publicKey,
          tokenAuthority : await getTokenAuthority(treasury),
          systemProgram: anchor.web3.SystemProgram.programId,
          tokenProgram: TOKEN_PROGRAM_ID
        },
        signers: [partnerAuthority],
      }));

      expect((await tokenAMint.getAccountInfo(payoutAccount)).amount.toNumber()).to.equal(990);
    });

    it('Cannot withdraw 10 payout tokens from treasury using wrong authority', async () => {
      await assert.rejects(program.rpc.treasuryWithdraw(new anchor.BN(10), {
        accounts : {
          treasury,
          sourceAccount: payoutAccount,
          destinationAccount: partnerTokenB,
          authority: olympusDao.publicKey,
          tokenAuthority: await getTokenAuthority(treasury),
          systemProgram: anchor.web3.SystemProgram.programId,
          tokenProgram: TOKEN_PROGRAM_ID
        },
        signers: [olympusDao],
      }));

      expect((await tokenAMint.getAccountInfo(payoutAccount)).amount.toNumber()).to.equal(990);
    });

    it('Cannot withdraw 10 payout tokens from wrong treasury', async () => {
      await assert.rejects(program.rpc.treasuryWithdraw(new anchor.BN(10), {
        accounts : {
          treasury: treasury2,
          sourceAccount: payoutAccount,
          destinationAccount: partnerTokenB,
          authority: olympusDao.publicKey,
          tokenAuthority : await getTokenAuthority(treasury),
          systemProgram: anchor.web3.SystemProgram.programId,
          tokenProgram: TOKEN_PROGRAM_ID
        },
        signers: [olympusDao],
      }));

      expect((await tokenAMint.getAccountInfo(payoutAccount)).amount.toNumber()).to.equal(990);
    });

  });


 describe('Bonder tests', () => {

  it('Can create bonder', async () => {
    await program.rpc.createBonder(false, 
      [33300, 33300, 33300, 33300, 33300].map(x => new anchor.BN(x)), [0,0,0,0].map(x => new anchor.BN(x)), {
      accounts : {
        olympusData,
        olympusDao: olympusDao.publicKey,
        authority: partnerAuthority.publicKey,
        principalMint: tokenBMint.publicKey,
        daoPrincipalAccount,
        principalAccount,
        treasury,
        bonder,
        systemProgram: anchor.web3.SystemProgram.programId,
        payer : olympusDao.publicKey,
        rent : anchor.web3.SYSVAR_RENT_PUBKEY,
        clock : anchor.web3.SYSVAR_CLOCK_PUBKEY,
        tokenProgram: TOKEN_PROGRAM_ID
      },
      signers: [ olympusDao ],
    });
  });

  const bond = anchor.web3.Keypair.generate();
  const nftMint = anchor.web3.Keypair.generate();
  const nftToken = anchor.web3.Keypair.generate();

  it('Can deposit to bonder to issue bond', async () => {
    let [bondAccount, bondAccountBump] = await getBondAccount(bond.publicKey);

    await program.rpc.bonderDeposit(new anchor.BN(100), new anchor.BN(100000000), {
      accounts : {
        authority: bonderAuthority.publicKey,
        principalAccount,
        tokenAccount: bonderTokenB,
        payoutMint : tokenAMint.publicKey,
        principalMint : tokenBMint.publicKey,
        payoutAccount,
        daoPrincipalAccount,
        daoPayoutAccount,
        treasury,
        bondAccount,
        bond : bond.publicKey,
        payer : bonderAuthority.publicKey,
        bonder,
        nftMint: nftMint.publicKey,
        nftToken: nftToken.publicKey,
        tokenAuthority: await getTokenAuthority(treasury),
        systemProgram: anchor.web3.SystemProgram.programId,
        tokenProgram: TOKEN_PROGRAM_ID,
        clock : anchor.web3.SYSVAR_CLOCK_PUBKEY,
        rent : anchor.web3.SYSVAR_RENT_PUBKEY
      },
      signers: [ bonderAuthority, bond, nftMint, nftToken],
    });

    //principal should have 97, because 3% should go to DAO
    expect((await tokenBMint.getAccountInfo(principalAccount)).amount.toNumber()).to.equal(97);
    expect((await tokenBMint.getAccountInfo(daoPrincipalAccount)).amount.toNumber()).to.equal(3);
    expect((await tokenAMint.getAccountInfo(payoutAccount)).amount.toNumber()).to.equal(890);
    expect((await tokenAMint.getAccountInfo(bondAccount)).amount.toNumber()).to.equal(100);
  });

  const failLimitBond = anchor.web3.Keypair.generate();
  const failNftMint = anchor.web3.Keypair.generate();
  const failNftToken = anchor.web3.Keypair.generate();

  it('Bond is not issued if limit price is exceeded', async () => {
    let [bondAccount, bondAccountBump] = await getBondAccount(failLimitBond.publicKey);

    await assert.rejects(program.rpc.bonderDeposit(new anchor.BN(10), new anchor.BN(0), {
      accounts : {
        authority: bonderAuthority.publicKey,
        principalAccount,
        tokenAccount: bonderTokenB,
        payoutMint : tokenAMint.publicKey,
        principalMint : tokenBMint.publicKey,
        payoutAccount,
        daoPrincipalAccount,
        daoPayoutAccount,
        treasury,
        bondAccount,
        bond : failLimitBond.publicKey,
        payer : bonderAuthority.publicKey,
        nftMint : failNftMint.publicKey,
        nftToken : failNftToken.publicKey,
        bonder,
        tokenAuthority: await getTokenAuthority(treasury),
        systemProgram: anchor.web3.SystemProgram.programId,
        tokenProgram: TOKEN_PROGRAM_ID,
        clock : anchor.web3.SYSVAR_CLOCK_PUBKEY,
        rent : anchor.web3.SYSVAR_RENT_PUBKEY
      },
      signers: [ bonderAuthority, failLimitBond, failNftMint, failNftToken],
    }));
  });


  it('Partner can withdraw bonded principal token', async () => {
    await program.rpc.treasuryWithdraw(new anchor.BN(10), {
      accounts : {
        treasury,
        sourceAccount: principalAccount,
        destinationAccount: partnerTokenB,
        authority: partnerAuthority.publicKey,
        tokenAuthority: await getTokenAuthority(treasury),
        systemProgram: anchor.web3.SystemProgram.programId,
        tokenProgram: TOKEN_PROGRAM_ID
      },
      signers: [partnerAuthority],
    })

    expect((await tokenBMint.getAccountInfo(partnerTokenB)).amount.toNumber()).to.equal(10);
  });

  it('Partner cannot manually withdraw 10 tokens from bond account', async () => {
    let [bondAccount, bondAccountBump] = await getBondAccount(bond.publicKey);

    let tx = new anchor.web3.Transaction().add(
      Token.createTransferInstruction(TOKEN_PROGRAM_ID, bondAccount, partnerTokenA, partnerAuthority.publicKey, [], 10)
    );

    await assert.rejects(anchor.web3.sendAndConfirmTransaction(
      anchor.getProvider().connection,
      tx,
      [partnerAuthority]
    ));
  });

  it('Bonder cannot manually withdraw 10 tokens from bond account', async () => {
    let [bondAccount, bondAccountBump] = await getBondAccount(bond.publicKey);

    let tx = new anchor.web3.Transaction().add(
      Token.createTransferInstruction(TOKEN_PROGRAM_ID, bondAccount, bonderTokenA, bonderAuthority.publicKey, [], 10)
    );

    await assert.rejects(anchor.web3.sendAndConfirmTransaction(
      anchor.getProvider().connection,
      tx,
      [bonderAuthority]
    ));
  });
 })

 describe("Bond tests", async() => {
    const fastBond = anchor.web3.Keypair.generate();
    const fastBondNftToken = anchor.web3.Keypair.generate();
    const fastBondNftMint = anchor.web3.Keypair.generate();

    it('Can redeem instantly maturing bond', async () => {
      let [bondAccount, bondAccountBump] = await getBondAccount(fastBond.publicKey);
  
      await program.rpc.bonderDeposit(new anchor.BN(10), new anchor.BN(100000000), {
        accounts : {
          authority: bonderAuthority.publicKey,
          principalAccount,
          tokenAccount: bonderTokenB,
          payoutMint : tokenAMint.publicKey,
          principalMint: tokenBMint.publicKey,
          payoutAccount,
          daoPayoutAccount,
          daoPrincipalAccount,
          treasury,
          bondAccount,
          bond : fastBond.publicKey,
          bonder,
          nftMint: fastBondNftMint.publicKey,
          nftToken : fastBondNftToken.publicKey,
          tokenAuthority : await getTokenAuthority(treasury),
          systemProgram: anchor.web3.SystemProgram.programId,
          payer : bonderAuthority.publicKey,
          tokenProgram: TOKEN_PROGRAM_ID,
          clock : anchor.web3.SYSVAR_CLOCK_PUBKEY,
          rent : anchor.web3.SYSVAR_RENT_PUBKEY
        },
        signers: [ bonderAuthority, fastBond, fastBondNftMint, fastBondNftToken],
      });
  
      // the bond should be fully redeemable right away
      await program.rpc.bondRedeem({
        accounts : {
          authority: bonderAuthority.publicKey,
          tokenAccount: bonderTokenA,
          bondAccount,
          treasury,
          bond : fastBond.publicKey,
          nftToken : fastBondNftToken.publicKey,
          bonder,
          payer : bonderAuthority.publicKey,
          tokenAuthority: await getTokenAuthority(treasury),
          systemProgram: anchor.web3.SystemProgram.programId,
          tokenProgram: TOKEN_PROGRAM_ID,
          clock : anchor.web3.SYSVAR_CLOCK_PUBKEY
        },
        signers: [ bonderAuthority],
      });
      expect((await tokenAMint.getAccountInfo(bonderTokenA)).amount.toNumber()).to.equal(10);
    });

    const wrongAuthorityBond = anchor.web3.Keypair.generate();
    const wrongAuthorityNftToken = anchor.web3.Keypair.generate();
    const wrongAuthorityNftMint = anchor.web3.Keypair.generate();
    let nft_partner_account;
    let nft_token;

    it('Cannot be redeemed by wrong authority', async () => {
      let [bondAccount, bondAccountBump] = await getBondAccount(wrongAuthorityBond.publicKey);
  
      await program.rpc.bonderDeposit(new anchor.BN(10), new anchor.BN(100000000), {
        accounts : {
          authority: bonderAuthority.publicKey,
          principalAccount,
          tokenAccount: bonderTokenB,
          payoutMint : tokenAMint.publicKey,
          principalMint: tokenBMint.publicKey,
          payoutAccount,
          daoPayoutAccount,
          daoPrincipalAccount,
          treasury,
          bondAccount,
          nftMint: wrongAuthorityNftMint.publicKey,
          nftToken : wrongAuthorityNftToken.publicKey,
          bond : wrongAuthorityBond.publicKey,
          bonder,
          payer : bonderAuthority.publicKey,
          tokenAuthority : await getTokenAuthority(treasury),
          systemProgram: anchor.web3.SystemProgram.programId,
          tokenProgram: TOKEN_PROGRAM_ID,
          clock : anchor.web3.SYSVAR_CLOCK_PUBKEY,
          rent : anchor.web3.SYSVAR_RENT_PUBKEY
        },
        signers: [ bonderAuthority, wrongAuthorityBond, wrongAuthorityNftMint, wrongAuthorityNftToken],
      });

      nft_token = new Token(anchor.getProvider().connection, wrongAuthorityNftMint.publicKey, TOKEN_PROGRAM_ID, partnerAuthority);
      nft_partner_account = await nft_token.createAccount(partnerAuthority.publicKey);


      // the bond should *not* be redeemable by the partner
      await assert.rejects(program.rpc.bondRedeem({
        accounts : {
          authority: partnerAuthority.publicKey,
          nftToken: nft_partner_account,
          tokenAccount: bonderTokenA,
          bondAccount,
          treasury,
          bond : wrongAuthorityBond.publicKey,
          bonder,
          payer : bonderAuthority.publicKey,
          tokenAuthority : await getTokenAuthority(treasury),
          systemProgram: anchor.web3.SystemProgram.programId,
          tokenProgram: TOKEN_PROGRAM_ID,
          clock : anchor.web3.SYSVAR_CLOCK_PUBKEY
        },
        signers: [ partnerAuthority ],
      }));
    });

    it('Can be redeemed after NFT transfer', async () => {
      let [bondAccount, bondAccountBump] = await getBondAccount(wrongAuthorityBond.publicKey);

      // transfer the NFT to the partner.
      await nft_token.transfer(wrongAuthorityNftToken.publicKey, nft_partner_account, bonderAuthority, [], 1);

      expect((await nft_token.getAccountInfo(nft_partner_account)).amount.toNumber()).to.equal(1);

      // partner should now have 10 more tokens
      let partnerInitialTokens = (await tokenAMint.getAccountInfo(partnerTokenA)).amount.toNumber();
      
      await program.rpc.bondRedeem({
        accounts : {
          authority: partnerAuthority.publicKey,
          nftToken: nft_partner_account,
          tokenAccount: partnerTokenA,
          bondAccount,
          treasury,
          bond : wrongAuthorityBond.publicKey,
          bonder,
          payer : partnerAuthority.publicKey,
          tokenAuthority : await getTokenAuthority(treasury),
          systemProgram: anchor.web3.SystemProgram.programId,
          tokenProgram: TOKEN_PROGRAM_ID,
          clock : anchor.web3.SYSVAR_CLOCK_PUBKEY
        },
        signers: [ partnerAuthority ],
      });
      
      let partnerFinalTokens = (await tokenAMint.getAccountInfo(partnerTokenA)).amount.toNumber();
      
      expect(partnerFinalTokens).to.equal(partnerInitialTokens + 10);
    });


    it('Bond creation fails if there are insufficient payout tokens', async () => {

      let partnerPayoutTokens = (await tokenAMint.getAccountInfo(payoutAccount)).amount.toNumber();
      
      // withdraw all tokens
      await program.rpc.treasuryWithdraw(new anchor.BN(partnerPayoutTokens), {
        accounts : {
          treasury,
          sourceAccount: payoutAccount,
          destinationAccount: partnerTokenA,
          authority: partnerAuthority.publicKey,
          tokenAuthority : await getTokenAuthority(treasury),
          systemProgram: anchor.web3.SystemProgram.programId,
          tokenProgram: TOKEN_PROGRAM_ID
        },
        signers: [partnerAuthority],
      })

      const fastBond = anchor.web3.Keypair.generate();
      const fastBondNftToken = anchor.web3.Keypair.generate();
      const fastBondNftMint = anchor.web3.Keypair.generate();
      let [bondAccount, bondAccountBump] = await getBondAccount(fastBond.publicKey);

      // attempt to create a bond
      await assert.rejects(program.rpc.bonderDeposit(new anchor.BN(10), new anchor.BN(100000000), {
        accounts : {
          authority: bonderAuthority.publicKey,
          principalAccount,
          tokenAccount: bonderTokenB,
          payoutMint : tokenAMint.publicKey,
          principalMint: tokenBMint.publicKey,
          payoutAccount,
          daoPayoutAccount,
          daoPrincipalAccount,
          treasury,
          bondAccount,
          bond : fastBond.publicKey,
          bonder,
          nftMint: fastBondNftMint.publicKey,
          nftToken : fastBondNftToken.publicKey,
          tokenAuthority : await getTokenAuthority(treasury),
          systemProgram: anchor.web3.SystemProgram.programId,
          payer : bonderAuthority.publicKey,
          tokenProgram: TOKEN_PROGRAM_ID,
          clock : anchor.web3.SYSVAR_CLOCK_PUBKEY,
          rent : anchor.web3.SYSVAR_RENT_PUBKEY
        },
        signers: [ bonderAuthority, fastBond, fastBondNftMint, fastBondNftToken],
      }));
    });
 });

});
