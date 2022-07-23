// Migrations are an early feature. Currently, they're nothing more than this
// single deploy script that's invoked from the CLI, injecting a provider
// configured from the workspace's Anchor.toml.

import * as anchor from "@project-serum/anchor";
import { ASSOCIATED_TOKEN_PROGRAM_ID, TOKEN_PROGRAM_ID, MINT_SIZE, MintLayout, AccountLayout, Account, getAccount, createAssociatedTokenAccountInstruction } from "@solana/spl-token";
import {  Transaction, SystemProgram, PublicKey } from '@solana/web3.js';
import {Wallet} from "@project-serum/anchor";
import { Program } from '@project-serum/anchor';
import { OlympusproSol } from '../target/types/olympuspro_sol';
import * as fsp from 'fs/promises';
import * as path from 'path';
import * as SplToken from "@solana/spl-token";

const createNewMint = async (connection : anchor.web3.Connection, payer : Wallet) => {

    const mintAccount = anchor.web3.Keypair.generate();
    const balanceNeeded = await SplToken.getMinimumBalanceForRentExemptMint(connection);
    const transaction = new Transaction();
    transaction.add(SystemProgram.createAccount({
      fromPubkey: payer.publicKey,
      newAccountPubkey: mintAccount.publicKey,
      lamports: balanceNeeded,
      space: MINT_SIZE,
      programId : TOKEN_PROGRAM_ID
    }),
      SplToken.createInitializeMintInstruction(mintAccount.publicKey,  0,
         payer.publicKey, payer.publicKey, TOKEN_PROGRAM_ID)); // Send the two instructions

    transaction.feePayer = payer.publicKey;
    transaction.recentBlockhash = (await anchor.getProvider().connection.getLatestBlockhash()).blockhash;
    transaction.sign(mintAccount);
    const signedTx = await payer.signTransaction(transaction);

    const txId = await anchor.getProvider().connection.sendRawTransaction(signedTx.serialize())
    await anchor.getProvider().connection.confirmTransaction(txId);

    return mintAccount.publicKey;
}

// This should eventually go into a library
const getBondAccount = async (bondKey : anchor.web3.PublicKey) => {
  const program = anchor.workspace.OlympusproSol as Program<OlympusproSol>;
  return await anchor.web3.PublicKey.findProgramAddress([Buffer.from("bond"), bondKey.toBuffer()], program.programId);
};

const getTokenAuthority = async (treasuryAccount : anchor.web3.PublicKey) => {
  const program = anchor.workspace.OlympusproSol as Program<OlympusproSol>;
  const [authority, bump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("olympusAuthority"), treasuryAccount.toBuffer()], program.programId);
  return authority;
}

const createTokenAccount = async(connection : anchor.web3.Connection, payer: Wallet, owner : anchor.web3.PublicKey, mint: anchor.web3.PublicKey) => {
    let account : Account;
    const [address] = await PublicKey.findProgramAddress(
      [owner.toBuffer(), TOKEN_PROGRAM_ID.toBuffer(), mint.toBuffer()],
      ASSOCIATED_TOKEN_PROGRAM_ID);

    try {
      account = await getAccount(connection, address, undefined, TOKEN_PROGRAM_ID);
    } catch (e) {
      try {
        const transaction = new Transaction().add(
          createAssociatedTokenAccountInstruction(
            payer.publicKey,
            address,
            owner,
            mint,
            TOKEN_PROGRAM_ID,
            ASSOCIATED_TOKEN_PROGRAM_ID
          )
        );

        transaction.feePayer = payer.publicKey;
        transaction.recentBlockhash = (await anchor.getProvider().connection.getLatestBlockhash()).blockhash;
        const signedTx = await payer.signTransaction(transaction);
        const txId = await anchor.getProvider().connection.sendRawTransaction(signedTx.serialize())
        await anchor.getProvider().connection.confirmTransaction(txId);

      } catch (e) {
        // ignore, account already exists?
      }

      account = await getAccount(connection, address, undefined, TOKEN_PROGRAM_ID);
    }
    
    return account.address;
}

const mintTo = async(connection : anchor.web3.Connection, mint : anchor.web3.PublicKey, destination : anchor.web3.PublicKey, authority : Wallet, amount : number) => {

    const transaction = new Transaction().add(SplToken.createMintToInstruction(mint, destination, authority.publicKey, amount));
    transaction.feePayer = authority.publicKey;
    transaction.recentBlockhash = (await anchor.getProvider().connection.getRecentBlockhash()).blockhash;
    const signedTx = await authority.signTransaction(transaction);
    const txId = await anchor.getProvider().connection.sendRawTransaction(signedTx.serialize())
    await anchor.getProvider().connection.confirmTransaction(txId);
}

const init = async() => {
    // Configure client to use the provider.
    anchor.setProvider(anchor.Provider.env());

    // Add your deploy script here.
    const connection = anchor.getProvider().connection;
    const olympusDao = anchor.getProvider().wallet as Wallet;

    const partnerAuthority = anchor.web3.Keypair.generate();
    const userAuthority = anchor.web3.Keypair.generate();

    // send SOL to the partner/user accounts
    const testLamports = 50_000_000;

    console.log(`send ${testLamports} to partner=${partnerAuthority.publicKey.toBase58()}`)
    const transferTxPartner = new Transaction();
    transferTxPartner.add(SystemProgram.transfer({
      fromPubkey: olympusDao.publicKey,
      toPubkey: partnerAuthority.publicKey,
      lamports: testLamports
    }));
    transferTxPartner.feePayer = olympusDao.publicKey;
    transferTxPartner.recentBlockhash = (await connection.getLatestBlockhash()).blockhash;
    const signedTransferTxPartner = await olympusDao.signTransaction(transferTxPartner);
    const transferTxPartnerSignature = await connection.sendRawTransaction(signedTransferTxPartner.serialize());
    await connection.confirmTransaction(transferTxPartnerSignature);
  
    console.log(`send ${testLamports} to user=${userAuthority.publicKey.toBase58()}`)
    const transferTxUser= new Transaction();
    transferTxUser.add(SystemProgram.transfer({
      fromPubkey: olympusDao.publicKey,
      toPubkey: userAuthority.publicKey,
      lamports: testLamports
    }));
    transferTxUser.feePayer = olympusDao.publicKey;
    transferTxUser.recentBlockhash = (await connection.getLatestBlockhash()).blockhash;
    const signedTransferTxUser = await olympusDao.signTransaction(transferTxUser);
    const transferTxUserSignature = await connection.sendRawTransaction(signedTransferTxUser.serialize());
    await connection.confirmTransaction(transferTxUserSignature);
    

    console.log("creating some mints")
    const tokenAMint = await createNewMint(connection, olympusDao);
    const tokenBMint = await createNewMint(connection, olympusDao);

    console.log("creating some token accounts");
    const partnerTokenA = await createTokenAccount(connection, olympusDao, partnerAuthority.publicKey, tokenAMint);
    const partnerTokenB = await createTokenAccount(connection, olympusDao, partnerAuthority.publicKey, tokenBMint);

    const olympusTokenA = await createTokenAccount(connection, olympusDao, olympusDao.publicKey, tokenAMint);
    const olympusTokenB = await createTokenAccount(connection, olympusDao, olympusDao.publicKey, tokenBMint);

    const userTokenA = await createTokenAccount(connection, olympusDao, userAuthority.publicKey, tokenAMint);
    const userTokenB = await createTokenAccount(connection, olympusDao, userAuthority.publicKey, tokenBMint);

    console.log("minting some tokens")
    // To start, give the partner 10K tokenA and user 10K tokenB
    console.log(`Try minting to ${partnerTokenA.toBase58()} (owner=${partnerAuthority.publicKey.toBase58()})`);
    await mintTo(connection, tokenAMint, partnerTokenA, olympusDao, 20_000);
    console.log(`Try minting to ${userTokenA.toBase58()} (owner=${userAuthority.publicKey.toBase58()})`);
    await mintTo(connection, tokenBMint, userTokenB, olympusDao, 10_000);

    const program = anchor.workspace.OlympusproSol as Program<OlympusproSol>;
    const [olympusData, olympusDataBump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("olympus")], program.programId);
    const [treasury, treasuryBump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("treasury"), tokenAMint.toBuffer(), olympusDao.publicKey.toBuffer()], program.programId);
    const [payoutAccount, payoutAccountBump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("account"), treasury.toBuffer(), tokenAMint.toBuffer()], program.programId);
    const [daoPayoutAccount, daoPayoutAccountBump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("daoAccount"), tokenAMint.toBuffer()], program.programId);
    const [daoPrincipalAccount, daoPrincipalAccountBump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("daoAccount"), tokenBMint.toBuffer()], program.programId);
    const [principalAccount, principalAccountBump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("account"), treasury.toBuffer(), tokenBMint.toBuffer()], program.programId);
    const [bonder, bonderBump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("bonder"), treasury.toBuffer(), tokenBMint.toBuffer()], program.programId);

    console.log(`Try creating a treasury.`);
    // Create a treasury
    const initTx = await program.transaction.createTreasury({
        accounts : {
          olympusData,
          treasury,
          payoutAccount,
          daoPayoutAccount,
          authority: olympusDao.publicKey,
          payoutMint : tokenAMint,
          olympusDao : olympusDao.publicKey,
          systemProgram: anchor.web3.SystemProgram.programId,
          payer : olympusDao.publicKey,
          tokenProgram: TOKEN_PROGRAM_ID,
          rent : anchor.web3.SYSVAR_RENT_PUBKEY
        }
      })
    
      initTx.feePayer = olympusDao.publicKey;
      initTx.recentBlockhash = (await anchor.getProvider().connection.getRecentBlockhash()).blockhash;
      const signedTx = await olympusDao.signTransaction(initTx);
      const txId = await anchor.getProvider().connection.sendRawTransaction(signedTx.serialize())

      await anchor.getProvider().connection.confirmTransaction(txId);

      console.log("Transfer 10K partner tokens to treasury")
      // Send 10K partner tokens to the treasury
      let tx = new anchor.web3.Transaction().add(
        SplToken.createTransferInstruction(partnerTokenA, payoutAccount, partnerAuthority.publicKey, 10_000)
      );
  
      tx.feePayer = partnerAuthority.publicKey;
      tx.recentBlockhash = (await anchor.getProvider().connection.getRecentBlockhash()).blockhash;
      tx.sign(partnerAuthority);
      const sendTx = await anchor.getProvider().connection.sendRawTransaction(tx.serialize()); 
      await anchor.getProvider().connection.confirmTransaction(sendTx);

      console.log("Creating a bonder")
      const bonderTx = await program.transaction.createBonder(false, 
        [33300, 33300, 33300, 33300, 33300].map(x => new anchor.BN(x)), [0,0,0,0].map(x => new anchor.BN(x)), {
        accounts : {
          olympusData,
          olympusDao: olympusDao.publicKey,
          authority: olympusDao.publicKey,
          principalMint: tokenBMint,
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
      });

    bonderTx.feePayer = olympusDao.publicKey;
    bonderTx.recentBlockhash = (await anchor.getProvider().connection.getRecentBlockhash()).blockhash;
    const signedTx2 = await olympusDao.signTransaction(bonderTx);
    const txId2 = await anchor.getProvider().connection.sendRawTransaction(signedTx2.serialize())
    await anchor.getProvider().connection.confirmTransaction(txId2);

    console.log("Try depositing to create a bond");
  
    const bond = anchor.web3.Keypair.generate();
    const nftMint = anchor.web3.Keypair.generate();
    const nftToken = anchor.web3.Keypair.generate();
    let [bondAccount, bondAccountBump] = await getBondAccount(bond.publicKey);

    await program.rpc.bonderDeposit(new anchor.BN(1), new anchor.BN(10), {
      accounts : {
        authority: userAuthority.publicKey,
        principalAccount,
        tokenAccount: userTokenB,
        payoutMint : tokenAMint,
        principalMint : tokenBMint,
        payoutAccount,
        daoPrincipalAccount,
        daoPayoutAccount,
        treasury,
        bondAccount,
        bond : bond.publicKey,
        payer : userAuthority.publicKey,
        bonder,
        nftMint: nftMint.publicKey,
        nftToken: nftToken.publicKey,
        tokenAuthority: await getTokenAuthority(treasury),
        systemProgram: anchor.web3.SystemProgram.programId,
        tokenProgram: TOKEN_PROGRAM_ID,
        clock : anchor.web3.SYSVAR_CLOCK_PUBKEY,
        rent : anchor.web3.SYSVAR_RENT_PUBKEY
      },
      signers: [ userAuthority, bond, nftMint, nftToken],
    });


    const outData = {
        tokenAMint,
        tokenBMint,
        partnerTokenA,
        partnerTokenB,
        olympusTokenA,
        olympusTokenB,
        userTokenA,
        userTokenB,
        treasury,
        bonder,
        bond: bond.publicKey.toBase58(),
        userAuthorityPublicKey : userAuthority.publicKey.toBase58(),
        userAuthorityPrivateKey: `[${userAuthority.secretKey.toString()}]`,
        partnerAuthorityPublicKey : partnerAuthority.publicKey.toBase58(),
        partnerAuthorityPrivateKey: `[${partnerAuthority.secretKey.toString()}]`
    }

    Object.keys(outData).forEach(key => {
        outData[key] = outData[key].toString();
    })

    console.log(JSON.stringify(outData, null, 2));

    await fsp.writeFile(path.join(__dirname, "accounts.json"), JSON.stringify(outData, null, 2), 'utf8')

}  

init();