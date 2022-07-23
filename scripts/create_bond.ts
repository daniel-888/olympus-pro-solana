// Migrations are an early feature. Currently, they're nothing more than this
// single deploy script that's invoked from the CLI, injecting a provider
// configured from the workspace's Anchor.toml.

import * as anchor from "@project-serum/anchor";
import { ASSOCIATED_TOKEN_PROGRAM_ID, TOKEN_PROGRAM_ID, MintLayout, AccountLayout } from "@solana/spl-token";
import {  Transaction, SystemProgram } from '@solana/web3.js';
import {Wallet} from "@project-serum/anchor/src/provider";
import { Program } from '@project-serum/anchor';
import { OlympusproSol } from '../target/types/olympuspro_sol';
import * as fsp from 'fs/promises';
import * as path from 'path';

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

const init = async() => {
    // Configure client to use the provider.
    anchor.setProvider(anchor.Provider.env());

    const accounts = JSON.parse(await fsp.readFile(path.join(__dirname, "accounts.json"), 'utf8'));
    // Add your deploy script here.
    const connection = anchor.getProvider().connection;
    const olympusDao = anchor.getProvider().wallet;

    const tokenAMint = new anchor.web3.PublicKey(accounts.tokenAMint);
    const tokenBMint =  new anchor.web3.PublicKey(accounts.tokenBMint);

    const partnerTokenA = new anchor.web3.PublicKey(accounts.partnerTokenA);
    const partnerTokenB = new anchor.web3.PublicKey(accounts.partnerTokenB);

    const olympusTokenA = new anchor.web3.PublicKey(accounts.olympusTokenA);
    const olympusTokenB = new anchor.web3.PublicKey(accounts.olympusTokenB);

    const userTokenA = new anchor.web3.PublicKey(accounts.userTokenA);
    const userTokenB = new anchor.web3.PublicKey(accounts.userTokenB);


    const program = anchor.workspace.OlympusproSol as Program<OlympusproSol>;
    const [olympusData, olympusDataBump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("olympus")], program.programId);
    const [treasury, treasuryBump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("treasury"), tokenAMint.toBuffer(), olympusDao.publicKey.toBuffer()], program.programId);
    const [payoutAccount, payoutAccountBump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("account"), treasury.toBuffer(), tokenAMint.toBuffer()], program.programId);
    const [daoPayoutAccount, daoPayoutAccountBump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("daoAccount"), tokenAMint.toBuffer()], program.programId);
    const [daoPrincipalAccount, daoPrincipalAccountBump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("daoAccount"), tokenBMint.toBuffer()], program.programId);
    const [principalAccount, principalAccountBump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("account"), treasury.toBuffer(), tokenBMint.toBuffer()], program.programId);
    const [bonder, bonderBump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("bonder"), treasury.toBuffer(), tokenBMint.toBuffer()], program.programId);


  const bond = anchor.web3.Keypair.generate();
  const nftMint = anchor.web3.Keypair.generate();
  const nftToken = anchor.web3.Keypair.generate();


    let [bondAccount, bondAccountBump] = await getBondAccount(bond.publicKey);

    const bondTx = await program.transaction.bonderDeposit(new anchor.BN(10), new anchor.BN(10), {
        accounts : {
        authority: olympusDao.publicKey,
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
        payer : olympusDao.publicKey,
        bonder,
        nftMint: nftMint.publicKey,
        nftToken: nftToken.publicKey,
        tokenAuthority: await getTokenAuthority(treasury),
        systemProgram: anchor.web3.SystemProgram.programId,
        tokenProgram: TOKEN_PROGRAM_ID,
        clock : anchor.web3.SYSVAR_CLOCK_PUBKEY,
        rent : anchor.web3.SYSVAR_RENT_PUBKEY
        }
    });

    bondTx.feePayer = olympusDao.publicKey;
    bondTx.recentBlockhash = (await anchor.getProvider().connection.getRecentBlockhash()).blockhash;
    bondTx.sign(bond, nftMint, nftToken);
    const signedTx2 = await olympusDao.signTransaction(bondTx);
    const txId2 = await anchor.getProvider().connection.sendRawTransaction(signedTx2.serialize())
    await anchor.getProvider().connection.confirmTransaction(txId2);

}  

init();