/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.GroupTheory.Perm.Certificates.Runtime.Families
public import TauCeti.GroupTheory.Perm.Certificates.Regression
public meta import TauCeti.GroupTheory.Perm.Certificates.RuntimeFamilies
public meta import TauCeti.GroupTheory.Perm.Certificates.Regression

/-!
# Executable regressions for the uniform TM2 runtime

These checks compare the proof-erased runtime with the canonical verifier,
exercise malformed inputs and first-success ordering, and execute a primitive
TM2 program. The universal correctness and transition bounds are proved in the
runtime modules; none of these evaluations is used as a proof.
-/

@[expose] public section

namespace TauCeti.RuntimeRegression

open Computability Turing

#eval show IO Unit from do
  let sInput := EndToEnd.symmetricInput 5
  let sBits := UniformFamilies.symmetricCandidate sInput []
  let aInput := EndToEnd.alternatingInput 6
  let aBits := UniformFamilies.alternatingCandidate aInput []
  let doubleBits := CertificateWire.writeCertificate
    { ExecutableRegression.symmetricFive with
      claim := CertifiedPermutation.Claim.doublyTransitive, cycleFactors := () }
  let duplicateTable : Fin 3 → Fin 3 := ![0, 0, 2]
  let shortBits := (List.range 4).flatMap fun n =>
    (List.range (2 ^ n)).map fun value => BinaryCodec.writeBits n value
  let constantRun := (flip bind (TM2.step (BitMachines.constProg [true, false])))^[5]
    (some (⟨some 0, none, BitMachines.stks [true, false, true] [] [] [] []⟩ :
      BitMachines.Cfg BitMachines.Stk (Fin 2)))
  let tests : List (String × Bool) := [
    ("uniform symmetric writer",
      decide (sBits = CertificateWire.writeCertificate ExecutableRegression.symmetricFive)),
    ("uniform alternating writer",
      decide (aBits = CertificateWire.writeCertificate ExecutableRegression.alternatingSix)),
    ("symmetric degree six",
      decide (UniformFamilies.symmetricCandidate (EndToEnd.symmetricInput 6) [] =
        CertificateWire.writeCertificate
          (SuccessfulFamilies.symmetricCertificate (degree := 6) (by decide)))),
    ("alternating degree seven",
      decide (UniformFamilies.alternatingCandidate (EndToEnd.alternatingInput 7) [] =
        CertificateWire.writeCertificate
          (SuccessfulFamilies.alternatingCertificate (degree := 7) (by decide)))),
    ("symmetric claim tag", decide (CertificateRuntime.verifyClaim sInput sBits = some 2)),
    ("alternating claim tag", decide (CertificateRuntime.verifyClaim aInput aBits = some 1)),
    ("double transitivity tag", decide (CertificateRuntime.verifyClaim sInput doubleBits = some 0)),
    ("empty certificate", (CertificateRuntime.verifyClaim sInput []).isNone),
    ("malformed input", (CertificateRuntime.verifyClaim [] sBits).isNone),
    ("truncated certificate", (CertificateRuntime.verifyClaim sInput sBits.dropLast).isNone),
    ("trailing certificate",
      (CertificateRuntime.verifyClaim sInput (sBits ++ [false])).isNone),
    ("trailing input", (CertificateRuntime.verifyClaim (sInput ++ [false]) sBits).isNone),
    ("reserved claim", (CertificateRuntime.verifyClaim sInput [true, true]).isNone),
    ("incorrect odd claim", (CertificateRuntime.verifyClaim aInput
      (CertificateWire.writeCertificate ExecutableRegression.incorrectOddClaim)).isNone),
    ("incorrect even claim", (CertificateRuntime.verifyClaim sInput
      (CertificateWire.writeCertificate ExecutableRegression.incorrectEvenClaim)).isNone),
    ("duplicate table", (BinaryCodec.readAll (CertificateRuntime.readTable 3)
      (BinaryCodec.writeVector BinaryCodec.writeIndex duplicateTable)).isNone),
    ("bounded index parser agreement", (List.range 9).all fun bound =>
      shortBits.all fun bits => decide (BinaryCodec.indexParser bound bits =
        (BinaryCodec.readIndex bound bits).map fun q => (q.1.val, q.2))),
    ("binary saturation", decide
      ((List.replicate 4096 true).foldl (BinaryCodec.binaryStep 3) 0 = 3)),
    ("malformed verifier agreement", shortBits.all fun input =>
      shortBits.all fun bits => decide (CertificateRuntime.verifyClaim input bits =
        (CertificateWire.verify input bits).map fun r =>
          CertificateRuntime.claimCode r.result.certificate.claim)),
    ("first accepted double certificate",
      decide (CertificateRuntime.scan sInput [doubleBits, sBits] = some doubleBits)),
    ("first accepted symmetric certificate",
      decide (CertificateRuntime.scan sInput [sBits, doubleBits] = some sBits)),
    ("skip rejected certificate",
      decide (CertificateRuntime.scan sInput [[true, true], sBits] = some sBits)),
    ("all rejected certificates",
      (CertificateRuntime.scan sInput [[], [true, true]]).isNone),
    ("zero trials", (CertificateRuntime.search (fun _ _ => sBits) sInput []).isNone),
    ("zero seed cap",
      (CertificateRuntime.search (fun _ _ => sBits) sInput ([[true]].take 0)).isNone),
    ("ignore seeds beyond cap", decide (CertificateRuntime.search
      (fun _ seed => if seed.headD false then sBits else doubleBits)
      sInput ([[false], [true]].take 1) = some doubleBits)),
    ("constant TM halts after five transitions",
      constantRun.any fun c => c.l.isNone && decide (c.var = none) &&
        decide (c.stk .main = [true, false]) &&
        [BitMachines.Stk.s₁, .s₂, .s₃, .s₄].all fun k => decide (c.stk k = [])),
    ("symmetric generator ignores seed",
      decide (UniformFamilies.symmetricCandidate sInput [true, false] = sBits)),
    ("alternating generator ignores seed",
      decide (UniformFamilies.alternatingCandidate aInput [false, true] = aBits)),
    ("malformed degree is zero", decide (UniformFamilies.degreeOf [true, true] = 0))]
  for test in tests do
    unless test.2 = true do
      throw (IO.userError s!"Runtime regression failed: {test.1}")
  IO.println s!"Runtime regressions: {tests.length} passed."

end TauCeti.RuntimeRegression
