/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.GroupTheory.Perm.Certificates.Families
public import TauCeti.GroupTheory.Perm.Certificates.Search
public import TauCeti.Probability.FiniteSeed.Law

/-!
# Raw-input acceptance and the runner's uniform probability law

Both explicit families use the same binary parser and verifier as arbitrary
inputs. A constant candidate generator succeeds on its first trial. For a
general candidate generator, the uniform seed law gives the exact failure
probability and the bound under an explicit success-probability hypothesis.
-/

open MeasureTheory ProbabilityTheory
open TauCeti.BinaryCodec TauCeti.CertificateWire TauCeti.CertifiedPermutation
open TauCeti.SuccessfulFamilies TauCeti.BoundedRunner

@[expose] public section

namespace TauCeti.EndToEnd

/-- Encode all ordered-pair transpositions on the given degree. -/
def symmetricInput (degree : ℕ) : List Bool :=
  writeGroup ⟨degree, swaps degree (fun _ => true)⟩

/-- Encode all ordered-distinct-triple three-cycles on the given degree. -/
def alternatingInput (degree : ℕ) : List Bool :=
  writeGroup ⟨degree, triples degree (fun _ => true)⟩

theorem symmetric_accepted {degree : ℕ} (hdegree : 5 ≤ degree) :
    (verify (symmetricInput degree)
      (writeCertificate (symmetricCertificate hdegree))).isSome = true :=
  (verify_encoded_iff _ _).mpr (symmetricCertificate_valid hdegree)

theorem alternating_accepted {degree : ℕ} (hdegree : 6 ≤ degree) :
    (verify (alternatingInput degree)
      (writeCertificate (alternatingCertificate hdegree))).isSome = true :=
  (verify_encoded_iff _ _).mpr (alternatingCertificate_valid hdegree)

theorem symmetric_search_accepts {degree trials : ℕ} (hdegree : 5 ≤ degree)
    (seeds : Fin trials → Unit) (htrials : 0 < trials) :
    (searchInput (symmetricInput degree)
      (fun _ : Unit => writeCertificate (symmetricCertificate hdegree)) seeds).isSome = true :=
  run_isSome_of_all_success _ seeds htrials (fun _ => symmetric_accepted hdegree)

theorem alternating_search_accepts {degree trials : ℕ} (hdegree : 6 ≤ degree)
    (seeds : Fin trials → Unit) (htrials : 0 < trials) :
    (searchInput (alternatingInput degree)
      (fun _ : Unit => writeCertificate (alternatingCertificate hdegree)) seeds).isSome = true :=
  run_isSome_of_all_success _ seeds htrials (fun _ => alternating_accepted hdegree)

theorem search_unknown_uniformMeasure {S : Type*} [Fintype S] [Nonempty S]
    (input : List Bool) (candidate : S → List Bool) (trials : ℕ) :
    letI : MeasurableSpace (Fin trials → S) := ⊤
    ((PMF.uniformOfFintype (Fin trials → S)).toMeasure
      {seeds | searchInput input candidate seeds = none}).toReal =
      (1 - FiniteSeeds.uniformProbability S
        (fun seed => (verify input (candidate seed)).isSome = true)) ^ trials := by
  rw [← FiniteSeeds.uniformProbability_eq_uniformMeasure]
  exact run_unknown_probability (fun seed => verify input (candidate seed)) trials

theorem search_unknown_uniformMeasure_le_half_pow {S : Type*}
    [Fintype S] [Nonempty S] (input : List Bool) (candidate : S → List Bool)
    (R k : ℕ) (hR : 0 < R)
    (haccepts : 1 / (R : ℝ) ≤ FiniteSeeds.uniformProbability S
      (fun seed => (verify input (candidate seed)).isSome = true)) :
    letI : MeasurableSpace (Fin (k * R) → S) := ⊤
    ((PMF.uniformOfFintype (Fin (k * R) → S)).toMeasure
      {seeds | searchInput input candidate seeds = none}).toReal ≤ (1 / 2 : ℝ) ^ k := by
  rw [← FiniteSeeds.uniformProbability_eq_uniformMeasure]
  exact searchInput_unknown_le_half_pow input candidate R k hR haccepts


end TauCeti.EndToEnd
