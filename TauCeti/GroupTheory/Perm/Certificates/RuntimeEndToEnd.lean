/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.GroupTheory.Perm.Certificates.RuntimeSearch
public import TauCeti.GroupTheory.Perm.Certificates.EndToEnd

/-!
# A certified search machine with a uniform-seed probability bound

The output contains both the checked claim tag and the first accepted
certificate. One finite-control TM2 machine works for every raw input and unary
confidence parameter. Its polynomial transition bound includes the encoded seed
input, candidate generation, verification, and the bounded traversal.

Soundness holds for every seed stream. The probability theorem separately
assumes a positive polynomial trial scale and its reciprocal lower bound on the
fraction of accepted seeds. It makes no sampling claim for arbitrary groups.
-/

@[expose] public section

namespace TauCeti.CertificateRuntime

open Computability BitEncoding Turing MeasureTheory ProbabilityTheory

/-- Return the claim tag and the first accepted certificate, or `none`. -/
def boundedSearchResult (candidate : List Bool → List Bool → List Bool)
    (R : Polynomial ℕ) (input : List Bool) (k : ℕ) (seeds : List (List Bool)) :
    Option (ℕ × List Bool) :=
  (boundedSearch candidate R input k seeds).bind fun certificate =>
    (verifyClaim input certificate).map fun tag => (tag, certificate)

@[fun_prop] theorem polyTime_boundedSearchResult
    (candidate : List Bool → List Bool → List Bool) (R : Polynomial ℕ)
    (hc : PolyTime (fun p : List Bool × List Bool => candidate p.1 p.2)) :
    PolyTime (fun p : List Bool × ℕ × List (List Bool) =>
      boundedSearchResult candidate R p.1 p.2.1 p.2.2) := by
  unfold boundedSearchResult
  fun_prop

theorem boundedSearchResult_eq_none_iff
    (candidate : List Bool → List Bool → List Bool) (R : Polynomial ℕ)
    (input : List Bool) (k : ℕ) (seeds : List (List Bool)) :
    boundedSearchResult candidate R input k seeds = none ↔
      boundedSearch candidate R input k seeds = none := by
  cases hs : boundedSearch candidate R input k seeds with
  | none => simp [boundedSearchResult, hs]
  | some certificate =>
    obtain ⟨_, _, _, r, hr, _⟩ := search_sound candidate input _ certificate hs
    simp [boundedSearchResult, hs, verifyClaim_eq, hr]

/-- The returned claim concerns the supplied raw input and a candidate from the capped list. -/
theorem boundedSearchResult_sound
    (candidate : List Bool → List Bool → List Bool) (R : Polynomial ℕ)
    (input : List Bool) (k : ℕ) (seeds : List (List Bool))
    (tag : ℕ) (certificate : List Bool)
    (h : boundedSearchResult candidate R input k seeds = some (tag, certificate)) :
    ∃ seed ∈ seeds.take (k * R.eval input.length),
      candidate input seed = certificate ∧
      ∃ r : CertificateWire.VerifiedInput,
        CertificateWire.verify input certificate = some r ∧
        BinaryCodec.readAll CertificateWire.readGroup input =
          some ⟨r.degree, r.generators⟩ ∧
        claimCode r.result.certificate.claim = tag ∧
        CertifiedPermutation.ClaimHolds r.result.certificate := by
  obtain ⟨c, hc, hout⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨t, ht, he⟩ := Option.map_eq_some_iff.mp hout
  have htag : t = tag := congrArg Prod.fst he
  have hcert : c = certificate := congrArg Prod.snd he
  subst c
  subst t
  obtain ⟨seed, hseed, he, _, _, _⟩ :=
    search_sound candidate input _ certificate hc
  obtain ⟨r, hr, htag, hsound⟩ := verifyClaim_sound input certificate tag ht
  exact ⟨seed, hseed, he, r, hr,
    CertificateWire.verify_input_matches input certificate r hr, htag, hsound⟩

/-- Encode a vector of fixed-length seeds as the list read by the machine. -/
def seedList {bits trials : ℕ} (seeds : Fin trials → Fin bits → Bool) :
    List (List Bool) :=
  List.ofFn fun i => List.ofFn (seeds i)

theorem seedList_length {bits trials : ℕ} (seeds : Fin trials → Fin bits → Bool) :
    (seedList seeds).length = trials := List.length_ofFn

theorem seedList_mem_length {bits trials : ℕ}
    (seeds : Fin trials → Fin bits → Bool) (seed : List Bool) (h : seed ∈ seedList seeds) :
    seed.length = bits := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
  exact List.length_ofFn

/-- The deterministic machine output for a fixed vector of uniformly sampled seeds. -/
def seededResult (candidate : List Bool → List Bool → List Bool)
    (R B : Polynomial ℕ) (input : List Bool) (k : ℕ)
    (seeds : Fin (k * R.eval input.length) → Fin (B.eval input.length) → Bool) :
    Option (ℕ × List Bool) :=
  boundedSearchResult candidate R input k (seedList seeds)

theorem seededResult_eq_none_iff
    (candidate : List Bool → List Bool → List Bool) (R B : Polynomial ℕ)
    (input : List Bool) (k : ℕ)
    (seeds : Fin (k * R.eval input.length) → Fin (B.eval input.length) → Bool) :
    seededResult candidate R B input k seeds = none ↔
      BoundedRunner.searchInput input
        (fun seed => candidate input (List.ofFn seed)) seeds = none := by
  rw [seededResult, boundedSearchResult_eq_none_iff, boundedSearch,
    List.take_of_length_le (by rw [seedList_length])]
  simp [search_eq_none_iff, seedList, BoundedRunner.searchInput,
    BoundedRunner.run_eq_none_iff]

/-- Exact failure probability under the finite uniform product law, including zero trials. -/
theorem seededResult_unknown_probability
    (candidate : List Bool → List Bool → List Bool) (R B : Polynomial ℕ)
    (input : List Bool) (k : ℕ) :
    FiniteSeeds.uniformProbability
      (Fin (k * R.eval input.length) → Fin (B.eval input.length) → Bool)
      (fun seeds => seededResult candidate R B input k seeds = none) =
      (1 - FiniteSeeds.uniformProbability (Fin (B.eval input.length) → Bool)
        (fun seed => (CertificateWire.verify input
          (candidate input (List.ofFn seed))).isSome = true)) ^ (k * R.eval input.length) := by
  have hevent :
      (fun seeds => seededResult candidate R B input k seeds = none) =
        (fun seeds => BoundedRunner.searchInput input
          (fun seed => candidate input (List.ofFn seed)) seeds = none) :=
    funext fun seeds => propext (seededResult_eq_none_iff candidate R B input k seeds)
  rw [hevent]
  exact BoundedRunner.run_unknown_probability _ _

/-- Amplification uses the stated acceptance fraction and positive trial scale. -/
theorem seededResult_unknown_le_half_pow
    (candidate : List Bool → List Bool → List Bool) (R B : Polynomial ℕ)
    (input : List Bool) (k : ℕ) (hR : 0 < R.eval input.length)
    (haccepts : 1 / ((R.eval input.length : ℕ) : ℝ) ≤
      FiniteSeeds.uniformProbability (Fin (B.eval input.length) → Bool)
        (fun seed => (CertificateWire.verify input
          (candidate input (List.ofFn seed))).isSome = true)) :
    FiniteSeeds.uniformProbability
      (Fin (k * R.eval input.length) → Fin (B.eval input.length) → Bool)
      (fun seeds => seededResult candidate R B input k seeds = none) ≤ (1 / 2 : ℝ) ^ k := by
  rw [seededResult_unknown_probability]
  exact TauCeti.failure_pow_mul_le_half_pow
    (FiniteSeeds.uniformProbability_le_one _ _) _ _ hR haccepts

/-- The failure bound is the probability of the machine's failure event under
Mathlib's uniform probability measure on the complete seed vector. -/
theorem seededResult_unknown_uniformMeasure_le_half_pow
    (candidate : List Bool → List Bool → List Bool) (R B : Polynomial ℕ)
    (input : List Bool) (k : ℕ) (hR : 0 < R.eval input.length)
    (haccepts : 1 / ((R.eval input.length : ℕ) : ℝ) ≤
      FiniteSeeds.uniformProbability (Fin (B.eval input.length) → Bool)
        (fun seed => (CertificateWire.verify input
          (candidate input (List.ofFn seed))).isSome = true)) :
    letI : MeasurableSpace
        (Fin (k * R.eval input.length) → Fin (B.eval input.length) → Bool) := ⊤
    ((PMF.uniformOfFintype
        (Fin (k * R.eval input.length) → Fin (B.eval input.length) → Bool)).toMeasure
      {seeds | seededResult candidate R B input k seeds = none}).toReal ≤
        (1 / 2 : ℝ) ^ k := by
  rw [← FiniteSeeds.uniformProbability_eq_uniformMeasure]
  exact seededResult_unknown_le_half_pow candidate R B input k hR haccepts

/-- A fixed finite-control machine has a polynomial transition bound in `input.length + k`,
including the external seed stream and the returned certificate and claim. -/
theorem seededResult_tm2
    (candidate : List Bool → List Bool → List Bool) (R B : Polynomial ℕ)
    (hc : PolyTime (fun p : List Bool × List Bool => candidate p.1 p.2)) :
    ∃ M : TM2ComputableAux Bool Bool, ∃ P : Polynomial ℕ,
      ∀ (input : List Bool) (k : ℕ)
        (seeds : Fin (k * R.eval input.length) → Fin (B.eval input.length) → Bool),
        Nonempty (TM2OutputsInTime M.tm
          ((enc (input, k, seedList seeds)).map M.inputAlphabet.symm)
          (some ((enc (seededResult candidate R B input k seeds)).map M.outputAlphabet.symm))
          (P.eval (input.length + k))) := by
  have hm : Nonempty (TM2ComputableInPolyTime enc enc
      (fun p : List Bool × ℕ × List (List Bool) =>
        boundedSearchResult candidate R p.1 p.2.1 p.2.2)) := by
    simpa only [PolyTime] using polyTime_boundedSearchResult candidate R hc
  obtain ⟨M⟩ := hm
  refine ⟨M.toTM2ComputableAux, M.time.comp (seedEnvelope R B), ?_⟩
  intro input k seeds
  have h := M.outputsFun (input, k, seedList seeds)
  refine ⟨⟨h.toEvalsTo, h.steps_le_m.trans ?_⟩⟩
  rw [Polynomial.eval_comp]
  exact Polynomial.eval_le_eval M.time
    (length_enc_searchInput_le R B input k (seedList seeds)
      (le_of_eq (seedList_length seeds))
      (fun seed hseed => le_of_eq (seedList_mem_length seeds seed hseed)))

end TauCeti.CertificateRuntime
