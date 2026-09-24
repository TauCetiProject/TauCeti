/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import TauCeti.RingTheory.Henselian.Basic

/-!
# The ring of integers of a single adic completion

The ring of integers `𝒪_v` of the completion `K_v` of the fraction field of a Dedekind domain `R`
at a height-one prime `v` is a local ring, and this file collects what it is: its maximal ideal
contracts to `v` itself, its ideal filtration is the valuation filtration `K_v` induces on it, and
in the subspace topology it is a complete `𝔪`-adic — hence Henselian — local ring.

Everything here concerns one completion. The comparison of two completions along an extension
`w ∣ v` is `TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.adicCompletion_charZero`: a completion of a field of
  characteristic zero has characteristic zero.
* `algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers` (in the same namespace): an
  element of `R` maps to `K_v` through `K` as it does through `𝒪_v`.
* `IsDedekindDomain.HeightOneSpectrum.under_maximalIdeal_adicCompletionIntegers`: `v` is the
  prime lying under the maximal ideal of `𝒪_v`.
* `IsDedekindDomain.HeightOneSpectrum.map_asIdeal_adicCompletionIntegers`: `v` generates the
  maximal ideal of `𝒪_v`.
* `IsDedekindDomain.HeightOneSpectrum.mem_maximalIdeal_pow_iff`: membership in `𝔪 ^ n` is the
  valuation bound `≤ exp (-n)`, identifying the ideal filtration with the valuation filtration.
* `IsDedekindDomain.HeightOneSpectrum.exists_ne_zero_mem_maximalIdeal_valued_lt`: the maximal
  ideal contains a nonzero element whose valuation is below two prescribed nonzero bounds.
* `IsDedekindDomain.HeightOneSpectrum.isOpen_setOf_valued_le`: a closed valuation ball of `K_v`
  around the origin is open.
* `IsDedekindDomain.HeightOneSpectrum.isAdic_maximalIdeal_adicCompletionIntegers`: the subspace
  topology on `𝒪_v` is the `𝔪`-adic one.
* `IsDedekindDomain.HeightOneSpectrum.exists_valued_sub_le`: every element of `𝒪_v` is
  congruent to an element of `R` modulo any power of the maximal ideal, so `R` is dense in `𝒪_v`.
* `IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap_adicCompletionIntegers`: the
  corresponding density statement for the canonical map `R → 𝒪_v`.
* `IsDedekindDomain.HeightOneSpectrum.residueFieldEquivAdicCompletionIntegers`: consequently the
  residue field of `v` is the residue field of `𝒪_v`;
  `residueFieldEquivAdicCompletionIntegers_apply_mk` describes that isomorphism on a quotient
  representative.

## Implementation notes

`Mathlib.NumberTheory.NumberField.Completion.FinitePlace` supplies two instances used throughout —
`IsDiscreteValuationRing (v.adicCompletionIntegers K)` and
`(Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).IsRankOneDiscrete`. Both are stated there for an
arbitrary Dedekind domain and its fraction field, not for number fields, so nothing here depends on
number-field theory; they simply live in that module upstream. This note records the reason so the
placement of a `NumberTheory` import inside `RingTheory` is not mistaken for a layering slip.

## Motivation

These results are consumed by a semilocal comparison in explicit `2`-descent, which matches a
square class of a global étale algebra with its images in the completions, and by the local
valuation conditions that cut out congruence subgroups of the ideles. Nothing here mentions
a curve — each statement is about a Dedekind domain and one of its completions.

## Provenance

Adapted, with the author's proof, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/Mathlib/Basic.lean` line 594, and
`EllipticCurves/Mathlib/AdicCompletionExtension.lean` for the filtration and Henselian results,
and for `residueFieldEquivAdicCompletionIntegers` and the approximation modulo the maximal ideal
behind it, which `exists_valued_sub_le` generalizes to every power of the maximal ideal.
The source states the contraction with `Ideal.comap` of an `algebraMap`; Mathlib spells that
`Ideal.under`, which is used here.
-/

public section

open WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The completion of a field of characteristic zero at a height-one prime has characteristic
zero, since the field embeds into it. -/
instance adicCompletion_charZero [CharZero K] (v : HeightOneSpectrum R) :
    CharZero (v.adicCompletion K) :=
  charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective

/-- The prime of `R` lying under the maximal ideal of the ring of integers of the completion of
`K` at `v` is `v` itself. -/
@[simp]
lemma under_maximalIdeal_adicCompletionIntegers (v : HeightOneSpectrum R) :
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)).under R = v.asIdeal := by
  ext x
  rw [Ideal.under_def, Ideal.mem_comap, ← valuation_lt_one_iff_mem (K := K)]
  -- `v.adicCompletionIntegers K` is by definition `Valued.v.valuationSubring`, which is what lets
  -- `Valuation.mem_maximalIdeal_iff` apply here.
  refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion K)
    (WithZero (Multiplicative ℤ))))).trans ?_
  rw [algebraMap_adicCompletionIntegers_apply, valuedAdicCompletion_eq_valuation']

section SingleCompletion

variable (v : HeightOneSpectrum R)

/-- An element of `R`, mapped to `K_v` through `K`, is the image of its image in `𝒪_v`. -/
@[simp]
theorem algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers (r : R) :
    algebraMap K (v.adicCompletion K) (algebraMap R K r) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
        (algebraMap R (v.adicCompletionIntegers K) r) := by
  rw [ValuationSubring.algebraMap_apply, algebraMap_adicCompletionIntegers_apply,
    algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self_apply]

/-- An irreducible element of the ring of integers of a completion has valuation `exp (-1)`. -/
theorem valued_algebraMap_eq_exp_neg_one_of_irreducible {π : v.adicCompletionIntegers K}
    (hπ : Irreducible π) :
    Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) = exp (-1) := by
  -- `v.adicCompletionIntegers K` is by definition `Valued.v.valuationSubring`, which is what lets
  -- `π`'s maximal ideal be retyped as an ideal of the valuation subring here.
  have hgen : IsLocalRing.maximalIdeal (Valued.v : Valuation (v.adicCompletion K)
      ℤᵐ⁰).valuationSubring = Ideal.span {π} := hπ.maximalIdeal_eq
  have huni := Valuation.isUniformizer_of_maximalIdeal_eq_span
    (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)) hgen
  rwa [Valuation.IsUniformizer.iff,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective K)] at huni

/-- The height-one prime `v` generates the maximal ideal of the ring of integers of the
completion at `v`. -/
@[simp]
theorem map_asIdeal_adicCompletionIntegers :
    Ideal.map (algebraMap R (v.adicCompletionIntegers K)) v.asIdeal =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap,
      ← Ideal.under_def, v.under_maximalIdeal_adicCompletionIntegers]
  · obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
    have hπmem : π ∈ v.asIdeal := by
      rw [← v.intValuation_lt_one_iff_mem, hπ]
      simp
    have hπval : Valued.v
        (algebraMap R (v.adicCompletionIntegers K) π : v.adicCompletion K) = exp (-1) := by
      rw [algebraMap_adicCompletionIntegers_apply, valuedAdicCompletion_eq_valuation',
        valuation_of_algebraMap, hπ]
    have hπuni : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).IsUniformizer
        (algebraMap R (v.adicCompletionIntegers K) π : v.adicCompletion K) := by
      rwa [Valuation.IsUniformizer.iff,
        Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
          (v.valuedAdicCompletion_surjective K)]
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible
      (v.adicCompletionIntegers K)
    have hϖuni : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).IsUniformizer
        (ϖ : v.adicCompletion K) :=
      Valuation.isUniformizer_of_maximalIdeal_eq_span _ hϖ.maximalIdeal_eq
    rw [hϖ.maximalIdeal_eq]
    have hassoc : Associated ϖ (algebraMap R (v.adicCompletionIntegers K) π) :=
      Valuation.associated_of_isUniformizer hϖuni hπuni
    rw [Ideal.span_singleton_eq_span_singleton.mpr hassoc]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
      (Ideal.mem_map_of_mem _ hπmem))

/-- An element of `𝒪_v` lies in the `n`-th power of the maximal ideal exactly when its valuation
is at most `exp (-n)`.

This identifies the ideal filtration of `𝒪_v` with the valuation filtration it inherits from
`K_v`, which is what makes the subspace topology visibly `𝔪`-adic below. -/
@[simp]
theorem mem_maximalIdeal_pow_iff {x : v.adicCompletionIntegers K} {n : ℕ} :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n ↔
      Valued.v (x : v.adicCompletion K) ≤ exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hint := Valuation.valuationSubring.integers (v := (Valued.v : Valuation
    (v.adicCompletion K) ℤᵐ⁰))
  have hπn : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) ^ n =
      exp (-(n : ℤ)) := by
    rw [v.valued_algebraMap_eq_exp_neg_one_of_irreducible hπ, ← exp_nsmul]
    simp
  rw [← hπn]
  exact Set.ext_iff.mp (hint.maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow hπ n) x

/-- The maximal ideal of the ring of integers of an adic completion contains a nonzero element
whose valuation is below the valuations of `a` and `b`, and below `1`. -/
theorem exists_ne_zero_mem_maximalIdeal_valued_lt {a b : v.adicCompletionIntegers K}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    ∃ s : v.adicCompletionIntegers K,
      s ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ∧ s ≠ 0 ∧
        Valued.v (s : v.adicCompletion K) < Valued.v (a : v.adicCompletion K) ∧
        Valued.v (s : v.adicCompletion K) < Valued.v (b : v.adicCompletion K) ∧
        Valued.v (s : v.adicCompletion K) < 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hπv : Valued.v (π : v.adicCompletion K) = exp (-1) := by
    rw [← Algebra.algebraMap_ofSubsemiring_apply
      (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).valuationSubring π]
    exact v.valued_algebraMap_eq_exp_neg_one_of_irreducible hπ
  have haval0 : Valued.v (a : v.adicCompletion K) ≠ 0 := by
    simp only [ne_eq, _root_.map_eq_zero, ZeroMemClass.coe_eq_zero]
    exact ha0
  have hbval0 : Valued.v (b : v.adicCompletion K) ≠ 0 := by
    simp only [ne_eq, _root_.map_eq_zero, ZeroMemClass.coe_eq_zero]
    exact hb0
  obtain ⟨n, hna, hnb⟩ := exists_exp_neg_natCast_lt_and_lt haval0 hbval0
  let s : v.adicCompletionIntegers K := π ^ (n + 1)
  have hsv : Valued.v (s : v.adicCompletion K) = exp (-((n + 1 : ℕ) : ℤ)) := by
    simp only [s]
    push_cast
    rw [map_pow, hπv, ← exp_nsmul, nsmul_eq_mul]
    congr 1
    omega
  have hsm : s ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    have h := v.mem_maximalIdeal_pow_iff (K := K) (x := s) (n := 1)
    rw [pow_one] at h
    apply h.mpr
    rw [hsv]
    exact exp_le_exp.mpr (by omega)
  have hs0 : s ≠ 0 := pow_ne_zero _ hπ.ne_zero
  refine ⟨s, hsm, hs0, ?_, ?_, ?_⟩
  · rw [hsv]
    exact (exp_lt_exp.mpr (by omega)).trans hna
  · rw [hsv]
    exact (exp_lt_exp.mpr (by omega)).trans hnb
  · rw [hsv, ← exp_zero, exp_lt_exp]
    omega

/-! ### `𝒪_v` is a complete adic Henselian local ring

The subspace topology `𝒪_v` inherits from `K_v` is the `𝔪`-adic one, and `𝒪_v` is closed in the
complete field `K_v`, hence complete. Being complete for the `𝔪`-adic topology it is `𝔪`-adically
complete, and a local ring that is complete with respect to its maximal ideal is Henselian.
-/

/-- The ring of integers of an adic completion is a topological ring, as a subring of `K_v`. -/
instance isTopologicalRing_adicCompletionIntegers :
    IsTopologicalRing (v.adicCompletionIntegers K) :=
  inferInstanceAs (IsTopologicalRing
    (Valued.v (R := v.adicCompletion K)).valuationSubring.toSubring)

/-- **A closed valuation ball of `K_v` around the origin is open.**  The valuation of `K_v` is
surjective onto `ℤᵐ⁰`, so every nonzero bound is attained and the ball is the closed ball around a
point, which `Valued.isOpen_closedBall` shows is open. -/
theorem isOpen_setOf_valued_le {γ : ℤᵐ⁰} (hγ : γ ≠ 0) :
    IsOpen {z : v.adicCompletion K | Valued.v z ≤ γ} := by
  obtain ⟨z, hz⟩ := v.valuedAdicCompletion_surjective K γ
  have hr0 : Valued.v.restrict z ≠ 0 := by
    rw [ne_eq, Valuation.restrict_eq_zero_iff, hz]
    exact hγ
  have h : {y : v.adicCompletion K | Valued.v y ≤ γ} =
      {y : v.adicCompletion K | Valued.v.restrict y ≤ Valued.v.restrict z} := by
    ext y
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Valuation.restrict_le_iff, hz]
  rw [h]
  exact Valued.isOpen_closedBall _ hr0

/-- **Each power of the maximal ideal of `𝒪_v` is open**: `𝔪 ^ n` is the preimage under the
inclusion `𝒪_v → K_v` of a closed valuation ball, and those are open. -/
theorem isOpen_maximalIdeal_pow_adicCompletionIntegers (n : ℕ) :
    IsOpen ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :
      Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K)) := by
  have h : ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :
        Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K)) =
      (fun x : v.adicCompletionIntegers K ↦ (x : v.adicCompletion K)) ⁻¹'
        {y : v.adicCompletion K | Valued.v y ≤ exp (-(n : ℤ))} :=
    Set.ext fun x ↦ v.mem_maximalIdeal_pow_iff (K := K)
  rw [h]
  exact (v.isOpen_setOf_valued_le (K := K) exp_ne_zero).preimage continuous_subtype_val

/-- **Every neighbourhood of `0` in `𝒪_v` contains a power of the maximal ideal.** A neighbourhood
is cut out by a valuation bound, and `exp` takes some integer below that bound; the corresponding
`𝔪 ^ n` is then undercut by it. -/
theorem exists_maximalIdeal_pow_subset_of_mem_nhds {s : Set (v.adicCompletionIntegers K)}
    (hs : s ∈ nhds 0) : ∃ n : ℕ, ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :
      Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K)) ⊆ s := by
  obtain ⟨t, ht, hts⟩ := mem_nhds_subtype _ _ _ |>.mp hs
  rw [ZeroMemClass.coe_zero] at ht
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp ht
  obtain ⟨m, hm⟩ : ∃ m : ℤ, exp m < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
    refine ⟨log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) - 1, ?_⟩
    conv_rhs => rw [← exp_log (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)]
    exact exp_lt_exp.mpr (by lia)
  refine ⟨(-m).toNat, fun x hx ↦ hts ?_⟩
  refine Set.mem_preimage.mpr (hγ ?_)
  have h1 := v.mem_maximalIdeal_pow_iff (K := K) |>.mp hx
  refine Set.mem_ofPred.mpr ((Valuation.restrict_lt_iff_lt_embedding (v := Valued.v)).mpr
    (h1.trans_lt ?_))
  calc exp (-(((-m).toNat : ℤ))) ≤ exp m := exp_le_exp.mpr (by lia)
    _ < _ := hm

/-- The subspace topology on the ring of integers `𝒪_v` of an adic completion is the `𝔪`-adic
topology of its maximal ideal. -/
theorem isAdic_maximalIdeal_adicCompletionIntegers :
    IsAdic (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :=
  isAdic_iff.mpr ⟨isOpen_maximalIdeal_pow_adicCompletionIntegers (K := K) v,
    fun _ hs ↦ exists_maximalIdeal_pow_subset_of_mem_nhds (K := K) v hs⟩

/-- `𝒪_v` is complete: it is a closed subset of the complete field `K_v`. -/
instance completeSpace_adicCompletionIntegers : CompleteSpace (v.adicCompletionIntegers K) :=
  (Valued.isClosed_valuationSubring (v.adicCompletion K)).completeSpace_coe

/-- `𝒪_v` is a uniform additive group, as an additive subgroup of `K_v`. -/
instance isUniformAddGroup_adicCompletionIntegers :
    IsUniformAddGroup (v.adicCompletionIntegers K) :=
  ((Valued.v (R := v.adicCompletion K)).valuationSubring.toSubring.toAddSubgroup).isUniformAddGroup

/-- `𝒪_v` is `𝔪`-adically complete: its topology is the `𝔪`-adic one and it is complete. -/
instance isAdicComplete_adicCompletionIntegers :
    IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K) :=
  -- `IsAdic` unfolds to an equality of topologies, so dot notation on it would resolve against
  -- `Eq`; the lemma is `protected` and must be named in full.
  (IsAdic.isAdicComplete_iff (v.isAdic_maximalIdeal_adicCompletionIntegers (K := K))).mpr
    ⟨inferInstance, inferInstance⟩

/-- **`R` is dense in `𝒪_v`**: every element of the ring of integers of the completion is
congruent to an element of `R` modulo any power `𝔪 ^ n` of the maximal ideal. -/
theorem exists_valued_sub_le (x : v.adicCompletionIntegers K) (n : ℕ) :
    ∃ a : R, Valued.v ((x : v.adicCompletion K) - algebraMap R (v.adicCompletion K) a) ≤
      exp (-(n : ℤ)) := by
  -- the elements of `𝒪_v` congruent to `x` modulo `𝔪 ^ n` form an open subset of `K_v`
  let U : Set (v.adicCompletionIntegers K) := (· - x) ⁻¹'
    ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :
      Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K))
  have hU : IsOpen (((↑) : v.adicCompletionIntegers K → v.adicCompletion K) '' U) :=
    (Valued.isOpen_valuationSubring _).isOpenMap_subtype_val _
      ((v.isOpen_maximalIdeal_pow_adicCompletionIntegers n).preimage (continuous_sub_right x))
  -- so it contains an element `z` of `K`, which is then integral at `v`
  obtain ⟨z, y, hy, hyz⟩ := (denseRange_algebraMap (K := K) v).exists_mem_open hU
    ⟨x, x, by simp [U], rfl⟩
  have hz : v.valuation K z ≤ 1 := by
    have hy1 : Valued.v (algebraMap K (v.adicCompletion K) z) ≤ 1 :=
      hyz ▸ (mem_adicCompletionIntegers R K v).mp y.2
    rwa [algebraMap_adicCompletion, Function.comp_apply, valuedAdicCompletion_eq_valuation'] at hy1
  -- and `z` is approximated by an element of `R`
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hz (Units.mk0 (exp (-(n : ℤ))) exp_ne_zero)
  refine ⟨a, ?_⟩
  have hxy : Valued.v ((x : v.adicCompletion K) - y) ≤ exp (-(n : ℤ)) := by
    have hy' := (v.mem_maximalIdeal_pow_iff (K := K)).mp hy
    rwa [AddSubgroupClass.coe_sub, Valuation.map_sub_swap] at hy'
  have hza : Valued.v ((y : v.adicCompletion K) - algebraMap R (v.adicCompletion K) a) ≤
      exp (-(n : ℤ)) := by
    rw [hyz, IsScalarTower.algebraMap_apply R K (v.adicCompletion K), ← map_sub,
      algebraMap_adicCompletion, Function.comp_apply, valuedAdicCompletion_eq_valuation',
      Algebra.algebraMap_self, RingHom.id_apply, Valuation.map_sub_swap]
    exact ha.le
  rw [← sub_add_sub_cancel _ (y : v.adicCompletion K)]
  exact Valuation.map_add_le _ hxy hza

/-- **`R` is dense in the ring of integers of its completion at `v`.** Equivalently, every
neighbourhood of an element of `𝒪_v` contains the image of an element of `R`. -/
theorem denseRange_algebraMap_adicCompletionIntegers :
    DenseRange (algebraMap R (v.adicCompletionIntegers K)) := by
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro x
  rw [mem_closure_iff_nhds']
  intro U hU
  have hzero : (fun z : v.adicCompletionIntegers K ↦ x - z) ⁻¹' U ∈ nhds 0 := by
    apply (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds
    simpa using hU
  obtain ⟨n, hn⟩ := v.exists_maximalIdeal_pow_subset_of_mem_nhds (K := K) hzero
  obtain ⟨a, ha⟩ := v.exists_valued_sub_le (K := K) x n
  refine ⟨⟨algebraMap R (v.adicCompletionIntegers K) a, ⟨a, rfl⟩⟩, ?_⟩
  have hdiff : x - algebraMap R (v.adicCompletionIntegers K) a ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n := by
    rw [v.mem_maximalIdeal_pow_iff (K := K)]
    push_cast [IsScalarTower.algebraMap_apply R (v.adicCompletionIntegers K)
      (v.adicCompletion K)]
    exact ha
  simpa only [Set.mem_preimage, sub_sub_cancel] using hn hdiff

/-- The residue field of `v` maps isomorphically onto the residue field of the ring of integers of
the completion at `v`. -/
noncomputable def residueFieldEquivAdicCompletionIntegers :
    (R ⧸ v.asIdeal) ≃+*
      (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) := by
  refine RingEquiv.ofBijective (Ideal.quotientMap (IsLocalRing.maximalIdeal _)
    (algebraMap R (v.adicCompletionIntegers K))
    (le_of_eq (v.under_maximalIdeal_adicCompletionIntegers (K := K)).symm)) ⟨?_, ?_⟩
  · exact Ideal.quotientMap_injective'
      (le_of_eq (v.under_maximalIdeal_adicCompletionIntegers (K := K)))
  · intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := v.exists_valued_sub_le (K := K) x 1
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Ideal.quotientMap_mk]
    refine Ideal.Quotient.eq.mpr ?_
    refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion K)
      ℤᵐ⁰))).mpr ?_
    push_cast [IsScalarTower.algebraMap_apply R (v.adicCompletionIntegers K)
      (v.adicCompletion K)]
    rw [Valuation.map_sub_swap]
    exact ha.trans_lt (by simp)

/-- **The residue-field equivalence on a quotient representative.** This is the characterization
consumers should use; the equivalence's construction as an `Ideal.quotientMap` is an implementation
detail and should not be unfolded. -/
@[simp]
theorem residueFieldEquivAdicCompletionIntegers_apply_mk (a : R) :
    v.residueFieldEquivAdicCompletionIntegers (K := K) (Ideal.Quotient.mk v.asIdeal a) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
        (algebraMap R (v.adicCompletionIntegers K) a) := (rfl)

end SingleCompletion

end IsDedekindDomain.HeightOneSpectrum

end
