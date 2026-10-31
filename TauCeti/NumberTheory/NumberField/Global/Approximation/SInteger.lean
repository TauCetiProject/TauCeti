/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import TauCeti.NumberTheory.NumberField.FinitePlace
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic

/-!
# Simultaneous approximation by `S`-integers

Let `K` be a number field and `S` a finite set of finite places of `K`. Given an element `γ v` of
`K` for each place `v` in `S` and for each infinite place, some `ξ ∈ K` is integral at every finite
place outside `S`, satisfies `|ξ + γ v|_v ≤ 1` at every `v ∈ S`, and satisfies `|ξ + γ v|_v ≤ A` at
every infinite place, where `A` depends on `K` alone and not on `S` or on the `γ v`
(`NumberField.exists_forall_apply_add_le`). Thus `-γ` is approximated by a single `S`-integer at
the places of `S` and at the infinite places at once, with a uniform loss at the infinite places.

This is the approximation step in the proof of Evertse's lemma (Bombieri–Gubler, Lemma 7.5.29),
where a basis is corrected by `S`-integral multiples of earlier vectors; the constant is uniform
in `S` and in the targets because the lemma is applied to forms which change with a parameter.

The proof has two halves.
* At the finite places, `NumberField.exists_forall_finitePlace_apply_add_le_one` is strong
  approximation for the finite adeles,
  `IsDedekindDomain.FiniteAdeleRing.exists_forall_sub_algebraMap_mem_adicCompletionIntegers`,
  applied to the finite adele with component `-γ v` at the places of `S` and `0` elsewhere.
* At the infinite places, `NumberField.exists_integer_forall_infinitePlace_add_le` translates by an
  algebraic integer `ω`, which changes no finite condition, so that the vector of the `ω + γ v`
  lands in the fundamental domain of the Minkowski lattice of `𝓞 K`. The constant is the sum of
  the norms of the embedded integral basis `mixedEmbedding.latticeBasis K`.

## Main results

* `NumberField.exists_forall_finitePlace_apply_add_le_one`: an element of `K` integral outside `S`
  and within `1` of `-γ v` at every place of `S`.
* `NumberField.exists_integer_forall_infinitePlace_add_le`: an algebraic integer within
  `∑ i, ‖mixedEmbedding.latticeBasis K i‖` of `-γ v` at every infinite place.
* `NumberField.exists_forall_apply_add_le`: the two combined, with a constant chosen before `S`
  and the targets.

## References

* J.-H. Evertse, *An improvement of the quantitative Subspace theorem*, Compositio Math. 101
  (1996), 225–311.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  Lemma 7.5.29.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Approximation at finitely many finite places by an element integral elsewhere.** For a finite
set `S` of finite places and targets `γ v ∈ K`, some `ξ ∈ K` is integral at every finite place
outside `S` and satisfies `|ξ + γ v|_v ≤ 1` at every place `v` of `S`. -/
theorem exists_forall_finitePlace_apply_add_le_one (S : Finset (FinitePlace K))
    (γ : FinitePlace K → K) :
    ∃ ξ : K, (∀ v : FinitePlace K, v ∉ S → v ξ ≤ 1) ∧ ∀ v ∈ S, v (ξ + γ v) ≤ 1 := by
  classical
  have hfin : {w : HeightOneSpectrum (𝓞 K) | FinitePlace.mk w ∈ S}.Finite :=
    S.finite_toSet.preimage fun _ _ _ _ h ↦ FinitePlace.mk_eq_iff.mp h
  -- The finite adele with component `-γ v` at the places of `S` and `0` elsewhere.
  let a : FiniteAdeleRing (𝓞 K) K := RestrictedProduct.mk
    (fun w ↦ if FinitePlace.mk w ∈ S then
      algebraMap K (w.adicCompletion K) (-γ (FinitePlace.mk w)) else 0)
    (by
      filter_upwards [hfin.compl_mem_cofinite] with w hw
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hw
      simp only [hw, ite_false]
      exact zero_mem _)
  have ha (w : HeightOneSpectrum (𝓞 K)) : a w = if FinitePlace.mk w ∈ S then
      algebraMap K (w.adicCompletion K) (-γ (FinitePlace.mk w)) else 0 :=
    RestrictedProduct.mk_apply (i := w) ..
  obtain ⟨x, hx⟩ := FiniteAdeleRing.exists_forall_sub_algebraMap_mem_adicCompletionIntegers a
  refine ⟨x, fun v hv ↦ ?_, fun v hv ↦ ?_⟩
  -- Negating `a v - x ∈ 𝒪_v` gives `x - a v ∈ 𝒪_v`, which reads `x` outside `S` and
  -- `x + γ v` on `S`.
  all_goals
    rw [← FinitePlace.mk_maximalIdeal v, FinitePlace.mk_apply_le_one_iff_algebraMap_mem]
    simpa [ha, hv] using neg_mem (hx v.maximalIdeal)

open scoped Classical in
/-- **Approximation at the infinite places by an algebraic integer.** For targets `γ v ∈ K` at
the infinite places, some `ω ∈ 𝓞 K` satisfies `|ω + γ v|_v ≤ A` at every infinite place `v`, where
`A = ∑ i, ‖mixedEmbedding.latticeBasis K i‖` is the sum of the norms of the embedded integral
basis. -/
theorem exists_integer_forall_infinitePlace_add_le (γ : InfinitePlace K → K) :
    ∃ ω : 𝓞 K, ∀ v : InfinitePlace K,
      v (ω + γ v) ≤ ∑ i, ‖mixedEmbedding.latticeBasis K i‖ := by
  -- The point of the mixed space whose component at each infinite place `w` is `c w`, embedded
  -- by `w`, and its norm at `v`.
  let p : (InfinitePlace K → K) → mixedSpace K := fun c ↦
    (fun w ↦ embedding_of_isReal w.2 (c w.1), fun w ↦ w.1.embedding (c w.1))
  have hp (c : InfinitePlace K → K) (v : InfinitePlace K) : normAtPlace v (p c) = v (c v) := by
    by_cases hv : IsReal v
    · rw [normAtPlace_apply_of_isReal hv]
      exact norm_embedding_of_isReal hv (c v)
    · rw [normAtPlace_apply_of_isComplex (not_isReal_iff_isComplex.mp hv)]
      exact norm_embedding_eq v (c v)
  let b := mixedEmbedding.latticeBasis K
  let z := p γ
  -- The integral part of `z` with respect to `b` is the image of an algebraic integer `y`.
  have hfloor : ((ZSpan.floor b z : Submodule.span ℤ (Set.range b)) : mixedSpace K) ∈
      mixedEmbedding.integerLattice K := by
    rw [← mixedEmbedding.span_latticeBasis K]
    exact (ZSpan.floor b z).property
  obtain ⟨y, hy⟩ := hfloor
  replace hy : mixedEmbedding K (y : K) = ZSpan.floor b z := by simpa using hy
  refine ⟨-y, fun v ↦ ?_⟩
  have hfract : ZSpan.fract b z = p fun w ↦ ((-y : 𝓞 K) : K) + γ w := by
    rw [ZSpan.fract_apply, ← hy]
    ext w <;> simp [z, p, sub_eq_neg_add]
  calc v (((-y : 𝓞 K) : K) + γ v) = normAtPlace v (ZSpan.fract b z) := by
        rw [hfract]
        exact (hp (fun w ↦ ((-y : 𝓞 K) : K) + γ w) v).symm
    _ ≤ ‖ZSpan.fract b z‖ := by
        rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
        exact Finset.le_sup' (fun w ↦ normAtPlace w (ZSpan.fract b z)) (Finset.mem_univ v)
    _ ≤ ∑ i, ‖b i‖ := ZSpan.norm_fract_le b z

/-- **Simultaneous approximation by `S`-integers** (the approximation step of Evertse's lemma,
Bombieri–Gubler, Lemma 7.5.29). There is a constant `A`, depending only on `K`, such that for
every finite set `S` of finite places and all targets `γ`, some `ξ ∈ K` is integral at every finite
place outside `S`, satisfies `|ξ + γ v|_v ≤ 1` at every `v ∈ S` and `|ξ + γ v|_v ≤ A` at every
infinite place. The targets are indexed by the underlying absolute values of the places, so that
one family serves both kinds of place; its values elsewhere are irrelevant. -/
theorem exists_forall_apply_add_le :
    ∃ A : ℝ, ∀ (S : Finset (FinitePlace K)) (γ : AbsoluteValue K ℝ → K), ∃ ξ : K,
      (∀ v : FinitePlace K, v ∉ S → v ξ ≤ 1) ∧ (∀ v ∈ S, v (ξ + γ v.1) ≤ 1) ∧
        ∀ v : InfinitePlace K, v (ξ + γ v.1) ≤ A := by
  classical
  refine ⟨∑ i, ‖mixedEmbedding.latticeBasis K i‖, fun S γ ↦ ?_⟩
  obtain ⟨ξ, hξS, hξ⟩ := exists_forall_finitePlace_apply_add_le_one S fun v ↦ γ v.1
  obtain ⟨ω, hω⟩ := exists_integer_forall_infinitePlace_add_le fun v ↦ ξ + γ v.1
  have hω₁ (v : FinitePlace K) : v (ω : K) ≤ 1 := by
    rw [← FinitePlace.norm_embedding_eq, RingOfIntegers.coe_eq_algebraMap]
    exact FinitePlace.norm_le_one K v.maximalIdeal ω
  refine ⟨ξ + ω, fun v hv ↦ ?_, fun v hv ↦ ?_, fun v ↦ ?_⟩
  · exact (v.add_le _ _).trans (max_le (hξS v hv) (hω₁ v))
  · rw [add_right_comm]
    exact (v.add_le _ _).trans (max_le (hξ v hv) (hω₁ v))
  · rw [add_comm ξ, add_assoc]
    exact hω v

end NumberField
