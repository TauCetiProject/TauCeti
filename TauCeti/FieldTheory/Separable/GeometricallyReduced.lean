/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.Flat.Basic

/-!
# Geometrically reduced field extensions are separably generated

Let `k` be a field of exponential characteristic `p` and `A` a commutative `k`-algebra which is
geometrically reduced, i.e. `AlgebraicClosure k ⊗[k] A` is reduced. Then the `p`-th powers of
`k`-linearly independent elements of `A` are again `k`-linearly independent. Indeed, if
`∑ cᵢ sᵢ ^ p = 0` with `cᵢ ∈ k`, choose `p`-th roots `dᵢ` of the `cᵢ` in the algebraic closure.
Then `∑ dᵢ ⊗ sᵢ` has `p`-th power `1 ⊗ ∑ cᵢ sᵢ ^ p = 0`, so it vanishes; since the `1 ⊗ sᵢ` are
linearly independent over the algebraic closure, every `dᵢ`, hence every `cᵢ`, is zero.

For a finitely generated field extension `K / k`, Mathlib's
`exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType` turns this
linear independence into a finite separating transcendence basis. Hence a finitely generated
geometrically reduced field extension is separably generated. Over a perfect field every finitely
generated extension is separably generated, so the content lies in positive characteristic over
an imperfect field.

Reducedness after extending scalars to *any* algebraically closed field `L` suffices
(`Algebra.IsGeometricallyReduced.of_isReduced_tensorProduct`, in
`TauCeti.RingTheory.TensorProduct.Reduced`). In particular, a finitely generated field extension
`K / k` with `L ⊗[k] K` a domain is separably generated.

## Main results

* `TauCeti.linearIndepOn_pow_of_isGeometricallyReduced`: in a geometrically reduced algebra, the
  `p`-th powers of `k`-linearly independent elements are `k`-linearly independent.
* `TauCeti.exists_isTranscendenceBasis_and_isSeparable_of_isGeometricallyReduced`: a finitely
  generated geometrically reduced field extension has a finite separating transcendence basis.

## References

* [The Stacks project, Tag 030W](https://stacks.math.columbia.edu/tag/030W)
* S. Lang, *Introduction to Algebraic Geometry*, Chapter III, Section 1.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {k : Type*} [Field k]

/-- In a geometrically reduced commutative algebra over a field `k` of exponential characteristic
`p`, the `p`-th powers of `k`-linearly independent elements are `k`-linearly independent. -/
theorem linearIndepOn_pow_of_isGeometricallyReduced {A : Type*} [CommRing A] [Algebra k A]
    (p : ℕ) [ExpChar k p] [Algebra.IsGeometricallyReduced k A] {s : Set A}
    (hs : LinearIndepOn k id s) : LinearIndepOn k (· ^ p) s := by
  classical
  let K := AlgebraicClosure k
  -- A choice of `p`-th roots in the algebraic closure, with the root of `0` equal to `0`.
  have hroot (c : k) : ∃ d : K, d ^ p = algebraMap k K c :=
    IsAlgClosed.exists_pow_nat_eq _ (expChar_pos k p)
  let g : k → K := fun c ↦ (hroot c).choose
  have hg (c : k) : g c ^ p = algebraMap k K c := (hroot c).choose_spec
  have hg0 : g 0 = 0 := by
    simpa [(expChar_pos k p).ne'] using hg 0
  -- The vectors `1 ⊗ a`, `a ∈ s`, are linearly independent over the algebraic closure.
  have hs' : LinearIndepOn K (fun a : A ↦ (1 : K) ⊗ₜ[k] a) s :=
    Module.Flat.linearIndependent_one_tmul hs
  rw [linearIndepOn_iff] at hs' ⊢
  intro l hl hl0
  let l' : A →₀ K := l.mapRange g hg0
  have hsum : Finsupp.linearCombination K (fun a : A ↦ (1 : K) ⊗ₜ[k] a) l' =
      ∑ a ∈ l.support, g (l a) ⊗ₜ[k] a := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
    simp [Finsupp.sum, TensorProduct.smul_tmul']
  -- The combination `∑ g (l a) ⊗ a` has `p`-th power `1 ⊗ ∑ l a • a ^ p = 0`, so it vanishes.
  have hzero : ∑ a ∈ l.support, g (l a) ⊗ₜ[k] a = 0 := by
    rcases subsingleton_or_nontrivial (K ⊗[k] A) with _ | _
    · exact Subsingleton.elim _ _
    have := expChar_of_injective_algebraMap (algebraMap k (K ⊗[k] A)).injective p
    refine IsReduced.eq_zero _ ⟨p, ?_⟩
    rw [sum_pow_char]
    simp_rw [Algebra.TensorProduct.tmul_pow, hg, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at hl0
    rw [← TensorProduct.tmul_sum, hl0, TensorProduct.tmul_zero]
  have hl'0 : l' = 0 := by
    refine hs' l' ?_ (hsum.trans hzero)
    rw [Finsupp.mem_supported] at hl ⊢
    exact (Finset.coe_subset.2 Finsupp.support_mapRange).trans hl
  ext a
  have ha : g (l a) = 0 := by simpa [l'] using congr($hl'0 a)
  have := hg (l a)
  rw [ha, zero_pow (expChar_pos k p).ne', eq_comm, map_eq_zero] at this
  simpa using this

variable (k) (K : Type*) [Field K] [Algebra k K]

/-- **A finitely generated geometrically reduced field extension is separably generated**: it has
a finite transcendence basis `s` such that `K` is separable algebraic over `k(s)`. -/
theorem exists_isTranscendenceBasis_and_isSeparable_of_isGeometricallyReduced
    [Algebra.EssFiniteType k K] [Algebra.IsGeometricallyReduced k K] :
    ∃ s : Finset K, IsTranscendenceBasis k ((↑) : s → K) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (s : Set K)) K := by
  obtain _ | ⟨p, ⟨hp⟩, _⟩ := CharP.exists' k
  · exact exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  · have : ExpChar k p := .prime hp
    exact exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType p hp
      fun _ hs ↦ linearIndepOn_pow_of_isGeometricallyReduced p hs

end TauCeti
