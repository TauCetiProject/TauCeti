/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.RealVectorSpace
public import TauCeti.LinearAlgebra.Dimension.RealRat
public import TauCeti.Topology.Algebra.Group.ContinuousAut.Basic

/-!
# A discontinuous automorphism of the reals under addition

A Check for `TauCeti.ContinuousAut` showing that the topology matters. For
`G = Multiplicative ℝ`, the reals under addition with their usual topology, the `ℚ`-linear
automorphism exchanging two elements `b₁, b₂` of a Hamel basis (`swapAut`) is an element of
`MulAut G` that is not continuous (`not_continuous_swapAut`), so `TauCeti.ContinuousAut.toMulAut`
is not surjective (`swapAut_notMem_range_toMulAut`): a continuous additive self-map of `ℝ` is
`x ↦ c x` (Mathlib's `map_real_smul`), and `c b₁ = b₂`, `c b₂ = b₁` force `c = ±1`, hence
`b₂ = ±b₁`.

This motivates `TauCeti.ContinuousOut`: since `G` is abelian, `OuterAut G` is isomorphic to
`MulAut G`, which therefore contains automorphisms not coming from `ContinuousAut G`; that
isomorphism is not proved here.
-/

public noncomputable section

open Multiplicative

namespace TauCeti.DiscontinuousAutReal

/-- The automorphism of the reals under addition given by the `ℚ`-linear map exchanging the
Hamel basis elements `b i` and `b j`. -/
def swapAut (i j : Module.Basis.ofVectorSpaceIndex ℚ ℝ) :
    MulAut (Multiplicative ℝ) :=
  AddEquiv.toMultiplicative
    ((Module.Basis.ofVectorSpace ℚ ℝ).equiv (Module.Basis.ofVectorSpace ℚ ℝ)
      (Equiv.swap i j)).toAddEquiv

/-- Exchanging two distinct Hamel basis elements is a discontinuous automorphism of the reals
under addition. -/
theorem not_continuous_swapAut {i j : Module.Basis.ofVectorSpaceIndex ℚ ℝ} (hij : i ≠ j) :
    ¬ Continuous (swapAut i j) := by
  intro hc
  set b := Module.Basis.ofVectorSpace ℚ ℝ
  let f : ℝ →+ ℝ := (b.equiv b (Equiv.swap i j)).toAddEquiv.toAddMonoidHom
  have hf : Continuous f := continuous_toAdd.comp (hc.comp continuous_ofAdd)
  have hlin (x : ℝ) : f x = x * f 1 := by
    simpa using map_real_smul f hf x 1
  have hi : b j = b i * f 1 := by
    rw [← hlin]
    simp [f, b.equiv_apply]
  have hj : b i = b j * f 1 := by
    rw [← hlin]
    simp [f, b.equiv_apply]
  have hc1 : f 1 * f 1 = 1 := by
    have : b i * 1 = b i * (f 1 * f 1) := by rw [mul_one, ← mul_assoc, ← hi, ← hj]
    exact (mul_left_cancel₀ (b.ne_zero i) this).symm
  rcases mul_self_eq_one_iff.1 hc1 with h1 | h1
  · rw [h1, mul_one] at hi
    exact hij (b.injective hi).symm
  · rw [h1, mul_neg_one] at hi
    have := congrArg (fun x => b.repr x j) hi
    simp [hij] at this

/-- Some automorphism of the reals under addition is not continuous. -/
theorem exists_mulAut_not_continuous :
    ∃ φ : MulAut (Multiplicative ℝ), ¬ Continuous φ := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne (Module.Basis.ofVectorSpaceIndex ℚ ℝ)
  exact ⟨swapAut i j, not_continuous_swapAut hij⟩

/-- The forgetful map from continuous automorphisms of the reals under addition to all
automorphisms is not surjective: it misses `swapAut i j`. -/
theorem swapAut_notMem_range_toMulAut {i j : Module.Basis.ofVectorSpaceIndex ℚ ℝ} (hij : i ≠ j) :
    swapAut i j ∉ (ContinuousAut.toMulAut : ContinuousAut (Multiplicative ℝ) →* _).range := by
  rintro ⟨φ, hφ⟩
  apply not_continuous_swapAut hij
  rw [← hφ, ContinuousAut.coe_toMulAut]
  exact φ.continuous

end TauCeti.DiscontinuousAutReal
