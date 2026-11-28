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

An example showing that the topology matters for `TauCeti.ContinuousAut`. For
`G = Multiplicative ℝ`, the reals under addition with their usual topology, the `ℚ`-linear
automorphism exchanging two elements `b₁, b₂` of a Hamel basis (`swapAut`) is an element of
`MulAut G` that is not continuous (`not_continuous_swapAut`), so `TauCeti.ContinuousAut.toMulAut`
is not surjective (`swapAut_notMem_range_toMulAut`): a continuous additive self-map of `ℝ` is
`x ↦ c x` (Mathlib's `map_real_smul`), and `c b₁ = b₂`, `c b₂ = b₁` force `c = ±1`, hence
`b₂ = ±b₁`.

This motivates `TauCeti.ContinuousOut`: since `G` is abelian, `OuterAut G` is isomorphic to
`MulAut G` (`TauCeti.OuterAut.mulEquivOfIsMulCommutative`), which therefore contains
automorphisms not coming from `ContinuousAut G`.
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

variable (i j : Module.Basis.ofVectorSpaceIndex ℚ ℝ)

/-- Under `toAdd`, `swapAut i j` is the `ℚ`-linear map exchanging the Hamel basis elements
`b i` and `b j`. -/
@[simp]
theorem toAdd_swapAut_apply (x : Multiplicative ℝ) :
    (swapAut i j x).toAdd =
      (Module.Basis.ofVectorSpace ℚ ℝ).equiv (Module.Basis.ofVectorSpace ℚ ℝ)
        (Equiv.swap i j) x.toAdd :=
  by simp [swapAut]

/-- `swapAut i j` sends the Hamel basis element `b i` to `b j`. -/
theorem swapAut_ofAdd_left :
    swapAut i j (ofAdd (Module.Basis.ofVectorSpace ℚ ℝ i)) =
      ofAdd (Module.Basis.ofVectorSpace ℚ ℝ j) := by
  apply toAdd.injective
  rw [toAdd_swapAut_apply, toAdd_ofAdd, Module.Basis.equiv_apply,
    Equiv.swap_apply_left, toAdd_ofAdd]

/-- `swapAut i j` sends the Hamel basis element `b j` to `b i`. -/
theorem swapAut_ofAdd_right :
    swapAut i j (ofAdd (Module.Basis.ofVectorSpace ℚ ℝ j)) =
      ofAdd (Module.Basis.ofVectorSpace ℚ ℝ i) := by
  apply toAdd.injective
  rw [toAdd_swapAut_apply, toAdd_ofAdd, Module.Basis.equiv_apply,
    Equiv.swap_apply_right, toAdd_ofAdd]

variable {i j}

/-- Exchanging two distinct Hamel basis elements is a discontinuous automorphism of the reals
under addition. -/
theorem not_continuous_swapAut (hij : i ≠ j) : ¬ Continuous (swapAut i j) := by
  intro hc
  set b := Module.Basis.ofVectorSpace ℚ ℝ
  -- `swapAut i j` read as an additive self-map of `ℝ`.
  let f : ℝ →+ ℝ := AddMonoidHom.mk' (fun x => (swapAut i j (ofAdd x)).toAdd) fun x y => by
    rw [ofAdd_add, map_mul, toAdd_mul]
  have hf : Continuous f := by
    rw [AddMonoidHom.mk'_apply]
    exact continuous_toAdd.comp (hc.comp continuous_ofAdd)
  have hlin (x : ℝ) : f x = x * f 1 := by
    simpa using map_real_smul f hf x 1
  have hi : b j = b i * f 1 := by
    rw [← hlin]
    simp only [f, AddMonoidHom.mk'_apply, b, swapAut_ofAdd_left, toAdd_ofAdd]
  have hj : b i = b j * f 1 := by
    rw [← hlin]
    simp only [f, AddMonoidHom.mk'_apply, b, swapAut_ofAdd_right, toAdd_ofAdd]
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
theorem swapAut_notMem_range_toMulAut (hij : i ≠ j) :
    swapAut i j ∉ (ContinuousAut.toMulAut : ContinuousAut (Multiplicative ℝ) →* _).range := by
  rintro ⟨φ, hφ⟩
  apply not_continuous_swapAut hij
  rw [← hφ, ContinuousAut.coe_toMulAut]
  exact φ.continuous

end TauCeti.DiscontinuousAutReal
