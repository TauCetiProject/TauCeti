/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Instances.RealVectorSpace
public import TauCeti.Topology.Algebra.Group.ContinuousAut.Basic

/-!
# Continuous and discontinuous automorphisms of the reals under addition

Checks for `TauCeti.ContinuousOut` showing that the topology matters. For
`G = Multiplicative ℝ`, the reals under addition with their usual topology:

* every continuous automorphism is `x ↦ c x` with `c ≠ 0`, so
  `TauCeti.ContinuousOut G ≃* ℝˣ` (`continuousOutEquiv`);
* the `ℚ`-linear automorphism exchanging two elements of a Hamel basis is an automorphism of `G`
  that is not continuous (`not_continuous_swapAut`), so `OuterAut G = MulAut G` is strictly bigger
  than the continuous automorphisms. Continuity would make it `x ↦ c x`, and `c b₁ = b₂`,
  `c b₂ = b₁` force `c = ±1`, hence `b₂ = ±b₁`.
-/

@[expose] public noncomputable section

open Multiplicative

namespace TauCeti.ContinuousOutReal

/-- A continuous automorphism of the reals under addition is multiplication by its value at
`1`. -/
theorem toAdd_apply_ofAdd (φ : ContinuousAut (Multiplicative ℝ)) (x : ℝ) :
    (φ (ofAdd x)).toAdd = x * (φ (ofAdd 1)).toAdd := by
  let f : ℝ →+ ℝ := AddMonoidHom.toMultiplicative.symm φ.toMulEquiv.toMonoidHom
  have hf : Continuous f := continuous_toAdd.comp (φ.continuous.comp continuous_ofAdd)
  have h := map_real_smul f hf x 1
  rw [smul_eq_mul, mul_one, smul_eq_mul] at h
  exact h

theorem toAdd_apply_ofAdd_one_ne_zero (φ : ContinuousAut (Multiplicative ℝ)) :
    (φ (ofAdd 1)).toAdd ≠ 0 := by
  intro h
  have h1 : φ (ofAdd 1) = φ 1 := by rw [map_one φ]; exact congrArg ofAdd h
  exact (one_ne_zero : (1 : ℝ) ≠ 0) (congrArg toAdd (φ.injective h1))

/-- The continuous automorphism `x ↦ c x` of the reals under addition, for a unit `c`. -/
def ofUnit (c : ℝˣ) : ContinuousAut (Multiplicative ℝ) where
  toFun x := ofAdd ((c : ℝ) * x.toAdd)
  invFun x := ofAdd (((c⁻¹ : ℝˣ) : ℝ) * x.toAdd)
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by simp [mul_add, ofAdd_add]
  continuous_toFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)
  continuous_invFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)

@[simp]
theorem ofUnit_apply (c : ℝˣ) (x : Multiplicative ℝ) :
    ofUnit c x = ofAdd ((c : ℝ) * x.toAdd) :=
  rfl

/-- The scaling factor `φ(1)` of a continuous automorphism of the reals under addition. -/
def scaleHom : ContinuousAut (Multiplicative ℝ) →* ℝˣ where
  toFun φ := Units.mk0 (φ (ofAdd 1)).toAdd (toAdd_apply_ofAdd_one_ne_zero φ)
  map_one' := Units.ext rfl
  map_mul' φ ψ := Units.ext <| by
    change (φ (ψ (ofAdd 1))).toAdd = (φ (ofAdd 1)).toAdd * (ψ (ofAdd 1)).toAdd
    rw [mul_comm]
    exact toAdd_apply_ofAdd φ (ψ (ofAdd 1)).toAdd

@[simp]
theorem coe_scaleHom_apply (φ : ContinuousAut (Multiplicative ℝ)) :
    (scaleHom φ : ℝ) = (φ (ofAdd 1)).toAdd :=
  rfl

/-- The continuous automorphisms of the reals under addition are the maps `x ↦ c x`, `c ≠ 0`. -/
def continuousAutEquiv : ContinuousAut (Multiplicative ℝ) ≃* ℝˣ where
  toFun := scaleHom
  invFun := ofUnit
  left_inv φ := ContinuousMulEquiv.ext fun x => by
    rw [ofUnit_apply, coe_scaleHom_apply, mul_comm, ← toAdd_apply_ofAdd]
    rfl
  right_inv c := Units.ext <| by
    change (c : ℝ) * 1 = c
    exact mul_one _
  map_mul' := scaleHom.map_mul

/-- The reals under addition are commutative. -/
local instance instIsMulCommutative : IsMulCommutative (Multiplicative ℝ) := ⟨⟨mul_comm⟩⟩

/-- For the reals under addition with their usual topology, `ContinuousOut G ≃* ℝˣ`. -/
def continuousOutEquiv : ContinuousOut (Multiplicative ℝ) ≃* ℝˣ :=
  ContinuousOut.mulEquivOfIsMulCommutative.trans continuousAutEquiv

/-- A Hamel basis of `ℝ` over `ℚ` has at least two elements. -/
instance nontrivial_ofVectorSpaceIndex : Nontrivial (Module.Basis.ofVectorSpaceIndex ℚ ℝ) := by
  rw [← Cardinal.one_lt_iff_nontrivial, (Module.Basis.ofVectorSpace ℚ ℝ).mk_eq_rank'',
    Real.rank_rat_real]
  exact_mod_cast Cardinal.nat_lt_continuum 1

/-- The automorphism of the reals under addition given by the `ℚ`-linear map exchanging the
Hamel basis elements `b i` and `b j`. -/
noncomputable def swapAut (i j : Module.Basis.ofVectorSpaceIndex ℚ ℝ) :
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

end TauCeti.ContinuousOutReal
