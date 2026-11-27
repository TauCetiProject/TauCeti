/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GL2.CompactCartan
public import TauCeti.Algebra.Lie.Sl2.Coordinates
public import TauCeti.LinearAlgebra.Finsupp.Supported

/-!
# The `𝔤𝔩₂(ℂ)`-module of all compact weights

In the compact Cartan basis `H_c, X_c, Y_c` of `𝔤𝔩₂(ℂ)` (`TauCeti.compactCartanH` and its
siblings), the formulas

`H_c v_ℓ = ℓ v_ℓ`, `X_c v_ℓ = (k + ℓ) / 2 v_{ℓ + 2}`, `Y_c v_ℓ = (k - ℓ) / 2 v_{ℓ - 2}`,

with the identity matrix acting by a scalar `μ`, define a `𝔤𝔩₂(ℂ)`-module structure on the finitely
supported vectors on *all* weights `ℓ ∈ ℤ`, for every `k μ : ℂ`. This is
`TauCeti.CompactWeightModule k μ`. Its Lie submodules of vectors supported on a set of weights that
`X_c` and `Y_c` leave only with coefficient zero (`TauCeti.CompactWeightModule.weightLieSubmodule`)
give explicit `𝔤𝔩₂(ℂ)`-modules, such as the discrete series of `GL₂(ℝ)`; the reflection
`v_ℓ ↦ v_{-ℓ}` preserves such a submodule when its set of weights `S` satisfies `-S = S`.

## Main definitions

* `TauCeti.compactRep k μ`: the Lie algebra homomorphism `𝔤𝔩₂(ℂ) → End(ℤ →₀ ℂ)` given by the
  formulas above, and `TauCeti.CompactWeightModule k μ`, the resulting module.
* `TauCeti.CompactWeightModule.weightVector k μ ℓ`: the weight vector `v_ℓ`.
* `TauCeti.CompactWeightModule.weightLieSubmodule k μ S`: the Lie submodule of the vectors
  supported on `S`.
* `TauCeti.CompactWeightModule.reflection k μ`: `v_ℓ ↦ v_{-ℓ}`.

## Main results

* `TauCeti.lie_compactCartanH_weightVector`, `TauCeti.lie_compactCartanX_weightVector`,
  `TauCeti.lie_compactCartanY_weightVector`: the normalization above;
  `TauCeti.lie_gl2RotationGenerator_weightVector`: `J v_ℓ = iℓ v_ℓ`, so that `r_θ = exp(θJ)` acts
  on `v_ℓ` by `e^{iℓθ}`.
* `TauCeti.CompactWeightModule.smul_weightVector_mem`: every Lie submodule of
  `TauCeti.CompactWeightModule k μ` is spanned by weight vectors, since it contains the weight
  components of its vectors. As `H_c` acts on `v_ℓ` by the distinct scalars `ℓ`, applying
  `H_c - ℓ` to a vector removes its `ℓ`-component, and an induction on the size of the support
  finishes.
* `TauCeti.CompactWeightModule.one_lie_lieSubmodule`: the central scalar of every Lie submodule of
  `TauCeti.CompactWeightModule k μ` is `μ`.
* `TauCeti.CompactWeightModule.gl2Casimir_lieSubmodule`: the Casimir operator of every Lie
  submodule of `TauCeti.CompactWeightModule k μ` is `k (k - 2) / 4`.
* `TauCeti.CompactWeightModule.reflection_lie`: the reflection intertwines the action of `M` with
  that of `A M A⁻¹`; `TauCeti.CompactWeightModule.reflection_mem_weightLieSubmodule_iff`: it maps
  the vectors supported on `S` onto those supported on `-S`.

## Implementation notes

`𝔤𝔩₂(ℂ)` is `Matrix (Fin 2) (Fin 2) ℂ` with the commutator bracket, through the local instance
`LieRing.ofAssociativeRing`, as elsewhere in Tau Ceti.

## References

* A. W. Knapp, *Local Langlands correspondence: the Archimedean case*, in *Motives*, Proc. Sympos.
  Pure Math. 55, part 2, Amer. Math. Soc., 1994, pp. 393–410, §2, pp. 398–400.
* W. Casselman, *Representations of SL₂(ℝ)*, lecture notes, §§2, 5–6, pp. 9–11, 17–20.
-/

public section

noncomputable section

open Complex

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

/-! ### The operators on weight vectors -/

/-- The weight operator `v_ℓ ↦ ℓ v_ℓ` on `ℤ →₀ ℂ`. -/
def compactWeightOp : Module.End ℂ (ℤ →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun ℓ : ℤ ↦ (ℓ : ℂ) • Finsupp.single ℓ (1 : ℂ)

/-- The raising operator `v_ℓ ↦ (k + ℓ) / 2 v_{ℓ + 2}` on `ℤ →₀ ℂ`. -/
def compactRaiseOp (k : ℂ) : Module.End ℂ (ℤ →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun ℓ : ℤ ↦ ((k + ℓ) / 2) • Finsupp.single (ℓ + 2) (1 : ℂ)

/-- The lowering operator `v_ℓ ↦ (k - ℓ) / 2 v_{ℓ - 2}` on `ℤ →₀ ℂ`. -/
def compactLowerOp (k : ℂ) : Module.End ℂ (ℤ →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun ℓ : ℤ ↦ ((k - ℓ) / 2) • Finsupp.single (ℓ - 2) (1 : ℂ)

/-- `H v_ℓ = ℓ v_ℓ`. -/
@[simp]
theorem compactWeightOp_single (ℓ : ℤ) :
    compactWeightOp (Finsupp.single ℓ 1) = (ℓ : ℂ) • Finsupp.single ℓ 1 := by
  simp [compactWeightOp]

/-- `X v_ℓ = (k + ℓ) / 2 v_{ℓ + 2}`. -/
@[simp]
theorem compactRaiseOp_single (k : ℂ) (ℓ : ℤ) :
    compactRaiseOp k (Finsupp.single ℓ 1) = ((k + ℓ) / 2) • Finsupp.single (ℓ + 2) 1 := by
  simp [compactRaiseOp]

/-- `Y v_ℓ = (k - ℓ) / 2 v_{ℓ - 2}`. -/
@[simp]
theorem compactLowerOp_single (k : ℂ) (ℓ : ℤ) :
    compactLowerOp k (Finsupp.single ℓ 1) = ((k - ℓ) / 2) • Finsupp.single (ℓ - 2) 1 := by
  simp [compactLowerOp]

/-- The raising and lowering operators satisfy `[X, Y] = H`. -/
theorem lie_compactRaiseOp_compactLowerOp (k : ℂ) :
    ⁅compactRaiseOp k, compactLowerOp k⁆ = compactWeightOp := by
  refine (Ring.lie_def _ _).trans <| Finsupp.lhom_ext' fun ℓ ↦ LinearMap.ext_ring ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, LinearMap.sub_apply,
    mul_apply_eq_comp, compactRaiseOp_single, compactLowerOp_single, map_smul,
    compactWeightOp_single, sub_add_cancel, add_sub_cancel_right, smul_smul, ← sub_smul]
  congr 1
  push_cast
  ring

/-- `[H, X] = 2 X` for the weight and raising operators. -/
theorem lie_compactWeightOp_compactRaiseOp (k : ℂ) :
    ⁅compactWeightOp, compactRaiseOp k⁆ = (2 : ℂ) • compactRaiseOp k := by
  refine (Ring.lie_def _ _).trans <| Finsupp.lhom_ext' fun ℓ ↦ LinearMap.ext_ring ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, LinearMap.sub_apply,
    mul_apply_eq_comp, compactRaiseOp_single, map_smul, compactWeightOp_single, smul_smul,
    ← sub_smul, LinearMap.smul_apply]
  congr 1
  push_cast
  ring

/-- `[H, Y] = -2 Y` for the weight and lowering operators. -/
theorem lie_compactWeightOp_compactLowerOp (k : ℂ) :
    ⁅compactWeightOp, compactLowerOp k⁆ = -((2 : ℂ) • compactLowerOp k) := by
  refine (Ring.lie_def _ _).trans <| Finsupp.lhom_ext' fun ℓ ↦ LinearMap.ext_ring ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, LinearMap.sub_apply,
    mul_apply_eq_comp, compactLowerOp_single, map_smul, compactWeightOp_single, smul_smul,
    ← sub_smul, LinearMap.neg_apply, LinearMap.smul_apply, ← neg_smul]
  congr 1
  push_cast
  ring

/-- The weight, raising and lowering operators form an `sl₂` triple. -/
theorem isSl2Triple_compactWeightOp (k : ℂ) :
    IsSl2Triple compactWeightOp (compactRaiseOp k) (compactLowerOp k) where
  h_ne_zero h := by simpa using congr($h (Finsupp.single 1 1))
  lie_e_f := lie_compactRaiseOp_compactLowerOp k
  lie_h_e_nsmul := by rw [lie_compactWeightOp_compactRaiseOp, ofNat_smul_eq_nsmul]
  lie_h_f_nsmul := by rw [lie_compactWeightOp_compactLowerOp, ofNat_smul_eq_nsmul]

/-! ### The representation of `𝔤𝔩₂(ℂ)` on all weights -/

/-- The linear map underlying `TauCeti.compactRep`. -/
private def compactRepLinear (k μ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Module.End ℂ (ℤ →₀ ℂ) :=
  compactCoordH.smulRight compactWeightOp + compactCoordX.smulRight (compactRaiseOp k) +
    compactCoordY.smulRight (compactLowerOp k) + (μ • compactCoordOne).smulRight 1

private theorem compactRepLinear_apply (k μ : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactRepLinear k μ M =
      compactCoordH M • compactWeightOp + compactCoordX M • compactRaiseOp k +
        compactCoordY M • compactLowerOp k + (μ * compactCoordOne M) • 1 := by
  simp [compactRepLinear]

/-- The action of `𝔤𝔩₂(ℂ)` on `ℤ →₀ ℂ` in which `H_c`, `X_c`, `Y_c` act by
`TauCeti.compactWeightOp`, `TauCeti.compactRaiseOp k`, `TauCeti.compactLowerOp k` and the identity
matrix acts by the scalar `μ`. -/
def compactRep (k μ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ →ₗ⁅ℂ⁆ Module.End ℂ (ℤ →₀ ℂ) where
  toLinearMap := compactRepLinear k μ
  map_lie' {M N} := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, compactRepLinear_apply,
      compactCoordH_lie, compactCoordX_lie, compactCoordY_lie, compactCoordOne_lie, mul_zero,
      zero_smul, add_zero]
    rw [(isSl2Triple_compactWeightOp k).lie_smul_add_smul_add_smul_add_smul
      fun x ↦ (Ring.lie_def _ _).trans (by rw [mul_one, one_mul, sub_self])]

/-- `TauCeti.compactRep k μ M` in the compact Cartan coordinates of `M`. -/
theorem compactRep_apply (k μ : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactRep k μ M = compactCoordH M • compactWeightOp + compactCoordX M • compactRaiseOp k +
      compactCoordY M • compactLowerOp k + (μ * compactCoordOne M) • 1 :=
  compactRepLinear_apply k μ M

/-- `H_c` acts by the weight operator. -/
@[simp]
theorem compactRep_compactCartanH (k μ : ℂ) : compactRep k μ compactCartanH = compactWeightOp := by
  simp [compactRep_apply]

/-- `X_c` acts by the raising operator. -/
@[simp]
theorem compactRep_compactCartanX (k μ : ℂ) :
    compactRep k μ compactCartanX = compactRaiseOp k := by
  simp [compactRep_apply]

/-- `Y_c` acts by the lowering operator. -/
@[simp]
theorem compactRep_compactCartanY (k μ : ℂ) :
    compactRep k μ compactCartanY = compactLowerOp k := by
  simp [compactRep_apply]

/-- The identity matrix acts by `μ`. -/
@[simp]
theorem compactRep_one (k μ : ℂ) : compactRep k μ 1 = μ • 1 := by
  simp [compactRep_apply]

/-! ### The module of all compact weights -/

/-- The `𝔤𝔩₂(ℂ)`-module of finitely supported vectors `∑ c_ℓ v_ℓ` on all compact weights `ℓ ∈ ℤ`,
with `H_c v_ℓ = ℓ v_ℓ`, `X_c v_ℓ = (k + ℓ) / 2 v_{ℓ + 2}`, `Y_c v_ℓ = (k - ℓ) / 2 v_{ℓ - 2}`, and
the identity matrix acting by `μ`. For `k : ℕ`, the discrete series `D_k(μ)` is its Lie submodule
`TauCeti.discreteSeries k μ` on the weights `|ℓ| ≥ k`, `ℓ ≡ k mod 2`. The type synonym is exposed
because the transported instances need its underlying type. -/
@[expose]
def CompactWeightModule (_k _μ : ℂ) : Type := ℤ →₀ ℂ

namespace CompactWeightModule

variable {k μ : ℂ}

instance instAddCommGroup : AddCommGroup (CompactWeightModule k μ) :=
  inferInstanceAs (AddCommGroup (ℤ →₀ ℂ))

instance instModule : Module ℂ (CompactWeightModule k μ) := inferInstanceAs (Module ℂ (ℤ →₀ ℂ))

instance instLieRingModule :
    LieRingModule (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule k μ) :=
  LieRingModule.compLieHom (ℤ →₀ ℂ) (compactRep k μ)

instance instLieModule : LieModule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule k μ) :=
  LieModule.compLieHom (ℤ →₀ ℂ) (compactRep k μ)

variable (k μ) in
/-- The coordinates `ℓ ↦ c_ℓ` of a vector `∑ c_ℓ v_ℓ`. -/
def equivFinsupp : CompactWeightModule k μ ≃ₗ[ℂ] (ℤ →₀ ℂ) := LinearEquiv.refl ℂ (ℤ →₀ ℂ)

/-- The bracket of `𝔤𝔩₂(ℂ)` with `TauCeti.CompactWeightModule k μ` is `TauCeti.compactRep k μ`. -/
theorem equivFinsupp_lie (M : Matrix (Fin 2) (Fin 2) ℂ) (v : CompactWeightModule k μ) :
    equivFinsupp k μ ⁅M, v⁆ = compactRep k μ M (equivFinsupp k μ v) :=
  (rfl)

variable (k μ) in
/-- The weight vector `v_ℓ`. -/
def weightVector (ℓ : ℤ) : CompactWeightModule k μ := Finsupp.single ℓ 1

/-- The coordinates of `v_ℓ`. -/
@[simp]
theorem equivFinsupp_weightVector (ℓ : ℤ) :
    equivFinsupp k μ (weightVector k μ ℓ) = Finsupp.single ℓ 1 :=
  (rfl)

variable (k μ) in
/-- The weight vectors form a basis of `TauCeti.CompactWeightModule k μ`. -/
def weightBasis : Module.Basis ℤ ℂ (CompactWeightModule k μ) := Finsupp.basisSingleOne

/-- The basis vectors are the weight vectors. -/
@[simp]
theorem weightBasis_apply (ℓ : ℤ) : weightBasis k μ ℓ = weightVector k μ ℓ :=
  (rfl)

/-- The coordinates in the weight basis are `TauCeti.CompactWeightModule.equivFinsupp k μ`. -/
@[simp]
theorem weightBasis_repr : (weightBasis k μ).repr = equivFinsupp k μ :=
  (rfl)

end CompactWeightModule

variable {k μ : ℂ}

open CompactWeightModule (weightVector weightBasis weightBasis_apply)

/-- `H_c v_ℓ = ℓ v_ℓ`. -/
@[simp]
theorem lie_compactCartanH_weightVector (ℓ : ℤ) :
    ⁅compactCartanH, weightVector k μ ℓ⁆ = (ℓ : ℂ) • weightVector k μ ℓ := by
  apply (CompactWeightModule.equivFinsupp k μ).injective
  rw [CompactWeightModule.equivFinsupp_lie, map_smul,
    CompactWeightModule.equivFinsupp_weightVector, compactRep_compactCartanH,
    compactWeightOp_single]

/-- `X_c v_ℓ = (k + ℓ) / 2 v_{ℓ + 2}`. -/
@[simp]
theorem lie_compactCartanX_weightVector (ℓ : ℤ) :
    ⁅compactCartanX, weightVector k μ ℓ⁆ = ((k + ℓ) / 2) • weightVector k μ (ℓ + 2) := by
  apply (CompactWeightModule.equivFinsupp k μ).injective
  rw [CompactWeightModule.equivFinsupp_lie, map_smul,
    CompactWeightModule.equivFinsupp_weightVector, CompactWeightModule.equivFinsupp_weightVector,
    compactRep_compactCartanX, compactRaiseOp_single]

/-- `Y_c v_ℓ = (k - ℓ) / 2 v_{ℓ - 2}`. -/
@[simp]
theorem lie_compactCartanY_weightVector (ℓ : ℤ) :
    ⁅compactCartanY, weightVector k μ ℓ⁆ = ((k - ℓ) / 2) • weightVector k μ (ℓ - 2) := by
  apply (CompactWeightModule.equivFinsupp k μ).injective
  rw [CompactWeightModule.equivFinsupp_lie, map_smul,
    CompactWeightModule.equivFinsupp_weightVector, CompactWeightModule.equivFinsupp_weightVector,
    compactRep_compactCartanY, compactLowerOp_single]

/-- **The central scalar**: the identity matrix acts by `μ`. -/
@[simp]
theorem one_lie_compactWeightModule (v : CompactWeightModule k μ) :
    ⁅(1 : Matrix (Fin 2) (Fin 2) ℂ), v⁆ = μ • v := by
  apply (CompactWeightModule.equivFinsupp k μ).injective
  rw [CompactWeightModule.equivFinsupp_lie, compactRep_one, map_smul]
  simp

/-- The bracket of a matrix with a weight vector, in the coordinates of the compact Cartan basis. -/
theorem lie_weightVector (M : Matrix (Fin 2) (Fin 2) ℂ) (ℓ : ℤ) :
    ⁅M, weightVector k μ ℓ⁆ = (compactCoordH M * ℓ + μ * compactCoordOne M) • weightVector k μ ℓ +
      (compactCoordX M * ((k + ℓ) / 2)) • weightVector k μ (ℓ + 2) +
      (compactCoordY M * ((k - ℓ) / 2)) • weightVector k μ (ℓ - 2) := by
  conv_lhs => rw [eq_compactCoord M]
  simp only [add_lie, smul_lie, lie_compactCartanH_weightVector, lie_compactCartanX_weightVector,
    lie_compactCartanY_weightVector, one_lie_compactWeightModule, smul_smul]
  module

/-- `J v_ℓ = iℓ v_ℓ`, the derivative of `r_θ v_ℓ = e^{iℓθ} v_ℓ`. -/
theorem lie_gl2RotationGenerator_weightVector (ℓ : ℤ) :
    ⁅gl2RotationGenerator, weightVector k μ ℓ⁆ = (I * ℓ) • weightVector k μ ℓ := by
  have hJ : gl2RotationGenerator = I • compactCartanH := by
    rw [compactCartanH_eq, smul_smul]
    simp
  rw [hJ, smul_lie, lie_compactCartanH_weightVector, smul_smul]

namespace CompactWeightModule

/-! ### Weight components -/

/-- A vector is the sum of its weight components. -/
theorem sum_smul_weightVector (v : CompactWeightModule k μ) :
    ∑ j ∈ (equivFinsupp k μ v).support, equivFinsupp k μ v j • weightVector k μ j = v := by
  have h := (weightBasis k μ).linearCombination_repr v
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at h
  simp only [weightBasis_apply] at h
  exact h

/-- The coordinates of `H_c v`: `H_c` multiplies the `j`-th coordinate by `j`. -/
@[simp]
theorem equivFinsupp_lie_compactCartanH_apply (v : CompactWeightModule k μ) (j : ℤ) :
    equivFinsupp k μ ⁅compactCartanH, v⁆ j = j * equivFinsupp k μ v j := by
  conv_lhs => rw [← sum_smul_weightVector v]
  simp only [lie_sum, lie_smul, lie_compactCartanH_weightVector, smul_smul, map_sum, map_smul,
    equivFinsupp_weightVector]
  rw [Finset.sum_apply']
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq']
  split_ifs with h
  · rw [mul_comm]
  · rw [Finsupp.notMem_support_iff.mp h, mul_zero]

/-- **Lie submodules are spanned by weight vectors.** The `ℓ`-component of a vector of a Lie
submodule `N` lies in `N`. -/
theorem smul_weightVector_mem
    {N : LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule k μ)}
    {v : CompactWeightModule k μ} (hv : v ∈ N) (ℓ : ℤ) :
    equivFinsupp k μ v ℓ • weightVector k μ ℓ ∈ N := by
  classical
  induction hn : (equivFinsupp k μ v).support.card using Nat.strong_induction_on
    generalizing v ℓ with
  | _ n ih =>
  by_cases hℓ : equivFinsupp k μ v ℓ = 0
  · rw [hℓ, zero_smul]
    exact N.zero_mem
  -- `u = (H_c - ℓ) v` has the coordinates `(j - ℓ) v_j`, and no `ℓ`-coordinate.
  set u := ⁅compactCartanH, v⁆ - (ℓ : ℂ) • v with hu_def
  have hu : u ∈ N := sub_mem (N.lie_mem hv) (N.smul_mem _ hv)
  have hcoord (j : ℤ) : equivFinsupp k μ u j = (j - ℓ) * equivFinsupp k μ v j := by
    simp [hu_def, sub_mul]
  have hsupp : (equivFinsupp k μ u).support = (equivFinsupp k μ v).support.erase ℓ := by
    ext j
    simp only [Finsupp.mem_support_iff, Finset.mem_erase, hcoord, ne_eq, mul_eq_zero, not_or,
      sub_eq_zero, Int.cast_inj]
  have hcard : (equivFinsupp k μ u).support.card < n := by
    rw [hsupp, ← hn]
    exact Finset.card_erase_lt_of_mem (Finsupp.mem_support_iff.mpr hℓ)
  -- The other components of `v` lie in `N`.
  have hother (j : ℤ) (hj : j ≠ ℓ) : equivFinsupp k μ v j • weightVector k μ j ∈ N := by
    have h := ih _ hcard hu j rfl
    rw [hcoord, mul_smul] at h
    exact (N.toSubmodule.smul_mem_iff (sub_ne_zero.mpr (Int.cast_injective.ne hj))).mp h
  -- The `ℓ`-component is `v` minus the others.
  have hsum := sum_smul_weightVector v
  rw [← Finset.add_sum_erase _ _ (Finsupp.mem_support_iff.mpr hℓ)] at hsum
  rw [eq_sub_of_add_eq hsum]
  exact sub_mem hv (sum_mem fun j hj ↦ hother j (Finset.ne_of_mem_erase hj))

/-- A weight vector with a nonzero coordinate of a vector of `N` lies in `N`. -/
theorem weightVector_mem_of_mem
    {N : LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule k μ)}
    {v : CompactWeightModule k μ} (hv : v ∈ N) {ℓ : ℤ} (hℓ : equivFinsupp k μ v ℓ ≠ 0) :
    weightVector k μ ℓ ∈ N :=
  (N.toSubmodule.smul_mem_iff hℓ).mp (smul_weightVector_mem hv ℓ)

end CompactWeightModule

/-! ### The Casimir operator and the central scalar -/

/-- **The Casimir operator acts by `k(k - 2)/4`** on every vector of
`TauCeti.CompactWeightModule k μ`. -/
theorem gl2Casimir_compactWeightModule :
    gl2Casimir (CompactWeightModule k μ) = (k * (k - 2) / 4) • 1 := by
  refine (weightBasis k μ).ext fun ℓ ↦ ?_
  simp only [weightBasis_apply, gl2Casimir_apply, LinearMap.smul_apply,
    lie_compactCartanH_weightVector, lie_compactCartanX_weightVector,
    lie_compactCartanY_weightVector, lie_smul, sub_add_cancel, add_sub_cancel_right, smul_smul,
    one_apply_eq_self]
  rw [← add_smul, ← add_smul, smul_smul]
  congr 1
  push_cast
  ring

namespace CompactWeightModule

/-- The Casimir operator acts by `k(k - 2)/4` on every Lie submodule of
`TauCeti.CompactWeightModule k μ`. -/
theorem gl2Casimir_lieSubmodule
    (N : LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule k μ)) (v : N) :
    gl2Casimir N v = (k * (k - 2) / 4) • v := by
  ext
  rw [coe_gl2Casimir_lieSubmodule, gl2Casimir_compactWeightModule, LieSubmodule.coe_smul,
    LinearMap.smul_apply, one_apply_eq_self]

/-- The identity matrix acts by `μ` on every Lie submodule of `TauCeti.CompactWeightModule k μ`. -/
theorem one_lie_lieSubmodule
    (N : LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule k μ)) (v : N) :
    ⁅(1 : Matrix (Fin 2) (Fin 2) ℂ), v⁆ = μ • v := by
  ext
  simp

/-! ### Lie submodules spanned by weight vectors -/

variable (k μ) in
/-- The Lie submodule of `TauCeti.CompactWeightModule k μ` of the vectors supported on a set `S` of
weights that `X_c` and `Y_c` leave only with coefficient zero. -/
def weightLieSubmodule (S : Set ℤ) (hX : ∀ ℓ ∈ S, ℓ + 2 ∉ S → k + ℓ = 0)
    (hY : ∀ ℓ ∈ S, ℓ - 2 ∉ S → k - ℓ = 0) :
    LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule k μ) where
  toSubmodule := (Finsupp.supported ℂ ℂ S).comap (CompactWeightModule.equivFinsupp k μ).toLinearMap
  lie_mem {M v} hv := by
    replace hv := Submodule.mem_comap.1 hv
    refine Submodule.mem_comap.2 ?_
    rw [LinearEquiv.coe_coe] at hv ⊢
    rw [equivFinsupp_lie, compactRep_apply]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, one_apply_eq_self]
    refine add_mem (add_mem (add_mem (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_))
      (Submodule.smul_mem _ _ ?_)) (Submodule.smul_mem _ _ hv)
    · exact Finsupp.map_mem_supported_of_map_single_eq_smul_single ℂ _ (fun ℓ : ℤ ↦ (ℓ : ℂ)) id
        compactWeightOp_single (fun ℓ hℓ h ↦ absurd hℓ h) hv
    · exact Finsupp.map_mem_supported_of_map_single_eq_smul_single ℂ _ _ (· + 2)
        (compactRaiseOp_single k) (fun ℓ hℓ h ↦ by rw [hX ℓ hℓ h, zero_div]) hv
    · exact Finsupp.map_mem_supported_of_map_single_eq_smul_single ℂ _ _ (· - 2)
        (compactLowerOp_single k) (fun ℓ hℓ h ↦ by rw [hY ℓ hℓ h, zero_div]) hv

/-- The underlying submodule of `TauCeti.CompactWeightModule.weightLieSubmodule`. -/
theorem toSubmodule_weightLieSubmodule {S : Set ℤ} {hX : ∀ ℓ ∈ S, ℓ + 2 ∉ S → k + ℓ = 0}
    {hY : ∀ ℓ ∈ S, ℓ - 2 ∉ S → k - ℓ = 0} :
    (weightLieSubmodule k μ S hX hY).toSubmodule =
      (Finsupp.supported ℂ ℂ S).comap (CompactWeightModule.equivFinsupp k μ).toLinearMap :=
  (rfl)

/-- Membership in `TauCeti.CompactWeightModule.weightLieSubmodule`: the coordinates are supported
on `S`. -/
theorem mem_weightLieSubmodule {S : Set ℤ} {hX : ∀ ℓ ∈ S, ℓ + 2 ∉ S → k + ℓ = 0}
    {hY : ∀ ℓ ∈ S, ℓ - 2 ∉ S → k - ℓ = 0} {v : CompactWeightModule k μ} :
    v ∈ weightLieSubmodule k μ S hX hY ↔
      CompactWeightModule.equivFinsupp k μ v ∈ Finsupp.supported ℂ ℂ S :=
  Iff.rfl

/-- `v_ℓ` lies in the Lie submodule of a set of weights containing `ℓ`. -/
theorem weightVector_mem_weightLieSubmodule {S : Set ℤ} {hX : ∀ ℓ ∈ S, ℓ + 2 ∉ S → k + ℓ = 0}
    {hY : ∀ ℓ ∈ S, ℓ - 2 ∉ S → k - ℓ = 0} {ℓ : ℤ} (hℓ : ℓ ∈ S) :
    weightVector k μ ℓ ∈ weightLieSubmodule k μ S hX hY :=
  mem_weightLieSubmodule.2 (Finsupp.single_mem_supported ℂ _ hℓ)

end CompactWeightModule

namespace CompactWeightModule

/-! ### The reflection -/

variable (k μ) in
/-- The **reflection** `v_ℓ ↦ v_{-ℓ}`, the action of `A = diag(1, -1)`, which interchanges the two
rays of `D_k(μ)`. -/
def reflection : CompactWeightModule k μ ≃ₗ[ℂ] CompactWeightModule k μ :=
  Finsupp.domLCongr (Equiv.neg ℤ)

/-- The coordinates of the reflection of `v` are those of `v` at the opposite weights. -/
@[simp]
theorem equivFinsupp_reflection_apply (v : CompactWeightModule k μ) (ℓ : ℤ) :
    equivFinsupp k μ (reflection k μ v) ℓ = equivFinsupp k μ v (-ℓ) :=
  -- `equivFinsupp` is the identity of `ℤ →₀ ℂ` and `reflection` is `Finsupp.domLCongr`, whose
  -- `_apply` lemmas do not fire syntactically on the type synonym, so this unfolds both to cite
  -- `Finsupp.equivMapDomain_apply`.
  Finsupp.equivMapDomain_apply (Equiv.neg ℤ) (equivFinsupp k μ v) ℓ

/-- The reflection sends `v_ℓ` to `v_{-ℓ}`. -/
@[simp]
theorem reflection_weightVector (ℓ : ℤ) :
    reflection k μ (weightVector k μ ℓ) = weightVector k μ (-ℓ) :=
  -- `reflection` is `Finsupp.domLCongr` and `weightVector` is `Finsupp.single` on the type
  -- synonym, so this unfolds both to cite `Finsupp.domLCongr_single`.
  Finsupp.domLCongr_single _ _ _

/-- The reflection is an involution. -/
@[simp]
theorem reflection_reflection (v : CompactWeightModule k μ) :
    reflection k μ (reflection k μ v) = v :=
  (equivFinsupp k μ).injective <| Finsupp.ext fun ℓ ↦ by simp

/-- The reflection is its own inverse. -/
@[simp]
theorem reflection_symm : (reflection k μ).symm = reflection k μ :=
  LinearEquiv.ext fun v ↦ (reflection k μ).symm_apply_eq.2 (reflection_reflection v).symm

/-- The reflection intertwines the action of `M` with that of `A M A⁻¹ = A M A`, `A = diag(1, -1)`
(`TauCeti.compactCartanReflection_mul_self`): it exchanges `X_c` and `Y_c` and negates `H_c`. -/
theorem reflection_lie (M : Matrix (Fin 2) (Fin 2) ℂ) (v : CompactWeightModule k μ) :
    reflection k μ ⁅M, v⁆ =
      ⁅compactCartanReflection * M * compactCartanReflection, reflection k μ v⁆ := by
  have h : (reflection k μ).toLinearMap ∘ₗ LieModule.toEnd ℂ _ _ M =
      LieModule.toEnd ℂ _ _ (compactCartanReflection * M * compactCartanReflection) ∘ₗ
        (reflection k μ).toLinearMap := by
    refine (weightBasis k μ).ext fun ℓ ↦ ?_
    simp only [weightBasis_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LieModule.toEnd_apply_apply, reflection_weightVector, lie_weightVector, map_add, map_smul,
      compactCoordH_compactCartanReflection_mul_mul, compactCoordX_compactCartanReflection_mul_mul,
      compactCoordY_compactCartanReflection_mul_mul,
      compactCoordOne_compactCartanReflection_mul_mul]
    rw [show -(ℓ + 2) = -ℓ - 2 by ring, show -(ℓ - 2) = -ℓ + 2 by ring]
    push_cast
    module
  simpa using congr($h v)

/-- The reflection maps the vectors supported on `S` onto those supported on `-S`. -/
theorem reflection_mem_weightLieSubmodule_iff {S S' : Set ℤ}
    {hX : ∀ ℓ ∈ S, ℓ + 2 ∉ S → k + ℓ = 0} {hY : ∀ ℓ ∈ S, ℓ - 2 ∉ S → k - ℓ = 0}
    {hX' : ∀ ℓ ∈ S', ℓ + 2 ∉ S' → k + ℓ = 0} {hY' : ∀ ℓ ∈ S', ℓ - 2 ∉ S' → k - ℓ = 0}
    (hS : ∀ ℓ, -ℓ ∈ S' ↔ ℓ ∈ S) {v : CompactWeightModule k μ} :
    reflection k μ v ∈ weightLieSubmodule k μ S' hX' hY' ↔ v ∈ weightLieSubmodule k μ S hX hY := by
  simp only [mem_weightLieSubmodule, Finsupp.mem_supported', equivFinsupp_reflection_apply]
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ h _ fun h' ↦ hx (by simpa using (hS (-x)).2 h')⟩
  simpa using h (-x) fun h' ↦ hx ((hS x).1 h')

end CompactWeightModule

end TauCeti
