/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.QuadraticTwoForm
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Isometry
public import TauCeti.Analysis.InnerProductSpace.ExteriorPower
-- Private: the intertwining of the whole Clifford algebra and the quadratic isometry induced by
-- `f` are used only inside proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
import TauCeti.Analysis.Normed.Operator.LinearIsometryEquiv.QuadraticForm

/-!
# Naturality of the Clifford map and of the quadratic two-form

Let `W` and `W'` be Hermitian Clifford modules over oriented real inner product spaces `V` and
`V'` of dimension four, with `Q v = -‖v‖²` and `Q' v = -‖v‖²`. Let `f : V ≃ V'` be a linear
isometry carrying the orientation `o` to `o'`, and `U : W ≃ W'` an equivalence intertwining
Clifford multiplication along `f`:

  `U c(v) = c'(f v) U` for all `v ∈ V`.

Such pairs `(f, U)` are the transition data of a `Spinᶜ` structure. For an element `[s, z]` of
`Spinᶜ(4)` acting on one spinor module, `f` is the rotation of `s` and `U = z ρ(s)`; for a change
of frame, `f` and `U` compare two fibres. The equivariance of the pointwise algebra of the
Seiberg–Witten equations under these pairs is what lets it be assembled into bundle maps.

By `CliffordAlgebra.comp_chirality_eq_chirality_comp`, `U` intertwines the chirality elements, so
it restricts to `U⁺ : W⁺ ≃ W'⁺` (`CliffordAlgebra.positiveHalfSpinorsEquiv`). This file proves the
naturality under `(f, U)` of the Clifford map `C : α ↦ C(iα)`
(`TauCeti.SeibergWitten.cliffordRestriction`), of its adjoint `τ = C*`
(`TauCeti.SeibergWitten.cliffordRestrictionAdjoint`) and, for unitary `U`, of the quadratic
two-form `q(ψ) = τ(Q₀(ψ)) / 4` (`TauCeti.SeibergWitten.quadraticTwoForm`) and its polarization,
which is the real derivative of `q`. Two-forms are transported by `⋀²f`, which preserves the
self-dual forms since `f` commutes with the Hodge stars (`Orientation.hodgeStar_map`).

## Main results

* `TauCeti.SeibergWitten.cliffordRestriction_map`: `C'(i ⋀²f α) = U⁺ C(iα) U⁺⁻¹`.
* `TauCeti.SeibergWitten.cliffordRestrictionAdjoint_conjContinuousAlgEquiv`:
  `τ'(U⁺ T U⁺⁻¹) = ⋀²f τ(T)` for every endomorphism `T` of `W⁺`.
* `TauCeti.SeibergWitten.quadraticTwoForm_positiveHalfSpinorsEquiv`: `q'(U⁺ ψ) = ⋀²f q(ψ)` for
  unitary `U`; this is the `Spinᶜ` equivariance of `q`.
* `TauCeti.SeibergWitten.quadraticTwoFormPolar_positiveHalfSpinorsEquiv`: the same for the
  polarization of `q`, `q'(U⁺ ψ, U⁺ φ) = ⋀²f q(ψ, φ)`.

## References

* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1 and §4.1.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Appendix D.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open CliffordAlgebra Module
open scoped RealInnerProductSpace InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {V' : Type*} [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [Fact (finrank ℝ V' = 4)]
  {Q' : QuadraticForm ℝ V'} {o' : Orientation ℝ V' (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {W' : Type*} [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [FiniteDimensional ℂ W']
  {ρ' : CliffordAlgebra Q' →ₐ[ℝ] Module.End ℂ W'}
  (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hQ' : ∀ v, Q' v = -‖v‖ ^ 2)
  {f : V ≃ₗᵢ[ℝ] V'} (ho : o.map (Fin 4) f.toLinearEquiv = o')

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance : FiniteDimensional ℝ V' := .of_fact_finrank_eq_succ 3

/-! ### The Clifford map and its adjoint -/

section Linear

variable {U : W ≃ₗ[ℂ] W'}
  (hU : ∀ v, U.toLinearMap ∘ₗ ρ (ι Q v) = ρ' (ι Q' (f v)) ∘ₗ U.toLinearMap)

include ho hU in
/-- **Naturality of the Clifford map**: for an equivalence `U` intertwining Clifford
multiplication along an orientation-preserving isometry `f`, `C'(i ⋀²f α) = U⁺ C(iα) U⁺⁻¹` on the
positive half-spinors. -/
theorem cliffordRestriction_map (x : ⋀[ℝ]^2 V) :
    cliffordRestriction o' ρ' (exteriorPower.map 2 f.toLinearMap x) =
      ContinuousLinearEquiv.conjContinuousAlgEquiv
        (positiveHalfSpinorsEquiv o ρ o' ρ' U
          (comp_chirality_eq_chirality_comp hQ hQ' ho hU)).toContinuousLinearEquiv
        (cliffordRestriction o ρ x) := by
  -- `f` is an isometry of the quadratic forms `Q v = -‖v‖²` and `Q' v = -‖v‖²`.
  let e : Q.IsometryEquiv Q' := f.toQuadraticIsometryEquiv (c := -1)
    (fun v ↦ (hQ v).trans (neg_one_mul _).symm) (fun v ↦ (hQ' v).trans (neg_one_mul _).symm)
  have h := LinearMap.congr_fun (comp_eq_map_comp_of_forall_ι
    (f := e.toIsometry) hU (bivectorExterior Q x))
  -- The isometry of quadratic forms has the same underlying linear map as `f`.
  have hf : e.toIsometry.toLinearMap = f.toLinearMap := rfl
  rw [map_bivectorExterior, hf] at h
  ext ψ'
  have hψ := h (U.symm ψ')
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at hψ
  simp [hψ]

include ho hU in
/-- **Naturality of the adjoint `τ = C*` of the Clifford map**: for an equivalence `U`
intertwining Clifford multiplication along an orientation-preserving isometry `f`,
`τ'(U⁺ T U⁺⁻¹) = ⋀²f τ(T)` for every endomorphism `T` of the positive half-spinors. -/
theorem cliffordRestrictionAdjoint_conjContinuousAlgEquiv (hkl : 2 + 2 = finrank ℝ V)
    (hkl' : 2 + 2 = finrank ℝ V')
    (T : positiveHalfSpinors o ρ →L[ℂ] positiveHalfSpinors o ρ) :
    (cliffordRestrictionAdjoint o' ρ' hkl'
        (ContinuousLinearEquiv.conjContinuousAlgEquiv
          (positiveHalfSpinorsEquiv o ρ o' ρ' U
            (comp_chirality_eq_chirality_comp hQ hQ' ho hU)).toContinuousLinearEquiv T) :
        ⋀[ℝ]^2 V') =
      exteriorPower.map 2 f.toLinearMap (cliffordRestrictionAdjoint o ρ hkl T) := by
  set e := positiveHalfSpinorsEquiv o ρ o' ρ' U (comp_chirality_eq_chirality_comp hQ hQ' ho hU)
  have hinj : Function.Injective (exteriorPower.map 2 f.toLinearMap) :=
    exteriorPower.map_injective_field f.injective
  -- `⋀²f` commutes with the Hodge stars, so it maps the self-dual forms of `V` onto those of `V'`.
  have hmem (y : ⋀[ℝ]^2 V) :
      exteriorPower.map 2 f.toLinearMap y ∈
          Module.End.eigenspace (o'.hodgeStar hkl' : Module.End ℝ (⋀[ℝ]^2 V')) 1 ↔
        y ∈ Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 := by
    subst ho
    simp only [Module.End.mem_eigenspace_iff, one_smul, LinearEquiv.coe_coe,
      o.hodgeStar_map f hkl hkl', hinj.eq_iff]
  set τT := cliffordRestrictionAdjoint o ρ hkl T
  suffices h : cliffordRestrictionAdjoint o' ρ' hkl'
      (e.toContinuousLinearEquiv.conjContinuousAlgEquiv T) = ⟨_, (hmem τT).2 τT.2⟩ from
    congrArg Subtype.val h
  -- Test against a self-dual form `β' = ⋀²f β` of `V'`.
  refine ext_inner_right ℝ fun β' ↦ ?_
  obtain ⟨β, hβ⟩ := exteriorPower.map_surjective (n := 2) f.surjective (β' : ⋀[ℝ]^2 V')
  have hβmem := (hmem β).1 (hβ ▸ β'.2)
  have hβ' : β' = ⟨_, (hmem β).2 hβmem⟩ := Subtype.ext hβ.symm
  -- Conjugation by `e` preserves traces.
  have htr (X : positiveHalfSpinors o ρ →L[ℂ] positiveHalfSpinors o ρ) :
      LinearMap.trace ℂ (positiveHalfSpinors o' ρ')
          (e.toContinuousLinearEquiv.conjContinuousAlgEquiv X) =
        LinearMap.trace ℂ (positiveHalfSpinors o ρ) X := by
    rw [← LinearMap.trace_conj' (X : Module.End ℂ (positiveHalfSpinors o ρ)) e]
    -- On underlying linear maps, `conjContinuousAlgEquiv` is `LinearEquiv.conj`.
    rfl
  rw [inner_cliffordRestrictionAdjoint_left, Submodule.coe_inner, hβ',
    cliffordRestriction_map hQ hQ' ho hU β, ← ContinuousLinearMap.toLinearMap_mul, ← map_mul, htr]
  -- `⋀²f` preserves the inner product; `f.toLinearIsometry` has underlying linear map `f`.
  exact ((exteriorPower.inner_map_map f.toLinearIsometry _ _).trans
    (inner_cliffordRestrictionAdjoint_left o ρ hkl T ⟨β, hβmem⟩)).symm

end Linear

/-! ### The quadratic two-form -/

section Isometry

variable {U : W ≃ₗᵢ[ℂ] W'}
  (hU : ∀ v, U.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
    ρ' (ι Q' (f v)) ∘ₗ U.toLinearEquiv.toLinearMap)

omit [FiniteDimensional ℂ W'] in
include ho hU in
/-- The restriction of a unitary Clifford intertwiner conjugates `Q₀`:
`Q₀(U⁺ ψ) = U⁺ Q₀(ψ) U⁺⁻¹`. -/
private theorem quadraticEnd_positiveHalfSpinorsEquiv (ψ : positiveHalfSpinors o ρ) :
    quadraticEnd (positiveHalfSpinorsEquiv o ρ o' ρ' U.toLinearEquiv
        (comp_chirality_eq_chirality_comp hQ hQ' ho hU) ψ) =
      ContinuousLinearEquiv.conjContinuousAlgEquiv
        (positiveHalfSpinorsEquiv o ρ o' ρ' U.toLinearEquiv
          (comp_chirality_eq_chirality_comp hQ hQ' ho hU)).toContinuousLinearEquiv
        (quadraticEnd ψ) := by
  ext φ'
  simp [Submodule.coe_inner, LinearIsometryEquiv.inner_map_eq_flip]

omit [FiniteDimensional ℂ W'] in
include ho hU in
/-- The restriction of a unitary Clifford intertwiner conjugates the polarization `B` of `Q₀`:
`B(U⁺ ψ, U⁺ φ) = U⁺ B(ψ, φ) U⁺⁻¹`. -/
private theorem quadraticEndPolar_positiveHalfSpinorsEquiv (ψ φ : positiveHalfSpinors o ρ) :
    quadraticEndPolar
        (positiveHalfSpinorsEquiv o ρ o' ρ' U.toLinearEquiv
          (comp_chirality_eq_chirality_comp hQ hQ' ho hU) ψ)
        (positiveHalfSpinorsEquiv o ρ o' ρ' U.toLinearEquiv
          (comp_chirality_eq_chirality_comp hQ hQ' ho hU) φ) =
      ContinuousLinearEquiv.conjContinuousAlgEquiv
        (positiveHalfSpinorsEquiv o ρ o' ρ' U.toLinearEquiv
          (comp_chirality_eq_chirality_comp hQ hQ' ho hU)).toContinuousLinearEquiv
        (quadraticEndPolar ψ φ) := by
  ext χ'
  simp only [quadraticEndPolar_apply_apply, Submodule.coe_inner,
    coe_positiveHalfSpinorsEquiv_apply, LinearIsometryEquiv.coe_toLinearEquiv,
    LinearIsometryEquiv.inner_map_eq_flip, LinearIsometryEquiv.symm_apply_apply, Complex.coe_smul,
    AddSubgroupClass.coe_sub, Submodule.coe_add, SetLike.val_smul, SetLike.val_smul_of_tower,
    ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply,
    LinearEquiv.coe_toContinuousLinearEquiv_symm', coe_positiveHalfSpinorsEquiv_symm_apply,
    LinearIsometryEquiv.coe_symm_toLinearEquiv, LinearEquiv.coe_toContinuousLinearEquiv', map_sub,
    map_add, map_smul, sub_right_inj]
  -- `U` is complex-linear, so it commutes with the real scalar `Re⟪ψ, φ⟫`.
  conv_rhs =>
    rw [← Complex.coe_smul, map_smul, LinearIsometryEquiv.apply_symm_apply, Complex.coe_smul]

include ho hU in
/-- **`Spinᶜ` equivariance of the quadratic two-form**: for a unitary equivalence `U` intertwining
Clifford multiplication along an orientation-preserving isometry `f`, `q'(U⁺ ψ) = ⋀²f q(ψ)`. -/
theorem quadraticTwoForm_positiveHalfSpinorsEquiv (hkl : 2 + 2 = finrank ℝ V)
    (hkl' : 2 + 2 = finrank ℝ V') (ψ : positiveHalfSpinors o ρ) :
    (quadraticTwoForm o' ρ' hkl' (positiveHalfSpinorsEquiv o ρ o' ρ' U.toLinearEquiv
        (comp_chirality_eq_chirality_comp hQ hQ' ho hU) ψ) : ⋀[ℝ]^2 V') =
      exteriorPower.map 2 f.toLinearMap (quadraticTwoForm o ρ hkl ψ) := by
  rw [quadraticTwoForm_def, quadraticTwoForm_def,
    quadraticEnd_positiveHalfSpinorsEquiv hQ hQ' ho hU, Submodule.coe_smul,
    cliffordRestrictionAdjoint_conjContinuousAlgEquiv hQ hQ' ho hU hkl hkl', Submodule.coe_smul,
    map_smul]

include ho hU in
/-- **Equivariance of the polarization of `q`**, which is its real derivative: for a unitary
equivalence `U` intertwining Clifford multiplication along an orientation-preserving isometry `f`,
`q'(U⁺ ψ, U⁺ φ) = ⋀²f q(ψ, φ)`. -/
theorem quadraticTwoFormPolar_positiveHalfSpinorsEquiv (hkl : 2 + 2 = finrank ℝ V)
    (hkl' : 2 + 2 = finrank ℝ V') (ψ φ : positiveHalfSpinors o ρ) :
    (quadraticTwoFormPolar o' ρ' hkl'
        (positiveHalfSpinorsEquiv o ρ o' ρ' U.toLinearEquiv
          (comp_chirality_eq_chirality_comp hQ hQ' ho hU) ψ)
        (positiveHalfSpinorsEquiv o ρ o' ρ' U.toLinearEquiv
          (comp_chirality_eq_chirality_comp hQ hQ' ho hU) φ) : ⋀[ℝ]^2 V') =
      exteriorPower.map 2 f.toLinearMap (quadraticTwoFormPolar o ρ hkl ψ φ) := by
  rw [quadraticTwoFormPolar_apply, quadraticTwoFormPolar_apply,
    quadraticEndPolar_positiveHalfSpinorsEquiv hQ hQ' ho hU, Submodule.coe_smul,
    cliffordRestrictionAdjoint_conjContinuousAlgEquiv hQ hQ' ho hU hkl hkl', Submodule.coe_smul,
    map_smul]

end Isometry

end TauCeti.SeibergWitten
