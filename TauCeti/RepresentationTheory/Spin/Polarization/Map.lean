/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Polarization.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Isometry

/-!
# Transport of polarization data along isometries

An isometric equivalence `e : (V₁, Q₁) ≃ (V₂, Q₂)` carries a polarization `V₁ = W ⊕ W' ⊕ L` of
`Q₁` to the polarization `V₂ = e W ⊕ e W' ⊕ e L` of `Q₂`. The polar pairing between the images is
the one between `W` and `W'`, because `e` preserves the polar form, and the remainder coordinate
of `e z` is that of `z`. The isometry is retained, not just the existence of one: the exterior
model `⋀·W` of the spin module is carried to `⋀·(e W)` along `e`, and two isometries with the same
images of the summands can give different maps of exterior algebras. The resulting naturality of the
Fock action is `TauCeti.SpinPolarizationData.spinAction_equivOfIsometry_comp_exteriorAlgebraMap`
in `TauCeti/RepresentationTheory/Spin/Polarization/CliffordAction.lean`.

This is how a polarization of a normalized form, such as a sum of squares or a split form, is
moved to an arbitrary nondegenerate form along a chosen diagonalizing isometry
(`TauCeti.SpinPolarizationData.ofNondegenerate`).

## Main definitions

* `TauCeti.SpinPolarizationData.map`: polarization data transported along an isometric
  equivalence.
* `TauCeti.SpinPolarizationData.mapWEquiv`: the restriction of the isometry to the first isotropic
  summands, which induces the comparison of exterior models.

## Main results

* `TauCeti.SpinPolarizationData.map_W`, `TauCeti.SpinPolarizationData.map_W'`,
  `TauCeti.SpinPolarizationData.map_line` and
  `TauCeti.SpinPolarizationData.map_lineCoordinate_apply`: the summands of the transported data
  are the images of the original summands, and `e z` has the remainder coordinate of `z`.
* `TauCeti.SpinPolarizationData.apply_mem_map_W`, `TauCeti.SpinPolarizationData.apply_mem_map_W'`
  and `TauCeti.SpinPolarizationData.apply_mem_map_line`: `e` carries each summand into the
  corresponding transported summand.
* `TauCeti.SpinPolarizationData.map_refl` and `TauCeti.SpinPolarizationData.map_trans`: transport
  along the identity is the identity, and transport along a composite is the composite of the
  transports.
* `TauCeti.SpinPolarizationData.map_map_symm` and
  `TauCeti.SpinPolarizationData.map_symm_map`: transport along an isometry and along its inverse
  are mutually inverse.
-/

public section

namespace TauCeti

universe u v₁ v₂ v₃

namespace SpinPolarizationData

variable {K : Type u} [CommRing K]
  {V₁ : Type v₁} [AddCommGroup V₁] [Module K V₁]
  {V₂ : Type v₂} [AddCommGroup V₂] [Module K V₂]
  {V₃ : Type v₃} [AddCommGroup V₃] [Module K V₃]
  {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂} {Q₃ : QuadraticForm K V₃}

/-- **Polarization data transported along an isometric equivalence.** The three summands are the
images of the summands of `P` under `e`, the decomposition and the polar pairing are carried along
`e`, and a vector `e z` of the new remainder has the coordinate of `z`
(`TauCeti.SpinPolarizationData.map_lineCoordinate_apply`). -/
noncomputable def map (P : SpinPolarizationData Q₁) (e : Q₁.IsometryEquiv Q₂) :
    SpinPolarizationData Q₂ :=
  let eS (S : Submodule K V₁) : S ≃ₗ[K] S.map (e.toLinearEquiv : V₁ →ₗ[K] V₂) :=
    e.toLinearEquiv.submoduleMap S
  have he (S : Submodule K V₁) (a : S.map (e.toLinearEquiv : V₁ →ₗ[K] V₂)) :
      e ((eS S).symm a : V₁) = a := by
    simp only [eS, LinearEquiv.submoduleMap_symm_apply]
    exact e.toLinearEquiv.apply_symm_apply a
  { W := P.W.map (e.toLinearEquiv : V₁ →ₗ[K] V₂)
    W' := P.W'.map (e.toLinearEquiv : V₁ →ₗ[K] V₂)
    line := P.line.map (e.toLinearEquiv : V₁ →ₗ[K] V₂)
    decompositionEquiv := (((eS P.W).prodCongr (eS P.W')).prodCongr (eS P.line)).symm.trans <|
      P.decompositionEquiv.trans e.toLinearEquiv
    decompositionEquiv_apply x := by
      simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_symm,
        LinearEquiv.prodCongr_apply, P.decompositionEquiv_apply,
        QuadraticMap.IsometryEquiv.coe_toLinearEquiv, map_add, he]
    isotropic_W x := by rw [← he P.W x, e.map_app, P.isotropic_W]
    isotropic_W' y := by rw [← he P.W' y, e.map_app, P.isotropic_W']
    pairingEquiv := (eS P.W').symm.trans <| P.pairingEquiv.trans (eS P.W).symm.dualMap
    pairingEquiv_apply y x := by
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply,
        P.pairingEquiv_apply, ← e.polar_apply, he, he]
    pairing_separatingLeft x hx := (eS P.W).symm.map_eq_zero_iff.mp <|
      P.pairing_separatingLeft _ fun y ↦ by
        rw [← e.polar_apply, he, ← hx (eS P.W' y), LinearEquiv.submoduleMap_apply,
          QuadraticMap.IsometryEquiv.coe_toLinearEquiv]
    lineCoordinate := P.lineCoordinate ∘ₗ (eS P.line).symm.toLinearMap
    lineCoordinate_injective := P.lineCoordinate_injective.comp (eS P.line).symm.injective
    lineCoordinate_sq z := by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, P.lineCoordinate_sq, ← e.map_app, he]
    line_orthogonal_W z x := by
      rw [← he P.line z, ← he P.W x, e.polar_apply, P.line_orthogonal_W]
    line_orthogonal_W' z y := by
      rw [← he P.line z, ← he P.W' y, e.polar_apply, P.line_orthogonal_W'] }

variable (P : SpinPolarizationData Q₁) (e : Q₁.IsometryEquiv Q₂)

/-- The first isotropic summand of the transported data is the image of the first summand. -/
@[simp]
theorem map_W : (P.map e).W = P.W.map (e.toLinearEquiv : V₁ →ₗ[K] V₂) :=
  (rfl)

/-- The second isotropic summand of the transported data is the image of the second summand. -/
@[simp]
theorem map_W' : (P.map e).W' = P.W'.map (e.toLinearEquiv : V₁ →ₗ[K] V₂) :=
  (rfl)

/-- The remainder of the transported data is the image of the remainder. -/
@[simp]
theorem map_line : (P.map e).line = P.line.map (e.toLinearEquiv : V₁ →ₗ[K] V₂) :=
  (rfl)

/-- The image of a vector of the first isotropic summand lies in the transported summand. -/
theorem apply_mem_map_W (x : P.W) : e x ∈ (P.map e).W := by
  rw [map_W]
  exact Submodule.mem_map_of_mem x.property

/-- The image of a vector of the second isotropic summand lies in the transported summand. -/
theorem apply_mem_map_W' (y : P.W') : e y ∈ (P.map e).W' := by
  rw [map_W']
  exact Submodule.mem_map_of_mem y.property

/-- The image of a vector of the remainder lies in the transported remainder. -/
theorem apply_mem_map_line (z : P.line) : e z ∈ (P.map e).line := by
  rw [map_line]
  exact Submodule.mem_map_of_mem z.property

/-- The image of a vector of the remainder has the coordinate of that vector. -/
@[simp]
theorem map_lineCoordinate_apply (z : P.line) (hz : e z ∈ (P.map e).line) :
    (P.map e).lineCoordinate ⟨e z, hz⟩ = P.lineCoordinate z := by
  -- The coordinate of the transported data is the original coordinate after `e.symm`.
  change P.lineCoordinate ((e.toLinearEquiv.submoduleMap P.line).symm ⟨e z, hz⟩) = _
  congr 1
  exact Subtype.ext (e.toLinearEquiv.symm_apply_apply z)

/-- The restriction of the isometry `e` to the first isotropic summands, `W ≃ e W`. The map of
exterior algebras it induces compares the exterior models of the spin modules of `P` and of
`P.map e`. -/
noncomputable def mapWEquiv : P.W ≃ₗ[K] (P.map e).W :=
  e.toLinearEquiv.submoduleMap P.W

@[simp]
theorem coe_mapWEquiv_apply (x : P.W) : (P.mapWEquiv e x : V₂) = e x :=
  (rfl)

/-- **Transport along the identity isometry is the identity.** -/
@[simp]
theorem map_refl : P.map (QuadraticMap.IsometryEquiv.refl Q₁) = P := by
  have hS (S : Submodule K V₁) :
      S.map ((QuadraticMap.IsometryEquiv.refl Q₁).toLinearEquiv : V₁ →ₗ[K] V₁) = S :=
    Submodule.map_id S
  refine ext_of_lineCoordinate (hS P.W) (hS P.W') (hS P.line) fun z ↦ ?_
  obtain ⟨_, z, hz, rfl⟩ := z
  exact (P.map_lineCoordinate_apply _ ⟨z, hz⟩ ⟨z, hz, rfl⟩).symm

/-- **Transport along a composite isometry is the composite of the transports.** -/
theorem map_trans (e' : Q₂.IsometryEquiv Q₃) : P.map (e.trans e') = (P.map e).map e' := by
  have hS (S : Submodule K V₁) :
      S.map ((e.trans e').toLinearEquiv : V₁ →ₗ[K] V₃) =
        (S.map (e.toLinearEquiv : V₁ →ₗ[K] V₂)).map (e'.toLinearEquiv : V₂ →ₗ[K] V₃) :=
    Submodule.map_comp (e.toLinearEquiv : V₁ →ₗ[K] V₂) (e'.toLinearEquiv : V₂ →ₗ[K] V₃) S
  refine ext_of_lineCoordinate (hS P.W) (hS P.W') (hS P.line) fun z ↦ ?_
  obtain ⟨_, z, hz, rfl⟩ := z
  exact ((P.map e).map_lineCoordinate_apply e' ⟨e z, z, hz, rfl⟩ ⟨e z, ⟨z, hz, rfl⟩, rfl⟩).trans
    ((P.map_lineCoordinate_apply e ⟨z, hz⟩ ⟨z, hz, rfl⟩).trans
      (P.map_lineCoordinate_apply (e.trans e') ⟨z, hz⟩ ⟨z, hz, rfl⟩).symm)

/-- Transporting along an isometry and then along its inverse recovers the original data. -/
@[simp]
theorem map_map_symm : (P.map e).map e.symm = P := by
  rw [← map_trans]
  convert P.map_refl
  exact DFunLike.ext _ _ fun x ↦ e.symm_apply_apply x

/-- Transporting along the inverse of an isometry and then along the isometry recovers the
original data. -/
@[simp]
theorem map_symm_map (P : SpinPolarizationData Q₂) : (P.map e.symm).map e = P := by
  simpa using (P.map_map_symm e.symm)

end SpinPolarizationData

end TauCeti
