/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.VonNeumannAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import TauCeti.Algebra.Group.Center

/-!
# Concrete von Neumann algebras: C⋆-closure, degenerate spaces, and unitary transport

A concrete von Neumann algebra is norm closed, since it is a double commutant.
Its elements therefore form a C⋆-algebra with the inherited operator norm and adjoint.
This allows the abstract continuous functional calculus and positive-functional APIs to
be applied directly to concrete algebras, including those acting on the zero Hilbert space
(`instSubsingleton`, `subsingleton_coe_iff`).

The instances use Mathlib's generic subobject constructions, in particular
`StarSubalgebra.cstarAlgebra`. The underlying star subalgebra has the same instances;
no new norm, completion, or algebra carrier is introduced.

Conjugation along a linear isometric equivalence `U : H₁ ≃ₗᵢ[ℂ] H₂` transports concrete von Neumann
algebras as an order isomorphism (`VonNeumannAlgebra.mapLinearIsometryEquiv`) commuting with
commutants, and restricts to a `⋆`-algebra isomorphism on carriers
(`VonNeumannAlgebra.equivMapLinearIsometryEquiv`).
-/

public section

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Concrete von Neumann algebras are closed under complex scalar multiplication. -/
instance instSMulMemClass : SMulMemClass (VonNeumannAlgebra H) ℂ (H →L[ℂ] H) where
  smul_mem {M} c {_} ha := SMulMemClass.smul_mem (s := M.toStarSubalgebra) c ha

/-- A concrete von Neumann algebra is closed in the operator norm topology. -/
instance isClosed (M : VonNeumannAlgebra H) : IsClosed (M : Set (H →L[ℂ] H)) := by
  rw [← M.centralizer_centralizer]
  exact Set.isClosed_centralizer _

/-- The underlying star subalgebra is closed in the same operator norm topology. -/
instance instIsClosedToStarSubalgebra (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  simpa only [coe_toStarSubalgebra] using M.isClosed

/-- On a subsingleton Hilbert space there is only one concrete von Neumann algebra. -/
instance instSubsingleton [Subsingleton H] : Subsingleton (VonNeumannAlgebra H) where
  allEq M N := ext fun x ↦
    ⟨fun _ ↦ Subsingleton.elim (0 : H →L[ℂ] H) x ▸ zero_mem N,
     fun _ ↦ Subsingleton.elim (0 : H →L[ℂ] H) x ▸ zero_mem M⟩

/-- The carrier type of a von Neumann algebra `M` on `H` is a subsingleton iff `H` is. -/
theorem subsingleton_coe_iff (M : VonNeumannAlgebra H) : Subsingleton M ↔ Subsingleton H := by
  refine ⟨fun _ ↦ subsingleton_of_forall_eq 0 fun v ↦ ?_, fun _ ↦ inferInstance⟩
  have h10 : (1 : H →L[ℂ] H) = 0 := congrArg Subtype.val (Subsingleton.elim (1 : M) (0 : M))
  simpa using congr($h10 v)

section UnitaryTransport
variable {H₁ H₂ H₃ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃]

private noncomputable def mapLinearIsometryEquivAux (U : H₁ ≃ₗᵢ[ℂ] H₂) (M : VonNeumannAlgebra H₁) :
    VonNeumannAlgebra H₂ where
  toStarSubalgebra := M.toStarSubalgebra.map U.conjStarAlgEquiv.toStarAlgHom
  centralizer_centralizer' := by
    have h := (M.toStarSubalgebra.coe_map U.conjStarAlgEquiv.toStarAlgHom).trans
      (congrArg (⇑U.conjStarAlgEquiv '' ·) (coe_toStarSubalgebra M))
    have hcc : (⇑U.conjStarAlgEquiv '' (M : Set _)).centralizer.centralizer =
        ⇑U.conjStarAlgEquiv '' (M : Set _) := by
      rw [Set.image_centralizer, Set.image_centralizer, M.centralizer_centralizer]
    -- The carrier is the coercion of the star subalgebra to a set, up to unfolding `SetLike.coe`.
    exact (congrArg (fun S : Set (H₂ →L[ℂ] H₂) ↦ S.centralizer.centralizer) h).trans
      (hcc.trans h.symm)
private theorem coe_mapLinearIsometryEquivAux (U : H₁ ≃ₗᵢ[ℂ] H₂) (M : VonNeumannAlgebra H₁) :
    (mapLinearIsometryEquivAux U M : Set (H₂ →L[ℂ] H₂)) = U.conjStarAlgEquiv '' (M : Set _) := by
  rw [← coe_toStarSubalgebra]; exact M.toStarSubalgebra.coe_map U.conjStarAlgEquiv.toStarAlgHom
private theorem mem_mapLinearIsometryEquivAux {U : H₁ ≃ₗᵢ[ℂ] H₂} {M : VonNeumannAlgebra H₁}
    {y : H₂ →L[ℂ] H₂} : y ∈ mapLinearIsometryEquivAux U M ↔ U.symm.conjStarAlgEquiv y ∈ M := by
  rw [← SetLike.mem_coe, coe_mapLinearIsometryEquivAux]
  exact ⟨fun ⟨x, hx, hxy⟩ ↦ hxy ▸ by simpa [← LinearIsometryEquiv.symm_conjStarAlgEquiv] using hx,
    fun hy ↦ ⟨U.symm.conjStarAlgEquiv y, hy, U.conjStarAlgEquiv.apply_symm_apply y⟩⟩

/-- Transport of von Neumann algebras along a linear isometric equivalence `U : H₁ ≃ₗᵢ[ℂ] H₂` via
spatial conjugation `T ↦ U ∘L T ∘L U.symm`, bundled as an order isomorphism. -/
noncomputable def mapLinearIsometryEquiv (U : H₁ ≃ₗᵢ[ℂ] H₂) :
    VonNeumannAlgebra H₁ ≃o VonNeumannAlgebra H₂ where
  toFun := mapLinearIsometryEquivAux U
  invFun := mapLinearIsometryEquivAux U.symm
  left_inv M := ext fun x ↦ by
    rw [mem_mapLinearIsometryEquivAux, mem_mapLinearIsometryEquivAux, LinearIsometryEquiv.symm_symm]
    simp [← LinearIsometryEquiv.symm_conjStarAlgEquiv]
  right_inv N := ext fun y ↦ by
    rw [mem_mapLinearIsometryEquivAux, mem_mapLinearIsometryEquivAux, LinearIsometryEquiv.symm_symm]
    simp [← LinearIsometryEquiv.symm_conjStarAlgEquiv]
  map_rel_iff' {a b} := by
    simp only [Equiv.coe_fn_mk, ← SetLike.coe_subset_coe, coe_mapLinearIsometryEquivAux]
    exact Set.image_subset_image_iff U.conjStarAlgEquiv.injective
@[simp, norm_cast] theorem coe_mapLinearIsometryEquiv (U : H₁ ≃ₗᵢ[ℂ] H₂)
    (M : VonNeumannAlgebra H₁) :
    (mapLinearIsometryEquiv U M : Set (H₂ →L[ℂ] H₂)) = U.conjStarAlgEquiv '' (M : Set _) := by
  simp [mapLinearIsometryEquiv, coe_mapLinearIsometryEquivAux]
@[simp] theorem mem_mapLinearIsometryEquiv {U : H₁ ≃ₗᵢ[ℂ] H₂} {M : VonNeumannAlgebra H₁}
    {y : H₂ →L[ℂ] H₂} : y ∈ mapLinearIsometryEquiv U M ↔ U.symm.conjStarAlgEquiv y ∈ M := by
  simp [mapLinearIsometryEquiv, mem_mapLinearIsometryEquivAux]
theorem conjStarAlgEquiv_mem_mapLinearIsometryEquiv {U : H₁ ≃ₗᵢ[ℂ] H₂}
    {M : VonNeumannAlgebra H₁} {x : H₁ →L[ℂ] H₁} :
    U.conjStarAlgEquiv x ∈ mapLinearIsometryEquiv U M ↔ x ∈ M := by
  simp [← LinearIsometryEquiv.symm_conjStarAlgEquiv]
@[simp] theorem mapLinearIsometryEquiv_symm (U : H₁ ≃ₗᵢ[ℂ] H₂) :
    (mapLinearIsometryEquiv U).symm = mapLinearIsometryEquiv U.symm := by
  ext N x
  rw [← (conjStarAlgEquiv_mem_mapLinearIsometryEquiv (U := U)), OrderIso.apply_symm_apply,
    mem_mapLinearIsometryEquiv, LinearIsometryEquiv.symm_symm]
@[simp] theorem mapLinearIsometryEquiv_refl :
    mapLinearIsometryEquiv (.refl ℂ H₁) = OrderIso.refl (VonNeumannAlgebra H₁) := by
  ext M x; simp [← LinearIsometryEquiv.symm_conjStarAlgEquiv]
theorem mapLinearIsometryEquiv_trans (U : H₁ ≃ₗᵢ[ℂ] H₂) (V : H₂ ≃ₗᵢ[ℂ] H₃) :
    mapLinearIsometryEquiv (U.trans V) =
      (mapLinearIsometryEquiv U).trans (mapLinearIsometryEquiv V) := by
  ext; simp [LinearIsometryEquiv.conjStarAlgEquiv_trans]
/-- Unitary transport commutes with taking commutants. -/
@[simp] theorem mapLinearIsometryEquiv_commutant (U : H₁ ≃ₗᵢ[ℂ] H₂) (M : VonNeumannAlgebra H₁) :
    mapLinearIsometryEquiv U M.commutant = (mapLinearIsometryEquiv U M).commutant :=
  SetLike.coe_injective <| by simp [coe_commutant, Set.image_centralizer]
/-- Spatial conjugation restricts to a `⋆`-algebra equivalence between `M` and its transported
von Neumann algebra `mapLinearIsometryEquiv U M`. -/
noncomputable def equivMapLinearIsometryEquiv (U : H₁ ≃ₗᵢ[ℂ] H₂) (M : VonNeumannAlgebra H₁) :
    M ≃⋆ₐ[ℂ] mapLinearIsometryEquiv U M :=
  { toFun := fun x ↦ ⟨U.conjStarAlgEquiv x.1, conjStarAlgEquiv_mem_mapLinearIsometryEquiv.2 x.2⟩
    invFun := fun y ↦ ⟨U.symm.conjStarAlgEquiv y.1, mem_mapLinearIsometryEquiv.1 y.2⟩
    left_inv := fun x ↦ Subtype.ext <| by simp [← LinearIsometryEquiv.symm_conjStarAlgEquiv]
    right_inv := fun y ↦ Subtype.ext <| U.conjStarAlgEquiv.apply_symm_apply y.1
    map_mul' := fun x y ↦ Subtype.ext <| map_mul U.conjStarAlgEquiv x.1 y.1
    map_add' := fun x y ↦ Subtype.ext <| map_add U.conjStarAlgEquiv x.1 y.1
    map_smul' := fun c x ↦ Subtype.ext <| map_smul U.conjStarAlgEquiv c x.1
    map_star' := fun x ↦ Subtype.ext <| map_star U.conjStarAlgEquiv x.1 }
@[simp, norm_cast] theorem coe_equivMapLinearIsometryEquiv (U : H₁ ≃ₗᵢ[ℂ] H₂)
    (M : VonNeumannAlgebra H₁) (x : M) :
    (equivMapLinearIsometryEquiv U M x : H₂ →L[ℂ] H₂) = U.conjStarAlgEquiv x := (rfl)
@[simp, norm_cast] theorem coe_equivMapLinearIsometryEquiv_symm (U : H₁ ≃ₗᵢ[ℂ] H₂)
    (M : VonNeumannAlgebra H₁) (y : mapLinearIsometryEquiv U M) :
    ((equivMapLinearIsometryEquiv U M).symm y : H₁ →L[ℂ] H₁) = U.symm.conjStarAlgEquiv y := (rfl)
end UnitaryTransport

end VonNeumannAlgebra
