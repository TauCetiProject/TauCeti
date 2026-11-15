/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.VonNeumannAlgebra.Lattice
import TauCeti.Algebra.Group.Center

/-!
# Spatial conjugation of concrete von Neumann algebras

Given a linear isometric equivalence `U : H ≃ₗᵢ[ℂ] K` between complex Hilbert spaces, conjugation
`T ↦ U ∘L T ∘L U.symm` (`LinearIsometryEquiv.conjStarAlgEquiv`) is a star algebra isomorphism
`(H →L[ℂ] H) ≃⋆ₐ[ℂ] (K →L[ℂ] K)`. Because multiplicative equivalences commute with taking
centralizers (`MulEquivClass.centralizer_image`), the image of a concrete von Neumann algebra
`M : VonNeumannAlgebra H` under `U.conjStarAlgEquiv` is equal to its own double commutant and
therefore forms a concrete von Neumann algebra `M.conj U : VonNeumannAlgebra K`.

Spatial conjugation gives an order isomorphism `VonNeumannAlgebra.conjOrderIso U` between the
complete lattices of von Neumann algebras on `H` and `K`, commutes with
`VonNeumannAlgebra.commutant` and `VonNeumannAlgebra.adjoin`, and restricts on carriers to a star
algebra equivalence `M.conjStarAlgEquiv U : M ≃⋆ₐ[ℂ] M.conj U`.

## Main definitions

* `VonNeumannAlgebra.conj`: transport of `M : VonNeumannAlgebra H` along `U : H ≃ₗᵢ[ℂ] K`.
* `VonNeumannAlgebra.conjOrderIso`: `M ↦ M.conj U` as an order isomorphism of complete lattices.
* `VonNeumannAlgebra.conjStarAlgEquiv`: the restricted star algebra isomorphism `M ≃⋆ₐ[ℂ] M.conj U`.

## Main statements

* `VonNeumannAlgebra.commutant_conj`: `(M.conj U).commutant = M.commutant.conj U`.
* `VonNeumannAlgebra.conj_adjoin`: `(adjoin s).conj U = adjoin (U.conjStarAlgEquiv '' s)`.
-/

public section

namespace VonNeumannAlgebra

variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

/-- Spatial transport of a concrete von Neumann algebra along a unitary equivalence
`U : H ≃ₗᵢ[ℂ] K`, given on operators by `T ↦ U ∘L T ∘L U.symm`. -/
noncomputable def conj (M : VonNeumannAlgebra H) (U : H ≃ₗᵢ[ℂ] K) : VonNeumannAlgebra K where
  toStarSubalgebra := M.toStarSubalgebra.map U.conjStarAlgEquiv.toStarAlgHom
  centralizer_centralizer' := by
    change (U.conjStarAlgEquiv '' (M : Set (H →L[ℂ] H))).centralizer.centralizer =
      U.conjStarAlgEquiv '' (M : Set (H →L[ℂ] H))
    rw [MulEquivClass.centralizer_image, MulEquivClass.centralizer_image,
      M.centralizer_centralizer]

@[simp, norm_cast]
theorem coe_conj (M : VonNeumannAlgebra H) (U : H ≃ₗᵢ[ℂ] K) :
    (M.conj U : Set (K →L[ℂ] K)) = U.conjStarAlgEquiv '' (M : Set (H →L[ℂ] H)) := by
  rfl

@[simp]
theorem toStarSubalgebra_conj (M : VonNeumannAlgebra H) (U : H ≃ₗᵢ[ℂ] K) :
    (M.conj U).toStarSubalgebra = M.toStarSubalgebra.map U.conjStarAlgEquiv.toStarAlgHom := by
  rfl

theorem mem_conj_iff {M : VonNeumannAlgebra H} {U : H ≃ₗᵢ[ℂ] K} {y : K →L[ℂ] K} :
    y ∈ M.conj U ↔ ∃ x ∈ M, U.conjStarAlgEquiv x = y := by
  rfl

@[simp]
theorem conjStarAlgEquiv_mem_conj_iff {M : VonNeumannAlgebra H} {U : H ≃ₗᵢ[ℂ] K}
    {x : H →L[ℂ] H} :
    U.conjStarAlgEquiv x ∈ M.conj U ↔ x ∈ M := by
  rw [← SetLike.mem_coe, coe_conj]
  exact U.conjStarAlgEquiv.injective.mem_set_image

theorem mem_conj_iff_symm {M : VonNeumannAlgebra H} {U : H ≃ₗᵢ[ℂ] K} {y : K →L[ℂ] K} :
    y ∈ M.conj U ↔ U.symm.conjStarAlgEquiv y ∈ M := by
  rw [← conjStarAlgEquiv_mem_conj_iff (U := U), ← LinearIsometryEquiv.symm_conjStarAlgEquiv,
    StarAlgEquiv.apply_symm_apply]

@[simp]
theorem conj_refl (M : VonNeumannAlgebra H) :
    M.conj (LinearIsometryEquiv.refl ℂ H) = M :=
  ext fun x ↦ by simp [← SetLike.mem_coe]

theorem conj_trans (M : VonNeumannAlgebra H) (U : H ≃ₗᵢ[ℂ] K) (V : K ≃ₗᵢ[ℂ] L) :
    M.conj (U.trans V) = (M.conj U).conj V :=
  SetLike.coe_injective <| by
    rw [coe_conj, coe_conj, coe_conj, LinearIsometryEquiv.conjStarAlgEquiv_trans,
      StarAlgEquiv.coe_trans, Set.image_comp]

@[simp]
theorem conj_symm_conj (M : VonNeumannAlgebra H) (U : H ≃ₗᵢ[ℂ] K) :
    (M.conj U).conj U.symm = M := by
  rw [← conj_trans, LinearIsometryEquiv.self_trans_symm, conj_refl]

@[simp]
theorem conj_conj_symm (N : VonNeumannAlgebra K) (U : H ≃ₗᵢ[ℂ] K) :
    (N.conj U.symm).conj U = N := by
  simpa using conj_symm_conj N U.symm

theorem conj_mono {M₁ M₂ : VonNeumannAlgebra H} (U : H ≃ₗᵢ[ℂ] K) (h : M₁ ≤ M₂) :
    M₁.conj U ≤ M₂.conj U := by
  rw [← SetLike.coe_subset_coe, coe_conj, coe_conj]
  exact Set.image_mono h

@[simp]
theorem conj_le_conj_iff {M₁ M₂ : VonNeumannAlgebra H} {U : H ≃ₗᵢ[ℂ] K} :
    M₁.conj U ≤ M₂.conj U ↔ M₁ ≤ M₂ :=
  ⟨fun h ↦ by simpa using conj_mono U.symm h, conj_mono U⟩

theorem conj_le_iff {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K} {U : H ≃ₗᵢ[ℂ] K} :
    M.conj U ≤ N ↔ M ≤ N.conj U.symm := by
  rw [← conj_le_conj_iff (U := U.symm), conj_symm_conj]

theorem le_conj_iff {N : VonNeumannAlgebra K} {M : VonNeumannAlgebra H} {U : H ≃ₗᵢ[ℂ] K} :
    N ≤ M.conj U ↔ N.conj U.symm ≤ M := by
  rw [← conj_le_conj_iff (U := U.symm), conj_symm_conj]

theorem conj_injective (U : H ≃ₗᵢ[ℂ] K) :
    Function.Injective fun M : VonNeumannAlgebra H ↦ M.conj U :=
  fun _ _ h ↦ le_antisymm (conj_le_conj_iff.mp h.le) (conj_le_conj_iff.mp h.ge)

/-- Spatial conjugation along `U : H ≃ₗᵢ[ℂ] K` as an order isomorphism between the complete
lattices of von Neumann algebras on `H` and `K`. -/
noncomputable def conjOrderIso (U : H ≃ₗᵢ[ℂ] K) :
    VonNeumannAlgebra H ≃o VonNeumannAlgebra K where
  toFun M := M.conj U
  invFun N := N.conj U.symm
  left_inv M := conj_symm_conj M U
  right_inv N := conj_conj_symm N U
  map_rel_iff' := conj_le_conj_iff

@[simp]
theorem conjOrderIso_apply (U : H ≃ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H) :
    conjOrderIso U M = M.conj U := by
  rfl

@[simp]
theorem conjOrderIso_symm_apply (U : H ≃ₗᵢ[ℂ] K) (N : VonNeumannAlgebra K) :
    (conjOrderIso U).symm N = N.conj U.symm := by
  rfl

/-- Spatial conjugation commutes with taking commutants. -/
@[simp]
theorem commutant_conj (M : VonNeumannAlgebra H) (U : H ≃ₗᵢ[ℂ] K) :
    (M.conj U).commutant = M.commutant.conj U :=
  SetLike.coe_injective <| by
    rw [coe_commutant, coe_conj, MulEquivClass.centralizer_image, coe_conj, coe_commutant]

/-- Spatial conjugation commutes with `VonNeumannAlgebra.adjoin`. -/
@[simp]
theorem conj_adjoin (s : Set (H →L[ℂ] H)) (U : H ≃ₗᵢ[ℂ] K) :
    (adjoin s).conj U = adjoin (U.conjStarAlgEquiv '' s) := by
  refine le_antisymm ?_ (adjoin_le_iff.mpr ?_)
  · rw [conj_le_iff, adjoin_le_iff]
    rintro x hx
    rw [SetLike.mem_coe, mem_conj_iff_symm, LinearIsometryEquiv.symm_symm]
    exact subset_adjoin _ ⟨x, hx, rfl⟩
  · rw [coe_conj]
    exact Set.image_mono (subset_adjoin s)

@[simp]
theorem conj_bot (U : H ≃ₗᵢ[ℂ] K) : (⊥ : VonNeumannAlgebra H).conj U = ⊥ :=
  (conjOrderIso U).map_bot

@[simp]
theorem conj_top (U : H ≃ₗᵢ[ℂ] K) : (⊤ : VonNeumannAlgebra H).conj U = ⊤ :=
  (conjOrderIso U).map_top

@[simp]
theorem conj_sup (M₁ M₂ : VonNeumannAlgebra H) (U : H ≃ₗᵢ[ℂ] K) :
    (M₁ ⊔ M₂).conj U = M₁.conj U ⊔ M₂.conj U :=
  (conjOrderIso U).map_sup M₁ M₂

@[simp]
theorem conj_inf (M₁ M₂ : VonNeumannAlgebra H) (U : H ≃ₗᵢ[ℂ] K) :
    (M₁ ⊓ M₂).conj U = M₁.conj U ⊓ M₂.conj U :=
  (conjOrderIso U).map_inf M₁ M₂

@[simp]
theorem conj_iSup {ι : Sort*} (M : ι → VonNeumannAlgebra H) (U : H ≃ₗᵢ[ℂ] K) :
    (⨆ i, M i).conj U = ⨆ i, (M i).conj U :=
  (conjOrderIso U).map_iSup M

@[simp]
theorem conj_iInf {ι : Sort*} (M : ι → VonNeumannAlgebra H) (U : H ≃ₗᵢ[ℂ] K) :
    (⨅ i, M i).conj U = ⨅ i, (M i).conj U :=
  (conjOrderIso U).map_iInf M

/-- Equal concrete von Neumann algebras on `H` are canonically star-isomorphic. -/
def equivOfEq {M N : VonNeumannAlgebra H} (h : M = N) : M ≃⋆ₐ[ℂ] N where
  toFun x := ⟨x.1, h ▸ x.2⟩
  invFun y := ⟨y.1, h.symm ▸ y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem coe_equivOfEq_apply {M N : VonNeumannAlgebra H} (h : M = N) (x : M) :
    ((equivOfEq h x : N) : H →L[ℂ] H) = x := by
  rfl

@[simp]
theorem equivOfEq_symm {M N : VonNeumannAlgebra H} (h : M = N) :
    (equivOfEq h).symm = equivOfEq h.symm := by
  rfl

/-- The star algebra equivalence `M ≃⋆ₐ[ℂ] M.conj U` induced by spatial conjugation along a
unitary equivalence `U : H ≃ₗᵢ[ℂ] K`. -/
noncomputable def conjStarAlgEquiv (M : VonNeumannAlgebra H) (U : H ≃ₗᵢ[ℂ] K) :
    M ≃⋆ₐ[ℂ] M.conj U where
  toFun x := ⟨U.conjStarAlgEquiv x.1, conjStarAlgEquiv_mem_conj_iff.mpr x.2⟩
  invFun y := ⟨U.symm.conjStarAlgEquiv y.1, mem_conj_iff_symm.mp y.2⟩
  left_inv x := Subtype.ext <| by simp [← LinearIsometryEquiv.symm_conjStarAlgEquiv]
  right_inv y := Subtype.ext <| by simp [← LinearIsometryEquiv.symm_conjStarAlgEquiv]
  map_mul' _ _ := Subtype.ext (map_mul U.conjStarAlgEquiv _ _)
  map_add' _ _ := Subtype.ext (map_add U.conjStarAlgEquiv _ _)
  map_smul' _ _ := Subtype.ext (map_smul U.conjStarAlgEquiv _ _)
  map_star' _ := Subtype.ext (map_star U.conjStarAlgEquiv _)

@[simp]
theorem coe_conjStarAlgEquiv_apply (M : VonNeumannAlgebra H) (U : H ≃ₗᵢ[ℂ] K) (x : M) :
    ((M.conjStarAlgEquiv U x : M.conj U) : K →L[ℂ] K) = U.conjStarAlgEquiv x := by
  rfl

@[simp]
theorem coe_conjStarAlgEquiv_symm_apply (M : VonNeumannAlgebra H) (U : H ≃ₗᵢ[ℂ] K)
    (y : M.conj U) :
    (((M.conjStarAlgEquiv U).symm y : M) : H →L[ℂ] H) = U.symm.conjStarAlgEquiv y := by
  rfl

end VonNeumannAlgebra
