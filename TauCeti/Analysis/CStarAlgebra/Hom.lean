/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import TauCeti.Topology.Algebra.Ring.TwoSidedIdeal
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit

/-!
# Topological and norm properties of C⋆-algebra homomorphisms and equivalences

A `⋆`-algebra homomorphism between complex C⋆-algebras is automatically continuous and contractive:
* its two-sided ideal kernel is closed (`NonUnitalStarAlgHom.isClosed_ker`, stated for any morphism
  class, so it covers unital `⋆`-homomorphisms and `⋆`-equivalences as well);
* it bundles as a continuous linear map (`NonUnitalStarAlgHom.toContinuousLinearMap`,
  `StarAlgHom.toContinuousLinearMap`) whose operator norm is `1` when nonzero and `0` when zero
  (`NonUnitalStarAlgHom.norm_toContinuousLinearMap_eq_one_or_zero`), by testing against an
  increasing approximate unit;
* a `⋆`-algebra equivalence of complex C⋆-algebras is isometric (`StarAlgEquiv.isometry`), so it
  bundles as a continuous linear equivalence `StarAlgEquiv.toContinuousLinearEquiv`.
-/

public section

open Filter Topology
open scoped CStarAlgebra

namespace NonUnitalStarAlgHom

section Ker

variable {F A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B] (φ : F)

/-- The two-sided ideal kernel of any `⋆`-homomorphism between C⋆-algebras (unital or not, and
in any morphism class) is closed. -/
instance isClosed_ker : IsClosed (TwoSidedIdeal.ker φ : Set A) :=
  TwoSidedIdeal.isClosed_ker (map_continuous φ)

end Ker

section OpNorm

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- A `⋆`-algebra homomorphism between complex C⋆-algebras bundled as a continuous linear map. -/
noncomputable def toContinuousLinearMap (φ : A →⋆ₙₐ[ℂ] B) : A →L[ℂ] B where
  toFun := φ
  map_add' := map_add φ
  map_smul' := map_smul φ
  cont := map_continuous φ

@[simp]
theorem coe_toContinuousLinearMap (φ : A →⋆ₙₐ[ℂ] B) : ⇑φ.toContinuousLinearMap = φ :=
  (rfl)

theorem toContinuousLinearMap_injective :
    Function.Injective (toContinuousLinearMap (A := A) (B := B)) :=
  fun _ _ h ↦ DFunLike.ext _ _ fun x ↦ congr($(h) x)

@[simp]
theorem toContinuousLinearMap_inj {φ ψ : A →⋆ₙₐ[ℂ] B} :
    φ.toContinuousLinearMap = ψ.toContinuousLinearMap ↔ φ = ψ :=
  toContinuousLinearMap_injective.eq_iff

@[simp]
theorem toContinuousLinearMap_zero : (0 : A →⋆ₙₐ[ℂ] B).toContinuousLinearMap = 0 := by
  ext
  simp

@[simp]
theorem toContinuousLinearMap_eq_zero_iff {φ : A →⋆ₙₐ[ℂ] B} :
    φ.toContinuousLinearMap = 0 ↔ φ = 0 := by
  rw [← toContinuousLinearMap_zero, toContinuousLinearMap_inj]

@[simp]
theorem toContinuousLinearMap_id :
    (NonUnitalStarAlgHom.id ℂ A).toContinuousLinearMap = ContinuousLinearMap.id ℂ A := by
  ext
  simp

theorem toContinuousLinearMap_comp {C : Type*} [NonUnitalCStarAlgebra C]
    (ψ : B →⋆ₙₐ[ℂ] C) (φ : A →⋆ₙₐ[ℂ] B) :
    (ψ.comp φ).toContinuousLinearMap = ψ.toContinuousLinearMap.comp φ.toContinuousLinearMap := by
  ext
  simp

/-- Every `⋆`-algebra homomorphism between complex C⋆-algebras has operator norm at most `1`. -/
theorem norm_toContinuousLinearMap_le_one (φ : A →⋆ₙₐ[ℂ] B) :
    ‖φ.toContinuousLinearMap‖ ≤ 1 :=
  φ.toContinuousLinearMap.opNorm_le_bound zero_le_one fun a ↦ by
    simpa using norm_apply_le φ a

/-- A `⋆`-algebra homomorphism between complex C⋆-algebras that does not vanish at `x` has operator
norm `1`. -/
theorem norm_toContinuousLinearMap_of_apply_ne_zero {φ : A →⋆ₙₐ[ℂ] B} {x : A} (hx : φ x ≠ 0) :
    ‖φ.toContinuousLinearMap‖ = 1 := by
  refine le_antisymm φ.norm_toContinuousLinearMap_le_one ?_
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  have hlim : Tendsto (fun e ↦ ‖φ (e * x)‖) (CStarAlgebra.approximateUnit A) (𝓝 ‖φ x‖) :=
    (continuous_norm.comp (map_continuous φ)).tendsto x |>.comp (hl.tendsto_mul_right x)
  have hle : ‖φ x‖ ≤ ‖φ.toContinuousLinearMap‖ * ‖φ x‖ := by
    refine le_of_tendsto hlim (hl.eventually_norm.mono fun e he ↦ ?_)
    calc ‖φ (e * x)‖ = ‖φ e * φ x‖ := by rw [map_mul]
      _ ≤ ‖φ e‖ * ‖φ x‖ := norm_mul_le _ _
      _ ≤ (‖φ.toContinuousLinearMap‖ * ‖e‖) * ‖φ x‖ := by
        gcongr
        simpa using φ.toContinuousLinearMap.le_opNorm e
      _ ≤ ‖φ.toContinuousLinearMap‖ * ‖φ x‖ := by
        gcongr
        exact mul_le_of_le_one_right (norm_nonneg _) he
  exact (le_mul_iff_one_le_left (norm_pos_iff.2 hx)).1 hle

/-- Every nonzero `⋆`-algebra homomorphism between complex C⋆-algebras has operator norm `1`. -/
theorem norm_toContinuousLinearMap_of_ne_zero {φ : A →⋆ₙₐ[ℂ] B} (hφ : φ ≠ 0) :
    ‖φ.toContinuousLinearMap‖ = 1 := by
  obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
    contrapose! hφ
    ext a
    exact hφ a
  exact norm_toContinuousLinearMap_of_apply_ne_zero hx

/-- Operator-norm dichotomy: the operator norm of any `⋆`-algebra homomorphism between complex
C⋆-algebras is either `1` or `0`. -/
theorem norm_toContinuousLinearMap_eq_one_or_zero (φ : A →⋆ₙₐ[ℂ] B) :
    ‖φ.toContinuousLinearMap‖ = 1 ∨ ‖φ.toContinuousLinearMap‖ = 0 := by
  rcases ne_or_eq φ 0 with hφ | rfl
  · exact Or.inl (norm_toContinuousLinearMap_of_ne_zero hφ)
  · exact Or.inr (norm_eq_zero.2 (toContinuousLinearMap_eq_zero_iff.2 rfl))

end OpNorm

end NonUnitalStarAlgHom

namespace StarAlgHom

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- A unital `⋆`-algebra homomorphism between complex C⋆-algebras bundled as a continuous linear
map. -/
noncomputable def toContinuousLinearMap (φ : A →⋆ₐ[ℂ] B) : A →L[ℂ] B :=
  φ.toNonUnitalStarAlgHom.toContinuousLinearMap

@[simp]
theorem coe_toContinuousLinearMap (φ : A →⋆ₐ[ℂ] B) : ⇑φ.toContinuousLinearMap = φ :=
  (rfl)

@[simp]
theorem toContinuousLinearMap_toNonUnitalStarAlgHom (φ : A →⋆ₐ[ℂ] B) :
    φ.toNonUnitalStarAlgHom.toContinuousLinearMap = φ.toContinuousLinearMap :=
  (rfl)

theorem toContinuousLinearMap_injective :
    Function.Injective (toContinuousLinearMap (A := A) (B := B)) :=
  fun _ _ h ↦ DFunLike.ext _ _ fun x ↦ congr($(h) x)

@[simp]
theorem toContinuousLinearMap_inj {φ ψ : A →⋆ₐ[ℂ] B} :
    φ.toContinuousLinearMap = ψ.toContinuousLinearMap ↔ φ = ψ :=
  toContinuousLinearMap_injective.eq_iff

@[simp]
theorem toContinuousLinearMap_id :
    (StarAlgHom.id ℂ A).toContinuousLinearMap = ContinuousLinearMap.id ℂ A := by
  ext
  simp

theorem toContinuousLinearMap_comp {C : Type*} [CStarAlgebra C]
    (ψ : B →⋆ₐ[ℂ] C) (φ : A →⋆ₐ[ℂ] B) :
    (ψ.comp φ).toContinuousLinearMap = ψ.toContinuousLinearMap.comp φ.toContinuousLinearMap := by
  ext
  simp

/-- Every unital `⋆`-algebra homomorphism between complex C⋆-algebras has operator norm at most
`1`. -/
theorem norm_toContinuousLinearMap_le_one (φ : A →⋆ₐ[ℂ] B) :
    ‖φ.toContinuousLinearMap‖ ≤ 1 :=
  φ.toNonUnitalStarAlgHom.norm_toContinuousLinearMap_le_one

/-- Every unital `⋆`-algebra homomorphism into a nontrivial complex C⋆-algebra has operator norm
`1`. -/
theorem norm_toContinuousLinearMap [Nontrivial B] (φ : A →⋆ₐ[ℂ] B) :
    ‖φ.toContinuousLinearMap‖ = 1 :=
  NonUnitalStarAlgHom.norm_toContinuousLinearMap_of_apply_ne_zero (x := 1) (by simp)

/-- Operator-norm dichotomy for unital `⋆`-algebra homomorphisms between complex C⋆-algebras. -/
theorem norm_toContinuousLinearMap_eq_one_or_zero (φ : A →⋆ₐ[ℂ] B) :
    ‖φ.toContinuousLinearMap‖ = 1 ∨ ‖φ.toContinuousLinearMap‖ = 0 :=
  φ.toNonUnitalStarAlgHom.norm_toContinuousLinearMap_eq_one_or_zero

end StarAlgHom

namespace StarAlgEquiv

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- A star-algebra equivalence of C⋆-algebras as a continuous linear equivalence. Both directions
are continuous because star-algebra equivalences of C⋆-algebras are isometric. -/
def toContinuousLinearEquiv (e : A ≃⋆ₐ[ℂ] B) : A ≃L[ℂ] B where
  toFun := e
  invFun := e.symm
  left_inv := e.symm_apply_apply
  right_inv := e.apply_symm_apply
  map_add' := map_add e
  map_smul' := map_smul e
  continuous_toFun := (StarAlgEquiv.isometry e).continuous
  continuous_invFun := (StarAlgEquiv.isometry e.symm).continuous

@[simp]
theorem coe_toContinuousLinearEquiv (e : A ≃⋆ₐ[ℂ] B) : ⇑e.toContinuousLinearEquiv = e :=
  (rfl)

@[simp]
theorem toContinuousLinearEquiv_symm (e : A ≃⋆ₐ[ℂ] B) :
    e.toContinuousLinearEquiv.symm = e.symm.toContinuousLinearEquiv :=
  (rfl)

@[simp]
theorem toContinuousLinearEquiv_refl :
    (StarAlgEquiv.refl ℂ A).toContinuousLinearEquiv = ContinuousLinearEquiv.refl ℂ A := by
  ext
  simp

@[simp]
theorem toContinuousLinearEquiv_trans {C : Type*} [NonUnitalCStarAlgebra C]
    (e₁ : A ≃⋆ₐ[ℂ] B) (e₂ : B ≃⋆ₐ[ℂ] C) :
    (e₁.trans e₂).toContinuousLinearEquiv =
      e₁.toContinuousLinearEquiv.trans e₂.toContinuousLinearEquiv := by
  ext
  simp

@[simp]
theorem toContinuousLinearMap_toNonUnitalStarAlgHom (e : A ≃⋆ₐ[ℂ] B) :
    e.toNonUnitalStarAlgHom.toContinuousLinearMap = (e.toContinuousLinearEquiv : A →L[ℂ] B) := by
  ext
  simp

@[simp]
theorem toContinuousLinearMap_toStarAlgHom {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (e : A ≃⋆ₐ[ℂ] B) :
    e.toStarAlgHom.toContinuousLinearMap = (e.toContinuousLinearEquiv : A →L[ℂ] B) := by
  ext
  simp

end StarAlgEquiv
