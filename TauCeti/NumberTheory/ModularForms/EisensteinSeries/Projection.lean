/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Congruence
import Mathlib.LinearAlgebra.Projection

/-!
# The Eisenstein projection and nebentypus

In weight at least three, the congruence Eisenstein subspace is complementary to the cusp
forms. Projection along this complement preserves every cusp constant term and is uniquely
determined by that property among Eisenstein forms.

For `Γ₁(N)`, the projection commutes with diamond operators: slashing permutes the primitive
residue-class Eisenstein series, while diamond operators preserve cusp forms. Consequently the
Eisenstein and cusp components of a form with prescribed nebentypus have that same nebentypus.
This gives a complementary decomposition inside `M_k(N, χ)` using the restriction of the
congruence Eisenstein subspace. Identifying this subspace with the span of the prescribed
primitive-character Eisenstein series is a separate spanning statement.

## Main results

* `congruenceEisensteinProjection`: projection to the congruence Eisenstein subspace.
* `constantTerms_congruenceEisensteinProjection`: projection preserves all cusp constant terms.
* `congruenceEisensteinProjection_eq_iff_constantTerms_eq`: its constant-term characterization.
* `congruenceEisensteinProjection_commute_diamondOp`: diamond equivariance.
* `isCompl_congruenceEisensteinSubspace_charSpace_range_cuspToModFormCharSpace`: the
  complementary decomposition with fixed nebentypus.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Sections 4.2 and 4.5.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup ModularForm CongruenceSubgroup
open _root_.EisensteinSeries
open scoped MatrixGroups

namespace TauCeti.EisensteinSeries

variable {N : ℕ} {k : ℤ} [NeZero N] {Γ : Subgroup SL(2, ℤ)}

/-- The projection to the congruence Eisenstein subspace along the cusp forms. -/
def congruenceEisensteinProjection (hΓ : Gamma N ≤ Γ) (hk : 3 ≤ k) :
    Module.End ℂ (ModularForm (Γ.map (mapGL ℝ)) k) :=
  (congruenceEisensteinSubspace hΓ hk).projection
    (cuspFormSubmodule (Γ.map (mapGL ℝ)) k)
    (isCompl_congruenceEisensteinSubspace_cuspFormSubmodule hΓ hk)

/-- The Eisenstein projection is the projection associated to the complementary subspaces. -/
theorem congruenceEisensteinProjection_def (hΓ : Gamma N ≤ Γ) (hk : 3 ≤ k) :
    congruenceEisensteinProjection hΓ hk =
      (congruenceEisensteinSubspace hΓ hk).projection
        (cuspFormSubmodule (Γ.map (mapGL ℝ)) k)
        (isCompl_congruenceEisensteinSubspace_cuspFormSubmodule hΓ hk) := (rfl)

/-- The Eisenstein component belongs to the congruence Eisenstein subspace. -/
@[simp]
theorem congruenceEisensteinProjection_mem (hΓ : Gamma N ≤ Γ) (hk : 3 ≤ k)
    (f : ModularForm (Γ.map (mapGL ℝ)) k) :
    congruenceEisensteinProjection hΓ hk f ∈ congruenceEisensteinSubspace hΓ hk := by
  rw [congruenceEisensteinProjection_def]
  exact Submodule.projection_apply_mem _ _

/-- The difference between a form and its Eisenstein component is cuspidal. -/
theorem sub_congruenceEisensteinProjection_mem_cuspFormSubmodule
    (hΓ : Gamma N ≤ Γ) (hk : 3 ≤ k) (f : ModularForm (Γ.map (mapGL ℝ)) k) :
    f - congruenceEisensteinProjection hΓ hk f ∈
      cuspFormSubmodule (Γ.map (mapGL ℝ)) k := by
  rw [congruenceEisensteinProjection_def]
  exact Submodule.sub_projection_mem _ _

/-- A form is fixed by the Eisenstein projection exactly when it is Eisenstein. -/
@[simp]
theorem congruenceEisensteinProjection_eq_self_iff (hΓ : Gamma N ≤ Γ) (hk : 3 ≤ k)
    (f : ModularForm (Γ.map (mapGL ℝ)) k) :
    congruenceEisensteinProjection hΓ hk f = f ↔ f ∈ congruenceEisensteinSubspace hΓ hk := by
  rw [congruenceEisensteinProjection_def]
  exact Submodule.projection_eq_self_iff _ _

/-- The Eisenstein component vanishes exactly when the original form is cuspidal. -/
@[simp]
theorem congruenceEisensteinProjection_eq_zero_iff (hΓ : Gamma N ≤ Γ) (hk : 3 ≤ k)
    (f : ModularForm (Γ.map (mapGL ℝ)) k) :
    congruenceEisensteinProjection hΓ hk f = 0 ↔
      f ∈ cuspFormSubmodule (Γ.map (mapGL ℝ)) k := by
  rw [congruenceEisensteinProjection_def]
  exact Submodule.projection_apply_eq_zero_iff _

section ConstantTerms

-- The constant-term map takes the ambient arithmetic instance as a parameter. Containment of
-- `Γ(N)` implies arithmeticity mathematically, but instance search does not use `hΓ`.
variable [(Γ.map (mapGL ℝ)).IsArithmetic]

/-- The Eisenstein component has the same constant term at every cusp as the original form. -/
@[simp↓]
theorem constantTermAt_congruenceEisensteinProjection (hΓ : Gamma N ≤ Γ) (hk : 3 ≤ k)
    (f : ModularForm (Γ.map (mapGL ℝ)) k) (γ : SL(2, ℤ)) :
    constantTermAt γ (congruenceEisensteinProjection hΓ hk f) = constantTermAt γ f := by
  have h := (mem_cuspFormSubmodule_iff_constantTermAt_eq_zero _).mp
    (sub_congruenceEisensteinProjection_mem_cuspFormSubmodule hΓ hk f) γ
  rw [map_sub, sub_eq_zero] at h
  exact h.symm

/-- The Eisenstein projection preserves the collection of all cusp constant terms. -/
@[simp]
theorem constantTerms_congruenceEisensteinProjection (hΓ : Gamma N ≤ Γ) (hk : 3 ≤ k)
    (f : ModularForm (Γ.map (mapGL ℝ)) k) :
    constantTerms (congruenceEisensteinProjection hΓ hk f) = constantTerms f := by
  ext γ
  simp only [constantTerms_apply]
  exact constantTermAt_congruenceEisensteinProjection hΓ hk f γ

/-- Among Eisenstein forms, the projection of `f` is characterized by having all the same
cusp constant terms as `f`. -/
theorem congruenceEisensteinProjection_eq_iff_constantTerms_eq (hΓ : Gamma N ≤ Γ)
    (hk : 3 ≤ k) (f e : ModularForm (Γ.map (mapGL ℝ)) k)
    (he : e ∈ congruenceEisensteinSubspace hΓ hk) :
    congruenceEisensteinProjection hΓ hk f = e ↔ constantTerms e = constantTerms f := by
  constructor
  · intro h
    rw [← h, constantTerms_congruenceEisensteinProjection]
  · intro h
    have hE := Submodule.sub_mem _ (congruenceEisensteinProjection_mem hΓ hk f) he
    have hS : congruenceEisensteinProjection hΓ hk f - e ∈
        cuspFormSubmodule (Γ.map (mapGL ℝ)) k := by
      rw [← ker_constantTerms, LinearMap.mem_ker, map_sub,
        constantTerms_congruenceEisensteinProjection, h, sub_self]
    exact sub_eq_zero.mp ((Submodule.disjoint_def.mp
      (disjoint_congruenceEisensteinSubspace_cuspFormSubmodule hΓ hk)) _ hE hS)

end ConstantTerms

/-- Diamond operators preserve the congruence Eisenstein subspace of `Γ₁(N)`. -/
theorem diamondOp_mem_congruenceEisensteinSubspace (hk : 3 ≤ k) (d : (ZMod N)ˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ congruenceEisensteinSubspace (Gamma_le_Gamma1 N) hk) :
    diamondOp k d f ∈ congruenceEisensteinSubspace (Gamma_le_Gamma1 N) hk := by
  classical
  obtain ⟨g, hg⟩ := Gamma0Map_toHomUnits_surjective (N := N) d
  obtain ⟨c, hc⟩ := (mem_primitiveEisensteinSubspace_iff hk _).mp
    ((mem_congruenceEisensteinSubspace_iff (Gamma_le_Gamma1 N) hk f).mp hf)
  have hcoe : ⇑f = ∑ a, c a • eisensteinSeries a k := by
    simpa only [FunLike.coe_sum, FunLike.coe_smul, coe_eisensteinSeriesMF,
      ModularForm.coe_ofLe] using (congrArg DFunLike.coe hc).symm
  have hsum : ModularForm.ofLe (Subgroup.map_mono (Gamma_le_Gamma1 N)) (diamondOp k d f) =
      ∑ a, c a • eisensteinSeriesMF hk
        (a ᵥ* SpecialLinearGroup.map (Int.castRingHom (ZMod N)) (g : SL(2, ℤ))) := by
    apply DFunLike.coe_injective
    rw [ModularForm.coe_ofLe, coe_diamondOp k d g hg, hcoe, SlashAction.sum_slash]
    simp only [FunLike.coe_sum, FunLike.coe_smul, coe_eisensteinSeriesMF,
      ModularForm.smul_slash, σ_mapGL_real_eq_refl,
      ContinuousAlgEquiv.refl_apply]
    congr 1
    ext a z
    have hslash : eisensteinSeries a k ∣[k] mapGL ℝ (g : SL(2, ℤ)) =
        eisensteinSeries a k ∣[k] (g : SL(2, ℤ)) :=
      (ModularForm.SL_slash (eisensteinSeries a k) (g : SL(2, ℤ))).symm
    exact congrFun (congrArg (fun F : UpperHalfPlane → ℂ ↦ c a • F)
      (hslash.trans (eisensteinSeries_slash_apply a k (g : SL(2, ℤ))))) z
  rw [mem_congruenceEisensteinSubspace_iff, hsum]
  exact Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _
    (mem_primitiveEisensteinSubspace hk _)

/-- The Eisenstein projection on `Γ₁(N)` commutes with every diamond operator. -/
theorem congruenceEisensteinProjection_commute_diamondOp (hk : 3 ≤ k) (d : (ZMod N)ˣ) :
    Commute (congruenceEisensteinProjection (Gamma_le_Gamma1 N) hk) (diamondOp k d) := by
  rw [congruenceEisensteinProjection_def]
  apply (LinearMap.IsIdempotentElem.commute_iff
    (Submodule.isIdempotentElem_projection _)).mpr
  rw [Submodule.range_projection, Submodule.ker_projection]
  constructor
  · exact (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr
      (fun f hf ↦ diamondOp_mem_congruenceEisensteinSubspace hk d hf)
  · apply (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr
    rintro f ⟨s, rfl⟩
    rw [CuspForm.toModularFormₗ_eq_coe, diamondOp_coe_cuspForm]
    exact CuspForm.isCuspForm_toModularFormₗ _

/-- The Eisenstein component preserves the prescribed nebentypus of a modular form. -/
theorem congruenceEisensteinProjection_mem_modFormCharSpace (hk : 3 ≤ k)
    (χ : (ZMod N)ˣ →* ℂˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    congruenceEisensteinProjection (Gamma_le_Gamma1 N) hk f ∈ modFormCharSpace k χ := by
  rw [mem_modFormCharSpace_iff]
  intro d
  rw [diamondOpHom_apply]
  have hc := (congruenceEisensteinProjection_commute_diamondOp hk d).eq
  have h := LinearMap.congr_fun hc f
  rw [Module.End.mul_apply, Module.End.mul_apply,
    diamondOp_apply_of_mem_modFormCharSpace k χ d hf, map_smul] at h
  exact h.symm

/-- In weight at least three, the restriction of the congruence Eisenstein subspace to a
nebentypus space is complementary to the cusp forms of that same nebentypus. -/
theorem isCompl_congruenceEisensteinSubspace_charSpace_range_cuspToModFormCharSpace
    (hk : 3 ≤ k) (χ : (ZMod N)ˣ →* ℂˣ) :
    IsCompl ((congruenceEisensteinSubspace (Gamma_le_Gamma1 N) hk).comap
      (modFormCharSpace k χ).subtype) (LinearMap.range (cuspToModFormCharSpace k χ)) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro f hfE hfS
    apply Subtype.ext
    have hfC : (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) ∈
        cuspFormSubmodule ((Gamma1 N).map (mapGL ℝ)) k := by
      obtain ⟨s, rfl⟩ := hfS
      rw [coe_cuspToModFormCharSpace]
      exact CuspForm.isCuspForm_toModularFormₗ _
    exact (Submodule.disjoint_def.mp
      (disjoint_congruenceEisensteinSubspace_cuspFormSubmodule (Gamma_le_Gamma1 N) hk)) _
        hfE hfC
  · apply codisjoint_iff.mpr
    apply eq_top_iff.mpr
    intro f _
    let e : modFormCharSpace k χ :=
      ⟨congruenceEisensteinProjection (Gamma_le_Gamma1 N) hk f,
        congruenceEisensteinProjection_mem_modFormCharSpace hk χ f.2⟩
    have he : e ∈ (congruenceEisensteinSubspace (Gamma_le_Gamma1 N) hk).comap
        (modFormCharSpace k χ).subtype := by
      rw [Submodule.mem_comap, Submodule.subtype_apply]
      exact congruenceEisensteinProjection_mem (Gamma_le_Gamma1 N) hk
        (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    have hs : f - e ∈ LinearMap.range (cuspToModFormCharSpace k χ) := by
      rw [range_cuspToModFormCharSpace_eq_ker_constantTerms, LinearMap.mem_ker,
        LinearMap.comp_apply, Submodule.subtype_apply, Submodule.coe_sub, map_sub]
      exact sub_eq_zero.mpr (constantTerms_congruenceEisensteinProjection
        (Gamma_le_Gamma1 N) hk f).symm
    exact Submodule.mem_sup.mpr ⟨e, he, f - e, hs, add_sub_cancel _ _⟩

end TauCeti.EisensteinSeries
