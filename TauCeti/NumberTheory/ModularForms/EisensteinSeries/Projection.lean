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

* `congruenceEisensteinProjection`: projection to the congruence Eisenstein subspace, with
  range, kernel and idempotence characterizations.
* `constantTerms_congruenceEisensteinProjection`: projection preserves all cusp constant terms.
* `congruenceEisensteinProjection_eq_iff_constantTerms_eq`: its constant-term characterization.
* `congruenceEisensteinProjection_diamondOp`: pointwise equivariance under diamond operators.
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

/-- The range of the Eisenstein projection is the congruence Eisenstein subspace. -/
@[simp]
theorem range_congruenceEisensteinProjection (hΓ : Gamma N ≤ Γ) (hk : 3 ≤ k) :
    LinearMap.range (congruenceEisensteinProjection hΓ hk) =
      congruenceEisensteinSubspace hΓ hk := by
  rw [congruenceEisensteinProjection_def]
  exact Submodule.range_projection _

/-- The kernel of the Eisenstein projection is the cusp-form submodule. -/
@[simp]
theorem ker_congruenceEisensteinProjection (hΓ : Gamma N ≤ Γ) (hk : 3 ≤ k) :
    LinearMap.ker (congruenceEisensteinProjection hΓ hk) =
      cuspFormSubmodule (Γ.map (mapGL ℝ)) k := by
  rw [congruenceEisensteinProjection_def]
  exact Submodule.ker_projection _

/-- The Eisenstein projection is an idempotent endomorphism. -/
theorem isIdempotentElem_congruenceEisensteinProjection (hΓ : Gamma N ≤ Γ) (hk : 3 ≤ k) :
    IsIdempotentElem (congruenceEisensteinProjection hΓ hk) := by
  rw [congruenceEisensteinProjection_def]
  exact Submodule.isIdempotentElem_projection _

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
  rw [congruenceEisensteinSubspace_def] at hf ⊢
  exact diamondOp_mem_comap_restrictₗ
    (fun γ _ _ hg ↦ gammaSlashₗ_mem_primitiveEisensteinSubspace hk γ hg) d hf

/-- The Eisenstein projection on `Γ₁(N)` commutes with every diamond operator. -/
theorem congruenceEisensteinProjection_commute_diamondOp (hk : 3 ≤ k) (d : (ZMod N)ˣ) :
    Commute (congruenceEisensteinProjection (Gamma_le_Gamma1 N) hk) (diamondOp k d) := by
  rw [congruenceEisensteinProjection_def]
  exact commute_projection_diamondOp _
    fun _ hf ↦ diamondOp_mem_congruenceEisensteinSubspace hk d hf

/-- Projecting the diamond translate of a form agrees with translating its Eisenstein
component. -/
theorem congruenceEisensteinProjection_diamondOp (hk : 3 ≤ k) (d : (ZMod N)ˣ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    congruenceEisensteinProjection (Gamma_le_Gamma1 N) hk (diamondOp k d f) =
      diamondOp k d (congruenceEisensteinProjection (Gamma_le_Gamma1 N) hk f) := by
  exact LinearMap.congr_fun (congruenceEisensteinProjection_commute_diamondOp hk d).eq f

/-- The Eisenstein component preserves the prescribed nebentypus of a modular form. -/
theorem congruenceEisensteinProjection_mem_modFormCharSpace (hk : 3 ≤ k)
    (χ : (ZMod N)ˣ →* ℂˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    congruenceEisensteinProjection (Gamma_le_Gamma1 N) hk f ∈ modFormCharSpace k χ := by
  rw [mem_modFormCharSpace_iff]
  intro d
  rw [diamondOpHom_apply]
  rw [← congruenceEisensteinProjection_diamondOp,
    diamondOp_apply_of_mem_modFormCharSpace k χ d hf, map_smul]

/-- In weight at least three, the restriction of the congruence Eisenstein subspace to a
nebentypus space is complementary to the cusp forms of that same nebentypus. -/
theorem isCompl_congruenceEisensteinSubspace_charSpace_range_cuspToModFormCharSpace
    (hk : 3 ≤ k) (χ : (ZMod N)ˣ →* ℂˣ) :
    IsCompl ((congruenceEisensteinSubspace (Gamma_le_Gamma1 N) hk).comap
      (modFormCharSpace k χ).subtype) (LinearMap.range (cuspToModFormCharSpace k χ)) :=
  isCompl_comap_subtype_range_cuspToModFormCharSpace
    (isCompl_congruenceEisensteinSubspace_cuspFormSubmodule (Gamma_le_Gamma1 N) hk)
    (fun d _ hf ↦ diamondOp_mem_congruenceEisensteinSubspace hk d hf) χ

end TauCeti.EisensteinSeries
