/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Norm
public import TauCeti.Analysis.Normed.Module.Quotient
public import TauCeti.Analysis.Normed.Group.Submodule
import TauCeti.Analysis.Normed.Group.OpenMapping

/-!
# Quotients of module-valued restricted series

For a closed coefficient submodule `N ≤ E`, the native quotient map `E → E ⧸ N` has bounded
lifts. Restricted families therefore preserve its short exact sequence, and Gauss families
carry the quotient topology. Neither completeness nor finitely many variables is required.
These results supply exact quotient sequences before choosing finite module presentations;
they do not assert independence of such presentations.
-/

public section

noncomputable section

namespace Submodule

open TauCeti.MvPowerSeries
open TauCeti.MvPowerSeries.IsRestrictedFamily

section Quotient

variable {σ R E : Type*} [SeminormedRing R] [SeminormedAddCommGroup E]
  [Module R E] [IsBoundedSMul R E] {c : σ → ℝ} (N : Submodule R E)

/-- Include restricted families over a coefficient submodule in families over the ambient
module. The submodule coefficients have their induced norm. -/
def restrictedFamilySubtype :
    IsRestrictedFamily.addSubgroup N c →ₗ[R] IsRestrictedFamily.addSubgroup E c :=
  mapLinearMap N.subtype (C := 1) (fun _ ↦ by simp)

@[simp]
theorem restrictedFamilySubtype_apply (a : IsRestrictedFamily.addSubgroup N c) (t : σ →₀ ℕ) :
    (restrictedFamilySubtype N a).1 t = (a.1 t : E) := by
  exact congrFun (coe_mapLinearMap N.subtype (C := 1) (fun _ ↦ by simp) a) t

/-- Apply the coefficient quotient map to a restricted family. -/
def restrictedFamilyMkQ :
    IsRestrictedFamily.addSubgroup E c →ₗ[R] IsRestrictedFamily.addSubgroup (E ⧸ N) c :=
  mapLinearMap N.mkQ (C := 1) (fun e ↦ by simpa using Submodule.Quotient.norm_mk_le N e)

@[simp]
theorem restrictedFamilyMkQ_apply (a : IsRestrictedFamily.addSubgroup E c) (t : σ →₀ ℕ) :
    (restrictedFamilyMkQ N a).1 t = Submodule.Quotient.mk (a.1 t) := by
  simp [restrictedFamilyMkQ]

/-- Inclusion of a coefficient submodule remains injective on restricted families. -/
theorem restrictedFamilySubtype_injective :
    Function.Injective (restrictedFamilySubtype (c := c) N) :=
  mapLinearMap_injective _ _ Subtype.val_injective

/-- The restricted-family sequence of a submodule and its quotient is exact in the middle.
Closedness is unnecessary for this algebraic assertion. -/
theorem range_restrictedFamilySubtype :
    LinearMap.range (restrictedFamilySubtype (c := c) N) =
      LinearMap.ker (restrictedFamilyMkQ N) := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    apply (mapLinearMap_eq_zero_iff _ _ _).mpr
    intro t
    simpa only [restrictedFamilySubtype_apply, Submodule.mkQ_apply]
      using (Submodule.Quotient.mk_eq_zero N).mpr (a.1 t).2
  · intro a ha
    have hcoeff (t : σ →₀ ℕ) : a.1 t ∈ N :=
      (Submodule.Quotient.mk_eq_zero N).mp
        ((mapLinearMap_eq_zero_iff _ _ _).mp ha t)
    refine ⟨⟨fun t ↦ ⟨a.1 t, hcoeff t⟩, ?_⟩, IsRestrictedFamily.ext fun _ ↦ by simp⟩
    exact mem_addSubgroup.mpr ((mem_addSubgroup.mp a.2).of_norm_le (C := 1) fun _ ↦ by simp)

/-- A family with coefficients in the submodule maps to zero in the quotient. -/
@[simp]
theorem restrictedFamilyMkQ_restrictedFamilySubtype (a : IsRestrictedFamily.addSubgroup N c) :
    restrictedFamilyMkQ N (restrictedFamilySubtype N a) = 0 :=
  LinearMap.mem_ker.mp (range_restrictedFamilySubtype N ▸ LinearMap.mem_range_self _ a)

/-- A restricted family over a closed coefficient quotient has a restricted lift with any
coefficient bound greater than one, at every polyradius. -/
theorem exists_restrictedFamilyMkQ_eq_and_norm_coeff_le [IsClosed (N : Set E)] {L : ℝ}
    (hL : 1 < L) (b : IsRestrictedFamily.addSubgroup (E ⧸ N) c) :
    ∃ a, restrictedFamilyMkQ N a = b ∧ ∀ t, ‖a.1 t‖ ≤ L * ‖b.1 t‖ := by
  apply exists_mapLinearMap_eq_and_norm_coeff_le N.mkQ _
  intro y
  by_cases hy : y = 0
  · exact ⟨0, by simp [hy], by simp [hy]⟩
  · obtain ⟨x, hx, hn⟩ := Submodule.Quotient.norm_mk_lt y
      (mul_pos (sub_pos.mpr hL) (norm_pos_iff.mpr hy))
    exact ⟨x, hx, hn.le.trans_eq (by ring)⟩

/-- Closed coefficient quotients induce surjections of algebraic restricted families, without
any positivity assumption on the radii. -/
theorem restrictedFamilyMkQ_surjective [IsClosed (N : Set E)] :
    Function.Surjective (restrictedFamilyMkQ (c := c) N) := by
  intro b
  obtain ⟨a, ha, -⟩ := exists_restrictedFamilyMkQ_eq_and_norm_coeff_le N (L := 2) (by norm_num) b
  exact ⟨a, ha⟩

section GaussFamilies

/-- The coefficient submodule inclusion on Gauss families. -/
def gaussFamilySubtype : Gauss c N →ₗ[R] Gauss c E :=
  Gauss.mapLinearMap N.subtype (C := 1) (fun _ ↦ by simp)

@[simp]
theorem gaussFamilySubtype_apply (a : Gauss c N) (t : σ →₀ ℕ) :
    gaussFamilySubtype N a t = (a t : E) := by
  exact Gauss.mapLinearMap_apply N.subtype (C := 1) (fun _ ↦ by simp) a t

/-- The coefficient quotient map on Gauss families. -/
def gaussFamilyMkQ : Gauss c E →ₗ[R] Gauss c (E ⧸ N) :=
  Gauss.mapLinearMap N.mkQ (C := 1) (fun e ↦ by simpa using Submodule.Quotient.norm_mk_le N e)

@[simp]
theorem gaussFamilyMkQ_apply (a : Gauss c E) (t : σ →₀ ℕ) :
    gaussFamilyMkQ N a t = Submodule.Quotient.mk (a t) := by simp [gaussFamilyMkQ]

/-- Inclusion of a coefficient submodule is injective on Gauss families. -/
theorem gaussFamilySubtype_injective : Function.Injective (gaussFamilySubtype (c := c) N) := by
  intro a b h
  apply Gauss.ext
  intro t
  exact Subtype.val_injective (by simpa using congrArg (fun d : Gauss c E ↦ d t) h)

/-- The Gauss-family sequence of a submodule and its quotient is exact in the middle. -/
theorem range_gaussFamilySubtype :
    LinearMap.range (gaussFamilySubtype (c := c) N) = LinearMap.ker (gaussFamilyMkQ N) := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    apply Gauss.ext
    intro t
    simp
  · intro a ha
    have hzero : restrictedFamilyMkQ N a.toAddSubgroup = 0 := by
      apply IsRestrictedFamily.ext
      intro t
      simpa using congrArg (fun b : Gauss c (E ⧸ N) ↦ b t) ha
    have hmem : a.toAddSubgroup ∈ LinearMap.ker (restrictedFamilyMkQ N) := hzero
    rw [← range_restrictedFamilySubtype] at hmem
    obtain ⟨b, hb⟩ := hmem
    refine ⟨Gauss.ofAddSubgroup b, Gauss.ext fun t ↦ ?_⟩
    simpa only [gaussFamilySubtype_apply, Gauss.ofAddSubgroup_apply,
      restrictedFamilySubtype_apply]
      using congrFun (congrArg Subtype.val hb) t

/-- A Gauss family with coefficients in the submodule maps to zero in the quotient. -/
@[simp]
theorem gaussFamilyMkQ_gaussFamilySubtype (a : Gauss c N) :
    gaussFamilyMkQ N (gaussFamilySubtype N a) = 0 :=
  LinearMap.mem_ker.mp (range_gaussFamilySubtype N ▸ LinearMap.mem_range_self _ a)

/-- The quotient map on coefficients is surjective on Gauss families, without any positivity
assumption on the radii. -/
theorem gaussFamilyMkQ_surjective [IsClosed (N : Set E)] :
    Function.Surjective (gaussFamilyMkQ (c := c) N) := by
  intro b
  obtain ⟨a, ha⟩ := restrictedFamilyMkQ_surjective N b.toAddSubgroup
  refine ⟨Gauss.ofAddSubgroup a, Gauss.ext fun t ↦ ?_⟩
  simpa only [gaussFamilyMkQ_apply, Gauss.ofAddSubgroup_apply,
    restrictedFamilyMkQ_apply]
    using congrFun (congrArg Subtype.val ha) t

variable [∀ i, Fact (0 < c i)]

/-- The coefficient submodule inclusion preserves the Gauss seminorm. -/
theorem isometry_gaussFamilySubtype : Isometry (gaussFamilySubtype (c := c) N) := by
  apply (AddMonoidHomClass.isometry_iff_norm _).mpr
  intro a
  simp only [Gauss.norm_eq_iSup, gaussFamilySubtype_apply, Submodule.norm_coe]

/-- The coefficient quotient map is contractive for the Gauss seminorm. -/
theorem norm_gaussFamilyMkQ_le (a : Gauss c E) : ‖gaussFamilyMkQ N a‖ ≤ ‖a‖ := by
  simpa [gaussFamilyMkQ] using Gauss.norm_mapLinearMap_le N.mkQ (C := 1) zero_le_one
    (fun e ↦ by simpa using Submodule.Quotient.norm_mk_le N e) a

variable [IsClosed (N : Set E)]

/-- Quotient Gauss families have lifts with any prescribed multiplicative bound greater than
one. This does not require a norm-minimizing representative of each coefficient class. -/
theorem exists_gaussFamilyMkQ_eq_and_norm_le {L : ℝ} (hL : 1 < L)
    (b : Gauss c (E ⧸ N)) :
    ∃ a, gaussFamilyMkQ N a = b ∧ ‖a‖ ≤ L * ‖b‖ := by
  obtain ⟨a, ha, hcoeff⟩ :=
    exists_restrictedFamilyMkQ_eq_and_norm_coeff_le N hL b.toAddSubgroup
  refine ⟨Gauss.ofAddSubgroup a, Gauss.ext fun t ↦ ?_,
    Gauss.norm_le_mul_of_norm_coeff_le (zero_lt_one.trans hL).le hcoeff⟩
  simpa only [gaussFamilyMkQ_apply, Gauss.ofAddSubgroup_apply,
    restrictedFamilyMkQ_apply]
    using congrFun (congrArg Subtype.val ha) t

/-- The quotient map on coefficients is open on Gauss families. -/
theorem isOpenMap_gaussFamilyMkQ : IsOpenMap (gaussFamilyMkQ (c := c) N) :=
  TauCeti.isOpenMap_of_exists_norm_le _
    (exists_gaussFamilyMkQ_eq_and_norm_le N (L := 2) (by norm_num))

/-- Restricted Gauss families over a closed coefficient quotient have the quotient topology. -/
theorem isQuotientMap_gaussFamilyMkQ :
    Topology.IsQuotientMap (gaussFamilyMkQ (c := c) N) :=
  (isOpenMap_gaussFamilyMkQ N).isQuotientMap
    (Gauss.uniformContinuous_mapLinearMap N.mkQ zero_le_one
      (fun e ↦ by simpa using Submodule.Quotient.norm_mk_le N e)).continuous
    (gaussFamilyMkQ_surjective N)

end GaussFamilies
end Quotient

end Submodule
