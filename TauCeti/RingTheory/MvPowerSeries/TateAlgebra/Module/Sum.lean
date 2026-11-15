/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Norm
import TauCeti.Data.Finsupp.Sum
import TauCeti.Data.Finsupp.Weight

/-!
# Iterating module-valued restricted series

Splitting the variables into two arbitrary sets identifies restricted coefficient families
with iterated restricted families, isometrically for their Gauss norms at positive polyradii.
The outer restrictedness condition concerns the Gauss norms of the slices, not just their
individual coefficients. This distinction is essential for iterating analytic operations on
module-valued series.

These lemmas generalise the scalar iteration argument, without ring or ultrametric
assumptions on the coefficient group. The scalar equivalence
`TauCeti.MvPowerSeries.restrictedSumEquiv` in `TateAlgebra/Sum.lean` is derived from them.
The linear isometry works over any seminormed coefficient ring acting boundedly on the group.
Neither completeness nor finitely many variables is required.

## References

* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §§5.1.1–5.1.2.
-/

public section

noncomputable section

namespace TauCeti.MvPowerSeries

open Filter _root_.MvPowerSeries
open scoped Topology

variable {σ τ E R : Type*} [SeminormedAddCommGroup E] {c : σ → ℝ} {d : τ → ℝ}
  [∀ i, Fact (0 < c i)] [∀ j, Fact (0 < d j)]

namespace IsRestrictedFamily.Gauss

/-- A slice of a jointly restricted family, with the exponents in `σ` fixed. -/
def sumSlice (a : Gauss (Sum.elim c d) E) (s : σ →₀ ℕ) : Gauss d E :=
  ofAddSubgroup ⟨fun t ↦ a (s.sumElim t),
    mem_addSubgroup.mpr ((mem_addSubgroup.mp a.toAddSubgroup.2).comp_sumElim s)⟩

omit [∀ j, Fact (0 < d j)] in
@[simp]
theorem sumSlice_apply (a : Gauss (Sum.elim c d) E) (s : σ →₀ ℕ) (t : τ →₀ ℕ) :
    sumSlice a s t = a (s.sumElim t) := (rfl)

/-- The Gauss norms of the slices of a jointly restricted family themselves decay with the
outer weights. Merely knowing that every slice is restricted would not suffice. -/
theorem isRestrictedFamily_sumSlice (a : Gauss (Sum.elim c d) E) :
    IsRestrictedFamily c (sumSlice a) := by
  classical
  rw [isRestrictedFamily_iff]
  refine tendsto_order.mpr ⟨fun _ hb ↦ .of_forall fun s ↦
    hb.trans_le (mul_nonneg (norm_nonneg _) (prod_pow_pos s).le), fun ε hε ↦ ?_⟩
  -- Project the finite set of coefficients reaching ε/2 onto the outer exponent set.
  have hbad : {k | ε / 2 ≤ ‖a k‖ * k.prod (Sum.elim c d · ^ ·)}.Finite := by
    simpa [eventually_cofinite, not_lt] using
      (isRestrictedFamily_iff.mp (mem_addSubgroup.mp a.toAddSubgroup.2)).eventually
        (gt_mem_nhds (half_pos hε))
  rw [eventually_cofinite]
  refine (hbad.image fun k ↦ k.comapDomain Sum.inl Sum.inl_injective.injOn).subset fun s hs ↦ ?_
  by_contra hns
  have hpos : 0 < s.prod (c · ^ ·) := prod_pow_pos s
  refine (half_lt_self hε).not_ge ((not_lt.mp hs).trans ?_)
  rw [← le_div_iff₀ hpos, norm_le_iff]
  intro t
  rw [le_div_iff₀ hpos, sumSlice_apply]
  rw [← Finsupp.mul_prod_pow_sumElim]
  by_contra hlt
  exact hns ⟨s.sumElim t, (not_le.mp hlt).le, Finsupp.comapDomain_inl_sumElim s t⟩

/-- Flattening restricted families of restricted families preserves joint restrictedness. -/
theorem isRestrictedFamily_flatten (a : Gauss c (Gauss d E)) :
    IsRestrictedFamily (Sum.elim c d) (fun k ↦
      a (k.comapDomain Sum.inl Sum.inl_injective.injOn)
        (k.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  classical
  rw [isRestrictedFamily_iff]
  refine tendsto_order.mpr ⟨fun _ hb ↦ .of_forall fun k ↦
    hb.trans_le (mul_nonneg (norm_nonneg _) (prod_pow_pos k).le), fun ε hε ↦ ?_⟩
  -- Only finitely many outer slices can contribute a coefficient reaching ε, and each of
  -- those slices has only finitely many coefficients reaching its rescaled threshold.
  have houter : {s | ε ≤ ‖a s‖ * s.prod (c · ^ ·)}.Finite := by
    simpa [eventually_cofinite, not_lt] using
      (isRestrictedFamily_iff.mp (mem_addSubgroup.mp a.toAddSubgroup.2)).eventually
        (gt_mem_nhds hε)
  have hinner (s : σ →₀ ℕ) : {t | ε / s.prod (c · ^ ·) ≤
      ‖a s t‖ * t.prod (d · ^ ·)}.Finite := by
    simpa [eventually_cofinite, not_lt] using
      (isRestrictedFamily_iff.mp (mem_addSubgroup.mp (a s).toAddSubgroup.2)).eventually
        (gt_mem_nhds (div_pos hε (prod_pow_pos s)))
  rw [eventually_cofinite]
  refine (houter.biUnion fun s _ ↦ (hinner s).image s.sumElim).subset fun k hk ↦ ?_
  set s := k.comapDomain Sum.inl Sum.inl_injective.injOn
  set t := k.comapDomain Sum.inr Sum.inr_injective.injOn
  have hk' : ε ≤ ‖a s t‖ * t.prod (d · ^ ·) * s.prod (c · ^ ·) := by
    rw [← Finsupp.mul_prod_pow_sumElim, Finsupp.comapDomain_sumElim_comapDomain]
    exact not_lt.mp hk
  refine Set.mem_biUnion (x := s) ?_ ⟨t, ?_, Finsupp.comapDomain_sumElim_comapDomain k⟩
  · exact hk'.trans (mul_le_mul_of_nonneg_right
      (norm_coeff_mul_prod_le (a s) t) (prod_pow_pos s).le)
  · exact (div_le_iff₀ (prod_pow_pos s)).mpr hk'

/-- Splitting and flattening jointly restricted families are inverse additive maps. -/
def sumAddEquiv : Gauss (Sum.elim c d) E ≃+ Gauss c (Gauss d E) where
  toFun a := ofAddSubgroup ⟨sumSlice a, mem_addSubgroup.mpr (isRestrictedFamily_sumSlice a)⟩
  invFun a := ofAddSubgroup ⟨fun k ↦
    a (k.comapDomain Sum.inl Sum.inl_injective.injOn)
      (k.comapDomain Sum.inr Sum.inr_injective.injOn),
    mem_addSubgroup.mpr (isRestrictedFamily_flatten a)⟩
  left_inv a := by
    ext k
    simp [sumSlice, Finsupp.comapDomain_sumElim_comapDomain]
  right_inv a := by
    ext s t
    simp [sumSlice]
  map_add' a b := by
    ext s t
    simp [sumSlice]

@[simp]
theorem sumAddEquiv_apply (a : Gauss (Sum.elim c d) E) (s : σ →₀ ℕ) (t : τ →₀ ℕ) :
    sumAddEquiv a s t = a (s.sumElim t) := (rfl)

@[simp]
theorem sumAddEquiv_symm_apply (a : Gauss c (Gauss d E)) (s : σ →₀ ℕ) (t : τ →₀ ℕ) :
    sumAddEquiv.symm a (s.sumElim t) = a s t := by
  simp [sumAddEquiv]

/-- Iteration preserves the weighted Gauss norm, including at radii not realised by scalars. -/
@[simp]
theorem norm_sumAddEquiv (a : Gauss (Sum.elim c d) E) : ‖sumAddEquiv a‖ = ‖a‖ := by
  apply le_antisymm
  · apply norm_le_iff.mpr
    intro s
    rw [← le_div_iff₀ (prod_pow_pos s), norm_le_iff]
    intro t
    rw [le_div_iff₀ (prod_pow_pos s), sumAddEquiv_apply, ← Finsupp.mul_prod_pow_sumElim]
    exact norm_coeff_mul_prod_le a _
  · apply norm_le_iff.mpr
    intro k
    rw [← Finsupp.comapDomain_sumElim_comapDomain k, Finsupp.mul_prod_pow_sumElim,
      ← sumAddEquiv_apply]
    exact (mul_le_mul_of_nonneg_right (norm_coeff_mul_prod_le _ _)
      (prod_pow_pos _).le).trans (norm_coeff_mul_prod_le (sumAddEquiv a) _)

/-- Splitting jointly restricted coefficient families is an isometry. -/
theorem isometry_sumAddEquiv : Isometry (sumAddEquiv (c := c) (d := d) (E := E)) :=
  AddMonoidHomClass.isometry_iff_norm _ |>.mpr norm_sumAddEquiv

variable (R) [SeminormedRing R] [Module R E] [IsBoundedSMul R E]

/-- Restricted module-valued series in disjoint sets of variables are isometrically the
restricted series in the first variables with restricted-series coefficients in the second. -/
def sumLinearIsometryEquiv : Gauss (Sum.elim c d) E ≃ₗᵢ[R] Gauss c (Gauss d E) where
  toLinearEquiv :=
    { sumAddEquiv with
      map_smul' := fun r a ↦ by
        ext s t
        simp [smul_apply] }
  norm_map' := norm_sumAddEquiv

@[simp]
theorem sumLinearIsometryEquiv_apply (a : Gauss (Sum.elim c d) E)
    (s : σ →₀ ℕ) (t : τ →₀ ℕ) :
    sumLinearIsometryEquiv R a s t = a (s.sumElim t) := (rfl)

@[simp]
theorem sumLinearIsometryEquiv_symm_apply (a : Gauss c (Gauss d E))
    (s : σ →₀ ℕ) (t : τ →₀ ℕ) :
    (sumLinearIsometryEquiv R).symm a (s.sumElim t) = a s t :=
  sumAddEquiv_symm_apply a s t

/-- A single coefficient becomes a single outer coefficient with a single inner coefficient. -/
@[simp]
theorem sumLinearIsometryEquiv_ofFinsupp_single (s : σ →₀ ℕ) (t : τ →₀ ℕ) (e : E) :
    sumLinearIsometryEquiv R (ofFinsupp R (Sum.elim c d) (Finsupp.single (s.sumElim t) e)) =
      ofFinsupp R c (Finsupp.single s (ofFinsupp R d (Finsupp.single t e))) := by
  classical
  ext u v
  simp only [sumLinearIsometryEquiv_apply, ofFinsupp_apply, Finsupp.single_apply,
    Finsupp.sumElim_inj]
  by_cases hs : s = u <;> by_cases ht : t = v <;> simp [hs, ht]

variable {R} {F : Type*} [SeminormedAddCommGroup F] [Module R F] [IsBoundedSMul R F]

/-- Iteration commutes with bounded coefficient linear maps, acting on both levels of the
iterated family. -/
theorem sumLinearIsometryEquiv_mapLinearMap (φ : E →ₗ[R] F) {C : ℝ}
    (hφ : ∀ e, ‖φ e‖ ≤ C * ‖e‖) (a : Gauss (Sum.elim c d) E) :
    sumLinearIsometryEquiv R (mapLinearMap φ hφ a) =
      mapLinearMap (mapLinearMap (c := d) φ hφ) (norm_mapLinearMap_le φ hφ)
        (sumLinearIsometryEquiv R a) := by
  ext s t
  simp

end IsRestrictedFamily.Gauss
end TauCeti.MvPowerSeries
