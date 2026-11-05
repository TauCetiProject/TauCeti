/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PlacesOver.FinitePlace
public import TauCeti.NumberTheory.NumberField.PlacesOver.Relative

/-!
# The local extension formula for absolute values above a finite place

The finite places above `v` correspond bijectively to the absolute values restricting to `v`
exactly: take the local-degree root of each finite place. This identifies the finite-place
classification with the normalization used to evaluate algebraic coefficients over the base.

Products indexed by those absolute values carry local-degree weights. At any element of the
extension they agree with products of the finite places themselves. At an element of the base
the product is the base absolute value raised to the degree of the extension. No Galois
hypothesis is required.

The classification is `NumberField.existsUnique_finitePlace_rpow_inv_eq_of_liesOver`; the degree
formula is `NumberField.FinitePlace.sum_localDegree`. The normalization and product identity
are the finite-place form of Bombieri–Gubler's local extension formula.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, §1.3, Corollary 1.3.2.
-/

public section

namespace NumberField.FinitePlace

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

variable (F) in
/-- Finite places above `v` correspond to absolute values restricting to `v` exactly, by taking
the reciprocal local-degree power of the finite place. -/
noncomputable def placesOverEquivAbsValues (v : FinitePlace K) :
    v.placesOver F ≃ {w : AbsoluteValue F ℝ // w.LiesOver v.1} := by
  let f : v.placesOver F → {w : AbsoluteValue F ℝ // w.LiesOver v.1} := fun w ↦
    ⟨w.val.relativeAbsValue K, by
      have : w.val.LiesOver v := mem_placesOver.mp w.property
      infer_instance⟩
  apply Equiv.ofBijective f
  constructor
  · intro w u h
    exact Subtype.ext (relativeAbsValue_injective (congrArg Subtype.val h))
  · intro u
    have : u.val.LiesOver (mk v.maximalIdeal).1 := by
      simpa only [v.mk_maximalIdeal] using u.property
    obtain ⟨P, hP, hroot⟩ :=
      (NumberField.existsUnique_finitePlace_rpow_inv_eq_of_liesOver
        (𝔭 := v.maximalIdeal) (w := u.val)).exists
    have hPv : (mk P).LiesOver v := by
      simpa only [v.mk_maximalIdeal] using (mk_liesOver_mk_iff P v.maximalIdeal).mpr hP
    refine ⟨⟨mk P, mem_placesOver.mpr hPv⟩, Subtype.ext (AbsoluteValue.ext fun y ↦ ?_)⟩
    simpa only [f, relativeAbsValue_apply, localDegree_def, maximalIdeal_mk, Nat.cast_mul]
      using (hroot y).symm

/-- The forward correspondence is the relative absolute value. -/
@[simp]
theorem placesOverEquivAbsValues_apply (v : FinitePlace K) (w : v.placesOver F) :
    (placesOverEquivAbsValues F v w).val = w.val.relativeAbsValue K :=
  (rfl)

/-- The inverse correspondence recovers a finite place by raising the absolute value to its
local degree. This holds at every element of the extension, not only at base-field elements. -/
@[simp]
theorem placesOverEquivAbsValues_symm_apply_pow (v : FinitePlace K)
    (w : {w : AbsoluteValue F ℝ // w.LiesOver v.1}) (y : F) :
    w.val y ^ ((placesOverEquivAbsValues F v).symm w).val.localDegree K =
      ((placesOverEquivAbsValues F v).symm w).val y := by
  have h := congrArg (fun u : {w : AbsoluteValue F ℝ // w.LiesOver v.1} ↦ u.val y)
    ((placesOverEquivAbsValues F v).apply_symm_apply w)
  rw [placesOverEquivAbsValues_apply] at h
  rw [← h, relativeAbsValue_pow_localDegree]

/-- The fibre of absolute values above a finite place is finite. -/
instance (v : FinitePlace K) : Finite {w : AbsoluteValue F ℝ // w.LiesOver v.1} :=
  Finite.of_equiv _ (placesOverEquivAbsValues F v)

attribute [local instance] Fintype.ofFinite

open scoped Classical in
/-- A local-degree weighted product over the absolute values above `v` is the unweighted
product over the finite places above `v`. -/
theorem prod_apply_pow_localDegree (v : FinitePlace K) (y : F) :
    (∏ w : {w : AbsoluteValue F ℝ // w.LiesOver v.1},
      w.val y ^ ((placesOverEquivAbsValues F v).symm w).val.localDegree K) =
        ∏ w ∈ (v.placesOver F).toFinset, w y := by
  classical
  simp only [placesOverEquivAbsValues_symm_apply_pow]
  exact ((placesOverEquivAbsValues F v).symm.prod_comp
    (fun w : v.placesOver F ↦ w.val y)).trans
      (Finset.prod_set_coe (f := fun w : FinitePlace F ↦ w y) (v.placesOver F))

open scoped Classical in
/-- **The local extension formula.** On a base-field element, the product over all absolute
values above a finite place, weighted by their local degrees, is the base absolute value to
the degree of the extension. -/
theorem prod_algebraMap_pow_localDegree (v : FinitePlace K) (x : K) :
    (∏ w : {w : AbsoluteValue F ℝ // w.LiesOver v.1},
      w.val (algebraMap K F x) ^ ((placesOverEquivAbsValues F v).symm w).val.localDegree K) =
        v x ^ Module.finrank K F := by
  classical
  rw [prod_apply_pow_localDegree]
  calc
    ∏ w ∈ (v.placesOver F).toFinset, w (algebraMap K F x) =
        ∏ w ∈ (v.placesOver F).toFinset, v x ^ w.localDegree K := by
      apply Finset.prod_congr rfl
      intro w hw
      have : w.LiesOver v := (mem_placesOver).mp (Set.mem_toFinset.mp hw)
      exact apply_algebraMap w v x
    _ = v x ^ Module.finrank K F := by
      rw [Finset.prod_pow_eq_pow_sum, sum_localDegree]

/-! The weights recover the original place even at a ramified prime; omitting them need not
recover it. The formula also includes the zero element of the base. -/

example (v : FinitePlace K) :
    (∏ w : {w : AbsoluteValue F ℝ // w.LiesOver v.1},
      w.val (algebraMap K F 0) ^
        ((placesOverEquivAbsValues F v).symm w).val.localDegree K) = 0 := by
  rw [prod_algebraMap_pow_localDegree, map_zero, zero_pow Module.finrank_pos.ne']

example (w : FinitePlace F) (y : F) (hy : 0 < w y) (hy1 : w y ≠ 1)
    (hdeg : 1 < w.localDegree K) : w.relativeAbsValue K y ≠ w y := by
  intro h
  have hp : w y ^ w.localDegree K = w y ^ 1 := by
    simpa only [h, pow_one] using w.relativeAbsValue_pow_localDegree (K := K) y
  exact hdeg.ne' (pow_right_injective₀ hy hy1 hp)

end NumberField.FinitePlace
