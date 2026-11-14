/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.InfinitePlace.Mult
public import TauCeti.NumberTheory.NumberField.PlacesOver.FinitePlace
public import TauCeti.NumberTheory.NumberField.PlacesOver.InfinitePlace
public import TauCeti.NumberTheory.NumberField.PlacesOver.Relative

/-!
# The local extension formula for absolute values above a place

Above a finite place `v`, the finite places of `F` correspond bijectively to the absolute values
restricting to `v` on the nose (`NumberField.FinitePlace.placesOverEquivAbsValues`), by taking the
local-degree root of each finite place. Above an infinite place `v`, the infinite places of `F`
correspond bijectively to the absolute values restricting to `v` directly, without any root
(`NumberField.InfinitePlace.placesOverEquivAbsValues`).

Products indexed by those absolute values carry local-degree weights at finite places and
multiplicity weights `w.mult ∈ {1, 2}` at infinite places. At any element of the extension they
agree with products over the places of `F` above `v`. At an element of the base the product is the
normalized base value raised to the degree `[F : K]`
(`NumberField.FinitePlace.prod_algebraMap_pow_localDegree`,
`NumberField.InfinitePlace.prod_algebraMap_pow_mult`). No Galois hypothesis is required.

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

namespace NumberField.InfinitePlace

section Field

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable (F) in
/-- Infinite places of `F` above `v` correspond bijectively to absolute values of `F` restricting
to `v`, via their underlying absolute values. -/
noncomputable def placesOverEquivAbsValues (v : InfinitePlace K) :
    v.placesOver F ≃ {w : AbsoluteValue F ℝ // w.LiesOver v.1} := by
  refine Equiv.ofBijective (fun w ↦ ⟨w.val.1, mem_placesOver.mp w.property⟩) ⟨?_, ?_⟩
  · intro w u h
    exact Subtype.ext (Subtype.ext (Subtype.mk.inj h))
  · intro u
    let := u.property
    obtain ⟨w, ⟨hw, hval⟩, -⟩ := NumberField.existsUnique_infinitePlace_of_liesOver v u.val
    exact ⟨⟨w, mem_placesOver.mpr hw⟩, Subtype.ext hval⟩

/-- The forward correspondence sends an infinite place above `v` to its underlying absolute
value. -/
@[simp]
theorem placesOverEquivAbsValues_apply (v : InfinitePlace K) (w : v.placesOver F) :
    (placesOverEquivAbsValues F v w).val = w.val.1 :=
  (rfl)

/-- The inverse correspondence recovers an infinite place whose underlying absolute value is `w`. -/
@[simp]
theorem placesOverEquivAbsValues_symm_apply_val (v : InfinitePlace K)
    (w : {w : AbsoluteValue F ℝ // w.LiesOver v.1}) :
    ((placesOverEquivAbsValues F v).symm w).val.1 = w.val :=
  congrArg Subtype.val ((placesOverEquivAbsValues F v).apply_symm_apply w)

/-- Evaluating the infinite place recovered by `(placesOverEquivAbsValues F v).symm` gives `w`. -/
@[simp]
theorem placesOverEquivAbsValues_symm_apply_coe (v : InfinitePlace K)
    (w : {w : AbsoluteValue F ℝ // w.LiesOver v.1}) (y : F) :
    ((placesOverEquivAbsValues F v).symm w).val y = w.val y :=
  congrArg (fun u : AbsoluteValue F ℝ ↦ u y) (placesOverEquivAbsValues_symm_apply_val v w)

end Field

section NumberField

variable {K F : Type*} [Field K] [Field F] [NumberField F] [Algebra K F]

/-- The fibre of absolute values of a number field above an infinite place is finite. -/
instance (v : InfinitePlace K) : Finite {w : AbsoluteValue F ℝ // w.LiesOver v.1} :=
  Finite.of_equiv _ (placesOverEquivAbsValues F v)

attribute [local instance] Fintype.ofFinite

open scoped Classical in
/-- A multiplicity-weighted product over the absolute values above an infinite place `v` is the
multiplicity-weighted product over the infinite places above `v`. -/
theorem prod_apply_pow_mult (v : InfinitePlace K) (y : F) :
    (∏ w : {w : AbsoluteValue F ℝ // w.LiesOver v.1},
      w.val y ^ ((placesOverEquivAbsValues F v).symm w).val.mult) =
        ∏ w ∈ (v.placesOver F).toFinset, w y ^ w.mult := by
  simp only [← placesOverEquivAbsValues_symm_apply_coe]
  exact ((placesOverEquivAbsValues F v).symm.prod_comp
    (fun w : v.placesOver F ↦ w.val y ^ w.val.mult)).trans
      (Finset.prod_set_coe (f := fun w : InfinitePlace F ↦ w y ^ w.mult) (v.placesOver F))

open scoped Classical in
/-- **The local extension formula at an infinite place.** On a base-field element, the product over
all absolute values of `F` above an infinite place `v`, weighted by their multiplicities `w.mult`,
equals the normalized base value `v x ^ v.mult` raised to `[F : K]`. -/
theorem prod_algebraMap_pow_mult (v : InfinitePlace K) (x : K) :
    (∏ w : {w : AbsoluteValue F ℝ // w.LiesOver v.1},
      w.val (algebraMap K F x) ^ ((placesOverEquivAbsValues F v).symm w).val.mult) =
        (v x ^ v.mult) ^ Module.finrank K F := by
  rw [prod_apply_pow_mult]
  calc
    ∏ w ∈ (v.placesOver F).toFinset, w (algebraMap K F x) ^ w.mult =
        ∏ w ∈ (v.placesOver F).toFinset, v x ^ w.mult := by
      refine Finset.prod_congr rfl fun w hw ↦ ?_
      have : w.LiesOver v := mem_placesOver.mp (Set.mem_toFinset.mp hw)
      rw [← comap_apply, LiesOver.comap_eq w v]
    _ = (v x ^ v.mult) ^ Module.finrank K F := by
      rw [Finset.prod_pow_eq_pow_sum, sum_mult_eq_mult_mul_finrank F v, pow_mul]

/-! At a ramified infinite place (`w` complex above `v` real), the normalized factor `w ^ w.mult`
is the square of `v ^ v.mult` on the base, whereas `w` itself restricts to `v` without a power. -/

example [NumberField K] (v : InfinitePlace K) :
    (∏ w : {w : AbsoluteValue F ℝ // w.LiesOver v.1},
      w.val (algebraMap K F 0) ^
        ((placesOverEquivAbsValues F v).symm w).val.mult) = 0 := by
  rw [prod_algebraMap_pow_mult, map_zero, zero_pow v.mult_ne_zero,
    zero_pow Module.finrank_pos.ne']

example (w : InfinitePlace F) (v : InfinitePlace K) [w.LiesOver v] (hw : w.IsRamified K) :
    w (algebraMap K F (2 : ℕ)) ^ w.mult ≠ v (2 : ℕ) ^ v.mult := by
  have hv : v.IsReal := hw.liesOver_isReal_under w v
  rw [← comap_apply, LiesOver.comap_eq w v, v.map_natCast,
    hw.isComplex.mult_eq_two, hv.mult_eq_one]
  norm_num

end NumberField

end NumberField.InfinitePlace
