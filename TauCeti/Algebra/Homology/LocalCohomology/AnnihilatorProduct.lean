/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.RingTheory.Depth.Basic
public import TauCeti.Algebra.Homology.LocalCohomology.DegreeZero
import TauCeti.Algebra.Homology.Ext.LeftDerived
import TauCeti.RingTheory.Depth.LocalCohomology

/-!
# Local-cohomology annihilator products

For a commutative ring `R`, an ideal `J` of `R`, an `R`-module `M`, and a natural number cutoff
`d : ℕ`, this file defines the finite ideal product (not intersection)
`a_J(M, d) = ∏_{0 ≤ j < d} Ann_R H^j_J(M)`.
Taking an explicit cutoff `d : ℕ` avoids converting an infinite or `⊥` support dimension to `ℕ`;
for a nonzero finite module `M` over a Noetherian local ring `(R, 𝔪)` of support dimension `d`,
Česnavičius's ideal `a(M)` is `localCohomology.annihilatorProduct (maximalIdeal R) M d`.

## Main definitions

* `localCohomology.degreeZeroEquivPrimaryComponent`: `H⁰_J(M) ≃ₗ[R] J.primaryComponent M`.
* `localCohomology.annihilatorProduct`: `∏ j ∈ Finset.range d, Ann_R H^j_J(M)`.

## Main results

* `isZero_obj_of_subsingleton`, `annihilatorProduct_zero`, `annihilatorProduct_succ`,
  `annihilatorProduct_one`, `annihilatorProduct_one_eq_annihilator_primaryComponent`,
  `annihilatorProduct_le`, `annihilatorProduct_antitone`,
  `annihilatorProduct_eq_top_of_forall_isZero`, `annihilatorProduct_eq_of_sameRadical`,
  `annihilatorProduct_eq_top_of_le_depth`, `LinearEquiv.annihilatorProduct_eq`.

## References

* K. Česnavičius, *Macaulayfication of Noetherian schemes*, Duke Math. J. 170 (2021),
  Definition 3.1(ii), Remark 3.3, Lemma 3.6.
-/

public section

universe u

open CategoryTheory Limits

namespace localCohomology

variable {R : Type u} [CommRing R]

/-- The degree-zero local cohomology module `H⁰_J(M)` is canonically linearly equivalent to the
`J`-primary component `Ideal.primaryComponent M J`. -/
noncomputable def degreeZeroEquivPrimaryComponent (J : Ideal R) (M : Type u) [AddCommGroup M]
    [Module R M] : (localCohomology J 0).obj (ModuleCat.of R M) ≃ₗ[R] J.primaryComponent M :=
  (LinearEquiv.ofInjective (degreeZeroToModule J (ModuleCat.of R M)).hom
    (degreeZeroToModule_injective J (ModuleCat.of R M))).trans
    (LinearEquiv.ofEq _ _ (range_hom_degreeZeroToModule J (ModuleCat.of R M)))

@[simp]
theorem coe_degreeZeroEquivPrimaryComponent_apply (J : Ideal R) (M : Type u) [AddCommGroup M]
    [Module R M] (x : (localCohomology J 0).obj (ModuleCat.of R M)) :
    (degreeZeroEquivPrimaryComponent J M x : M) =
      degreeZeroToModule J (ModuleCat.of R M) x := (rfl)

/-- Every local cohomology module of a subsingleton module vanishes. -/
theorem isZero_obj_of_subsingleton (J : Ideal R) (M : Type u) [AddCommGroup M] [Module R M]
    [Subsingleton M] (j : ℕ) : IsZero ((localCohomology J j).obj (ModuleCat.of R M)) := by
  have hM : IsZero (ModuleCat.of R M) := ModuleCat.isZero_of_subsingleton _
  refine IsZero.of_iso ?_ (colimitObjIsoColimitCompEvaluation _ (ModuleCat.of R M))
  rw [IsZero.iff_id_eq_zero]
  refine colimit.hom_ext fun n ↦ IsZero.eq_of_src ?_ _ _
  refine (Abelian.Ext.subsingleton_iff_isZero_Ext R _ (ModuleCat.of R M) j).1 ?_
  let P := projectiveResolution (ModuleCat.of R (R ⧸ J ^ n.unop.unop))
  cases j with
  | zero => exact P.subsingleton_ext_zero_iff.2 fun f _ ↦ hM.eq_of_tgt f 0
  | succ k => exact (P.subsingleton_ext_succ_iff k).2 fun f _ ↦ ⟨0, hM.eq_of_tgt _ f⟩

/-- The local-cohomology annihilator product `a_J(M, d) = ∏_{0 ≤ j < d} Ann_R H^j_J(M)`, defined as
a finite product of ideals (not an intersection) with an explicit natural cutoff `d`. -/
noncomputable def annihilatorProduct (J : Ideal R) (M : Type u) [AddCommGroup M] [Module R M]
    (d : ℕ) : Ideal R :=
  ∏ j ∈ Finset.range d, Module.annihilator R ((localCohomology J j).obj (ModuleCat.of R M))

/-- Unfolds `localCohomology.annihilatorProduct`. -/
theorem annihilatorProduct_def (J : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] (d : ℕ) :
    annihilatorProduct J M d = ∏ j ∈ Finset.range d,
      Module.annihilator R ((localCohomology J j).obj (ModuleCat.of R M)) := (rfl)

/-- At cutoff zero, the annihilator product is the unit ideal. -/
@[simp]
theorem annihilatorProduct_zero (J : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] :
    annihilatorProduct J M 0 = ⊤ := by
  rw [annihilatorProduct_def, Finset.range_zero, Finset.prod_empty, Ideal.one_eq_top]

/-- Recurrence for the annihilator product: increasing the cutoff by one multiplies by
`Ann_R H^d_J(M)`. -/
theorem annihilatorProduct_succ (J : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] (d : ℕ) :
    annihilatorProduct J M (d + 1) =
      annihilatorProduct J M d *
        Module.annihilator R ((localCohomology J d).obj (ModuleCat.of R M)) := by
  rw [annihilatorProduct_def, annihilatorProduct_def, Finset.prod_range_succ]

/-- At cutoff one, the annihilator product is `Ann_R H^0_J(M)`. -/
theorem annihilatorProduct_one (J : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] :
    annihilatorProduct J M 1 =
      Module.annihilator R ((localCohomology J 0).obj (ModuleCat.of R M)) := by
  rw [annihilatorProduct_succ, annihilatorProduct_zero, Ideal.top_mul]

/-- At cutoff one, the annihilator product is the annihilator of the `J`-primary component of `M`
(not its radical). -/
theorem annihilatorProduct_one_eq_annihilator_primaryComponent (J : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M] :
    annihilatorProduct J M 1 = Module.annihilator R (J.primaryComponent M) := by
  rw [annihilatorProduct_one]
  exact (degreeZeroEquivPrimaryComponent J M).annihilator_eq

/-- The annihilator product `a_J(M, d)` is contained in `Ann_R H^j_J(M)` for every `j < d`. -/
theorem annihilatorProduct_le (J : Ideal R) (M : Type u) [AddCommGroup M] [Module R M]
    {j d : ℕ} (hj : j < d) :
    annihilatorProduct J M d ≤
      Module.annihilator R ((localCohomology J j).obj (ModuleCat.of R M)) :=
  Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_range.mpr hj))

/-- The annihilator product is antitone in the cutoff `d`. -/
theorem annihilatorProduct_antitone (J : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] :
    Antitone (annihilatorProduct J M) :=
  antitone_nat_of_succ_le fun d ↦ by rw [annihilatorProduct_succ]; exact Ideal.mul_le_left

/-- **Unit-product criterion.** If `H^j_J(M) = 0` for all `j < d`, then `a_J(M, d) = ⊤`. -/
theorem annihilatorProduct_eq_top_of_forall_isZero (J : Ideal R) (M : Type u) [AddCommGroup M]
    [Module R M] {d : ℕ}
    (h : ∀ j < d, IsZero ((localCohomology J j).obj (ModuleCat.of R M))) :
    annihilatorProduct J M d = ⊤ := by
  rw [annihilatorProduct_def, Finset.prod_eq_one fun j hj ↦ ?_, Ideal.one_eq_top]
  rw [Ideal.one_eq_top, Module.annihilator_eq_top_iff]
  exact ModuleCat.isZero_iff_subsingleton.mp (h j (Finset.mem_range.mp hj))

/-- If `H^j_J(M)` is subsingleton for all `j < d`, then `a_J(M, d) = ⊤`. -/
theorem annihilatorProduct_eq_top_of_forall_subsingleton (J : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M] {d : ℕ}
    (h : ∀ j < d, Subsingleton ((localCohomology J j).obj (ModuleCat.of R M))) :
    annihilatorProduct J M d = ⊤ :=
  annihilatorProduct_eq_top_of_forall_isZero J M fun j hj ↦
    ModuleCat.isZero_iff_subsingleton.mpr (h j hj)

/-- Every annihilator product of a subsingleton module is the unit ideal. -/
@[simp]
theorem annihilatorProduct_of_subsingleton (J : Ideal R) (M : Type u) [AddCommGroup M]
    [Module R M] [Subsingleton M] (d : ℕ) : annihilatorProduct J M d = ⊤ :=
  annihilatorProduct_eq_top_of_forall_isZero J M fun j _ ↦ isZero_obj_of_subsingleton J M j

/-- Over a Noetherian ring, ideals with the same radical have the same local-cohomology annihilator
product. -/
theorem annihilatorProduct_eq_of_sameRadical [IsNoetherianRing R] {J K : Ideal R}
    (hJK : J.radical = K.radical) (M : Type u) [AddCommGroup M] [Module R M] (d : ℕ) :
    annihilatorProduct J M d = annihilatorProduct K M d :=
  Finset.prod_congr rfl fun j _ ↦
    ((isoOfSameRadical hJK j).app (ModuleCat.of R M)).toLinearEquiv.annihilator_eq

/-- For a finite module over a Noetherian ring, if `d ≤ J.depth M`, then `a_J(M, d) = ⊤`. -/
theorem annihilatorProduct_eq_top_of_le_depth [IsNoetherianRing R] (J : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M] [Module.Finite R M] {d : ℕ}
    (hd : (d : ℕ∞) ≤ J.depth (ModuleCat.of R M)) : annihilatorProduct J M d = ⊤ :=
  annihilatorProduct_eq_top_of_forall_isZero J M fun _ hj ↦
    isZero_obj_of_lt_depth J (ModuleCat.of R M) ((Nat.cast_lt.mpr hj).trans_le hd)

end localCohomology

namespace LinearEquiv

variable {R : Type u} [CommRing R] {M N : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Linearly equivalent modules have the same local-cohomology annihilator products. -/
theorem annihilatorProduct_eq (e : M ≃ₗ[R] N) (J : Ideal R) (d : ℕ) :
    localCohomology.annihilatorProduct J M d = localCohomology.annihilatorProduct J N d :=
  Finset.prod_congr rfl fun j _ ↦
    ((localCohomology J j).mapIso e.toModuleIso).toLinearEquiv.annihilator_eq

end LinearEquiv
