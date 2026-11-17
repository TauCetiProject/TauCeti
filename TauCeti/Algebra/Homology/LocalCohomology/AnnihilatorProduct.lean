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
`d : ℕ`, this file defines the local-cohomology annihilator product

`a_J(M, d) = ∏_{0 ≤ j < d} Ann_R H^j_J(M)`

as a finite product of ideals of `R` (not an intersection). Taking an explicit natural cutoff `d`
avoids converting an infinite or bottom support dimension into a natural number; for a nonzero
finite module `M` over a Noetherian local ring `(R, 𝔪)` of support dimension `d`, Česnavičius's
ideal `a(M)` is `localCohomology.annihilatorProduct (IsLocalRing.maximalIdeal R) M d`.

## Main definitions

* `localCohomology.degreeZeroEquivPrimaryComponent`: canonical linear equivalence
  `(localCohomology J 0).obj (ModuleCat.of R M) ≃ₗ[R] J.primaryComponent M`.
* `localCohomology.annihilatorProduct`: the finite ideal product
  `∏ j ∈ Finset.range d, Module.annihilator R ((localCohomology J j).obj (ModuleCat.of R M))`.

## Main results

* `localCohomology.isZero_obj_of_subsingleton`: all local cohomology modules of a subsingleton
  module vanish.
* `localCohomology.annihilatorProduct_zero`, `localCohomology.annihilatorProduct_succ`,
  `localCohomology.annihilatorProduct_one`: base cases and recurrence for `annihilatorProduct`.
* `localCohomology.annihilatorProduct_one_eq_annihilator_primaryComponent`: in degree cutoff `1`,
  the annihilator product is the annihilator of the `J`-primary component (not its radical).
* `localCohomology.annihilatorProduct_le` and `localCohomology.annihilatorProduct_antitone`: the
  product is contained in each individual annihilator factor and is antitone in `d`.
* `localCohomology.annihilatorProduct_eq_top_of_forall_isZero`: if `H^j_J(M) = 0` for all `j < d`,
  then `annihilatorProduct J M d = ⊤`.
* `localCohomology.annihilatorProduct_eq_of_sameRadical`: over a Noetherian ring, ideals with the
  same radical yield the same annihilator product.
* `localCohomology.annihilatorProduct_eq_top_of_le_depth`: for a finite module over a Noetherian
  ring, `d ≤ J.depth M` implies `annihilatorProduct J M d = ⊤`.
* `LinearEquiv.annihilatorProduct_eq`: linear equivalences preserve `annihilatorProduct`.

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
    [Module R M] :
    (localCohomology J 0).obj (ModuleCat.of R M) ≃ₗ[R] J.primaryComponent M :=
  (LinearEquiv.ofInjective (degreeZeroToModule J (ModuleCat.of R M)).hom
    (degreeZeroToModule_injective J (ModuleCat.of R M))).trans
    (LinearEquiv.ofEq _ _ (range_hom_degreeZeroToModule J (ModuleCat.of R M)))

@[simp]
theorem coe_degreeZeroEquivPrimaryComponent_apply (J : Ideal R) (M : Type u) [AddCommGroup M]
    [Module R M] (x : (localCohomology J 0).obj (ModuleCat.of R M)) :
    (degreeZeroEquivPrimaryComponent J M x : M) =
      degreeZeroToModule J (ModuleCat.of R M) x :=
  (rfl)

/-- Every local cohomology module of a subsingleton module vanishes. -/
theorem isZero_obj_of_subsingleton (J : Ideal R) (M : Type u) [AddCommGroup M] [Module R M]
    [Subsingleton M] (j : ℕ) :
    IsZero ((localCohomology J j).obj (ModuleCat.of R M)) := by
  have hM : IsZero (ModuleCat.of R M) := ModuleCat.isZero_of_subsingleton _
  refine IsZero.of_iso ?_ (colimitObjIsoColimitCompEvaluation _ (ModuleCat.of R M))
  rw [IsZero.iff_id_eq_zero]
  refine colimit.hom_ext fun n ↦ ?_
  have hExt : IsZero (((Ext R (ModuleCat.{u} R) j).obj
      (Opposite.op (ModuleCat.of R (R ⧸ J ^ n.unop.unop)))).obj (ModuleCat.of R M)) := by
    refine (Abelian.Ext.subsingleton_iff_isZero_Ext R _ (ModuleCat.of R M) j).1 ?_
    let P := projectiveResolution (ModuleCat.of R (R ⧸ J ^ n.unop.unop))
    cases j with
    | zero => exact P.subsingleton_ext_zero_iff.2 fun f _ ↦ hM.eq_of_tgt f 0
    | succ k => exact (P.subsingleton_ext_succ_iff k).2 fun f _ ↦
        ⟨0, hM.eq_of_tgt _ f⟩
  exact hExt.eq_of_src _ _

/-- The local-cohomology annihilator product `a_J(M, d) = ∏_{0 ≤ j < d} Ann_R H^j_J(M)`, defined as
a finite product of ideals (not an intersection) with an explicit natural cutoff `d`. -/
noncomputable def annihilatorProduct (J : Ideal R) (M : Type u) [AddCommGroup M] [Module R M]
    (d : ℕ) : Ideal R :=
  ∏ j ∈ Finset.range d, Module.annihilator R ((localCohomology J j).obj (ModuleCat.of R M))

/-- Unfolds `localCohomology.annihilatorProduct`. -/
theorem annihilatorProduct_def (J : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] (d : ℕ) :
    annihilatorProduct J M d =
      ∏ j ∈ Finset.range d, Module.annihilator R ((localCohomology J j).obj (ModuleCat.of R M)) :=
  (rfl)

/-- At cutoff zero, the annihilator product is the unit ideal. -/
@[simp]
theorem annihilatorProduct_zero (J : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] :
    annihilatorProduct J M 0 = ⊤ := by
  rw [annihilatorProduct_def, Finset.range_zero, Finset.prod_empty, Ideal.one_eq_top]

/-- Recurrence for the annihilator product: increasing the cutoff by one multiplies by
`Ann_R H^d_J(M)`. -/
theorem annihilatorProduct_succ (J : Ideal R) (M : Type u) [AddCommGroup M] [Module R M]
    (d : ℕ) :
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
      Module.annihilator R ((localCohomology J j).obj (ModuleCat.of R M)) := by
  rw [annihilatorProduct_def]
  exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_range.mpr hj))

/-- The annihilator product is antitone in the cutoff `d`. -/
theorem annihilatorProduct_antitone (J : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] :
    Antitone (annihilatorProduct J M) := by
  refine antitone_nat_of_succ_le fun d ↦ ?_
  rw [annihilatorProduct_succ]
  exact Ideal.mul_le_left

/-- **Unit-product criterion.** If `H^j_J(M) = 0` for all `j < d`, then `a_J(M, d) = ⊤`. -/
theorem annihilatorProduct_eq_top_of_forall_isZero (J : Ideal R) (M : Type u) [AddCommGroup M]
    [Module R M] {d : ℕ}
    (h : ∀ j < d, IsZero ((localCohomology J j).obj (ModuleCat.of R M))) :
    annihilatorProduct J M d = ⊤ := by
  rw [annihilatorProduct_def]
  have h1 : ∀ j ∈ Finset.range d,
      Module.annihilator R ((localCohomology J j).obj (ModuleCat.of R M)) = (1 : Ideal R) := by
    intro j hj
    rw [Ideal.one_eq_top, Module.annihilator_eq_top_iff]
    exact ModuleCat.isZero_iff_subsingleton.mp (h j (Finset.mem_range.mp hj))
  rw [Finset.prod_eq_one h1, Ideal.one_eq_top]

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
    [Module R M] [Subsingleton M] (d : ℕ) :
    annihilatorProduct J M d = ⊤ :=
  annihilatorProduct_eq_top_of_forall_isZero J M fun j _ ↦ isZero_obj_of_subsingleton J M j

/-- Over a Noetherian ring, ideals with the same radical have the same local-cohomology annihilator
product. -/
theorem annihilatorProduct_eq_of_sameRadical [IsNoetherianRing R] {J K : Ideal R}
    (hJK : J.radical = K.radical) (M : Type u) [AddCommGroup M] [Module R M] (d : ℕ) :
    annihilatorProduct J M d = annihilatorProduct K M d := by
  rw [annihilatorProduct_def, annihilatorProduct_def]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  exact ((isoOfSameRadical hJK j).app (ModuleCat.of R M)).toLinearEquiv.annihilator_eq

/-- For a finite module over a Noetherian ring, if `d ≤ J.depth M`, then `a_J(M, d) = ⊤`. -/
theorem annihilatorProduct_eq_top_of_le_depth [IsNoetherianRing R] (J : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M] [Module.Finite R M] {d : ℕ}
    (hd : (d : ℕ∞) ≤ J.depth (ModuleCat.of R M)) :
    annihilatorProduct J M d = ⊤ :=
  annihilatorProduct_eq_top_of_forall_isZero J M fun _ hj ↦
    isZero_obj_of_lt_depth J (ModuleCat.of R M) ((Nat.cast_lt.mpr hj).trans_le hd)

end localCohomology

namespace LinearEquiv

variable {R : Type u} [CommRing R] {M N : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Linearly equivalent modules have the same local-cohomology annihilator products. -/
theorem annihilatorProduct_eq (e : M ≃ₗ[R] N) (J : Ideal R) (d : ℕ) :
    localCohomology.annihilatorProduct J M d = localCohomology.annihilatorProduct J N d := by
  rw [localCohomology.annihilatorProduct_def, localCohomology.annihilatorProduct_def]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  exact ((localCohomology J j).mapIso e.toModuleIso).toLinearEquiv.annihilator_eq

end LinearEquiv
