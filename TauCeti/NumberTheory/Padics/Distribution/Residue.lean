/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Convolution
public import TauCeti.NumberTheory.Padics.Measure.Residue

/-!
# Restricting locally analytic distributions to residue classes

For `n : ℕ` and `a ∈ ZMod (pⁿ)`, the indicator of the residue class `a + pⁿℤ_p` is locally
analytic, so a locally analytic distribution `μ` on `ℤ_p` restricts to it:
`(Res_a μ)(f) = μ(1_{a + pⁿℤ_p} f)`. This file constructs these restrictions on coefficient
vectors, on locally analytic functions and on distributions.

On the analytic stage `LA_h(E)` of a level `h ≥ n`, every disc `b + pʰℤ_p` lies in a single
residue class modulo `pⁿ`, the class of `b.val`. Multiplying by the indicator of `a + pⁿℤ_p`
keeps the coefficients on the discs of the classes `b` with `b.val ≡ a` and replaces the others
by zero; this is the coordinate projection `ZeroAtInftyContinuousMap.indicatorCLM`. On a stage of
level `h < n`, a vector is first re-expanded to the level `max h n`. Re-expansion only reads the
coefficients on the disc containing a smaller disc
(`TauCeti.AnalyticStage.transitionLE_indicatorCLM`), so the restrictions are compatible with the
transitions between levels and induce the restriction `TauCeti.LocallyAnalytic.restrictResidue`
on the algebraic direct limit `LA(ℤ_p, E)`. All identities are proved on coefficients, so no
torsion-freeness of `E` is needed.

The transpose is `TauCeti.LocallyAnalyticDistribution.restrictResidue`. As for measures, the
restrictions at a fixed depth are orthogonal idempotents adding up to the identity, and they do
not increase the stage seminorms of level at least `n`. They extend the restriction of measures
`AbstractMeasure.restrictResidue` (`restrictResidue_ofMeasure`) and keep exactly the point masses
in the class (`restrictResidue_dirac`).

## Main definitions

* `TauCeti.AnalyticStage.restrictResidue S n a`: restriction to `a + pⁿℤ_p`,
  `LA_h(E) →L[S] LA_{max h n}(E)`.
* `TauCeti.LocallyAnalytic.restrictResidue S n a`: restriction of locally analytic functions.
* `TauCeti.LocallyAnalyticDistribution.restrictResidue n a`: restriction of distributions,
  `(Res_a μ)(f) = μ(1_{a + pⁿℤ_p} f)`.

## Main results

* `TauCeti.AnalyticStage.eval_indicatorCLM`: projecting onto the discs of a set of classes
  evaluates to the product with the indicator of their union.
* `TauCeti.LocallyAnalytic.eval_restrictResidue`: restriction evaluates to `1_{a + pⁿℤ_p} f`.
* `TauCeti.LocallyAnalyticDistribution.stage_restrictResidue_of_le`,
  `TauCeti.LocallyAnalyticDistribution.stageSeminorm_restrictResidue_le`: on a stage of level
  `h ≥ n`, restriction is the coordinate projection, so it does not increase the stage seminorm.
* `TauCeti.LocallyAnalyticDistribution.restrictResidue_restrictResidue`,
  `TauCeti.LocallyAnalyticDistribution.sum_restrictResidue`: the restrictions at depth `n` are
  orthogonal idempotents with sum the identity.
* `TauCeti.LocallyAnalyticDistribution.restrictResidue_dirac`,
  `TauCeti.LocallyAnalyticDistribution.restrictResidue_ofMeasure`: compatibility with point masses
  and with the restriction of measures.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §II.4.
-/

public section

open scoped ZeroAtInfty
open ZeroAtInftyContinuousMap

namespace TauCeti

variable {p : ℕ} [Fact p.Prime]

namespace AnalyticStage

variable {h : ℕ} {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-! ### Projecting onto the discs of a set of classes -/

/-- Projecting onto the discs of a set `U` of classes of level `h` evaluates to the product of the
function with the indicator of the union of these discs. -/
@[simp]
theorem eval_indicatorCLM (U : Set (ZMod (p ^ h))) (c : AnalyticStage p h E) (x : ℤ_[p]) :
    eval S (indicatorCLM S (Prod.fst ⁻¹' U) c) x =
      (PadicInt.toZModPow h ⁻¹' U).indicator (eval S c) x := by
  obtain ⟨⟨a, w⟩, rfl⟩ := (PadicInt.discHomeomorph p h).surjective x
  classical
  rw [PadicInt.discHomeomorph_apply, Set.indicator_apply, Set.mem_preimage,
    PadicInt.toZModPow_natCast_val_add_mul, eval_natCast_val_add_mul, eval_natCast_val_add_mul]
  by_cases ha : a ∈ U <;> simp [ha]

/-- Re-expanding a vector projected onto the discs of a set `U` of classes of level `h` projects
the re-expansion onto the discs of level `h + 1` lying in them. -/
theorem transition_indicatorCLM (U : Set (ZMod (p ^ h))) (c : AnalyticStage p h E) :
    transition S (indicatorCLM S (Prod.fst ⁻¹' U) c) =
      indicatorCLM S
        (Prod.fst ⁻¹' ((fun b : ZMod (p ^ (h + 1)) ↦ (ZMod.cast b : ZMod (p ^ h))) ⁻¹' U))
        (transition S c) := by
  ext ⟨a', j⟩
  by_cases ha : (ZMod.cast a' : ZMod (p ^ h)) ∈ U <;> simp [transition_apply, ha, reexpand_def]

/-- Re-expanding a vector projected onto the discs of a set `U` of classes of level `h` to a level
`k ≥ h` projects the re-expansion onto the discs of level `k` lying in them. -/
theorem transitionLE_indicatorCLM {k : ℕ} (hhk : h ≤ k) (U : Set (ZMod (p ^ h)))
    (c : AnalyticStage p h E) :
    transitionLE S hhk (indicatorCLM S (Prod.fst ⁻¹' U) c) =
      indicatorCLM S (Prod.fst ⁻¹' ((fun b : ZMod (p ^ k) ↦ (ZMod.cast b : ZMod (p ^ h))) ⁻¹' U))
        (transitionLE S hhk c) := by
  induction k, hhk using Nat.le_induction with
  | base => simp
  | succ k hhk ih =>
    rw [transitionLE_succ S hhk, ContinuousLinearMap.comp_apply, ih, transition_indicatorCLM,
      ContinuousLinearMap.comp_apply]
    congr 3
    ext b
    have hb : (ZMod.cast (ZMod.cast b : ZMod (p ^ k)) : ZMod (p ^ h)) = ZMod.cast b :=
      DFunLike.congr_fun (ZMod.castHom_comp (pow_dvd_pow p hhk) (pow_dvd_pow p k.le_succ)) b
    simp only [Set.mem_preimage, hb]

/-! ### Restriction to a residue class -/

variable (n : ℕ) (a : ZMod (p ^ n))

omit [Fact p.Prime] in
/-- The classes of level `k ≥ n` lying in a residue class modulo `pⁿ` are the classes of level `k`
above the classes of an intermediate level lying in it. -/
private theorem preimage_residue {k l : ℕ} (hnk : n ≤ k) (hkl : k ≤ l) :
    (fun b : ZMod (p ^ l) ↦ (ZMod.cast b : ZMod (p ^ k))) ⁻¹'
        {b | (ZMod.cast b : ZMod (p ^ n)) = a} =
      {b | (ZMod.cast b : ZMod (p ^ n)) = a} := by
  ext b
  have hb : (ZMod.cast (ZMod.cast b : ZMod (p ^ k)) : ZMod (p ^ n)) = ZMod.cast b :=
    DFunLike.congr_fun (ZMod.castHom_comp (pow_dvd_pow p hnk) (pow_dvd_pow p hkl)) b
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hb]

/-- Restriction of a coefficient vector of `LA_h(E)` to the residue class `a + pⁿℤ_p`: the vector
is re-expanded to the level `max h n`, where it is projected onto the discs of the classes `b`
with `b.val ≡ a` modulo `pⁿ`. -/
noncomputable def restrictResidue : AnalyticStage p h E →L[S] AnalyticStage p (max h n) E :=
  indicatorCLM S (Prod.fst ⁻¹' {b : ZMod (p ^ max h n) | (ZMod.cast b : ZMod (p ^ n)) = a}) ∘L
    transitionLE S (le_max_left h n)

/-- The restriction to a residue class re-expands to the level `max h n`, then projects. -/
theorem restrictResidue_apply (c : AnalyticStage p h E) :
    restrictResidue S n a c =
      indicatorCLM S (Prod.fst ⁻¹' {b : ZMod (p ^ max h n) | (ZMod.cast b : ZMod (p ^ n)) = a})
        (transitionLE S (le_max_left h n) c) :=
  (rfl)

/-- On a stage of level `h ≥ n`, the restriction to a residue class is the projection onto the
discs of the classes in it, followed by re-expansion to the level `max h n`. -/
theorem restrictResidue_of_le (hnh : n ≤ h) (c : AnalyticStage p h E) :
    restrictResidue S n a c =
      transitionLE S (le_max_left h n)
        (indicatorCLM S (Prod.fst ⁻¹' {b : ZMod (p ^ h) | (ZMod.cast b : ZMod (p ^ n)) = a})
          c) := by
  rw [restrictResidue_apply, transitionLE_indicatorCLM S (le_max_left h n),
    preimage_residue n a hnh (le_max_left h n)]

/-- The restriction to a residue class commutes with re-expansion. -/
theorem transitionLE_restrictResidue {k : ℕ} (hhk : h ≤ k) (c : AnalyticStage p h E) :
    transitionLE S (max_le_max_right n hhk) (restrictResidue S n a c) =
      restrictResidue S n a (transitionLE S hhk c) := by
  rw [restrictResidue_apply, restrictResidue_apply,
    transitionLE_indicatorCLM S (max_le_max_right n hhk),
    preimage_residue n a (le_max_right h n) (max_le_max_right n hhk),
    transitionLE_transitionLE, transitionLE_transitionLE]

end AnalyticStage

namespace LocallyAnalytic

open AnalyticStage

variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]
  (n : ℕ) (a : ZMod (p ^ n))

/-- Restriction of locally analytic functions to the residue class `a + pⁿℤ_p`, that is,
multiplication by its indicator, induced by `AnalyticStage.restrictResidue` on each stage. -/
noncomputable def restrictResidue : LocallyAnalytic p S E →ₗ[S] LocallyAnalytic p S E :=
  Module.DirectLimit.lift S ℕ _ _
    (fun h ↦ ofStage S (max h n) ∘ₗ (AnalyticStage.restrictResidue S n a).toLinearMap)
    fun h k hhk c ↦ by
      simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply]
      rw [← transitionLE_restrictResidue, ofStage_transitionLE]

/-- The restriction to a residue class is computed on any stage after re-expansion to the level
`max h n`. -/
theorem restrictResidue_ofStage (h : ℕ) (c : AnalyticStage p h E) :
    restrictResidue S n a (ofStage S h c) =
      ofStage S (max h n) (AnalyticStage.restrictResidue S n a c) :=
  lift_ofStage S _ _ h c

/-- On a stage of level `h ≥ n`, the restriction to a residue class is the projection onto the
discs of the classes in it. -/
theorem restrictResidue_ofStage_of_le {h : ℕ} (hnh : n ≤ h) (c : AnalyticStage p h E) :
    restrictResidue S n a (ofStage S h c) =
      ofStage S h
        (indicatorCLM S (Prod.fst ⁻¹' {b : ZMod (p ^ h) | (ZMod.cast b : ZMod (p ^ n)) = a})
          c) := by
  rw [restrictResidue_ofStage, restrictResidue_of_le S n a hnh, ofStage_transitionLE]

/-- Every locally analytic function comes from a vector of a stage of level at least `n`. -/
private theorem exists_ofStage_of_le (f : LocallyAnalytic p S E) :
    ∃ h, n ≤ h ∧ ∃ c : AnalyticStage p h E, ofStage S h c = f := by
  obtain ⟨h, c, rfl⟩ := exists_ofStage S f
  exact ⟨max h n, le_max_right h n, transitionLE S (le_max_left h n) c, ofStage_transitionLE S _ c⟩

/-- The restriction to `a + pⁿℤ_p` evaluates to the product with the indicator of the class. -/
@[simp]
theorem eval_restrictResidue (f : LocallyAnalytic p S E) (x : ℤ_[p]) :
    eval S (restrictResidue S n a f) x =
      if PadicInt.toZModPow n x = a then eval S f x else 0 := by
  obtain ⟨h, hnh, c, rfl⟩ := exists_ofStage_of_le S n f
  rw [restrictResidue_ofStage_of_le S n a hnh, eval_ofStage, eval_ofStage, eval_indicatorCLM]
  simp [Set.indicator_apply, PadicInt.cast_toZModPow n h hnh]

/-- The restrictions to the residue classes modulo `pⁿ` are orthogonal idempotents. -/
theorem restrictResidue_restrictResidue (b : ZMod (p ^ n)) (f : LocallyAnalytic p S E) :
    restrictResidue S n a (restrictResidue S n b f) =
      if a = b then restrictResidue S n a f else 0 := by
  obtain ⟨h, hnh, c, rfl⟩ := exists_ofStage_of_le S n f
  simp only [restrictResidue_ofStage_of_le S n _ hnh]
  split_ifs with hab
  · subst hab
    congr 1
    ext i
    simp [Set.indicator_indicator]
  · rw [← map_zero (ofStage S h)]
    congr 1
    ext ⟨b', j⟩
    by_cases hb' : (ZMod.cast b' : ZMod (p ^ n)) = a <;> simp [hb', hab]

/-- A locally analytic function is the sum of its restrictions to the residue classes modulo
`pⁿ`. -/
@[simp]
theorem sum_restrictResidue (f : LocallyAnalytic p S E) :
    ∑ a : ZMod (p ^ n), restrictResidue S n a f = f := by
  obtain ⟨h, hnh, c, rfl⟩ := exists_ofStage_of_le S n f
  simp only [restrictResidue_ofStage_of_le S n _ hnh, ← map_sum]
  congr 1
  ext i
  simp [Set.indicator_apply]

/-- Modulo `p ^ 0 = 1` there is a single residue class, so restriction is the identity. -/
@[simp]
theorem restrictResidue_zero_depth (a : ZMod (p ^ 0)) (f : LocallyAnalytic p S E) :
    restrictResidue S 0 a f = f := by
  have : Subsingleton (ZMod (p ^ 0)) := by
    rw [pow_zero]
    infer_instance
  obtain ⟨h, -, c, rfl⟩ := exists_ofStage_of_le S 0 f
  rw [restrictResidue_ofStage_of_le S 0 a (Nat.zero_le h)]
  congr 1
  exact indicatorCLM_eq_self fun i hi ↦ absurd (Subsingleton.elim _ _) hi

end LocallyAnalytic

namespace LocallyAnalyticDistribution

open AnalyticStage LocallyAnalytic

variable {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]
  (n : ℕ) (a : ZMod (p ^ n))

/-- Restriction of a locally analytic distribution to the residue class `a + pⁿℤ_p`:
`(Res_a μ)(f) = μ(1_{a + pⁿℤ_p} f)`. -/
noncomputable def restrictResidue :
    LocallyAnalyticDistribution p K →ₗ[K] LocallyAnalyticDistribution p K :=
  dualMap (LocallyAnalytic.restrictResidue K n a) (fun _ ↦ AnalyticStage.restrictResidue K n a)
    (LocallyAnalytic.restrictResidue_ofStage K n a)

/-- The restriction `Res_a μ` takes the value `μ(1_{a + pⁿℤ_p} f)` on `f`. -/
@[simp]
theorem coe_restrictResidue_apply (μ : LocallyAnalyticDistribution p K)
    (f : LocallyAnalytic p K K) :
    (restrictResidue n a μ : Module.Dual K (LocallyAnalytic p K K)) f =
      (μ : Module.Dual K (LocallyAnalytic p K K)) (LocallyAnalytic.restrictResidue K n a f) :=
  coe_dualMap_apply μ f

/-- The restriction of `Res_a μ` to the stage of level `h` is the restriction of `μ` to the stage
of level `max h n` composed with the restriction of coefficient vectors. -/
theorem stage_restrictResidue (h : ℕ) (μ : LocallyAnalyticDistribution p K) :
    stage h (restrictResidue n a μ) = stage (max h n) μ ∘L AnalyticStage.restrictResidue K n a :=
  stage_dualMap h μ

/-- On a stage of level `h ≥ n`, the restriction of `Res_a μ` is the restriction of `μ` composed
with the projection onto the discs of the classes in `a + pⁿℤ_p`. -/
theorem stage_restrictResidue_of_le {h : ℕ} (hnh : n ≤ h) (μ : LocallyAnalyticDistribution p K) :
    stage h (restrictResidue n a μ) =
      stage h μ ∘L
        indicatorCLM K (Prod.fst ⁻¹' {b : ZMod (p ^ h) | (ZMod.cast b : ZMod (p ^ n)) = a}) := by
  ext c
  simp [restrictResidue_ofStage_of_le K n a hnh]

/-- Restriction to a residue class modulo `pⁿ` does not increase the stage seminorms of level
`h ≥ n`. -/
theorem stageSeminorm_restrictResidue_le {h : ℕ} (hnh : n ≤ h)
    (μ : LocallyAnalyticDistribution p K) :
    stageSeminorm h (restrictResidue n a μ) ≤ stageSeminorm h μ := by
  rw [stageSeminorm_apply, stageSeminorm_apply, stage_restrictResidue_of_le n a hnh]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (stage h μ)) fun c ↦ ?_
  exact ((stage h μ).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (norm_indicatorCLM_apply_le _ c) (norm_nonneg _))

/-- The restrictions to the residue classes modulo `pⁿ` are orthogonal idempotents. -/
theorem restrictResidue_restrictResidue (b : ZMod (p ^ n)) (μ : LocallyAnalyticDistribution p K) :
    restrictResidue n a (restrictResidue n b μ) =
      if a = b then restrictResidue n a μ else 0 := by
  refine Subtype.ext <| LinearMap.ext fun f ↦ ?_
  by_cases hab : a = b
  · subst hab
    simp [LocallyAnalytic.restrictResidue_restrictResidue]
  · simp [LocallyAnalytic.restrictResidue_restrictResidue, hab, Ne.symm hab]

/-- Restricting twice to the same residue class is restricting once. -/
@[simp]
theorem restrictResidue_idem (μ : LocallyAnalyticDistribution p K) :
    restrictResidue n a (restrictResidue n a μ) = restrictResidue n a μ := by
  simp [restrictResidue_restrictResidue]

/-- A distribution is the sum of its restrictions to the residue classes modulo `pⁿ`. -/
@[simp]
theorem sum_restrictResidue (μ : LocallyAnalyticDistribution p K) :
    ∑ a : ZMod (p ^ n), restrictResidue n a μ = μ := by
  refine Subtype.ext <| LinearMap.ext fun f ↦ ?_
  rw [Submodule.coe_sum, LinearMap.sum_apply]
  simp only [coe_restrictResidue_apply, ← map_sum, LocallyAnalytic.sum_restrictResidue]

/-- Modulo `p ^ 0 = 1` there is a single residue class, so restriction is the identity. -/
@[simp]
theorem restrictResidue_zero_depth (a : ZMod (p ^ 0)) (μ : LocallyAnalyticDistribution p K) :
    restrictResidue 0 a μ = μ :=
  Subtype.ext <| LinearMap.ext fun f ↦ by simp

/-- Restriction to a residue class keeps exactly the point masses in the class. -/
@[simp]
theorem restrictResidue_dirac (x : ℤ_[p]) :
    restrictResidue n a (dirac (K := K) x) = if PadicInt.toZModPow n x = a then dirac x else 0 := by
  refine Subtype.ext <| LinearMap.ext fun f ↦ ?_
  split_ifs with hx <;> simp [hx]

/-- On the distribution of a measure, restriction to a residue class is the restriction of the
measure. -/
@[simp]
theorem restrictResidue_ofMeasure (μ : AbstractMeasure ℤ_[p] K K) :
    restrictResidue n a (ofMeasure μ) = ofMeasure (AbstractMeasure.restrictResidue n a μ) := by
  refine Subtype.ext <| LinearMap.ext fun f ↦ ?_
  rw [coe_restrictResidue_apply, coe_ofMeasure_apply, coe_ofMeasure_apply,
    AbstractMeasure.restrictResidue_apply]
  congr 1
  ext x
  simp [ContinuousMap.fiberIndicator_apply]

end LocallyAnalyticDistribution

end TauCeti
