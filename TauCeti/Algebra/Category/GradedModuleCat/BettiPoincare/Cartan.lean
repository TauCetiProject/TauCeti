/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BettiPoincare.Ext
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ExtEuler.PowerSeries

/-!
# The Cartan–Betti Euler identity

Let `C(q)` be the graded Cartan matrix in a projective basis `bP` of `K₀^gr(proj A)` and a module
basis `bM` of `G₀^gr(mod A)`, and let `B(q, t)` be the Betti Poincaré power-series matrix
`TauCeti.bettiPoincarePowerSeriesMatrix` of graded projective resolutions of the basis modules.
This file proves the **Cartan–Betti Euler identity** `C(q) · B(q, -1) = I` in two complementary
settings:

1. **Finite resolutions over an arbitrary commutative base ring (`CommRing k`, `Ring A`)**: if each
   basis module `Mⱼ` (with `bM j = [Mⱼ]`) has a concrete graded projective resolution `rⱼ` with
   finitely generated terms such that `(rⱼ).X (Nⱼ)` is a subsingleton at some homological degree
   `Nⱼ`, then evaluating the polynomial truncation `PowerSeries.trunc (Nⱼ) (B i j)` at `-1` yields
   `C * B_trunc(-1) = 1` in `Matrix J J (LaurentPolynomial ℤ)`. Neither a field, a grading
   decomposition, minimality, nor finite-dimensionality over `k` is required. When `I = J`, the
   two-sided inverse identity `B_trunc(-1) * C = 1` and `B_trunc(-1) = C⁻¹` follow.
2. **Unbounded formal-power-series identity over an arbitrary field (`Field k`)**: over a
   finite-dimensional nonnegatively graded algebra with an exhaustive degree-zero simple family `Sᵢ`
   cut out by degree-zero idempotents `eᵢ` with `gdim(eᵢ • Sᵢ) ≠ 0`, let `rⱼ` be minimal graded
   projective resolutions of the `Sⱼ` with finitely generated terms (possibly of infinite length).
   Then every entry of `B` has a well-defined Alexander-graded Euler formal power series
   `Bigraded.eulerPowerSeries`, and in `Matrix I I (PowerSeries ℤ)`:

   ```text
   C_ps * B_ps = 1   and   B_ps * C_ps = 1.
   ```

   Unlike the Ext Cartan–Poincaré identity
   `TauCeti.gradedCartanMatrix_trunc_transpose_mul_eulerPowerSeries_eq_diagonal`, whose right-hand
   side retains the nonsplitting-field diagonal `dim_k(eᵢ • (Sᵢ)₀)`, the division-ring factors
   cancel out completely from `C_ps * B_ps = 1`. Moreover, simultaneous linearity of the minimal
   resolutions `rⱼ` is equivalent to `C_ps * B_maslov = 1`, where `B_maslov` applies
   `Bigraded.maslovEulerPowerSeries` entrywise to `bettiPoincarePowerSeriesMatrix bP r`.

## Main results

* `TauCeti.GradedProjectiveResolution.gradedCartanMap_sum_alternating_finiteProjectiveTerm`:
  alternating sum of resolution-term classes under `gradedCartanMap` equals `[M]` once a single
  term `r.X N` is a subsingleton.
* `TauCeti.gradedCartanMatrix_mul_eval_trunc_bettiPoincarePowerSeriesMatrix`,
  `TauCeti.eval_trunc_bettiPoincarePowerSeriesMatrix_mul_gradedCartanMatrix`, and
  `TauCeti.eval_trunc_bettiPoincarePowerSeriesMatrix_eq_inv_gradedCartanMatrix`: the Laurent
  Cartan–Betti identity `C(q) · B(q, -1) = 1` for finite resolutions.
* `TauCeti.gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincarePowerSeriesMatrix`,
  `TauCeti.eulerPowerSeries_bettiPoincarePowerSeriesMatrix_mul_gradedCartanMatrix_trunc`, and
  `TauCeti.eulerPowerSeries_bettiPoincarePowerSeriesMatrix_eq_inv_gradedCartanMatrix_trunc`: the
  unbounded formal-power-series Cartan–Betti identity over any field with `gdim(eᵢ • Sᵢ) ≠ 0`.
* `TauCeti.forall_isLinear_iff_gradedCartanMatrix_trunc_mul_maslovEulerPowerSeries_betti`:
  simultaneous linearity of minimal resolutions of `S` is equivalent to `C_ps * B_maslov = 1`.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Sections 1.2 and 2.11.
* Z. Dancso and A. Licata, *Koszul algebras and flow lattices*, Section 2.2.
* P. Webb, *A Course in Finite Group Representation Theory*, Proposition 7.4.1.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory LaurentPolynomial
open scoped Matrix Pointwise

universe uk uA uI uJ

/-! ### Finite resolutions over an arbitrary commutative base ring -/

section FiniteResolution

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

private lemma laurentK0_of_shortExact {S : ShortComplex (GradedModuleCat.{uA} 𝒜)}
    (hS : S.ShortExact) (h₁ : gradedFiniteModules 𝒜 S.X₁)
    (h₂ : gradedFiniteModules 𝒜 S.X₂) (h₃ : gradedFiniteModules 𝒜 S.X₃) :
    LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) ⟨S.X₂, h₂⟩ =
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) ⟨S.X₁, h₁⟩ +
        LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) ⟨S.X₃, h₃⟩ := by
  let S' : ShortComplex (gradedFiniteModules 𝒜).FullSubcategory :=
    ShortComplex.mk
      (ObjectProperty.homMk S.f :
        (⟨S.X₁, h₁⟩ : (gradedFiniteModules 𝒜).FullSubcategory) ⟶ ⟨S.X₂, h₂⟩)
      (ObjectProperty.homMk S.g :
        (⟨S.X₂, h₂⟩ : (gradedFiniteModules 𝒜).FullSubcategory) ⟶ ⟨S.X₃, h₃⟩)
      (ObjectProperty.hom_ext _ S.zero)
  exact LaurentK0.of_conflation.{uA} (gradedFiniteModulesExactStructure 𝒜)
    ((gradedFiniteModulesExactStructure_conflation_iff S').mpr hS)

private lemma laurentK0_of_gradedFiniteModules_eq_zero_of_subsingleton
    (X : (gradedFiniteModules 𝒜).FullSubcategory) [Subsingleton X.obj] :
    LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) X = 0 := by
  have hzero : Limits.IsZero X :=
    (Limits.IsZero.iff_id_eq_zero _).mpr <|
      ObjectProperty.hom_ext _ (GradedModuleCat.hom_ext (LinearMap.ext fun _ ↦
        Subsingleton.elim _ _))
  rw [← LaurentK0.ofExactK0_exactK0_of.{uA}, ExactK0.of_eq_zero_of_isZero.{uA} hzero, map_zero]

private lemma exact_kernelObj_step {P₁ P₀ Q : GradedModuleCat.{uA} 𝒜}
    (d₁ : P₁ ⟶ P₀) (d₀ : P₀ ⟶ Q) [Module.Finite A P₁]
    (hex : Function.Exact d₁.hom d₀.hom) :
    ∃ hK₀ : gradedFiniteModules 𝒜 (GradedModuleCat.kernelObj d₀),
      (Subsingleton P₁ → Subsingleton (GradedModuleCat.kernelObj d₀)) ∧
        ∀ (hK₁ : gradedFiniteModules 𝒜 (GradedModuleCat.kernelObj d₁)),
          LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜)
              ⟨P₁, gradedFiniteModules_iff.mpr inferInstance⟩ =
            LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜)
                ⟨GradedModuleCat.kernelObj d₁, hK₁⟩ +
              LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜)
                ⟨GradedModuleCat.kernelObj d₀, hK₀⟩ := by
  let p : P₁ ⟶ GradedModuleCat.kernelObj d₀ :=
    GradedModuleCat.ofHom
      (LinearMap.codRestrict (LinearMap.ker d₀.hom) d₁.hom fun x ↦
        LinearMap.mem_ker.mpr (hex.apply_apply_eq_zero x))
      (LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦ by
        simpa [GradedModuleCat.kernelObj] using GradedModuleCat.map_mem d₁ hx)
  have hp_surj : Function.Surjective p.hom := fun ⟨y, hy⟩ ↦ by
    obtain ⟨x, rfl⟩ := (hex y).mp (LinearMap.mem_ker.mp hy)
    exact ⟨x, rfl⟩
  have hK₀ : gradedFiniteModules 𝒜 (GradedModuleCat.kernelObj d₀) :=
    gradedFiniteModules_iff.mpr (Module.Finite.of_surjective p.hom hp_surj)
  refine ⟨hK₀, fun _ ↦ hp_surj.subsingleton, fun hK₁ ↦ ?_⟩
  have hzero : GradedModuleCat.kernelι d₁ ≫ p = 0 :=
    GradedModuleCat.hom_ext (LinearMap.ext fun z ↦ Subtype.ext z.2)
  have hS : (ShortComplex.mk (GradedModuleCat.kernelι d₁) p hzero).ShortExact :=
    { exact := GradedModuleCat.exact_iff.mpr fun x ↦
        ⟨fun hx ↦ LinearMap.mem_range.mpr ⟨⟨x, Subtype.ext_iff.mp hx⟩, rfl⟩,
          by rintro ⟨y, rfl⟩; exact Subtype.ext y.2⟩
      mono_f := (GradedModuleCat.mono_iff_injective _).mpr (Submodule.injective_subtype _)
      epi_g := (GradedModuleCat.epi_iff_surjective _).mpr hp_surj }
  exact laurentK0_of_shortExact hS hK₁ (gradedFiniteModules_iff.mpr inferInstance) hK₀

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}
  (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
  [∀ n, Module.Finite A (r.X n)]

private def cycleFiniteModule : ℕ → (gradedFiniteModules 𝒜).FullSubcategory
  | 0 => ⟨GradedModuleCat.kernelObj r.augmentation,
      (exact_kernelObj_step (r.differential 0) r.augmentation r.exact_d_π).1⟩
  | n + 1 => ⟨GradedModuleCat.kernelObj (r.differential n),
      (exact_kernelObj_step (r.differential (n + 1)) (r.differential n) (r.exact_d_d n)).1⟩

private lemma gradedCartanMap_zero_eq_add_cycle (hM : gradedFiniteModules 𝒜 M) :
    gradedCartanMap 𝒜
        (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
          (r.finiteProjectiveTerm 0)) =
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (r.cycleFiniteModule 0) +
        LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) ⟨M, hM⟩ := by
  have hS : (ShortComplex.mk (GradedModuleCat.kernelι r.augmentation) r.augmentation
      (GradedModuleCat.kernelι_comp _)).ShortExact :=
    { exact := GradedModuleCat.exact_iff.mpr (LinearMap.exact_subtype_ker_map r.π)
      mono_f := (GradedModuleCat.mono_iff_injective _).mpr (Submodule.injective_subtype _)
      epi_g := (GradedModuleCat.epi_iff_surjective _).mpr r.surjective_π }
  have hterm : gradedCartanMap 𝒜
      (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r.finiteProjectiveTerm 0)) =
    LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜)
      ⟨r.termObj 0, gradedFiniteModules_iff.mpr inferInstance⟩ := by
    have h0 : r.finiteProjectiveTerm 0 =
        ⟨r.termObj 0, gradedFiniteProjectiveModules_iff.mpr ⟨inferInstance, r.projective 0⟩⟩ :=
      ObjectProperty.FullSubcategory.ext (r.finiteProjectiveTerm_obj 0)
    rw [h0, gradedCartanMap_of]
  rw [hterm]
  exact laurentK0_of_shortExact hS (r.cycleFiniteModule 0).property
    (gradedFiniteModules_iff.mpr inferInstance) hM

private lemma gradedCartanMap_succ_eq_add_cycle (n : ℕ) :
    gradedCartanMap 𝒜
        (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
          (r.finiteProjectiveTerm (n + 1))) =
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (r.cycleFiniteModule (n + 1)) +
        LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (r.cycleFiniteModule n) := by
  have hterm : gradedCartanMap 𝒜
      (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r.finiteProjectiveTerm (n + 1))) =
    LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜)
      ⟨r.termObj (n + 1), gradedFiniteModules_iff.mpr inferInstance⟩ := by
    have h1 : r.finiteProjectiveTerm (n + 1) =
        ⟨r.termObj (n + 1),
          gradedFiniteProjectiveModules_iff.mpr ⟨inferInstance, r.projective (n + 1)⟩⟩ :=
      ObjectProperty.FullSubcategory.ext (r.finiteProjectiveTerm_obj (n + 1))
    rw [h1, gradedCartanMap_of]
  rw [hterm]
  cases n with
  | zero =>
    exact (exact_kernelObj_step (r.differential 0) r.augmentation r.exact_d_π).2.2
      (r.cycleFiniteModule 1).property
  | succ m =>
    exact (exact_kernelObj_step (r.differential (m + 1)) (r.differential m) (r.exact_d_d m)).2.2
      (r.cycleFiniteModule (m + 2)).property

private lemma sum_alternating_gradedCartanMap_eq_add_cycle (hM : gradedFiniteModules 𝒜 M)
    (m : ℕ) :
    (∑ n ∈ Finset.range (m + 1),
        (-1 : LaurentPolynomial ℤ) ^ n •
          gradedCartanMap 𝒜
            (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
              (r.finiteProjectiveTerm n))) =
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) ⟨M, hM⟩ +
        (-1 : LaurentPolynomial ℤ) ^ m •
          LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (r.cycleFiniteModule m) := by
  induction m with
  | zero =>
    rw [Finset.sum_range_one, r.gradedCartanMap_zero_eq_add_cycle hM]
    simp only [pow_zero, one_smul, add_comm]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, r.gradedCartanMap_succ_eq_add_cycle m, smul_add,
      add_assoc]
    congr 1
    calc
      (-1 : LaurentPolynomial ℤ) ^ m •
          LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (r.cycleFiniteModule m) +
        ((-1 : LaurentPolynomial ℤ) ^ (m + 1) •
            LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜)
              (r.cycleFiniteModule (m + 1)) +
          (-1 : LaurentPolynomial ℤ) ^ (m + 1) •
            LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (r.cycleFiniteModule m))
        = ((-1 : LaurentPolynomial ℤ) ^ m •
            LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (r.cycleFiniteModule m) +
          (-1 : LaurentPolynomial ℤ) ^ (m + 1) •
            LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (r.cycleFiniteModule m)) +
          (-1 : LaurentPolynomial ℤ) ^ (m + 1) •
            LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜)
              (r.cycleFiniteModule (m + 1)) := by abel
      _ = (-1 : LaurentPolynomial ℤ) ^ (m + 1) •
            LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜)
              (r.cycleFiniteModule (m + 1)) := by
        rw [← add_smul, pow_succ, mul_neg_one, add_neg_cancel, zero_smul, zero_add]

/-- **Graded Euler relation for a finite graded projective resolution.** If `r.X N` is a
subsingleton at homological degree `N`, the alternating sum of `[Pₙ]` over `n < N` maps under
`gradedCartanMap 𝒜` to `[M]` in `G₀^gr(mod A)`. Neither a field, a grading decomposition, nor
minimality is assumed. -/
theorem gradedCartanMap_sum_alternating_finiteProjectiveTerm (N : ℕ) [Subsingleton (r.X N)]
    (hM : gradedFiniteModules 𝒜 M :=
      gradedFiniteModules_iff.mpr (Module.Finite.of_surjective r.π r.surjective_π)) :
    gradedCartanMap 𝒜
        (∑ n ∈ Finset.range N,
          (-1 : LaurentPolynomial ℤ) ^ n •
            LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
              (r.finiteProjectiveTerm n)) =
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) ⟨M, hM⟩ := by
  rw [map_sum]
  simp only [map_smul]
  cases N with
  | zero =>
    have : Subsingleton (⟨M, hM⟩ : (gradedFiniteModules 𝒜).FullSubcategory).obj :=
      r.surjective_π.subsingleton
    rw [Finset.sum_range_zero, laurentK0_of_gradedFiniteModules_eq_zero_of_subsingleton ⟨M, hM⟩]
  | succ m =>
    rw [r.sum_alternating_gradedCartanMap_eq_add_cycle hM m]
    have : Subsingleton (r.cycleFiniteModule m).obj := by
      cases m with
      | zero =>
        exact (exact_kernelObj_step (r.differential 0) r.augmentation r.exact_d_π).2.1
          ‹Subsingleton (r.X 1)›
      | succ l =>
        exact (exact_kernelObj_step (r.differential (l + 1)) (r.differential l)
          (r.exact_d_d l)).2.1 ‹Subsingleton (r.X (l + 2))›
    rw [laurentK0_of_gradedFiniteModules_eq_zero_of_subsingleton (r.cycleFiniteModule m),
      smul_zero, add_zero]

end GradedProjectiveResolution

/-- **The Laurent Cartan–Betti identity `C(q) · B(q, -1) = 1` for finite resolutions.** Let `bP`
(indexed by `I`) and `bM` (indexed by `J`) be bases of `K₀^gr(proj A)` and `G₀^gr(mod A)` with
`bM j = [M j]`. If each `M j` has a graded projective resolution `r j` with finitely generated
terms and `Subsingleton ((r j).X (N j))`, then multiplying `gradedCartanMatrix 𝒜 bP bM` on the
right by the matrix of polynomial truncations evaluated at `-1` yields the identity matrix. -/
theorem gradedCartanMatrix_mul_eval_trunc_bettiPoincarePowerSeriesMatrix
    {I : Type uI} {J : Type uJ} [Fintype I] [Finite J] [DecidableEq J]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (bM : Module.Basis J (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)))
    (M : J → (gradedFiniteModules 𝒜).FullSubcategory)
    (hbM : ∀ j, bM j = LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (M j))
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)]
    (N : J → ℕ) [∀ j, Subsingleton ((r j).X (N j))] :
    gradedCartanMatrix 𝒜 bP bM *
      Matrix.of (fun i j ↦
        (PowerSeries.trunc (N j) (bettiPoincarePowerSeriesMatrix bP r i j)).eval (-1)) = 1 := by
  refine Matrix.ext fun l j ↦ ?_
  let x : LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) :=
    ∑ n ∈ Finset.range (N j),
      (-1 : LaurentPolynomial ℤ) ^ n •
        LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
          ((r j).finiteProjectiveTerm n)
  have hcol (i : I) :
      (PowerSeries.trunc (N j) (bettiPoincarePowerSeriesMatrix bP r i j)).eval (-1) =
        bP.repr x i := by
    rw [bettiPoincarePowerSeriesMatrix_apply, ← Polynomial.eval₂_id,
      PowerSeries.eval₂_trunc_eq_sum_range, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [RingHom.id_apply, GradedProjectiveResolution.coeff_bettiPoincarePowerSeries,
      map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  have hmul :
      (gradedCartanMatrix 𝒜 bP bM *
        Matrix.of (fun i m ↦
          (PowerSeries.trunc (N m) (bettiPoincarePowerSeriesMatrix bP r i m)).eval (-1))) l j =
        Matrix.mulVec (gradedCartanMatrix 𝒜 bP bM) (bP.repr x) l := by
    rw [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [Matrix.of_apply, hcol i]
  rw [hmul, gradedCartanMatrix_mulVec_repr,
    (r j).gradedCartanMap_sum_alternating_finiteProjectiveTerm (N j) (M j).property,
    ← hbM j, bM.repr_self, Finsupp.single_apply, Matrix.one_apply]
  simp [eq_comm]

/-- Square two-sided form of the finite-resolution Cartan–Betti identity: `B_trunc(-1) * C = 1`. -/
theorem eval_trunc_bettiPoincarePowerSeriesMatrix_mul_gradedCartanMatrix
    {I : Type uI} [Fintype I] [DecidableEq I]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (bM : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)))
    (M : I → (gradedFiniteModules 𝒜).FullSubcategory)
    (hbM : ∀ j, bM j = LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (M j))
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)]
    (N : I → ℕ) [∀ j, Subsingleton ((r j).X (N j))] :
    Matrix.of (fun i j ↦
        (PowerSeries.trunc (N j) (bettiPoincarePowerSeriesMatrix bP r i j)).eval (-1)) *
      gradedCartanMatrix 𝒜 bP bM = 1 :=
  mul_eq_one_comm.mp
    (gradedCartanMatrix_mul_eval_trunc_bettiPoincarePowerSeriesMatrix bP bM M hbM r N)

/-- For square bases, `B(q, -1)` is the nonsingular matrix inverse of `gradedCartanMatrix`. -/
theorem eval_trunc_bettiPoincarePowerSeriesMatrix_eq_inv_gradedCartanMatrix
    {I : Type uI} [Fintype I] [DecidableEq I]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (bM : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)))
    (M : I → (gradedFiniteModules 𝒜).FullSubcategory)
    (hbM : ∀ j, bM j = LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (M j))
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)]
    (N : I → ℕ) [∀ j, Subsingleton ((r j).X (N j))] :
    Matrix.of (fun i j ↦
        (PowerSeries.trunc (N j) (bettiPoincarePowerSeriesMatrix bP r i j)).eval (-1)) =
      (gradedCartanMatrix 𝒜 bP bM)⁻¹ :=
  (Matrix.inv_eq_right_inv
    (gradedCartanMatrix_mul_eval_trunc_bettiPoincarePowerSeriesMatrix bP bM M hbM r N)).symm

end FiniteResolution

/-! ### Unbounded formal-power-series Cartan–Betti identities -/

section UnboundedPowerSeries

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [Module.Finite k A]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
  {I : Type uI} [Fintype I] [DecidableEq I]
  (S : I → (gradedFiniteModules 𝒜).FullSubcategory) {e : I → A}
  (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
  (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0)
  (hS : IsExhaustiveGradedSimpleFamily S)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)

include hbP in
/-- **Unbounded formal-power-series Cartan–Betti identity (`B_ps * C_ps = 1`).** Over any ground
field `k` with `gdim(eᵢ • Sᵢ) ≠ 0`, let `rⱼ` be minimal graded projective resolutions of the
exhaustive degree-zero simple family `Sⱼ` with finitely generated terms. Then the matrix of
Alexander-graded Euler formal power series of `(r j).bettiPoincarePowerSeries bP i` is a left
inverse of the truncated graded Cartan matrix in `Matrix I I (PowerSeries ℤ)`, with no
cohomological global-dimension bound and no splitting-field hypothesis. -/
theorem eulerPowerSeries_bettiPoincarePowerSeriesMatrix_mul_gradedCartanMatrix_trunc
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hB : ∀ i j, Bigraded.HasEulerPowerSeries ((r j).bettiPoincarePowerSeries bP i) :=
      fun i j ↦ (hr j).hasEulerPowerSeries_bettiPoincarePowerSeries
        S he he₀ hI hne bP hbP hself (fun q hq ↦ hconc j q hq.ne) hconc i) :
    Matrix.of (fun i j ↦ Bigraded.eulerPowerSeries (hB i j)) *
      ((gradedCartanMatrix 𝒜 bP
          (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
        fun p ↦ (p.trunc : PowerSeries ℤ)) = 1 := by
  let _ (j : I) (n : ℕ) : Module.Finite k ((r j).X n) := Module.Finite.trans A ((r j).X n)
  let h (i j : I) :
      IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj :=
    GradedModuleCat.isGradedExtInternallyFinite_of_moduleFinite (S i).obj (S j).obj
  set Cps : Matrix I I (PowerSeries ℤ) :=
    (gradedCartanMatrix 𝒜 bP
      (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
      fun p ↦ (p.trunc : PowerSeries ℤ)
  set Bps : Matrix I I (PowerSeries ℤ) :=
    Matrix.of fun i j ↦ Bigraded.eulerPowerSeries (hB i j)
  set d : I → PowerSeries ℤ := fun i ↦
    PowerSeries.C (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ)
  have hExt := congrArg Matrix.transpose
    (gradedCartanMatrix_trunc_transpose_mul_eulerPowerSeries_eq_diagonal
      S he he₀ hI hne hself hS bP hbP r hr hneg hconc h)
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose] at hExt
  have hDB : Matrix.diagonal d * Bps =
      (Matrix.of fun j i ↦ Bigraded.eulerPowerSeries
        ((hr j).hasEulerPowerSeries_bigradedExtPoincarePowerSeries
          (fun p hp ↦ hconc j p hp.ne) (hconc i) (h j i)))ᵀ :=
    Matrix.ext fun i j ↦ by
      rw [Matrix.diagonal_mul, Matrix.transpose_apply, Matrix.of_apply]
      exact (hr j).C_finrank_mul_eulerPowerSeries S he he₀ hI hne bP hbP hself
        (fun q hq ↦ hconc j q hq.ne) hconc i (h j i) (hB i j) _
  rw [← hDB, Matrix.mul_assoc] at hExt
  refine Matrix.ext fun i j ↦ ?_
  have hd0 : d i ≠ 0 := by
    intro h0
    have hpos : (0 : ℤ) < Module.finrank k ↥(e i • (S i).obj.grading.piece 0) :=
      Int.natCast_pos.mpr
        ((S i).obj.finrank_smul_piece_zero_pos_of_concentrated (e i) (hconc i) (hself i))
    have hc := congrArg PowerSeries.constantCoeff h0
    simp only [d, PowerSeries.constantCoeff_C, map_zero] at hc
    omega
  have hij := congrFun (congrFun hExt i) j
  rw [Matrix.diagonal_mul, Matrix.diagonal_apply] at hij
  apply mul_left_cancel₀ hd0
  rw [hij, Matrix.one_apply]
  split_ifs <;> simp [d]

include hbP in
/-- **Unbounded formal-power-series Cartan–Betti identity (`C_ps * B_ps = 1`).** Multiplying the
truncated graded Cartan matrix on the right by the Alexander-graded Euler formal power-series
matrix of minimal resolutions `rⱼ` yields the identity matrix over any field `k` with
`gdim(eᵢ • Sᵢ) ≠ 0`. -/
theorem gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincarePowerSeriesMatrix
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hB : ∀ i j, Bigraded.HasEulerPowerSeries ((r j).bettiPoincarePowerSeries bP i) :=
      fun i j ↦ (hr j).hasEulerPowerSeries_bettiPoincarePowerSeries
        S he he₀ hI hne bP hbP hself (fun q hq ↦ hconc j q hq.ne) hconc i) :
    ((gradedCartanMatrix 𝒜 bP
          (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
        fun p ↦ (p.trunc : PowerSeries ℤ)) *
      Matrix.of (fun i j ↦ Bigraded.eulerPowerSeries (hB i j)) = 1 :=
  mul_eq_one_comm.mp
    (eulerPowerSeries_bettiPoincarePowerSeriesMatrix_mul_gradedCartanMatrix_trunc
      S he he₀ hI hne hself hS bP hbP r hr hneg hconc hB)

include hbP in
/-- The Alexander-graded Euler formal power-series matrix of minimal resolutions `rⱼ` is the
nonsingular inverse of the truncated graded Cartan matrix in `Matrix I I (PowerSeries ℤ)`. -/
theorem eulerPowerSeries_bettiPoincarePowerSeriesMatrix_eq_inv_gradedCartanMatrix_trunc
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hB : ∀ i j, Bigraded.HasEulerPowerSeries ((r j).bettiPoincarePowerSeries bP i) :=
      fun i j ↦ (hr j).hasEulerPowerSeries_bettiPoincarePowerSeries
        S he he₀ hI hne bP hbP hself (fun q hq ↦ hconc j q hq.ne) hconc i) :
    Matrix.of (fun i j ↦ Bigraded.eulerPowerSeries (hB i j)) =
      (((gradedCartanMatrix 𝒜 bP
          (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
        fun p ↦ (p.trunc : PowerSeries ℤ)))⁻¹ :=
  (Matrix.inv_eq_right_inv
    (gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincarePowerSeriesMatrix
      S he he₀ hI hne hself hS bP hbP r hr hneg hconc hB)).symm

include hbP in
/-- **Linearity is the total-Betti formal-power-series Cartan–Poincaré identity.** Chosen minimal
resolutions `rⱼ` of the exhaustive degree-zero simple family `Sⱼ` with finitely generated terms are
all linear if and only if `C_ps * B_maslov = 1` in `Matrix I I (PowerSeries ℤ)`, where `B_maslov`
applies `Bigraded.maslovEulerPowerSeries` entrywise to `bettiPoincarePowerSeriesMatrix bP r`. -/
theorem forall_isLinear_iff_gradedCartanMatrix_trunc_mul_maslovEulerPowerSeries_betti
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) :
    (∀ j, (r j).IsLinear) ↔
      ((gradedCartanMatrix 𝒜 bP
            (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
          fun p ↦ (p.trunc : PowerSeries ℤ)) *
        (bettiPoincarePowerSeriesMatrix bP r).map Bigraded.maslovEulerPowerSeries = 1 := by
  let hB (i j : I) : Bigraded.HasEulerPowerSeries ((r j).bettiPoincarePowerSeries bP i) :=
    (hr j).hasEulerPowerSeries_bettiPoincarePowerSeries
      S he he₀ hI hne bP hbP hself (fun q hq ↦ hconc j q hq.ne) hconc i
  set Cps := (gradedCartanMatrix 𝒜 bP
    (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
    fun p ↦ (p.trunc : PowerSeries ℤ)
  set Bps := Matrix.of fun i j ↦ Bigraded.eulerPowerSeries (hB i j)
  have hBC := eulerPowerSeries_bettiPoincarePowerSeriesMatrix_mul_gradedCartanMatrix_trunc
    S he he₀ hI hne hself hS bP hbP r hr hneg hconc hB
  have hCB := gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincarePowerSeriesMatrix
    S he he₀ hI hne hself hS bP hbP r hr hneg hconc hB
  have hiff (i j : I) :
      Bigraded.eulerPowerSeries (hB i j) =
        Bigraded.maslovEulerPowerSeries (bettiPoincarePowerSeriesMatrix bP r i j) ↔
      ∀ (n : ℕ) (p : ℤ), (n : ℤ) ≠ p →
        (PowerSeries.coeff n (bettiPoincarePowerSeriesMatrix bP r i j)).coeff p = 0 := by
    rw [bettiPoincarePowerSeriesMatrix_apply]
    exact Bigraded.eulerPowerSeries_eq_maslovEulerPowerSeries_iff (hB i j)
      (fun n p ↦ (hr j).coeff_coeff_bettiPoincarePowerSeries_nonneg
        S he he₀ hI hne bP hbP hself hconc n p i)
      (fun _ _ hpn ↦ (hr j).coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_lt
        S he he₀ hI hne bP hbP hself (fun q hq ↦ hconc j q hq.ne) hconc (by omega) i)
  rw [forall_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix
    S he he₀ hI hne bP hbP hself hS r hr hneg hconc]
  constructor
  · intro hdiag
    rw [← hCB]
    congr 1
    exact Matrix.ext fun i j ↦ ((hiff i j).2 (hdiag i j)).symm
  · intro hid i j
    have heq : Bps = (bettiPoincarePowerSeriesMatrix bP r).map Bigraded.maslovEulerPowerSeries := by
      calc Bps = Bps * 1 := (Matrix.mul_one Bps).symm
        _ = Bps * (Cps *
              (bettiPoincarePowerSeriesMatrix bP r).map Bigraded.maslovEulerPowerSeries) := by
            rw [hid]
        _ = (Bps * Cps) *
              (bettiPoincarePowerSeriesMatrix bP r).map Bigraded.maslovEulerPowerSeries :=
            (Matrix.mul_assoc _ _ _).symm
        _ = (bettiPoincarePowerSeriesMatrix bP r).map Bigraded.maslovEulerPowerSeries := by
            rw [hBC, Matrix.one_mul]
    exact (hiff i j).1 (congrFun (congrFun heq i) j)

end UnboundedPowerSeries

section UnitDiagonal

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [Module.Finite k A]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
  {I : Type uI} [Fintype I] [DecidableEq I]
  (S : I → (gradedFiniteModules 𝒜).FullSubcategory) {e : I → A}
  (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
  (hself : ∀ i, (S i).obj.smulGradedDimension (e i) = 1)
  (hS : IsExhaustiveGradedSimpleFamily S)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)

include hbP in
/-- Specialization of `gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincarePowerSeriesMatrix`
to `gradedSimpleClassBasis` when `gdim(eᵢ • Sᵢ) = 1` for all `i`. -/
theorem gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincarePowerSeriesMatrix_simpleBasis
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hB : ∀ i j, Bigraded.HasEulerPowerSeries ((r j).bettiPoincarePowerSeries bP i) :=
      fun i j ↦ (hr j).hasEulerPowerSeries_bettiPoincarePowerSeries
        S he he₀ hI hne bP hbP (fun m ↦ (hself m).symm ▸ one_ne_zero)
          (fun q hq ↦ hconc j q hq.ne) hconc i) :
    ((gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasis S he he₀ hne hself hS)).map
        fun p ↦ (p.trunc : PowerSeries ℤ)) *
      Matrix.of (fun i j ↦ Bigraded.eulerPowerSeries (hB i j)) = 1 := by
  have hbasis : gradedSimpleClassBasis S he he₀ hne hself hS =
      gradedSimpleClassBasisOfNeZero S he he₀ hne (fun m ↦ (hself m).symm ▸ one_ne_zero) hS :=
    DFunLike.ext _ _ fun _ ↦ by simp
  rw [hbasis]
  exact gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincarePowerSeriesMatrix
    S he he₀ hI hne (fun m ↦ (hself m).symm ▸ one_ne_zero) hS bP hbP r hr hneg hconc hB

end UnitDiagonal

end TauCeti
