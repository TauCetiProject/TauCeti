/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bigraded.PowerSeries
public import TauCeti.Algebra.Category.GradedModuleCat.BettiPoincare.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Ideal
public import TauCeti.Algebra.Category.GradedModuleCat.DegreeQuotient
public import TauCeti.Algebra.Category.GradedModuleCat.FiniteLength
public import TauCeti.Algebra.Category.GradedModuleCat.HomLaurentSupport
public import TauCeti.Algebra.Category.GradedModuleCat.Ideal
public import TauCeti.Algebra.Category.GradedModuleCat.Idempotent.GradedDimension
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.SimpleFamily
public import TauCeti.Algebra.Module.GradedModule.Linearity

/-!
# Graded Betti multiplicities and the diagonal-support criterion for linear resolutions

Let `A` be a `ℤ`-graded `k`-algebra over a field `k` and let `N` be a `k`-finite-dimensional graded
`A`-module. For every finitely generated graded projective `P`, the graded Hom spaces
`Hom_{A-gr}(P, N{d})` have finite Laurent support, and their graded dimension
`∑_d dim_k Hom_{A-gr}(P, N{d}) qᵈ` is additive on split conflations and covariantly `q`-linear
(`P{1} ↦ q · -`). It therefore descends to a `ℤ[q,q⁻¹]`-linear functional
`TauCeti.gradedProjectiveHomGradedDimension N` on `K₀^gr(proj A)` without requiring `A` itself to
be finite-dimensional over `k`.

When `bP` is a `ℤ[q,q⁻¹]`-basis of `K₀^gr(proj A)` given by degree-zero-generated projectives `Pᵢ`
and `Sᵢ` are `k`-finite-dimensional degree-zero graded modules satisfying `Hom(Pᵢ, Sⱼ) = 0` for
`i ≠ j`, evaluating `gradedProjectiveHomGradedDimension (Sᵢ)` reads the `i`th projective coordinate
up to the scalar multiplicity `dᵢ = dim_k Hom_{A-gr}(Pᵢ, Sᵢ)`. Applied to a graded projective
resolution `r` of `M` with finitely generated terms, this identifies the bigraded coefficients of
`r.bettiPoincarePowerSeries bP i`:

```text
dᵢ · [qᵈ][tⁿ] B_M(q, t)_i = dim_k Hom_{A-gr}(Pₙ, Sᵢ{d}) = dim_k Extⁿ_{A-gr}(M, Sᵢ{d}),
```

where the second equality holds whenever `r` is minimal. Over a nonnegatively graded algebra with
`dim_k A₀ < ∞` (allowing infinite-dimensional Koszul algebras such as polynomial rings), when `S`
is an exhaustive degree-zero simple family and each `dᵢ > 0`, a resolution `r` with finitely
generated projective terms is linear if and only if every `r.bettiPoincarePowerSeries bP i` is
supported on the diagonal `d = n`, and a family of resolutions is simultaneously linear if and only
if `TauCeti.bettiPoincarePowerSeriesMatrix` is supported on the diagonal in every entry.

## Main definitions

* `TauCeti.gradedProjectiveHomGradedDimension`: the `ℤ[q,q⁻¹]`-linear functional on
  `K₀^gr(proj A)` sending `[P]` to `∑_d dim_k Hom_{A-gr}(P, N{d}) qᵈ`.

## Main results

* `TauCeti.gradedProjectiveHomGradedDimension_eq_mul_repr`: pairing against an orthogonal
  degree-zero target `Sᵢ` multiplies the `i`th projective coordinate by `dim_k Hom(Pᵢ, Sᵢ)`.
* `TauCeti.GradedProjectiveResolution.finrank_mul_coeff_coeff_bettiPoincarePowerSeries` and
  `TauCeti.GradedProjectiveResolution.IsMinimal.finrank_mul_coeff_coeff_bettiPoincarePowerSeries`:
  the Betti Poincaré coefficients compute graded Hom and graded Ext dimensions.
* `TauCeti.GradedProjectiveResolution.IsMinimal.hasEulerPowerSeries_bettiPoincarePowerSeries`:
  lower-triangularity and slicewise finiteness for modules vanishing in negative degrees.
* `TauCeti.GradedProjectiveResolution.isLinear_iff_diagonal_bettiPoincarePowerSeries` and
  `TauCeti.GradedProjectiveResolution.IsMinimal.isLinear_iff_eulerPowerSeries_eq`:
  linearity characterized by diagonal support and by agreement of the Alexander- and Maslov-graded
  Euler power series.
* `TauCeti.forall_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix`: simultaneous linearity of
  a family of resolutions characterized by diagonal support of the Betti Poincaré matrix.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Sections 1.2 and 2.11, for graded Betti numbers, linear resolutions, and Poincaré matrices.
* P. Webb, *A Course in Finite Group Representation Theory*, Proposition 7.4.1, for the
  endomorphism-dimension factor `dim_k Hom(Pᵢ, Sᵢ)` over non-splitting fields.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits LaurentPolynomial
open scoped Pointwise

universe uk uA uI uJ

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-! ### Covariant graded Hom functionals on `K₀^gr(proj A)` -/

section HomGradedDimension

omit [GradedAlgebra 𝒜] in
private def biprodHomLinearEquiv (X Y Z : GradedModuleCat.{uA} 𝒜) :
    (X ⊞ Y ⟶ Z) ≃ₗ[k] (X ⟶ Z) × (Y ⟶ Z) where
  toFun f := (biprod.inl ≫ f, biprod.inr ≫ f)
  invFun fg := biprod.desc fg.1 fg.2
  left_inv f := biprod.hom_ext' _ _ (by simp) (by simp)
  right_inv fg := Prod.ext (by simp) (by simp)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

omit [GradedAlgebra 𝒜] in
private def shiftObjHomLinearEquiv (M N : GradedModuleCat.{uA} 𝒜) (r s : ℤ) :
    (M.shiftObj r ⟶ N.shiftObj s) ≃ₗ[k] (M ⟶ N.shiftObj (s + -r)) where
  toFun f := GradedModuleCat.ofHom (M := M) (N := N.shiftObj (s + -r)) f.hom <|
    LinearMap.isHomogeneous_def.mpr fun p x hx ↦ by
      have hx' : x ∈ (M.shiftObj r).grading.piece (p + r) := by
        rw [GradedModuleCat.mem_shiftObj_piece_iff, add_sub_cancel_right]
        exact hx
      have hfx := GradedModuleCat.map_mem f hx'
      rw [GradedModuleCat.mem_shiftObj_piece_iff] at hfx ⊢
      simpa only [show p + 0 - (s + -r) = p + r - s by omega] using hfx
  invFun g := GradedModuleCat.ofHom (M := M.shiftObj r) (N := N.shiftObj s) g.hom <|
    LinearMap.isHomogeneous_def.mpr fun p x hx ↦ by
      rw [GradedModuleCat.mem_shiftObj_piece_iff] at hx
      have hgx := GradedModuleCat.map_mem g hx
      rw [GradedModuleCat.mem_shiftObj_piece_iff] at hgx ⊢
      simpa only [show p + 0 - s = p - r - (s + -r) by omega] using hgx
  left_inv _ := GradedModuleCat.hom_ext rfl
  right_inv _ := GradedModuleCat.hom_ext rfl
  map_add' _ _ := GradedModuleCat.hom_ext rfl
  map_smul' _ _ := GradedModuleCat.hom_ext rfl

private def homGradedDimensionInvariant (N : GradedModuleCat.{uA} 𝒜) [Module.Finite k N] :
    GradedExactStructure.ShiftInvariant (gradedFiniteProjectiveModulesExactStructure 𝒜)
      (laurentTAut ℤ (LaurentPolynomial ℤ)) where
  obj P := gradedDimension k (fun d : ℤ ↦ P.obj ⟶ N.shiftObj d)
    (GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj.{uA} P.obj N)
  map_conflation S hS := by
    change (gradedFiniteProjectiveModulesExactStructure 𝒜).toExactStructure.Conflation S at hS
    rw [gradedFiniteProjectiveModulesExactStructure_eq_split, ExactStructure.split_conflation] at hS
    obtain ⟨σ⟩ := hS
    let eIso : S.X₂.obj ≅ S.X₁.obj ⊞ S.X₃.obj :=
      (σ.map (gradedFiniteProjectiveModules 𝒜).ι).isoBinaryBiproduct
    let e (d : ℤ) : (S.X₂.obj ⟶ N.shiftObj d) ≃ₗ[k]
        (S.X₁.obj ⟶ N.shiftObj d) × (S.X₃.obj ⟶ N.shiftObj d) :=
      (Linear.homCongr k eIso (Iso.refl _)).trans
        (biprodHomLinearEquiv S.X₁.obj S.X₃.obj (N.shiftObj d))
    have h₁ := GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj.{uA} S.X₁.obj N
    have h₂ := GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj.{uA} S.X₂.obj N
    have h₃ := GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj.{uA} S.X₃.obj N
    exact (gradedDimension_congr h₂ (h₁.prod h₃) fun d ↦ (e d).finrank_eq).trans
      (gradedDimension_prod h₁ h₃)
  map_shift P := by
    let P' := (gradedFiniteProjectiveModulesExactStructure 𝒜).shift.functor.obj P
    let eShift : P'.obj ≅ P.obj.shiftObj 1 :=
      (gradedFiniteProjectiveModulesExactStructureShiftFunctorCompιIso (𝒜 := 𝒜)).app P
    let e (d : ℤ) : (P'.obj ⟶ N.shiftObj d) ≃ₗ[k] (P.obj ⟶ N.shiftObj (d + -1)) :=
      (Linear.homCongr k eShift (Iso.refl _)).trans
        (shiftObjHomLinearEquiv P.obj N 1 d)
    have hP := GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj.{uA} P.obj N
    have hP' := GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj.{uA} P'.obj N
    rw [laurentTAut_apply, smul_eq_mul]
    exact (gradedDimension_congr hP' (hP.reindex_add (-1)) fun d ↦ (e d).finrank_eq).trans
      (by simpa using gradedDimension_reindex_add hP (-1))

/-- **The covariant graded Hom functional on `K₀^gr(proj A)`.** For a `k`-finite-dimensional graded
`A`-module `N`, this `ℤ[q,q⁻¹]`-linear map sends `[P]` to `∑_d dim_k Hom_{A-gr}(P, N{d}) qᵈ`. The
algebra `A` itself need not be finite-dimensional over `k`. -/
def gradedProjectiveHomGradedDimension (N : GradedModuleCat.{uA} 𝒜) [Module.Finite k N] :
    LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) →ₗ[LaurentPolynomial ℤ]
      LaurentPolynomial ℤ :=
  LaurentK0.lift _ (homGradedDimensionInvariant N)

/-- On the class of a finite graded projective `P`, `gradedProjectiveHomGradedDimension N` computes
the graded dimension of `d ↦ Hom_{A-gr}(P, N{d})`. -/
@[simp]
theorem gradedProjectiveHomGradedDimension_of (N : GradedModuleCat.{uA} 𝒜) [Module.Finite k N]
    (P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    gradedProjectiveHomGradedDimension N
        (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) P) =
      gradedDimension k (fun d : ℤ ↦ P.obj ⟶ N.shiftObj d)
        (GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj.{uA} P.obj N) :=
  LaurentK0.lift_of.{uA} _ P

/-- The `qᵈ`-coefficient of `gradedProjectiveHomGradedDimension N [P]` is
`dim_k Hom_{A-gr}(P, N{d})`. -/
theorem coeff_gradedProjectiveHomGradedDimension_of (N : GradedModuleCat.{uA} 𝒜)
    [Module.Finite k N] (P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) (d : ℤ) :
    (gradedProjectiveHomGradedDimension N
        (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) P)).coeff d =
      Module.finrank k (P.obj ⟶ N.shiftObj d) := by
  rw [gradedProjectiveHomGradedDimension_of, coeff_gradedDimension]

/-- A finitely generated graded projective `P` generated in degree `r` pairs with a degree-zero
target `N` as the single monomial `dim_k Hom(P, N{r}) qʳ`. -/
theorem gradedProjectiveHomGradedDimension_of_isGeneratedInDegree
    (N : GradedModuleCat.{uA} 𝒜) [Module.Finite k N]
    (hN : ∀ p, p ≠ 0 → N.grading.piece p = ⊥)
    (P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) {r : ℤ}
    (hP : P.obj.grading.IsGeneratedInDegree A r) :
    gradedProjectiveHomGradedDimension N
        (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) P) =
      C (Module.finrank k (P.obj ⟶ N.shiftObj r) : ℤ) * T r := by
  rw [gradedProjectiveHomGradedDimension_of,
    gradedDimension_eq_sum _ {r} fun d hd ↦ ?_, Finset.sum_singleton]
  have hd' : d ≠ r := Finset.notMem_singleton.mp hd
  refine subsingleton_of_forall_eq 0 fun f ↦ GradedModuleCat.hom_ext ?_
  rw [GradedModuleCat.hom_zero]
  exact P.obj.grading.linearMap_eq_zero_of_isGeneratedInDegree hP f.isHomogeneous
    (by simpa [sub_eq_add_neg] using hN (r - d) (sub_ne_zero.mpr hd'.symm))

/-- A finitely generated graded projective generated in degree zero pairs with a degree-zero target
as the constant polynomial `dim_k Hom(P, N)`. -/
theorem gradedProjectiveHomGradedDimension_of_isGeneratedInDegree_zero
    (N : GradedModuleCat.{uA} 𝒜) [Module.Finite k N]
    (hN : ∀ p, p ≠ 0 → N.grading.piece p = ⊥)
    (P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory)
    (hP : P.obj.grading.IsGeneratedInDegree A 0) :
    gradedProjectiveHomGradedDimension N
        (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) P) =
      C (Module.finrank k (P.obj ⟶ N) : ℤ) := by
  let e0 : (P.obj ⟶ N.shiftObj 0) ≃ₗ[k] (P.obj ⟶ N) :=
    Linear.homCongr k (Iso.refl P.obj) ((GradedModuleCat.shiftFunctorZeroIso 𝒜).app N)
  rw [gradedProjectiveHomGradedDimension_of_isGeneratedInDegree N hN P hP, T_zero, mul_one,
    e0.finrank_eq]

/-- Graded Hom from a finitely generated graded module into a `k`-finite-dimensional graded module
is finite-dimensional over `k`. -/
theorem GradedModuleCat.moduleFinite_hom_of_moduleFinite_left
    (P N : GradedModuleCat.{uA} 𝒜) [Module.Finite A P] [Module.Finite k N] :
    Module.Finite k (P ⟶ N) := by
  let _ : Module.Finite k (P ⟶ N.shiftObj 0) :=
    (GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj.{uA} P N).finiteDimensional 0
  let e0 : (P ⟶ N.shiftObj 0) ≃ₗ[k] (P ⟶ N) :=
    Linear.homCongr k (Iso.refl P) ((GradedModuleCat.shiftFunctorZeroIso 𝒜).app N)
  exact Module.Finite.equiv e0

/-- **Reading projective coordinates via degree-zero targets.** Let `bP` be a `ℤ[q,q⁻¹]`-basis of
`K₀^gr(proj A)` realized by degree-zero-generated projectives `Pᵢ`, and let `Sᵢ` be degree-zero
`k`-finite-dimensional modules with `Hom(Pᵢ, Sⱼ) = 0` for `i ≠ j`. Then
`gradedProjectiveHomGradedDimension (Sᵢ) x = dim_k Hom(Pᵢ, Sᵢ) · coordᵢ(x)`. -/
theorem gradedProjectiveHomGradedDimension_eq_mul_repr {I : Type uI}
    (P : I → (gradedFiniteProjectiveModules 𝒜).FullSubcategory)
    (hPgen : ∀ i, (P i).obj.grading.IsGeneratedInDegree A 0)
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (hbP : ∀ i, bP i = LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (P i))
    (S : I → GradedModuleCat.{uA} 𝒜) [∀ i, Module.Finite k (S i)]
    (hSconc : ∀ i p, p ≠ 0 → (S i).grading.piece p = ⊥)
    (horth : Pairwise fun i j ↦ Subsingleton ((P i).obj ⟶ S j))
    (x : LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)) (i : I) :
    gradedProjectiveHomGradedDimension (S i) x =
      C (Module.finrank k ((P i).obj ⟶ S i) : ℤ) * bP.repr x i := by
  classical
  conv_lhs => rw [← bP.linearCombination_repr x]
  rw [Finsupp.linearCombination_apply, map_finsuppSum,
    Finsupp.sum_eq_single i (fun j _ hji ↦ ?_) (by simp)]
  · rw [map_smul, hbP i,
      gradedProjectiveHomGradedDimension_of_isGeneratedInDegree_zero (S i) (hSconc i) (P i)
        (hPgen i), smul_eq_mul, mul_comm]
  · let _ := horth hji
    rw [map_smul, hbP j,
      gradedProjectiveHomGradedDimension_of_isGeneratedInDegree_zero (S i) (hSconc i) (P j)
        (hPgen j), Module.finrank_zero_of_subsingleton, Nat.cast_zero, map_zero, smul_zero]

end HomGradedDimension

/-! ### Graded Betti multiplicities via Hom and Ext -/

namespace GradedProjectiveResolution

section BettiMultiplicity

variable {I : Type uI}
  (P : I → (gradedFiniteProjectiveModules 𝒜).FullSubcategory)
  (hPgen : ∀ i, (P i).obj.grading.IsGeneratedInDegree A 0)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (P i))
  (S : I → GradedModuleCat.{uA} 𝒜) [∀ i, Module.Finite k (S i)]
  (hSconc : ∀ i p, p ≠ 0 → (S i).grading.piece p = ⊥)
  (horth : Pairwise fun i j ↦ Subsingleton ((P i).obj ⟶ S j))
  {M : GradedModuleCat.{uA} 𝒜}

include hPgen hbP hSconc horth in
/-- **The `n`th power-series coefficient of the Betti Poincaré series is the graded Hom dimension
out of `Pₙ`**, weighted by `dim_k Hom(Pᵢ, Sᵢ)`. -/
theorem finrank_mul_coeff_bettiPoincarePowerSeries
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ m, Module.Finite A (r.X m)] (i : I) (n : ℕ) :
    C (Module.finrank k ((P i).obj ⟶ S i) : ℤ) *
        PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i) =
      gradedDimension k (fun d : ℤ ↦ r.termObj n ⟶ (S i).shiftObj d)
        (GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj.{uA} (r.termObj n) (S i)) := by
  rw [coeff_bettiPoincarePowerSeries,
    ← gradedProjectiveHomGradedDimension_eq_mul_repr P hPgen bP hbP S hSconc horth,
    gradedProjectiveHomGradedDimension_of]
  rfl

include hPgen hbP hSconc horth in
/-- **Bigraded Betti coefficients as graded Hom dimensions.** The `(n, d)`-coefficient of
`r.bettiPoincarePowerSeries bP i` times `dim_k Hom(Pᵢ, Sᵢ)` equals `dim_k Hom(Pₙ, Sᵢ{d})`. -/
theorem finrank_mul_coeff_coeff_bettiPoincarePowerSeries
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ m, Module.Finite A (r.X m)] (i : I) (n : ℕ) (d : ℤ) :
    (Module.finrank k ((P i).obj ⟶ S i) : ℤ) *
        (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff d =
      Module.finrank k (r.termObj n ⟶ (S i).shiftObj d) := by
  have h := congrArg (fun p : LaurentPolynomial ℤ ↦ p.coeff d)
    (r.finrank_mul_coeff_bettiPoincarePowerSeries P hPgen bP hbP S hSconc horth i n)
  rwa [coeff_C_mul, coeff_gradedDimension] at h

include hPgen hbP hSconc horth in
/-- When `dim_k Hom(Pᵢ, Sᵢ) = 1`, the `(n, d)`-coefficient of the Betti Poincaré series is
literally `dim_k Hom(Pₙ, Sᵢ{d})`. -/
theorem coeff_coeff_bettiPoincarePowerSeries_of_finrank_eq_one
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ m, Module.Finite A (r.X m)] (i : I)
    (hsplit : Module.finrank k ((P i).obj ⟶ S i) = 1) (n : ℕ) (d : ℤ) :
    (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff d =
      Module.finrank k (r.termObj n ⟶ (S i).shiftObj d) := by
  simpa only [hsplit, Nat.cast_one, one_mul] using
    r.finrank_mul_coeff_coeff_bettiPoincarePowerSeries P hPgen bP hbP S hSconc horth i n d

include hPgen hbP hSconc horth in
/-- Every bigraded coefficient of `r.bettiPoincarePowerSeries bP i` is nonnegative whenever
`Hom(Pᵢ, Sᵢ)` is nontrivial. -/
theorem coeff_coeff_bettiPoincarePowerSeries_nonneg
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ m, Module.Finite A (r.X m)] (i : I) [Nontrivial ((P i).obj ⟶ S i)] (n : ℕ) (d : ℤ) :
    0 ≤ (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff d := by
  let _ := GradedModuleCat.moduleFinite_hom_of_moduleFinite_left (P i).obj (S i)
  have hpos : (0 : ℤ) < Module.finrank k ((P i).obj ⟶ S i) :=
    Nat.cast_pos.mpr (Module.finrank_pos (R := k))
  have hmul : 0 ≤ (Module.finrank k ((P i).obj ⟶ S i) : ℤ) *
      (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff d := by
    rw [r.finrank_mul_coeff_coeff_bettiPoincarePowerSeries P hPgen bP hbP S hSconc horth i n d]
    exact Nat.cast_nonneg _
  rcases mul_nonneg_iff.mp hmul with ⟨_, hb⟩ | ⟨ha, _⟩
  · exact hb
  · omega

include hPgen hbP hSconc horth in
/-- When `Hom(Pᵢ, Sᵢ)` is nontrivial, the `(n, d)`-coefficient of `r.bettiPoincarePowerSeries bP i`
vanishes if and only if `Hom(Pₙ, Sᵢ{d})` is a subsingleton. -/
theorem coeff_coeff_bettiPoincarePowerSeries_eq_zero_iff_subsingleton_hom
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ m, Module.Finite A (r.X m)] (i : I) [Nontrivial ((P i).obj ⟶ S i)] (n : ℕ) (d : ℤ) :
    (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff d = 0 ↔
      Subsingleton (r.termObj n ⟶ (S i).shiftObj d) := by
  let _ := GradedModuleCat.moduleFinite_hom_of_moduleFinite_left (P i).obj (S i)
  let _ := (GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj.{uA}
    (r.termObj n) (S i)).finiteDimensional d
  have hne : (Module.finrank k ((P i).obj ⟶ S i) : ℤ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos (R := k)).ne'
  rw [← mul_eq_zero_iff_left hne,
    r.finrank_mul_coeff_coeff_bettiPoincarePowerSeries P hPgen bP hbP S hSconc horth i n d,
    Nat.cast_eq_zero, Module.finrank_zero_iff]

include hPgen hbP hSconc horth in
/-- **Bigraded Betti coefficients of a minimal resolution compute graded Ext.** For a minimal
graded projective resolution `r` of `M`, `dim_k Hom(Pᵢ, Sᵢ)` times the `(n, d)`-coefficient of
`r.bettiPoincarePowerSeries bP i` equals `dim_k Extⁿ(M, Sᵢ{d})`. -/
theorem IsMinimal.finrank_mul_coeff_coeff_bettiPoincarePowerSeries
    [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ m, Module.Finite A (r.X m)] (hr : r.IsMinimal) (i : I) (n : ℕ) (d : ℤ) :
    (Module.finrank k ((P i).obj ⟶ S i) : ℤ) *
        (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff d =
      Module.finrank k (Ext.{uA} M ((S i).shiftObj d) n) := by
  have hpos : (⨆ (m : ℤ) (_ : 0 < m), 𝒜 m) • (⊤ : Submodule k ((S i).shiftObj d)) = ⊥ :=
    GradedModuleCat.positive_smul_top_eq_bot_of_concentrated ((S i).shiftObj d) d fun q hq ↦ by
      simpa [sub_eq_add_neg] using hSconc i (q - d) (sub_ne_zero.mpr hq)
  rw [r.finrank_mul_coeff_coeff_bettiPoincarePowerSeries P hPgen bP hbP S hSconc horth i n d,
    (hr.extLinearEquiv hpos n).finrank_eq]

include hPgen hbP hSconc horth in
/-- Over a splitting field (`dim_k Hom(Pᵢ, Sᵢ) = 1`), the `(n, d)`-coefficient of a minimal
resolution's Betti Poincaré series is `dim_k Extⁿ(M, Sᵢ{d})`. -/
theorem IsMinimal.coeff_coeff_bettiPoincarePowerSeries_eq_finrank_ext
    [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ m, Module.Finite A (r.X m)] (hr : r.IsMinimal) (i : I)
    (hsplit : Module.finrank k ((P i).obj ⟶ S i) = 1) (n : ℕ) (d : ℤ) :
    (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff d =
      Module.finrank k (Ext.{uA} M ((S i).shiftObj d) n) := by
  simpa only [hsplit, Nat.cast_one, one_mul] using
    hr.finrank_mul_coeff_coeff_bettiPoincarePowerSeries P hPgen bP hbP S hSconc horth i n d

include hPgen hbP hSconc horth in
/-- **Lower-triangularity of the Betti Poincaré series of a minimal resolution.** Over a
nonnegatively graded algebra, if `M` vanishes below degree `c`, then `[qᵈ][tⁿ] B_M(q, t)_i = 0`
for all `d < c + n`. -/
theorem IsMinimal.coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_lt
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ m, Module.Finite A (r.X m)] (hneg : ∀ p < 0, 𝒜 p = ⊥) (hr : r.IsMinimal)
    {c : ℤ} (hM : ∀ p < c, M.grading.piece p = ⊥)
    (i : I) [Nontrivial ((P i).obj ⟶ S i)] (n : ℕ) {d : ℤ} (hd : d < c + n) :
    (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff d = 0 := by
  rw [r.coeff_coeff_bettiPoincarePowerSeries_eq_zero_iff_subsingleton_hom
    P hPgen bP hbP S hSconc horth i n d]
  refine subsingleton_of_forall_eq 0 fun f ↦ GradedModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  change f.hom x = 0
  induction x using DirectSum.Decomposition.inductionOn (r.grading n).piece with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | @homogeneous p x =>
      by_cases hp : p < c + n
      · have hx0 : (x : r.X n) = 0 := by
          simpa only [hr.piece_eq_bot_of_lt_of_moduleFinite hneg hM n hp,
            Submodule.mem_bot] using x.property
        simp [hx0]
      · have hfx := GradedModuleCat.map_mem f x.property
        rw [GradedModuleCat.mem_shiftObj_piece_iff, hSconc i (p - d) (by omega),
          Submodule.mem_bot] at hfx
        exact hfx

include hPgen hbP hSconc horth in
/-- **Existence of the Alexander-graded Euler power series.** For a minimal graded projective
resolution of a module `M` vanishing in negative degrees over a nonnegatively graded algebra, each
coordinate `r.bettiPoincarePowerSeries bP i` satisfies `Bigraded.HasEulerPowerSeries`. -/
theorem IsMinimal.hasEulerPowerSeries_bettiPoincarePowerSeries
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ m, Module.Finite A (r.X m)] (hneg : ∀ p < 0, 𝒜 p = ⊥) (hr : r.IsMinimal)
    (hM : ∀ p < 0, M.grading.piece p = ⊥) (i : I) [Nontrivial ((P i).obj ⟶ S i)] :
    Bigraded.HasEulerPowerSeries (r.bettiPoincarePowerSeries bP i) :=
  Bigraded.HasEulerPowerSeries.of_lowerTriangular fun n d hd ↦
    hr.coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_lt P hPgen bP hbP S hSconc horth hneg hM
      i n (by omega : d < 0 + n)

end BettiMultiplicity

/-! ### Diagonal support and linear resolutions -/

section Linearity

variable {I : Type uI}
  (P : I → (gradedFiniteProjectiveModules 𝒜).FullSubcategory)
  (hPgen : ∀ i, (P i).obj.grading.IsGeneratedInDegree A 0)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (P i))

include hPgen hbP in
/-- **A linear resolution has diagonally supported Betti Poincaré series.** Neither a nonnegative
algebra grading nor semisimplicity is required for the forward implication. -/
theorem IsLinear.coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_ne
    (S : I → GradedModuleCat.{uA} 𝒜) [∀ i, Module.Finite k (S i)]
    (hSconc : ∀ i p, p ≠ 0 → (S i).grading.piece p = ⊥)
    (horth : Pairwise fun i j ↦ Subsingleton ((P i).obj ⟶ S j))
    {M : GradedModuleCat.{uA} 𝒜}
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ m, Module.Finite A (r.X m)] (hr : r.IsLinear)
    (i : I) [Nontrivial ((P i).obj ⟶ S i)] (n : ℕ) (d : ℤ) (hnd : (n : ℤ) ≠ d) :
    (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff d = 0 := by
  rw [r.coeff_coeff_bettiPoincarePowerSeries_eq_zero_iff_subsingleton_hom
    P hPgen bP hbP S hSconc horth i n d]
  refine subsingleton_of_forall_eq 0 (hr.hom_eq_zero n ?_)
  simpa [sub_eq_add_neg] using hSconc i ((n : ℤ) - d) (sub_ne_zero.mpr hnd)

include hPgen hbP in
/-- **Diagonal support of the Betti Poincaré series detects linear resolutions.** Over a
nonnegatively graded algebra with `dim_k A₀ < ∞`, let `S` be an exhaustive family of
`k`-finite-dimensional degree-zero simple modules paired against degree-zero-generated basis
projectives `Pᵢ` with `Hom(Pᵢ, Sⱼ) = 0` for `i ≠ j` and `Hom(Pᵢ, Sᵢ) ≠ 0`. Then a resolution `r`
with finitely generated projective terms is linear if and only if every Betti Poincaré coordinate
`r.bettiPoincarePowerSeries bP i` vanishes off the diagonal `d = n`. -/
theorem isLinear_iff_diagonal_bettiPoincarePowerSeries [Module.Finite k (𝒜 0)]
    (S : I → (gradedFiniteModules 𝒜).FullSubcategory) [∀ i, Module.Finite k (S i).obj]
    (hS : IsExhaustiveGradedSimpleFamily S)
    (hSconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (horth : Pairwise fun i j ↦ Subsingleton ((P i).obj ⟶ (S j).obj))
    (hself : ∀ i, Nontrivial ((P i).obj ⟶ (S i).obj))
    (hneg : ∀ p < 0, 𝒜 p = ⊥) {M : GradedModuleCat.{uA} 𝒜}
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ m, Module.Finite A (r.X m)] :
    r.IsLinear ↔ ∀ i (n : ℕ) (d : ℤ), (n : ℤ) ≠ d →
      (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff d = 0 := by
  refine ⟨fun hr i n d hnd ↦ ?_, fun hdiag ↦ ?_⟩
  · let _ := hself i
    exact hr.coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_ne P hPgen bP hbP
      (fun j ↦ (S j).obj) hSconc horth i n d hnd
  · refine (isLinear_iff_piece_le_positive_smul_top_of_moduleFinite hneg).mpr fun n d hdn ↦ ?_
    have : Module.Finite A (r.termObj n) := inferInstanceAs (Module.Finite A (r.X n))
    have : Module.Finite k ((r.termObj n).degreeQuotient d) :=
      (r.termObj n).moduleFinite_degreeQuotient (k := k) d
    have hQ : IsZero ((r.termObj n).degreeQuotient d) := by
      by_contra hQ
      obtain ⟨N, q, _, hsN, hq⟩ := ((r.termObj n).degreeQuotient d).exists_simple_quotient hQ
      have : Epi q := hq
      have : Simple N := hsN
      have : Epi ((r.termObj n).degreeQuotientπ d) :=
        (GradedModuleCat.epi_iff_surjective _).mpr ((r.termObj n).degreeQuotientπ_surjective d)
      have hNfinA : Module.Finite A N := Module.Finite.of_surjective
        (((r.termObj n).degreeQuotientπ d ≫ q).hom)
        ((GradedModuleCat.epi_iff_surjective _).mp inferInstance)
      have hNd (p : ℤ) (hp : p ≠ d) : N.grading.piece p = ⊥ :=
        GradedModuleCat.piece_eq_bot_of_surjective q
          ((GradedModuleCat.epi_iff_surjective q).mp hq) p
          ((r.termObj n).degreeQuotient_piece_eq_bot hp)
      have : Simple (((GradedModuleCat.shift 𝒜) ^ (-d)).functor.obj N) := simple_obj _ N
      have hsN' : Simple (N.shiftObj (-d)) :=
        Simple.of_iso ((GradedModuleCat.shiftPowIso 𝒜 (-d)).app N).symm
      have hN'0 (p : ℤ) (hp : p ≠ 0) : (N.shiftObj (-d)).grading.piece p = ⊥ := by
        simpa [sub_eq_add_neg] using hNd (p + d) (by omega)
      obtain ⟨i, ⟨eN⟩⟩ := hS.exists_iso_of_concentrated S hSconc
        ⟨N.shiftObj (-d), gradedFiniteModules_shiftObj (gradedFiniteModules_iff.mpr hNfinA) (-d)⟩
        hsN' hN'0
      let isoN : N ≅ (S i).obj.shiftObj d :=
        ((GradedModuleCat.shiftFunctorZeroIso 𝒜).app N).symm ≪≫
          eqToIso (congrArg N.shiftObj (by omega : 0 = -d + d)) ≪≫
          ((GradedModuleCat.shiftFunctorAddIso 𝒜 (-d) d).app N).symm ≪≫
          (GradedModuleCat.shiftFunctor (𝒜 := 𝒜) d).mapIso eN
      let _ := hself i
      have hHom : Subsingleton (r.termObj n ⟶ (S i).obj.shiftObj d) :=
        (r.coeff_coeff_bettiPoincarePowerSeries_eq_zero_iff_subsingleton_hom
          P hPgen bP hbP (fun j ↦ (S j).obj) hSconc horth i n d).mp (hdiag i n d hdn.symm)
      exact Simple.not_isZero N (IsZero.of_iso (IsZero.of_epi_eq_zero
        ((r.termObj n).degreeQuotientπ d ≫ q ≫ isoN.hom) (hHom.elim _ 0)) isoN)
    exact (r.termObj n).piece_le_positive_smul_top_of_subsingleton_hom hneg d
      (subsingleton_of_forall_eq 0 fun f ↦ hQ.eq_of_tgt f 0)

include hPgen hbP in
/-- For a linear resolution, the `n`th power-series coefficient of `r.bettiPoincarePowerSeries bP i`
is a scalar multiple of the Laurent monomial `qⁿ = T n`. -/
theorem IsLinear.coeff_bettiPoincarePowerSeries_eq_C_mul_T
    (S : I → GradedModuleCat.{uA} 𝒜) [∀ i, Module.Finite k (S i)]
    (hSconc : ∀ i p, p ≠ 0 → (S i).grading.piece p = ⊥)
    (horth : Pairwise fun i j ↦ Subsingleton ((P i).obj ⟶ S j))
    {M : GradedModuleCat.{uA} 𝒜}
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ m, Module.Finite A (r.X m)] (hr : r.IsLinear)
    (i : I) [Nontrivial ((P i).obj ⟶ S i)] (n : ℕ) :
    PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i) =
      C ((PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff n) * T n := by
  ext d
  rw [← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with hnd
  · exact congrArg _ hnd.symm
  · exact hr.coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_ne
      P hPgen bP hbP S hSconc horth i n d hnd

include hPgen hbP in
/-- **Monomial characterization of linear resolutions.** Under the hypotheses of
`isLinear_iff_diagonal_bettiPoincarePowerSeries`, a resolution `r` is linear if and only if in
every homological degree `n` and coordinate `i`, the `tⁿ`-coefficient of
`r.bettiPoincarePowerSeries bP i` is an integer multiple of `qⁿ = T n`. -/
theorem isLinear_iff_exists_coeff_bettiPoincarePowerSeries_eq_C_mul_T [Module.Finite k (𝒜 0)]
    (S : I → (gradedFiniteModules 𝒜).FullSubcategory) [∀ i, Module.Finite k (S i).obj]
    (hS : IsExhaustiveGradedSimpleFamily S)
    (hSconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (horth : Pairwise fun i j ↦ Subsingleton ((P i).obj ⟶ (S j).obj))
    (hself : ∀ i, Nontrivial ((P i).obj ⟶ (S i).obj))
    (hneg : ∀ p < 0, 𝒜 p = ⊥) {M : GradedModuleCat.{uA} 𝒜}
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ m, Module.Finite A (r.X m)] :
    r.IsLinear ↔ ∀ i (n : ℕ), ∃ c : ℤ,
      PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i) = C c * T n := by
  refine ⟨fun hr i n ↦ ?_, fun h ↦
    (r.isLinear_iff_diagonal_bettiPoincarePowerSeries
      P hPgen bP hbP S hS hSconc horth hself hneg).mpr fun i n d hnd ↦ ?_⟩
  · let _ := hself i
    exact ⟨_, hr.coeff_bettiPoincarePowerSeries_eq_C_mul_T
      P hPgen bP hbP (fun j ↦ (S j).obj) hSconc horth i n⟩
  · obtain ⟨c, hc⟩ := h i n
    rw [hc, ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hnd.symm]

include hPgen hbP in
/-- **Euler-specialization criterion for linear resolutions.** For a minimal graded projective
resolution of a module `M` vanishing in negative degrees, `r` is linear if and only if for every
`i`, the Alexander-graded and Maslov-graded Euler formal power series of
`r.bettiPoincarePowerSeries bP i` coincide. -/
theorem IsMinimal.isLinear_iff_eulerPowerSeries_eq
    [Module.Finite k (𝒜 0)]
    (S : I → (gradedFiniteModules 𝒜).FullSubcategory) [∀ i, Module.Finite k (S i).obj]
    (hS : IsExhaustiveGradedSimpleFamily S)
    (hSconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (horth : Pairwise fun i j ↦ Subsingleton ((P i).obj ⟶ (S j).obj))
    (hself : ∀ i, Nontrivial ((P i).obj ⟶ (S i).obj))
    (hneg : ∀ p < 0, 𝒜 p = ⊥) {M : GradedModuleCat.{uA} 𝒜}
    (hM : ∀ p < 0, M.grading.piece p = ⊥)
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ m, Module.Finite A (r.X m)] (hr : r.IsMinimal) :
    r.IsLinear ↔ ∀ i,
      Bigraded.eulerPowerSeries
          (letI := hself i;
            hr.hasEulerPowerSeries_bettiPoincarePowerSeries
              P hPgen bP hbP (fun j ↦ (S j).obj) hSconc horth hneg hM i) =
        Bigraded.maslovEulerPowerSeries (r.bettiPoincarePowerSeries bP i) := by
  rw [r.isLinear_iff_diagonal_bettiPoincarePowerSeries P hPgen bP hbP S hS hSconc horth hself hneg]
  refine forall_congr' fun i ↦ ?_
  let _ := hself i
  exact (Bigraded.eulerPowerSeries_eq_maslovEulerPowerSeries_iff
    (hr.hasEulerPowerSeries_bettiPoincarePowerSeries
      P hPgen bP hbP (fun j ↦ (S j).obj) hSconc horth hneg hM i)
    (r.coeff_coeff_bettiPoincarePowerSeries_nonneg
      P hPgen bP hbP (fun j ↦ (S j).obj) hSconc horth i)
    (fun n d hd ↦ hr.coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_lt
      P hPgen bP hbP (fun j ↦ (S j).obj) hSconc horth hneg hM i n (by omega : d < 0 + n))).symm

end Linearity

end GradedProjectiveResolution

/-! ### Matrix-level diagonal criterion and idempotent projective bases -/

section MatrixLinearity

variable {I : Type uI} {J : Type uJ} [Module.Finite k (𝒜 0)]
  (P : I → (gradedFiniteProjectiveModules 𝒜).FullSubcategory)
  (hPgen : ∀ i, (P i).obj.grading.IsGeneratedInDegree A 0)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (P i))
  (S : I → (gradedFiniteModules 𝒜).FullSubcategory) [∀ i, Module.Finite k (S i).obj]
  (hS : IsExhaustiveGradedSimpleFamily S)
  (hSconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
  (horth : Pairwise fun i j ↦ Subsingleton ((P i).obj ⟶ (S j).obj))
  (hself : ∀ i, Nontrivial ((P i).obj ⟶ (S i).obj))

include hPgen hbP hS hSconc horth hself in
/-- **A family of resolutions is simultaneously linear if and only if its Betti Poincaré matrix is
diagonally supported.** In particular, when `M j = (S j).obj` is an exhaustive degree-zero simple
family, diagonal support of `bettiPoincarePowerSeriesMatrix bP r` characterizes Koszulity of the
chosen resolutions. -/
theorem forall_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix
    (hneg : ∀ p < 0, 𝒜 p = ⊥) {M : J → GradedModuleCat.{uA} 𝒜}
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j m, Module.Finite A ((r j).X m)] :
    (∀ j, (r j).IsLinear) ↔
      ∀ i j (n : ℕ) (d : ℤ), (n : ℤ) ≠ d →
        (PowerSeries.coeff n (bettiPoincarePowerSeriesMatrix bP r i j)).coeff d = 0 := by
  simp only [bettiPoincarePowerSeriesMatrix_apply,
    GradedProjectiveResolution.isLinear_iff_diagonal_bettiPoincarePowerSeries
      P hPgen bP hbP S hS hSconc horth hself hneg]
  exact ⟨fun h i j n d hnd ↦ h j i n d hnd, fun h j i n d hnd ↦ h i j n d hnd⟩

end MatrixLinearity

section IdempotentBasis

omit [Field k] in
/-- For a homogeneous element `e ∈ 𝒜 p` generating a homogeneous left ideal `Ae`, the graded module
`ofIdeal 𝒜 (Ideal.span {e}) hI` is generated in degree `p`. -/
theorem GradedModuleCat.isGeneratedInDegree_ofIdeal_span_singleton
    {k₀ : Type*} [CommRing k₀] {B : Type*} [Ring B] [Algebra k₀ B]
    {ℬ : ℤ → Submodule k₀ B} [GradedAlgebra ℬ] {e : B} {p : ℤ} (he : e ∈ ℬ p)
    (hI : (Ideal.span {e} : Ideal B).IsHomogeneous ℬ) :
    (GradedModuleCat.ofIdeal ℬ (Ideal.span {e}) hI).grading.IsGeneratedInDegree B p := by
  rw [InternalGrading.isGeneratedInDegree_iff]
  intro x
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp x.2
  let g : (Ideal.span {e} : Ideal B) := ⟨e, Ideal.mem_span_singleton_self e⟩
  have hx : x = a • g := Subtype.ext (by simpa [g, smul_eq_mul] using ha.symm)
  rw [hx]
  exact Submodule.smul_mem _ a (Submodule.subset_span
    ((GradedModuleCat.mem_ofIdeal_piece_iff hI).mpr he))

variable {I : Type uI} {J : Type uJ} [Module.Finite k (𝒜 0)]
  (S : I → (gradedFiniteModules 𝒜).FullSubcategory) [∀ i, Module.Finite k (S i).obj]
  {e : I → A} (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hne : Pairwise fun i j ↦ (S j).obj.smulGradedDimension (e i) = 0)
  (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0)
  (hS : IsExhaustiveGradedSimpleFamily S)
  (hSconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)

include he₀ hne hself hS hSconc hbP in
/-- **Diagonal-support linearity criterion in an idempotent projective basis `[A eᵢ]`.** Over any
nonnegatively graded algebra with `dim_k A₀ < ∞` (not necessarily finite-dimensional over `k`), a
family of resolutions with finitely generated projective terms is simultaneously linear if and only
if its Betti Poincaré matrix in `[A eᵢ]` is diagonally supported. -/
theorem forall_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix_of_ofIdeal_span_singleton
    (hneg : ∀ p < 0, 𝒜 p = ⊥) {M : J → GradedModuleCat.{uA} 𝒜}
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j m, Module.Finite A ((r j).X m)] :
    (∀ j, (r j).IsLinear) ↔
      ∀ i j (n : ℕ) (d : ℤ), (n : ℤ) ≠ d →
        (PowerSeries.coeff n (bettiPoincarePowerSeriesMatrix bP r i j)).coeff d = 0 := by
  have horth : Pairwise fun i j ↦
      Subsingleton (GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i) ⟶ (S j).obj) :=
    fun i j hij ↦ by
      have h0 : Module.finrank k ↥(e i • (S j).obj.grading.piece 0) = 0 := by
        simpa [GradedModuleCat.coeff_smulGradedDimension] using
          congrArg (fun q : LaurentPolynomial ℤ ↦ q.coeff 0) (hne hij)
      have : Subsingleton ↥(e i • (S j).obj.grading.piece 0) :=
        (Module.finrank_zero_iff (R := k)).mp h0
      exact (GradedModuleCat.ofIdealSpanSingletonHomEquiv (he i) (he₀ i) (hI i)
        (S j).obj).toEquiv.subsingleton
  have hnt : ∀ i,
      Nontrivial (GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i) ⟶ (S i).obj) := fun i ↦ by
    have hpos := GradedModuleCat.finrank_smul_piece_zero_pos_of_concentrated (e i) (S i).obj
      (hSconc i) (hself i)
    have : Nontrivial ↥(e i • (S i).obj.grading.piece 0) :=
      Module.nontrivial_of_finrank_pos hpos
    exact (GradedModuleCat.ofIdealSpanSingletonHomEquiv (he i) (he₀ i) (hI i)
      (S i).obj).toEquiv.nontrivial
  exact forall_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix
    (fun i ↦ ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)
    (fun i ↦ GradedModuleCat.isGeneratedInDegree_ofIdeal_span_singleton (he₀ i) (hI i))
    bP hbP S hS hSconc horth hnt hneg r

namespace GradedProjectiveResolution

include he₀ hne hself hS hSconc hbP in
/-- Single-resolution form of
`forall_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix_of_ofIdeal_span_singleton`. -/
theorem isLinear_iff_diagonal_bettiPoincarePowerSeries_of_ofIdeal_span_singleton
    (hneg : ∀ p < 0, 𝒜 p = ⊥) {M : GradedModuleCat.{uA} 𝒜}
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ m, Module.Finite A (r.X m)] :
    r.IsLinear ↔
      ∀ i (n : ℕ) (d : ℤ), (n : ℤ) ≠ d →
        (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff d = 0 := by
  simpa using
    forall_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix_of_ofIdeal_span_singleton
      S he he₀ hI hne hself hS hSconc bP hbP hneg (M := fun _ : Unit ↦ M) (fun _ ↦ r)

end GradedProjectiveResolution

end IdempotentBasis

end TauCeti
