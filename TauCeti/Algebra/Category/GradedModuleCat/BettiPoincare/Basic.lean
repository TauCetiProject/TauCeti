/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.RingTheory.PowerSeries.Trunc
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ForgetGrading
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.ProjectiveCoordinates
public import TauCeti.Algebra.Category.GradedModuleCat.MinimalResolution

/-!
# The Betti Poincaré series of a graded projective resolution

Let `A` be a `ℤ`-graded `k`-algebra and let `bP` be a `ℤ[q,q⁻¹]`-basis of the graded projective
Grothendieck group `K₀^gr(proj A)`. Given a concrete graded projective resolution `r` of a graded
module `M` whose terms are finitely generated over `A`, each resolution term
`r.finiteProjectiveTerm n` defines a class `[Pₙ] ∈ K₀^gr(proj A)`. Expanding `[Pₙ]` in `bP`
packages the graded Betti numbers of `r` into a formal power series in homological degree `t` with
Laurent-polynomial internal coefficients:

```text
B_i(M; q, t) = ∑_{n ≥ 0} coord_i([Pₙ]) tⁿ ∈ (ℤ[q, q⁻¹])⟦t⟧.
```

For a family of graded modules `M : J → GradedModuleCat 𝒜` equipped with chosen resolutions, these
series assemble into the `I × J` matrix `TauCeti.bettiPoincarePowerSeriesMatrix`, whose `j`th column
records the projective coordinates of the resolution of `M j`.

When `r` is minimal and bounded below (automatic for finitely generated terms over a nonnegatively
graded algebra), uniqueness of minimal graded projective resolutions up to termwise graded
isomorphism shows that `B_i(M; q, t)` depends only on `M` and `bP`, not on the choice of minimal
resolution. Shifting `M` to `M{d}` multiplies the series by `qᵈ`, and specializing `q = 1` via
`TauCeti.laurentEval` sums the internal graded Betti numbers in each homological degree to recover
the ungraded `K₀(proj A)` expansion of `[Pₙ]`.

No homological vanishing bound or evaluation at `t = -1` is assumed here: infinite resolutions
produce genuine formal power series.

## Main definitions

* `TauCeti.GradedProjectiveResolution.bettiPoincarePowerSeries`: the `i`th Betti Poincaré formal
  power series of a finite-term graded projective resolution relative to a projective basis `bP`.
* `TauCeti.GradedProjectiveResolution.ofShortExact`: the two-term graded projective resolution
  attached to a short exact sequence `0 ⟶ P₁ ⟶ P₀ ⟶ M ⟶ 0` with projective `P₀, P₁`.
* `TauCeti.bettiPoincarePowerSeriesMatrix`: the `I × J` matrix of Betti Poincaré power series for a
  family of resolved graded modules.

## Main results

* `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincarePowerSeries_eq_of_boundedBelow` and
  `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincarePowerSeries_eq`: independence of the
  chosen minimal resolution.
* `TauCeti.GradedProjectiveResolution.bettiPoincarePowerSeries_shiftObj` and
  `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincarePowerSeries_shiftObj_eq`: shifting `M`
  by `d` multiplies the Betti Poincaré series by `qᵈ`.
* `TauCeti.GradedProjectiveResolution.bettiPoincarePowerSeries_ofShortExact`: explicit linear-in-`t`
  formula `coord_i([P₀]) + coord_i([P₁]) t` for a two-term resolution.
* `TauCeti.bettiPoincarePowerSeriesMatrix_basis_change`: changing the projective basis multiplies
  the Betti Poincaré matrix on the left by the transition matrix.
* `TauCeti.GradedProjectiveResolution.exactK0_forget_finiteProjectiveTerm_eq_sum_laurentEval_one`:
  setting `q = 1` recovers the ungraded `K₀(proj A)` expansion of each resolution term.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Sections 1.2 and 2.11, for graded Poincaré series and minimal resolutions.
* D. Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*, Section 19.1, for
  graded Betti numbers from minimal free and projective resolutions.
* Z. Dancso and A. Licata, "Koszul algebras and flow lattices", Section 2.2, for the Laurent
  Grothendieck group conventions and specialization at `q = 1`.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits LaurentPolynomial

universe uk uA uI uI' uJ

section General

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} {I : Type uI} {I' : Type uI'} {J : Type uJ}

namespace GradedProjectiveResolution

section SingleResolution

variable {M : GradedModuleCat.{uA} 𝒜}
  (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
  [∀ n, Module.Finite A (r.X n)]
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))

/-- Shifting a resolution `r` to `M{d}` shifts its `n`th finite graded projective term by `d`. -/
@[simp]
theorem shiftObj_finiteProjectiveTerm (d : ℤ) (n : ℕ) :
    (r.shiftObj d).finiteProjectiveTerm n =
      ⟨(r.finiteProjectiveTerm n).obj.shiftObj d,
        gradedFiniteProjectiveModules_shiftObj (r.finiteProjectiveTerm n).property d⟩ := by
  have hobj : ((r.shiftObj d).finiteProjectiveTerm n).obj =
      (r.finiteProjectiveTerm n).obj.shiftObj d := by
    rw [finiteProjectiveTerm_obj, shiftObj_termObj, finiteProjectiveTerm_obj]
  rcases h : (r.shiftObj d).finiteProjectiveTerm n with ⟨obj, prop⟩
  rw [h] at hobj
  subst hobj
  rfl

/-- **The `i`th Betti Poincaré power series** of a finite-term graded projective resolution `r`
with respect to a basis `bP` of `K₀^gr(proj A)`. Its coefficient at `tⁿ` is the `i`th Laurent
coordinate of `[Pₙ]`, and the coefficient of `qᵈ tⁿ` is the `(n, d)` graded Betti multiplicity in
projective coordinate `i`. -/
def bettiPoincarePowerSeries (i : I) : PowerSeries (LaurentPolynomial ℤ) :=
  PowerSeries.mk fun n ↦
    bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
      (r.finiteProjectiveTerm n)) i

/-- The coefficient of `tⁿ` in `r.bettiPoincarePowerSeries bP i` is the `i`th projective basis
coordinate of the `n`th resolution term. -/
@[simp]
theorem coeff_bettiPoincarePowerSeries (i : I) (n : ℕ) :
    PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i) =
      bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r.finiteProjectiveTerm n)) i := by
  simp [bettiPoincarePowerSeries]

/-- The constant term in homological degree `t⁰` is the projective coordinate of `P₀`. -/
@[simp]
theorem constantCoeff_bettiPoincarePowerSeries (i : I) :
    PowerSeries.constantCoeff (r.bettiPoincarePowerSeries bP i) =
      bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r.finiteProjectiveTerm 0)) i := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_bettiPoincarePowerSeries]

/-- The `(n, d)` bidegree coefficient is the coefficient of `qᵈ` in the `i`th coordinate of
`[Pₙ]`. -/
theorem coeff_coeff_bettiPoincarePowerSeries (i : I) (n : ℕ) (d : ℤ) :
    (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff d =
      (bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r.finiteProjectiveTerm n)) i).coeff d := by
  rw [coeff_bettiPoincarePowerSeries]

/-- Summing the `tⁿ`-coefficients of the Betti Poincaré series against `bP` reconstructs the class
of the `n`th resolution term in `K₀^gr(proj A)`. -/
theorem sum_coeff_bettiPoincarePowerSeries_smul [Fintype I] (n : ℕ) :
    ∑ i, PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i) • bP i =
      LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r.finiteProjectiveTerm n) := by
  simpa only [coeff_bettiPoincarePowerSeries] using
    bP.sum_repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
      (r.finiteProjectiveTerm n))

/-- **Internal shift law for the Betti Poincaré series.** Shifting the resolved module to `M{d}`
multiplies the Betti Poincaré series of its shifted resolution by `qᵈ`. -/
@[simp]
theorem bettiPoincarePowerSeries_shiftObj (d : ℤ) (i : I) :
    (r.shiftObj d).bettiPoincarePowerSeries bP i =
      PowerSeries.C (T d : LaurentPolynomial ℤ) * r.bettiPoincarePowerSeries bP i := by
  ext n
  rw [coeff_bettiPoincarePowerSeries, PowerSeries.coeff_C_mul, coeff_bettiPoincarePowerSeries,
    shiftObj_finiteProjectiveTerm, laurentK0_projective_of_shiftObj, map_smul, Finsupp.smul_apply,
    smul_eq_mul]

/-- Shifting by `1` multiplies the Betti Poincaré series by `q`. -/
theorem bettiPoincarePowerSeries_shiftObj_one (i : I) :
    (r.shiftObj 1).bettiPoincarePowerSeries bP i =
      PowerSeries.C (T 1 : LaurentPolynomial ℤ) * r.bettiPoincarePowerSeries bP i :=
  r.bettiPoincarePowerSeries_shiftObj bP 1 i

/-- Shifting `r` by `d` translates the internal degree index of every graded Betti number by `d`. -/
theorem coeff_coeff_bettiPoincarePowerSeries_shiftObj (d : ℤ) (i : I) (n : ℕ) (p : ℤ) :
    (PowerSeries.coeff n ((r.shiftObj d).bettiPoincarePowerSeries bP i)).coeff p =
      (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff (p - d) := by
  rw [bettiPoincarePowerSeries_shiftObj, PowerSeries.coeff_C_mul, T,
    AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff (p - d) (fun _ _ ↦ by omega), one_mul]

/-- If the resolution vanishes in homological degrees `≥ b`, its Betti Poincaré series equals its
polynomial truncation below `b`. -/
theorem bettiPoincarePowerSeries_eq_coe_trunc {b : ℕ}
    (hb : ∀ n ≥ b, Subsingleton (r.X n)) (i : I) :
    r.bettiPoincarePowerSeries bP i =
      (PowerSeries.trunc b (r.bettiPoincarePowerSeries bP i) :
        PowerSeries (LaurentPolynomial ℤ)) := by
  ext n
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hn
  · rfl
  · rw [coeff_bettiPoincarePowerSeries]
    have hsub : Subsingleton (r.finiteProjectiveTerm n).obj := by
      rw [r.finiteProjectiveTerm_obj n]
      exact hb n (Nat.le_of_not_gt hn)
    have hzero : IsZero (r.finiteProjectiveTerm n) :=
      (IsZero.iff_id_eq_zero _).2 <| ObjectProperty.hom_ext _ <|
        GradedModuleCat.hom_ext (LinearMap.ext fun _ ↦ hsub.elim _ _)
    rw [← LaurentK0.ofExactK0_exactK0_of.{uA}, ExactK0.of_eq_zero_of_isZero.{uA} hzero, map_zero,
      map_zero, Finsupp.zero_apply]

/-- Over a finite projective basis, all coordinates of `r.bettiPoincarePowerSeries bP` come from
polynomials in `t` if and only if the classes `[Pₙ]` vanish above some homological bound. -/
theorem forall_exists_polynomial_bettiPoincarePowerSeries_iff [Finite I] :
    (∀ i, ∃ p : Polynomial (LaurentPolynomial ℤ),
      (p : PowerSeries (LaurentPolynomial ℤ)) = r.bettiPoincarePowerSeries bP i) ↔
      ∃ b : ℕ, ∀ n ≥ b,
        LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
          (r.finiteProjectiveTerm n) = 0 := by
  classical
  cases nonempty_fintype I
  constructor
  · intro hp
    choose p hp using hp
    refine ⟨Finset.univ.sup (fun i ↦ (p i).natDegree) + 1, fun n hn ↦ ?_⟩
    rw [← r.sum_coeff_bettiPoincarePowerSeries_smul bP n]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hdeg : (p i).natDegree < n :=
      Nat.lt_of_le_of_lt (Finset.le_sup (f := fun i ↦ (p i).natDegree) (Finset.mem_univ i)) hn
    have hc : PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i) = 0 := by
      rw [← hp i, Polynomial.coeff_coe]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt hdeg
    rw [hc, zero_smul]
  · rintro ⟨b, hb⟩ i
    refine ⟨PowerSeries.trunc b (r.bettiPoincarePowerSeries bP i), ?_⟩
    ext n
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hn
    · rfl
    · rw [coeff_bettiPoincarePowerSeries, hb n (Nat.le_of_not_gt hn), map_zero,
        Finsupp.zero_apply]

/-- **Specialization at `q = 1`.** Evaluating the internal variable at `1` sums the internal
graded Betti coefficients in each homological degree `n`. -/
theorem coeff_map_laurentEval_one_bettiPoincarePowerSeries (i : I) (n : ℕ) :
    PowerSeries.coeff n
        (PowerSeries.map (laurentEval (R := ℤ) (1 : ℤˣ) : LaurentPolynomial ℤ →+* ℤ)
          (r.bettiPoincarePowerSeries bP i)) =
      ∑ d ∈ (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff.support,
        (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff d := by
  rw [PowerSeries.coeff_map]
  set f := PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)
  have hf : f = ∑ d ∈ f.coeff.support, C (f.coeff d) * T d := by
    ext d
    rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    simp_rw [← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hd : d ∈ f.coeff.support
    · simp [hd]
    · simp [hd, Finsupp.notMem_support_iff.mp hd]
  conv_lhs => rw [hf]
  simp

/-- For a diagonally supported Betti Poincaré series, setting `q = 1` retains the diagonal
coefficient `(n, n)` in each homological degree `n`. -/
theorem map_laurentEval_one_bettiPoincarePowerSeries_of_diagonal {i : I}
    (hdiag : ∀ (n : ℕ) (d : ℤ), (n : ℤ) ≠ d →
      (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff d = 0) :
    PowerSeries.map (laurentEval (R := ℤ) (1 : ℤˣ) : LaurentPolynomial ℤ →+* ℤ)
        (r.bettiPoincarePowerSeries bP i) =
      PowerSeries.mk fun n ↦ (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff n := by
  ext n
  rw [coeff_map_laurentEval_one_bettiPoincarePowerSeries, PowerSeries.coeff_mk]
  by_cases hmem : (n : ℤ) ∈ (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff.support
  · refine Finset.sum_eq_single (n : ℤ) (fun d _ hd ↦ hdiag n d hd.symm)
      (fun hn ↦ absurd hmem hn)
  · rw [Finset.sum_eq_zero]
    · exact (Finsupp.notMem_support_iff.mp hmem).symm
    · intro d hd
      have hne : (n : ℤ) ≠ d := fun h ↦ hmem (h ▸ hd)
      exact hdiag n d hne

/-- **Forgetting the grading on `[Pₙ]`.** Specializing `q = 1` in the Betti Poincaré series
computes the expansion of the ungraded projective class `[Pₙ] ∈ K₀(proj A)` along the images of
the graded basis vectors `bP i` under `TauCeti.gradedFiniteProjectiveModulesForgetK0`. -/
theorem exactK0_forget_finiteProjectiveTerm_eq_sum_laurentEval_one [Fintype I] (n : ℕ) :
    ExactK0.of.{uA}
        ((gradedFiniteProjectiveModulesForget 𝒜).obj (r.finiteProjectiveTerm n)) =
      ∑ i, PowerSeries.coeff n
          (PowerSeries.map (laurentEval (R := ℤ) (1 : ℤˣ) : LaurentPolynomial ℤ →+* ℤ)
            (r.bettiPoincarePowerSeries bP i)) •
        gradedFiniteProjectiveModulesForgetK0 𝒜 (LaurentSpecialization.mk 1 (bP i)) := by
  rw [← gradedFiniteProjectiveModulesForgetK0_mk_of,
    ← r.sum_coeff_bettiPoincarePowerSeries_smul bP n, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [LinearMap.map_smul, LaurentSpecialization.mk_smul, LinearMap.map_smul,
    PowerSeries.coeff_map]
  rfl

end SingleResolution

/-! ### Independence of the minimal resolution -/

section Uniqueness

variable {M : GradedModuleCat.{uA} 𝒜}
  {r₁ r₂ : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
  [∀ n, Module.Finite A (r₁.X n)] [∀ n, Module.Finite A (r₂.X n)]
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))

/-- **Uniqueness of the Betti Poincaré series for bounded-below minimal resolutions.** Any two
minimal resolutions of `M` whose terms are bounded below in internal degree define the same Betti
Poincaré power series in every projective coordinate. -/
theorem IsMinimal.bettiPoincarePowerSeries_eq_of_boundedBelow [DirectSum.Decomposition 𝒜]
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal)
    (b₁ b₂ : ℕ → ℤ) (hb₁ : ∀ n p, p < b₁ n → (r₁.grading n).piece p = ⊥)
    (hb₂ : ∀ n p, p < b₂ n → (r₂.grading n).piece p = ⊥) (i : I) :
    r₁.bettiPoincarePowerSeries bP i = r₂.bettiPoincarePowerSeries bP i := by
  ext n
  simp only [coeff_bettiPoincarePowerSeries]
  have e : r₁.finiteProjectiveTerm n ≅ r₂.finiteProjectiveTerm n :=
    ObjectProperty.isoMk _ (eqToIso (r₁.finiteProjectiveTerm_obj n) ≪≫
      hr₁.termObjIso hr₂ (b₁ n) (b₂ n) (hb₁ n) (hb₂ n) ≪≫
      (eqToIso (r₂.finiteProjectiveTerm_obj n)).symm)
  rw [LaurentK0.of_congr.{uA} _ e]

/-- **Uniqueness of the Betti Poincaré series over a nonnegatively graded algebra.** Finitely
generated resolution terms are automatically bounded below, so any two minimal resolutions of `M`
with finitely generated terms yield the same Betti Poincaré power series. -/
theorem IsMinimal.bettiPoincarePowerSeries_eq [GradedAlgebra 𝒜]
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal) (i : I) :
    r₁.bettiPoincarePowerSeries bP i = r₂.bettiPoincarePowerSeries bP i := by
  ext n
  simp only [coeff_bettiPoincarePowerSeries]
  have e : r₁.finiteProjectiveTerm n ≅ r₂.finiteProjectiveTerm n :=
    ObjectProperty.isoMk _ (eqToIso (r₁.finiteProjectiveTerm_obj n) ≪≫
      hr₁.termObjIsoOfModuleFinite hneg hr₂ n ≪≫
      (eqToIso (r₂.finiteProjectiveTerm_obj n)).symm)
  rw [LaurentK0.of_congr.{uA} _ e]

/-- **Resolution-independent shift law.** Over a nonnegatively graded algebra, the Betti Poincaré
series of any minimal resolution of `M{d}` with finitely generated terms equals `qᵈ` times that of
any minimal resolution of `M` with finitely generated terms. -/
theorem IsMinimal.bettiPoincarePowerSeries_shiftObj_eq [GradedAlgebra 𝒜]
    (hneg : ∀ p < 0, 𝒜 p = ⊥) {d : ℤ}
    {rM : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    {rShift : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M.shiftObj d).grading}
    [∀ n, Module.Finite A (rM.X n)] [∀ n, Module.Finite A (rShift.X n)]
    (hrM : rM.IsMinimal) (hrShift : rShift.IsMinimal) (i : I) :
    rShift.bettiPoincarePowerSeries bP i =
      PowerSeries.C (T d : LaurentPolynomial ℤ) * rM.bettiPoincarePowerSeries bP i := by
  rw [hrShift.bettiPoincarePowerSeries_eq bP hneg ((rM.isMinimal_shiftObj_iff d).2 hrM),
    rM.bettiPoincarePowerSeries_shiftObj bP d i]

end Uniqueness

/-! ### Two-term graded projective resolutions from short exact sequences -/

section ShortExact

variable {S : ShortComplex (GradedModuleCat.{uA} 𝒜)}

/-- Auxiliary zero graded module in `GradedModuleCat.{uA} 𝒜`, used for the vanishing tail of a
two-term graded projective resolution. -/
private abbrev zeroGradedObj (𝒜 : ℤ → Submodule k A) : GradedModuleCat.{uA} 𝒜 :=
  GradedModuleCat.directSumObj (Empty.elim : Empty → GradedModuleCat.{uA} 𝒜)

private instance subsingleton_zeroGradedObj : Subsingleton (zeroGradedObj.{uk, uA} 𝒜) :=
  ⟨fun _ _ ↦ DFinsupp.ext fun j ↦ j.elim⟩

private instance moduleProjective_zeroGradedObj :
    Module.Projective A (zeroGradedObj.{uk, uA} 𝒜) :=
  Module.Projective.of_lifting_property fun _ _ _ ↦
    ⟨0, LinearMap.ext fun x ↦ by
      rw [Subsingleton.elim x 0, LinearMap.comp_apply, LinearMap.zero_apply, map_zero, map_zero]⟩

private instance moduleFinite_zeroGradedObj : Module.Finite A (zeroGradedObj.{uk, uA} 𝒜) :=
  Module.Finite.of_surjective (0 : A →ₗ[A] zeroGradedObj.{uk, uA} 𝒜) fun x ↦
    ⟨0, Subsingleton.elim 0 x⟩

private abbrev shortExactTermObj (S : ShortComplex (GradedModuleCat.{uA} 𝒜)) :
    ℕ → GradedModuleCat.{uA} 𝒜
  | 0 => S.X₂
  | 1 => S.X₁
  | _ + 2 => zeroGradedObj.{uk, uA} 𝒜

/-- **Two-term graded projective resolution from a short exact sequence.** Given a short exact
sequence `0 ⟶ P₁ ⟶ P₀ ⟶ M ⟶ 0` in `GradedModuleCat 𝒜` whose first two objects have projective
underlying `A`-modules, this packages `P₀` in degree `0`, `P₁` in degree `1`, and `0` in degrees
`≥ 2` into a `GradedProjectiveResolution` of `M`. -/
def ofShortExact (hS : S.ShortExact) [Module.Projective A S.X₁] [Module.Projective A S.X₂] :
    GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 S.X₃.grading where
  X n := shortExactTermObj S n
  grading n := (shortExactTermObj S n).grading
  gradedSMul n := (shortExactTermObj S n).gradedSMul
  projective
    | 0 => inferInstanceAs (Module.Projective A S.X₂)
    | 1 => inferInstanceAs (Module.Projective A S.X₁)
    | _ + 2 => inferInstanceAs (Module.Projective A (zeroGradedObj.{uk, uA} 𝒜))
  d
    | 0 => S.f.hom
    | _ + 1 => 0
  π := S.g.hom
  isHomogeneous_d
    | 0 => S.f.isHomogeneous
    | _ + 1 => LinearMap.isHomogeneous_zero _ _ 0
  isHomogeneous_π := S.g.isHomogeneous
  surjective_π := (GradedModuleCat.epi_iff_surjective S.g).1 hS.epi_g
  exact_d_π := (GradedModuleCat.exact_iff (S := S)).1 hS.exact
  exact_d_d
    | 0 => fun x ↦
      ⟨fun hx ↦ ⟨0, by
        have hinj := (GradedModuleCat.mono_iff_injective S.f).1 hS.mono_f
        change (0 : zeroGradedObj.{uk, uA} 𝒜 →ₗ[A] S.X₁) 0 = x
        rw [LinearMap.zero_apply]
        exact ((injective_iff_map_eq_zero S.f.hom).1 hinj x hx).symm⟩,
       fun ⟨y, hy⟩ ↦ by
        change S.f.hom x = 0
        rw [← hy]
        exact map_zero S.f.hom⟩
    | _ + 1 => fun x ↦ ⟨fun _ ↦ ⟨0, Subsingleton.elim 0 x⟩, fun _ ↦ rfl⟩

instance moduleFinite_ofShortExact_X (hS : S.ShortExact)
    [Module.Projective A S.X₁] [Module.Projective A S.X₂]
    [Module.Finite A S.X₁] [Module.Finite A S.X₂] (n : ℕ) :
    Module.Finite A ((ofShortExact hS).X n) := by
  unfold ofShortExact
  match n with
  | 0 => exact inferInstanceAs (Module.Finite A S.X₂)
  | 1 => exact inferInstanceAs (Module.Finite A S.X₁)
  | _ + 2 => exact inferInstanceAs (Module.Finite A (zeroGradedObj.{uk, uA} 𝒜))

/-- A two-term graded projective resolution `ofShortExact hS` is minimal if and only if the first
map `P₁ ⟶ P₀` lands in `A₊ P₀`. -/
theorem isMinimal_ofShortExact_iff (hS : S.ShortExact)
    [Module.Projective A S.X₁] [Module.Projective A S.X₂] :
    (ofShortExact hS).IsMinimal ↔
      ∀ x : S.X₁, S.f.hom x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k S.X₂) := by
  rw [isMinimal_iff]
  refine ⟨fun h ↦ h 0, fun h n ↦ ?_⟩
  cases n with
  | zero => exact h
  | succ n =>
    unfold ofShortExact
    intro _
    simp

/-- A two-term graded projective resolution `ofShortExact hS` is linear if and only if `P₀` is
generated in degree `0` and `P₁` is generated in degree `1`. -/
theorem isLinear_ofShortExact_iff (hS : S.ShortExact)
    [Module.Projective A S.X₁] [Module.Projective A S.X₂] :
    (ofShortExact hS).IsLinear ↔
      S.X₂.grading.IsGeneratedInDegree A 0 ∧ S.X₁.grading.IsGeneratedInDegree A 1 := by
  rw [isLinear_iff]
  refine ⟨fun h ↦ ⟨h 0, h 1⟩, fun ⟨h0, h1⟩ n ↦ ?_⟩
  match n with
  | 0 => exact h0
  | 1 => exact h1
  | n + 2 =>
    change (zeroGradedObj.{uk, uA} 𝒜).grading.IsGeneratedInDegree A (n + 2 : ℕ)
    refine ((zeroGradedObj.{uk, uA} 𝒜).grading.isGeneratedInDegree_iff _).2 fun x ↦ ?_
    rw [Subsingleton.elim x 0]
    exact zero_mem _

/-- **Betti Poincaré series of a two-term resolution.** For a short exact sequence
`0 ⟶ P₁ ⟶ P₀ ⟶ M ⟶ 0` of finite graded modules with `P₀, P₁` projective, the `i`th Betti Poincaré
series of `ofShortExact hS` is `coord_i([P₀]) + coord_i([P₁]) t`. -/
theorem bettiPoincarePowerSeries_ofShortExact (hS : S.ShortExact)
    [Module.Projective A S.X₁] [Module.Projective A S.X₂]
    [Module.Finite A S.X₁] [Module.Finite A S.X₂]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))) (i : I) :
    (ofShortExact hS).bettiPoincarePowerSeries bP i =
      PowerSeries.C (bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
          ⟨S.X₂, gradedFiniteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩) i) +
        PowerSeries.C (bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
          ⟨S.X₁, gradedFiniteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩) i) *
          PowerSeries.X := by
  ext n
  match n with
  | 0 =>
    have h0 : (ofShortExact hS).finiteProjectiveTerm 0 =
        ⟨S.X₂, gradedFiniteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩ :=
      ObjectProperty.FullSubcategory.ext (((ofShortExact hS).finiteProjectiveTerm_obj 0).trans rfl)
    simp [h0]
  | 1 =>
    have h1 : (ofShortExact hS).finiteProjectiveTerm 1 =
        ⟨S.X₁, gradedFiniteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩ :=
      ObjectProperty.FullSubcategory.ext (((ofShortExact hS).finiteProjectiveTerm_obj 1).trans rfl)
    simp [h1]
  | n + 2 =>
    have hsub : Subsingleton ((ofShortExact hS).finiteProjectiveTerm (n + 2)).obj := by
      rw [(ofShortExact hS).finiteProjectiveTerm_obj (n + 2)]
      exact inferInstanceAs (Subsingleton (zeroGradedObj.{uk, uA} 𝒜))
    have hzero : IsZero ((ofShortExact hS).finiteProjectiveTerm (n + 2)) :=
      (IsZero.iff_id_eq_zero _).2 <| ObjectProperty.hom_ext _ <|
        GradedModuleCat.hom_ext (LinearMap.ext fun _ ↦ hsub.elim _ _)
    rw [coeff_bettiPoincarePowerSeries, ← LaurentK0.ofExactK0_exactK0_of.{uA},
      ExactK0.of_eq_zero_of_isZero.{uA} hzero, map_zero, map_zero, Finsupp.zero_apply]
    simp

end ShortExact

end GradedProjectiveResolution

/-! ### The matrix-valued Betti Poincaré series -/

/-- **The matrix-valued Betti Poincaré power series** of a family of graded modules `M : J → _`,
computed from chosen finite-term graded projective resolutions `r j` relative to a projective basis
`bP` indexed by `I`. Row `i` corresponds to `bP i` and column `j` to the resolved module `M j`. -/
def bettiPoincarePowerSeriesMatrix
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (M : J → GradedModuleCat.{uA} 𝒜)
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r j).X n)] :
    Matrix I J (PowerSeries (LaurentPolynomial ℤ)) :=
  Matrix.of fun i j ↦ (r j).bettiPoincarePowerSeries bP i

/-- Entry `(i, j)` of the Betti Poincaré matrix is the `i`th Betti Poincaré series of `r j`. -/
@[simp]
theorem bettiPoincarePowerSeriesMatrix_apply
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (M : J → GradedModuleCat.{uA} 𝒜)
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r j).X n)] (i : I) (j : J) :
    bettiPoincarePowerSeriesMatrix bP M r i j = (r j).bettiPoincarePowerSeries bP i :=
  (rfl)

/-- **Left change of projective basis.** Replacing `bP` by another basis `bP'` multiplies the Betti
Poincaré matrix on the left by the constant-power-series transition matrix `bP'.toMatrix bP`. -/
theorem bettiPoincarePowerSeriesMatrix_basis_change [Fintype I]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (bP' : Module.Basis I' (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (M : J → GradedModuleCat.{uA} 𝒜)
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r j).X n)] :
    bettiPoincarePowerSeriesMatrix bP' M r =
      Matrix.map (bP'.toMatrix bP) PowerSeries.C * bettiPoincarePowerSeriesMatrix bP M r := by
  refine Matrix.ext fun i' j ↦ PowerSeries.ext fun n ↦ ?_
  rw [bettiPoincarePowerSeriesMatrix_apply, Matrix.mul_apply, map_sum (PowerSeries.coeff n),
    GradedProjectiveResolution.coeff_bettiPoincarePowerSeries]
  conv_lhs =>
    rw [← bP.sum_repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
      ((r j).finiteProjectiveTerm n))]
  rw [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.map_apply, PowerSeries.coeff_C_mul, Module.Basis.toMatrix_apply,
    bettiPoincarePowerSeriesMatrix_apply,
    GradedProjectiveResolution.coeff_bettiPoincarePowerSeries, map_smul,
    Finsupp.smul_apply, smul_eq_mul, mul_comm]

/-- **Independence of minimal resolutions for the Betti Poincaré matrix.** Over a nonnegatively
graded algebra, any two families of finite-term minimal resolutions of `M` produce the same
matrix-valued Betti Poincaré series. -/
theorem bettiPoincarePowerSeriesMatrix_congr [GradedAlgebra 𝒜]
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (M : J → GradedModuleCat.{uA} 𝒜)
    (r₁ r₂ : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r₁ j).X n)] [∀ j n, Module.Finite A ((r₂ j).X n)]
    (hr₁ : ∀ j, (r₁ j).IsMinimal) (hr₂ : ∀ j, (r₂ j).IsMinimal) :
    bettiPoincarePowerSeriesMatrix bP M r₁ = bettiPoincarePowerSeriesMatrix bP M r₂ :=
  Matrix.ext fun i j ↦ (hr₁ j).bettiPoincarePowerSeries_eq bP hneg (hr₂ j) i

end General

end TauCeti
