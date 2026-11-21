/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Trunc
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Resolution
public import TauCeti.Algebra.Category.GradedModuleCat.MinimalResolution

/-!
# Matrix-valued Betti Poincaré series and finite Cartan–Betti identities

Let `𝒜` be a `ℤ`-graded `k`-algebra and let `bP` be a `ℤ[q,q⁻¹]`-basis of the graded projective
Grothendieck group `K₀^gr(proj A)` indexed by `I`. For any graded projective resolution `r` of a
graded `A`-module `M` whose terms `r.X n` are finitely generated `A`-modules, the **`i`-th Betti
Poincaré series** of `r` is the formal power series

```text
Bᵢ(r; q, t) = ∑_{n ≥ 0} (bP.repr [Pₙ] i) tⁿ ∈ (ℤ[q,q⁻¹])⟦t⟧,
```

recording simultaneously the homological degree `t` and the internal shift `q` of every projective
summand in `Pₙ`. Given a family of resolutions `r j` of modules `M j`, these entries assemble into
the **Betti Poincaré matrix** `bettiPoincareMatrix bP r` with rows indexed by the projective basis
`I` and columns indexed by the resolved family `J`.

This file develops the basis-generic, Ext-free part of the theory:

1. **Shift law**: shifting a resolution to `M{d}` multiplies its Betti Poincaré series by `qᵈ`
   (`GradedProjectiveResolution.bettiPoincareSeries_shiftObj`).
2. **Independence of minimal resolution**: over a direct-sum grading, any two bounded-below minimal
   resolutions of `M` (in particular, over a nonnegatively graded algebra, any two minimal
   resolutions with finitely generated terms) have the same Betti Poincaré series
   (`GradedProjectiveResolution.IsMinimal.bettiPoincareSeries_eq` and
   `IsMinimal.bettiPoincareSeries_shiftObj_eq`).
3. **Finite-resolution Cartan–Betti identity**: using the alternating resolution class formula
   `GradedProjectiveResolution.laurentK0_eq_gradedCartanMap_sum`, in any module basis `bM` of
   resolved classes, evaluating the truncated Betti matrix at `t = -1` gives `C(q) · B(q, -1) = I`
   (`gradedCartanMatrix_mul_eval_neg_one_trunc_bettiPoincareMatrix_eq_one`), and when every finite
   graded module admits a finite projective resolution it equals the matrix of
   `gradedCartanInverse` (`eval_neg_one_trunc_bettiPoincareMatrix_eq_toMatrix_gradedCartanInverse`).

No field assumption, finite-dimensionality over `k`, or Ext theory is needed here; comparison with
bigraded Ext, diagonal-support criteria for linearity, and unbounded formal-power-series identities
live in `TauCeti.Algebra.Category.GradedModuleCat.Betti.Cartan`.

## Main definitions

* `TauCeti.GradedProjectiveResolution.bettiPoincareSeries`: the bigraded Betti Poincaré series of a
  graded projective resolution with finitely generated terms in a projective basis `bP`.
* `TauCeti.bettiPoincareMatrix`: the matrix of Betti Poincaré series with projective rows and
  resolved-module columns.

## Main results

* `TauCeti.GradedProjectiveResolution.bettiPoincareSeries_shiftObj`: the shift law
  `Bᵢ(r{d}; q, t) = qᵈ · Bᵢ(r; q, t)`.
* `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincareSeries_eq` and
  `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincareSeries_eq_of_nonneg`: independence of
  the choice of minimal resolution.
* `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincareSeries_shiftObj_eq`: any minimal
  resolution of `M{d}` has Betti series `qᵈ` times that of any minimal resolution of `M`.
* `TauCeti.gradedCartanMatrix_mul_eval_neg_one_trunc_bettiPoincareMatrix_eq_one`: the finite
  Laurent-polynomial Cartan–Betti identity `C(q) · B(q, -1) = I`.
* `TauCeti.eval_neg_one_trunc_bettiPoincareMatrix_eq_toMatrix_gradedCartanInverse`: identification
  of `B(q, -1)` with the matrix of `gradedCartanInverse`.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Sections 1.2 and 2.11, for graded minimal resolutions and Poincaré/Cartan identities.
* Z. Dancso and A. Licata, "Koszul algebras and flow lattices", Section 2.2, for the graded
  Cartan matrix convention over `ℤ[q,q⁻¹]`.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded
  projective modules and shifts.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits LaurentPolynomial

universe uk uA uI uJ v

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

/-! ### Betti Poincaré series -/

namespace GradedProjectiveResolution

section Series

variable {I : Type uI}
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  {M : GradedModuleCat.{uA} 𝒜}
  (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
  [∀ n, Module.Finite A (r.X n)]

/-- **The Betti Poincaré series of a graded projective resolution** in a projective basis `bP`:
its `n`-th coefficient in `(ℤ[q,q⁻¹])⟦t⟧` is the `i`-th coordinate of the class `[Pₙ]` in
`K₀^gr(proj A)`. -/
def bettiPoincareSeries (i : I) : PowerSeries (LaurentPolynomial ℤ) :=
  PowerSeries.mk fun n =>
    bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
      (r.finiteProjectiveTerm n)) i

/-- The `n`-th power-series coefficient of `bettiPoincareSeries` is the `i`-th projective
coordinate of `[Pₙ]`. -/
@[simp]
theorem coeff_bettiPoincareSeries (i : I) (n : ℕ) :
    PowerSeries.coeff n (r.bettiPoincareSeries bP i) =
      bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r.finiteProjectiveTerm n)) i := by
  simp [bettiPoincareSeries]

/-- Reconstruct the class of the `n`-th resolution term from the `n`-th coefficients of the Betti
Poincaré series. -/
theorem of_finiteProjectiveTerm_eq_sum_coeff_bettiPoincareSeries [Fintype I] (n : ℕ) :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r.finiteProjectiveTerm n) =
      ∑ i, PowerSeries.coeff n (r.bettiPoincareSeries bP i) • bP i := by
  conv_lhs =>
    rw [← bP.sum_repr (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n))]
  simp only [coeff_bettiPoincareSeries]

/-- **Shift law for the Betti Poincaré series**: shifting the resolution by `d` multiplies every
entry by `qᵈ`. -/
@[simp]
theorem bettiPoincareSeries_shiftObj (d : ℤ) (i : I) :
    (r.shiftObj d).bettiPoincareSeries bP i =
      PowerSeries.C (T d) * r.bettiPoincareSeries bP i := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_bettiPoincareSeries, PowerSeries.coeff_C_mul, coeff_bettiPoincareSeries,
    finiteProjectiveTerm_shiftObj, laurentK0_projective_of_shiftObj, map_smul,
    Finsupp.smul_apply, smul_eq_mul]

/-- A vanishing term of a resolution contributes zero to the Betti Poincaré series. -/
theorem coeff_bettiPoincareSeries_eq_zero_of_subsingleton (i : I) {n : ℕ}
    (h : Subsingleton (r.X n)) :
    PowerSeries.coeff n (r.bettiPoincareSeries bP i) = 0 := by
  have hzeroObj : IsZero ((gradedFiniteProjectiveModules 𝒜).ι.obj (r.finiteProjectiveTerm n)) := by
    rw [ObjectProperty.ι_obj, finiteProjectiveTerm_obj]
    exact (IsZero.iff_id_eq_zero _).2
      (GradedModuleCat.hom_ext <| LinearMap.ext fun _ => h.elim _ _)
  have hzero : IsZero (r.finiteProjectiveTerm n) :=
    IsZero.of_full_of_faithful_of_isZero (gradedFiniteProjectiveModules 𝒜).ι _ hzeroObj
  rw [coeff_bettiPoincareSeries, ← LaurentK0.ofExactK0_exactK0_of.{uA},
    ExactK0.of_eq_zero_of_isZero.{uA} hzero, map_zero, map_zero, Finsupp.zero_apply]

/-- When a resolution vanishes from homological degree `N` onward, its Betti Poincaré series is a
polynomial of degree strictly less than `N`, equal to its `N`-truncation. -/
theorem bettiPoincareSeries_eq_coe_trunc (i : I) {N : ℕ}
    (hN : ∀ n ≥ N, Subsingleton (r.X n)) :
    r.bettiPoincareSeries bP i =
      (PowerSeries.trunc N (r.bettiPoincareSeries bP i) : PowerSeries (LaurentPolynomial ℤ)) := by
  refine PowerSeries.ext fun n => ?_
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hn
  · rfl
  · exact r.coeff_bettiPoincareSeries_eq_zero_of_subsingleton bP i (hN n (Nat.le_of_not_lt hn))

/-- Evaluating the `N`-truncation of a Betti Poincaré series at `t = -1` gives the alternating sum
of the first `N` projective coordinates. -/
theorem eval_neg_one_trunc_bettiPoincareSeries (i : I) (N : ℕ) :
    (PowerSeries.trunc N (r.bettiPoincareSeries bP i)).eval (-1) =
      ∑ n ∈ Finset.range N,
        (-1 : LaurentPolynomial ℤ) ^ n *
          bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
            (r.finiteProjectiveTerm n)) i := by
  rw [Polynomial.eval, PowerSeries.eval₂_trunc_eq_sum_range]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [RingHom.id_apply, coeff_bettiPoincareSeries, mul_comm]

end Series

/-! ### Independence of minimal resolution -/

section Uniqueness

variable [DirectSum.Decomposition 𝒜] {I : Type uI}
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  {M : GradedModuleCat.{uA} 𝒜}

/-- **Independence of minimal resolution for the Betti Poincaré series.** Any two bounded-below
minimal graded projective resolutions of `M` with finitely generated terms produce the same Betti
Poincaré series. -/
theorem IsMinimal.bettiPoincareSeries_eq
    {r₁ r₂ : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ n, Module.Finite A (r₁.X n)] [∀ n, Module.Finite A (r₂.X n)]
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal)
    (hb₁ : ∀ n, ∃ b : ℤ, ∀ p < b, (r₁.grading n).piece p = ⊥)
    (hb₂ : ∀ n, ∃ b : ℤ, ∀ p < b, (r₂.grading n).piece p = ⊥) (i : I) :
    r₁.bettiPoincareSeries bP i = r₂.bettiPoincareSeries bP i := by
  refine PowerSeries.ext fun n => ?_
  obtain ⟨e⟩ := hr₁.nonempty_iso_termObj hr₂ hb₁ hb₂ n
  rw [coeff_bettiPoincareSeries, coeff_bettiPoincareSeries]
  congr 2
  refine LaurentK0.of_congr.{uA} _
    (ObjectProperty.isoMk (P := gradedFiniteProjectiveModules 𝒜)
      (X := r₁.finiteProjectiveTerm n) (Y := r₂.finiteProjectiveTerm n) ?_)
  exact eqToIso (r₁.finiteProjectiveTerm_obj n) ≪≫ e ≪≫ eqToIso (r₂.finiteProjectiveTerm_obj n).symm

/-- Over a nonnegatively graded algebra, finitely generated terms are automatically bounded below,
so any two minimal resolutions of `M` with finitely generated terms have the same Betti Poincaré
series. -/
theorem IsMinimal.bettiPoincareSeries_eq_of_nonneg
    {r₁ r₂ : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ n, Module.Finite A (r₁.X n)] [∀ n, Module.Finite A (r₂.X n)]
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (i : I) :
    r₁.bettiPoincareSeries bP i = r₂.bettiPoincareSeries bP i :=
  hr₁.bettiPoincareSeries_eq bP hr₂
    (fun m => (r₁.grading m).exists_piece_eq_bot_of_lt 𝒜 hneg)
    (fun m => (r₂.grading m).exists_piece_eq_bot_of_lt 𝒜 hneg) i

/-- **Intrinsic shift law for minimal resolutions**: over a nonnegatively graded algebra, the Betti
Poincaré series of any minimal resolution of `M{d}` with finitely generated terms equals `qᵈ` times
the Betti Poincaré series of any minimal resolution of `M` with finitely generated terms. -/
theorem IsMinimal.bettiPoincareSeries_shiftObj_eq
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    {d : ℤ} {r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M.shiftObj d).grading}
    [∀ n, Module.Finite A (r.X n)] [∀ n, Module.Finite A (r'.X n)]
    (hr : r.IsMinimal) (hr' : r'.IsMinimal) (hneg : ∀ p < 0, 𝒜 p = ⊥) (i : I) :
    r'.bettiPoincareSeries bP i = PowerSeries.C (T d) * r.bettiPoincareSeries bP i := by
  have hmin : (r.shiftObj d).IsMinimal := (r.isMinimal_shiftObj_iff d).mpr hr
  rw [hr'.bettiPoincareSeries_eq_of_nonneg bP hmin hneg i, bettiPoincareSeries_shiftObj]

end Uniqueness

end GradedProjectiveResolution

/-! ### The Betti Poincaré matrix -/

section Matrix

variable {I : Type uI} {J : Type uJ}
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  {M : J → GradedModuleCat.{uA} 𝒜}
  (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
  [∀ j n, Module.Finite A ((r j).X n)]

/-- **The Betti Poincaré matrix** of a family of graded projective resolutions `r j` with finitely
generated terms in a projective basis `bP`: rows are indexed by the projective basis `I` and
columns by the resolved family `J`. -/
def bettiPoincareMatrix : Matrix I J (PowerSeries (LaurentPolynomial ℤ)) :=
  Matrix.of fun i j => (r j).bettiPoincareSeries bP i

/-- The `(i, j)` entry of the Betti Poincaré matrix is the `i`-th Betti Poincaré series of the
`j`-th resolution. -/
@[simp]
theorem bettiPoincareMatrix_apply (i : I) (j : J) :
    bettiPoincareMatrix bP r i j = (r j).bettiPoincareSeries bP i := by
  rw [bettiPoincareMatrix, Matrix.of_apply]

/-- Over a nonnegatively graded algebra, the Betti Poincaré matrix is independent of the choice of
minimal resolutions of the family `M` with finitely generated terms. -/
theorem bettiPoincareMatrix_eq_of_isMinimal [DirectSum.Decomposition 𝒜]
    {r₁ r₂ : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading}
    [∀ j n, Module.Finite A ((r₁ j).X n)] [∀ j n, Module.Finite A ((r₂ j).X n)]
    (hr₁ : ∀ j, (r₁ j).IsMinimal) (hr₂ : ∀ j, (r₂ j).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) :
    bettiPoincareMatrix bP r₁ = bettiPoincareMatrix bP r₂ :=
  Matrix.ext fun i j => (hr₁ j).bettiPoincareSeries_eq_of_nonneg bP (hr₂ j) hneg i

end Matrix

/-! ### Finite-resolution Cartan–Betti identities -/

section FiniteCartanBetti

variable {I : Type uI} {J : Type uJ}
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (bM : Module.Basis J (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)))
  {M : J → (gradedFiniteModules 𝒜).FullSubcategory}
  (hbM : ∀ j, bM j = LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (M j))
  (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).obj.grading)
  [∀ j n, Module.Finite A ((r j).X n)]

include hbM in
/-- **Finite-resolution Cartan–Betti identity `C(q) · B(q, -1) = I`.** If the modules forming a
basis `bM` of `G₀^gr(mod A)` admit finite graded projective resolutions vanishing from homological
degree `N` onward, then multiplying the graded Cartan matrix `C(q)` on the right by the truncated
Betti Poincaré matrix evaluated at `t = -1` yields the identity matrix over `ℤ[q,q⁻¹]`. -/
theorem gradedCartanMatrix_mul_eval_neg_one_trunc_bettiPoincareMatrix_eq_one
    [Fintype I] [Finite J] [DecidableEq J]
    {N : ℕ} (hN : ∀ j, ∀ n ≥ N, Subsingleton ((r j).X n)) :
    gradedCartanMatrix 𝒜 bP bM *
        (bettiPoincareMatrix bP r).map (fun P => (PowerSeries.trunc N P).eval (-1)) = 1 := by
  refine Matrix.ext fun j₁ j₂ => ?_
  rw [Matrix.mul_apply, Matrix.one_apply]
  let alt : LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) :=
    ∑ n ∈ Finset.range N,
      (-1 : LaurentPolynomial ℤ) ^ n •
        LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
          ((r j₂).finiteProjectiveTerm n)
  have hcol : ∀ i,
      ((bettiPoincareMatrix bP r).map (fun P => (PowerSeries.trunc N P).eval (-1))) i j₂ =
        bP.repr alt i := fun i => by
    rw [Matrix.map_apply, bettiPoincareMatrix_apply,
      GradedProjectiveResolution.eval_neg_one_trunc_bettiPoincareSeries]
    simp [alt, map_sum, map_smul, Finsupp.finsetSum_apply]
  have hmul :
      ∑ i, gradedCartanMatrix 𝒜 bP bM j₁ i *
          ((bettiPoincareMatrix bP r).map (fun P => (PowerSeries.trunc N P).eval (-1))) i j₂ =
        (Matrix.mulVec (gradedCartanMatrix 𝒜 bP bM) (bP.repr alt)) j₁ := by
    rw [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun i _ => by rw [hcol i]
  rw [hmul, gradedCartanMatrix_mulVec_repr,
    ← (r j₂).laurentK0_eq_gradedCartanMap_sum N (hN j₂) (M j₂).property,
    ← hbM j₂, Module.Basis.repr_self, Finsupp.single_apply]
  simp [eq_comm]

include hbM in
/-- **Matrix form of `gradedCartanInverse`.** When every finite graded module admits a finite
graded-projective resolution, the truncated Betti Poincaré matrix evaluated at `t = -1` is the
matrix of `gradedCartanInverse 𝒜 h` in the bases `bM` and `bP`. -/
theorem eval_neg_one_trunc_bettiPoincareMatrix_eq_toMatrix_gradedCartanInverse
    [DirectSum.Decomposition 𝒜] [Finite I] [Fintype J] [DecidableEq J]
    (h : gradedFiniteModules 𝒜 ≤
      (gradedModuleCanonicalExactStructure 𝒜).admitsFiniteResolution
        (gradedFiniteProjectiveModules 𝒜))
    {N : ℕ} (hN : ∀ j, ∀ n ≥ N, Subsingleton ((r j).X n)) :
    (bettiPoincareMatrix bP r).map (fun P => (PowerSeries.trunc N P).eval (-1)) =
      LinearMap.toMatrix bM bP (gradedCartanInverse 𝒜 h) := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.map_apply, bettiPoincareMatrix_apply,
    GradedProjectiveResolution.eval_neg_one_trunc_bettiPoincareSeries,
    LinearMap.toMatrix_apply, hbM j,
    (r j).laurentK0_eq_gradedCartanMap_sum N (hN j) (M j).property]
  have hinv := (gradedCartanEquiv 𝒜 h).symm_apply_apply
    (∑ n ∈ Finset.range N,
      (-1 : LaurentPolynomial ℤ) ^ n •
        LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
          ((r j).finiteProjectiveTerm n))
  rw [gradedCartanEquiv_symm_apply, gradedCartanEquiv_apply] at hinv
  rw [hinv]
  simp [map_sum, map_smul, Finsupp.finsetSum_apply]

include hbM in
/-- When every finite graded module admits a finite graded-projective resolution, the truncated
Betti Poincaré matrix evaluated at `t = -1` is also a left inverse of the graded Cartan matrix. -/
theorem eval_neg_one_trunc_bettiPoincareMatrix_mul_gradedCartanMatrix_eq_one
    [DirectSum.Decomposition 𝒜] [Fintype I] [Fintype J] [DecidableEq I]
    (h : gradedFiniteModules 𝒜 ≤
      (gradedModuleCanonicalExactStructure 𝒜).admitsFiniteResolution
        (gradedFiniteProjectiveModules 𝒜))
    {N : ℕ} (hN : ∀ j, ∀ n ≥ N, Subsingleton ((r j).X n)) :
    (bettiPoincareMatrix bP r).map (fun P => (PowerSeries.trunc N P).eval (-1)) *
        gradedCartanMatrix 𝒜 bP bM = 1 := by
  classical
  rw [eval_neg_one_trunc_bettiPoincareMatrix_eq_toMatrix_gradedCartanInverse bP bM hbM r h hN]
  have hC : gradedCartanMatrix 𝒜 bP bM = LinearMap.toMatrix bP bM (gradedCartanMap 𝒜) := by
    refine Matrix.ext fun j i => ?_
    rw [gradedCartanMatrix_apply, LinearMap.toMatrix_apply]
  rw [hC, ← LinearMap.toMatrix_comp]
  have hcomp : (gradedCartanInverse 𝒜 h).comp (gradedCartanMap 𝒜) = LinearMap.id :=
    LinearMap.ext fun x => by
      simpa [gradedCartanEquiv_symm_apply, gradedCartanEquiv_apply] using
        (gradedCartanEquiv 𝒜 h).symm_apply_apply x
  rw [hcomp, LinearMap.toMatrix_id]

end FiniteCartanBetti

end TauCeti
