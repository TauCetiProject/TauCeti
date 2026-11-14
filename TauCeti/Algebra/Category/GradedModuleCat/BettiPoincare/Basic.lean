/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.MinimalResolution

/-!
# The Betti Poincaré series of graded projective resolutions

Let `A` be a `ℤ`-graded `k`-algebra and let `bP` be a `ℤ[q,q⁻¹]`-basis of the graded projective
Grothendieck group `K₀^gr(proj A)`. Any concrete graded projective resolution `P_• ⟶ M` with
finitely generated projective terms gives a sequence of classes `[Pₙ] ∈ K₀^gr(proj A)` whose `bP`-
coordinates assemble into a formal power series

```text
B_M(q, t)_i = ∑_{n ≥ 0} coord_i([Pₙ]) tⁿ ∈ (ℤ[q,q⁻¹])⟦t⟧.
```

For a family of graded modules `M : J → GradedModuleCat 𝒜` equipped with such resolutions, the
resulting series form the `I × J` **Betti Poincaré matrix**
`TauCeti.bettiPoincarePowerSeriesMatrix`, with rows indexed by the projective basis `I` and columns
indexed by `J`. This row-and-column orientation matches `TauCeti.gradedCartanMatrix`, whose rows are
indexed by `J` and columns by `I`.

When the resolutions are minimal and bounded below (in particular, automatically when `A` is
nonnegatively decomposed because the terms are finitely generated over `A`), uniqueness of minimal
graded projective resolutions up to chain isomorphism makes both the individual Betti Poincaré
series and the Betti Poincaré matrix independent of the chosen minimal resolutions. Shifting the
resolved module `M ↦ M{d}` multiplies its Betti Poincaré series by `qᵈ`, and in particular shifting
by `{1}` multiplies it by `q`.

## Main definitions

* `TauCeti.GradedProjectiveResolution.finiteProjectiveTerm`: the `n`th finitely generated term of a
  graded projective resolution in `(gradedFiniteProjectiveModules 𝒜).FullSubcategory`.
* `TauCeti.GradedProjectiveResolution.bettiPoincarePowerSeries`: the `i`th coordinate formal power
  series of a graded projective resolution in `PowerSeries (LaurentPolynomial ℤ)`.
* `TauCeti.bettiPoincarePowerSeriesMatrix`: the `I × J` matrix of Betti Poincaré series of a family
  of graded projective resolutions.

## Main results

* `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincarePowerSeries_eq` and
  `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincarePowerSeries_eq_of_moduleFinite`:
  independence of the chosen minimal resolution.
* `TauCeti.GradedProjectiveResolution.bettiPoincarePowerSeries_shiftObj`: shifting `M` by `d`
  multiplies its Betti Poincaré series by `qᵈ`.
* `TauCeti.bettiPoincarePowerSeriesMatrix_eq_of_moduleFinite` and
  `TauCeti.bettiPoincarePowerSeriesMatrix_shiftObj_const`: resolution independence and shift
  equivariance for the Betti Poincaré matrix.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  *Journal of the AMS* **9** (1996), Sections 1.2 and 2.11, for graded Betti numbers and formal
  Poincaré/Hilbert matrices.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for minimal graded
  projective resolutions.
* Z. Dancso and A. Licata, *Koszul algebras and flow lattices*, *Journal of Combinatorial Theory,
  Series A* **185** (2022), Section 2.2, for the Laurent Grothendieck group `K₀^gr(proj A)`.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory LaurentPolynomial

universe uk uA uI uJ

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

/-! ### Finite projective resolution terms and their `K₀^gr` classes -/

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}

/-- A finitely generated term of a concrete graded projective resolution, as an object of the
finite graded projective category. -/
@[expose] def finiteProjectiveTerm
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading) (n : ℕ)
    [Module.Finite A (r.X n)] : (gradedFiniteProjectiveModules 𝒜).FullSubcategory :=
  ⟨r.termObj n, gradedFiniteProjectiveModules_iff.mpr ⟨inferInstance, r.projective n⟩⟩

/-- The underlying graded object of the finite projective term is the original resolution term. -/
@[simp]
theorem finiteProjectiveTerm_obj
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading) (n : ℕ)
    [Module.Finite A (r.X n)] : (r.finiteProjectiveTerm n).obj = r.termObj n :=
  (rfl)

/-- The finite projective terms of a shifted resolution are the internal shifts of the original
finite projective terms. -/
@[simp]
theorem shiftObj_finiteProjectiveTerm
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading) (d : ℤ) (n : ℕ)
    [Module.Finite A (r.X n)] :
    (r.shiftObj d).finiteProjectiveTerm n =
      ⟨(r.finiteProjectiveTerm n).obj.shiftObj d,
        gradedFiniteProjectiveModules_shiftObj (r.finiteProjectiveTerm n).property d⟩ :=
  (rfl)

/-- Shifting a resolution by `d` multiplies the `K₀^gr(proj A)` class of each finite projective
term by `qᵈ`. -/
theorem laurentK0_shiftObj_finiteProjectiveTerm
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading) (d : ℤ) (n : ℕ)
    [Module.Finite A (r.X n)] :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        ((r.shiftObj d).finiteProjectiveTerm n) =
      (T d : LaurentPolynomial ℤ) •
        LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
          (r.finiteProjectiveTerm n) := by
  rw [shiftObj_finiteProjectiveTerm, laurentK0_projective_of_shiftObj]

section MinimalUniqueness

variable [DirectSum.Decomposition 𝒜]
  {r r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}

/-- Corresponding finite projective terms of two bounded-below minimal graded projective
resolutions of `M` define the same class in `K₀^gr(proj A)`. -/
theorem IsMinimal.laurentK0_finiteProjectiveTerm_eq (hr : r.IsMinimal) (hr' : r'.IsMinimal)
    (b : ℕ → ℤ) (hbelow : ∀ m p, p < b m → (r.grading m).piece p = ⊥)
    (b' : ℕ → ℤ) (hbelow' : ∀ m p, p < b' m → (r'.grading m).piece p = ⊥)
    (n : ℕ) [Module.Finite A (r.X n)] [Module.Finite A (r'.X n)] :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (r.finiteProjectiveTerm n) =
      LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r'.finiteProjectiveTerm n) :=
  LaurentK0.of_congr _
    (ObjectProperty.isoMk (gradedFiniteProjectiveModules 𝒜)
      (hr.termObjIso hr' b hbelow b' hbelow' n))

/-- Over a nonnegatively decomposed ring, corresponding terms of two minimal graded projective
resolutions of `M` with finitely generated terms define the same class in `K₀^gr(proj A)`. -/
theorem IsMinimal.laurentK0_finiteProjectiveTerm_eq_of_moduleFinite
    [∀ m, Module.Finite A (r.X m)] [∀ m, Module.Finite A (r'.X m)]
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hr : r.IsMinimal) (hr' : r'.IsMinimal) (n : ℕ) :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (r.finiteProjectiveTerm n) =
      LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r'.finiteProjectiveTerm n) :=
  LaurentK0.of_congr _
    (ObjectProperty.isoMk (gradedFiniteProjectiveModules 𝒜)
      (hr.termObjIsoOfModuleFinite hneg hr' n))

end MinimalUniqueness

/-! ### The Betti Poincaré series of a single resolution -/

section Series

variable {I : Type uI}

/-- **The Betti Poincaré series** of a graded projective resolution with finitely generated terms,
in the projective basis `bP`: its `n`th power-series coefficient is the `i`th `bP`-coordinate of
`[Pₙ]` in `K₀^gr(proj A)`. -/
def bettiPoincarePowerSeries
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))) (i : I) :
    PowerSeries (LaurentPolynomial ℤ) :=
  PowerSeries.mk fun n ↦
    bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
      (r.finiteProjectiveTerm n)) i

/-- The `n`th coefficient of the Betti Poincaré series is the `i`th projective coordinate of the
`n`th resolution term. -/
@[simp]
theorem coeff_bettiPoincarePowerSeries
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))) (i : I) (n : ℕ) :
    PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i) =
      bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r.finiteProjectiveTerm n)) i := by
  simp [bettiPoincarePowerSeries]

/-- The constant term of the Betti Poincaré series is the `i`th projective coordinate of `P₀`. -/
@[simp]
theorem constantCoeff_bettiPoincarePowerSeries
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))) (i : I) :
    PowerSeries.constantCoeff (r.bettiPoincarePowerSeries bP i) =
      bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r.finiteProjectiveTerm 0)) i := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_bettiPoincarePowerSeries]

/-- In a finite projective basis `bP`, the `n`th coefficients of `r.bettiPoincarePowerSeries bP`
reconstruct the class of `Pₙ` in `K₀^gr(proj A)`. -/
theorem of_finiteProjectiveTerm_eq_sum_coeff_bettiPoincarePowerSeries [Fintype I]
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ m, Module.Finite A (r.X m)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))) (n : ℕ) :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (r.finiteProjectiveTerm n) =
      ∑ i, PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i) • bP i := by
  simp only [coeff_bettiPoincarePowerSeries]
  exact (bP.sum_repr _).symm

/-- Pushing forward along the graded Cartan map expresses the class of `Pₙ` in `G₀^gr(mod A)` as a
linear combination of the Cartan images of `bP` weighted by the `n`th Betti coefficients. -/
theorem gradedCartanMap_of_finiteProjectiveTerm_eq_sum [Fintype I]
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ m, Module.Finite A (r.X m)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))) (n : ℕ) :
    LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜)
        ⟨r.termObj n, gradedFiniteModules_iff.mpr inferInstance⟩ =
      ∑ i, PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i) • gradedCartanMap 𝒜 (bP i) := by
  have h := congrArg (gradedCartanMap 𝒜)
    (r.of_finiteProjectiveTerm_eq_sum_coeff_bettiPoincarePowerSeries bP n)
  simpa only [finiteProjectiveTerm, gradedCartanMap_of, map_sum, map_smul] using h

/-- **Shifting the resolved module by `d` multiplies its Betti Poincaré series by `qᵈ`.** -/
@[simp]
theorem bettiPoincarePowerSeries_shiftObj
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))) (d : ℤ) (i : I) :
    (r.shiftObj d).bettiPoincarePowerSeries bP i =
      PowerSeries.C (T d : LaurentPolynomial ℤ) * r.bettiPoincarePowerSeries bP i := by
  ext n
  rw [coeff_bettiPoincarePowerSeries, PowerSeries.coeff_C_mul, coeff_bettiPoincarePowerSeries,
    laurentK0_shiftObj_finiteProjectiveTerm, map_smul, Finsupp.smul_apply, smul_eq_mul]

/-- Shifting the resolved module by `{1}` multiplies its Betti Poincaré series by `q = T 1`. -/
theorem bettiPoincarePowerSeries_shiftObj_one
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))) (i : I) :
    (r.shiftObj 1).bettiPoincarePowerSeries bP i =
      PowerSeries.C (T 1 : LaurentPolynomial ℤ) * r.bettiPoincarePowerSeries bP i :=
  r.bettiPoincarePowerSeries_shiftObj bP 1 i

/-- **Minimal-resolution independence of the Betti Poincaré series.** Any two bounded-below minimal
graded projective resolutions of `M` with finitely generated terms have the same Betti Poincaré
series. -/
theorem IsMinimal.bettiPoincarePowerSeries_eq [DirectSum.Decomposition 𝒜]
    {r r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ n, Module.Finite A (r.X n)] [∀ n, Module.Finite A (r'.X n)]
    (hr : r.IsMinimal) (hr' : r'.IsMinimal)
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (b : ℕ → ℤ) (hbelow : ∀ n p, p < b n → (r.grading n).piece p = ⊥)
    (b' : ℕ → ℤ) (hbelow' : ∀ n p, p < b' n → (r'.grading n).piece p = ⊥) (i : I) :
    r.bettiPoincarePowerSeries bP i = r'.bettiPoincarePowerSeries bP i := by
  ext n
  simp only [coeff_bettiPoincarePowerSeries,
    hr.laurentK0_finiteProjectiveTerm_eq hr' b hbelow b' hbelow' n]

/-- Over a nonnegatively decomposed ring, any two minimal graded projective resolutions of `M` with
finitely generated terms have the same Betti Poincaré series. -/
theorem IsMinimal.bettiPoincarePowerSeries_eq_of_moduleFinite [DirectSum.Decomposition 𝒜]
    {r r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ n, Module.Finite A (r.X n)] [∀ n, Module.Finite A (r'.X n)]
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hr : r.IsMinimal) (hr' : r'.IsMinimal)
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))) (i : I) :
    r.bettiPoincarePowerSeries bP i = r'.bettiPoincarePowerSeries bP i := by
  ext n
  simp only [coeff_bettiPoincarePowerSeries,
    hr.laurentK0_finiteProjectiveTerm_eq_of_moduleFinite hneg hr' n]

end Series

end GradedProjectiveResolution

/-! ### The matrix-valued Betti Poincaré series -/

section Matrix

variable {I : Type uI} {J : Type uJ}
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  {M : J → GradedModuleCat.{uA} 𝒜}

/-- **The matrix-valued Betti Poincaré series** of a family of graded projective resolutions:
rows are indexed by the projective basis `I` and columns by the family `J`, with `(i, j)`-entry
`(r j).bettiPoincarePowerSeries bP i`. -/
def bettiPoincarePowerSeriesMatrix
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r j).X n)] :
    Matrix I J (PowerSeries (LaurentPolynomial ℤ)) :=
  Matrix.of fun i j ↦ (r j).bettiPoincarePowerSeries bP i

/-- The `(i, j)`-entry of the Betti Poincaré matrix is the `i`th Betti Poincaré series of `r j`. -/
@[simp]
theorem bettiPoincarePowerSeriesMatrix_apply
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r j).X n)] (i : I) (j : J) :
    bettiPoincarePowerSeriesMatrix bP r i j = (r j).bettiPoincarePowerSeries bP i :=
  (rfl)

/-- The `n`th power-series coefficient of `(bettiPoincarePowerSeriesMatrix bP r) i j` is the `i`th
projective coordinate of the `n`th term of `r j`. -/
theorem coeff_bettiPoincarePowerSeriesMatrix
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r j).X n)] (i : I) (j : J) (n : ℕ) :
    PowerSeries.coeff n (bettiPoincarePowerSeriesMatrix bP r i j) =
      bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        ((r j).finiteProjectiveTerm n)) i := by
  simp [bettiPoincarePowerSeriesMatrix]

/-- Shifting each resolved module `M j` by `d j` multiplies the `j`th column of the Betti Poincaré
matrix by `q^{d j}`. -/
theorem bettiPoincarePowerSeriesMatrix_shiftObj
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r j).X n)] (d : J → ℤ) (i : I) (j : J) :
    bettiPoincarePowerSeriesMatrix bP (fun j ↦ (r j).shiftObj (d j)) i j =
      PowerSeries.C (T (d j) : LaurentPolynomial ℤ) * bettiPoincarePowerSeriesMatrix bP r i j := by
  simp

/-- Shifting every resolved module in the family by the same degree `d` scales the Betti Poincaré
matrix by `qᵈ`. -/
theorem bettiPoincarePowerSeriesMatrix_shiftObj_const
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r j).X n)] (d : ℤ) :
    bettiPoincarePowerSeriesMatrix bP (fun j ↦ (r j).shiftObj d) =
      PowerSeries.C (T d : LaurentPolynomial ℤ) • bettiPoincarePowerSeriesMatrix bP r := by
  ext i j
  simp [smul_eq_mul]

/-- The Betti Poincaré matrix of bounded-below minimal resolutions depends only on the resolved
family `M`, not on the chosen minimal resolutions. -/
theorem bettiPoincarePowerSeriesMatrix_eq [DirectSum.Decomposition 𝒜]
    {r r' : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading}
    [∀ j n, Module.Finite A ((r j).X n)] [∀ j n, Module.Finite A ((r' j).X n)]
    (hr : ∀ j, (r j).IsMinimal) (hr' : ∀ j, (r' j).IsMinimal)
    (b : J → ℕ → ℤ) (hbelow : ∀ j n p, p < b j n → ((r j).grading n).piece p = ⊥)
    (b' : J → ℕ → ℤ) (hbelow' : ∀ j n p, p < b' j n → ((r' j).grading n).piece p = ⊥) :
    bettiPoincarePowerSeriesMatrix bP r = bettiPoincarePowerSeriesMatrix bP r' :=
  Matrix.ext fun i j ↦
    (hr j).bettiPoincarePowerSeries_eq (hr' j) bP (b j) (hbelow j) (b' j) (hbelow' j) i

/-- Over a nonnegatively decomposed ring, the Betti Poincaré matrix of minimal resolutions with
finitely generated terms depends only on the resolved family `M`. -/
theorem bettiPoincarePowerSeriesMatrix_eq_of_moduleFinite [DirectSum.Decomposition 𝒜]
    {r r' : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading}
    [∀ j n, Module.Finite A ((r j).X n)] [∀ j n, Module.Finite A ((r' j).X n)]
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hr : ∀ j, (r j).IsMinimal) (hr' : ∀ j, (r' j).IsMinimal) :
    bettiPoincarePowerSeriesMatrix bP r = bettiPoincarePowerSeriesMatrix bP r' :=
  Matrix.ext fun i j ↦
    (hr j).bettiPoincarePowerSeries_eq_of_moduleFinite hneg (hr' j) bP i

end Matrix

end TauCeti
