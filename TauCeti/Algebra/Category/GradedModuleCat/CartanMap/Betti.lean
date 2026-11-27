/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Resolution
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.Betti
public import TauCeti.Algebra.Category.GradedModuleCat.Resolution
public import TauCeti.CategoryTheory.Exact.Resolution.OfChainComplex

/-!
# The Cartan matrix times the Betti Poincaré matrix of finite resolutions

Let `A` be a graded algebra and `P` a graded projective resolution of a graded module `M` by
finitely generated terms whose term `P_{N+1}` vanishes. Then `P_N ⟶ ⋯ ⟶ P₀ ⟶ M` is a finite
resolution of `M` by finite graded projectives, so in `G₀^gr(mod A)`

`[M] = ∑_{n ≤ N} (-1)ⁿ [P_n]`,

where on the right the classes of the terms are taken in `K₀^gr(proj A)` and mapped by the graded
Cartan map. In a Laurent basis `[Pᵢ]` of `K₀^gr(proj A)`, the coordinates of `[P_n]` are the
coefficients of `tⁿ` of the Betti Poincaré series of `P`, so the right-hand side is the Betti
Poincaré series evaluated at `t = -1`, a Laurent polynomial in `q`.

For a family of graded modules `Sⱼ` whose classes form a Laurent basis of `G₀^gr(mod A)`, such as
the graded simples, this is the identity of Laurent-polynomial matrices

`C(q) · B(q, -1) = I`

between the graded Cartan matrix `C(q)`, with rows the classes `[Sⱼ]` and columns the projective
basis, and the Betti Poincaré matrix `B(q, t)` of finite resolutions of the `Sⱼ`, with rows the
projective basis and columns the `Sⱼ`. It is the matrix form of the graded resolution theorem:
the columns of `B(q, -1)` are the alternating classes of the resolutions, which the graded Cartan
map sends to the `[Sⱼ]`; when the graded Cartan map is invertible, `B(q, -1)` is the matrix of its
inverse. Unlike the coefficientwise
identity for possibly infinite minimal resolutions
(`TauCeti.gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincarePowerSeries_eq_one`), no
minimality, finite dimensionality, nonnegative grading or condition on the degree-zero part of `A`
is needed, and the resolutions may be arbitrary.

## Main definitions

* `TauCeti.GradedProjectiveResolution.toFiniteResolution`: a graded projective resolution by
  finitely generated terms with vanishing term in degree `N + 1`, as a finite resolution by finite
  graded projectives.

## Main results

* `TauCeti.GradedProjectiveResolution.gradedCartanMap_sum_finiteProjectiveTerm`: the graded Cartan
  map sends `∑_{n ≤ N} (-1)ⁿ [P_n]` to `[M]`.
* `TauCeti.gradedCartanMatrix_mul_eval_trunc_bettiPoincarePowerSeriesMatrix_eq_one`: the identity
  `C(q) · B(q, -1) = I` of Laurent-polynomial matrices for finite resolutions.

## References

* Charles A. Weibel, *The K-book*, Chapter II, Theorem 7.6, for the resolution theorem.
* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  *Journal of the AMS* **9** (1996), Section 2.11, for the Cartan matrix and the Poincaré series
  of resolutions of the simples.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits LaurentPolynomial

universe uk uA uI uJ

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜} (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)

/-- A module resolved by a graded projective resolution with finitely generated term in degree
zero is finitely generated. -/
theorem gradedFiniteModules_of_finite [Module.Finite A (r.X 0)] : gradedFiniteModules 𝒜 M :=
  gradedFiniteModules_iff.2 (Module.Finite.of_surjective r.π r.surjective_π)

variable [∀ n, Module.Finite A (r.X n)]

/-- A graded projective resolution by finitely generated terms whose term in homological degree
`N + 1` vanishes, as a finite resolution of length `N` by finite graded projectives for the
canonical exact structure of graded modules. The terms above `N + 1` play no role. -/
def toFiniteResolution {N : ℕ} (hN : Subsingleton (r.X (N + 1))) :
    (gradedModuleCanonicalExactStructure 𝒜).toExactStructure.FiniteResolution
      (gradedFiniteProjectiveModules 𝒜) M :=
  -- The canonical exact structure of graded modules is that of the abelian category.
  .ofEq (GradedExactStructure.abelian_toExactStructure _).symm <|
  ExactStructure.FiniteResolution.ofChainComplex (K := r.complex) (ε := r.augmentation)
    (hε := r.complex_d_one_zero_comp_augmentation) r.exact_complex_d_one_zero
    (fun i _ ↦ (HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i (by simp) (by simp)).1
      (r.complex_exactAt_succ i))
    (by simpa using GradedModuleCat.isZero_of_subsingleton (r.termObj (N + 1)))
    (fun i _ ↦ by simpa using (r.finiteProjectiveTerm i).property)

/-- The finite resolution of a graded projective resolution with vanishing term in degree `N + 1`
has length `N`. -/
@[simp]
theorem length_toFiniteResolution {N : ℕ} (hN : Subsingleton (r.X (N + 1))) :
    (r.toFiniteResolution hN).length = N := by
  rw [toFiniteResolution, ExactStructure.FiniteResolution.length_ofEq,
    ExactStructure.FiniteResolution.length_ofChainComplex]

/-- The alternating class of the finite resolution of a graded projective resolution with
vanishing term in degree `N + 1` is `∑_{n ≤ N} (-1)ⁿ [P_n]`. -/
theorem foldAlternating_toFiniteResolution {N : ℕ} (hN : Subsingleton (r.X (N + 1))) :
    (r.toFiniteResolution hN).foldAlternating (fun Z hZ ↦
        LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) ⟨Z, hZ⟩) =
      ∑ n ∈ Finset.range (N + 1),
        (-1 : ℤ) ^ n • LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n) := by
  rw [toFiniteResolution, ExactStructure.FiniteResolution.foldAlternating_ofEq,
    ExactStructure.FiniteResolution.foldAlternating_ofChainComplex _ _ _ _ _
    fun e _ _ ↦ LaurentK0.of_congr _ (ObjectProperty.isoMk _ e), ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun n _ ↦ congrArg _
    (congrArg _ (ObjectProperty.FullSubcategory.ext (by simp)))

variable [DirectSum.Decomposition 𝒜]

/-- **A finite resolution writes a module as an alternating sum of projectives.** If the term of a
graded projective resolution of `M` by finitely generated terms vanishes in degree `N + 1`, the
graded Cartan map sends `∑_{n ≤ N} (-1)ⁿ [P_n]` to `[M]`. -/
theorem gradedCartanMap_sum_finiteProjectiveTerm {N : ℕ} (hN : Subsingleton (r.X (N + 1))) :
    gradedCartanMap 𝒜 (∑ n ∈ Finset.range (N + 1),
        (-1 : ℤ) ^ n • LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n)) =
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜)
        ⟨M, r.gradedFiniteModules_of_finite⟩ := by
  rw [← r.foldAlternating_toFiniteResolution hN, gradedCartanMap_foldAlternating]

end GradedProjectiveResolution

variable [DirectSum.Decomposition 𝒜]

/-- **The Cartan matrix times the Betti Poincaré matrix at `t = -1` is the identity**, for finite
resolutions. Let `bP` be a Laurent basis of `K₀^gr(proj A)` indexed by a finite type, and let the
classes of graded modules `Sⱼ` form a Laurent basis `bS` of `G₀^gr(mod A)`. Given graded projective
resolutions of the `Sⱼ` by finitely generated terms, all vanishing in degree `N + 1`, the graded
Cartan matrix `C(q)` times the Betti Poincaré matrix `B(q, t)` truncated below `t^(N + 1)` and
evaluated at `t = -1` is the identity matrix over `ℤ[q,q⁻¹]`. When the terms vanish in every
degree above `N`, the truncation is the whole Betti Poincaré matrix
(`TauCeti.GradedProjectiveResolution.trunc_bettiPoincarePowerSeries`). -/
theorem gradedCartanMatrix_mul_eval_trunc_bettiPoincarePowerSeriesMatrix_eq_one
    {I : Type uI} [Fintype I] {J : Type uJ} [Finite J] [DecidableEq J]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (bS : Module.Basis J (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)))
    {S : J → GradedModuleCat.{uA} 𝒜}
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).grading)
    [∀ j n, Module.Finite A ((r j).X n)]
    (hbS : ∀ j, bS j = LaurentK0.of.{uA} _ ⟨S j, (r j).gradedFiniteModules_of_finite⟩)
    {N : ℕ} (hN : ∀ j, Subsingleton ((r j).X (N + 1))) :
    gradedCartanMatrix 𝒜 bP bS *
        (bettiPoincarePowerSeriesMatrix r bP).map
          (fun f ↦ (PowerSeries.trunc (N + 1) f).eval (-1)) = 1 := by
  ext i j
  have hcol : (fun l ↦ ((bettiPoincarePowerSeriesMatrix r bP).map
      (fun f ↦ (PowerSeries.trunc (N + 1) f).eval (-1))) l j) =
      bP.repr (∑ n ∈ Finset.range (N + 1),
        (-1 : ℤ) ^ n • LaurentK0.of.{uA} _ ((r j).finiteProjectiveTerm n)) := by
    ext l
    rw [Matrix.map_apply, bettiPoincarePowerSeriesMatrix_apply,
      GradedProjectiveResolution.eval_trunc_bettiPoincarePowerSeries]
  rw [Matrix.mul_apply', hcol, ← Matrix.mulVec, gradedCartanMatrix_mulVec_repr,
    (r j).gradedCartanMap_sum_finiteProjectiveTerm (hN j), ← hbS, Module.Basis.repr_self]
  simp [Matrix.one_apply, Finsupp.single_apply, eq_comm]

end TauCeti
