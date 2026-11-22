/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Betti.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Resolution

/-!
# Finite-resolution Cartan–Betti identities

For a family of graded projective resolutions `r j` of finite graded modules `M j` forming a
`ℤ[q,q⁻¹]`-basis `bM` of `G₀^gr(mod A)`, if every `r j` has finitely generated terms and vanishes
from homological degree `N` onward, evaluating the `N`-truncated Betti Poincaré matrix at `t = -1`
satisfies the Laurent-polynomial Cartan–Betti identity `C(q) · B(q, -1) = I`
(`TauCeti.gradedCartanMatrix_mul_eval_neg_one_trunc_bettiPoincareMatrix_eq_one`). When every
finite graded module admits a finite projective resolution, the same matrix represents
`gradedCartanInverse`
(`TauCeti.eval_neg_one_trunc_bettiPoincareMatrix_eq_toMatrix_gradedCartanInverse`) and hence is also
a left inverse of `C(q)`.

No field assumption, finite-dimensionality over `k`, or Ext theory is needed here.

## Main results

* `TauCeti.gradedCartanMatrix_mul_eval_neg_one_trunc_bettiPoincareMatrix_eq_one`: the finite
  Laurent-polynomial Cartan–Betti identity `C(q) · B(q, -1) = I`.
* `TauCeti.eval_neg_one_trunc_bettiPoincareMatrix_eq_toMatrix_gradedCartanInverse`: identification
  of `B(q, -1)` with the matrix of `gradedCartanInverse`.
* `TauCeti.eval_neg_one_trunc_bettiPoincareMatrix_mul_gradedCartanMatrix_eq_one`: the left-inverse
  identity `B(q, -1) · C(q) = I`.

## References

* Z. Dancso and A. Licata, "Koszul algebras and flow lattices", Section 2.2, for the graded
  Cartan matrix convention over `ℤ[q,q⁻¹]`.
* Charles A. Weibel, *The K-book*, Chapter II, Theorem 7.6.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory LaurentPolynomial

universe uk uA uI uJ

section FiniteCartanBetti

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}
  {I : Type uI} {J : Type uJ}
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (bM : Module.Basis J (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)))
  {M : J → (gradedFiniteModules 𝒜).FullSubcategory}
  (hbM : ∀ j, bM j = LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (M j))
  (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).obj.grading)
  [∀ j n, Module.Finite A ((r j).X n)]

private abbrev alternatingTermClass {M : GradedModuleCat.{uA} 𝒜}
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)] (N : ℕ) :
    LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) :=
  ∑ n ∈ Finset.range N,
    (-1 : LaurentPolynomial ℤ) ^ n •
      LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r.finiteProjectiveTerm n)

private theorem repr_alternatingTermClass {M : GradedModuleCat.{uA} 𝒜}
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)] (i : I) (N : ℕ) :
    (PowerSeries.trunc N (r.bettiPoincareSeries bP i)).eval (-1) =
      bP.repr (alternatingTermClass r N) i := by
  rw [GradedProjectiveResolution.eval_neg_one_trunc_bettiPoincareSeries]
  simp [alternatingTermClass, map_sum, map_smul, Finsupp.finsetSum_apply]

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
  have hmul :
      ∑ i, gradedCartanMatrix 𝒜 bP bM j₁ i *
          ((bettiPoincareMatrix bP r).map (fun P => (PowerSeries.trunc N P).eval (-1))) i j₂ =
        (Matrix.mulVec (gradedCartanMatrix 𝒜 bP bM)
          (bP.repr (alternatingTermClass (r j₂) N))) j₁ := by
    rw [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.map_apply, bettiPoincareMatrix_apply, repr_alternatingTermClass]
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
  rw [Matrix.map_apply, bettiPoincareMatrix_apply, repr_alternatingTermClass,
    LinearMap.toMatrix_apply, hbM j]
  have hM := (r j).laurentK0_eq_gradedCartanMap_sum N (hN j) (M j).property
  have hinv := congrArg (gradedCartanEquiv 𝒜 h).symm hM
  rw [gradedCartanEquiv_symm_apply, ← gradedCartanEquiv_apply 𝒜 h,
    (gradedCartanEquiv 𝒜 h).symm_apply_apply] at hinv
  rw [hinv]

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
