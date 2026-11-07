/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.ClusterSet
public import TauCeti.Topology.Algebra.Polynomial.Basic
public import TauCeti.Topology.Algebra.Polynomial.Root.Extension
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Extension of bounded roots over convex bases

A bounded continuous root of a polynomial family on a convex base extends continuously
to the closed base, provided every specialization over the closed base is nonzero. The convex
base can be a relative simplex interior: it need not be open in its ambient vector space.
The extension continues to solve the polynomial equation and retains any closed interval
bound on the original section. This is the root-extension step used to lift a base
triangulation through cylindrical sections.

`Polynomial.exists_continuousOn_closure_eqOn_root` applies this to a polynomial whose
coefficients are multivariate polynomials in the base coordinates. Its nonvanishing
hypothesis concerns the entire specialized polynomial, not its discriminant: repeated
boundary roots are allowed, but an identically zero specialization is not.

## References

* Bochnak, Coste and Roy, *Real Algebraic Geometry*, §9.2.
-/

public section

open Set Topology TauCeti

namespace Convex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] {U : Set E} {f : E → ℝ}

/-- A bounded continuous root section on a convex base extends to its closure if evaluation
is continuous there and no specialization is the zero polynomial. -/
theorem continuousOn_extendFrom_of_polynomial_root (hU : Convex ℝ U) {p : E → Polynomial ℝ}
    (hp : ContinuousOn (fun z : E × ℝ ↦ (p z.1).eval z.2) (closure U ×ˢ univ))
    (hf : ContinuousOn f U) (hroot : ∀ x ∈ U, (p x).eval (f x) = 0)
    (hbdd : Bornology.IsBounded (f '' U)) (hne : ∀ x ∈ closure U, p x ≠ 0) :
    ContinuousOn (extendFrom U f) (closure U) :=
  TauCeti.continuousOn_extendFrom_of_polynomial_root hp hf hroot hbdd hne
    fun x _ ↦ hU.isPreconnectedApproachAt x

end Convex

namespace Polynomial

variable {ι : Type*} {U : Set (ι → ℝ)} {f : (ι → ℝ) → ℝ}

/-- A continuous root section of a polynomial with polynomial base coefficients extends
from a convex base to its closure, still solves the equation, and retains its interval
bounds. This includes sections over relative simplex interiors and allows roots to merge. -/
theorem exists_continuousOn_closure_eqOn_root (P : Polynomial (MvPolynomial ι ℝ))
    (hU : Convex ℝ U) (hf : ContinuousOn f U) {a b : ℝ} (hbdd : MapsTo f U (Icc a b))
    (hroot : ∀ x ∈ U, (P.map (MvPolynomial.eval x)).eval (f x) = 0)
    (hne : ∀ x ∈ closure U, P.map (MvPolynomial.eval x) ≠ 0) :
    ∃ F : (ι → ℝ) → ℝ, ContinuousOn F (closure U) ∧ EqOn F f U ∧
      MapsTo F (closure U) (Icc a b) ∧
      ∀ x ∈ closure U, (P.map (MvPolynomial.eval x)).eval (F x) = 0 := by
  have hP : Continuous fun z : (ι → ℝ) × ℝ ↦ (P.map (MvPolynomial.eval z.1)).eval z.2 :=
    continuous_eval_of_continuous_coeff (f := fun x ↦ P.map (MvPolynomial.eval x))
      (d := P.natDegree)
      (fun i _ ↦ by simpa only [coeff_map] using (P.coeff i).continuous_eval)
      (fun _ ↦ natDegree_map_le)
  have hF := hU.continuousOn_extendFrom_of_polynomial_root hP.continuousOn hf hroot
    (isCompact_Icc.isBounded.subset hbdd.image_subset) hne
  have heq : EqOn (extendFrom U f) f U := fun x hx ↦ extendFrom_extends hf x hx
  refine ⟨extendFrom U f, hF, heq, ?_, fun x hx ↦
    eval_extendFrom_eq_zero hP.continuousOn hf hroot hF hx⟩
  have hmaps : MapsTo (extendFrom U f) U (Icc a b) := fun x hx ↦ heq hx ▸ hbdd hx
  simpa only [closure_Icc] using hmaps.closure_of_continuousOn hF

end Polynomial
