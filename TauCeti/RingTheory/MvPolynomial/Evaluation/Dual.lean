/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Evaluation.Homogeneous
import Mathlib.LinearAlgebra.Dual.Basis
import TauCeti.Data.Finsupp.Weight
import TauCeti.RingTheory.MvPolynomial.Finrank

/-!
# Evaluation spans the dual of a homogeneous component

Under a residue-field size bound, evaluation at points of a local ring where a homogeneous
polynomial takes a unit value spans the dual of the degree-`n` component, even after mapping
those points to another coefficient ring. This lets one test a linear map on the dual using
point evaluations instead of coefficient functionals.
-/

public section

namespace MvPolynomial.IsHomogeneous

open IsLocalRing

/-- Let `g` be homogeneous of degree `e` over a local ring `W`, with a unit value at some point.
If the residue field has at least `n + e` elements, the evaluations at the images of the points
where `g` is a unit span the dual of the degree-`n` component over the target of `ι`. -/
theorem span_range_aeval_eq_top {σ W R : Type*} [Finite σ] [CommRing W] [IsLocalRing W]
    [CommSemiring R] {n e : ℕ} {g : MvPolynomial σ W} (hg : g.IsHomogeneous e) (ι : W →+* R)
    (hcard : ((n + e : ℕ) : Cardinal) ≤ Cardinal.mk (ResidueField W))
    (hg₀ : ∃ y, IsUnit (eval y g)) :
    Submodule.span R (Set.range fun y : {y : σ → W // IsUnit (eval y g)} ↦
      (MvPolynomial.aeval (ι ∘ y.val)).toLinearMap.comp
        (homogeneousSubmodule σ R n).subtype) = ⊤ := by
  classical
  let := Fintype.ofFinite σ
  let := Fintype.ofFinite {γ : σ →₀ ℕ // γ.degree = n}
  let E := (TauCeti.homogeneousMonomialBasis (R := R) (σ := σ) n).dualBasis.equivFun
  apply (Submodule.map_injective_of_injective E.injective)
  rw [Submodule.map_span, Submodule.map_top, E.toLinearMap.range_eq_top.mpr E.surjective]
  rw [← Set.range_comp]
  convert hg.span_range_prod_pow_eq_top ι hcard hg₀ using 3
  funext y γ
  calc
    E ((MvPolynomial.aeval (ι ∘ y.val)).toLinearMap.comp
        (homogeneousSubmodule σ R n).subtype) γ =
      MvPolynomial.eval (ι ∘ y.val) (monomial γ.val 1) := by
        rw [Module.Basis.dualBasis_equivFun]
        simp
    _ = _ := by rw [MvPolynomial.eval_monomial]; simp [Finsupp.prod_fintype]

end MvPolynomial.IsHomogeneous
