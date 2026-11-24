/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Ramification
import TauCeti.AlgebraicGeometry.Curves.Degree.Pullback

/-!
# Euler-characteristic degree Riemann–Hurwitz formulas for curves

Let `f : X ⟶ Y` be a morphism of schemes over a field `k` with invertible relative differential
sheaves `Ω_{X/k}` and `Ω_{Y/k}`, where `X` is a proper integral curve over `k` with
finite-dimensional `H⁰(X, 𝒪_X)` and `H¹(X, 𝒪_X)` and `cotangentMap k f ≠ 0`. From the Picard-group
Riemann–Hurwitz relation `[Ω_{X/k}] = f^* [Ω_{Y/k}] · [𝒪_X(-R_f)]⁻¹`
(`mk_relativeDifferentials_eq_pullback_mul_inv_ramification`) and the degree of the effective
Cartier ramification divisor `R_f`, taking Euler-characteristic degrees yields:

`deg Ω_{X/k} = deg (f^* Ω_{Y/k}) + dim_k Γ(R_f, 𝒪_{R_f})`

(`eulerDegree_relativeDifferentials_eq_add_ramification_finrank`). When `f` is finite, flat, and
dominant onto a proper integral curve `Y` with finite-dimensional `H⁰(Y, 𝒪_Y)` and `H¹(Y, 𝒪_Y)`,
combining this with the pullback degree formula
(`LineBundleClass.eulerDegree_pullback_eq_finrank_functionField_mul`) gives the scheme-theoretic
degree Riemann–Hurwitz formula:

`deg Ω_{X/k} = [K(X) : f^* K(Y)] · deg Ω_{Y/k} + dim_k Γ(R_f, 𝒪_{R_f})`

(`eulerDegree_relativeDifferentials_eq_finrank_mul_add_ramification`).

## Main results

* `TauCeti.AlgebraicGeometry.eulerDegree_relativeDifferentials_eq_add_ramification_finrank`:
  `deg Ω_{X/k} = deg (f^* Ω_{Y/k}) + dim_k Γ(R_f, 𝒪_{R_f})`.
* `TauCeti.AlgebraicGeometry.eulerDegree_relativeDifferentials_eq_finrank_mul_add_ramification`:
  `deg Ω_{X/k} = [K(X) : f^* K(Y)] · deg Ω_{Y/k} + dim_k Γ(R_f, 𝒪_{R_f})` for finite flat dominant
  morphisms of proper integral curves.

## References

* [The Stacks Project, Tag 0C1B](https://stacks.math.columbia.edu/tag/0C1B)
* R. Hartshorne, *Algebraic Geometry*, Proposition IV.2.1 and Theorem IV.2.3
* H. Stichtenoth, *Algebraic Function Fields and Codes*, §3.4
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [IsIntegral X]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 0)]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
  [SheafOfModules.isInvertible X (X.relativeDifferentials k)]
  [SheafOfModules.isInvertible Y (Y.relativeDifferentials k)]

/-- **The Euler-characteristic degree Riemann–Hurwitz relation** on a proper integral curve `X`
over a field `k` with invertible `Ω_{X/k}` and `Ω_{Y/k}`, finite-dimensional `H⁰(X, 𝒪_X)` and
`H¹(X, 𝒪_X)`, and `cotangentMap k f ≠ 0`:
`deg Ω_{X/k} = deg (f^* Ω_{Y/k}) + dim_k Γ(R_f, 𝒪_{R_f})`. -/
theorem eulerDegree_relativeDifferentials_eq_add_ramification_finrank
    [IsProper (X ↘ Spec (.of k))] [RelativeDimensionLE 1 (X ↘ Spec (.of k))]
    (hf : cotangentMap k f ≠ 0) :
    InvertibleSheaf.eulerDegree k ⟨X.relativeDifferentials k, inferInstance⟩ =
      InvertibleSheaf.eulerDegree k
        ((InvertibleSheaf.pullback f).obj ⟨Y.relativeDifferentials k, inferInstance⟩) +
        (((ramificationIdealSheaf k f).subschemeι ≫
          X ↘ Spec (.of k)).finrank default : ℤ) := by
  have := mono_cotangentMap_of_ne_zero k f hf
  let hI := isEffectiveCartier_ramificationIdealSheaf k f
  have := hI.isFinite_subschemeι_comp (f := X ↘ Spec (.of k))
  rw [← LineBundleClass.eulerDegree_mk,
    mk_relativeDifferentials_eq_pullback_mul_inv_ramification k f]
  simp [-mk_toInvertibleSheaf_ramificationIdealSheaf, -LineBundleClass.inv_mk,
    hI.eulerDegree_toInvertibleSheaf k (ramificationIdealSheaf k f) default]

/-- **The Euler-characteristic degree Riemann–Hurwitz formula** for a finite flat dominant
morphism `f : X ⟶ Y` from an integral scheme `X` onto a proper integral curve `Y` over a field `k`,
assuming `Ω_{X/k}` and `Ω_{Y/k}` are invertible, `H⁰` and `H¹` of `𝒪_X` and `𝒪_Y` are
finite-dimensional over `k`, and `cotangentMap k f ≠ 0`:
`deg Ω_{X/k} = [K(X) : f^* K(Y)] · deg Ω_{Y/k} + dim_k Γ(R_f, 𝒪_{R_f})`. -/
theorem eulerDegree_relativeDifferentials_eq_finrank_mul_add_ramification
    [IsIntegral Y] [IsProper (Y ↘ Spec (.of k))] [RelativeDimensionLE 1 (Y ↘ Spec (.of k))]
    [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial Y).obj 0)]
    [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial Y).obj 1)]
    [IsFinite f] [Flat f] [IsDominant f] (hf : cotangentMap k f ≠ 0) :
    InvertibleSheaf.eulerDegree k ⟨X.relativeDifferentials k, inferInstance⟩ =
      Module.finrank f.functionFieldMap.hom.fieldRange X.functionField *
        InvertibleSheaf.eulerDegree k ⟨Y.relativeDifferentials k, inferInstance⟩ +
        (((ramificationIdealSheaf k f).subschemeι ≫
          X ↘ Spec (.of k)).finrank default : ℤ) := by
  have : IsProper (X ↘ Spec (.of k)) :=
    comp_over f (Spec (.of k)) ▸ inferInstanceAs (IsProper (f ≫ Y ↘ Spec (.of k)))
  have : RelativeDimensionLE 1 (X ↘ Spec (.of k)) := by
    rw [← comp_over f (Spec (.of k)), ← Nat.zero_add 1]
    infer_instance
  rw [eulerDegree_relativeDifferentials_eq_add_ramification_finrank k f hf,
    ← LineBundleClass.eulerDegree_mk, ← LineBundleClass.pullback_mk,
    LineBundleClass.eulerDegree_pullback_eq_finrank_functionField_mul k f,
    LineBundleClass.eulerDegree_mk]

end TauCeti.AlgebraicGeometry

end
