/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Gradient

/-!
# Directional and Fréchet derivatives of symmetric-algebra polynomial evaluations

Let `𝕜` be a nontrivially normed field and `M` a `𝕜`-vector space equipped with a finite basis `b`.
Every symmetric tensor `p : SymmetricAlgebra 𝕜 M` defines a polynomial function
`ξ ↦ SymmetricAlgebra.lift ξ p` on the algebraic dual `Module.Dual 𝕜 M` and, when `E` is a normed
`𝕜`-vector space, a function `η ↦ SymmetricAlgebra.lift η.toLinearMap p` on the continuous dual
`StrongDual 𝕜 E`.

This module establishes the ordinary calculus formulas identifying the directional derivative along
an affine line `t ↦ ξ + t • η` and the Fréchet derivative on `StrongDual 𝕜 E` with the algebraic
gradient `b.symmetricGradient p`, without depending on manifold infrastructure.

## Main results

* `Module.Basis.hasDerivAt_lift_add_smul`, `Module.Basis.hasDerivAt_lift_add_smul_zero`,
  `Module.Basis.deriv_lift_add_smul`, `Module.Basis.deriv_lift_add_smul_zero`: directional
  derivative of `t ↦ SymmetricAlgebra.lift (ξ + t • η) p` along an affine line in
  `Module.Dual 𝕜 M`.
* `Module.Basis.hasFDerivAt_lift`: Fréchet derivative at `ξ : StrongDual 𝕜 E` of
  `η ↦ SymmetricAlgebra.lift η.toLinearMap p`, identified via `ContinuousLinearMap.apply` with
  `b.symmetricGradient p ξ.toLinearMap`.

## References

* J. E. Marsden and T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Springer
  (1999), §10.1 (functional derivatives of polynomial functions on the dual of a Lie algebra).
-/

public section

namespace Module.Basis

section AffineLineDeriv

variable {𝕜 M ι : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup M] [Module 𝕜 M] [Fintype ι]

/-- **Directional derivative along an affine line of linear forms.** For a finite basis `b` of `M`,
the derivative at `t₀` of `t ↦ SymmetricAlgebra.lift (ξ + t • η) p` is `η` paired with
`b.symmetricGradient p (ξ + t₀ • η)`. -/
theorem hasDerivAt_lift_add_smul (b : Module.Basis ι 𝕜 M) (p : SymmetricAlgebra 𝕜 M)
    (ξ η : Module.Dual 𝕜 M) (t₀ : 𝕜) :
    HasDerivAt (fun t : 𝕜 ↦ SymmetricAlgebra.lift (ξ + t • η) p)
      (η (b.symmetricGradient p (ξ + t₀ • η))) t₀ := by
  induction p using SymmetricAlgebra.induction with
  | algebraMap r =>
    rw [b.symmetricGradient_algebraMap, map_zero]
    simpa only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using
      hasDerivAt_const t₀ r
  | ι x =>
    rw [b.symmetricGradient_ι]
    simpa only [SymmetricAlgebra.lift_ι_apply, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, one_mul, id_eq] using ((hasDerivAt_id t₀).mul_const (η x)).const_add (ξ x)
  | add p q hp hq =>
    rw [b.symmetricGradient_add, map_add]
    simpa only [map_add] using hp.fun_add hq
  | mul p q hp hq =>
    have hmul := hp.fun_mul hq
    simp only [← map_mul] at hmul
    convert hmul using 1
    rw [b.symmetricGradient_mul, map_add, LinearMap.map_smul, LinearMap.map_smul, smul_eq_mul,
      smul_eq_mul]
    ring

/-- At `t = 0`, the directional derivative of `t ↦ SymmetricAlgebra.lift (ξ + t • η) p` is
`η (b.symmetricGradient p ξ)`. -/
theorem hasDerivAt_lift_add_smul_zero (b : Module.Basis ι 𝕜 M) (p : SymmetricAlgebra 𝕜 M)
    (ξ η : Module.Dual 𝕜 M) :
    HasDerivAt (fun t : 𝕜 ↦ SymmetricAlgebra.lift (ξ + t • η) p)
      (η (b.symmetricGradient p ξ)) 0 := by
  simpa using b.hasDerivAt_lift_add_smul p ξ η 0

/-- The derivative at `t₀` of `t ↦ SymmetricAlgebra.lift (ξ + t • η) p` is
`η (b.symmetricGradient p (ξ + t₀ • η))`. -/
theorem deriv_lift_add_smul (b : Module.Basis ι 𝕜 M) (p : SymmetricAlgebra 𝕜 M)
    (ξ η : Module.Dual 𝕜 M) (t₀ : 𝕜) :
    deriv (fun t : 𝕜 ↦ SymmetricAlgebra.lift (ξ + t • η) p) t₀ =
      η (b.symmetricGradient p (ξ + t₀ • η)) :=
  (b.hasDerivAt_lift_add_smul p ξ η t₀).deriv

/-- The derivative at `0` of `t ↦ SymmetricAlgebra.lift (ξ + t • η) p` is
`η (b.symmetricGradient p ξ)`. -/
theorem deriv_lift_add_smul_zero (b : Module.Basis ι 𝕜 M) (p : SymmetricAlgebra 𝕜 M)
    (ξ η : Module.Dual 𝕜 M) :
    deriv (fun t : 𝕜 ↦ SymmetricAlgebra.lift (ξ + t • η) p) 0 =
      η (b.symmetricGradient p ξ) :=
  (b.hasDerivAt_lift_add_smul_zero p ξ η).deriv

end AffineLineDeriv

section FDeriv

variable {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [Fintype ι]

/-- **Fréchet derivative of polynomial evaluation on `StrongDual 𝕜 E`.** Under the biduality map
`ContinuousLinearMap.apply 𝕜 𝕜`, the Fréchet derivative at `ξ` of
`η ↦ SymmetricAlgebra.lift η.toLinearMap p` is `b.symmetricGradient p ξ.toLinearMap`. -/
theorem hasFDerivAt_lift (b : Module.Basis ι 𝕜 E) (p : SymmetricAlgebra 𝕜 E)
    (ξ : StrongDual 𝕜 E) :
    HasFDerivAt (fun η : StrongDual 𝕜 E ↦ SymmetricAlgebra.lift η.toLinearMap p)
      (ContinuousLinearMap.apply 𝕜 𝕜 (b.symmetricGradient p ξ.toLinearMap)) ξ := by
  induction p using SymmetricAlgebra.induction with
  | algebraMap r =>
    rw [b.symmetricGradient_algebraMap, map_zero]
    simpa only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using
      hasFDerivAt_const r ξ
  | ι x =>
    rw [b.symmetricGradient_ι]
    simp_rw [SymmetricAlgebra.lift_ι_apply, ContinuousLinearMap.coe_coe]
    exact (ContinuousLinearMap.apply 𝕜 𝕜 x : StrongDual 𝕜 E →L[𝕜] 𝕜).hasFDerivAt
  | add p q hp hq =>
    rw [b.symmetricGradient_add, map_add]
    simpa only [map_add] using hp.fun_add hq
  | mul p q hp hq =>
    rw [b.symmetricGradient_mul, map_add, map_smul, map_smul]
    simpa only [map_mul] using hp.fun_mul hq

end FDeriv

end Module.Basis
