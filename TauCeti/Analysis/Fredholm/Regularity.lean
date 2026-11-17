/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.LinearMap.Index
public import TauCeti.Analysis.Fredholm.ClosedRange
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
public import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Fredholm operators on a scale of spaces and regularity

Let `T : E → F` be a Fredholm operator and `T' : E' → F'` a continuous linear map, related by
injective linear maps `i : E' → E` and `j : F' → F` with `T (i x) = j (T' x)`. The model is an
elliptic operator `P` of order `m` on a compact manifold, with `T = P : H^(s+m) → H^s`,
`T' = P : H^(t+m) → H^t` for `t > s`, and `i`, `j` the inclusions of Sobolev spaces. Assume
* the *regularity property*: if `T x = j y`, then `x = i x'` for some `x'`
  (elliptic regularity: `u ∈ H^(s+m)` and `Pu ∈ H^t` give `u ∈ H^(t+m)`), and
* `j` has dense range.

Then `i` identifies the kernels of `T'` and `T` (`LinearMap.kerEquivOfRegularity`), `j`
identifies their cokernels (`LinearMap.cokerEquivOfRegularity`), the two indices agree, and `T'`
is Fredholm too when it acts between real or complex Banach spaces. Applied to an elliptic
operator, once elliptic regularity and the Fredholm property of `P : H^(s+m) → H^s` are available,
this shows that its kernel, cokernel and index do not depend on `s`. Density of `j`
enters only through the cokernel: the range of `T` is closed of finite codimension, so together
with the dense range of `j` it spans `F` (`ContinuousLinearMap.IsFredholm.range_sup_range_eq_top`),
and the algebraic comparison `LinearMap.cokerEquivOfRegularity` applies.

## Main declarations

* `ContinuousLinearMap.IsFredholm.range_sup_range_eq_top`: the range of a Fredholm operator and a
  dense subspace together span the target, so the cokernel is represented by elements of any
  dense subspace.
* `ContinuousLinearMap.IsFredholm.index_eq_of_regularity`: the indices of `T'` and `T` agree.
* `ContinuousLinearMap.IsFredholm.of_regularity`: between real or complex Banach spaces, `T'` is
  Fredholm.

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §6, pp. 517–519 (independence of the index from the Sobolev order).
-/

public section

namespace ContinuousLinearMap

open Module

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E E' F F' : Type*}
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul 𝕜 F]
variable {T : E →L[𝕜] F}

section Module

variable [AddCommGroup E'] [Module 𝕜 E'] [AddCommGroup F'] [Module 𝕜 F']
variable {i : E' →ₗ[𝕜] E} {j : F' →ₗ[𝕜] F}

/-- The range of a Fredholm operator `T : E → F` and the range of a linear map with dense range
together span `F`. -/
theorem IsFredholm.range_sup_range_eq_top (hT : IsFredholm T) (hj : DenseRange j) :
    LinearMap.range (T : E →ₗ[𝕜] F) ⊔ LinearMap.range j = ⊤ :=
  have := hT.finite_coker
  Submodule.sup_eq_top_of_dense hT.isClosed_range (by rwa [LinearMap.coe_range])

/-- **Independence of the index from the regularity level.** Let `T` be Fredholm and
`T (i x) = j (T' x)` with `i` and `j` injective, `j` of dense range, and `T x = j y` only when `x`
is in the range of `i`. Then `T'` has the same index as `T`. -/
theorem IsFredholm.index_eq_of_regularity [TopologicalSpace E'] [TopologicalSpace F']
    {T' : E' →L[𝕜] F'} (hT : IsFredholm T)
    (hcomm : ∀ x, T (i x) = j (T' x)) (hi : Function.Injective i) (hj : Function.Injective j)
    (hjd : DenseRange j) (hreg : ∀ x y, T x = j y → ∃ x', i x' = x) :
    T'.index = T.index := by
  rw [index_def, index_def]
  exact LinearMap.index_eq_of_regularity hcomm hi hj hreg (hT.range_sup_range_eq_top hjd)

end Module

section Banach

variable [IsRCLikeNormedField 𝕜]
variable [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [CompleteSpace E']
variable [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [CompleteSpace F']
variable {T' : E' →L[𝕜] F'} {i : E' →ₗ[𝕜] E} {j : F' →ₗ[𝕜] F}

/-- **Fredholm property at a higher regularity level.** Let `T` be Fredholm and
`T (i x) = j (T' x)` with `i` and `j` injective, `j` of dense range, and `T x = j y` only when `x`
is in the range of `i`. If `T'` acts between real or complex Banach spaces, then it is
Fredholm. -/
theorem IsFredholm.of_regularity (hT : IsFredholm T)
    (hcomm : ∀ x, T (i x) = j (T' x)) (hi : Function.Injective i) (hj : Function.Injective j)
    (hjd : DenseRange j) (hreg : ∀ x y, T x = j y → ∃ x', i x' = x) :
    IsFredholm T' :=
  have := hT.finite_ker
  have : FiniteDimensional 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F)) := hT.finite_coker
  .of_finite_ker_coker T' (LinearMap.kerEquivOfRegularity hcomm hi hj hreg).symm.finiteDimensional
    (LinearMap.cokerEquivOfRegularity hcomm hj hreg
      (hT.range_sup_range_eq_top hjd)).symm.finiteDimensional

end Banach

end ContinuousLinearMap
