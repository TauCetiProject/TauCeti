/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Analysis.Fredholm.ConstantNullity
public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.RangeProjection
import TauCeti.Analysis.Calculus.FDeriv.SecondOrderIdentity

/-!
# Orthogonal kernel projections and right inverses of Fredholm families

Let `T x : E →L[𝕜] F` be a family of operators between Banach spaces over `ℝ` or `ℂ`, continuous
in a parameter `x` and Fredholm at `x₀`, and let `ι : E →L[𝕜] H` be an injective operator into a
Hilbert space. Typically `E` is a Sobolev space of sections and `ι` its inclusion into `L²`, so
that `⟪ι e, ι e'⟫` is the `L²` pairing on `E`, for whose norm `E` is in general not complete.
Near every parameter where the kernel of `T x` has the dimension of that of `T x₀`, the kernel
has a projection along its `ι`-orthogonal complement, and when `T x₀` is onto, the operators `T x`
near `x₀` have right inverses with values in that complement. This file shows that both depend
continuously on `x`.

The kernels move continuously by
`ContinuousLinearMap.IsFredholm.exists_continuousOn_ker_parametrization`: there is a continuous
family `κ x : ker (T x₀) →L[𝕜] E` whose range is `ker (T x)` at the parameters of constant
nullity. Reading `κ x` on `V = EuclideanSpace 𝕜 (Fin (finrank 𝕜 (T x₀).ker))` through a linear
equivalence, so that the Gram operator is defined, and with `A = ι ∘ κ x`, the projection is

`π x = κ x (A† A)⁻¹ A† ι`

(`ContinuousLinearMap.gramProjection`), where the Gram operator `A† A` of `V` is invertible as
long as `A` is injective, which is an open condition. Since inversion is continuous on the units of
the complete normed ring `V →L[𝕜] V`, `π x` is continuous in `x`. It fixes `ker (T x)` and
`ι (e - π x e)` is orthogonal to `ι (ker (T x))`. When `T x₀` is onto, so is every `T x` near
`x₀`, with a continuous family of right inverses `R x`
(`ContinuousLinearMap.IsFredholm.exists_continuousOn_splitting`), and `Q x = (1 - π x) R x` is
the right inverse with values in the `ι`-orthogonal complement of the kernel. Every `e ∈ E` then
splits as `e = π x e + Q x (T x e)`.

Over `ℝ`, a `C^n` family has `C^n` projections and right inverses, since the adjoint is a real
continuous linear map of operators (`ContinuousLinearMap.adjointRealCLM`) and inversion is
analytic. Over `ℂ` the projection depends on `κ x` conjugate-linearly as well, so it is not
complex-differentiable, and the `C^n` statements are made for real families.

For the gauge-fixed operator of a plane vortex or of the linearized Seiberg–Witten equations on
a Sobolev space, these are the kernel projections and right inverses on `L²`-orthogonal
complements of the kernel, which move continuously with the solution about which one linearizes.

Their derivatives are determined by differentiating the defining identities. Let `T` be a real
family, differentiable at `x₀`, with `T x₀` Fredholm and onto, write `π x` and `Q x` for the
orthogonal kernel projection and right inverse of `T x`, and `T'`, `π'`, `Q'` for the derivatives
of `T`, `π`, `Q` at `x₀` along a direction `v`, with `π = π x₀` and `Q = Q x₀`. Differentiating
`T x ∘ π x = 0` and `T x ∘ Q x = 1` gives `T x₀ ∘ π' = -T' ∘ π` and `T x₀ ∘ Q' = -T' ∘ Q`, so the
components of `π' e` and `Q' y` in the `ι`-orthogonal complement of `ker (T x₀)` are `-Q T' π e`
and `-Q T' Q y`. Differentiating the orthogonality relations gives their kernel components through
the pairings

`⟪ι (π' e), ι k⟫ = -⟪ι (e - π e), ι (Q (T' k))⟫`,  `⟪ι (Q' y), ι k⟫ = ⟪ι (Q y), ι (Q (T' k))⟫`

for `k ∈ ker (T x₀)`, and these two conditions characterize `π' e` and `Q' y`. No adjoint of `T'`
or `Q` with respect to the `ι`-pairing is needed, which matters when `E` is a Sobolev space and
the pairing is the `L²` pairing. These are the differentiated identities through which estimates
on kernel projections and right inverses along a family of operators, such as the linearizations
at a smooth family of plane vortices, pass to their parameter derivatives.

For a family `C²` at `x₀`, differentiating these identities once more gives the second
derivatives `π''` and `Q''`, the derivatives along `w` of `x ↦ π'_v(x)` and `x ↦ Q'_v(x)`. With
`T''` the derivative along `w` of `x ↦ T'_v(x)`, their components in the `ι`-orthogonal complement
of the kernel are `-Q (T'' (π e) + T'_v (π'_w e) + T'_w (π'_v e))` and
`-Q (T'' (Q y) + T'_v (Q'_w y) + T'_w (Q'_v y))`, and their kernel components are determined by

`⟪ι (π'' e), ι k⟫ = -⟪ι (e - π e), ι (Q (T'' k + T'_v (π'_w k) + T'_w (π'_v k)))⟫`
`  - ⟪ι (π'_v e), ι (π'_w k)⟫ - ⟪ι (π'_w e), ι (π'_v k)⟫`,
`⟪ι (Q'' y), ι k⟫ = ⟪ι (Q y), ι (Q (T'' k + T'_v (π'_w k) + T'_w (π'_v k)))⟫`
`  - ⟪ι (Q'_v y), ι (π'_w k)⟫ - ⟪ι (Q'_w y), ι (π'_v k)⟫`.

Second derivatives are stated as derivatives of first derivatives applied to fixed vectors, such
as `fderiv ℝ (fun x ↦ fderiv ℝ Q x v y) x₀ w`, which take values in `E` or `F`.

When `F` is a Hilbert space as well, `ι ∘ Q x` is an operator between Hilbert spaces with an
adjoint `(ι ∘ Q x)†`, formally the operator `(T x T x*)⁻¹ T x` on `H`. On the `ι`-orthogonal
complement of `ker (T x₀)` the derivative of these adjoints is
`(ι ∘ Q')† g = -(T' ∘ Q)† ((ι ∘ Q)† g)`: the kernel component of `Q' y` pairs to zero with such a
`g`, and the complement component is `-Q T' Q y`.

## Main results

* `ContinuousLinearMap.rightInverse_sub_comp` and
  `ContinuousLinearMap.apply_add_apply_apply_eq_self`: for a single operator `T` and `π` with
  values in its kernel, `R - π R` is a right inverse of `T` whenever `R` is, and when `π` projects
  along the `ι`-orthogonal complement of the kernel, a right inverse `Q` with values in that
  complement splits every `e` as `e = π e + Q (T e)`.
* `ContinuousLinearMap.eq_zero_of_mem_ker_of_forall_inner_eq_zero`: an element of the kernel
  `ι`-orthogonal to the kernel vanishes.
* `ContinuousLinearMap.IsOrthogonalKerProjection.inner_apply_comm`: the orthogonal kernel
  projection is symmetric for the `ι`-pairing, `⟪ι (π e), ι e'⟫ = ⟪ι e, ι (π e')⟫`.
* `ContinuousLinearMap.apply_eq_of_ker_projection_conj` and
  `ContinuousLinearMap.apply_eq_of_rightInverse_conj`: an equivalence `e` carrying the kernel of
  `T` to that of `T'` and the `ι`-pairing to the `ι'`-pairing conjugates the orthogonal kernel
  projections and right inverses, `π' (e y) = e (π y)` and `Q' (σ f) = e (Q f)` when
  `T' ∘ e = σ ∘ T`. With `e` the identity, this is their uniqueness.
* `ContinuousLinearMap.IsOrthogonalKerProjection.unique` and
  `ContinuousLinearMap.IsOrthogonalRightInverse.unique`: the projection onto the kernel along its
  `ι`-orthogonal complement, and the right inverse with values in that complement, are unique.
  They are named `ContinuousLinearMap.orthogonalKerProjection ι T` and
  `ContinuousLinearMap.orthogonalRightInverse ι T`.
* `ContinuousLinearMap.isOrthogonalKerProjection_orthogonalKerProjection` and
  `ContinuousLinearMap.IsFredholm.isOrthogonalRightInverse_orthogonalRightInverse`: they exist
  when the kernel is finite-dimensional, respectively when `T` is Fredholm and onto.
* `ContinuousLinearMap.IsFredholm.sub_orthogonalKerProjection_apply`: for `T` Fredholm and onto,
  the component of `e` in the `ι`-orthogonal complement of the kernel is `e - π e = Q (T e)`.
* `ContinuousLinearMap.IsFredholm.continuousAt_orthogonalKerProjection` and
  `ContinuousLinearMap.IsFredholm.continuousAt_orthogonalRightInverse`: they are continuous in `T`
  at every Fredholm operator that is onto.
* `ContinuousLinearMap.IsFredholm.exists_continuousOn_orthogonal_ker_projection`: continuous
  projections onto the kernels along their `ι`-orthogonal complements, at the parameters of
  constant nullity.
* `ContinuousLinearMap.IsFredholm.exists_continuousOn_orthogonal_rightInverse`: for a family onto
  at `x₀`, continuous kernel projections and right inverses near `x₀`, with values in the
  `ι`-orthogonal complements of the kernels, splitting `E` as `ker (T x) ⊕ Q x F`.
* `ContinuousLinearMap.IsFredholm.exists_contDiffOn_orthogonal_ker_projection` and
  `ContinuousLinearMap.IsFredholm.exists_contDiffOn_orthogonal_rightInverse`: the same for a
  real `C^n` family, with `C^n` projections and right inverses.
* `ContinuousLinearMap.IsFredholm.contDiffAt_orthogonalKerProjection` and
  `ContinuousLinearMap.IsFredholm.contDiffAt_orthogonalRightInverse`: over `ℝ`, the orthogonal
  kernel projection and right inverse are `C^n` functions of the operator at every Fredholm
  operator that is onto.
* `ContinuousLinearMap.IsFredholm.eventually_isOrthogonalKerProjection_and_isOrthogonalRightInverse`
  says that near a Fredholm operator that is onto, every operator has its orthogonal kernel
  projection and right inverse.
* `ContinuousLinearMap.IsFredholm.apply_fderiv_orthogonalKerProjection_apply`,
  `ContinuousLinearMap.IsFredholm.sub_orthogonalKerProjection_fderiv_orthogonalKerProjection_apply`,
  `ContinuousLinearMap.IsFredholm.inner_fderiv_orthogonalKerProjection_apply` and
  `ContinuousLinearMap.IsFredholm.fderiv_orthogonalKerProjection_apply_eq_iff`: the derivative of
  the orthogonal kernel projections along a real family, through `T x₀ ∘ π' = -T' ∘ π`, its
  splitting and its kernel pairings, which characterize it.
* `ContinuousLinearMap.IsFredholm.apply_fderiv_orthogonalRightInverse_apply`,
  `ContinuousLinearMap.IsFredholm.sub_orthogonalKerProjection_fderiv_orthogonalRightInverse_apply`,
  `ContinuousLinearMap.IsFredholm.inner_fderiv_orthogonalRightInverse_apply` and
  `ContinuousLinearMap.IsFredholm.fderiv_orthogonalRightInverse_apply_eq_iff`: the same for the
  orthogonal right inverses.
* `ContinuousLinearMap.IsFredholm.apply_fderiv_fun_fderiv_orthogonalKerProjection_apply`,
  `IsFredholm.sub_orthogonalKerProjection_fderiv_fun_fderiv_orthogonalKerProjection_apply` and
  `ContinuousLinearMap.IsFredholm.inner_fderiv_fun_fderiv_orthogonalKerProjection_apply`: the
  second derivative of the orthogonal kernel projections along a real `C²` family, through
  `T x₀ ∘ π''`, its complement component and its kernel pairings.
* `ContinuousLinearMap.IsFredholm.apply_fderiv_fun_fderiv_orthogonalRightInverse_apply`,
  `IsFredholm.sub_orthogonalKerProjection_fderiv_fun_fderiv_orthogonalRightInverse_apply` and
  `ContinuousLinearMap.IsFredholm.inner_fderiv_fun_fderiv_orthogonalRightInverse_apply`: the
  same for the orthogonal right inverses.
* `ContinuousLinearMap.IsFredholm.adjoint_comp_fderiv_orthogonalRightInverse_apply`: on the
  `ι`-orthogonal complement of the kernel, the derivative of the adjoints `(ι ∘ Q x)†` is
  `-(T' ∘ Q)† ∘ (ι ∘ Q)†`.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, second edition, Springer, 1976,
  Chapter IV, §5 (stability of the nullity and of the kernel under small perturbations).
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix A.2 (Fredholm families and their kernels).
-/

public section

open Function Module Set Topology Filter
open scoped InnerProductSpace

namespace ContinuousLinearMap

section SingleOperator

variable {𝕜 E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- If `π` takes values in the kernel of `T` and `R` is a right inverse of `T`, then so is
`R - π R`. -/
theorem rightInverse_sub_comp [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [IsTopologicalAddGroup E] [AddCommGroup F] [Module 𝕜 F]
    {T : E →L[𝕜] F} {π : E →L[𝕜] E} {R : F →L[𝕜] E}
    (hmem : ∀ e, π e ∈ T.ker) (hR : RightInverse R T) : RightInverse (R - π ∘L R) T := fun y ↦ by
  have h0 : T (π (R y)) = 0 := LinearMap.mem_ker.1 (hmem (R y))
  simp [hR y, h0]

/-- Let `ι` be an injective operator into an inner product space. An element of the kernel of `T`
whose image under `ι` is orthogonal to `ι` of the kernel vanishes. -/
theorem eq_zero_of_mem_ker_of_forall_inner_eq_zero {H : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    {ι : E →L[𝕜] H} (hι : Injective ι) {T : E →L[𝕜] F} {w : E} (hw : w ∈ T.ker)
    (h : ∀ k ∈ T.ker, ⟪ι w, ι k⟫_𝕜 = 0) : w = 0 :=
  hι ((inner_self_eq_zero.1 (h w hw)).trans (map_zero ι).symm)

/-- Let `ι` be an injective operator into an inner product space, let `π` take values in the kernel
of `T` with `ι (e - π e)` orthogonal to `ι` of the kernel, and let `Q` be a right inverse of `T`
whose values are `ι`-orthogonal to the kernel. Then every `e` splits as `e = π e + Q (T e)`. -/
theorem apply_add_apply_apply_eq_self {H : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    {ι : E →L[𝕜] H} (hι : Injective ι) {T : E →L[𝕜] F}
    {π : E →L[𝕜] E} {Q : F →L[𝕜] E} (hmem : ∀ e, π e ∈ T.ker)
    (horth : ∀ e, ∀ k ∈ T.ker, ⟪ι (e - π e), ι k⟫_𝕜 = 0) (hQ : RightInverse Q T)
    (hQorth : ∀ y, ∀ k ∈ T.ker, ⟪ι (Q y), ι k⟫_𝕜 = 0) (e : E) : π e + Q (T e) = e := by
  -- The defect `d = e - π e - Q (T e)` lies in the kernel and is `ι`-orthogonal to it.
  set d := e - π e - Q (T e)
  have h0 : T (π e) = 0 := LinearMap.mem_ker.1 (hmem e)
  have hd : d ∈ T.ker := by
    simp [d, hQ (T e), h0]
  have : d = 0 := eq_zero_of_mem_ker_of_forall_inner_eq_zero hι hd fun k hk ↦ by
    rw [map_sub, inner_sub_left, horth e k hk, hQorth _ k hk, sub_zero]
  exact (sub_eq_zero.1 (by simpa only [d, sub_sub] using this)).symm

section Orthogonal

variable {H : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {ι : E →L[𝕜] H} {T : E →L[𝕜] F}

/-- `π` is the projection onto the kernel of `T` along its `ι`-orthogonal complement: it takes
values in the kernel, and `ι (e - π e)` is orthogonal to `ι k` for every `k` in the kernel. -/
structure IsOrthogonalKerProjection (ι : E →L[𝕜] H) (T : E →L[𝕜] F) (π : E →L[𝕜] E) : Prop where
  /-- The projection takes values in the kernel. -/
  mem_ker : ∀ e, π e ∈ T.ker
  /-- The projection is along the `ι`-orthogonal complement of the kernel. -/
  inner_sub_eq_zero : ∀ e, ∀ k ∈ T.ker, ⟪ι (e - π e), ι k⟫_𝕜 = 0

/-- `Q` is a right inverse of `T` whose values are `ι`-orthogonal to the kernel of `T`. -/
structure IsOrthogonalRightInverse (ι : E →L[𝕜] H) (T : E →L[𝕜] F) (Q : F →L[𝕜] E) : Prop where
  /-- `Q` is a right inverse of `T`. -/
  rightInverse : RightInverse Q T
  /-- The values of `Q` are `ι`-orthogonal to the kernel. -/
  inner_eq_zero : ∀ y, ∀ k ∈ T.ker, ⟪ι (Q y), ι k⟫_𝕜 = 0

/-- **Uniqueness of the orthogonal kernel projection.** For an injective `ι` into an inner product
space, two projections onto the kernel of `T` along its `ι`-orthogonal complement agree. -/
theorem IsOrthogonalKerProjection.unique (hι : Injective ι) {π π' : E →L[𝕜] E}
    (h : IsOrthogonalKerProjection ι T π) (h' : IsOrthogonalKerProjection ι T π') : π = π' := by
  ext e
  refine sub_eq_zero.1 (eq_zero_of_mem_ker_of_forall_inner_eq_zero hι
    (T.ker.sub_mem (h.mem_ker e) (h'.mem_ker e)) fun k hk ↦ ?_)
  have hd : π e - π' e = (e - π' e) - (e - π e) := by abel
  rw [hd, map_sub, inner_sub_left, h'.inner_sub_eq_zero e k hk, h.inner_sub_eq_zero e k hk,
    sub_zero]

/-- The orthogonal kernel projection fixes the kernel, for an injective `ι`. -/
theorem IsOrthogonalKerProjection.apply_of_mem_ker (hι : Injective ι) {π : E →L[𝕜] E}
    (h : IsOrthogonalKerProjection ι T π) {k : E} (hk : k ∈ T.ker) : π k = k :=
  (sub_eq_zero.1 (eq_zero_of_mem_ker_of_forall_inner_eq_zero hι
    (T.ker.sub_mem hk (h.mem_ker k)) (h.inner_sub_eq_zero k))).symm

/-- Pairing with the orthogonal kernel projection gives its squared norm:
`⟪ι e, ι (π e)⟫ = ‖ι (π e)‖²`, since `ι (e - π e)` is orthogonal to `ι (π e)`. -/
theorem IsOrthogonalKerProjection.inner_apply_eq_norm_sq {π : E →L[𝕜] E}
    (h : IsOrthogonalKerProjection ι T π) (e : E) :
    ⟪ι e, ι (π e)⟫_𝕜 = (‖ι (π e)‖ : 𝕜) ^ 2 := by
  have h₀ := h.inner_sub_eq_zero e (π e) (h.mem_ker e)
  rw [map_sub, inner_sub_left, sub_eq_zero] at h₀
  rw [h₀, inner_self_eq_norm_sq_to_K]

/-- The real form of `IsOrthogonalKerProjection.inner_apply_eq_norm_sq`, without the coercion:
`⟪ι e, ι (π e)⟫_ℝ = ‖ι (π e)‖²`. -/
theorem IsOrthogonalKerProjection.real_inner_apply_eq_norm_sq [Module ℝ E] [Module ℝ F]
    [InnerProductSpace ℝ H] {ι : E →L[ℝ] H} {T : E →L[ℝ] F} {π : E →L[ℝ] E}
    (h : IsOrthogonalKerProjection ι T π) (e : E) : ⟪ι e, ι (π e)⟫_ℝ = ‖ι (π e)‖ ^ 2 := by
  simpa only [RCLike.ofReal_real_eq_id, id_eq] using h.inner_apply_eq_norm_sq e

/-- **An orthogonal kernel projection is symmetric for the `ι`-pairing:**
`⟪ι (π e), ι e'⟫ = ⟪ι e, ι (π e')⟫`, both sides being `⟪ι (π e), ι (π e')⟫`. -/
theorem IsOrthogonalKerProjection.inner_apply_comm {π : E →L[𝕜] E}
    (h : IsOrthogonalKerProjection ι T π) (e e' : E) : ⟪ι (π e), ι e'⟫_𝕜 = ⟪ι e, ι (π e')⟫_𝕜 := by
  have h₁ := h.inner_sub_eq_zero e' (π e) (h.mem_ker e)
  have h₂ := h.inner_sub_eq_zero e (π e') (h.mem_ker e')
  rw [map_sub, inner_sub_left, sub_eq_zero] at h₁ h₂
  rw [h₂, ← inner_conj_symm, h₁, inner_conj_symm]

/-- **Uniqueness of the orthogonal right inverse.** For an injective `ι` into an inner product
space, two right inverses of `T` whose values are `ι`-orthogonal to the kernel of `T` agree. -/
theorem IsOrthogonalRightInverse.unique (hι : Injective ι) {Q Q' : F →L[𝕜] E}
    (h : IsOrthogonalRightInverse ι T Q) (h' : IsOrthogonalRightInverse ι T Q') : Q = Q' := by
  ext y
  refine sub_eq_zero.1 (eq_zero_of_mem_ker_of_forall_inner_eq_zero (T := T) hι
    (LinearMap.mem_ker.2 (by simp [h.rightInverse y, h'.rightInverse y])) fun k hk ↦ ?_)
  rw [map_sub, inner_sub_left, h.inner_eq_zero y k hk, h'.inner_eq_zero y k hk, sub_zero]

/-- **The orthogonal splitting.** For an injective `ι`, if `π` is the projection onto the kernel
of `T` along its `ι`-orthogonal complement and `Q` is a right inverse of `T` with values in that
complement, then every `e` splits as `e = π e + Q (T e)`. -/
theorem IsOrthogonalKerProjection.apply_add_apply_apply_eq_self (hι : Injective ι)
    {π : E →L[𝕜] E} {Q : F →L[𝕜] E} (hπ : IsOrthogonalKerProjection ι T π)
    (hQ : IsOrthogonalRightInverse ι T Q) (e : E) : π e + Q (T e) = e :=
  ContinuousLinearMap.apply_add_apply_apply_eq_self hι hπ.mem_ker hπ.inner_sub_eq_zero
    hQ.rightInverse hQ.inner_eq_zero e

open Classical in
/-- **The orthogonal kernel projection** of `T` for `ι`: the projection onto the kernel of `T`
along its `ι`-orthogonal complement. It is unique for an injective `ι`
(`ContinuousLinearMap.IsOrthogonalKerProjection.unique`) and exists when the kernel is
finite-dimensional
(`ContinuousLinearMap.isOrthogonalKerProjection_orthogonalKerProjection`); it is `0` when no
such projection exists. -/
noncomputable def orthogonalKerProjection (ι : E →L[𝕜] H) (T : E →L[𝕜] F) : E →L[𝕜] E :=
  if h : ∃ π, IsOrthogonalKerProjection ι T π then h.choose else 0

open Classical in
/-- **The orthogonal right inverse** of `T` for `ι`: the right inverse of `T` whose values are
`ι`-orthogonal to the kernel of `T`. It is unique for an injective `ι`
(`ContinuousLinearMap.IsOrthogonalRightInverse.unique`) and exists when `T` is Fredholm and onto
(`ContinuousLinearMap.IsFredholm.isOrthogonalRightInverse_orthogonalRightInverse`); it is `0`
when no such right inverse exists. -/
noncomputable def orthogonalRightInverse (ι : E →L[𝕜] H) (T : E →L[𝕜] F) : F →L[𝕜] E :=
  if h : ∃ Q, IsOrthogonalRightInverse ι T Q then h.choose else 0

/-- Whenever a projection onto the kernel along its `ι`-orthogonal complement exists,
`ContinuousLinearMap.orthogonalKerProjection ι T` is one. -/
theorem IsOrthogonalKerProjection.isOrthogonalKerProjection_orthogonalKerProjection
    {π : E →L[𝕜] E} (h : IsOrthogonalKerProjection ι T π) :
    IsOrthogonalKerProjection ι T (orthogonalKerProjection ι T) := by
  have he : ∃ π, IsOrthogonalKerProjection ι T π := ⟨π, h⟩
  rw [orthogonalKerProjection, dite_eq_left_of_eq_true (eq_true he)]
  exact he.choose_spec

/-- Whenever a right inverse with values `ι`-orthogonal to the kernel exists,
`ContinuousLinearMap.orthogonalRightInverse ι T` is one. -/
theorem IsOrthogonalRightInverse.isOrthogonalRightInverse_orthogonalRightInverse
    {Q : F →L[𝕜] E} (h : IsOrthogonalRightInverse ι T Q) :
    IsOrthogonalRightInverse ι T (orthogonalRightInverse ι T) := by
  have he : ∃ Q, IsOrthogonalRightInverse ι T Q := ⟨Q, h⟩
  rw [orthogonalRightInverse, dite_eq_left_of_eq_true (eq_true he)]
  exact he.choose_spec

/-- For an injective `ι`, a projection onto the kernel of `T` along its `ι`-orthogonal complement
is `ContinuousLinearMap.orthogonalKerProjection ι T`. -/
theorem IsOrthogonalKerProjection.eq_orthogonalKerProjection (hι : Injective ι) {π : E →L[𝕜] E}
    (h : IsOrthogonalKerProjection ι T π) : π = orthogonalKerProjection ι T :=
  h.unique hι h.isOrthogonalKerProjection_orthogonalKerProjection

/-- For an injective `ι`, a right inverse of `T` with values `ι`-orthogonal to the kernel is
`ContinuousLinearMap.orthogonalRightInverse ι T`. -/
theorem IsOrthogonalRightInverse.eq_orthogonalRightInverse (hι : Injective ι) {Q : F →L[𝕜] E}
    (h : IsOrthogonalRightInverse ι T Q) : Q = orthogonalRightInverse ι T :=
  h.unique hι h.isOrthogonalRightInverse_orthogonalRightInverse

end Orthogonal

variable {H E' F' H' : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F]
  [Module 𝕜 F] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [AddCommGroup E'] [Module 𝕜 E']
  [TopologicalSpace E'] [AddCommGroup F'] [Module 𝕜 F'] [TopologicalSpace F']
  [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H'] {ι : E →L[𝕜] H} {ι' : E' →L[𝕜] H'}
  {T : E →L[𝕜] F} {T' : E' →L[𝕜] F'}

/-- An equivalence carrying the kernel of `T` onto the kernel of `T'` and the pairing through `ι`
to the pairing through `ι'` carries vectors `ι`-orthogonal to the kernel of `T` to vectors
`ι'`-orthogonal to the kernel of `T'`. -/
private theorem inner_map_eq_zero_of_ker_conj (e : E ≃ₗ[𝕜] E')
    (hker : ∀ y, e y ∈ T'.ker ↔ y ∈ T.ker)
    (he : ∀ y y', ⟪ι' (e y), ι' (e y')⟫_𝕜 = ⟪ι y, ι y'⟫_𝕜) {y : E}
    (hy : ∀ k ∈ T.ker, ⟪ι y, ι k⟫_𝕜 = 0) {k : E'} (hk : k ∈ T'.ker) :
    ⟪ι' (e y), ι' k⟫_𝕜 = 0 := by
  rw [← e.apply_symm_apply k, he]
  exact hy _ ((hker _).1 (by rwa [e.apply_symm_apply]))

/-- **Orthogonal kernel projections are equivariant.** Let `e : E ≃ₗ[𝕜] E'` carry the kernel of
`T` onto the kernel of `T'` and the pairing through `ι` to the pairing through `ι'`, with `ι'`
injective. If `π` takes values in the kernel of `T` with `ι (y - π y)` orthogonal to `ι` of the
kernel, and `π'` is such a projection for `T'` and `ι'`, then `π' (e y) = e (π y)`. For
`e = LinearEquiv.refl` this is the uniqueness of the projection. No linearity of `π` or `π'` is
assumed. -/
theorem apply_eq_of_ker_projection_conj (hι' : Injective ι') (e : E ≃ₗ[𝕜] E')
    (hker : ∀ y, e y ∈ T'.ker ↔ y ∈ T.ker)
    (he : ∀ y y', ⟪ι' (e y), ι' (e y')⟫_𝕜 = ⟪ι y, ι y'⟫_𝕜) {π : E → E} {π' : E' → E'}
    (hπ : ∀ y, π y ∈ T.ker) (hπo : ∀ y, ∀ k ∈ T.ker, ⟪ι (y - π y), ι k⟫_𝕜 = 0)
    (hπ' : ∀ y, π' y ∈ T'.ker) (hπ'o : ∀ y, ∀ k ∈ T'.ker, ⟪ι' (y - π' y), ι' k⟫_𝕜 = 0)
    (y : E) : π' (e y) = e (π y) := by
  -- The difference lies in the kernel of `T'` and is `ι'`-orthogonal to it.
  refine sub_eq_zero.1 (eq_zero_of_mem_ker_of_forall_inner_eq_zero hι'
    (sub_mem (hπ' _) ((hker _).2 (hπ y))) fun k hk ↦ ?_)
  have h : π' (e y) - e (π y) = e (y - π y) - (e y - π' (e y)) := by
    rw [map_sub]
    abel
  rw [h, map_sub, inner_sub_left, inner_map_eq_zero_of_ker_conj e hker he (hπo y) hk,
    hπ'o _ k hk, sub_zero]

/-- **Orthogonal right inverses are equivariant.** Let `e : E ≃ₗ[𝕜] E'` carry the kernel of `T`
onto the kernel of `T'` and the pairing through `ι` to the pairing through `ι'`, with `ι'`
injective, and let `T' (e y) = σ (T y)`. If `Q` is a right inverse of `T` with values
`ι`-orthogonal to the kernel, and `Q'` such a right inverse of `T'` for `ι'`, then
`Q' (σ f) = e (Q f)`. For `e = LinearEquiv.refl` this is the uniqueness of the right inverse.
No linearity of `Q`, `Q'` or `σ` is assumed. -/
theorem apply_eq_of_rightInverse_conj (hι' : Injective ι') (e : E ≃ₗ[𝕜] E') (σ : F → F')
    (hTe : ∀ y, T' (e y) = σ (T y)) (hker : ∀ y, e y ∈ T'.ker ↔ y ∈ T.ker)
    (he : ∀ y y', ⟪ι' (e y), ι' (e y')⟫_𝕜 = ⟪ι y, ι y'⟫_𝕜) {Q : F → E} {Q' : F' → E'}
    (hQ : ∀ f, T (Q f) = f) (hQo : ∀ f, ∀ k ∈ T.ker, ⟪ι (Q f), ι k⟫_𝕜 = 0)
    (hQ' : ∀ f, T' (Q' f) = f) (hQ'o : ∀ f, ∀ k ∈ T'.ker, ⟪ι' (Q' f), ι' k⟫_𝕜 = 0) (f : F) :
    Q' (σ f) = e (Q f) := by
  -- The difference solves the homogeneous equation and is `ι'`-orthogonal to the kernel.
  refine sub_eq_zero.1 (eq_zero_of_mem_ker_of_forall_inner_eq_zero (T := T') hι' ?_
    fun k hk ↦ ?_)
  · rw [LinearMap.mem_ker, coe_coe, map_sub, hQ', hTe, hQ, sub_self]
  · rw [map_sub, inner_sub_left, hQ'o _ k hk, inner_map_eq_zero_of_ker_conj e hker he (hQo f) hk,
      sub_zero]

end SingleOperator

section Family

variable {𝕜 E F H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The Euclidean parametrization of a finite-dimensional space, on which Gram operators live. -/
private noncomputable def euclideanEquiv (K : Submodule 𝕜 E) [FiniteDimensional 𝕜 K] :
    EuclideanSpace 𝕜 (Fin (finrank 𝕜 K)) ≃L[𝕜] K :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

omit [CompleteSpace E] [CompleteSpace F] in
/-- The pointwise half of the kernel projection theorems. Let `κ x` be operators on `ker (T x₀)`
which are injective with range `ker (T x)` at the parameters of constant nullity, and let `κ' x`
be `κ x` read on a Euclidean space. On an open set `U' ∋ x₀` the Gram operators of `ι κ' x` are
invertible, and the Gram projections of `κ' x` are projections onto the kernels along their
`ι`-orthogonal complements at the parameters of constant nullity. -/
private theorem orthogonal_ker_projection_of_ker_parametrization {X : Type*} [TopologicalSpace X]
    {T : X → E →L[𝕜] F} {x₀ : X} (ι : E →L[𝕜] H) (hι : Injective ι)
    [FiniteDimensional 𝕜 (T x₀).ker] {U : Set X} (hU : IsOpen U) (hx₀U : x₀ ∈ U)
    {κ : X → (T x₀).ker →L[𝕜] E} (hκ : ContinuousOn κ U)
    (hκker : ∀ x ∈ U, finrank 𝕜 (T x).ker = finrank 𝕜 (T x₀).ker →
      Injective (κ x) ∧ (κ x).range = (T x).ker) :
    ∃ U' ⊆ U, IsOpen U' ∧ x₀ ∈ U' ∧ ∀ x ∈ U',
      IsUnit (adjoint (ι ∘L κ x ∘L (euclideanEquiv (T x₀).ker).toContinuousLinearMap) ∘L
        (ι ∘L κ x ∘L (euclideanEquiv (T x₀).ker).toContinuousLinearMap)) ∧
      (finrank 𝕜 (T x).ker = finrank 𝕜 (T x₀).ker →
        (∀ e, gramProjection ι (κ x ∘L (euclideanEquiv (T x₀).ker).toContinuousLinearMap) e ∈
          (T x).ker) ∧
        (∀ k ∈ (T x).ker,
          gramProjection ι (κ x ∘L (euclideanEquiv (T x₀).ker).toContinuousLinearMap) k = k) ∧
        ∀ e, ∀ k ∈ (T x).ker, ⟪ι (e - gramProjection ι
          (κ x ∘L (euclideanEquiv (T x₀).ker).toContinuousLinearMap) e), ι k⟫_𝕜 = 0) := by
  set eL := (euclideanEquiv (T x₀).ker).toContinuousLinearMap
  have hGc : Continuous fun κ : EuclideanSpace 𝕜 (Fin (finrank 𝕜 (T x₀).ker)) →L[𝕜] E ↦
      adjoint (ι ∘L κ) ∘L (ι ∘L κ) :=
    (compL 𝕜 _ E H ι).continuous.clm_adjoint.clm_comp (compL 𝕜 _ E H ι).continuous
  refine ⟨U ∩ (fun x ↦ κ x ∘L eL) ⁻¹' {κ | IsUnit (adjoint (ι ∘L κ) ∘L (ι ∘L κ))},
    inter_subset_left, (hκ.clm_comp continuousOn_const).isOpen_inter_preimage hU
      (Units.isOpen.preimage hGc), ⟨hx₀U, ?_⟩, fun x hx ↦ ⟨hx.2, fun hker ↦ ?_⟩⟩
  · exact (isUnit_adjoint_comp_self_iff _).2
      (hι.comp (((hκker x₀ hx₀U rfl).1).comp (euclideanEquiv _).injective))
  have hK : (κ x ∘L eL).range = (T x).ker := by
    rw [← (hκker x hx.1 hker).2]
    exact LinearMap.range_comp_of_range_eq_top _
      (LinearEquiv.range (euclideanEquiv (T x₀).ker).toLinearEquiv)
  rw [← hK]
  refine ⟨gramProjection_apply_mem_range ι _, fun k hk ↦ ?_, fun e k hk ↦ ?_⟩
  · obtain ⟨v, rfl⟩ := hk
    exact gramProjection_apply_apply hx.2 v
  · obtain ⟨v, rfl⟩ := hk
    exact gramProjection_inner_eq_zero hx.2 e v

variable {X : Type*} [TopologicalSpace X] {T : X → E →L[𝕜] F} {x₀ : X}

omit [CompleteSpace F] in
/-- Near a parameter where a continuous family is Fredholm and onto, the right inverses `R x` of a
splitting with `T x (R x y) + P x y = y` are right inverses, every `T x` is onto, and the nullity
is constant. -/
private theorem surjective_of_splitting (hT₀ : IsFredholm (T x₀)) (hsurj : Surjective (T x₀))
    (hT : ContinuousAt T x₀) {S : Submodule 𝕜 F} {U : Set X} (hx₀U : x₀ ∈ U)
    {R : X → F →L[𝕜] E} {P : X → F →L[𝕜] S}
    (hRP : ∀ x ∈ U, (∀ y, T x (R x y) + P x y = y) ∧
      (finrank 𝕜 (T x).ker = finrank 𝕜 (T x₀).ker →
        ∃ hS : S.IsTopCompl (T x).range, P x = S.projectionOntoL (T x).range hS)) :
    ∃ W : Set X, IsOpen W ∧ x₀ ∈ W ∧ ∀ x ∈ U ∩ W, (∀ y, T x (R x y) = y) ∧
      finrank 𝕜 (T x).ker = finrank 𝕜 (T x₀).ker := by
  obtain ⟨W, hW, hWo, hx₀W⟩ := eventually_nhds_iff.1 (hT₀.eventually_finrank_ker_eq_iff hT)
  -- `S` complements the range of `T x₀`, which is everything, so `S = 0`.
  have hS : S = ⊥ := by
    obtain ⟨hS, -⟩ := (hRP x₀ hx₀U).2 rfl
    simpa [LinearMap.range_eq_top.2 hsurj] using hS.isCompl.inf_eq_bot
  refine ⟨W, hWo, hx₀W, fun x hx ↦ ?_⟩
  have hTR : ∀ y, T x (R x y) = y := fun y ↦ by
    have hP : (P x y : F) = 0 := by simpa [hS] using (P x y).property
    simpa [hP] using (hRP x hx.1).1 y
  have hsurjx : Surjective (T x) := fun y ↦ ⟨R x y, hTR y⟩
  exact ⟨hTR, (hW x hx.2).2
    (by rw [LinearMap.range_eq_top.2 hsurjx, LinearMap.range_eq_top.2 hsurj])⟩

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace H] [TopologicalSpace X] in
/-- The pointwise half of the right inverse theorems for families: where `π x` is the projection
onto `ker (T x)` along its `ι`-orthogonal complement at constant nullity and `R x` is a right
inverse of `T x` at constant nullity, `T x` is onto and `R x - π x R x` is the right inverse with
values in that complement. -/
private theorem orthogonal_rightInverse_of_projection {ι : E →L[𝕜] H} (hι : Injective ι)
    {U₁ U₂ W : Set X} {π : X → E →L[𝕜] E} {R : X → F →L[𝕜] E}
    (hπker : ∀ x ∈ U₁, finrank 𝕜 (T x).ker = finrank 𝕜 (T x₀).ker →
      (∀ e, π x e ∈ (T x).ker) ∧ (∀ k ∈ (T x).ker, π x k = k) ∧
        ∀ e, ∀ k ∈ (T x).ker, ⟪ι (e - π x e), ι k⟫_𝕜 = 0)
    (hW : ∀ x ∈ U₂ ∩ W, (∀ y, T x (R x y) = y) ∧ finrank 𝕜 (T x).ker = finrank 𝕜 (T x₀).ker) :
    ∀ x ∈ U₁ ∩ (U₂ ∩ W), Surjective (T x) ∧
      (∀ e, π x e ∈ (T x).ker) ∧ (∀ k ∈ (T x).ker, π x k = k) ∧
      (∀ e, ∀ k ∈ (T x).ker, ⟪ι (e - π x e), ι k⟫_𝕜 = 0) ∧
      (∀ y, T x ((R x - π x ∘L R x) y) = y) ∧
      (∀ y, ∀ k ∈ (T x).ker, ⟪ι ((R x - π x ∘L R x) y), ι k⟫_𝕜 = 0) ∧
      ∀ e, π x e + (R x - π x ∘L R x) (T x e) = e := fun x hx ↦ by
  obtain ⟨hTR, hker⟩ := hW x hx.2
  obtain ⟨hmem, hfix, horth⟩ := hπker x hx.1 hker
  have hQorth : ∀ y, ∀ k ∈ (T x).ker, ⟪ι ((R x - π x ∘L R x) y), ι k⟫_𝕜 = 0 :=
    fun y k hk ↦ horth (R x y) k hk
  exact ⟨fun y ↦ ⟨R x y, hTR y⟩, hmem, hfix, horth, rightInverse_sub_comp hmem hTR, hQorth,
    apply_add_apply_apply_eq_self hι hmem horth (rightInverse_sub_comp hmem hTR) hQorth⟩

/-- **Orthogonal kernel projections of a Fredholm family move continuously.** Let `T` be
continuous on an open set `s` and Fredholm at `x₀ ∈ s`, and let `ι : E →L[𝕜] H` be injective, into
a Hilbert space. Near `x₀` there is a continuous family of operators `π x : E →L[𝕜] E` which, at
every parameter where the kernel of `T x` has the dimension of that of `T x₀`, is the projection
onto `ker (T x)` along its `ι`-orthogonal complement: `π x` takes values in `ker (T x)`, fixes it,
and `ι (e - π x e)` is orthogonal to `ι k` for every `k ∈ ker (T x)`. -/
theorem IsFredholm.exists_continuousOn_orthogonal_ker_projection (ι : E →L[𝕜] H)
    (hι : Injective ι) {s : Set X} (hT₀ : IsFredholm (T x₀)) (hT : ContinuousOn T s)
    (hs : IsOpen s) (hx₀ : x₀ ∈ s) :
    ∃ U ⊆ s, IsOpen U ∧ x₀ ∈ U ∧ ∃ π : X → E →L[𝕜] E, ContinuousOn π U ∧
      ∀ x ∈ U, finrank 𝕜 (T x).ker = finrank 𝕜 (T x₀).ker →
        (∀ e, π x e ∈ (T x).ker) ∧ (∀ k ∈ (T x).ker, π x k = k) ∧
          ∀ e, ∀ k ∈ (T x).ker, ⟪ι (e - π x e), ι k⟫_𝕜 = 0 := by
  obtain ⟨U, hUs, hU, hx₀U, κ, hκ, hκker⟩ :=
    hT₀.exists_continuousOn_ker_parametrization hT hs hx₀
  have := hT₀.finite_ker
  obtain ⟨U', hU'U, hU', hx₀U', hG⟩ :=
    orthogonal_ker_projection_of_ker_parametrization ι hι hU hx₀U hκ hκker
  set eL := (euclideanEquiv (T x₀).ker).toContinuousLinearMap
  exact ⟨U', hU'U.trans hUs, hU', hx₀U', fun x ↦ gramProjection ι (κ x ∘L eL), fun x hx ↦
    (continuousAt_gramProjection ι (hG x hx).1).comp_continuousWithinAt
      (f := fun x ↦ κ x ∘L eL) ((hκ.clm_comp continuousOn_const x (hU'U hx)).mono hU'U),
    fun x hx ↦ (hG x hx).2⟩

/-- **Orthogonal right inverses of a surjective Fredholm family move continuously.** Let `T` be
continuous on an open set `s` and Fredholm and onto at `x₀ ∈ s`, and let `ι : E →L[𝕜] H` be
injective, into a Hilbert space. Near `x₀` every `T x` is onto, and there are continuous families
of operators `π x : E →L[𝕜] E` and `Q x : F →L[𝕜] E` such that `π x` is the projection onto
`ker (T x)` along its `ι`-orthogonal complement and `Q x` is a right inverse of `T x` with values in
that complement. Every `e ∈ E` splits as `e = π x e + Q x (T x e)`. -/
theorem IsFredholm.exists_continuousOn_orthogonal_rightInverse (ι : E →L[𝕜] H)
    (hι : Injective ι) {s : Set X} (hT₀ : IsFredholm (T x₀)) (hsurj : Surjective (T x₀))
    (hT : ContinuousOn T s) (hs : IsOpen s) (hx₀ : x₀ ∈ s) :
    ∃ U ⊆ s, IsOpen U ∧ x₀ ∈ U ∧ ∃ π : X → E →L[𝕜] E, ∃ Q : X → F →L[𝕜] E,
      ContinuousOn π U ∧ ContinuousOn Q U ∧ ∀ x ∈ U, Surjective (T x) ∧
        (∀ e, π x e ∈ (T x).ker) ∧ (∀ k ∈ (T x).ker, π x k = k) ∧
        (∀ e, ∀ k ∈ (T x).ker, ⟪ι (e - π x e), ι k⟫_𝕜 = 0) ∧
        (∀ y, T x (Q x y) = y) ∧ (∀ y, ∀ k ∈ (T x).ker, ⟪ι (Q x y), ι k⟫_𝕜 = 0) ∧
        ∀ e, π x e + Q x (T x e) = e := by
  obtain ⟨U₁, hU₁s, hU₁, hx₀U₁, π, hπ, hπker⟩ :=
    hT₀.exists_continuousOn_orthogonal_ker_projection ι hι hT hs hx₀
  obtain ⟨S, -, -, U₂, -, hU₂, hx₀U₂, R, P, hR, -, hRP⟩ :=
    hT₀.exists_continuousOn_splitting hT hs hx₀ (D := ⊤) (by simp)
  obtain ⟨W, hWo, hx₀W, hW⟩ :=
    surjective_of_splitting hT₀ hsurj (hT.continuousAt (hs.mem_nhds hx₀)) hx₀U₂ hRP
  refine ⟨U₁ ∩ (U₂ ∩ W), inter_subset_left.trans hU₁s, hU₁.inter (hU₂.inter hWo),
    ⟨hx₀U₁, hx₀U₂, hx₀W⟩, π, fun x ↦ R x - π x ∘L R x, hπ.mono inter_subset_left, ?_,
    orthogonal_rightInverse_of_projection hι hπker hW⟩
  have hR' : ContinuousOn R (U₁ ∩ (U₂ ∩ W)) := hR.mono fun x hx ↦ hx.2.1
  exact hR'.sub ((hπ.mono inter_subset_left).clm_comp hR')

end Family

section OrthogonalOperators

variable {𝕜 E F H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] {ι : E →L[𝕜] H}

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Existence of the orthogonal kernel projection.** For an injective `ι` into a Hilbert space and
an operator `T` with finite-dimensional kernel, `ContinuousLinearMap.orthogonalKerProjection ι T`
is the projection onto the kernel of `T` along its `ι`-orthogonal complement. -/
theorem isOrthogonalKerProjection_orthogonalKerProjection (hι : Injective ι) (T : E →L[𝕜] F)
    [FiniteDimensional 𝕜 T.ker] :
    IsOrthogonalKerProjection ι T (orthogonalKerProjection ι T) := by
  set κ := T.ker.subtypeL ∘L (euclideanEquiv T.ker).toContinuousLinearMap
  have hG : IsUnit (adjoint (ι ∘L κ) ∘L (ι ∘L κ)) :=
    (isUnit_adjoint_comp_self_iff _).2
      (hι.comp (Subtype.val_injective.comp (euclideanEquiv T.ker).injective))
  refine IsOrthogonalKerProjection.isOrthogonalKerProjection_orthogonalKerProjection
    (π := gramProjection ι κ) ⟨fun e ↦ ?_, fun e k hk ↦ ?_⟩
  · obtain ⟨v, hv⟩ := gramProjection_apply_mem_range ι κ e
    rw [← hv]
    exact (euclideanEquiv T.ker v).property
  · have hkκ : k = κ ((euclideanEquiv T.ker).symm ⟨k, hk⟩) := by simp [κ]
    rw [hkκ]
    exact gramProjection_inner_eq_zero hG e _

/-- Near a Fredholm operator `T₀` that is onto, the orthogonal kernel projections and right
inverses exist and depend continuously on the operator. -/
private theorem IsFredholm.exists_continuousOn_orthogonalKerProjection (hι : Injective ι)
    {T₀ : E →L[𝕜] F} (hT₀ : IsFredholm T₀) (hsurj : Surjective T₀) :
    ∃ U : Set (E →L[𝕜] F), IsOpen U ∧ T₀ ∈ U ∧ ContinuousOn (orthogonalKerProjection ι) U ∧
      ContinuousOn (orthogonalRightInverse ι) U ∧
      ∀ T ∈ U, IsOrthogonalRightInverse ι T (orthogonalRightInverse ι T) := by
  obtain ⟨U, -, hU, hT₀U, π, Q, hπ, hQ, h⟩ := hT₀.exists_continuousOn_orthogonal_rightInverse
    (T := id) ι hι hsurj continuousOn_id isOpen_univ (mem_univ T₀)
  have hspec (T : E →L[𝕜] F) (hT : T ∈ U) :
      IsOrthogonalKerProjection ι T (π T) ∧ IsOrthogonalRightInverse ι T (Q T) := by
    obtain ⟨-, hmem, -, horth, hQT, hQorth, -⟩ := h T hT
    exact ⟨⟨hmem, horth⟩, ⟨hQT, hQorth⟩⟩
  exact ⟨U, hU, hT₀U,
    hπ.congr fun T hT ↦ ((hspec T hT).1.eq_orthogonalKerProjection hι).symm,
    hQ.congr fun T hT ↦ ((hspec T hT).2.eq_orthogonalRightInverse hι).symm,
    fun T hT ↦ (hspec T hT).2.isOrthogonalRightInverse_orthogonalRightInverse⟩

/-- **Existence of the orthogonal right inverse.** For an injective `ι` into a Hilbert space and a
Fredholm operator `T` that is onto, `ContinuousLinearMap.orthogonalRightInverse ι T` is a right
inverse of `T` whose values are `ι`-orthogonal to the kernel of `T`. -/
theorem IsFredholm.isOrthogonalRightInverse_orthogonalRightInverse (hι : Injective ι)
    {T : E →L[𝕜] F} (hT : IsFredholm T) (hsurj : Surjective T) :
    IsOrthogonalRightInverse ι T (orthogonalRightInverse ι T) := by
  obtain ⟨U, -, hTU, -, -, h⟩ := hT.exists_continuousOn_orthogonalKerProjection hι hsurj
  exact h T hTU

/-- **The complement component through the right inverse.** For an injective `ι` into a Hilbert
space and a Fredholm operator `T` that is onto, the component of `e` in the `ι`-orthogonal
complement of the kernel is `e - π e = Q (T e)`, where `π` is the orthogonal kernel projection
and `Q` the orthogonal right inverse of `T`. -/
theorem IsFredholm.sub_orthogonalKerProjection_apply (hι : Injective ι) {T : E →L[𝕜] F}
    (hT : IsFredholm T) (hsurj : Surjective T) (e : E) :
    e - orthogonalKerProjection ι T e = orthogonalRightInverse ι T (T e) := by
  have := hT.finite_ker
  exact sub_eq_iff_eq_add'.2 ((isOrthogonalKerProjection_orthogonalKerProjection hι
    T).apply_add_apply_apply_eq_self hι
      (hT.isOrthogonalRightInverse_orthogonalRightInverse hι hsurj) e).symm

/-- **The orthogonal kernel projection moves continuously** near a Fredholm operator `T` that is
onto: `ContinuousLinearMap.orthogonalKerProjection ι` is continuous at `T` in operator norm. -/
theorem IsFredholm.continuousAt_orthogonalKerProjection (hι : Injective ι) {T : E →L[𝕜] F}
    (hT : IsFredholm T) (hsurj : Surjective T) : ContinuousAt (orthogonalKerProjection ι) T := by
  obtain ⟨U, hU, hTU, h, -⟩ := hT.exists_continuousOn_orthogonalKerProjection hι hsurj
  exact h.continuousAt (hU.mem_nhds hTU)

/-- **The orthogonal right inverse moves continuously** near a Fredholm operator `T` that is
onto: `ContinuousLinearMap.orthogonalRightInverse ι` is continuous at `T` in operator norm. -/
theorem IsFredholm.continuousAt_orthogonalRightInverse (hι : Injective ι) {T : E →L[𝕜] F}
    (hT : IsFredholm T) (hsurj : Surjective T) : ContinuousAt (orthogonalRightInverse ι) T := by
  obtain ⟨U, hU, hTU, -, h, -⟩ := hT.exists_continuousOn_orthogonalKerProjection hι hsurj
  exact h.continuousAt (hU.mem_nhds hTU)

/-- **The orthogonal splitting persists near a surjective Fredholm operator.** For an injective `ι`
into a Hilbert space and a Fredholm operator `T` that is onto, every operator `T'` near `T` has the
projection `ContinuousLinearMap.orthogonalKerProjection ι T'` onto its kernel along the
`ι`-orthogonal complement, and the right inverse `ContinuousLinearMap.orthogonalRightInverse ι T'`
with values in that complement. -/
theorem IsFredholm.eventually_isOrthogonalKerProjection_and_isOrthogonalRightInverse
    (hι : Injective ι) {T : E →L[𝕜] F} (hT : IsFredholm T) (hsurj : Surjective T) :
    ∀ᶠ T' in 𝓝 T, IsOrthogonalKerProjection ι T' (orthogonalKerProjection ι T') ∧
      IsOrthogonalRightInverse ι T' (orthogonalRightInverse ι T') := by
  obtain ⟨U, -, hU, hTU, π, Q, -, -, h⟩ := hT.exists_continuousOn_orthogonal_rightInverse
    (T := id) ι hι hsurj continuousOn_id isOpen_univ (mem_univ T)
  filter_upwards [hU.mem_nhds hTU] with T' hT'
  obtain ⟨-, hmem, -, horth, hQT, hQorth, -⟩ := h T' hT'
  exact ⟨IsOrthogonalKerProjection.isOrthogonalKerProjection_orthogonalKerProjection
      (π := π T') ⟨hmem, horth⟩,
    IsOrthogonalRightInverse.isOrthogonalRightInverse_orthogonalRightInverse
      (Q := Q T') ⟨hQT, hQorth⟩⟩

end OrthogonalOperators

section RealFamily

variable {E F H X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {T : X → E →L[ℝ] F} {x₀ : X} {n : WithTop ℕ∞}

/-- **Orthogonal kernel projections of a real `C^n` Fredholm family are `C^n`.** The projections
of `ContinuousLinearMap.IsFredholm.exists_continuousOn_orthogonal_ker_projection` have the
regularity of the family. -/
theorem IsFredholm.exists_contDiffOn_orthogonal_ker_projection (ι : E →L[ℝ] H)
    (hι : Injective ι) {s : Set X} (hT₀ : IsFredholm (T x₀)) (hT : ContDiffOn ℝ n T s)
    (hs : IsOpen s) (hx₀ : x₀ ∈ s) :
    ∃ U ⊆ s, IsOpen U ∧ x₀ ∈ U ∧ ∃ π : X → E →L[ℝ] E, ContDiffOn ℝ n π U ∧
      ∀ x ∈ U, finrank ℝ (T x).ker = finrank ℝ (T x₀).ker →
        (∀ e, π x e ∈ (T x).ker) ∧ (∀ k ∈ (T x).ker, π x k = k) ∧
          ∀ e, ∀ k ∈ (T x).ker, ⟪ι (e - π x e), ι k⟫_ℝ = 0 := by
  obtain ⟨U, hUs, hU, hx₀U, κ, hκ, hκker⟩ :=
    hT₀.exists_contDiffOn_ker_parametrization hT hs hx₀
  have := hT₀.finite_ker
  obtain ⟨U', hU'U, hU', hx₀U', hG⟩ :=
    orthogonal_ker_projection_of_ker_parametrization ι hι hU hx₀U hκ.continuousOn hκker
  set eL := (euclideanEquiv (T x₀).ker).toContinuousLinearMap
  refine ⟨U', hU'U.trans hUs, hU', hx₀U', fun x ↦ gramProjection ι (κ x ∘L eL), fun x hx ↦ ?_,
    fun x hx ↦ (hG x hx).2⟩
  exact (contDiffAt_gramProjection ι (hG x hx).1).comp_contDiffWithinAt (f := fun x ↦ κ x ∘L eL)
    x ((hκ.clm_comp contDiffOn_const x (hU'U hx)).mono hU'U)

/-- **Orthogonal right inverses of a real surjective `C^n` Fredholm family are `C^n`.** The
projections and right inverses of
`ContinuousLinearMap.IsFredholm.exists_continuousOn_orthogonal_rightInverse` have the regularity
of the family. -/
theorem IsFredholm.exists_contDiffOn_orthogonal_rightInverse (ι : E →L[ℝ] H)
    (hι : Injective ι) {s : Set X} (hT₀ : IsFredholm (T x₀)) (hsurj : Surjective (T x₀))
    (hT : ContDiffOn ℝ n T s) (hs : IsOpen s) (hx₀ : x₀ ∈ s) :
    ∃ U ⊆ s, IsOpen U ∧ x₀ ∈ U ∧ ∃ π : X → E →L[ℝ] E, ∃ Q : X → F →L[ℝ] E,
      ContDiffOn ℝ n π U ∧ ContDiffOn ℝ n Q U ∧ ∀ x ∈ U, Surjective (T x) ∧
        (∀ e, π x e ∈ (T x).ker) ∧ (∀ k ∈ (T x).ker, π x k = k) ∧
        (∀ e, ∀ k ∈ (T x).ker, ⟪ι (e - π x e), ι k⟫_ℝ = 0) ∧
        (∀ y, T x (Q x y) = y) ∧ (∀ y, ∀ k ∈ (T x).ker, ⟪ι (Q x y), ι k⟫_ℝ = 0) ∧
        ∀ e, π x e + Q x (T x e) = e := by
  obtain ⟨U₁, hU₁s, hU₁, hx₀U₁, π, hπ, hπker⟩ :=
    hT₀.exists_contDiffOn_orthogonal_ker_projection ι hι hT hs hx₀
  obtain ⟨S, -, -, U₂, -, hU₂, hx₀U₂, R, P, hR, -, hRP⟩ :=
    hT₀.exists_contDiffOn_splitting hT hs hx₀ (D := ⊤) (by simp)
  obtain ⟨W, hWo, hx₀W, hW⟩ := surjective_of_splitting hT₀ hsurj
    (hT.continuousOn.continuousAt (hs.mem_nhds hx₀)) hx₀U₂ hRP
  refine ⟨U₁ ∩ (U₂ ∩ W), inter_subset_left.trans hU₁s, hU₁.inter (hU₂.inter hWo),
    ⟨hx₀U₁, hx₀U₂, hx₀W⟩, π, fun x ↦ R x - π x ∘L R x, hπ.mono inter_subset_left, ?_,
    orthogonal_rightInverse_of_projection hι hπker hW⟩
  have hR' : ContDiffOn ℝ n R (U₁ ∩ (U₂ ∩ W)) := hR.mono fun x hx ↦ hx.2.1
  exact hR'.sub ((hπ.mono inter_subset_left).clm_comp hR')

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- Near a real Fredholm operator `T₀` that is onto, the orthogonal kernel projections and right
inverses are `C^n` functions of the operator. -/
private theorem IsFredholm.exists_contDiffOn_orthogonalKerProjection {ι : E →L[ℝ] H}
    (hι : Injective ι) {T₀ : E →L[ℝ] F} (hT₀ : IsFredholm T₀) (hsurj : Surjective T₀) :
    ∃ U : Set (E →L[ℝ] F), IsOpen U ∧ T₀ ∈ U ∧ ContDiffOn ℝ n (orthogonalKerProjection ι) U ∧
      ContDiffOn ℝ n (orthogonalRightInverse ι) U := by
  obtain ⟨U, -, hU, hT₀U, π, Q, hπ, hQ, h⟩ := hT₀.exists_contDiffOn_orthogonal_rightInverse
    (T := id) ι hι hsurj contDiffOn_id isOpen_univ (mem_univ T₀)
  have hspec (T : E →L[ℝ] F) (hT : T ∈ U) :
      IsOrthogonalKerProjection ι T (π T) ∧ IsOrthogonalRightInverse ι T (Q T) := by
    obtain ⟨-, hmem, -, horth, hQT, hQorth, -⟩ := h T hT
    exact ⟨⟨hmem, horth⟩, ⟨hQT, hQorth⟩⟩
  exact ⟨U, hU, hT₀U,
    hπ.congr fun T hT ↦ ((hspec T hT).1.eq_orthogonalKerProjection hι).symm,
    hQ.congr fun T hT ↦ ((hspec T hT).2.eq_orthogonalRightInverse hι).symm⟩

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- **The orthogonal kernel projection is a `C^n` function of the operator** near a real Fredholm
operator `T` that is onto: `ContinuousLinearMap.orthogonalKerProjection ι` is `C^n` at `T`. -/
theorem IsFredholm.contDiffAt_orthogonalKerProjection {ι : E →L[ℝ] H} (hι : Injective ι)
    {T : E →L[ℝ] F} (hT : IsFredholm T) (hsurj : Surjective T) :
    ContDiffAt ℝ n (orthogonalKerProjection ι) T := by
  obtain ⟨U, hU, hTU, h, -⟩ := hT.exists_contDiffOn_orthogonalKerProjection (n := n) hι hsurj
  exact h.contDiffAt (hU.mem_nhds hTU)

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- **The orthogonal right inverse is a `C^n` function of the operator** near a real Fredholm
operator `T` that is onto: `ContinuousLinearMap.orthogonalRightInverse ι` is `C^n` at `T`. -/
theorem IsFredholm.contDiffAt_orthogonalRightInverse {ι : E →L[ℝ] H} (hι : Injective ι)
    {T : E →L[ℝ] F} (hT : IsFredholm T) (hsurj : Surjective T) :
    ContDiffAt ℝ n (orthogonalRightInverse ι) T := by
  obtain ⟨U, hU, hTU, -, h⟩ := hT.exists_contDiffOn_orthogonalKerProjection (n := n) hι hsurj
  exact h.contDiffAt (hU.mem_nhds hTU)

end RealFamily

section Derivative

/-! ### Derivatives of the orthogonal kernel projections and right inverses -/

variable {E F H X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {ι : E →L[ℝ] H} {T : X → E →L[ℝ] F} {x₀ : X}

/-- Near a parameter where a family differentiable there is Fredholm and onto, the orthogonal
kernel projections and right inverses of the family have their defining properties. -/
private theorem IsFredholm.eventually_isOrthogonal_comp (hι : Injective ι)
    (hT : IsFredholm (T x₀)) (hsurj : Surjective (T x₀)) (hd : DifferentiableAt ℝ T x₀) :
    ∀ᶠ x in 𝓝 x₀, IsOrthogonalKerProjection ι (T x) (orthogonalKerProjection ι (T x)) ∧
      IsOrthogonalRightInverse ι (T x) (orthogonalRightInverse ι (T x)) :=
  hd.continuousAt.eventually
    (hT.eventually_isOrthogonalKerProjection_and_isOrthogonalRightInverse hι hsurj)

private theorem IsFredholm.hasFDerivAt_orthogonalKerProjection_comp (hι : Injective ι)
    (hT : IsFredholm (T x₀)) (hsurj : Surjective (T x₀)) (hd : DifferentiableAt ℝ T x₀) :
    HasFDerivAt (fun x ↦ orthogonalKerProjection ι (T x))
      (fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀) x₀ :=
  ((hT.contDiffAt_orthogonalKerProjection (n := 1) hι hsurj).differentiableAt_one.comp x₀
    hd).hasFDerivAt

private theorem IsFredholm.hasFDerivAt_orthogonalRightInverse_comp (hι : Injective ι)
    (hT : IsFredholm (T x₀)) (hsurj : Surjective (T x₀)) (hd : DifferentiableAt ℝ T x₀) :
    HasFDerivAt (fun x ↦ orthogonalRightInverse ι (T x))
      (fderiv ℝ (fun x ↦ orthogonalRightInverse ι (T x)) x₀) x₀ :=
  ((hT.contDiffAt_orthogonalRightInverse (n := 1) hι hsurj).differentiableAt_one.comp x₀
    hd).hasFDerivAt

/-- **The derivative of the orthogonal kernel projections, applied by the operator.** Let `T` be a
family of real operators, differentiable at `x₀`, where `T x₀` is Fredholm and onto, and write
`π x` for its projection onto `ker (T x)` along the `ι`-orthogonal complement. Differentiating
`T x (π x e) = 0` gives `T x₀ (π' e) = -T' (π x₀ e)`, where `π'` and `T'` are the derivatives of
`π` and `T` at `x₀` along `v`. -/
theorem IsFredholm.apply_fderiv_orthogonalKerProjection_apply (hι : Injective ι)
    (hT : IsFredholm (T x₀)) (hsurj : Surjective (T x₀)) (hd : DifferentiableAt ℝ T x₀)
    (v : X) (e : E) :
    T x₀ (fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ v e) =
      -fderiv ℝ T x₀ v (orthogonalKerProjection ι (T x₀) e) := by
  have h := hd.hasFDerivAt.clm_apply
    ((hT.hasFDerivAt_orthogonalKerProjection_comp hι hsurj hd).clm_apply
      (hasFDerivAt_const e x₀))
  have h0 : HasFDerivAt (fun x ↦ T x (orthogonalKerProjection ι (T x) e)) (0 : X →L[ℝ] F) x₀ :=
    (hasFDerivAt_const (0 : F) x₀).congr_of_eventuallyEq <|
      (hT.eventually_isOrthogonal_comp hι hsurj hd).mono fun x hx ↦
        LinearMap.mem_ker.1 (hx.1.mem_ker e)
  have hv := DFunLike.congr_fun (h.unique h0) v
  simp only [add_apply, comp_apply, flip_apply, zero_apply, map_zero, zero_add] at hv
  exact eq_neg_of_add_eq_zero_left hv

/-- **The complement component of the derivative of the kernel projections.** In the setting of
`ContinuousLinearMap.IsFredholm.apply_fderiv_orthogonalKerProjection_apply`, with `Q` the right
inverse of `T x₀` with values `ι`-orthogonal to its kernel, the component of `π' e` in the
`ι`-orthogonal complement of the kernel is `π' e - π (π' e) = -Q (T' (π e))`, where `π'` is the
derivative of the kernel projections along `v`. -/
theorem IsFredholm.sub_orthogonalKerProjection_fderiv_orthogonalKerProjection_apply
    (hι : Injective ι) (hT : IsFredholm (T x₀)) (hsurj : Surjective (T x₀))
    (hd : DifferentiableAt ℝ T x₀) (v : X) (e : E) :
    fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ v e -
        orthogonalKerProjection ι (T x₀)
          (fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ v e) =
      -orthogonalRightInverse ι (T x₀)
        (fderiv ℝ T x₀ v (orthogonalKerProjection ι (T x₀) e)) := by
  rw [hT.sub_orthogonalKerProjection_apply hι hsurj,
    hT.apply_fderiv_orthogonalKerProjection_apply hι hsurj hd, map_neg]

/-- Differentiating the orthogonality `⟪ι (e - π x e), ι (π x f)⟫ = 0` of the kernel projections. -/
private theorem IsFredholm.inner_sub_fderiv_orthogonalKerProjection (hι : Injective ι)
    (hT : IsFredholm (T x₀)) (hsurj : Surjective (T x₀)) (hd : DifferentiableAt ℝ T x₀)
    (v : X) (e f : E) :
    ⟪ι (e - orthogonalKerProjection ι (T x₀) e),
        ι (fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ v f)⟫_ℝ =
      ⟪ι (fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ v e),
        ι (orthogonalKerProjection ι (T x₀) f)⟫_ℝ := by
  have hπ := hT.hasFDerivAt_orthogonalKerProjection_comp hι hsurj hd
  have h₁ := ι.hasFDerivAt.comp x₀
    ((hasFDerivAt_const e x₀).sub (hπ.clm_apply (hasFDerivAt_const e x₀)))
  have h₂ := ι.hasFDerivAt.comp x₀ (hπ.clm_apply (hasFDerivAt_const f x₀))
  have h := HasFDerivAt.inner ℝ h₁ h₂
  have h0 : HasFDerivAt (fun x ↦ ⟪ι (e - orthogonalKerProjection ι (T x) e),
      ι (orthogonalKerProjection ι (T x) f)⟫_ℝ) (0 : X →L[ℝ] ℝ) x₀ :=
    (hasFDerivAt_const (0 : ℝ) x₀).congr_of_eventuallyEq <|
      (hT.eventually_isOrthogonal_comp hι hsurj hd).mono fun x hx ↦
        hx.1.inner_sub_eq_zero e _ (hx.1.mem_ker f)
  have hv := DFunLike.congr_fun (h.unique h0) v
  simp only [comp_apply, fderivInnerCLM_apply, prod_apply, Pi.sub_apply, zero_sub, neg_apply,
    comp_zero, zero_add, flip_apply, map_neg, inner_neg_left, zero_apply, Function.comp_apply] at hv
  linarith

/-- **The derivative of the orthogonal kernel projections, paired with the kernel.** In the setting
of `ContinuousLinearMap.IsFredholm.apply_fderiv_orthogonalKerProjection_apply`, the kernel component
of `π' e` is determined by `⟪ι (π' e), ι k⟫ = -⟪ι (e - π e), ι (Q (T' k))⟫` for every `k` in the
kernel of `T x₀`, where `Q` is the right inverse of `T x₀` with values `ι`-orthogonal to its
kernel. -/
theorem IsFredholm.inner_fderiv_orthogonalKerProjection_apply (hι : Injective ι)
    (hT : IsFredholm (T x₀)) (hsurj : Surjective (T x₀)) (hd : DifferentiableAt ℝ T x₀)
    (v : X) (e : E) {k : E} (hk : k ∈ (T x₀).ker) :
    ⟪ι (fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ v e), ι k⟫_ℝ =
      -⟪ι (e - orthogonalKerProjection ι (T x₀) e),
        ι (orthogonalRightInverse ι (T x₀) (fderiv ℝ T x₀ v k))⟫_ℝ := by
  have := hT.finite_ker
  have hπ := isOrthogonalKerProjection_orthogonalKerProjection hι (T x₀)
  have hk' : orthogonalKerProjection ι (T x₀) k = k := hπ.apply_of_mem_ker hι hk
  have h := hT.inner_sub_fderiv_orthogonalKerProjection hι hsurj hd v e k
  rw [eq_add_of_sub_eq'
      (hT.sub_orthogonalKerProjection_fderiv_orthogonalKerProjection_apply hι hsurj hd v k), hk',
    map_add ι (orthogonalKerProjection ι (T x₀) _), inner_add_right,
    hπ.inner_sub_eq_zero e _ (hπ.mem_ker _), zero_add, map_neg, inner_neg_right] at h
  exact h.symm

/-- **Characterization of the derivative of the orthogonal kernel projections.** In the setting of
`ContinuousLinearMap.IsFredholm.apply_fderiv_orthogonalKerProjection_apply`, the derivative `π' e`
of the kernel projections along `v` is the unique `w` with `T x₀ w = -T' (π e)` and
`⟪ι w, ι k⟫ = -⟪ι (e - π e), ι (Q (T' k))⟫` for every `k` in the kernel of `T x₀`. -/
theorem IsFredholm.fderiv_orthogonalKerProjection_apply_eq_iff (hι : Injective ι)
    (hT : IsFredholm (T x₀)) (hsurj : Surjective (T x₀)) (hd : DifferentiableAt ℝ T x₀)
    (v : X) (e w : E) :
    fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ v e = w ↔
      T x₀ w = -fderiv ℝ T x₀ v (orthogonalKerProjection ι (T x₀) e) ∧
        ∀ k ∈ (T x₀).ker, ⟪ι w, ι k⟫_ℝ = -⟪ι (e - orthogonalKerProjection ι (T x₀) e),
          ι (orthogonalRightInverse ι (T x₀) (fderiv ℝ T x₀ v k))⟫_ℝ := by
  constructor
  · rintro rfl
    exact ⟨hT.apply_fderiv_orthogonalKerProjection_apply hι hsurj hd v e,
      fun k hk ↦ hT.inner_fderiv_orthogonalKerProjection_apply hι hsurj hd v e hk⟩
  · rintro ⟨h₁, h₂⟩
    refine sub_eq_zero.1 (eq_zero_of_mem_ker_of_forall_inner_eq_zero (T := T x₀) hι ?_
      fun k hk ↦ ?_)
    · rw [LinearMap.mem_ker, coe_coe, map_sub,
        hT.apply_fderiv_orthogonalKerProjection_apply hι hsurj hd, h₁, sub_self]
    · rw [map_sub, inner_sub_left, hT.inner_fderiv_orthogonalKerProjection_apply hι hsurj hd v e hk,
        h₂ k hk, sub_self]

/-- **The derivative of the orthogonal right inverses, applied by the operator.** Let `T` be a
family of real operators, differentiable at `x₀`, where `T x₀` is Fredholm and onto, and write
`Q x` for its right inverse with values `ι`-orthogonal to `ker (T x)`. Differentiating
`T x (Q x y) = y` gives `T x₀ (Q' y) = -T' (Q x₀ y)`, where `Q'` and `T'` are the derivatives of
`Q` and `T` at `x₀` along `v`. -/
theorem IsFredholm.apply_fderiv_orthogonalRightInverse_apply (hι : Injective ι)
    (hT : IsFredholm (T x₀)) (hsurj : Surjective (T x₀)) (hd : DifferentiableAt ℝ T x₀)
    (v : X) (y : F) :
    T x₀ (fderiv ℝ (fun x ↦ orthogonalRightInverse ι (T x)) x₀ v y) =
      -fderiv ℝ T x₀ v (orthogonalRightInverse ι (T x₀) y) := by
  have h := hd.hasFDerivAt.clm_apply
    ((hT.hasFDerivAt_orthogonalRightInverse_comp hι hsurj hd).clm_apply
      (hasFDerivAt_const y x₀))
  have h0 : HasFDerivAt (fun x ↦ T x (orthogonalRightInverse ι (T x) y)) (0 : X →L[ℝ] F) x₀ :=
    (hasFDerivAt_const y x₀).congr_of_eventuallyEq <|
      (hT.eventually_isOrthogonal_comp hι hsurj hd).mono fun x hx ↦ hx.2.rightInverse y
  have hv := DFunLike.congr_fun (h.unique h0) v
  simp only [add_apply, comp_apply, flip_apply, zero_apply, map_zero, zero_add] at hv
  exact eq_neg_of_add_eq_zero_left hv

/-- **The complement component of the derivative of the right inverses.** In the setting of
`ContinuousLinearMap.IsFredholm.apply_fderiv_orthogonalRightInverse_apply`, with `π` the projection
onto the kernel of `T x₀` along its `ι`-orthogonal complement, the component of `Q' y` in the
`ι`-orthogonal complement of the kernel is `Q' y - π (Q' y) = -Q (T' (Q y))`, where `Q'` is the
derivative of the right inverses along `v`. -/
theorem IsFredholm.sub_orthogonalKerProjection_fderiv_orthogonalRightInverse_apply
    (hι : Injective ι) (hT : IsFredholm (T x₀)) (hsurj : Surjective (T x₀))
    (hd : DifferentiableAt ℝ T x₀) (v : X) (y : F) :
    fderiv ℝ (fun x ↦ orthogonalRightInverse ι (T x)) x₀ v y -
        orthogonalKerProjection ι (T x₀)
          (fderiv ℝ (fun x ↦ orthogonalRightInverse ι (T x)) x₀ v y) =
      -orthogonalRightInverse ι (T x₀)
        (fderiv ℝ T x₀ v (orthogonalRightInverse ι (T x₀) y)) := by
  rw [hT.sub_orthogonalKerProjection_apply hι hsurj,
    hT.apply_fderiv_orthogonalRightInverse_apply hι hsurj hd, map_neg]

/-- Differentiating the orthogonality `⟪ι (Q x y), ι (π x f)⟫ = 0` of the right inverses to the
kernels. -/
private theorem IsFredholm.inner_fderiv_orthogonalRightInverse_eq_neg (hι : Injective ι)
    (hT : IsFredholm (T x₀)) (hsurj : Surjective (T x₀)) (hd : DifferentiableAt ℝ T x₀)
    (v : X) (y : F) (f : E) :
    ⟪ι (fderiv ℝ (fun x ↦ orthogonalRightInverse ι (T x)) x₀ v y),
        ι (orthogonalKerProjection ι (T x₀) f)⟫_ℝ =
      -⟪ι (orthogonalRightInverse ι (T x₀) y),
        ι (fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ v f)⟫_ℝ := by
  have h₁ := ι.hasFDerivAt.comp x₀
    ((hT.hasFDerivAt_orthogonalRightInverse_comp hι hsurj hd).clm_apply (hasFDerivAt_const y x₀))
  have h₂ := ι.hasFDerivAt.comp x₀
    ((hT.hasFDerivAt_orthogonalKerProjection_comp hι hsurj hd).clm_apply (hasFDerivAt_const f x₀))
  have h := HasFDerivAt.inner ℝ h₁ h₂
  have h0 : HasFDerivAt (fun x ↦ ⟪ι (orthogonalRightInverse ι (T x) y),
      ι (orthogonalKerProjection ι (T x) f)⟫_ℝ) (0 : X →L[ℝ] ℝ) x₀ :=
    (hasFDerivAt_const (0 : ℝ) x₀).congr_of_eventuallyEq <|
      (hT.eventually_isOrthogonal_comp hι hsurj hd).mono fun x hx ↦
        hx.2.inner_eq_zero y _ (hx.1.mem_ker f)
  have hv := DFunLike.congr_fun (h.unique h0) v
  simp only [comp_apply, fderivInnerCLM_apply, prod_apply, add_apply, flip_apply, zero_apply,
    map_zero, zero_add, Function.comp_apply] at hv
  linarith

/-- **The derivative of the orthogonal right inverses, paired with the kernel.** In the setting of
`ContinuousLinearMap.IsFredholm.apply_fderiv_orthogonalRightInverse_apply`, the kernel component of
`Q' y` is determined by `⟪ι (Q' y), ι k⟫ = ⟪ι (Q y), ι (Q (T' k))⟫` for every `k` in the kernel
of `T x₀`. -/
theorem IsFredholm.inner_fderiv_orthogonalRightInverse_apply (hι : Injective ι)
    (hT : IsFredholm (T x₀)) (hsurj : Surjective (T x₀)) (hd : DifferentiableAt ℝ T x₀)
    (v : X) (y : F) {k : E} (hk : k ∈ (T x₀).ker) :
    ⟪ι (fderiv ℝ (fun x ↦ orthogonalRightInverse ι (T x)) x₀ v y), ι k⟫_ℝ =
      ⟪ι (orthogonalRightInverse ι (T x₀) y),
        ι (orthogonalRightInverse ι (T x₀) (fderiv ℝ T x₀ v k))⟫_ℝ := by
  have := hT.finite_ker
  have hπ := isOrthogonalKerProjection_orthogonalKerProjection hι (T x₀)
  have hQ := hT.isOrthogonalRightInverse_orthogonalRightInverse hι hsurj
  have hk' : orthogonalKerProjection ι (T x₀) k = k := hπ.apply_of_mem_ker hι hk
  have h := hT.inner_fderiv_orthogonalRightInverse_eq_neg hι hsurj hd v y k
  rw [eq_add_of_sub_eq'
      (hT.sub_orthogonalKerProjection_fderiv_orthogonalKerProjection_apply hι hsurj hd v k), hk',
    map_add ι (orthogonalKerProjection ι (T x₀) _), inner_add_right,
    hQ.inner_eq_zero y _ (hπ.mem_ker _), zero_add, map_neg, inner_neg_right, neg_neg] at h
  exact h

/-- **Characterization of the derivative of the orthogonal right inverses.** In the setting of
`ContinuousLinearMap.IsFredholm.apply_fderiv_orthogonalRightInverse_apply`, the derivative `Q' y`
of the right inverses along `v` is the unique `w` with `T x₀ w = -T' (Q y)` and
`⟪ι w, ι k⟫ = ⟪ι (Q y), ι (Q (T' k))⟫` for every `k` in the kernel of `T x₀`. -/
theorem IsFredholm.fderiv_orthogonalRightInverse_apply_eq_iff (hι : Injective ι)
    (hT : IsFredholm (T x₀)) (hsurj : Surjective (T x₀)) (hd : DifferentiableAt ℝ T x₀)
    (v : X) (y : F) (w : E) :
    fderiv ℝ (fun x ↦ orthogonalRightInverse ι (T x)) x₀ v y = w ↔
      T x₀ w = -fderiv ℝ T x₀ v (orthogonalRightInverse ι (T x₀) y) ∧
        ∀ k ∈ (T x₀).ker, ⟪ι w, ι k⟫_ℝ = ⟪ι (orthogonalRightInverse ι (T x₀) y),
          ι (orthogonalRightInverse ι (T x₀) (fderiv ℝ T x₀ v k))⟫_ℝ := by
  constructor
  · rintro rfl
    exact ⟨hT.apply_fderiv_orthogonalRightInverse_apply hι hsurj hd v y,
      fun k hk ↦ hT.inner_fderiv_orthogonalRightInverse_apply hι hsurj hd v y hk⟩
  · rintro ⟨h₁, h₂⟩
    refine sub_eq_zero.1 (eq_zero_of_mem_ker_of_forall_inner_eq_zero (T := T x₀) hι ?_
      fun k hk ↦ ?_)
    · rw [LinearMap.mem_ker, coe_coe, map_sub,
        hT.apply_fderiv_orthogonalRightInverse_apply hι hsurj hd, h₁, sub_self]
    · rw [map_sub, inner_sub_left, hT.inner_fderiv_orthogonalRightInverse_apply hι hsurj hd v y hk,
        h₂ k hk, sub_self]

end Derivative

section SecondDerivative

/-! ### Second derivatives of the orthogonal kernel projections and right inverses

Second derivatives are written as derivatives of first derivatives applied to fixed vectors, such as
`fderiv ℝ (fun x ↦ fderiv ℝ Q x v y) x₀ w` for the second derivative of `Q` along `w` and `v`
applied to `y`. These take values in `E` or `F`, and do not involve the iterated operator space
`X →L[ℝ] F →L[ℝ] E` of `fderiv ℝ (fderiv ℝ Q) x₀`. -/

variable {E F H X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {ι : E →L[ℝ] H} {T : X → E →L[ℝ] F} {x₀ : X}

/-- Near a parameter where a `C²` family is Fredholm and onto, its orthogonal kernel projections
and right inverses are `C²`, and have their defining properties. -/
private theorem IsFredholm.contDiffAt_two_and_eventually (hι : Injective ι)
    (hT : IsFredholm (T x₀)) (hsurj : Surjective (T x₀)) (hT2 : ContDiffAt ℝ 2 T x₀) :
    ContDiffAt ℝ 2 (fun x ↦ orthogonalKerProjection ι (T x)) x₀ ∧
      ContDiffAt ℝ 2 (fun x ↦ orthogonalRightInverse ι (T x)) x₀ ∧
      ∀ᶠ x in 𝓝 x₀, IsOrthogonalKerProjection ι (T x) (orthogonalKerProjection ι (T x)) ∧
        IsOrthogonalRightInverse ι (T x) (orthogonalRightInverse ι (T x)) :=
  ⟨(hT.contDiffAt_orthogonalKerProjection hι hsurj).comp x₀ hT2,
    (hT.contDiffAt_orthogonalRightInverse hι hsurj).comp x₀ hT2,
    hT2.continuousAt.eventually
      (hT.eventually_isOrthogonalKerProjection_and_isOrthogonalRightInverse hι hsurj)⟩

/-- **The second derivative of the orthogonal kernel projections, applied by the operator.** Let
`T` be a family of real operators, `C²` at `x₀`, where `T x₀` is Fredholm and onto, and write
`π x` for its projection onto `ker (T x)` along the `ι`-orthogonal complement. Write `T'_v`, `π'_v`
for the derivatives at `x₀` along `v`, and `π''` for the derivative along `w` of `x ↦ π'_v(x)`,
and `T''` for that of `x ↦ T'_v(x)`. Differentiating `T x (π x e) = 0` twice gives
`T x₀ (π'' e) = -(T'' (π x₀ e) + T'_v (π'_w e) + T'_w (π'_v e))`. -/
theorem IsFredholm.apply_fderiv_fun_fderiv_orthogonalKerProjection_apply (hι : Injective ι)
    (hT : IsFredholm (T x₀)) (hsurj : Surjective (T x₀)) (hT2 : ContDiffAt ℝ 2 T x₀)
    (v w : X) (e : E) :
    T x₀ (fderiv ℝ (fun x ↦ fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x v e) x₀ w) =
      -(fderiv ℝ (fun x ↦ fderiv ℝ T x v (orthogonalKerProjection ι (T x₀) e)) x₀ w +
        fderiv ℝ T x₀ v (fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ w e) +
        fderiv ℝ T x₀ w (fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ v e)) := by
  obtain ⟨hπ, -, h⟩ := hT.contDiffAt_two_and_eventually hι hsurj hT2
  exact TauCeti.apply_fderiv_fun_fderiv_apply_of_eventually hT2 hπ e
    (h.mono fun x hx ↦ LinearMap.mem_ker.1 (hx.1.mem_ker e)) v w

/-- **The second derivative of the orthogonal right inverses, applied by the operator.** Let `T`
be a family of real operators, `C²` at `x₀`, where `T x₀` is Fredholm and onto, and write `Q x`
for its right inverse with values `ι`-orthogonal to `ker (T x)`. Write `T'_v`, `Q'_v` for the
derivatives at `x₀` along `v`, and `Q''`, `T''` for the derivatives along `w` of `x ↦ Q'_v(x)` and
`x ↦ T'_v(x)`. Differentiating `T x (Q x y) = y` twice gives
`T x₀ (Q'' y) = -(T'' (Q x₀ y) + T'_v (Q'_w y) + T'_w (Q'_v y))`. -/
theorem IsFredholm.apply_fderiv_fun_fderiv_orthogonalRightInverse_apply (hι : Injective ι)
    (hT : IsFredholm (T x₀)) (hsurj : Surjective (T x₀)) (hT2 : ContDiffAt ℝ 2 T x₀)
    (v w : X) (y : F) :
    T x₀ (fderiv ℝ (fun x ↦ fderiv ℝ (fun x ↦ orthogonalRightInverse ι (T x)) x v y) x₀ w) =
      -(fderiv ℝ (fun x ↦ fderiv ℝ T x v (orthogonalRightInverse ι (T x₀) y)) x₀ w +
        fderiv ℝ T x₀ v (fderiv ℝ (fun x ↦ orthogonalRightInverse ι (T x)) x₀ w y) +
        fderiv ℝ T x₀ w (fderiv ℝ (fun x ↦ orthogonalRightInverse ι (T x)) x₀ v y)) := by
  obtain ⟨-, hQ, h⟩ := hT.contDiffAt_two_and_eventually hι hsurj hT2
  exact TauCeti.apply_fderiv_fun_fderiv_apply_of_eventually hT2 hQ y
    (h.mono fun x hx ↦ hx.2.rightInverse y) v w

/-- **The complement component of the second derivative of the kernel projections.** In the
setting of
`ContinuousLinearMap.IsFredholm.apply_fderiv_fun_fderiv_orthogonalKerProjection_apply`, with `Q`
the right inverse of `T x₀` with values `ι`-orthogonal to its kernel, the component of `π'' e` in
the `ι`-orthogonal complement of the kernel is
`π'' e - π (π'' e) = -Q (T'' (π e) + T'_v (π'_w e) + T'_w (π'_v e))`. -/
theorem IsFredholm.sub_orthogonalKerProjection_fderiv_fun_fderiv_orthogonalKerProjection_apply
    (hι : Injective ι) (hT : IsFredholm (T x₀)) (hsurj : Surjective (T x₀))
    (hT2 : ContDiffAt ℝ 2 T x₀) (v w : X) (e : E) :
    fderiv ℝ (fun x ↦ fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x v e) x₀ w -
        orthogonalKerProjection ι (T x₀)
          (fderiv ℝ (fun x ↦ fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x v e) x₀ w) =
      -orthogonalRightInverse ι (T x₀)
        (fderiv ℝ (fun x ↦ fderiv ℝ T x v (orthogonalKerProjection ι (T x₀) e)) x₀ w +
          fderiv ℝ T x₀ v (fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ w e) +
          fderiv ℝ T x₀ w (fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ v e)) := by
  rw [hT.sub_orthogonalKerProjection_apply hι hsurj,
    hT.apply_fderiv_fun_fderiv_orthogonalKerProjection_apply hι hsurj hT2, map_neg]

/-- **The complement component of the second derivative of the right inverses.** In the setting
of `ContinuousLinearMap.IsFredholm.apply_fderiv_fun_fderiv_orthogonalRightInverse_apply`, with `π`
the projection onto the kernel of `T x₀` along its `ι`-orthogonal complement, the component of
`Q'' y` in the `ι`-orthogonal complement of the kernel is
`Q'' y - π (Q'' y) = -Q (T'' (Q y) + T'_v (Q'_w y) + T'_w (Q'_v y))`. -/
theorem IsFredholm.sub_orthogonalKerProjection_fderiv_fun_fderiv_orthogonalRightInverse_apply
    (hι : Injective ι) (hT : IsFredholm (T x₀)) (hsurj : Surjective (T x₀))
    (hT2 : ContDiffAt ℝ 2 T x₀) (v w : X) (y : F) :
    fderiv ℝ (fun x ↦ fderiv ℝ (fun x ↦ orthogonalRightInverse ι (T x)) x v y) x₀ w -
        orthogonalKerProjection ι (T x₀)
          (fderiv ℝ (fun x ↦ fderiv ℝ (fun x ↦ orthogonalRightInverse ι (T x)) x v y) x₀ w) =
      -orthogonalRightInverse ι (T x₀)
        (fderiv ℝ (fun x ↦ fderiv ℝ T x v (orthogonalRightInverse ι (T x₀) y)) x₀ w +
          fderiv ℝ T x₀ v (fderiv ℝ (fun x ↦ orthogonalRightInverse ι (T x)) x₀ w y) +
          fderiv ℝ T x₀ w (fderiv ℝ (fun x ↦ orthogonalRightInverse ι (T x)) x₀ v y)) := by
  rw [hT.sub_orthogonalKerProjection_apply hι hsurj,
    hT.apply_fderiv_fun_fderiv_orthogonalRightInverse_apply hι hsurj hT2, map_neg]

/-- For `z` with `ι z` orthogonal to `ι` of the kernel of `T x₀`, and `k` in that kernel, the
pairing of `ι z` with `ι (π'' k)` is minus its pairing with `ι (Q (T'' k + T'_v (π'_w k) +
T'_w (π'_v k)))`: only the complement component of `π'' k` contributes. -/
private theorem IsFredholm.inner_fderiv_fun_fderiv_orthogonalKerProjection_apply_eq_neg
    (hι : Injective ι) (hT : IsFredholm (T x₀)) (hsurj : Surjective (T x₀))
    (hT2 : ContDiffAt ℝ 2 T x₀) (v w : X) {z : E} (hz : ∀ k ∈ (T x₀).ker, ⟪ι z, ι k⟫_ℝ = 0)
    {k : E} (hk : k ∈ (T x₀).ker) :
    ⟪ι z, ι (fderiv ℝ (fun x ↦ fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x v k) x₀ w)⟫_ℝ =
      -⟪ι z, ι (orthogonalRightInverse ι (T x₀)
        (fderiv ℝ (fun x ↦ fderiv ℝ T x v k) x₀ w +
          fderiv ℝ T x₀ v (fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ w k) +
          fderiv ℝ T x₀ w (fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ v k)))⟫_ℝ := by
  have := hT.finite_ker
  have hπ := isOrthogonalKerProjection_orthogonalKerProjection hι (T x₀)
  rw [eq_add_of_sub_eq'
      (hT.sub_orthogonalKerProjection_fderiv_fun_fderiv_orthogonalKerProjection_apply
        hι hsurj hT2 v w k), hπ.apply_of_mem_ker hι hk,
    map_add ι (orthogonalKerProjection ι (T x₀) _), inner_add_right, hz _ (hπ.mem_ker _), zero_add,
    map_neg, inner_neg_right]

/-- **The second derivative of the orthogonal right inverses, paired with the kernel.** In the
setting of `ContinuousLinearMap.IsFredholm.apply_fderiv_fun_fderiv_orthogonalRightInverse_apply`,
with `π` the orthogonal kernel projections, the kernel component of `Q'' y` is determined by

`⟪ι (Q'' y), ι k⟫ = ⟪ι (Q y), ι (Q (T'' k + T'_v (π'_w k) + T'_w (π'_v k)))⟫`
`  - ⟪ι (Q'_v y), ι (π'_w k)⟫ - ⟪ι (Q'_w y), ι (π'_v k)⟫`

for every `k` in the kernel of `T x₀`. -/
theorem IsFredholm.inner_fderiv_fun_fderiv_orthogonalRightInverse_apply (hι : Injective ι)
    (hT : IsFredholm (T x₀)) (hsurj : Surjective (T x₀)) (hT2 : ContDiffAt ℝ 2 T x₀)
    (v w : X) (y : F) {k : E} (hk : k ∈ (T x₀).ker) :
    ⟪ι (fderiv ℝ (fun x ↦ fderiv ℝ (fun x ↦ orthogonalRightInverse ι (T x)) x v y) x₀ w),
        ι k⟫_ℝ =
      ⟪ι (orthogonalRightInverse ι (T x₀) y), ι (orthogonalRightInverse ι (T x₀)
        (fderiv ℝ (fun x ↦ fderiv ℝ T x v k) x₀ w +
          fderiv ℝ T x₀ v (fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ w k) +
          fderiv ℝ T x₀ w (fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ v k)))⟫_ℝ -
        ⟪ι (fderiv ℝ (fun x ↦ orthogonalRightInverse ι (T x)) x₀ v y),
          ι (fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ w k)⟫_ℝ -
        ⟪ι (fderiv ℝ (fun x ↦ orthogonalRightInverse ι (T x)) x₀ w y),
          ι (fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ v k)⟫_ℝ := by
  have := hT.finite_ker
  have hπ := isOrthogonalKerProjection_orthogonalKerProjection hι (T x₀)
  have hQ := hT.isOrthogonalRightInverse_orthogonalRightInverse hι hsurj
  obtain ⟨hπ2, hQ2, h⟩ := hT.contDiffAt_two_and_eventually hι hsurj hT2
  -- Differentiate `⟪ι (Q x y), ι (π x k)⟫ = 0` twice; the last term pairs `Q y` with `π'' k`,
  -- whose kernel component is orthogonal to `Q y`.
  have h₂ := TauCeti.inner_fderiv_fun_fderiv_of_eventually hQ2 hπ2 y k
    (h.mono fun x hx ↦ hx.2.inner_eq_zero y _ (hx.1.mem_ker k)) v w
  rw [hT.inner_fderiv_fun_fderiv_orthogonalKerProjection_apply_eq_neg hι hsurj hT2 v w
    (hQ.inner_eq_zero y) hk, hπ.apply_of_mem_ker hι hk] at h₂
  linarith

/-- **The second derivative of the orthogonal kernel projections, paired with the kernel.** In the
setting of `ContinuousLinearMap.IsFredholm.apply_fderiv_fun_fderiv_orthogonalKerProjection_apply`,
with `Q` the orthogonal right inverse of `T x₀`, the kernel component of `π'' e` is determined by

`⟪ι (π'' e), ι k⟫ = -⟪ι (e - π e), ι (Q (T'' k + T'_v (π'_w k) + T'_w (π'_v k)))⟫`
`  - ⟪ι (π'_v e), ι (π'_w k)⟫ - ⟪ι (π'_w e), ι (π'_v k)⟫`

for every `k` in the kernel of `T x₀`. -/
theorem IsFredholm.inner_fderiv_fun_fderiv_orthogonalKerProjection_apply (hι : Injective ι)
    (hT : IsFredholm (T x₀)) (hsurj : Surjective (T x₀)) (hT2 : ContDiffAt ℝ 2 T x₀)
    (v w : X) (e : E) {k : E} (hk : k ∈ (T x₀).ker) :
    ⟪ι (fderiv ℝ (fun x ↦ fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x v e) x₀ w),
        ι k⟫_ℝ =
      -⟪ι (e - orthogonalKerProjection ι (T x₀) e), ι (orthogonalRightInverse ι (T x₀)
        (fderiv ℝ (fun x ↦ fderiv ℝ T x v k) x₀ w +
          fderiv ℝ T x₀ v (fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ w k) +
          fderiv ℝ T x₀ w (fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ v k)))⟫_ℝ -
        ⟪ι (fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ v e),
          ι (fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ w k)⟫_ℝ -
        ⟪ι (fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ w e),
          ι (fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x₀ v k)⟫_ℝ := by
  have := hT.finite_ker
  have hπ := isOrthogonalKerProjection_orthogonalKerProjection hι (T x₀)
  obtain ⟨hπ2, -, h⟩ := hT.contDiffAt_two_and_eventually hι hsurj hT2
  -- Differentiate `⟪ι (e - π x e), ι (π x k)⟫ = 0` twice, as the identity for `S x = 1 - π x`,
  -- whose derivatives are those of `π` with the opposite sign.
  have hS (x : X) : fderiv ℝ (fun x ↦ (1 : E →L[ℝ] E) - orthogonalKerProjection ι (T x)) x =
      -fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x :=
    fderiv_const_sub _
  have hS' (u : X) : (fun x ↦ fderiv ℝ (fun x ↦ (1 : E →L[ℝ] E) -
      orthogonalKerProjection ι (T x)) x u e) =
        fun x ↦ -fderiv ℝ (fun x ↦ orthogonalKerProjection ι (T x)) x u e :=
    funext fun x ↦ by rw [hS, neg_apply, neg_apply]
  have h₂ := TauCeti.inner_fderiv_fun_fderiv_of_eventually (ι := ι)
    (S := fun x ↦ 1 - orthogonalKerProjection ι (T x)) (contDiffAt_const.sub hπ2) hπ2 e k
    (h.mono fun x hx ↦ by
      simpa only [sub_apply, one_apply_eq_self] using
        hx.1.inner_sub_eq_zero e _ (hx.1.mem_ker k)) v w
  rw [hS', fderiv_fun_neg, hS] at h₂
  simp only [neg_apply, sub_apply, one_apply_eq_self, map_neg, inner_neg_left] at h₂
  rw [hT.inner_fderiv_fun_fderiv_orthogonalKerProjection_apply_eq_neg hι hsurj hT2 v w
    (hπ.inner_sub_eq_zero e) hk, hπ.apply_of_mem_ker hι hk] at h₂
  linarith

end SecondDerivative

section AdjointDerivative

/-! ### The derivative of the adjoints of the orthogonal right inverses -/

variable {E F H X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {ι : E →L[ℝ] H} {T : X → E →L[ℝ] F} {x₀ : X}

/-- **The derivative of the adjoints of the orthogonal right inverses.** In the setting of
`ContinuousLinearMap.IsFredholm.apply_fderiv_orthogonalRightInverse_apply`, with `F` a Hilbert
space, let `Q x` be the right inverse of `T x` with values `ι`-orthogonal to `ker (T x)`, read as
the operator `ι ∘ Q x` between Hilbert spaces. If `g` is orthogonal to `ι` of the kernel of `T x₀`,
then `(ι ∘ Q')† g = -(T' ∘ Q)† ((ι ∘ Q)† g)`, where `Q'` and `T'` are the derivatives of `Q` and
`T` at `x₀` along `v`. -/
theorem IsFredholm.adjoint_comp_fderiv_orthogonalRightInverse_apply (hι : Injective ι)
    (hT : IsFredholm (T x₀)) (hsurj : Surjective (T x₀)) (hd : DifferentiableAt ℝ T x₀)
    (v : X) {g : H} (hg : ∀ k ∈ (T x₀).ker, ⟪g, ι k⟫_ℝ = 0) :
    adjoint (ι ∘L fderiv ℝ (fun x ↦ orthogonalRightInverse ι (T x)) x₀ v) g =
      -adjoint (fderiv ℝ T x₀ v ∘L orthogonalRightInverse ι (T x₀))
        (adjoint (ι ∘L orthogonalRightInverse ι (T x₀)) g) := by
  have := hT.finite_ker
  have hπ := isOrthogonalKerProjection_orthogonalKerProjection hι (T x₀)
  refine ext_inner_right ℝ fun y ↦ ?_
  -- `Q' y` is `-Q (T' (Q y))` plus a kernel element, which pairs to zero with `g`.
  have hQ' : fderiv ℝ (fun x ↦ orthogonalRightInverse ι (T x)) x₀ v y =
      -orthogonalRightInverse ι (T x₀) (fderiv ℝ T x₀ v (orthogonalRightInverse ι (T x₀) y)) +
        orthogonalKerProjection ι (T x₀)
          (fderiv ℝ (fun x ↦ orthogonalRightInverse ι (T x)) x₀ v y) :=
    eq_add_of_sub_eq (hT.sub_orthogonalKerProjection_fderiv_orthogonalRightInverse_apply hι hsurj
      hd v y)
  rw [adjoint_inner_left, comp_apply, hQ']
  simp [adjoint_inner_left, inner_add_right, hg _ (hπ.mem_ker _)]

end AdjointDerivative

end ContinuousLinearMap
