/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.ConstantNullity
public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.RangeProjection

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

## Main results

* `ContinuousLinearMap.rightInverse_sub_comp` and
  `ContinuousLinearMap.apply_add_apply_apply_eq_self`: for a single operator `T` and `π` with
  values in its kernel, `R - π R` is a right inverse of `T` whenever `R` is, and when `π` projects
  along the `ι`-orthogonal complement of the kernel, a right inverse `Q` with values in that
  complement splits every `e` as `e = π e + Q (T e)`.
* `ContinuousLinearMap.eq_zero_of_mem_ker_of_forall_inner_eq_zero`: an element of the kernel
  `ι`-orthogonal to the kernel vanishes.
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
    ((adjoint : _ ≃ₗᵢ⋆[𝕜] _).continuous.comp (compL 𝕜 _ E H ι).continuous).clm_comp
      (compL 𝕜 _ E H ι).continuous
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

end RealFamily

end ContinuousLinearMap
