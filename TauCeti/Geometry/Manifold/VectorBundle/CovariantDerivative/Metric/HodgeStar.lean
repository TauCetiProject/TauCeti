/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.SkewAdjoint
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.LocalFrame

/-!
# Metric-compatible connections commute with the Hodge star of two-forms

Let `M` be a Riemannian manifold with a metric-compatible connection `∇ᵀ` on its tangent bundle,
such as the Levi-Civita connection, and let `W` be a vector bundle with a connection `∇`. A field
`Θ` of `W`-valued bilinear forms on the tangent spaces, `Θ y : T_y M × T_y M → W y`, is a section
of the iterated `Hom` bundle `Hom(TM, Hom(TM, W))`, and the connection induced there
(`CovariantDerivative.hom`) differentiates it by

`(∇_v Θ)(u, w) = ∇_v (Θ(X, Y)) - Θ(∇ᵀ_v X, w) - Θ(u, ∇ᵀ_v Y)`

for any fields `X`, `Y` with values `u`, `w` at the base point
(`CovariantDerivative.hom_hom_apply`).

In dimension four, the Hodge dual of a two-form is given in an orthonormal frame `(eₖ)` by
`(⋆Θ)(u, w) = ½ ∑ₖ ∑ₗ vol(u, w, eₖ, eₗ) Θ(eₖ, eₗ)`
(`Orientation.vectorFormHodgeStar_apply_ιMulti_two`). This file shows that the covariant derivative
commutes with the Hodge star: if, near a point `x`, a field `Θ'` is the Hodge dual of `Θ` in a local
frame `(eₖ)` whose inner products are constant, then at `x`

`(∇_v Θ')(u, w) = ½ ∑ₖ ∑ₗ vol(u, w, eₖ, eₗ) (∇_v Θ)(eₖ, eₗ)`,

that is, `∇_v (⋆Θ) = ⋆(∇_v Θ)`
(`CovariantDerivative.IsMetricCompatible.hom_hom_apply_eq_sum_sum_volumeForm_smul`).

The proof differentiates the frame expression of `Θ'`. Differentiating `Θ(eₖ, eₗ)` produces
`(∇_v Θ)(eₖ, eₗ)` together with the terms `Θ(∇ᵀ_v eₖ, eₗ) + Θ(eₖ, ∇ᵀ_v eₗ)`, in which `∇ᵀ_v`
differentiates the frame. Since the inner products of the frame are constant and `∇ᵀ` is
metric-compatible, `∇ᵀ_v` acts on the frame at `x` by a skew-adjoint endomorphism `A`, by
`CovariantDerivative.IsMetricCompatible.inner_apply_eq_neg_inner_apply_of_eventuallyEq_const`,
and these terms cancel against `Θ'(A u, w) + Θ'(u, A w)` because the frame expression of the Hodge
dual commutes with skew-adjoint derivations
(`Orientation.sum_sum_volumeForm_smul_add_eq_sum_sum_add_smul`).

More generally, if `Θ'` is `a Θ + c ⋆Θ` in the frame, then `∇_v Θ' = a ∇_v Θ + c ⋆(∇_v Θ)`
(`CovariantDerivative.IsMetricCompatible.hom_hom_apply_eq_smul_add_smul_sum_sum_volumeForm_smul`).
With `a = c = 1 / 2` this identifies the covariant derivative of the self-dual part of a two-form
with the self-dual part of its covariant derivative; for the curvature of a connection this is
`CovariantDerivative.IsMetricCompatible.hom_hom_apply_eq_vectorFormSelfDualPart`.

## Main results

* `CovariantDerivative.IsMetricCompatible.hom_hom_apply_eq_sum_sum_volumeForm_smul`: for a
  metric-compatible `∇ᵀ`, the covariant derivative of the Hodge dual of a field of two-forms is the
  Hodge dual of its covariant derivative.
* `CovariantDerivative.IsMetricCompatible.hom_hom_apply_eq_smul_add_smul_sum_sum_volumeForm_smul`:
  the same for combinations `a Θ + c ⋆Θ`, such as the self-dual and anti-self-dual parts.

## References

* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford University Press,
  1990, Section 2.1.
-/

public section

noncomputable section

open Bundle Filter Module
open scoped ContDiff Manifold RealInnerProductSpace Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul ℝ (W x)] [FiberBundle G W] [VectorBundle ℝ G W]
  (covW : CovariantDerivative I G W)
  {covT : CovariantDerivative I E (TangentSpace I : M → Type _)}
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

omit [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- The covariant derivative of a section whose values near `x` are a fixed combination of the
frame components `Θ(eₖ, eₗ)` of a field `Θ` is the same combination of their covariant
derivatives. -/
private theorem apply_eq_sum_sum_smul_of_eventually {x : M} {ι : Type*} [Fintype ι]
    {e : ι → Π y : M, TangentSpace I y} (he : ∀ i, MDiffAt (T% (e i)) x)
    {Θ : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] W y}
    (hΘ : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
      (E := fun z ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] W z) y (Θ y)) x)
    {σ : Π y : M, W y} (hσ : MDiffAt (T% σ) x) (c : ι → ι → ℝ)
    (hev : ∀ᶠ y in 𝓝 x, σ y = ∑ k, ∑ l, c k l • Θ y (e k y) (e l y)) (v : TangentSpace I x) :
    covW σ x v = ∑ k, ∑ l, c k l • covW (fun y ↦ Θ y (e k y) (e l y)) x v := by
  set τ : ι × ι → Π y : M, W y := fun p y ↦ Θ y (e p.1 y) (e p.2 y)
  have hτ : ∀ p ∈ (Finset.univ : Finset (ι × ι)), MDiffAt (T% (τ p)) x := fun p _ ↦
    (hΘ.clm_bundle_apply (he p.1)).clm_bundle_apply (he p.2)
  have hev' : ∀ᶠ y in 𝓝 x, σ y = (∑ p, c p.1 p.2 • τ p) y :=
    hev.mono fun y hy ↦ by simp only [hy, τ, Finset.sum_apply, Pi.smul_apply,
      Fintype.sum_prod_type]
  have hsum : MDiffAt (T% (∑ p, c p.1 p.2 • τ p)) x := by
    simpa [Finset.sum_apply] using
      MDifferentiableAt.sum_section fun p hp ↦ (hτ p hp).smul_const_section (a := c p.1 p.2)
  rw [covW.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hσ hsum univ_mem hev',
    covW.isCovariantDerivativeOnUniv.sum_smul_const _ hτ, Fintype.sum_prod_type]
  simp only [τ, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply]

/-- **A metric-compatible connection commutes with the Hodge star of two-forms.** Let `∇ᵀ` be a
metric-compatible connection on the tangent bundle, `(eₖ)` a local frame near `x`, differentiable at
`x`, whose inner products are constant near `x` and whose value at `x` is an orthonormal basis
`(bₖ)` of `T_x M`, and `o` an orientation of the four-dimensional space `T_x M`. If, near `x`, the
field `Θ'` of `W`-valued bilinear forms is the Hodge dual of `Θ` in the frame `(eₖ)`,
`Θ'(eᵢ, eⱼ) = ½ ∑ₖ ∑ₗ vol(bᵢ, bⱼ, bₖ, bₗ) Θ(eₖ, eₗ)`, then at `x` the covariant derivative of `Θ'`
is the Hodge dual of that of `Θ`:
`(∇_v Θ')(u, w) = ½ ∑ₖ ∑ₗ vol(u, w, bₖ, bₗ) (∇_v Θ)(bₖ, bₗ)`. -/
theorem IsMetricCompatible.hom_hom_apply_eq_sum_sum_volumeForm_smul
    (hT : IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) covT) {x : M}
    [Fact (finrank ℝ (TangentSpace I x) = 4)]
    (o : Orientation ℝ (TangentSpace I x) (Fin 4)) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) {e : ι → Π y : M, TangentSpace I y}
    (he : ∀ i, MDiffAt (T% (e i)) x) (hb : ∀ i, e i x = b i)
    (hon : ∀ i j, (fun y ↦ ⟪e i y, e j y⟫) =ᶠ[𝓝 x] fun _ ↦ ⟪b i, b j⟫)
    {Θ Θ' : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] W y}
    (hΘ : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
      (E := fun z ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] W z) y (Θ y)) x)
    (hΘ' : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
      (E := fun z ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] W z) y (Θ' y)) x)
    (hΘΘ' : ∀ᶠ y in 𝓝 x, ∀ i j, Θ' y (e i y) (e j y) =
      (2⁻¹ : ℝ) • ∑ k, ∑ l, o.volumeForm ![b i, b j, b k, b l] • Θ y (e k y) (e l y))
    (v u w : TangentSpace I x) :
    covT.hom (covT.hom covW) Θ' x v u w =
      (2⁻¹ : ℝ) • ∑ k, ∑ l, o.volumeForm ![u, w, b k, b l] •
        covT.hom (covT.hom covW) Θ x v (b k) (b l) := by
  classical
  -- `∇ᵀ_v` differentiates the frame at `x` by a skew-adjoint endomorphism `A`.
  set A := b.toBasis.constr ℝ fun k ↦ covT (e k) x v
  have hAb (k : ι) : A (b k) = covT (e k) x v := by
    rw [← OrthonormalBasis.coe_toBasis]
    exact b.toBasis.constr_basis ℝ (fun k ↦ covT (e k) x v) k
  have hA := hT.inner_apply_eq_neg_inner_apply_of_eventuallyEq_const b.toBasis he
    (by simpa using hb) (by simpa using hon) v (by simpa using hAb)
  -- The values of `Θ'` at `x` on all vectors, from its frame expression.
  have hΘ'x (p q : TangentSpace I x) : Θ' x p q =
      ∑ k, ∑ l, o.volumeForm ![p, q, b k, b l] • ((2⁻¹ : ℝ) • Θ x (b k) (b l)) := by
    have h := o.apply_eq_sum_sum_volumeForm_smul b.toBasis (Θ' x).toLinearMap₁₂
      (fun k l ↦ (2⁻¹ : ℝ) • Θ x (b k) (b l)) (fun i j ↦ by
        have h := hΘΘ'.self_of_nhds i j
        simp only [hb] at h
        rw [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, h]
        simp only [Finset.smul_sum, smul_comm (2⁻¹ : ℝ)]) p q
    simpa only [OrthonormalBasis.coe_toBasis,
      ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply] using h
  -- Differentiating the frame components of `Θ` and of `Θ'`.
  have hcomp (k l : ι) : covW (fun y ↦ Θ y (e k y) (e l y)) x v =
      covT.hom (covT.hom covW) Θ x v (b k) (b l) +
        (Θ x (A (b k)) (b l) + Θ x (b k) (A (b l))) := by
    rw [← hb k, ← hb l, hom_hom_apply covT covT covW hΘ (he k) (he l) v, hb k, hb l, hAb k,
      hAb l]
    abel
  have hcov (i j : ι) : covW (fun y ↦ Θ' y (e i y) (e j y)) x v =
      ∑ k, ∑ l, ((2⁻¹ : ℝ) * o.volumeForm ![b i, b j, b k, b l]) •
        covW (fun y ↦ Θ y (e k y) (e l y)) x v :=
    apply_eq_sum_sum_smul_of_eventually covW he hΘ
      ((hΘ'.clm_bundle_apply (he i)).clm_bundle_apply (he j)) _
      (hΘΘ'.mono fun y hy ↦ by simp only [hy i j, Finset.smul_sum, mul_smul]) v
  -- The identity on pairs of basis vectors.
  have hbasis (i j : ι) : covT.hom (covT.hom covW) Θ' x v (b i) (b j) =
      ∑ k, ∑ l, o.volumeForm ![b i, b j, b k, b l] •
        ((2⁻¹ : ℝ) • covT.hom (covT.hom covW) Θ x v (b k) (b l)) := by
    rw [← hb i, ← hb j, hom_hom_apply covT covT covW hΘ' (he i) (he j) v, hb i, hb j, hcov,
      ← hAb i, ← hAb j, hΘ'x, hΘ'x]
    have hcore := o.sum_sum_volumeForm_smul_add_eq_sum_sum_add_smul b hA (Θ x).toLinearMap₁₂
      (b i) (b j)
    simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply] at hcore
    simp only [hcomp, mul_smul, smul_comm _ (2⁻¹ : ℝ), ← Finset.smul_sum, ← smul_sub]
    congr 1
    simp only [smul_add, Finset.sum_add_distrib, add_smul] at hcore ⊢
    rw [hcore]
    abel
  have h := o.apply_eq_sum_sum_volumeForm_smul b.toBasis
    (covT.hom (covT.hom covW) Θ' x v).toLinearMap₁₂ _ (fun i j ↦ by simpa using hbasis i j) u w
  rw [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply] at h
  simp only [OrthonormalBasis.coe_toBasis] at h
  rw [h]
  simp only [Finset.smul_sum, smul_comm (2⁻¹ : ℝ)]

/-- **A metric-compatible connection commutes with combinations of the identity and the Hodge
star.** In the setting of
`CovariantDerivative.IsMetricCompatible.hom_hom_apply_eq_sum_sum_volumeForm_smul`, if near `x` the
field `Θ'` is `a Θ + c ⋆Θ` in the frame `(eₖ)`, then at `x` its covariant derivative is
`a ∇_v Θ + c ⋆(∇_v Θ)`. For `a = c = 1 / 2` this says that the covariant derivative of the
self-dual part of `Θ` is the self-dual part of `∇_v Θ`, and for `a = -c = 1 / 2` the same holds for
the anti-self-dual parts. -/
theorem IsMetricCompatible.hom_hom_apply_eq_smul_add_smul_sum_sum_volumeForm_smul
    (hT : IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) covT) {x : M}
    [Fact (finrank ℝ (TangentSpace I x) = 4)]
    (o : Orientation ℝ (TangentSpace I x) (Fin 4)) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) {e : ι → Π y : M, TangentSpace I y}
    (he : ∀ i, MDiffAt (T% (e i)) x) (hb : ∀ i, e i x = b i)
    (hon : ∀ i j, (fun y ↦ ⟪e i y, e j y⟫) =ᶠ[𝓝 x] fun _ ↦ ⟪b i, b j⟫)
    {Θ Θ' : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] W y}
    (hΘ : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
      (E := fun z ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] W z) y (Θ y)) x)
    (hΘ' : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
      (E := fun z ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] W z) y (Θ' y)) x)
    (a c : ℝ)
    (hΘΘ' : ∀ᶠ y in 𝓝 x, ∀ i j, Θ' y (e i y) (e j y) = a • Θ y (e i y) (e j y) +
      c • ((2⁻¹ : ℝ) • ∑ k, ∑ l, o.volumeForm ![b i, b j, b k, b l] • Θ y (e k y) (e l y)))
    (v u w : TangentSpace I x) :
    covT.hom (covT.hom covW) Θ' x v u w =
      a • covT.hom (covT.hom covW) Θ x v u w + c • ((2⁻¹ : ℝ) •
        ∑ k, ∑ l, o.volumeForm ![u, w, b k, b l] • covT.hom (covT.hom covW) Θ x v (b k) (b l)) := by
  -- `Θ' - a Θ` is the Hodge dual of `c Θ` in the frame.
  have hcΘ := MDifferentiableAt.smul_const_section (a := c) hΘ
  have haΘ := MDifferentiableAt.smul_const_section (a := a) hΘ
  have hQ := mdifferentiableAt_sub_section hΘ' haΘ
  have hstar := hT.hom_hom_apply_eq_sum_sum_volumeForm_smul covW o b he hb hon hcΘ hQ
    (hΘΘ'.mono fun y hy i j ↦ by
      simp only [Pi.sub_apply, Pi.smul_apply, sub_apply,
        FunLike.coe_smul, hy i j, add_sub_cancel_left, Finset.smul_sum, smul_comm c])
    v u w
  rw [(covT.hom (covT.hom covW)).isCovariantDerivativeOnUniv.sub hΘ' haΘ,
    (covT.hom (covT.hom covW)).isCovariantDerivativeOnUniv.smul_const _ hΘ,
    (covT.hom (covT.hom covW)).isCovariantDerivativeOnUniv.smul_const _ hΘ] at hstar
  simp only [sub_apply, FunLike.coe_smul, Pi.smul_apply,
    Finset.smul_sum, smul_comm c] at hstar ⊢
  rw [← sub_eq_iff_eq_add', hstar]

end CovariantDerivative

end
