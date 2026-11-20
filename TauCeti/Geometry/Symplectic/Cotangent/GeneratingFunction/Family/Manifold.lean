/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Level
public import TauCeti.Geometry.Symplectic.Cotangent.GeneratingFunction.GeneratedMap
public import TauCeti.Geometry.Symplectic.Lagrangian.Exact
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Mixed

/-!
# Generating families on manifolds

Let `M` be a manifold and `A` a normed space of *auxiliary variables*. A real function `S(q, a)`
on `M × A` is a **generating family** for the cotangent bundle `T*M`. Its *fibre derivative* is
the differential of `S(q, ·)`,

`∂_a S : M × A → A'`, `(q, a) ↦ d_a S(q, a)`

(`TauCeti.CotangentBundle.familyFiberDeriv`), and its *fibre-critical set* is the zero set
`Σ_S = {(q, a) | ∂_a S(q, a) = 0}`. The family is *transverse* when `0` is a regular value of
`∂_a S`. The source projection `(q, a) ↦ (q, d_q S(q, a))` of the cotangent relation generated
by `S` (`TauCeti.CotangentBundle.generatingSource`) maps `Σ_S` to `T*M`. This file is the manifold
version of the generating families on normed spaces of
`TauCeti.Geometry.Symplectic.Cotangent.GeneratingFunction.Family.Basic`, where `M` is a normed
space.

For a smooth transverse generating family on a finite-dimensional boundaryless manifold `M`, with
`A` finite-dimensional:

* **The fibre-critical set is a manifold.** It is a regular level of `∂_a S`, so with the atlas
  `TauCeti.regularLevelChartedSpace` it is a smooth manifold of the dimension of `M`
  (`TauCeti.CotangentBundle.isManifold_familyCriticalSet`), smoothly embedded in `M × A`, with
  tangent spaces the kernels of the differential of `∂_a S`
  (`TauCeti.CotangentBundle.range_mfderiv_coe_familyCriticalSet`).
* **Exactness.** Along `Σ_S`, the source projection pulls the Liouville form `λ` of `T*M` back
  to `d(S|Σ_S)` (`TauCeti.CotangentBundle.mpullback_generatingSource_comp_coe_liouvilleForm`),
  because `dS = d_q S + ∂_a S` and `∂_a S` vanishes on `Σ_S`. Since `ω = -dλ`, the source
  projection is isotropic along `Σ_S`.
* **Immersion.** The differential of the source projection is injective on the tangent spaces of
  `Σ_S` (`TauCeti.CotangentBundle.injective_mfderiv_generatingSource_comp_coe`). It keeps the
  base component and acts on the auxiliary directions by the mixed Hessian
  (`TauCeti.mixedHessian`). The differential of `∂_a S` is the mixed Hessian with the two orders
  of differentiation exchanged, plus the second derivative of `S(q, ·)`
  (`TauCeti.CotangentBundle.mvfderiv_familyFiberDeriv_apply_apply`). So an auxiliary direction
  `b` killed by both differentials is killed by every value of the differential of `∂_a S`, and
  transversality forces `b = 0`.

Hence the source projection restricted to `Σ_S` is an exact Lagrangian map with primitive `S|Σ_S`
(`TauCeti.CotangentBundle.isExactLagrangianMap_generatingSource_comp_coe`) and a Lagrangian
immersion into `T*M` (`TauCeti.CotangentBundle.isLagrangianImmersion_generatingSource_comp_coe`).
Its image need not be embedded: distinct critical points with the same image give
self-intersections. A generating function `S(q, Q)` on `M × A` is the case in which the auxiliary
variables are the target positions `Q`: its fibre-critical set is where the target covector
`-d_Q S` vanishes (`TauCeti.CotangentBundle.familyFiberDeriv_eq_neg_generatingTarget_snd`).

## Families of correspondences

Let `M` and `N` be manifolds. A real function `S((q, Q), a)` on `(M × N) × A` is a **generating
family** of a cotangent relation between `T*M` and `T*N`. For each fixed `a` the function
`S(·, a)` on `M × N` generates the relation

`p = d_q S((q, Q), a)`, `P = -d_Q S((q, Q), a)`

(`TauCeti.CotangentBundle.generatingCorrespondence`), and the family relation is the union of
these relations over the points where `S` is stationary in `a`. Its parametrization is

`G : ((q, Q), a) ↦ ((q, d_q S), (Q, -d_Q S)) ∈ T*M × T*N`

(`TauCeti.CotangentBundle.familyCorrespondence`), restricted to the fibre-critical set
`Σ_S = {z | ∂_a S z = 0}` of the fibre derivative `∂_a S`
(`TauCeti.CotangentBundle.familyFiberDeriv`, for the base manifold `M × N`).

Suppose that `M` and `N` are finite-dimensional and boundaryless and that `A` is
finite-dimensional. When `S` is smooth and the derivative of `∂_a S` is surjective at every point
of `Σ_S`, the family is transverse, and by the results above for the base `M × N`, `Σ_S` is a
smooth manifold of dimension `dim (M × N)`
(`TauCeti.CotangentBundle.familyCriticalSetChartedSpace`,
`TauCeti.CotangentBundle.isManifold_familyCriticalSet`). This file proves that `G` restricted
to `Σ_S` is a Lagrangian correspondence in the immersed sense, for the twisted product
`pr₁^*ω_M - pr₂^*ω_N`:

* **Exactness.** `G` pulls the primitive `pr₁^*λ_M - pr₂^*λ_N` of the twisted product back to
  `dS - ∂_a S(da)` (`TauCeti.CotangentBundle.mpullback_familyCorrespondence_liouvilleForm_apply`),
  so along `Σ_S` it pulls it back to the differential of the restriction of `S`
  (`TauCeti.CotangentBundle.mpullback_familyCorrespondence_comp_coe_liouvilleForm`).
* **Injectivity.** At a transverse point, the differential of `G` is injective on the kernel of
  the differential of `∂_a S` (`TauCeti.CotangentBundle.injOn_mfderiv_familyCorrespondence_ker`).
  A vector `(v, b)` killed by `dG` has `v = 0`, since `G` lies over `(q, Q)`; then the covectors
  `d_q S` and `d_Q S` do not move in the direction `b`, and by the symmetry of mixed derivatives
  (`TauCeti.Manifold.fderiv_mvfderiv_apply`) neither does `∂_a S(·)(b)` in any direction of
  `M × N`. Together with `(0, b) ∈ ker d(∂_a S)` and the symmetry of the second derivative in `a`,
  every covector in the range of `d(∂_a S)` vanishes on `b`, so `b = 0` by surjectivity.
* Hence `G ∘ Subtype.val` is an exact Lagrangian map with primitive the restriction of `S`
  (`TauCeti.CotangentBundle.isExactLagrangianMap_familyCorrespondence_comp_coe`) and a Lagrangian
  immersion (`TauCeti.CotangentBundle.isLagrangianImmersion_familyCorrespondence_comp_coe`): an
  immersed Lagrangian correspondence `T*M ⇝ T*N`.

This is the form of the results above for correspondences, as
`TauCeti.CotangentBundle.generatingCorrespondence` is for a single generating function. The image
of `G` on `Σ_S` need not be embedded: distinct critical points may have the same image. The
pointwise exactness and injectivity statements hold for arbitrary manifolds and a normed space
`A`; the finite-dimensional and boundaryless hypotheses enter only through the regular-level atlas
on `Σ_S`. As for the phase functions of Hörmander, no compactness is
assumed.

## References

* L. Hörmander, *Fourier integral operators. I*, Acta Math. 127 (1971), 79–183, Section 3.1, for
  the Lagrangian defined by a nondegenerate phase function.
* A. Weinstein, *Lectures on Symplectic Manifolds*, CBMS Regional Conference Series in
  Mathematics 29, AMS, 1977, for generating families (Morse families).
-/

public section

noncomputable section

open Bundle Manifold Module
open scoped Manifold ContDiff Topology

namespace TauCeti.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] {S : M × A → ℝ}

/-! ### The fibre derivative -/

/-- The **fibre derivative** `∂_a S(q, a)` of a generating family `S : M × A → ℝ` on a manifold
`M` with auxiliary variables `a` in a normed space `A`: the differential of `S(q, ·)` at `a`, a
covector on `A`. It is minus the covector of the target projection
`TauCeti.CotangentBundle.generatingTarget` of the cotangent relation generated by `S`. -/
def familyFiberDeriv (S : M × A → ℝ) (x : M × A) : A →L[ℝ] ℝ :=
  mvfderiv 𝓘(ℝ, A) (fun a ↦ S (x.1, a)) x.2

omit [TopologicalSpace M] in
/-- The fibre derivative is the manifold derivative of `S(q, ·)`. -/
theorem familyFiberDeriv_def (S : M × A → ℝ) (x : M × A) :
    familyFiberDeriv S x = mvfderiv 𝓘(ℝ, A) (fun a ↦ S (x.1, a)) x.2 :=
  (rfl)

omit [TopologicalSpace M] in
@[simp]
theorem familyFiberDeriv_apply (S : M × A → ℝ) (x : M × A) (b : A) :
    familyFiberDeriv S x b = fderiv ℝ (fun a ↦ S (x.1, a)) x.2 b :=
  mvfderiv_eq_fderiv_apply _ _ b

omit [TopologicalSpace M] in
/-- The fibre derivative is the Fréchet derivative of `S(q, ·)`. -/
theorem familyFiberDeriv_eq_fderiv (S : M × A → ℝ) (x : M × A) :
    familyFiberDeriv S x = fderiv ℝ (fun a ↦ S (x.1, a)) x.2 :=
  ContinuousLinearMap.ext (familyFiberDeriv_apply S x)

omit [TopologicalSpace M] in
/-- The fibre derivative of `S` is minus the covector of the target projection of the cotangent
relation generated by `S`. -/
theorem familyFiberDeriv_eq_neg_generatingTarget_snd (S : M × A → ℝ) (x : M × A) :
    familyFiberDeriv S x = -(generatingTarget 𝓘(ℝ, A) S x).snd := by
  rw [generatingTarget_snd, familyFiberDeriv_def]
  exact (neg_neg _).symm

/-- The fibre derivative of a smooth generating family is smooth. -/
theorem contMDiff_familyFiberDeriv [IsManifold I 1 M]
    (hS : ContMDiff (I.prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) :
    ContMDiff (I.prod 𝓘(ℝ, A)) 𝓘(ℝ, A →L[ℝ] ℝ) ∞ (familyFiberDeriv S) := fun x ↦
  (ContMDiffAt.fderiv_right (g := fun y a ↦ S (y, a)) (hS x) le_rfl).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y ↦ familyFiberDeriv_eq_fderiv S y)

/-- **The differential of the fibre derivative.** For a smooth generating family on a boundaryless
manifold, the differential of `∂_a S` at `x = (q, a)` sends `u = (δq, δa)` to the covector
`b ↦ d_a (d_q S)(b, δq) + D²_a S(δa, b)`: its part along `M` is the mixed Hessian
(`TauCeti.mixedHessian`), with the two orders of differentiation exchanged, and its part along
`A` is the second derivative of `S(q, ·)`. -/
theorem mvfderiv_familyFiberDeriv_apply_apply [I.Boundaryless] [IsManifold I ∞ M]
    (hS : ContMDiff (I.prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) (x : M × A)
    (u : TangentSpace (I.prod 𝓘(ℝ, A)) x) (b : A) :
    mvfderiv (I.prod 𝓘(ℝ, A)) (familyFiberDeriv S) x u b =
      mixedHessian I 𝓘(ℝ, A) S x b u.1 + fderiv ℝ (fderiv ℝ (fun a ↦ S (x.1, a))) x.2 u.2 b := by
  have hD := ((contMDiff_familyFiberDeriv hS) x).mdifferentiableAt (by simp)
  rw [hD.mvfderiv_prod_eq_add_apply, add_apply]
  congr 1
  · -- Along `M`, the fibre derivative is `q ↦ d_a S(q, a)`, whose derivative is the mixed Hessian
    -- of the transposed function.
    have h := mixedHessian_comp_swap_apply ((hS x).of_le (by simp)) u.1 b
    rw [mixedHessian_def] at h
    simpa only [familyFiberDeriv_def, Function.comp_apply, Prod.swap_prod_mk, Prod.fst_swap,
      Prod.snd_swap] using h
  · rw [funext fun a ↦ familyFiberDeriv_eq_fderiv S (x.1, a), mvfderiv_eq_fderiv]
    -- `NormedSpace.fromTangentSpace` is the identity of `A`, the tangent space of `A`.
    rfl

/-- At a point where the differential of the fibre derivative is surjective, a vector which both
it and the differential of the source projection kill is zero. -/
private theorem eq_zero_of_mfderiv_generatingSource_eq_zero [I.Boundaryless] [IsManifold I ∞ M]
    (hS : ContMDiff (I.prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) {x : M × A}
    (hsurj : Function.Surjective
      (mfderiv (I.prod 𝓘(ℝ, A)) 𝓘(ℝ, A →L[ℝ] ℝ) (familyFiberDeriv S) x))
    {w : E × A} (hker : mvfderiv (I.prod 𝓘(ℝ, A)) (familyFiberDeriv S) x w = 0)
    (hsrc :
      mfderiv (I.prod 𝓘(ℝ, A)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (generatingSource I S) x w = 0) :
    w = 0 := by
  -- Read the differential of the source projection between the model spaces.
  obtain ⟨T, hT⟩ : ∃ T : E × A →L[ℝ] E × (E →L[ℝ] ℝ),
      mfderiv (I.prod 𝓘(ℝ, A)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (generatingSource I S) x = T :=
    ⟨_, rfl⟩
  replace hsrc : T w = 0 := by
    rw [← hT]
    exact hsrc
  -- The source projection keeps the base component, so `δq = 0`.
  have h₁ : w.1 = 0 := by
    have h := DFunLike.congr_fun (hT ▸ fst_comp_mfderiv_generatingSource hS x :
      ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ) ∘L T = ContinuousLinearMap.fst ℝ E A) w
    rw [ContinuousLinearMap.comp_apply, hsrc] at h
    exact h.symm
  -- On the auxiliary directions the source projection acts by the mixed Hessian.
  have hH : mixedHessian I 𝓘(ℝ, A) S x w.2 = 0 := by
    have h := DFunLike.congr_fun (hT ▸ mfderiv_generatingSource_comp_inr hS x :
      T ∘L ContinuousLinearMap.inr ℝ E A =
        ContinuousLinearMap.inr ℝ E (E →L[ℝ] ℝ) ∘L mixedHessian I 𝓘(ℝ, A) S x) w.2
    have h₂ : (T (ContinuousLinearMap.inr ℝ E A w.2)).2 = mixedHessian I 𝓘(ℝ, A) S x w.2 :=
      congrArg Prod.snd h
    rw [show ContinuousLinearMap.inr ℝ E A w.2 = w from Prod.ext h₁.symm rfl, hsrc] at h₂
    exact h₂.symm
  have hg : ContDiff ℝ ∞ (fun a ↦ S (x.1, a)) :=
    contMDiff_iff_contDiff.mp (hS.comp (contMDiff_const.prodMk contMDiff_id))
  have hsymm := (hg.contDiffAt (x := x.2)).isSymmSndFDerivAt (by simp)
  -- Every value `β = D(∂_a S) u` of the differential of the fibre derivative kills `b = w.2`.
  refine Prod.ext h₁ (SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun β ↦ ?_)
  obtain ⟨u, hu⟩ := hsurj β
  have hβ := mvfderiv_familyFiberDeriv_apply_apply hS x u w.2
  have hw := mvfderiv_familyFiberDeriv_apply_apply hS x w u.2
  rw [hker, h₁, map_zero, zero_add, zero_apply] at hw
  rw [mvfderiv_apply_eq_mfderiv_apply, hu, hH, zero_apply, zero_add, hsymm] at hβ
  rw [hβ, ← hw]

/-! ### The fibre-critical set as a manifold -/

section CriticalSet

variable [I.Boundaryless] [IsManifold I ∞ M] [FiniteDimensional ℝ E] [FiniteDimensional ℝ A]
  (hS : ContMDiff (I.prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S)
  (hreg : IsRegularValue (I.prod 𝓘(ℝ, A)) 𝓘(ℝ, A →L[ℝ] ℝ) (familyFiberDeriv S) 0)

/-- The fibre-critical set has the dimension of `M`. -/
private theorem finrank_prod_sub_finrank_dual :
    finrank ℝ (E × A) - finrank ℝ (A →L[ℝ] ℝ) = finrank ℝ E := by
  rw [finrank_prod, ContinuousLinearMap.dual_finrank_eq]
  omega

/-- The cotangent bundle `T*M` has twice the dimension of the fibre-critical set. -/
private theorem two_mul_finrank_eq_finrank_prod_dual :
    2 * finrank ℝ (Fin (finrank ℝ E) → ℝ) = finrank ℝ (E × (E →L[ℝ] ℝ)) := by
  simp only [finrank_fin_fun, finrank_prod, ContinuousLinearMap.dual_finrank_eq]
  ring

/-- The **fibre-critical set** `{(q, a) | ∂_a S(q, a) = 0}` of a smooth generating family `S` on
`M × A` which is transverse, in the sense that `0` is a regular value of the fibre derivative
`∂_a S`, as a charted space modelled on `Fin (dim M) → ℝ`: the atlas
`TauCeti.regularLevelChartedSpace` of the regular level. Install it locally with `letI`. -/
@[instance_reducible]
def familyCriticalSetChartedSpace :
    ChartedSpace (Fin (finrank ℝ E) → ℝ) {x : M × A // familyFiberDeriv S x = 0} :=
  regularLevelChartedSpace (fun x _ ↦ (contMDiff_familyFiberDeriv hS x).of_le (by simp)) hreg
    finrank_prod_sub_finrank_dual

/-- The fibre-critical set of a smooth transverse generating family is a smooth manifold of the
dimension of `M`. -/
theorem isManifold_familyCriticalSet :
    letI := familyCriticalSetChartedSpace hS hreg
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E) → ℝ) ∞ {x : M × A // familyFiberDeriv S x = 0} :=
  isManifold_regularLevel (by simp) (fun x _ ↦ contMDiff_familyFiberDeriv hS x) hreg
    finrank_prod_sub_finrank_dual

/-- The fibre-critical set of a smooth transverse generating family is smoothly embedded in
`M × A`. -/
theorem isSmoothEmbedding_coe_familyCriticalSet :
    letI := familyCriticalSetChartedSpace hS hreg
    IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E) → ℝ) (I.prod 𝓘(ℝ, A)) ∞
      (Subtype.val : {x : M × A // familyFiberDeriv S x = 0} → M × A) :=
  isSmoothEmbedding_coe_regularLevel (by simp) (fun x _ ↦ contMDiff_familyFiberDeriv hS x)
    hreg finrank_prod_sub_finrank_dual

/-- The tangent space of the fibre-critical set at `z` is the kernel of the differential of the
fibre derivative there. -/
theorem range_mfderiv_coe_familyCriticalSet (z : {x : M × A // familyFiberDeriv S x = 0}) :
    letI := familyCriticalSetChartedSpace hS hreg
    (mfderiv 𝓘(ℝ, Fin (finrank ℝ E) → ℝ) (I.prod 𝓘(ℝ, A))
      (Subtype.val : {x : M × A // familyFiberDeriv S x = 0} → M × A) z).range =
      (mfderiv (I.prod 𝓘(ℝ, A)) 𝓘(ℝ, A →L[ℝ] ℝ) (familyFiberDeriv S) z.val).ker :=
  range_mfderiv_coe_regularLevel _ hreg _ z

/-! ### The Lagrangian immersion -/

/-- **The fibre-critical set is exact with primitive `S`.** Along the inclusion of the
fibre-critical set of a smooth transverse generating family, the source projection
`(q, a) ↦ (q, d_q S(q, a))` pulls the Liouville form of `T*M` back to the differential of the
restriction of `S`. Indeed `dS = d_q S + ∂_a S`, and `∂_a S` vanishes on the fibre-critical
set. -/
theorem mpullback_generatingSource_comp_coe_liouvilleForm :
    letI := familyCriticalSetChartedSpace hS hreg
    mpullback 𝓘(ℝ, Fin (finrank ℝ E) → ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
        (generatingSource I S ∘ (Subtype.val : {x : M × A // familyFiberDeriv S x = 0} → M × A))
        (liouvilleForm I M).val =
      mextDeriv (RoughForm.ofFunction 𝓘(ℝ, Fin (finrank ℝ E) → ℝ)
        (S ∘ (Subtype.val : {x : M × A // familyFiberDeriv S x = 0} → M × A))) := by
  let _ := familyCriticalSetChartedSpace hS hreg
  have := isManifold_familyCriticalSet hS hreg
  have hval := (isSmoothEmbedding_coe_familyCriticalSet hS hreg).contMDiff
  funext z
  ext v
  have hval' : MDifferentiableAt _ _ (Subtype.val :
      {x : M × A // familyFiberDeriv S x = 0} → M × A) z :=
    (hval z).mdifferentiableAt (by simp)
  have hSz : MDifferentiableAt (I.prod 𝓘(ℝ, A)) 𝓘(ℝ) S z.val :=
    (hS z.val).mdifferentiableAt (by simp)
  rw [mpullback_liouvilleForm_apply_of_proj_comp_eq (ψ := generatingSource I S ∘ Subtype.val)
      (g := Prod.fst ∘ Subtype.val) (fun _ ↦ proj_generatingSource _)
      (((contMDiff_generatingSource hS).comp hval z).mdifferentiableAt (by simp)),
    mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    mvfderiv_comp_apply_of_eq z hSz hval' rfl, hSz.mvfderiv_prod_eq_add_apply,
    mfderiv_comp z (mdifferentiableAt_fst) hval', mfderiv_fst]
  have h0 : mvfderiv 𝓘(ℝ, A) (fun y ↦ S (z.val.1, y)) z.val.2 = 0 :=
    (familyFiberDeriv_def S z.val).symm.trans z.property
  rw [h0]
  -- The zero covector is typed on the tangent space of `A`, which is `A` itself.
  erw [zero_apply, add_zero]
  exact DFunLike.congr_fun (generatingSource_snd (I := I) (S := S) z.val) _

/-- **The source projection immerses the fibre-critical set.** At every point of the
fibre-critical set of a smooth transverse generating family, the differential of
`(q, a) ↦ (q, d_q S(q, a))` restricted to the fibre-critical set is injective. -/
theorem injective_mfderiv_generatingSource_comp_coe
    (z : {x : M × A // familyFiberDeriv S x = 0}) :
    letI := familyCriticalSetChartedSpace hS hreg
    Function.Injective (mfderiv 𝓘(ℝ, Fin (finrank ℝ E) → ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (generatingSource I S ∘ (Subtype.val : {x : M × A // familyFiberDeriv S x = 0} → M × A))
      z) := by
  let _ := familyCriticalSetChartedSpace hS hreg
  have := isManifold_familyCriticalSet hS hreg
  have hemb := isSmoothEmbedding_coe_familyCriticalSet hS hreg
  rw [mfderiv_comp z ((contMDiff_generatingSource hS z.val).mdifferentiableAt (by simp))
    ((hemb.contMDiff z).mdifferentiableAt (by simp))]
  refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
  obtain ⟨w, hw⟩ : ∃ w : E × A,
      mfderiv 𝓘(ℝ, Fin (finrank ℝ E) → ℝ) (I.prod 𝓘(ℝ, A)) Subtype.val z v = w := ⟨_, rfl⟩
  -- The tangent vector `w` of the fibre-critical set lies in the kernel of the differential of
  -- the fibre derivative.
  have hker : w ∈ (mfderiv 𝓘(ℝ, Fin (finrank ℝ E) → ℝ) (I.prod 𝓘(ℝ, A)) Subtype.val z).range :=
    ⟨v, hw⟩
  rw [range_mfderiv_coe_familyCriticalSet hS hreg z] at hker
  have hw0 : w = 0 := eq_zero_of_mfderiv_generatingSource_eq_zero hS
    (isRegularPoint_iff.mp (hreg.isRegularPoint z.property)) hker (hw ▸ hv)
  exact hemb.isImmersion.mfderiv_injective (by simp) z (hw.trans (hw0.trans (map_zero _).symm))

/-- **The fibre-critical set of a generating family is an exact Lagrangian.** On a boundaryless
finite-dimensional manifold `M`, let `S` be a smooth generating family on `M × A` which is
transverse: `0` is a regular value of its fibre derivative `∂_a S`. Then the source projection
`(q, a) ↦ (q, d_q S(q, a))` restricted to the fibre-critical set is an exact Lagrangian map into
`T*M`, for the canonical symplectic form and the Liouville form, with primitive the restriction of
`S`. -/
theorem isExactLagrangianMap_generatingSource_comp_coe :
    letI := familyCriticalSetChartedSpace hS hreg
    (isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate.IsExactLagrangianMap
      𝓘(ℝ, Fin (finrank ℝ E) → ℝ) (liouvilleForm I M)
      (generatingSource I S ∘ (Subtype.val : {x : M × A // familyFiberDeriv S x = 0} → M × A))
      (S ∘ (Subtype.val : {x : M × A // familyFiberDeriv S x = 0} → M × A)) := by
  let _ := familyCriticalSetChartedSpace hS hreg
  have := isManifold_familyCriticalSet hS hreg
  have hval := (isSmoothEmbedding_coe_familyCriticalSet hS hreg).contMDiff
  refine (SmoothTwoForm.IsNondegenerate.isExactLagrangianMap_iff_of_finrank
    symplecticForm_eq_neg_mextDerivₗ ((contMDiff_generatingSource hS).comp hval)
    (injective_mfderiv_generatingSource_comp_coe hS hreg) ?_).mpr
    ⟨hS.comp hval, mpullback_generatingSource_comp_coe_liouvilleForm hS hreg⟩
  exact two_mul_finrank_eq_finrank_prod_dual

/-- **The fibre-critical set of a generating family is a Lagrangian immersion.** For a smooth
transverse generating family `S` on `M × A`, the source projection `(q, a) ↦ (q, d_q S(q, a))`
restricted to the fibre-critical set is a Lagrangian immersion into `T*M`. Its image need not be
embedded. -/
theorem isLagrangianImmersion_generatingSource_comp_coe :
    letI := familyCriticalSetChartedSpace hS hreg
    (isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate.IsLagrangianImmersion
      𝓘(ℝ, Fin (finrank ℝ E) → ℝ)
      (generatingSource I S ∘
        (Subtype.val : {x : M × A // familyFiberDeriv S x = 0} → M × A)) := by
  let _ := familyCriticalSetChartedSpace hS hreg
  have := isManifold_familyCriticalSet hS hreg
  have hval := (isSmoothEmbedding_coe_familyCriticalSet hS hreg).contMDiff
  refine ⟨((contMDiff_generatingSource hS).comp hval).isImmersion_of_injective_mfderiv (by simp)
    (injective_mfderiv_generatingSource_comp_coe hS hreg),
    (isExactLagrangianMap_generatingSource_comp_coe hS hreg).isLagrangianMap.isIsotropicMap,
    two_mul_finrank_eq_finrank_prod_dual⟩

end CriticalSet

end TauCeti.CotangentBundle

/-! ### Families of correspondences -/

open Function

namespace TauCeti.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F H' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] {S : (M × N) × A → ℝ}

/-! ### The family relation -/

variable (I J) in
/-- The **cotangent relation generated by a family** `S((q, Q), a)` on `(M × N) × A`, parametrized
by `((q, Q), a)` as `((q, d_q S), (Q, -d_Q S)) ∈ T*M × T*N`: at a parameter `a` it is the
relation generated by `S(·, a)`. Restricted to the points where `S` is stationary in `a`, it is a
Lagrangian immersion for a smooth transverse family on finite-dimensional boundaryless manifolds,
with `A` finite-dimensional
(`TauCeti.CotangentBundle.isLagrangianImmersion_familyCorrespondence_comp_coe`). -/
def familyCorrespondence (S : (M × N) × A → ℝ) (z : (M × N) × A) :
    CotangentBundle I M × CotangentBundle J N :=
  generatingCorrespondence I J (fun x ↦ S (x, z.2)) z.1

omit [NormedAddCommGroup A] [NormedSpace ℝ A] in
/-- At a parameter `a`, the family relation is the relation generated by `S(·, a)`. -/
@[simp]
theorem familyCorrespondence_apply (x : M × N) (a : A) :
    familyCorrespondence I J S (x, a) = generatingCorrespondence I J (fun x' ↦ S (x', a)) x :=
  (rfl)

omit [NormedAddCommGroup A] [NormedSpace ℝ A] in
/-- The family relation lies over the pair of base points. -/
@[simp]
theorem map_proj_familyCorrespondence (z : (M × N) × A) :
    Prod.map TotalSpace.proj TotalSpace.proj (familyCorrespondence I J S z) = z.1 := by
  simp [familyCorrespondence]

omit [NormedAddCommGroup A] [NormedSpace ℝ A] in
/-- The family relation at `z`, written out: the covectors `d_q S` at `q` and `-d_Q S` at `Q`. -/
theorem familyCorrespondence_eq_mk (z : (M × N) × A) :
    familyCorrespondence I J S z =
      (TotalSpace.mk' (E →L[ℝ] ℝ) z.1.1 (mvfderiv I (fun q ↦ S ((q, z.1.2), z.2)) z.1.1),
        TotalSpace.mk' (F →L[ℝ] ℝ) z.1.2 (-mvfderiv J (fun Q ↦ S ((z.1.1, Q), z.2)) z.1.2)) := by
  simp only [familyCorrespondence, generatingCorrespondence_apply, generatingSource_eq_mk,
    generatingTarget_eq_mk]

/-! ### Smoothness -/

section Smooth

variable [IsManifold I 2 M] [IsManifold J 2 N]

/-- The source component `((q, Q), a) ↦ (q, d_q S)` of the family relation of a smooth family is
smooth. -/
theorem contMDiff_familyCorrespondence_fst
    (hS : ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) :
    ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun z ↦ (familyCorrespondence I J S z).1) := by
  -- Reassociated, this is the source projection of the relation generated by `S` on
  -- `M × (N × A)`.
  refine ((contMDiff_generatingSource (I := I) (J := J.prod 𝓘(ℝ, A))
    (S := fun p : M × (N × A) ↦ S ((p.1, p.2.1), p.2.2))
    (hS.comp ((contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd)).prodMk
      (contMDiff_snd.comp contMDiff_snd)))).comp ((contMDiff_fst.comp contMDiff_fst).prodMk
        ((contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd))).congr fun z ↦ ?_
  simp only [familyCorrespondence, generatingCorrespondence_apply, comp_apply,
    generatingSource_eq_mk]

/-- The target component `((q, Q), a) ↦ (Q, -d_Q S)` of the family relation of a smooth family is
smooth. -/
theorem contMDiff_familyCorrespondence_snd
    (hS : ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) :
    ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
      (fun z ↦ (familyCorrespondence I J S z).2) := by
  -- Reassociated, this is the target projection of the relation generated by `S` on
  -- `(M × A) × N`.
  refine ((contMDiff_generatingTarget (I := I.prod 𝓘(ℝ, A)) (J := J)
    (S := fun p : (M × A) × N ↦ S ((p.1.1, p.2), p.1.2))
    (hS.comp (((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd).prodMk
      (contMDiff_snd.comp contMDiff_fst)))).comp (((contMDiff_fst.comp contMDiff_fst).prodMk
        contMDiff_snd).prodMk (contMDiff_snd.comp contMDiff_fst))).congr fun z ↦ ?_
  simp only [familyCorrespondence, generatingCorrespondence_apply, comp_apply,
    generatingTarget_eq_mk]

/-- The family relation of a smooth family is smooth. -/
theorem contMDiff_familyCorrespondence (hS : ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) :
    ContMDiff ((I.prod J).prod 𝓘(ℝ, A))
      ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod (J.prod 𝓘(ℝ, F →L[ℝ] ℝ))) ∞
      (familyCorrespondence I J S) :=
  (contMDiff_familyCorrespondence_fst hS).prodMk (contMDiff_familyCorrespondence_snd hS)

end Smooth

/-! ### Exactness -/

section Differential

/-- The derivative of the projection `((q, Q), a) ↦ q`. -/
private theorem hasMFDerivAt_fst_fst (z : (M × N) × A) :
    HasMFDerivAt ((I.prod J).prod 𝓘(ℝ, A)) I (fun z : (M × N) × A ↦ z.1.1) z
      ((ContinuousLinearMap.fst ℝ E F).comp (ContinuousLinearMap.fst ℝ (E × F) A)) :=
  (hasMFDerivAt_fst (I := I) (I' := J) z.1).comp z
    (hasMFDerivAt_fst (I := I.prod J) (I' := 𝓘(ℝ, A)) z)

/-- The derivative of the projection `((q, Q), a) ↦ Q`. -/
private theorem hasMFDerivAt_snd_fst (z : (M × N) × A) :
    HasMFDerivAt ((I.prod J).prod 𝓘(ℝ, A)) J (fun z : (M × N) × A ↦ z.1.2) z
      ((ContinuousLinearMap.snd ℝ E F).comp (ContinuousLinearMap.fst ℝ (E × F) A)) :=
  (hasMFDerivAt_snd (I := I) (I' := J) z.1).comp z
    (hasMFDerivAt_fst (I := I.prod J) (I' := 𝓘(ℝ, A)) z)

variable [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- **The family relation pulls the Liouville primitive back to `dS - ∂_a S (da)`.** At every
point `z = (x, a)`, the pullback of the one-form `pr₁^*λ_M - pr₂^*λ_N` on `T*M × T*N` along the
family relation takes the value `dS(u) - ∂_a S(z)(u.2)` on a tangent vector `u = (u.1, u.2)`. -/
theorem mpullback_familyCorrespondence_liouvilleForm_apply
    (hS : ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) (z : (M × N) × A)
    (v : Fin 1 → TangentSpace ((I.prod J).prod 𝓘(ℝ, A)) z) :
    mpullback (F := ℝ) (k := 1) ((I.prod J).prod 𝓘(ℝ, A))
        ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
        (familyCorrespondence I J S)
        (SmoothForm.mpullback (Prod.fst : CotangentBundle I M × CotangentBundle J N → _)
            (contMDiff_fst (I := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J := J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
            (liouvilleForm I M) -
          SmoothForm.mpullback (Prod.snd : CotangentBundle I M × CotangentBundle J N → _)
            (contMDiff_snd (I := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J := J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
            (liouvilleForm J N)).val z v =
      mvfderiv ((I.prod J).prod 𝓘(ℝ, A)) S z (v 0) - familyFiberDeriv S z (v 0).2 := by
  have hq : mfderiv ((I.prod J).prod 𝓘(ℝ, A)) I (fun z : (M × N) × A ↦ z.1.1) z (v 0) =
      ((v 0).1.1 : E) :=
    DFunLike.congr_fun (hasMFDerivAt_fst_fst z).mfderiv (v 0)
  have hQ : mfderiv ((I.prod J).prod 𝓘(ℝ, A)) J (fun z : (M × N) × A ↦ z.1.2) z (v 0) =
      ((v 0).1.2 : F) :=
    DFunLike.congr_fun (hasMFDerivAt_snd_fst z).mfderiv (v 0)
  have hSz : MDifferentiableAt ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) S z :=
    (hS z).mdifferentiableAt (by simp)
  have hSx : MDifferentiableAt (I.prod J) 𝓘(ℝ) (fun x ↦ S (x, z.2)) z.1 :=
    ((hS.comp (contMDiff_id.prodMk contMDiff_const)) z.1).mdifferentiableAt (by simp)
  rw [mpullback_prodMk_liouvilleForm_apply (contMDiff_familyCorrespondence_fst hS)
      (contMDiff_familyCorrespondence_snd hS) (g₁ := fun z ↦ z.1.1) (g₂ := fun z ↦ z.1.2)
      (fun _ ↦ by simp [familyCorrespondence]) (fun _ ↦ by simp [familyCorrespondence]) z v,
    hq, hQ, familyCorrespondence_eq_mk]
  -- The two covectors of `G` are the partial differentials of `S(·, a)`, and `dS` is their sum
  -- plus the fibre derivative.
  have h₁ := hSz.mvfderiv_prod_eq_add_apply (v 0)
  have h₂ := hSx.mvfderiv_prod_eq_add_apply (v 0).1
  have h₃ : mvfderiv 𝓘(ℝ, A) (fun a ↦ S (z.1, a)) z.2 (v 0).2 = familyFiberDeriv S z (v 0).2 :=
    DFunLike.congr_fun (familyFiberDeriv_def S z).symm _
  have h₄ := neg_apply (mvfderiv J (fun Q ↦ S ((z.1.1, Q), z.2)) z.1.2)
    (v 0).1.2
  simp only at h₂ ⊢
  linear_combination -h₁ - h₂ - h₃ - h₄

/-! ### Injectivity at a transverse point -/

/-- The family relation lies over the pair of base points, so the derivatives of its two components
determine the `M × N` component of a tangent vector. -/
private theorem fst_eq_zero_of_mfderiv_familyCorrespondence_eq_zero
    (hS : ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) {z : (M × N) × A}
    {u : TangentSpace ((I.prod J).prod 𝓘(ℝ, A)) z}
    (h₁ : mfderiv ((I.prod J).prod 𝓘(ℝ, A)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun z ↦ (familyCorrespondence I J S z).1) z u = 0)
    (h₂ : mfderiv ((I.prod J).prod 𝓘(ℝ, A)) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun z ↦ (familyCorrespondence I J S z).2) z u = 0) :
    (u.1 : E × F) = 0 := by
  have hπ₁ := mfderiv_comp_apply z
    ((Bundle.contMDiff_proj (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
      (familyCorrespondence I J S z).1).mdifferentiableAt (n := 1) one_ne_zero)
    ((contMDiff_familyCorrespondence_fst hS z).mdifferentiableAt (by simp)) u
  have hπ₂ := mfderiv_comp_apply z
    ((Bundle.contMDiff_proj (fun y : N ↦ TangentSpace J y →L[ℝ] ℝ)
      (familyCorrespondence I J S z).2).mdifferentiableAt (n := 1) one_ne_zero)
    ((contMDiff_familyCorrespondence_snd hS z).mdifferentiableAt (by simp)) u
  rw [h₁, map_zero] at hπ₁
  rw [h₂, map_zero] at hπ₂
  -- The base points of the two components are `q` and `Q`.
  rw [show (π (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) ∘
      fun z ↦ (familyCorrespondence I J S z).1) = fun z ↦ z.1.1 from
    funext fun _ ↦ by simp [familyCorrespondence], (hasMFDerivAt_fst_fst z).mfderiv] at hπ₁
  rw [show (π (F →L[ℝ] ℝ) (fun y : N ↦ TangentSpace J y →L[ℝ] ℝ) ∘
      fun z ↦ (familyCorrespondence I J S z).2) = fun z ↦ z.1.2 from
    funext fun _ ↦ by simp [familyCorrespondence], (hasMFDerivAt_snd_fst z).mfderiv] at hπ₂
  exact Prod.ext hπ₁ hπ₂

/-- If the source covector `d_q S` of the family relation does not move in the direction `(0, b)`,
then `a ↦ d_q S((q, Q), a)` is differentiable with zero derivative in the direction `b`. -/
private theorem fderiv_mvfderiv_fst_apply_eq_zero
    (hS : ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) {z : (M × N) × A} {b : A}
    (h₁ : mfderiv ((I.prod J).prod 𝓘(ℝ, A)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun z ↦ (familyCorrespondence I J S z).1) z ((0, b) : (E × F) × A) = 0) :
    DifferentiableAt ℝ (fun a ↦ mvfderiv I (fun q ↦ S ((q, z.1.2), a)) z.1.1) z.2 ∧
      fderiv ℝ (fun a ↦ mvfderiv I (fun q ↦ S ((q, z.1.2), a)) z.1.1) z.2 b = 0 := by
  set c : A → E →L[ℝ] ℝ := fun a ↦ mvfderiv I (fun q ↦ S ((q, z.1.2), a)) z.1.1
  have hd : DifferentiableAt ℝ c z.2 :=
    ((Manifold.contMDiffAt_mvfderiv_of_contMDiffAt_uncurry (I := I) (m := 1)
      (G := fun a q ↦ S ((q, z.1.2), a))
      ((hS.comp ((contMDiff_snd.prodMk contMDiff_const).prodMk contMDiff_fst)) (z.2, z.1.1))
      (by simp)).mdifferentiableAt one_ne_zero).differentiableAt
  refine ⟨hd, ?_⟩
  -- Along `a ↦ (z.1, a)` the source component of `G` is the curve `a ↦ (q, c a)` in the fibre
  -- over `q`, with derivative `(0, dc)`.
  have h : mfderiv 𝓘(ℝ, A) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun a ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) z.1.1
        (c a)) z.2 b = 0 := by
    have hγ : (fun z ↦ (familyCorrespondence I J S z).1) ∘ (fun a ↦ (z.1, a)) =
        fun a ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) z.1.1
          (c a) :=
      funext fun a ↦ congrArg Prod.fst (familyCorrespondence_eq_mk (z.1, a))
    rw [← hγ]
    have hι : MDifferentiableAt 𝓘(ℝ, A) ((I.prod J).prod 𝓘(ℝ, A)) (fun a ↦ (z.1, a)) z.2 :=
      mdifferentiableAt_const.prodMk mdifferentiableAt_id
    exact (mfderiv_comp_apply z.2
      ((contMDiff_familyCorrespondence_fst hS _).mdifferentiableAt (by simp)) hι b).trans
        (by rw [mfderiv_prod_right]; exact h₁)
  exact (mfderiv_mk_apply_eq_zero_iff z.1.1 hd.hasFDerivAt.hasMFDerivAt b).mp h

/-- If the target covector `-d_Q S` of the family relation does not move in the direction
`(0, b)`, then `a ↦ d_Q S((q, Q), a)` is differentiable with zero derivative in the direction
`b`. -/
private theorem fderiv_mvfderiv_snd_apply_eq_zero
    (hS : ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) {z : (M × N) × A} {b : A}
    (h₂ : mfderiv ((I.prod J).prod 𝓘(ℝ, A)) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun z ↦ (familyCorrespondence I J S z).2) z ((0, b) : (E × F) × A) = 0) :
    DifferentiableAt ℝ (fun a ↦ mvfderiv J (fun Q ↦ S ((z.1.1, Q), a)) z.1.2) z.2 ∧
      fderiv ℝ (fun a ↦ mvfderiv J (fun Q ↦ S ((z.1.1, Q), a)) z.1.2) z.2 b = 0 := by
  set c : A → F →L[ℝ] ℝ := fun a ↦ mvfderiv J (fun Q ↦ S ((z.1.1, Q), a)) z.1.2
  have hd : DifferentiableAt ℝ c z.2 :=
    ((Manifold.contMDiffAt_mvfderiv_of_contMDiffAt_uncurry (I := J) (m := 1)
      (G := fun a Q ↦ S ((z.1.1, Q), a))
      ((hS.comp ((contMDiff_const.prodMk contMDiff_snd).prodMk contMDiff_fst)) (z.2, z.1.2))
      (by simp)).mdifferentiableAt one_ne_zero).differentiableAt
  refine ⟨hd, ?_⟩
  -- Along `a ↦ (z.1, a)` the target component of `G` is the curve `a ↦ (Q, -c a)` in the fibre
  -- over `Q`, with derivative `(0, -dc)`.
  have h : mfderiv 𝓘(ℝ, A) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun a ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun x : N ↦ TangentSpace J x →L[ℝ] ℝ) z.1.2
        (-c a)) z.2 b = 0 := by
    have hγ : (fun z ↦ (familyCorrespondence I J S z).2) ∘ (fun a ↦ (z.1, a)) =
        fun a ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun x : N ↦ TangentSpace J x →L[ℝ] ℝ) z.1.2
          (-c a) :=
      funext fun a ↦ congrArg Prod.snd (familyCorrespondence_eq_mk (z.1, a))
    rw [← hγ]
    have hι : MDifferentiableAt 𝓘(ℝ, A) ((I.prod J).prod 𝓘(ℝ, A)) (fun a ↦ (z.1, a)) z.2 :=
      mdifferentiableAt_const.prodMk mdifferentiableAt_id
    exact (mfderiv_comp_apply z.2
      ((contMDiff_familyCorrespondence_snd hS _).mdifferentiableAt (by simp)) hι b).trans
        (by rw [mfderiv_prod_right]; exact h₂)
  -- The tangent space of `A` at `z.2` is `A` itself.
  have h' : (-fderiv ℝ c z.2) b = 0 := (mfderiv_mk_apply_eq_zero_iff (c := fun a ↦ -c a) z.1.2
    hd.hasFDerivAt.neg.hasMFDerivAt b).mp h
  rwa [neg_apply, neg_eq_zero] at h'

/-- If neither covector of the family relation moves in the direction `(0, b)`, then the fibre
derivative `∂_a S(·)(b)` does not move on `M × N` either: by the symmetry of mixed derivatives its
differential is the derivative of `d_x S` in the direction `b`. -/
private theorem mvfderiv_familyFiberDeriv_apply_eq_zero
    (hS : ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) {z : (M × N) × A} {b : A}
    (h₁ : mfderiv ((I.prod J).prod 𝓘(ℝ, A)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun z ↦ (familyCorrespondence I J S z).1) z ((0, b) : (E × F) × A) = 0)
    (h₂ : mfderiv ((I.prod J).prod 𝓘(ℝ, A)) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun z ↦ (familyCorrespondence I J S z).2) z ((0, b) : (E × F) × A) = 0) (w : E × F) :
    mvfderiv (I.prod J) (fun x ↦ familyFiberDeriv S (x, z.2) b) z.1 w = 0 := by
  -- Along the curve `a ↦ (z.1, a)` the covectors `d_q S` and `d_Q S` at the fixed points `q` and
  -- `Q` do not move in the direction `b`.
  set c₁ : A → E →L[ℝ] ℝ := fun a ↦ mvfderiv I (fun q ↦ S ((q, z.1.2), a)) z.1.1
  set c₂ : A → F →L[ℝ] ℝ := fun a ↦ mvfderiv J (fun Q ↦ S ((z.1.1, Q), a)) z.1.2
  obtain ⟨hd₁, hc₁⟩ : DifferentiableAt ℝ c₁ z.2 ∧ fderiv ℝ c₁ z.2 b = 0 :=
    fderiv_mvfderiv_fst_apply_eq_zero hS h₁
  obtain ⟨hd₂, hc₂⟩ : DifferentiableAt ℝ c₂ z.2 ∧ fderiv ℝ c₂ z.2 b = 0 :=
    fderiv_mvfderiv_snd_apply_eq_zero hS h₂
  -- The differential of `S(·, a)` at `x` is the sum of the two covectors.
  have hfun : (fun a ↦ mvfderiv (I.prod J) (fun x ↦ S (x, a)) z.1 w) =
      fun a ↦ c₁ a w.1 + c₂ a w.2 := by
    funext a
    have hSa : MDifferentiableAt (I.prod J) 𝓘(ℝ) (fun x ↦ S (x, a)) z.1 :=
      ((hS.comp (contMDiff_id.prodMk contMDiff_const)) z.1).mdifferentiableAt (by simp)
    exact hSa.mvfderiv_prod_eq_add_apply w
  have hD := (hd₁.hasFDerivAt.clm_apply (hasFDerivAt_const w.1 z.2)).fun_add
    (hd₂.hasFDerivAt.clm_apply (hasFDerivAt_const w.2 z.2))
  have hmix := TauCeti.Manifold.fderiv_mvfderiv_apply (F := fun a x ↦ S (x, a)) (a := z.2)
    (x := z.1) (((hS.comp (contMDiff_snd.prodMk contMDiff_fst)) _).of_le (by simp)) w b
  simp only [familyFiberDeriv_apply]
  rw [← hmix, hfun, hD.fderiv]
  simp [hc₁, hc₂]

/-- The differential of the fibre derivative, evaluated on `b`: its `M × N` part is the
differential of `∂_a S(·)(b)` and its `A` part is the second derivative of `S(x, ·)`. -/
private theorem mfderiv_familyFiberDeriv_apply_apply
    (hS : ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) (z : (M × N) × A)
    (u : TangentSpace ((I.prod J).prod 𝓘(ℝ, A)) z) (b : A) :
    mvfderiv ((I.prod J).prod 𝓘(ℝ, A)) (familyFiberDeriv S) z u b =
      mvfderiv (I.prod J) (fun x ↦ familyFiberDeriv S (x, z.2) b) z.1 u.1 +
        fderiv ℝ (fderiv ℝ fun a ↦ S (z.1, a)) z.2 u.2 b := by
  have hD : MDifferentiableAt ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ, A →L[ℝ] ℝ)
      (familyFiberDeriv S) z :=
    (contMDiff_familyFiberDeriv hS z).mdifferentiableAt (by simp)
  have hb : MDifferentiableAt ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ)
      (fun z' ↦ familyFiberDeriv S z' b) z :=
    (ContinuousLinearMap.apply ℝ ℝ b).mdifferentiableAt.comp z hD
  have hSx : ContDiff ℝ ∞ fun a ↦ S (z.1, a) :=
    contMDiff_iff_contDiff.mp (hS.comp (contMDiff_const.prodMk contMDiff_id))
  have hA : HasFDerivAt (fun a ↦ familyFiberDeriv S (z.1, a) b)
      ((fderiv ℝ (fderiv ℝ fun a ↦ S (z.1, a)) z.2).flip b) z.2 := by
    simpa using ((hSx.fderiv_right (m := 1) (by simp)).differentiable (by simp)
      z.2).hasFDerivAt.clm_apply (hasFDerivAt_const b z.2)
  rw [← ContinuousLinearMap.apply_apply b,
    ← (ContinuousLinearMap.apply ℝ ℝ b).mvfderiv_comp_apply hD u]
  simp only [Function.comp_def, ContinuousLinearMap.apply_apply]
  rw [hb.mvfderiv_prod_eq_add_apply u]
  -- In the `A` direction, `∂_a S(x, ·)(b)` is the derivative of `a ↦ dS(x, ·)_a (b)`.
  exact congrArg (_ + ·) ((mvfderiv_eq_fderiv_apply _ _ _).trans
    (DFunLike.congr_fun hA.fderiv u.2))

/-- At a transverse point, a tangent vector in the kernel of the differential of the fibre
derivative which both components of the differential of the family relation kill is zero. -/
private theorem eq_zero_of_mfderiv_familyCorrespondence_eq_zero
    (hS : ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) {z : (M × N) × A}
    (hsurj : Surjective
      (mfderiv ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ, A →L[ℝ] ℝ) (familyFiberDeriv S) z))
    {u : TangentSpace ((I.prod J).prod 𝓘(ℝ, A)) z}
    (hu : mfderiv ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ, A →L[ℝ] ℝ) (familyFiberDeriv S) z u = 0)
    (h₁ : mfderiv ((I.prod J).prod 𝓘(ℝ, A)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun z ↦ (familyCorrespondence I J S z).1) z u = 0)
    (h₂ : mfderiv ((I.prod J).prod 𝓘(ℝ, A)) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun z ↦ (familyCorrespondence I J S z).2) z u = 0) : u = 0 := by
  have hu₁ := fst_eq_zero_of_mfderiv_familyCorrespondence_eq_zero hS h₁ h₂
  obtain ⟨b, rfl⟩ : ∃ b : A, u = ((0, b) : (E × F) × A) := ⟨u.2, Prod.ext hu₁ rfl⟩
  -- The fibre derivative `∂_a S(·)(b)` does not move on `M × N`.
  have hmix := mvfderiv_familyFiberDeriv_apply_eq_zero hS h₁ h₂
  have hsymm : IsSymmSndFDerivAt ℝ (fun a ↦ S (z.1, a)) z.2 :=
    (contMDiff_iff_contDiff.mp (hS.comp (contMDiff_const.prodMk contMDiff_id))).contDiffAt
      |>.isSymmSndFDerivAt (by simp)
  -- Hence every covector in the range of `d(∂_a S)` vanishes on `b`: its value is the second
  -- derivative of `S(x, ·)` at `(·, b)`, which is symmetric and vanishes since `(0, b)` lies in
  -- the kernel.
  have hD (w : TangentSpace ((I.prod J).prod 𝓘(ℝ, A)) z) :
      mvfderiv ((I.prod J).prod 𝓘(ℝ, A)) (familyFiberDeriv S) z w b = 0 := by
    have h₀ := mfderiv_familyFiberDeriv_apply_apply hS z ((0, b) : (E × F) × A) w.2
    have hw := mfderiv_familyFiberDeriv_apply_apply hS z w b
    have hz : mvfderiv (I.prod J) (fun x ↦ familyFiberDeriv S (x, z.2) w.2) z.1 (0 : E × F) = 0 :=
      map_zero _
    have hb : mvfderiv ((I.prod J).prod 𝓘(ℝ, A)) (familyFiberDeriv S) z
        ((0, b) : (E × F) × A) w.2 = 0 := by
      have hu' : mvfderiv ((I.prod J).prod 𝓘(ℝ, A)) (familyFiberDeriv S) z
          ((0, b) : (E × F) × A) = (0 : A →L[ℝ] ℝ) :=
        (mvfderiv_apply_eq_mfderiv_apply _ _ _).trans hu
      exact (congrArg (fun φ : A →L[ℝ] ℝ ↦ φ w.2) hu').trans (by simp)
    linear_combination hw + hmix w.1 - hsymm b w.2 - h₀ + hb - hz
  refine Prod.ext rfl (SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun β ↦ ?_)
  obtain ⟨w, rfl⟩ := hsurj β
  rw [← mvfderiv_apply_eq_mfderiv_apply]
  exact hD w

/-- **Injectivity at a transverse point.** If the differential of the fibre derivative `∂_a S` of a
smooth family is surjective at `z`, the differential of the family relation is injective on the
kernel of the differential of `∂_a S`. -/
theorem injOn_mfderiv_familyCorrespondence_ker
    (hS : ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) {z : (M × N) × A}
    (hsurj : Surjective
      (mfderiv ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ, A →L[ℝ] ℝ) (familyFiberDeriv S) z)) :
    Set.InjOn
      (mfderiv ((I.prod J).prod 𝓘(ℝ, A))
        ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
        (familyCorrespondence I J S) z)
      (mfderiv ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ, A →L[ℝ] ℝ) (familyFiberDeriv S) z).ker := by
  have hprod := mfderiv_prodMk
    ((contMDiff_familyCorrespondence_fst hS z).mdifferentiableAt (by simp))
    ((contMDiff_familyCorrespondence_snd hS z).mdifferentiableAt (by simp))
  intro u hu u' hu' h
  rw [← sub_eq_zero]
  have h' := Prod.mk.inj (hprod ▸ h)
  simp only [ContinuousLinearMap.coe_coe] at h'
  simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hu hu'
  refine eq_zero_of_mfderiv_familyCorrespondence_eq_zero hS hsurj ?_ ?_ ?_
  · rw [map_sub, hu, hu', sub_zero]
  · rw [map_sub, h'.1, sub_self]
  · rw [map_sub, h'.2, sub_self]

end Differential

/-! ### The Lagrangian correspondence on the fibre-critical set -/

section CriticalSet

variable [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ M] [IsManifold J ∞ N]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ A]
  (hS : ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S)
  (hreg : IsRegularValue ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ, A →L[ℝ] ℝ) (familyFiberDeriv S) 0)

omit [TopologicalSpace H] [TopologicalSpace H'] in
/-- The fibre-critical set has half the dimension of `T*M × T*N`. -/
private theorem two_mul_finrank_eq_finrank_cotangent :
    2 * finrank ℝ (Fin (finrank ℝ (E × F)) → ℝ) =
      finrank ℝ ((E × (E →L[ℝ] ℝ)) × (F × (F →L[ℝ] ℝ))) := by
  simp only [finrank_fin_fun, finrank_prod, ContinuousLinearMap.dual_finrank_eq]
  ring

/-- **The family relation is exact on the fibre-critical set.** Along the fibre-critical set of a
smooth transverse family, the family relation pulls the primitive `pr₁^*λ_M - pr₂^*λ_N` of the
twisted product back to the differential of the restriction of `S`. -/
theorem mpullback_familyCorrespondence_comp_coe_liouvilleForm :
    letI := familyCriticalSetChartedSpace hS hreg
    mpullback (F := ℝ) (k := 1) 𝓘(ℝ, Fin (finrank ℝ (E × F)) → ℝ)
        ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
        (familyCorrespondence I J S ∘ Subtype.val)
        (SmoothForm.mpullback (Prod.fst : CotangentBundle I M × CotangentBundle J N → _)
            (contMDiff_fst (I := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J := J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
            (liouvilleForm I M) -
          SmoothForm.mpullback (Prod.snd : CotangentBundle I M × CotangentBundle J N → _)
            (contMDiff_snd (I := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J := J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
            (liouvilleForm J N)).val =
      mextDeriv (RoughForm.ofFunction 𝓘(ℝ, Fin (finrank ℝ (E × F)) → ℝ)
        (S ∘ (Subtype.val : {z : (M × N) × A // familyFiberDeriv S z = 0} → (M × N) × A))) := by
  let := familyCriticalSetChartedSpace hS hreg
  have := isManifold_familyCriticalSet hS hreg
  have hcoe := (isSmoothEmbedding_coe_familyCriticalSet hS hreg).contMDiff.mdifferentiable
    (by simp)
  rw [mpullback_comp hcoe ((contMDiff_familyCorrespondence hS).mdifferentiable (by simp))]
  funext z
  ext v
  rw [TauCeti.mpullback_apply, mpullback_familyCorrespondence_liouvilleForm_apply hS, z.property,
    mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    mvfderiv_comp_apply z ((hS z).mdifferentiableAt (by simp)) (hcoe z)]
  simp only [mvfderiv_apply_eq_mfderiv_apply]
  -- The fibre derivative vanishes at `z`, so its value on `(dz v).2` is `0`.
  exact sub_zero _

/-- **The differential of the family relation is injective on the fibre-critical set.** -/
theorem injective_mfderiv_familyCorrespondence_comp_coe
    (z : {z : (M × N) × A // familyFiberDeriv S z = 0}) :
    letI := familyCriticalSetChartedSpace hS hreg
    Injective (mfderiv 𝓘(ℝ, Fin (finrank ℝ (E × F)) → ℝ)
      ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
      (familyCorrespondence I J S ∘ Subtype.val) z) := by
  let := familyCriticalSetChartedSpace hS hreg
  have hemb := isSmoothEmbedding_coe_familyCriticalSet hS hreg
  have hcoe := (hemb.isImmersion.contMDiff z).mdifferentiableAt (by simp)
  have hG := (contMDiff_familyCorrespondence hS z.val).mdifferentiableAt (by simp)
  -- The inclusion is injective with tangent image the kernel of `d(∂_a S)`, on which the
  -- differential of the family relation is injective.
  have hmem (v) : mfderiv 𝓘(ℝ, Fin (finrank ℝ (E × F)) → ℝ) ((I.prod J).prod 𝓘(ℝ, A))
      Subtype.val z v ∈
      (mfderiv ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ, A →L[ℝ] ℝ) (familyFiberDeriv S) z).ker := by
    rw [← range_mfderiv_coe_familyCriticalSet hS hreg z]
    exact ⟨v, rfl⟩
  intro v w hvw
  rw [mfderiv_comp_apply z hG hcoe, mfderiv_comp_apply z hG hcoe] at hvw
  exact hemb.isImmersion.mfderiv_injective (by simp) z
    (injOn_mfderiv_familyCorrespondence_ker hS
      (isRegularPoint_iff.mp (hreg.isRegularPoint z.property)) (hmem v) (hmem w) hvw)

/-- **A transverse generating family defines an exact Lagrangian map.** On finite-dimensional
boundaryless manifolds `M` and `N`, the family relation `((q, Q), a) ↦ ((q, d_q S), (Q, -d_Q S))`
of a smooth transverse family `S` on `(M × N) × A`, restricted to its fibre-critical set, is an
exact Lagrangian map into `T*M × T*N` for the twisted product `pr₁^*ω_M - pr₂^*ω_N` and its
primitive `pr₁^*λ_M - pr₂^*λ_N`, with primitive the restriction of `S`. -/
theorem isExactLagrangianMap_familyCorrespondence_comp_coe :
    letI := familyCriticalSetChartedSpace hS hreg
    ((isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate.twistedProd
        (isSymplectic_symplecticForm (I := J) (M := N)).isNondegenerate).IsExactLagrangianMap
      𝓘(ℝ, Fin (finrank ℝ (E × F)) → ℝ)
      (SmoothForm.mpullback (Prod.fst : CotangentBundle I M × CotangentBundle J N → _)
          (contMDiff_fst (I := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J := J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
          (liouvilleForm I M) -
        SmoothForm.mpullback (Prod.snd : CotangentBundle I M × CotangentBundle J N → _)
          (contMDiff_snd (I := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J := J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
          (liouvilleForm J N))
      (familyCorrespondence I J S ∘ Subtype.val)
      (S ∘ (Subtype.val : {z : (M × N) × A // familyFiberDeriv S z = 0} → (M × N) × A)) := by
  let := familyCriticalSetChartedSpace hS hreg
  have := isManifold_familyCriticalSet hS hreg
  have hcoe := (isSmoothEmbedding_coe_familyCriticalSet hS hreg).isImmersion.contMDiff
  refine (SmoothTwoForm.IsNondegenerate.isExactLagrangianMap_iff_of_finrank
    (twistedProd_symplecticForm I M J N) ((contMDiff_familyCorrespondence hS).comp hcoe)
    (injective_mfderiv_familyCorrespondence_comp_coe hS hreg)
    two_mul_finrank_eq_finrank_cotangent).mpr
      ⟨hS.comp hcoe, mpullback_familyCorrespondence_comp_coe_liouvilleForm hS hreg⟩

/-- **A transverse generating family defines a Lagrangian immersion.** On finite-dimensional
boundaryless manifolds `M` and `N`, the family relation `((q, Q), a) ↦ ((q, d_q S), (Q, -d_Q S))`
of a smooth transverse family `S` on `(M × N) × A`, restricted to its fibre-critical set, is a
Lagrangian immersion into `T*M × T*N` for the twisted product `pr₁^*ω_M - pr₂^*ω_N`: an immersed
Lagrangian correspondence `T*M ⇝ T*N`. -/
theorem isLagrangianImmersion_familyCorrespondence_comp_coe :
    letI := familyCriticalSetChartedSpace hS hreg
    ((isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate.twistedProd
        (isSymplectic_symplecticForm (I := J) (M := N)).isNondegenerate).IsLagrangianImmersion
      𝓘(ℝ, Fin (finrank ℝ (E × F)) → ℝ) (familyCorrespondence I J S ∘
        (Subtype.val : {z : (M × N) × A // familyFiberDeriv S z = 0} → (M × N) × A)) := by
  let := familyCriticalSetChartedSpace hS hreg
  have := isManifold_familyCriticalSet hS hreg
  have hL := isExactLagrangianMap_familyCorrespondence_comp_coe hS hreg
  refine ⟨((contMDiff_familyCorrespondence hS).comp
      (isSmoothEmbedding_coe_familyCriticalSet hS hreg).isImmersion.contMDiff
      ).isImmersion_of_injective_mfderiv (by simp)
      (injective_mfderiv_familyCorrespondence_comp_coe hS hreg),
    hL.isLagrangianMap.isIsotropicMap, two_mul_finrank_eq_finrank_cotangent⟩

end CriticalSet

end TauCeti.CotangentBundle
