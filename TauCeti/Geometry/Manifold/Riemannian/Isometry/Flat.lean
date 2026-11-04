/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Restriction
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.VectorSpace
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Flat.TorsionFree
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Flat Riemannian metrics and local Euclidean isometries

A classical theorem of Riemann characterizes flat Riemannian metrics locally: the Riemann curvature
tensor of a smooth Riemannian manifold `M` without boundary vanishes on an open set `U` if and only
if every point `x₀ ∈ U` admits an open neighbourhood `U₀ ⊆ U` that is smoothly Riemannian isometric
to an open neighbourhood `V₀` of `0` in Euclidean space of the same dimension, sending `x₀` to `0`.

Both directions combine previously developed pieces:

* **Local Euclidean isometry implies flat curvature** (valid also on manifolds with boundary or
  corners): a local Riemannian isometry has invertible differentials everywhere and intertwines the
  curvature tensor (`TauCeti.IsLocalRiemannianIsometry.mfderiv_curvatureTensor`), so it preserves
  and reflects vanishing of `curvatureTensor`
  (`TauCeti.IsLocalRiemannianIsometry.curvatureTensor_eq_zero_iff`). Applied to the
  open-submanifold inclusions `U₀ → M` and `V₀ → F` together with a Riemannian isometry `U₀ ≃ V₀`
  and flatness of the Euclidean model space
  (`TauCeti.Manifold.curvatureTensor_leviCivitaConnection_model_space`), this forces the curvature
  tensor of `M` to vanish on `U₀`.
* **Flat curvature implies a local Euclidean isometry** (on boundaryless manifolds): if the
  curvature tensor of `leviCivitaConnection I M` vanishes near `x₀`, metric-compatibility produces a
  smooth local orthonormal parallel frame `{s i}` near `x₀`
  (`CovariantDerivative.IsMetricCompatible.exists_orthonormal_isLocalFrameOn_parallel`). Because the
  Levi-Civita connection is torsion-free (`torsion_leviCivitaConnection_eq_zero`), the dual coframe
  sending `s i` to an orthonormal basis `{bF i}` of the model inner-product space `F` integrates via
  the Poincaré lemma to a smooth map `f : M → F` with `f x₀ = 0` and `df_y (s i y) = bF i` near `x₀`
  (`CovariantDerivative.exists_contMDiff_mfderiv_parallel_frame_eq`). Orthonormality of `{s i y}`
  and `{bF i}` implies that `df_y` preserves inner products near `x₀` and is a linear equivalence at
  `x₀`; the manifold inverse function theorem (`TauCeti.isLocalDiffeomorphAt_of_mfderiv_eq`) then
  restricts `f` to a smooth `RiemannianIsometry` between open neighbourhoods of `x₀` and `0`.
  Boundarylessness is genuinely required for this direction: an open subset `V₀` of `F` has only
  interior points, so no boundary or corner point of `M` can admit a diffeomorphism onto `V₀`.

We record the characterization both for ambient `[RiemannianBundle]` instances (pointwise germ, open
subset, and global forms, for any model inner-product space `F` of equal dimension as well as
`EuclideanSpace ℝ (Fin (Module.finrank ℝ E))`) and for bundled smooth metrics
`Bundle.ContMDiffRiemannianMetric`.

## Main results

* `TauCeti.isLocalRiemannianIsometry_subtype_val`: the inclusion `Subtype.val : U → M` of an open
  submanifold carrying the restricted Riemannian metric is a local Riemannian isometry.
* `TauCeti.IsLocalRiemannianIsometry.curvatureTensor_eq_zero_iff`: a local Riemannian isometry
  reflects and preserves pointwise vanishing of the Riemann curvature tensor.
* `TauCeti.curvatureTensor_open_eq_zero_iff`: the curvature tensor of an open submanifold vanishes
  at `x` iff the ambient curvature tensor vanishes at `x`.
* `TauCeti.curvatureTensor_eq_zero_of_riemannianIsometry_open`: an open submanifold isometric to an
  open subset of a real inner-product space has vanishing ambient curvature tensor.
* `TauCeti.exists_riemannianIsometry_open_of_eventually_curvatureTensor_eq_zero`: flat curvature
  near `x₀` produces a pointed `RiemannianIsometry` from an open neighbourhood `U₀ ⊆ U` of `x₀` to
  an open neighbourhood `V₀` of `0` in any real inner-product space `F` of equal dimension.
* `TauCeti.eventually_curvatureTensor_eq_zero_iff_exists_riemannianIsometry_open` and
  `TauCeti.eventually_curvatureTensor_eq_zero_iff_exists_riemannianIsometry_euclideanSpace`: germ
  equivalence between flat curvature near `x₀` and existence of a local Euclidean isometry.
* `TauCeti.forall_mem_curvatureTensor_eq_zero_iff_forall_exists_riemannianIsometry_open` and
  `TauCeti.forall_mem_curvatureTensor_eq_zero_iff_forall_exists_riemannianIsometry_euclideanSpace`:
  flat curvature on an open set `U` is equivalent to a local Euclidean isometry around every point
  of `U`.
* `TauCeti.forall_curvatureTensor_eq_zero_iff_forall_exists_riemannianIsometry_euclideanSpace`:
  global flatness on `M` is equivalent to local Euclidean isometries around every point.
* `Bundle.ContMDiffRiemannianMetric.eventually_curvatureTensor_leviCivitaConnection_eq_zero_iff` and
  `Bundle.ContMDiffRiemannianMetric.forall_mem_curvatureTensor_leviCivitaConnection_eq_zero_iff`:
  the corresponding characterizations for a bundled smooth Riemannian metric `g`.

## References

* B. Riemann, *Über die Hypothesen, welche der Geometrie zu Grunde liegen* (1854), Abh. Königl.
  Ges. Wiss. Göttingen 13 (1868), 133–152.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Theorem 7.10.
* M. Spivak, *A Comprehensive Introduction to Differential Geometry*, Vol. II, 3rd ed., Publish or
  Perish (1999), Chapter 4D, Theorem 13.
-/

public section

noncomputable section

open Bundle CovariantDerivative Filter Manifold Module Set TopologicalSpace
open scoped ContDiff Manifold Topology TauCeti

namespace TauCeti

/-- For an open submanifold `U : Opens M` carrying the restricted ambient Riemannian metric
(`Manifold.instRiemannianBundleOpen`), the inclusion `Subtype.val : U → M` is a local Riemannian
isometry. -/
theorem isLocalRiemannianIsometry_subtype_val
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] (U : Opens M) :
    IsLocalRiemannianIsometry I I (Subtype.val : U → M) where
  contMDiff := contMDiff_subtype_val
  isInvertible_mfderiv x :=
    ⟨Manifold.tangentSpaceOpenEquiv (I := I) x, (Manifold.mfderiv_subtype_val x).symm⟩
  inner_mfderiv x v w := by
    rw [Manifold.inner_tangentSpace_open U x v w, Manifold.mfderiv_subtype_val]
    rfl

section WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- A local Riemannian isometry preserves and reflects vanishing of the Riemann curvature tensor at
each point, because its differential is invertible and intertwines `curvatureTensor`. -/
theorem IsLocalRiemannianIsometry.curvatureTensor_eq_zero_iff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N] [IsManifold J ∞ N]
    [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
    [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
    {f : M → N} (hf : IsLocalRiemannianIsometry I J f) (x : M) :
    (leviCivitaConnection I M).curvatureTensor x = 0 ↔
      (leviCivitaConnection J N).curvatureTensor (f x) = 0 := by
  obtain ⟨φ, hφ⟩ := hf.isInvertible_mfderiv x
  constructor
  · intro h0
    ext u' v' w'
    have hu : mfderiv I J f x (φ.symm u') = u' := by rw [← hφ]; exact φ.apply_symm_apply u'
    have hv : mfderiv I J f x (φ.symm v') = v' := by rw [← hφ]; exact φ.apply_symm_apply v'
    have hw : mfderiv I J f x (φ.symm w') = w' := by rw [← hφ]; exact φ.apply_symm_apply w'
    rw [← hu, ← hv, ← hw, ← hf.mfderiv_curvatureTensor, h0]
    simp
  · intro h0
    ext u v w
    apply φ.injective
    have happly (z : TangentSpace I x) : φ z = mfderiv I J f x z := DFunLike.congr_fun hφ z
    rw [happly, hf.mfderiv_curvatureTensor, h0]
    simp

/-- On an open submanifold `U : Opens M` carrying the restricted Riemannian metric, the curvature
tensor vanishes at `x : U` if and only if the ambient curvature tensor vanishes at `(x : M)`. -/
@[simp]
theorem curvatureTensor_open_eq_zero_iff (U : Opens M) (x : U) :
    (leviCivitaConnection I U).curvatureTensor x = 0 ↔
      (leviCivitaConnection I M).curvatureTensor (x : M) = 0 :=
  (isLocalRiemannianIsometry_subtype_val (I := I) U).curvatureTensor_eq_zero_iff x

/-- If an open submanifold `U₀ : Opens M` admits a local Riemannian isometry into an open subset
`V₀ : Opens F` of a finite-dimensional real inner-product space `F`, then the ambient curvature
tensor of `M` vanishes at every point of `U₀`. -/
theorem curvatureTensor_eq_zero_of_isLocalRiemannianIsometry_open
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {U₀ : Opens M} {V₀ : Opens F} {f : U₀ → V₀}
    (hf : IsLocalRiemannianIsometry I 𝓘(ℝ, F) f) {x : M} (hx : x ∈ U₀) :
    (leviCivitaConnection I M).curvatureTensor x = 0 := by
  rw [← curvatureTensor_open_eq_zero_iff U₀ ⟨x, hx⟩,
    hf.curvatureTensor_eq_zero_iff ⟨x, hx⟩,
    curvatureTensor_open_eq_zero_iff V₀ (f ⟨x, hx⟩)]
  exact Manifold.curvatureTensor_leviCivitaConnection_model_space (f ⟨x, hx⟩ : F)

/-- If an open submanifold `U₀ : Opens M` is Riemannian isometric to an open subset `V₀ : Opens F`
of a finite-dimensional real inner-product space `F`, then the ambient curvature tensor of `M`
vanishes on `U₀`. -/
theorem curvatureTensor_eq_zero_of_riemannianIsometry_open
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {U₀ : Opens M} {V₀ : Opens F} (Φ : RiemannianIsometry I 𝓘(ℝ, F) U₀ V₀)
    {x : M} (hx : x ∈ U₀) :
    (leviCivitaConnection I M).curvatureTensor x = 0 :=
  curvatureTensor_eq_zero_of_isLocalRiemannianIsometry_open Φ.isLocalRiemannianIsometry hx

end WithBoundary

section Boundaryless

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **Flat curvature near a point produces a local Euclidean isometry.** On a boundaryless smooth
Riemannian manifold `M`, if `(leviCivitaConnection I M).curvatureTensor` vanishes near `x₀` and
`F` is any finite-dimensional real inner-product space of the same dimension as `E`, then inside any
neighbourhood `U ∈ 𝓝 x₀` there is an open neighbourhood `U₀ : Opens M` of `x₀`, an open
neighbourhood `V₀ : Opens F` of `0`, and a smooth `RiemannianIsometry` `Φ : U₀ → V₀` sending `x₀`
to `0`. -/
theorem exists_riemannianIsometry_open_of_eventually_curvatureTensor_eq_zero
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (hdim : finrank ℝ E = finrank ℝ F) {x₀ : M} {U : Set M} (hU : U ∈ 𝓝 x₀)
    (hflat : ∀ᶠ y in 𝓝 x₀, (leviCivitaConnection I M).curvatureTensor y = 0) :
    ∃ (U₀ : Opens M) (V₀ : Opens F) (hx₀ : x₀ ∈ U₀) (_ : (0 : F) ∈ V₀)
      (Φ : RiemannianIsometry I 𝓘(ℝ, F) U₀ V₀),
      (U₀ : Set M) ⊆ U ∧ (Φ ⟨x₀, hx₀⟩ : F) = 0 := by
  classical
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  let eT := trivializationAt E (TangentSpace I) x₀
  have hx₀T : x₀ ∈ eT.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hdim_x₀ : finrank ℝ (TangentSpace I x₀) = finrank ℝ F :=
    (eT.linearEquivAt ℝ x₀ hx₀T).finrank_eq.trans hdim
  let bF : OrthonormalBasis (Fin (finrank ℝ F)) ℝ F := stdOrthonormalBasis ℝ F
  let b₀ : OrthonormalBasis (Fin (finrank ℝ F)) ℝ (TangentSpace I x₀) :=
    (stdOrthonormalBasis ℝ (TangentSpace I x₀)).reindex (finCongr hdim_x₀)
  -- Step 1: extend `b₀` to a smooth local orthonormal parallel frame `{s i}` around `x₀`.
  obtain ⟨W, s, hW, hx₀W, -, hs, -, horth, hpar⟩ :=
    (isMetricCompatible_leviCivitaConnection I).exists_orthonormal_isLocalFrameOn_parallel b₀ hflat
  -- Step 2: integrate the dual coframe sending `s i` to `bF i` using torsion-freeness and Poincaré.
  have htors : ∀ y ∈ W, (leviCivitaConnection I M).torsion y = 0 := fun y _ ↦ by
    simp [torsion_leviCivitaConnection_eq_zero]
  obtain ⟨U_f, hU_f, f, hf_smooth, hf₀, hdf⟩ :=
    (leviCivitaConnection I M).exists_contMDiff_mfderiv_parallel_frame_eq
      hW hx₀W hs hpar htors (fun i ↦ bF i)
  let W₁ : Set M := (W ∩ interior U_f) ∩ interior U
  have hW₁ : IsOpen W₁ := (hW.inter isOpen_interior).inter isOpen_interior
  have hx₀W₁ : x₀ ∈ W₁ :=
    ⟨⟨hx₀W, mem_interior_iff_mem_nhds.mpr hU_f⟩, mem_interior_iff_mem_nhds.mpr hU⟩
  -- Step 3: on `W₁`, `mfderiv f y` maps an orthonormal basis `{s i y}` to `{bF i}`, so it preserves
  -- inner products everywhere on `W₁` and is a continuous linear equivalence at `x₀`.
  have hinner_f {y : M} (hy : y ∈ W₁) (v w : TangentSpace I y) :
      inner ℝ (mfderiv I 𝓘(ℝ, F) f y v) (mfderiv I 𝓘(ℝ, F) f y w) = inner ℝ v w := by
    have hyW : y ∈ W := hy.1.1
    have hyUf : y ∈ U_f := interior_subset hy.1.2
    let b_y : Basis (Fin (finrank ℝ F)) ℝ (TangentSpace I y) := hs.toBasisAt hyW
    conv_lhs => rw [← b_y.sum_repr v, ← b_y.sum_repr w]
    conv_rhs => rw [← b_y.sum_repr v, ← b_y.sum_repr w]
    simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    have hsi : b_y i = s i y := hs.toBasisAt_coe hyW i
    have hsj : b_y j = s j y := hs.toBasisAt_coe hyW j
    rw [hsi, hsj]
    have hFji : inner ℝ (mfderiv I 𝓘(ℝ, F) f y (s j y)) (mfderiv I 𝓘(ℝ, F) f y (s i y)) =
        if j = i then (1 : ℝ) else 0 := by
      rw [hdf y hyUf j, hdf y hyUf i]
      exact orthonormal_iff_ite.mp bF.orthonormal j i
    rw [hFji, orthonormal_iff_ite.mp (horth y hyW) j i]
  let b_target : Basis (Fin (finrank ℝ F)) ℝ (TangentSpace 𝓘(ℝ, F) (f x₀)) := bF.toBasis
  let e₀ : TangentSpace I x₀ ≃L[ℝ] TangentSpace 𝓘(ℝ, F) (f x₀) :=
    ((hs.toBasisAt hx₀W).equiv b_target (Equiv.refl _)).toContinuousLinearEquiv
  have he₀ : (e₀ : TangentSpace I x₀ →L[ℝ] TangentSpace 𝓘(ℝ, F) (f x₀)) =
      mfderiv I 𝓘(ℝ, F) f x₀ := by
    refine ContinuousLinearMap.coe_injective ((hs.toBasisAt hx₀W).ext fun i ↦ ?_)
    have hx₀Uf : x₀ ∈ U_f := interior_subset hx₀W₁.1.2
    have h1 : e₀ (hs.toBasisAt hx₀W i) = b_target i := by
      dsimp only [e₀]
      rw [LinearEquiv.coe_toContinuousLinearEquiv', Basis.equiv_apply, Equiv.refl_apply]
    have h2 : mfderiv I 𝓘(ℝ, F) f x₀ (hs.toBasisAt hx₀W i) = b_target i := by
      rw [hs.toBasisAt_coe hx₀W i]
      exact hdf x₀ hx₀Uf i
    exact h1.trans h2.symm
  -- Step 4: apply the manifold inverse function theorem at `x₀` and restrict to `W₁`.
  have hf_ld : IsLocalDiffeomorphAt I 𝓘(ℝ, F) ∞ f x₀ :=
    isLocalDiffeomorphAt_of_mfderiv_eq hf_smooth.contMDiffOn hW₁ hx₀W₁
      (BoundarylessManifold.isInteriorPoint (x := x₀)) (by simp) he₀
  let Ψ : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞ := hf_ld.localInverse.symm.restrOpen W₁ hW₁
  have hΨ_src : Ψ.source = hf_ld.localInverse.target ∩ W₁ :=
    hf_ld.localInverse.symm.restrOpen_source hW₁
  have hΨ_eq {y : M} (hy : y ∈ Ψ.source) : Ψ y = f y := by
    have hy_tgt : y ∈ hf_ld.localInverse.target := (hΨ_src ▸ hy).1
    have hsymm_src : hf_ld.localInverse.symm y ∈ hf_ld.localInverse.source :=
      hf_ld.localInverse.symm.map_source hy_tgt
    have h1 := hf_ld.localInverse_right_inv hsymm_src
    have h2 : hf_ld.localInverse (hf_ld.localInverse.symm y) = y :=
      hf_ld.localInverse.toPartialEquiv.right_inv hy_tgt
    rw [h2] at h1
    rw [hf_ld.localInverse.symm.coe_restrOpen hW₁]
    exact h1.symm
  let U₀ : Opens M := ⟨Ψ.source, Ψ.open_source⟩
  let V₀ : Opens F := ⟨Ψ.target, Ψ.open_target⟩
  have hx₀U₀ : x₀ ∈ U₀ := by
    -- Membership in `U₀ = ⟨Ψ.source, _⟩` is membership in `Ψ.source`.
    change x₀ ∈ Ψ.source
    rw [hΨ_src]
    exact ⟨hf_ld.localInverse_mem_target, hx₀W₁⟩
  have hΨx₀ : Ψ x₀ = 0 := (hΨ_eq hx₀U₀).trans hf₀
  have h0V₀ : (0 : F) ∈ V₀ := hΨx₀ ▸ Ψ.map_source hx₀U₀
  let Φ_equiv : U₀ ≃ V₀ :=
    { toFun := fun y ↦ ⟨Ψ y.1, Ψ.map_source y.2⟩
      invFun := fun z ↦ ⟨Ψ.symm z.1, Ψ.map_target z.2⟩
      left_inv := fun y ↦ Subtype.ext (Ψ.left_inv y.2)
      right_inv := fun z ↦ Subtype.ext (Ψ.right_inv z.2) }
  have hΦ_val : (Subtype.val : V₀ → F) ∘ Φ_equiv = f ∘ (Subtype.val : U₀ → M) := by
    funext y
    exact hΨ_eq y.2
  have hΦ_smooth : ContMDiff I 𝓘(ℝ, F) ∞ Φ_equiv := by
    refine (ContMDiff.subtypeVal_comp_iff V₀ Φ_equiv).mp ?_
    rw [hΦ_val]
    exact hf_smooth.comp contMDiff_subtype_val
  have hΦ_symm_smooth : ContMDiff 𝓘(ℝ, F) I ∞ Φ_equiv.symm := by
    refine (ContMDiff.subtypeVal_comp_iff U₀ Φ_equiv.symm).mp ?_
    exact Ψ.contMDiffOn_invFun.comp_contMDiff contMDiff_subtype_val fun z ↦ z.2
  let Φ_diffeo : Diffeomorph I 𝓘(ℝ, F) U₀ V₀ ∞ :=
    { toEquiv := Φ_equiv
      contMDiff_toFun := hΦ_smooth
      contMDiff_invFun := hΦ_symm_smooth }
  refine ⟨U₀, V₀, hx₀U₀, h0V₀,
    { toDiffeomorph := Φ_diffeo
      inner_mfderiv' := fun y v w ↦ ?_ },
    fun y hy ↦ interior_subset ((hΨ_src ▸ hy : y ∈ hf_ld.localInverse.target ∩ W₁).2.2), hΨx₀⟩
  -- Differentiate `Subtype.val ∘ Φ_diffeo = f ∘ Subtype.val` and use isometricity of open
  -- submanifold inclusions on both sides.
  have happly (u : TangentSpace I y) :
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (Subtype.val : V₀ → F) (Φ_diffeo y)
        (mfderiv I 𝓘(ℝ, F) Φ_diffeo y u) : F) =
        mfderiv I 𝓘(ℝ, F) f y.1 (mfderiv I I (Subtype.val : U₀ → M) y u) := by
    rw [← mfderiv_comp_apply y
        ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) (Φ_diffeo y))
        (hΦ_smooth.mdifferentiable (by simp) y),
      ← mfderiv_comp_apply y (hf_smooth.mdifferentiable (by simp) y.1)
        ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) y)]
    exact congrArg (fun g : U₀ → F ↦ (mfderiv I 𝓘(ℝ, F) g y u : F)) hΦ_val
  have hyW₁ : y.1 ∈ W₁ := (hΨ_src ▸ y.2 : y.1 ∈ hf_ld.localInverse.target ∩ W₁).2
  rw [← (isLocalRiemannianIsometry_subtype_val (I := 𝓘(ℝ, F)) V₀).inner_mfderiv (Φ_diffeo y),
    ← (isLocalRiemannianIsometry_subtype_val (I := I) U₀).inner_mfderiv y, ← hinner_f hyW₁]
  -- On `TangentSpace 𝓘(ℝ, F) _`, the Riemannian inner product is the inner product of `F`.
  change Inner.inner ℝ
    (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (Subtype.val : V₀ → F) (Φ_diffeo y)
      (mfderiv I 𝓘(ℝ, F) Φ_diffeo y v) : F)
    (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (Subtype.val : V₀ → F) (Φ_diffeo y)
      (mfderiv I 𝓘(ℝ, F) Φ_diffeo y w) : F) =
    Inner.inner ℝ (mfderiv I 𝓘(ℝ, F) f y.1 (mfderiv I I (Subtype.val : U₀ → M) y v) : F)
      (mfderiv I 𝓘(ℝ, F) f y.1 (mfderiv I I (Subtype.val : U₀ → M) y w) : F)
  rw [happly v, happly w]
  rfl

/-- **Pointwise germ characterization of flat Riemannian metrics (general inner-product model).**
On a boundaryless smooth Riemannian manifold `M`, for any finite-dimensional real inner-product
space `F` with `finrank ℝ E = finrank ℝ F`, the curvature tensor vanishes near `x₀` if and only if
`x₀` has an open neighbourhood `U₀ : Opens M` Riemannian isometric to an open subset `V₀ : Opens F`
(and in fact sending `x₀` to `0`). -/
theorem eventually_curvatureTensor_eq_zero_iff_exists_riemannianIsometry_open
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (hdim : finrank ℝ E = finrank ℝ F) (x₀ : M) :
    (∀ᶠ y in 𝓝 x₀, (leviCivitaConnection I M).curvatureTensor y = 0) ↔
      ∃ (U₀ : Opens M) (V₀ : Opens F) (hx₀ : x₀ ∈ U₀) (_ : (0 : F) ∈ V₀)
        (Φ : RiemannianIsometry I 𝓘(ℝ, F) U₀ V₀), (Φ ⟨x₀, hx₀⟩ : F) = 0 := by
  constructor
  · intro hflat
    obtain ⟨U₀, V₀, hx₀, h0, Φ, -, hΦ₀⟩ :=
      exists_riemannianIsometry_open_of_eventually_curvatureTensor_eq_zero hdim univ_mem hflat
    exact ⟨U₀, V₀, hx₀, h0, Φ, hΦ₀⟩
  · rintro ⟨U₀, V₀, hx₀, -, Φ, -⟩
    filter_upwards [U₀.isOpen.mem_nhds hx₀] with y hy
    exact curvatureTensor_eq_zero_of_riemannianIsometry_open Φ hy

/-- **Pointwise germ characterization of flat Riemannian metrics (`EuclideanSpace` model).** On a
boundaryless smooth Riemannian manifold `M`, the curvature tensor vanishes near `x₀` if and only if
`x₀` has an open neighbourhood `U₀ : Opens M` Riemannian isometric to an open neighbourhood
`V₀ : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))` of `0` sending `x₀` to `0`. -/
theorem eventually_curvatureTensor_eq_zero_iff_exists_riemannianIsometry_euclideanSpace
    (x₀ : M) :
    (∀ᶠ y in 𝓝 x₀, (leviCivitaConnection I M).curvatureTensor y = 0) ↔
      ∃ (U₀ : Opens M) (V₀ : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E))))
        (hx₀ : x₀ ∈ U₀) (_ : (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) ∈ V₀)
        (Φ : RiemannianIsometry I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E))) U₀ V₀),
        (Φ ⟨x₀, hx₀⟩ : EuclideanSpace ℝ (Fin (finrank ℝ E))) = 0 :=
  eventually_curvatureTensor_eq_zero_iff_exists_riemannianIsometry_open
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := finrank ℝ E)).symm x₀

/-- **Flat curvature on an open set vs. local isometries to an inner-product space.** On a
boundaryless smooth Riemannian manifold `M` and an open set `U ⊆ M`, for any finite-dimensional real
inner-product space `F` with `finrank ℝ E = finrank ℝ F`, the curvature tensor vanishes at every
point of `U` if and only if around every `x ∈ U` there exist an open neighbourhood `U₀ : Opens M`
contained in `U`, an open neighbourhood `V₀ : Opens F` of `0`, and a smooth `RiemannianIsometry`
`Φ : U₀ → V₀` sending `x` to `0`. -/
theorem forall_mem_curvatureTensor_eq_zero_iff_forall_exists_riemannianIsometry_open
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (hdim : finrank ℝ E = finrank ℝ F) {U : Set M} (hU : IsOpen U) :
    (∀ x ∈ U, (leviCivitaConnection I M).curvatureTensor x = 0) ↔
      ∀ x ∈ U, ∃ (U₀ : Opens M) (V₀ : Opens F) (hx : x ∈ U₀) (_ : (0 : F) ∈ V₀)
        (Φ : RiemannianIsometry I 𝓘(ℝ, F) U₀ V₀),
        (U₀ : Set M) ⊆ U ∧ (Φ ⟨x, hx⟩ : F) = 0 := by
  constructor
  · intro hflat x hx
    exact exists_riemannianIsometry_open_of_eventually_curvatureTensor_eq_zero hdim
      (hU.mem_nhds hx) (eventually_of_mem (hU.mem_nhds hx) hflat)
  · intro hiso x hx
    obtain ⟨U₀, V₀, hxU₀, -, Φ, -, -⟩ := hiso x hx
    exact curvatureTensor_eq_zero_of_riemannianIsometry_open Φ hxU₀

/-- **Riemann's theorem on flat Riemannian metrics on an open set.** On a boundaryless smooth
Riemannian manifold `M`, the Riemann curvature tensor vanishes on an open set `U ⊆ M` if and only if
every point `x ∈ U` admits an open neighbourhood `U₀ ⊆ U` smoothly Riemannian isometric to an open
neighbourhood `V₀` of `0` in `EuclideanSpace ℝ (Fin (finrank ℝ E))`, sending `x` to `0`. -/
theorem forall_mem_curvatureTensor_eq_zero_iff_forall_exists_riemannianIsometry_euclideanSpace
    {U : Set M} (hU : IsOpen U) :
    (∀ x ∈ U, (leviCivitaConnection I M).curvatureTensor x = 0) ↔
      ∀ x ∈ U, ∃ (U₀ : Opens M) (V₀ : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E))))
        (hx : x ∈ U₀) (_ : (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) ∈ V₀)
        (Φ : RiemannianIsometry I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E))) U₀ V₀),
        (U₀ : Set M) ⊆ U ∧
          (Φ ⟨x, hx⟩ : EuclideanSpace ℝ (Fin (finrank ℝ E))) = 0 :=
  forall_mem_curvatureTensor_eq_zero_iff_forall_exists_riemannianIsometry_open
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := finrank ℝ E)).symm hU

/-- **Riemann's theorem on flat Riemannian manifolds.** A boundaryless smooth Riemannian manifold
`M` has everywhere vanishing Riemann curvature tensor if and only if every point `x : M` admits an
open neighbourhood smoothly Riemannian isometric to an open neighbourhood of `0` in
`EuclideanSpace ℝ (Fin (finrank ℝ E))`, sending `x` to `0`. -/
theorem forall_curvatureTensor_eq_zero_iff_forall_exists_riemannianIsometry_euclideanSpace :
    (∀ x : M, (leviCivitaConnection I M).curvatureTensor x = 0) ↔
      ∀ x : M, ∃ (U₀ : Opens M) (V₀ : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E))))
        (hx : x ∈ U₀) (_ : (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) ∈ V₀)
        (Φ : RiemannianIsometry I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E))) U₀ V₀),
        (Φ ⟨x, hx⟩ : EuclideanSpace ℝ (Fin (finrank ℝ E))) = 0 := by
  simpa using
    forall_mem_curvatureTensor_eq_zero_iff_forall_exists_riemannianIsometry_euclideanSpace
      (I := I) (M := M) isOpen_univ

end Boundaryless

end TauCeti

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
/-- The inner product installed on `U₀ : Opens M` by `g.restrictOpenTangentSpace U₀` agrees with
the scoped `Manifold.instRiemannianBundleOpen U₀` inner product induced by installing `g` on `M`. -/
private theorem inner_restrictOpenTangentSpace_eq_open
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (U₀ : Opens M)
    (x : U₀) (v w : TangentSpace I x) :
    (letI : RiemannianBundle (fun y : U₀ ↦ TangentSpace I y) :=
        ⟨(g.restrictOpenTangentSpace U₀).toRiemannianMetric⟩;
      Inner.inner ℝ v w) =
    (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      Inner.inner ℝ v w) := by
  let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  rw [TauCeti.Manifold.inner_tangentSpace_open U₀ x v w,
    inner_riemannianBundle (g.restrictOpenTangentSpace U₀),
    g.restrictOpenTangentSpace_inner U₀ x v w]
  rfl

/-- **Germ flatness of a bundled smooth metric vs. local Euclidean isometries.** For a smooth
Riemannian metric `g` on a boundaryless manifold `M`, the Levi-Civita curvature tensor of `g`
vanishes near `x₀` if and only if `x₀` admits an open neighbourhood `U₀ : Opens M` on which the
restricted metric `g.restrictOpenTangentSpace U₀` is smoothly Riemannian isometric to an open
neighbourhood `V₀` of `0` in `EuclideanSpace ℝ (Fin (finrank ℝ E))`, sending `x₀` to `0`. -/
theorem eventually_curvatureTensor_leviCivitaConnection_eq_zero_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (x₀ : M) :
    (∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩;
      (leviCivitaConnection I M).curvatureTensor y) = 0) ↔
      ∃ (U₀ : Opens M) (V₀ : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E))))
        (hx₀ : x₀ ∈ U₀) (_ : (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) ∈ V₀),
        letI : RiemannianBundle (fun x : U₀ ↦ TangentSpace I x) :=
          ⟨(g.restrictOpenTangentSpace U₀).toRiemannianMetric⟩
        ∃ Φ : TauCeti.RiemannianIsometry I
            𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E))) U₀ V₀,
          (Φ ⟨x₀, hx₀⟩ : EuclideanSpace ℝ (Fin (finrank ℝ E))) = 0 := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [TauCeti.eventually_curvatureTensor_eq_zero_iff_exists_riemannianIsometry_euclideanSpace x₀]
  refine exists_congr fun U₀ ↦ exists_congr fun V₀ ↦ exists_congr fun hx₀ ↦
    exists_congr fun _ ↦ ⟨fun ⟨Φ, hΦ⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [← TauCeti.RiemannianIsometry.coe_toDiffeomorph] at hΦ
    cases Φ with | mk d hd =>
    let _ : RiemannianBundle (fun x : U₀ ↦ TangentSpace I x) :=
      ⟨(g.restrictOpenTangentSpace U₀).toRiemannianMetric⟩
    refine ⟨{ toDiffeomorph := d, inner_mfderiv' := fun x v w ↦ ?_ }, ?_⟩
    · rw [inner_restrictOpenTangentSpace_eq_open g U₀ x v w]
      exact hd x v w
    · rw [← TauCeti.RiemannianIsometry.coe_toDiffeomorph]
      exact hΦ
  · obtain ⟨d, hd, hΦ⟩ : ∃ d : Diffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E))) U₀ V₀ ∞,
        (∀ x (v w : TangentSpace I x),
          Inner.inner ℝ (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E))) d x v)
            (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E))) d x w) =
            Inner.inner ℝ v w) ∧
          (d ⟨x₀, hx₀⟩ : EuclideanSpace ℝ (Fin (finrank ℝ E))) = 0 := by
      let _ : RiemannianBundle (fun x : U₀ ↦ TangentSpace I x) :=
        ⟨(g.restrictOpenTangentSpace U₀).toRiemannianMetric⟩
      obtain ⟨Φ, hΦ⟩ := h
      rw [← TauCeti.RiemannianIsometry.coe_toDiffeomorph] at hΦ
      cases Φ with | mk d hd =>
      refine ⟨d, fun x v w ↦ ?_, hΦ⟩
      rw [← inner_restrictOpenTangentSpace_eq_open g U₀ x v w]
      exact hd x v w
    refine ⟨{ toDiffeomorph := d, inner_mfderiv' := hd }, ?_⟩
    rw [← TauCeti.RiemannianIsometry.coe_toDiffeomorph]
    exact hΦ

/-- **Open-set flatness of a bundled smooth metric vs. local Euclidean isometries.** For a smooth
Riemannian metric `g` on a boundaryless manifold `M` and an open set `U ⊆ M`, the Levi-Civita
curvature tensor of `g` vanishes on `U` if and only if around every `x ∈ U` there is an open
neighbourhood `U₀ : Opens M` with `(U₀ : Set M) ⊆ U` on which `g.restrictOpenTangentSpace U₀` is
smoothly Riemannian isometric to an open neighbourhood `V₀` of `0` in
`EuclideanSpace ℝ (Fin (finrank ℝ E))`, sending `x` to `0`. -/
theorem forall_mem_curvatureTensor_leviCivitaConnection_eq_zero_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {U : Set M} (hU : IsOpen U) :
    (∀ x ∈ U, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩;
      (leviCivitaConnection I M).curvatureTensor x) = 0) ↔
      ∀ x ∈ U, ∃ (U₀ : Opens M) (V₀ : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E))))
        (hx : x ∈ U₀) (_ : (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) ∈ V₀),
        letI : RiemannianBundle (fun x : U₀ ↦ TangentSpace I x) :=
          ⟨(g.restrictOpenTangentSpace U₀).toRiemannianMetric⟩
        ∃ Φ : TauCeti.RiemannianIsometry I
            𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E))) U₀ V₀,
          (U₀ : Set M) ⊆ U ∧
            (Φ ⟨x, hx⟩ : EuclideanSpace ℝ (Fin (finrank ℝ E))) = 0 := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [TauCeti.forall_mem_curvatureTensor_eq_zero_iff_forall_exists_riemannianIsometry_euclideanSpace
    hU]
  refine forall₂_congr fun x _ ↦ exists_congr fun U₀ ↦ exists_congr fun V₀ ↦
    exists_congr fun hx ↦ exists_congr fun _ ↦ ⟨fun ⟨Φ, hsub, hΦ⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [← TauCeti.RiemannianIsometry.coe_toDiffeomorph] at hΦ
    cases Φ with | mk d hd =>
    let _ : RiemannianBundle (fun y : U₀ ↦ TangentSpace I y) :=
      ⟨(g.restrictOpenTangentSpace U₀).toRiemannianMetric⟩
    refine ⟨{ toDiffeomorph := d, inner_mfderiv' := fun y v w ↦ ?_ }, hsub, ?_⟩
    · rw [inner_restrictOpenTangentSpace_eq_open g U₀ y v w]
      exact hd y v w
    · rw [← TauCeti.RiemannianIsometry.coe_toDiffeomorph]
      exact hΦ
  · obtain ⟨d, hd, hsub, hΦ⟩ :
        ∃ d : Diffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E))) U₀ V₀ ∞,
          (∀ y (v w : TangentSpace I y),
            Inner.inner ℝ (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E))) d y v)
              (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E))) d y w) =
              Inner.inner ℝ v w) ∧
            (U₀ : Set M) ⊆ U ∧
            (d ⟨x, hx⟩ : EuclideanSpace ℝ (Fin (finrank ℝ E))) = 0 := by
      let _ : RiemannianBundle (fun y : U₀ ↦ TangentSpace I y) :=
        ⟨(g.restrictOpenTangentSpace U₀).toRiemannianMetric⟩
      obtain ⟨Φ, hsub, hΦ⟩ := h
      rw [← TauCeti.RiemannianIsometry.coe_toDiffeomorph] at hΦ
      cases Φ with | mk d hd =>
      refine ⟨d, fun y v w ↦ ?_, hsub, hΦ⟩
      rw [← inner_restrictOpenTangentSpace_eq_open g U₀ y v w]
      exact hd y v w
    refine ⟨{ toDiffeomorph := d, inner_mfderiv' := hd }, hsub, ?_⟩
    rw [← TauCeti.RiemannianIsometry.coe_toDiffeomorph]
    exact hΦ

end Bundle.ContMDiffRiemannianMetric

end
