/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.DefiningFunction.Basic
public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Outward
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic

/-!
# Regular sublevels as Riemannian manifolds with boundary

Let `(N, g)` be a boundaryless smooth manifold modelled on a real space `E` of dimension `n + 1`,
with a smooth Riemannian metric, and let `a` be a regular value of a smooth function `f : N → ℝ`.
The sublevel `D = {f ≤ a}` is a smooth manifold with boundary for Tau Ceti's atlas
`TauCeti.scalarRegularSublevelChartedSpace`, and its inclusion `j : D → N` is smooth with
invertible differential at every point, boundary points included. This file equips `D` with the
metric `g_D = j^* g` pulled back along `j` (`TauCeti.scalarRegularSublevelMetric`) and proves:

* `j` is a local Riemannian isometry `(D, g_D) → (N, g)`
  (`TauCeti.isLocalRiemannianIsometry_subtypeVal_scalarRegularSublevel`); Tau Ceti's naturality
  theorems for local isometries, which assume no boundaryless source, then apply to `j`;
* `dj` carries gradients of restrictions to gradients: `dj(grad^D (u ∘ j)) = grad^N u` for every
  `u : N → ℝ` differentiable at the point
  (`TauCeti.mfderiv_mgradient_comp_subtypeVal_scalarRegularSublevel`);
* at a point of the level `f⁻¹(a)`, a tangent vector `v` of `D` points outward exactly when
  `df(dj v) > 0` (`TauCeti.isOutwardPointing_scalarRegularSublevel_iff_mfderiv`): the outward
  vectors of a sublevel are those on which its function increases, read in `N`;
* `a - f` is a global boundary defining function of `D`
  (`TauCeti.isBoundaryDefiningFunctionOn_scalarRegularSublevel`), so the formulas of
  RiemannianManifoldsWithConvexBoundary §§1.3-1.4 for the inward unit normal and the second
  fundamental form apply to it.

These cover the first two items of RiemannianManifoldsWithConvexBoundary §3.1 for the regular domain
`D_ρ = {ρ ≥ 0}`, which is the sublevel `{-ρ ≤ 0}`, the defining-function part of its third item,
and the outward criterion of RiemannianGeometry R7.9 for regular sublevels.
-/

public section

open Bundle Module Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {n : ℕ} {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace N]
  [ChartedSpace H N] [IsManifold I ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace I y)]
  [IsContMDiffRiemannianBundle I ∞ E (fun y : N ↦ TangentSpace I y)]
  {f : N → ℝ} {a : ℝ}

private theorem contMDiff_succ_of_contMDiff_infty {E' H' M' F' H'' N' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'}
    [TopologicalSpace M'] [ChartedSpace H' M'] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [TopologicalSpace H''] {J' : ModelWithCorners ℝ F' H''} [TopologicalSpace N']
    [ChartedSpace H'' N'] {φ : M' → N'} (hφ : ContMDiff I' J' ∞ φ) : ContMDiff I' J' (∞ + 1) φ := by
  simpa using hφ

variable (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hreg : IsRegularValue I 𝓘(ℝ) f a)
  (hn : finrank ℝ E = n + 1)

/-- The **metric of a regular sublevel**: the pullback `j^* g` of the metric of `N` along the
inclusion `j` of the sublevel `{f ≤ a}` at a regular value `a` of a smooth function `f`, for the
atlas `TauCeti.scalarRegularSublevelChartedSpace`. It is a smooth Riemannian metric because `j` is
smooth with invertible differential at every point, boundary points included. -/
def scalarRegularSublevelMetric :
    letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
    haveI := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
    ContMDiffRiemannianMetric (𝓡∂ (n + 1)) ∞ (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : {x | f x ≤ a} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
  letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
  haveI := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
  (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := I) (n := ∞) (F := E)
    (V := fun y : N ↦ TangentSpace I y)).pullback Subtype.val
    (contMDiff_succ_of_contMDiff_infty
      (contMDiff_subtypeVal_scalarRegularSublevel hreg hn ENat.LEInfty.out hf))
    fun x ↦ (isInvertible_mfderiv_subtypeVal_scalarRegularSublevel
      (hf.of_le ENat.LEInfty.out) hreg hn x).injective

/-- The metric of a regular sublevel is the metric of `N` applied to the differentials of the
inclusion. -/
theorem scalarRegularSublevelMetric_inner (x : {x | f x ≤ a})
    (v w : letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
      TangentSpace (𝓡∂ (n + 1)) x) :
    letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
    haveI := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
    (scalarRegularSublevelMetric hf hreg hn).inner x v w =
      inner ℝ (mfderiv (𝓡∂ (n + 1)) I (Subtype.val : {x | f x ≤ a} → N) x v)
        (mfderiv (𝓡∂ (n + 1)) I (Subtype.val : {x | f x ≤ a} → N) x w) :=
  letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
  haveI := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
  ContMDiffRiemannianMetric.pullback_ofIsContMDiffRiemannianBundle_inner _ _ _ x v w

/-- **The inclusion of a regular sublevel is a local Riemannian isometry** for the pulled-back
metric `TauCeti.scalarRegularSublevelMetric`: it is smooth, its differential is invertible at
every point, boundary points included, and it preserves inner products. -/
theorem isLocalRiemannianIsometry_subtypeVal_scalarRegularSublevel :
    letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
    haveI := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
    letI : RiemannianBundle (fun x : {x | f x ≤ a} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
      ⟨(scalarRegularSublevelMetric hf hreg hn).toRiemannianMetric⟩
    IsLocalRiemannianIsometry (𝓡∂ (n + 1)) I (Subtype.val : {x | f x ≤ a} → N) :=
  letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
  haveI := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
  letI : RiemannianBundle (fun x : {x | f x ≤ a} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨(scalarRegularSublevelMetric hf hreg hn).toRiemannianMetric⟩
  { contMDiff := contMDiff_subtypeVal_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
    isInvertible_mfderiv :=
      isInvertible_mfderiv_subtypeVal_scalarRegularSublevel (hf.of_le ENat.LEInfty.out) hreg hn
    inner_mfderiv x v w := (scalarRegularSublevelMetric_inner hf hreg hn x v w).symm }

/-- **Gradients of restrictions to a regular sublevel.** For `u : N → ℝ` differentiable at a point
`j x` of the regular sublevel `D = {f ≤ a}`, with the pulled-back metric on `D`, the differential
of the inclusion `j` carries the gradient of `u ∘ j` at `x` to the gradient of `u` at `j x`,
boundary points included. -/
theorem mfderiv_mgradient_comp_subtypeVal_scalarRegularSublevel {u : N → ℝ} (x : {x | f x ≤ a})
    (hu : MDifferentiableAt I 𝓘(ℝ) u x) :
    letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
    haveI := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
    letI : RiemannianBundle (fun x : {x | f x ≤ a} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
      ⟨(scalarRegularSublevelMetric hf hreg hn).toRiemannianMetric⟩
    mfderiv (𝓡∂ (n + 1)) I (Subtype.val : {x | f x ≤ a} → N) x
        (Manifold.mgradient (𝓡∂ (n + 1)) (u ∘ Subtype.val) x) =
      Manifold.mgradient I u x :=
  letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
  haveI := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
  letI : RiemannianBundle (fun x : {x | f x ≤ a} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨(scalarRegularSublevelMetric hf hreg hn).toRiemannianMetric⟩
  (isLocalRiemannianIsometry_subtypeVal_scalarRegularSublevel hf hreg hn).mfderiv_mgradient_comp hu

omit [RiemannianBundle (fun y : N ↦ TangentSpace I y)]
  [IsContMDiffRiemannianBundle I ∞ E (fun y : N ↦ TangentSpace I y)] in
/-- **The outward criterion for a regular sublevel, read in `N`.** At a point `x` of the level
`f⁻¹(a)`, a tangent vector `v` of the sublevel `{f ≤ a}` points outward exactly when
`df(dj v) > 0`, where `j` is the inclusion. -/
theorem isOutwardPointing_scalarRegularSublevel_iff_mfderiv {x : {x | f x ≤ a}} (hx : f x = a)
    (v : letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
      TangentSpace (𝓡∂ (n + 1)) x) :
    letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
    IsOutwardPointing x v ↔
      0 < mvfderiv I f x (mfderiv (𝓡∂ (n + 1)) I (Subtype.val : {x | f x ≤ a} → N) x v) := by
  let := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
  have := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
  rw [isOutwardPointing_scalarRegularSublevel_iff (hf.of_le ENat.LEInfty.out) hn hreg hx v]
  exact iff_of_eq (congrArg _ (mvfderiv_comp_apply (g := f) (f := Subtype.val) x
    (hf.mdifferentiableAt (by simp))
    ((contMDiff_subtypeVal_scalarRegularSublevel hreg hn ENat.LEInfty.out hf).mdifferentiableAt
      (by simp)) v))

omit [RiemannianBundle (fun y : N ↦ TangentSpace I y)]
  [IsContMDiffRiemannianBundle I ∞ E (fun y : N ↦ TangentSpace I y)] in
/-- **The function of a regular sublevel is a global boundary defining function.** On the regular
sublevel `{f ≤ a}`, the function `a - f` is smooth, positive on the interior `{f < a}`, zero on the
boundary `f⁻¹(a)` and has nonzero differential there. -/
theorem isBoundaryDefiningFunctionOn_scalarRegularSublevel :
    letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
    IsBoundaryDefiningFunctionOn n (fun x : {x | f x ≤ a} ↦ a - f x) univ := by
  let := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
  have := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
  have hj := contMDiff_subtypeVal_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
  have hfj : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ (f ∘ Subtype.val : {x | f x ≤ a} → ℝ) := hf.comp hj
  refine ⟨isOpen_univ, (contMDiff_const.sub hfj).contMDiffOn, fun x _ hx ↦ ?_, fun x _ hx ↦ ?_,
    fun x _ hx h0 ↦ ?_⟩
  · rw [interior_scalarRegularSublevel hreg hn ENat.LEInfty.out hf] at hx
    exact sub_pos.2 hx
  · rw [boundary_scalarRegularSublevel hreg hn ENat.LEInfty.out hf] at hx
    exact sub_eq_zero.2 hx.symm
  · rw [boundary_scalarRegularSublevel hreg hn ENat.LEInfty.out hf] at hx
    have hjx : MDifferentiableAt (𝓡∂ (n + 1)) I (Subtype.val : {x | f x ≤ a} → N) x :=
      hj.mdifferentiableAt (by simp)
    -- `d(a - f ∘ j) = -df ∘ dj`, so it vanishes only if `df` vanishes on the range of `dj`,
    -- which is everything; but `df ≠ 0` at the regular point `x`.
    obtain ⟨w, hw⟩ := isRegularPoint_iff.1 (isRegularValue_iff.1 hreg (x : N) hx) (1 : ℝ)
    obtain ⟨v, rfl⟩ := (isInvertible_mfderiv_subtypeVal_scalarRegularSublevel
      (hf.of_le ENat.LEInfty.out) hreg hn x).surjective w
    have h1 : mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ) ((fun _ : {x | f x ≤ a} ↦ a) - f ∘ Subtype.val) x v =
        0 :=
      congrArg (fun L : TangentSpace (𝓡∂ (n + 1)) x →L[ℝ] ℝ ↦ L v) h0
    rw [mfderiv_sub mdifferentiableAt_const (hfj.mdifferentiableAt (by simp)), mfderiv_const,
      mfderiv_comp x (hf.mdifferentiableAt (by simp)) hjx] at h1
    have h2 : mfderiv I 𝓘(ℝ) f x
        (mfderiv (𝓡∂ (n + 1)) I (Subtype.val : {x | f x ≤ a} → N) x v) = 0 := by
      change ((0 : TangentSpace (𝓡∂ (n + 1)) x →L[ℝ] ℝ) -
        show TangentSpace (𝓡∂ (n + 1)) x →L[ℝ] ℝ from (mfderiv I 𝓘(ℝ) f x).comp
          (mfderiv (𝓡∂ (n + 1)) I (Subtype.val : {x | f x ≤ a} → N) x)) v = 0 at h1
      rw [sub_apply, zero_apply, zero_sub, neg_eq_zero] at h1
      exact h1
    have h3 : (1 : ℝ) = 0 := hw.symm.trans h2
    exact one_ne_zero h3

end TauCeti
