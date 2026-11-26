/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Rescale
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Isometry

/-!
# Exponential transport for `WithMetric`

The tautological map `ofWithMetric : WithMetric g → M` identifies `expDomain` and `riemannianExp`
on `WithMetric g` with those on `M` whenever `M` carries `g`, both in `[RiemannianBundle]` form
(`TauCeti.WithMetric.mem_expDomain_iff_mfderiv_ofWithMetric`,
`TauCeti.WithMetric.ofWithMetric_riemannianExp`) and in
`letI` form at `toWithMetric g p` (`TauCeti.WithMetric.mem_expDomain_toWithMetric_iff`,
`TauCeti.WithMetric.ofWithMetric_riemannianExp_toWithMetric`). It also intertwines `expDomain` and
`riemannianExp` along `diffeomorphWithMetric` under constant metric rescaling `g ↦ c g`
(`TauCeti.WithMetric.mfderiv_diffeomorphWithMetric_rescale_const_mem_expDomain`,
`TauCeti.WithMetric.riemannianExp_mfderiv_diffeomorphWithMetric_rescale_const`).
-/

public section

open Bundle Manifold TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.WithMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

section RiemannianBundle

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  (hg : ∀ x (v w : TangentSpace I x), inner ℝ v w = g.inner x v w)
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

include hg

/-- Membership in `expDomain` on `WithMetric g` reduces to `M` when `M` carries `g`. -/
theorem mem_expDomain_iff_mfderiv_ofWithMetric {x : WithMetric g} {v : TangentSpace I x} :
    v ∈ expDomain I (WithMetric g) x ↔
      mfderiv I I ofWithMetric x v ∈ expDomain I M x.ofWithMetric := by
  have h := (riemannianIsometryOfInner g hg).mfderiv_mem_expDomain_iff (p := x) (v := v)
  rw [coe_riemannianIsometryOfInner] at h; exact h.symm

/-- `ofWithMetric` intertwines `riemannianExp` on `WithMetric g` with `riemannianExp` on `M` when
`M` carries `g`. -/
theorem ofWithMetric_riemannianExp [I.Boundaryless] [T2Space M]
    (x : WithMetric g) (v : TangentSpace I x) :
    (riemannianExp I (WithMetric g) x v).ofWithMetric =
      riemannianExp I M x.ofWithMetric (mfderiv I I ofWithMetric x v) := by
  have h := (riemannianIsometryOfInner g hg).riemannianExp_mfderiv x v
  rw [coe_riemannianIsometryOfInner] at h; exact h.symm

end RiemannianBundle

/-- `letI` version of `mem_expDomain_iff_mfderiv_ofWithMetric` at `toWithMetric g p`. -/
theorem mem_expDomain_toWithMetric_iff (p : M) (v : TangentSpace I (toWithMetric g p)) :
    v ∈ expDomain I (WithMetric g) (toWithMetric g p) ↔
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        letI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
          Bundle.instIsContMDiffRiemannianBundle g;
        mfderiv I I ofWithMetric (toWithMetric g p) v ∈ expDomain I M p) := by
  let _ : RiemannianBundle _ := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I ∞ E _ := Bundle.instIsContMDiffRiemannianBundle g
  simpa only [ofWithMetric_toWithMetric] using
    mem_expDomain_iff_mfderiv_ofWithMetric g g.inner_riemannianBundle (x := toWithMetric g p)
      (v := v)

/-- `letI` version of `ofWithMetric_riemannianExp` at `toWithMetric g p`. -/
theorem ofWithMetric_riemannianExp_toWithMetric [I.Boundaryless] [T2Space M]
    (p : M) (v : TangentSpace I (toWithMetric g p)) :
    (riemannianExp I (WithMetric g) (toWithMetric g p) v).ofWithMetric =
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        letI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
          Bundle.instIsContMDiffRiemannianBundle g;
        riemannianExp I M p (mfderiv I I ofWithMetric (toWithMetric g p) v)) := by
  let _ : RiemannianBundle _ := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I ∞ E _ := Bundle.instIsContMDiffRiemannianBundle g
  simpa only [ofWithMetric_toWithMetric] using
    ofWithMetric_riemannianExp g g.inner_riemannianBundle (toWithMetric g p) v

/-- Exponential-domain transport under `diffeomorphWithMetric` for constant metric rescaling. -/
theorem mfderiv_diffeomorphWithMetric_rescale_const_mem_expDomain
    {c : ℝ} (hc : 0 < c) {x : WithMetric g} {v : TangentSpace I x}
    (hv : v ∈ expDomain I (WithMetric g) x) :
    (diffeomorphWithMetric g (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc)
        ∞).mfderivToContinuousLinearEquiv (by simp) x v ∈
      expDomain I (WithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc))
        (diffeomorphWithMetric g (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc) ∞ x) := by
  set g_c := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  have hmem :
      (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g_c.toRiemannianMetric⟩;
        mfderiv I I ofWithMetric x v ∈ expDomain I M x.ofWithMetric) := by
    rw [g.expDomain_rescale_const hc x.ofWithMetric]
    let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) :=
      Bundle.instIsContMDiffRiemannianBundle g
    rw [← mem_expDomain_iff_mfderiv_ofWithMetric g g.inner_riemannianBundle]
    exact hv
  let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g_c.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) :=
    Bundle.instIsContMDiffRiemannianBundle g_c
  rw [mem_expDomain_iff_mfderiv_ofWithMetric g_c g_c.inner_riemannianBundle]
  exact (congr_mfderiv_ofWithMetric_diffeomorphWithMetric g_c ∞ (by simp)
    (fun b u ↦ u ∈ expDomain I M b) x v).mpr hmem

/-- Exponential equivariance under `diffeomorphWithMetric` for constant metric rescaling. -/
theorem riemannianExp_mfderiv_diffeomorphWithMetric_rescale_const [I.Boundaryless] [T2Space M]
    {c : ℝ} (hc : 0 < c) (x : WithMetric g) (v : TangentSpace I x) :
    riemannianExp I (WithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc))
        (diffeomorphWithMetric g (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc) ∞ x)
        ((diffeomorphWithMetric g (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc)
          ∞).mfderivToContinuousLinearEquiv (by simp) x v) =
      diffeomorphWithMetric g (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc) ∞
        (riemannianExp I (WithMetric g) x v) := by
  set g_c := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  set Φ := diffeomorphWithMetric g g_c ∞
  refine ofWithMetric_injective ?_
  have hexp_c :
      (riemannianExp I (WithMetric g_c) (Φ x)
          (Φ.mfderivToContinuousLinearEquiv (by simp) x v)).ofWithMetric =
        (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g_c.toRiemannianMetric⟩;
          riemannianExp I M (Φ x).ofWithMetric
            (mfderiv I I ofWithMetric (Φ x)
              (Φ.mfderivToContinuousLinearEquiv (by simp) x v))) :=
    let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g_c.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) :=
      Bundle.instIsContMDiffRiemannianBundle g_c
    ofWithMetric_riemannianExp g_c g_c.inner_riemannianBundle (Φ x) _
  have hexp_eq :
      (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g_c.toRiemannianMetric⟩;
        riemannianExp I M (Φ x).ofWithMetric
          (mfderiv I I ofWithMetric (Φ x)
            (Φ.mfderivToContinuousLinearEquiv (by simp) x v))) =
      (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
        riemannianExp I M x.ofWithMetric (mfderiv I I ofWithMetric x v)) := by
    trans (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g_c.toRiemannianMetric⟩;
        riemannianExp I M x.ofWithMetric (mfderiv I I ofWithMetric x v))
    · let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g_c.toRiemannianMetric⟩
      exact congr_mfderiv_ofWithMetric_diffeomorphWithMetric g_c ∞ (by simp)
        (fun b u ↦ riemannianExp I M b u) x v
    · exact g.riemannianExp_rescale_const hc x.ofWithMetric (mfderiv I I ofWithMetric x v)
  have hexp_g :
      (riemannianExp I (WithMetric g) x v).ofWithMetric =
        (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
          riemannianExp I M x.ofWithMetric (mfderiv I I ofWithMetric x v)) :=
    let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) :=
      Bundle.instIsContMDiffRiemannianBundle g
    ofWithMetric_riemannianExp g g.inner_riemannianBundle x v
  rw [hexp_c, hexp_eq, ← hexp_g]
  simp [Φ]

end TauCeti.WithMetric

end
