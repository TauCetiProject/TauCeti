/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Isometry

/-!
# Exponential transport for `WithMetric`

The tautological map `ofWithMetric : WithMetric g → M` identifies `expDomain` and `riemannianExp`
on `WithMetric g` with those on `M` whenever `M` carries `g`, both in `[RiemannianBundle]` form
(`TauCeti.WithMetric.mem_expDomain_iff`, `TauCeti.WithMetric.ofWithMetric_riemannianExp`) and in
`letI` form at `toWithMetric g p` (`TauCeti.WithMetric.mem_expDomain_toWithMetric_iff`,
`TauCeti.WithMetric.ofWithMetric_riemannianExp_toWithMetric`).
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
theorem mem_expDomain_iff {x : WithMetric g} {v : TangentSpace I x} :
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

/-- `letI` version of `mem_expDomain_iff` at `toWithMetric g p`. -/
theorem mem_expDomain_toWithMetric_iff (p : M) (v : TangentSpace I (toWithMetric g p)) :
    v ∈ expDomain I (WithMetric g) (toWithMetric g p) ↔
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        letI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
          Bundle.instIsContMDiffRiemannianBundle g;
        mfderiv I I ofWithMetric (toWithMetric g p) v ∈ expDomain I M p) :=
  let _ : RiemannianBundle _ := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I ∞ E _ := Bundle.instIsContMDiffRiemannianBundle g
  mem_expDomain_iff g g.inner_riemannianBundle

/-- `letI` version of `ofWithMetric_riemannianExp` at `toWithMetric g p`. -/
theorem ofWithMetric_riemannianExp_toWithMetric [I.Boundaryless] [T2Space M]
    (p : M) (v : TangentSpace I (toWithMetric g p)) :
    (riemannianExp I (WithMetric g) (toWithMetric g p) v).ofWithMetric =
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        letI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
          Bundle.instIsContMDiffRiemannianBundle g;
        riemannianExp I M p (mfderiv I I ofWithMetric (toWithMetric g p) v)) :=
  let _ : RiemannianBundle _ := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I ∞ E _ := Bundle.instIsContMDiffRiemannianBundle g
  ofWithMetric_riemannianExp g g.inner_riemannianBundle (toWithMetric g p) v

end TauCeti.WithMetric

end
