/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Maximal
public import Mathlib.Analysis.Convex.Star

/-!
# The Riemannian exponential map

This file defines the natural domain of the Riemannian exponential map at a point and the map
itself. A tangent vector belongs to the domain precisely when its geodesic exists at time `1`.
The value of the exponential is independent of the local geodesic witness used to compute it.

Rescaling the initial velocity identifies membership in the exponential domain with membership of
the corresponding time in the maximal geodesic interval. Consequently the domain is star-convex
at the zero vector, and evaluating the exponential on a scaled velocity evaluates any geodesic
with the original initial data at the scaling parameter.

The exponential is totalized by the base point outside its natural domain. Every theorem using
its geometric value therefore carries a domain hypothesis. Openness and smoothness of the domain
and map require smooth dependence of the geodesic flow on its initial data and are developed
separately.

## Main definitions and results

* `TauCeti.Manifold.expDomain` is the set of tangent vectors whose geodesics exist at time `1`.
* `TauCeti.Manifold.riemannianExp` evaluates such a geodesic at time `1`.
* `TauCeti.Manifold.smul_mem_expDomain_iff` relates the domain to maximal existence times.
* `TauCeti.Manifold.starConvex_expDomain` proves radial closure of the natural domain.
* `TauCeti.Manifold.riemannianExp_smul_eq` evaluates a scaled initial velocity along a geodesic.
* `TauCeti.Manifold.expDomain_eq_univ_iff_isGeodesicallyCompleteAt` identifies an everywhere
  defined exponential with pointwise geodesic completeness.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2018, Ch. 5.
-/

-- Roadmap: HopfRinow

public section

open Bundle Function Manifold Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

variable (I M) in
/-- The natural domain of the Riemannian exponential at `p`: the initial velocities whose maximal
geodesic interval contains time `1`. -/
def expDomain (p : M) : Set (TangentSpace I p) :=
  {v | (1 : ℝ) ∈ geodesicInterval I M p v}

omit [I.Boundaryless] in
/-- Membership in the exponential domain means existence of the corresponding geodesic at time
`1`. -/
@[simp] theorem mem_expDomain {p : M} {v : TangentSpace I p} :
    v ∈ expDomain I M p ↔ (1 : ℝ) ∈ geodesicInterval I M p v :=
  Iff.rfl

omit [I.Boundaryless] in
/-- The zero tangent vector belongs to the exponential domain. -/
theorem zero_mem_expDomain {p : M} :
    (0 : TangentSpace I p) ∈ expDomain I M p := by
  simp

private structure GeodesicWitnessAt (p : M) (v : TangentSpace I p) (t : ℝ) where
  curve : ℝ → M
  left : ℝ
  right : ℝ
  isGeodesicCurveOnFrom : IsGeodesicCurveOnFrom I curve (Ioo left right) p v
  time_mem : t ∈ Ioo left right

omit [I.Boundaryless] in
private theorem nonempty_geodesicWitnessAt {p : M} {v : TangentSpace I p} {t : ℝ}
    (ht : t ∈ geodesicInterval I M p v) :
    Nonempty (GeodesicWitnessAt (I := I) (M := M) p v t) := by
  obtain ⟨γ, a, b, hγ, ht⟩ := mem_geodesicInterval_iff.mp ht
  exact ⟨⟨γ, a, b, hγ, ht⟩⟩

private noncomputable def geodesicValue {p : M} (v : TangentSpace I p) (t : ℝ)
    (ht : t ∈ geodesicInterval I M p v) : M :=
  (Classical.choice (nonempty_geodesicWitnessAt (I := I) (M := M) ht)).curve t

private theorem geodesicValue_eq [T2Space (TangentBundle I M)] {p : M}
    {v : TangentSpace I p} {t a b : ℝ} (ht : t ∈ geodesicInterval I M p v)
    {γ : ℝ → M} (hγ : IsGeodesicCurveOnFrom I γ (Ioo a b) p v)
    (htγ : t ∈ Ioo a b) : geodesicValue (I := I) (M := M) v t ht = γ t := by
  let w := Classical.choice (nonempty_geodesicWitnessAt (I := I) (M := M) ht)
  have hw : IsGeodesicCurveOnFrom I w.curve (Ioo w.left w.right) p v :=
    w.isGeodesicCurveOnFrom
  have ht_inter : t ∈ Ioo (max w.left a) (min w.right b) :=
    ⟨max_lt w.time_mem.1 htγ.1, lt_min w.time_mem.2 htγ.2⟩
  exact hw.eqOn_of_inter hγ ht_inter

variable (I M) in
/-- The Riemannian exponential at `p`, evaluated at time `1` along the geodesic with initial
velocity `v`. Outside its natural domain the function is totalized by the value `p`. -/
noncomputable def riemannianExp (p : M) (v : TangentSpace I p) : M :=
  by
    classical
    exact if hv : v ∈ expDomain I M p then
      geodesicValue (I := I) (M := M) v 1 (mem_expDomain.mp hv)
    else p

omit [I.Boundaryless] in
/-- Outside its natural domain the totalized Riemannian exponential is the base point. -/
theorem riemannianExp_of_not_mem {p : M} {v : TangentSpace I p}
    (hv : v ∉ expDomain I M p) : riemannianExp I M p v = p := by
  simp [riemannianExp, hv]

/-- Any geodesic witness defined at time `1` computes the Riemannian exponential. -/
theorem riemannianExp_eq [T2Space (TangentBundle I M)] {p : M} {v : TangentSpace I p}
    {γ : ℝ → M} {a b : ℝ} (hγ : IsGeodesicCurveOnFrom I γ (Ioo a b) p v)
    (h1 : (1 : ℝ) ∈ Ioo a b) : riemannianExp I M p v = γ 1 := by
  have hv : v ∈ expDomain I M p := hγ.subset_geodesicInterval h1
  simp only [riemannianExp, hv, dite_true]
  exact geodesicValue_eq (mem_expDomain.mp hv) hγ h1

/-- The Riemannian exponential sends the zero tangent vector to its base point. -/
@[simp] theorem riemannianExp_zero [T2Space (TangentBundle I M)] {p : M} :
    riemannianExp I M p (0 : TangentSpace I p) = p := by
  let γ : ℝ → M := fun _ ↦ p
  have hγ : IsGeodesicCurveOnFrom I γ (Ioo (-2) 2) p (0 : TangentSpace I p) := by
    refine ⟨isGeodesicCurveOn_const (uniqueDiffOn_Ioo (-2) 2) p, by norm_num, ?_⟩
    simp [γ, curveVelocityWithin_const]
  simpa [γ] using riemannianExp_eq (I := I) (M := M) hγ (by norm_num)

/-- Scaling an initial velocity into the exponential domain is equivalent to the original
geodesic existing at the corresponding time. This includes the zero-scaling case. -/
theorem smul_mem_expDomain_iff {p : M} {v : TangentSpace I p} {t : ℝ} :
    t • v ∈ expDomain I M p ↔ t ∈ geodesicInterval I M p v := by
  by_cases ht : t = 0
  · subst t
    simp
  · simpa using (mem_geodesicInterval_smul_iff (I := I) (M := M) (v := v) (a := t)
      (t := (1 : ℝ)) ht)

/-- The exponential domain is star-convex at the zero tangent vector. -/
theorem starConvex_expDomain {p : M} :
    StarConvex ℝ (0 : TangentSpace I p) (expDomain I M p) := by
  rw [starConvex_zero_iff]
  intro v hv t ht0 ht1
  rw [smul_mem_expDomain_iff]
  exact ordConnected_geodesicInterval.uIcc_subset zero_mem_geodesicInterval
    (mem_expDomain.mp hv) (by simpa [uIcc_of_le ht0] using ⟨ht0, ht1⟩)

/-- Evaluating the Riemannian exponential on a scaled initial velocity evaluates the original
geodesic at the scaling parameter. Both sides carry the necessary domain hypotheses explicitly. -/
theorem riemannianExp_smul_eq [T2Space (TangentBundle I M)] {p : M}
    {v : TangentSpace I p} {γ : ℝ → M} {a b t : ℝ}
    (hγ : IsGeodesicCurveOnFrom I γ (Ioo a b) p v) (ht : t ∈ Ioo a b) :
    riemannianExp I M p (t • v) = γ t := by
  by_cases ht0 : t = 0
  · subst t
    simpa using (riemannianExp_zero (I := I) (M := M)).trans hγ.base_eq.symm
  · obtain ⟨a', b', h1, hγ'⟩ := hγ.exists_comp_mul_left_Ioo_one_mem ht0 ht
    simpa [Function.comp_apply] using riemannianExp_eq (I := I) (M := M) hγ' h1

variable (I M) in
/-- Pointwise geodesic completeness at `p`: every geodesic starting at `p` exists for all real
parameters. -/
def IsGeodesicallyCompleteAt (p : M) : Prop :=
  ∀ v : TangentSpace I p, geodesicInterval I M p v = univ

variable (I M) in
/-- Geodesic completeness: every geodesic initial condition has an all-time maximal interval. -/
def IsGeodesicallyComplete : Prop :=
  ∀ p : M, IsGeodesicallyCompleteAt I M p

/-- The exponential at a point is defined on its whole tangent space exactly when every geodesic
from that point exists for all time. -/
theorem expDomain_eq_univ_iff_isGeodesicallyCompleteAt {p : M} :
    expDomain I M p = univ ↔ IsGeodesicallyCompleteAt I M p := by
  constructor
  · intro h v
    apply eq_univ_of_forall
    intro t
    apply smul_mem_expDomain_iff.mp
    rw [h]
    exact mem_univ (t • v)
  · intro h
    apply eq_univ_of_forall
    intro v
    rw [mem_expDomain, h v]
    exact mem_univ 1

/-- A Riemannian manifold is geodesically complete exactly when the exponential domain at every
point is the whole tangent space. -/
theorem isGeodesicallyComplete_iff_expDomain_eq_univ :
    IsGeodesicallyComplete I M ↔ ∀ p : M, expDomain I M p = univ := by
  simp only [IsGeodesicallyComplete, expDomain_eq_univ_iff_isGeodesicallyCompleteAt]

end TauCeti.Manifold

end
