/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Trajectory

/-!
# The Riemannian exponential map

For a point `p` of a smooth finite-dimensional Riemannian manifold `M`, the exponential map sends
a tangent vector `v ∈ T_p M` to the point reached at time `1` by the maximal geodesic leaving `p`
with velocity `v`.  Its natural domain is the set of `v` whose maximal geodesic interval contains
`1`.

The map is defined as a total function which takes the junk value `p` outside its natural domain;
every theorem about its mathematical value carries the corresponding domain hypothesis.  The
homogeneity of maximal geodesics turns into the two basic facts relating the exponential map to
geodesics: `t` lies in the maximal interval of `v` exactly when `t • v` lies in the domain, and
then `exp_p (t • v)` is the maximal geodesic at time `t`.  In particular the domain is star-shaped
at `0`, and it is all of `T_p M` exactly when every geodesic leaving `p` is defined for all time.

## Main definitions and results

* `TauCeti.Manifold.expDomain`: the natural domain of the exponential map at `p`.
* `TauCeti.Manifold.riemannianExp`: the exponential map at `p`.
* `TauCeti.Manifold.IsGeodesicallyCompleteAt`: every geodesic leaving `p` is defined for all time.
* `TauCeti.Manifold.mem_geodesicInterval_iff_smul_mem_expDomain`: the maximal interval of `v` is
  the set of times `t` with `t • v` in the domain.
* `TauCeti.Manifold.riemannianExp_smul`: `exp_p (t • v)` is the maximal geodesic at time `t`.
* `TauCeti.Manifold.starConvex_expDomain`: the domain is star-shaped at `0`.
* `TauCeti.Manifold.expDomain_eq_univ_iff`: the exponential map at `p` is defined on all of
  `T_p M` exactly when `M` is geodesically complete at `p`.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Ch. 5.
-/

-- Roadmap: HopfRinow

public section

open Bundle Manifold Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-! ### The domain and the map -/

variable (I M) in
/-- The natural domain of the Riemannian exponential map at `p`: the tangent vectors `v` whose
maximal geodesic from `p` with initial velocity `v` is defined at time `1`. -/
def expDomain (p : M) : Set (TangentSpace I p) :=
  {v | (1 : ℝ) ∈ geodesicInterval I M p v}

variable (I M) in
/-- The Riemannian exponential map at `p`: the value at time `1` of the maximal geodesic from `p`
with initial velocity `v`.  Outside `expDomain I M p` it takes the junk value `p`. -/
def riemannianExp (p : M) (v : TangentSpace I p) : M :=
  maximalGeodesic I M p v 1

omit [I.Boundaryless] in
/-- A tangent vector lies in the domain of the exponential map exactly when its maximal geodesic
interval contains `1`. -/
@[simp] theorem mem_expDomain_iff {p : M} {v : TangentSpace I p} :
    v ∈ expDomain I M p ↔ (1 : ℝ) ∈ geodesicInterval I M p v :=
  Iff.rfl

omit [I.Boundaryless] in
/-- The exponential map is the maximal geodesic evaluated at time `1`. -/
theorem riemannianExp_def (p : M) (v : TangentSpace I p) :
    riemannianExp I M p v = maximalGeodesic I M p v 1 := by
  rfl

omit [I.Boundaryless] in
/-- The zero vector lies in the domain of the exponential map. -/
theorem zero_mem_expDomain (p : M) : (0 : TangentSpace I p) ∈ expDomain I M p := by
  simp only [mem_expDomain_iff, geodesicInterval_zero, mem_univ]

/-- The exponential map sends the zero vector to the base point. -/
@[simp] theorem riemannianExp_zero [T2Space (TangentBundle I M)] (p : M) :
    riemannianExp I M p 0 = p := by
  simp [riemannianExp_def]

/-- Outside its natural domain, the exponential map takes its junk value `p`. -/
@[simp] theorem riemannianExp_of_notMem_expDomain {p : M} {v : TangentSpace I p}
    (hv : v ∉ expDomain I M p) : riemannianExp I M p v = p :=
  maximalGeodesic_eq_of_not_mem (mt mem_expDomain_iff.2 hv)

/-! ### Homogeneity -/

/-- **The domain of the exponential map along a ray.**  A time `t` lies in the maximal geodesic
interval of `v` exactly when `t • v` lies in the domain of the exponential map. -/
theorem mem_geodesicInterval_iff_smul_mem_expDomain {p : M} {v : TangentSpace I p} {t : ℝ} :
    t ∈ geodesicInterval I M p v ↔ t • v ∈ expDomain I M p := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · rw [mem_expDomain_iff, mem_geodesicInterval_smul_iff ht, mul_one]

/-- The geodesic interval of `v` is the preimage of the domain of the exponential map under
`t ↦ t • v`. -/
theorem geodesicInterval_eq_preimage_expDomain (p : M) (v : TangentSpace I p) :
    geodesicInterval I M p v = (fun t : ℝ ↦ t • v) ⁻¹' expDomain I M p := by
  ext t
  exact mem_geodesicInterval_iff_smul_mem_expDomain

/-- **The exponential map along a ray.**  If `t` lies in the maximal geodesic interval of `v`,
then `exp_p (t • v)` is the maximal geodesic from `p` with initial velocity `v` at time `t`. -/
theorem riemannianExp_smul [T2Space (TangentBundle I M)] {p : M} {v : TangentSpace I p} {t : ℝ}
    (ht : t ∈ geodesicInterval I M p v) :
    riemannianExp I M p (t • v) = maximalGeodesic I M p v t := by
  have h1 : (1 : ℝ) ∈ geodesicInterval I M p (t • v) :=
    mem_expDomain_iff.1 (mem_geodesicInterval_iff_smul_mem_expDomain.1 ht)
  rw [riemannianExp_def, maximalGeodesic_smul h1, mul_one]

/-- The domain of the exponential map is star-shaped at the zero vector. -/
theorem starConvex_expDomain (p : M) : StarConvex ℝ (0 : TangentSpace I p) (expDomain I M p) := by
  intro v hv a b _ hb hab
  rw [smul_zero, zero_add, ← mem_geodesicInterval_iff_smul_mem_expDomain]
  have hb1 : b ≤ 1 := by linarith
  exact ordConnected_geodesicInterval.out zero_mem_geodesicInterval (mem_expDomain_iff.1 hv)
    ⟨hb, hb1⟩

/-! ### Completeness at a point -/

variable (I M) in
/-- A Riemannian manifold is **geodesically complete at `p`** when every maximal geodesic leaving
`p` is defined for all time. -/
def IsGeodesicallyCompleteAt (p : M) : Prop :=
  ∀ v : TangentSpace I p, geodesicInterval I M p v = univ

/-- **Completeness at a point via the exponential map.**  The exponential map at `p` is defined on
all of `T_p M` exactly when every geodesic leaving `p` is defined for all time. -/
theorem expDomain_eq_univ_iff {p : M} :
    expDomain I M p = univ ↔ IsGeodesicallyCompleteAt I M p := by
  refine ⟨fun h v ↦ ?_, fun h ↦ eq_univ_of_forall fun v ↦ ?_⟩
  · rw [geodesicInterval_eq_preimage_expDomain, h, preimage_univ]
  · rw [mem_expDomain_iff, h v]
    exact mem_univ _

end TauCeti.Manifold

end
