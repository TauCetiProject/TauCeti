/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Convexity
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential.Basic
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Nonsingularity of the exponential map in nonpositive curvature

If sectional curvature is nonpositive along the radial geodesic from `p` to `exp_p v`,
then the differential of `exp_p` at `v` is injective. Indeed, a vector in its kernel gives
a Jacobi field vanishing at times zero and one, hence the zero field; its initial covariant
derivative recovers the vector. Finite dimensionality and the manifold inverse function
theorem then give a smooth local inverse at `v`.

The pointwise results require curvature bounds only along this one segment and membership
in the natural exponential domain. They need neither completeness nor a dimension bound.
For a manifold with nonpositive sectional curvature, the exponential map is therefore a
local diffeomorphism on its whole natural domain. This is the nonsingularity step in the
Cartan–Hadamard theorem; no global injectivity or covering conclusion is asserted here.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapters 10 and 12.
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {p : M} {v : TangentSpace I p}

/-- Nonpositive sectional curvature along a radial segment makes the differential of the
exponential map at its final initial-velocity vector injective. The segment need not minimize. -/
theorem injective_mfderiv_riemannianExp_of_sectionalCurvature_nonpos
    (hv : v ∈ expDomain I M p)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u w : TangentSpace I (riemannianExp I M p (t • v)),
      LinearIndependent ℝ ![u, w] →
        (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
          (riemannianExp I M p (t • v)) u w ≤ 0) :
    Function.Injective (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v) := by
  apply (injective_iff_map_eq_zero _).2
  intro w hw
  -- The tangent space of the vector space `T_p M` is that vector space itself. Give the
  -- vector this type explicitly so scalar operations use its fixed fibre instances.
  let w' : TangentSpace I p := w
  have hw' : mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w' = 0 := hw
  have hJ := isJacobiFieldOn_mfderiv_riemannianExp p v w'
  have hsub : Icc (0 : ℝ) 1 ⊆ geodesicInterval I M p v :=
    ordConnected_geodesicInterval.out zero_mem_geodesicInterval (mem_expDomain_iff.1 hv)
  have hdiff := uniqueDiffOn_Icc (zero_lt_one : (0 : ℝ) < 1)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hzero (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) (t • w') = 0 :=
    (hJ.mono hdiff hsub).eq_zero_of_endpoints_eq_zero_of_sectionalCurvature_nonpos
      (a := 0) (b := 1) isPreconnected_Icc hK h0 (by simp) (by norm_num)
      (by simp only [zero_smul]; exact map_zero _)
      (by
        -- `erw` unfolds the tangent-space wrappers when rewriting the source point
        -- of the differential, which also appears in its dependent type.
        erw [one_smul ℝ v, one_smul ℝ w']
        exact hw') ht
  have hd := alongCurveWithin_congr (leviCivitaConnection I M)
    (fun t : ℝ ↦ riemannianExp I M p (t • v))
    (fun t ↦ mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) (t • w'))
    (W := fun _ ↦ 0)
    (Filter.mem_of_superset self_mem_nhdsWithin hzero) (hzero 0 h0)
  rw [hJ.alongCurveWithin_subset (hdiff 0 h0) hsub h0,
    alongCurveWithin_mfderiv_riemannianExp_zero, alongCurveWithin_zero] at hd
  exact hd

/-- In nonpositive sectional curvature along a radial segment, the exponential map has a
smooth local inverse at its final initial-velocity vector, without any completeness hypothesis. -/
theorem isLocalDiffeomorphAt_riemannianExp_of_sectionalCurvature_nonpos
    (hv : v ∈ expDomain I M p)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u w : TangentSpace I (riemannianExp I M p (t • v)),
      LinearIndependent ℝ ![u, w] →
        (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
          (riemannianExp I M p (t • v)) u w ≤ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I p) I ∞ (riemannianExp I M p) v := by
  have hinj := injective_mfderiv_riemannianExp_of_sectionalCurvature_nonpos hv hK
  let e := (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v).toLinearMap
    |>.linearEquivOfInjective hinj (by simp [TauCeti.finrank_tangentSpace])
  exact isLocalDiffeomorphAt_of_mfderiv_eq (contMDiffOn_riemannianExp (I := I) p)
    (isOpen_expDomain (I := I) p) hv BoundarylessManifold.isInteriorPoint (by simp)
    ⟨e.toContinuousLinearEquiv, by ext; simp [e]⟩

/-- On a manifold of nonpositive sectional curvature, the exponential map is a smooth local
diffeomorphism on its natural domain. -/
theorem isLocalDiffeomorphOn_riemannianExp_of_sectionalCurvature_nonpos
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p : M) :
    IsLocalDiffeomorphOn 𝓘(ℝ, TangentSpace I p) I ∞ (riemannianExp I M p)
      (expDomain I M p) :=
  fun v ↦ isLocalDiffeomorphAt_riemannianExp_of_sectionalCurvature_nonpos v.2
    (fun t _ ↦ hK (riemannianExp I M p (t • v.1)))

end TauCeti.Manifold
