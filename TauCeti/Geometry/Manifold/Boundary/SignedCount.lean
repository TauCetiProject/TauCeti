/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.InducedOrientation
public import TauCeti.Geometry.Manifold.Boundary.OneDimensional
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Stokes
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ZeroDim

/-!
# The signed boundary count of a compact oriented one-manifold

Let `M` be a compact Hausdorff smooth manifold modelled on the half-line `EuclideanHalfSpace 1`,
with an orientation `o`. Its boundary is finite
(`TauCeti.ModelWithCorners.finite_boundary_euclideanHalfSpace_one`) and carries the induced
outward-first orientation `TauCeti.boundaryOrientation o`. On a zero-dimensional manifold an
orientation is a sign `±1` at each point: the sign `Orientation.signBasis` of the orientation of
the zero tangent space relative to its unique basis, indexed by `Fin 0`. At a boundary point `x`
the sign is `1` exactly when an outward tangent vector at `x` is positively oriented for `o`, and
`-1` exactly when it is negatively oriented.

The statements take the basis of each zero tangent space as an argument `e`; any choice, such as
`(EuclideanSpace.basisFun (Fin 0) ℝ).toBasis`, is the unique one.

This file proves that these signs add up to zero. Equivalently, `M` has as many boundary points at
which the orientation points outward as boundary points at which it points inward. This is the
oriented refinement of the parity statement
`TauCeti.ModelWithCorners.even_ncard_boundary_euclideanHalfSpace_one`. It is the input to the
classical proof that the integral Morse differential squares to zero: an oriented compactified
space of index-two trajectories is a compact oriented one-manifold whose boundary points are the
broken trajectories, so the signed counts of broken trajectories cancel.

The proof is Stokes' theorem `TauCeti.integralTopForm_mextDeriv` for the constant function `1`.
Its exterior derivative vanishes, so the integral of the boundary restriction vanishes, and on the
finite zero-dimensional boundary that integral is the sum of the orientation signs
(`TauCeti.integralTopForm_ofFunction_finite_zeroDim`).

## Main results

* `TauCeti.signBasis_orientationAt_boundaryOrientation_eq_one_iff`,
  `TauCeti.signBasis_orientationAt_boundaryOrientation_eq_neg_one_iff`: the boundary sign at a
  point is `1`, respectively `-1`, exactly when an outward vector there is positively,
  respectively negatively, oriented.
* `TauCeti.finsum_signBasis_orientationAt_boundaryOrientation_eq_zero`: the boundary signs of a
  compact oriented one-manifold add up to zero.
* `TauCeti.ncard_setOf_signBasis_eq_one_eq_ncard_setOf_signBasis_eq_neg_one`: a compact oriented
  one-manifold has as many boundary points of sign `1` as of sign `-1`.

## References

* J. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5, where the vanishing of the signed boundary count of a compact oriented one-manifold proves
  the homotopy invariance of the degree.
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2, where it proves that the integral Morse differential
  squares to zero.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (0 + 1)) M]
  [IsManifold (𝓡∂ (0 + 1)) ∞ M]

local instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) 1 ((𝓡∂ (0 + 1)).boundary M) :=
  isManifold_boundary M one_ne_zero

/-- The boundary sign at `x`, read against any basis `e` of the zero-dimensional tangent space,
is `1` exactly when an outward tangent vector at `x`, taken as a basis of the tangent line, is
positively oriented. -/
theorem signBasis_orientationAt_boundaryOrientation_eq_one_iff
    (o : Manifold.Orientation (𝓡∂ (0 + 1)) M (Fin 1)) (x : (𝓡∂ (0 + 1)).boundary M)
    {v : TangentSpace (𝓡∂ (0 + 1)) (x : M)} (hv : IsOutwardPointing (x : M) v)
    (b : Module.Basis (Fin 1) ℝ (TangentSpace (𝓡∂ (0 + 1)) (x : M))) (hb : b 0 = v)
    (e : Module.Basis (Fin 0) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) x)) :
    Orientation.signBasis ((boundaryOrientation o).orientationAt x) e = 1 ↔
      b.orientation = o.orientationAt (x : M) := by
  rw [← boundaryOrientation_spec o x hv e b (by funext i; rw [Fin.fin_one_eq_zero i, hb]; rfl)]
  rcases e.orientation_eq_or_eq_neg ((boundaryOrientation o).orientationAt x) with h | h <;>
    rw [h]
  · exact ⟨fun _ ↦ rfl, fun _ ↦ Orientation.signBasis_orientation e⟩
  · rw [Orientation.signBasis_neg, Orientation.signBasis_orientation]
    exact ⟨fun h' ↦ absurd h' (by decide), fun h' ↦ absurd h' (Module.Ray.ne_neg_self _)⟩

/-- The boundary sign at `x`, read against any basis `e` of the zero-dimensional tangent space,
is `-1` exactly when an outward tangent vector at `x`, taken as a basis of the tangent line, is
negatively oriented. -/
theorem signBasis_orientationAt_boundaryOrientation_eq_neg_one_iff
    (o : Manifold.Orientation (𝓡∂ (0 + 1)) M (Fin 1)) (x : (𝓡∂ (0 + 1)).boundary M)
    {v : TangentSpace (𝓡∂ (0 + 1)) (x : M)} (hv : IsOutwardPointing (x : M) v)
    (b : Module.Basis (Fin 1) ℝ (TangentSpace (𝓡∂ (0 + 1)) (x : M))) (hb : b 0 = v)
    (e : Module.Basis (Fin 0) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) x)) :
    Orientation.signBasis ((boundaryOrientation o).orientationAt x) e = -1 ↔
      b.orientation = -o.orientationAt (x : M) := by
  have key := signBasis_orientationAt_boundaryOrientation_eq_one_iff o x hv b hb e
  rcases Int.units_eq_one_or (Orientation.signBasis ((boundaryOrientation o).orientationAt x) e)
    with h | h
  · refine ⟨fun h' ↦ absurd (h.symm.trans h') (by decide), fun h' ↦ ?_⟩
    exact absurd ((key.mp h).symm.trans h') (Module.Ray.ne_neg_self _)
  · refine ⟨fun _ ↦ ?_, fun _ ↦ h⟩
    have hne : o.orientationAt (x : M) ≠ b.orientation :=
      fun he ↦ absurd (h.symm.trans (key.mpr he.symm)) (by decide)
    rw [(b.orientation_ne_iff_eq_neg _).mp hne]
    exact (neg_neg b.orientation).symm

variable [T2Space M] [CompactSpace M]

/-- **The signed boundary count of a compact oriented one-manifold vanishes.** The boundary signs
of the induced outward-first orientation, read against any bases `e x` of the zero-dimensional
tangent spaces, add up to zero. -/
theorem finsum_signBasis_orientationAt_boundaryOrientation_eq_zero
    (o : Manifold.Orientation (𝓡∂ (0 + 1)) M (Fin 1))
    (e : ∀ x : (𝓡∂ (0 + 1)).boundary M,
      Module.Basis (Fin 0) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) x)) :
    ∑ᶠ x, (Orientation.signBasis ((boundaryOrientation o).orientationAt x) (e x) : ℤ) = 0 := by
  classical
  let _ : Fintype ((𝓡∂ (0 + 1)).boundary M) :=
    (ModelWithCorners.finite_boundary_euclideanHalfSpace_one (M := M)).fintype
  let φ := RoughForm.ofFunction (𝓡∂ (0 + 1)) (fun _ : M ↦ (1 : ℝ))
  have hφ : IsSmoothForm (𝓡∂ (0 + 1)) 1 φ := isSmoothForm_ofFunction_iff.mpr contMDiff_const
  have hc : IsCompact (_root_.tsupport (α := EuclideanSpace ℝ (Fin 1) [⋀^Fin 0]→L[ℝ] ℝ) φ) :=
    (isClosed_tsupport _).isCompact
  have hd : mextDeriv φ = 0 := by
    funext x
    rw [mextDeriv_ofFunction, mvfderiv_eq_zero_iff.mpr (mfderiv_const ..)]
    ext v
    simp
  -- Stokes for the constant function `1`: the boundary integral is the signed count.
  have h := integralTopForm_mextDeriv o hφ hc
  rw [hd, integralTopForm_zero, boundaryRestriction_eq_mpullback, mpullback_ofFunction,
    integralTopForm_ofFunction_finite_zeroDim (b := (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis)]
    at h
  -- A basis indexed by `Fin 0` is unique, so the signs do not depend on the chosen bases.
  have he (x : (𝓡∂ (0 + 1)).boundary M) : e x =
      ((EuclideanSpace.basisFun (Fin 0) ℝ).toBasis :
        Module.Basis (Fin 0) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) x)) :=
    Module.Basis.eq_of_apply_eq fun i ↦ i.elim0
  rw [finsum_eq_sum_of_fintype]
  simp only [he]
  exact_mod_cast (by simpa using h.symm :
    ∑ x : (𝓡∂ (0 + 1)).boundary M, ((Orientation.signBasis
      ((boundaryOrientation o).orientationAt x)
      (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis : ℤ) : ℝ) = 0)

/-- A compact oriented one-manifold has as many boundary points of sign `1` as of sign `-1`: by
`TauCeti.signBasis_orientationAt_boundaryOrientation_eq_one_iff`, as many boundary points at which
the orientation points outward as boundary points at which it points inward. -/
theorem ncard_setOf_signBasis_eq_one_eq_ncard_setOf_signBasis_eq_neg_one
    (o : Manifold.Orientation (𝓡∂ (0 + 1)) M (Fin 1))
    (e : ∀ x : (𝓡∂ (0 + 1)).boundary M,
      Module.Basis (Fin 0) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) x)) :
    {x | Orientation.signBasis ((boundaryOrientation o).orientationAt x) (e x) = 1}.ncard =
      {x | Orientation.signBasis ((boundaryOrientation o).orientationAt x) (e x) = -1}.ncard := by
  classical
  let _ : Fintype ((𝓡∂ (0 + 1)).boundary M) :=
    (ModelWithCorners.finite_boundary_euclideanHalfSpace_one (M := M)).fintype
  suffices ∀ s : (𝓡∂ (0 + 1)).boundary M → ℤˣ, ∑ᶠ x, (s x : ℤ) = 0 →
      {x | s x = 1}.ncard = {x | s x = -1}.ncard from
    this _ (finsum_signBasis_orientationAt_boundaryOrientation_eq_zero o e)
  intro s h
  rw [finsum_eq_sum_of_fintype,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x ↦ s x = 1)] at h
  have hneg : Finset.univ.filter (fun x ↦ ¬s x = 1) = Finset.univ.filter (fun x ↦ s x = -1) := by
    ext x
    rcases Int.units_eq_one_or (s x) with hx | hx <;> simp [hx]
  have h₁ : ∑ x ∈ Finset.univ.filter (fun x ↦ s x = 1), (s x : ℤ) =
      (Finset.univ.filter (fun x ↦ s x = 1)).card := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    exact Finset.sum_congr rfl fun x hx ↦ by simp [(Finset.mem_filter.mp hx).2]
  have h₂ : ∑ x ∈ Finset.univ.filter (fun x ↦ s x = -1), (s x : ℤ) =
      -(Finset.univ.filter (fun x ↦ s x = -1)).card := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x hx ↦ by simp [(Finset.mem_filter.mp hx).2]
  rw [hneg] at h
  rw [← Finset.coe_filter_univ, ← Finset.coe_filter_univ, Set.ncard_coe_finset,
    Set.ncard_coe_finset]
  omega

end TauCeti
