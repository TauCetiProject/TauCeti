/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Projectivization
public import TauCeti.Topology.Algebra.Projectivization.ZeroLocus
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.CoordinateRing

/-!
# The analytic topology on projective Weierstrass points

Give the native nonsingular projective points their subspace topology in projective space.
Continuous nonzero homogeneous coordinates therefore give continuous point-valued maps. For a
complex elliptic curve, every point of the projective cubic is nonsingular, so the comparison
is a homeomorphism onto the closed zero locus of the Weierstrass polynomial. In particular the
native point type is compact and Hausdorff. Compactness is an input to the construction of the
complex elliptic exponential map by complete translation flows.

The ellipticity hypothesis in the compactness statement is essential: the nonsingular locus
of a singular cubic need not be compact.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, VI.1.
-/

public section

open scoped LinearAlgebra.Projectivization Topology

namespace WeierstrassCurve.Projective.Point

section Topology

variable {F : Type*} [Field F] [TopologicalSpace F] {W : Projective F}

/-- The analytic topology on native nonsingular projective points is induced from projective
space by their homogeneous coordinates. -/
noncomputable instance instTopologicalSpace : TopologicalSpace W.Point :=
  TopologicalSpace.induced toProjectivization inferInstance

/-- Native nonsingular points carry exactly the subspace topology in projective space. -/
theorem isEmbedding_toProjectivization :
    Topology.IsEmbedding (toProjectivization : W.Point → ℙ F (Fin 3 → F)) :=
  toProjectivization_injective.isEmbedding_induced

/-- The comparison from native points to projective space is continuous. -/
@[fun_prop]
theorem continuous_toProjectivization :
    Continuous (toProjectivization : W.Point → ℙ F (Fin 3 → F)) :=
  isEmbedding_toProjectivization.continuous

instance [T2Space (ℙ F (Fin 3 → F))] : T2Space W.Point :=
  isEmbedding_toProjectivization.t2Space

/-- A map to native nonsingular points is continuous exactly when its map to projective space
is continuous. -/
theorem continuous_iff_toProjectivization {X : Type*} [TopologicalSpace X] {f : X → W.Point} :
    Continuous f ↔ Continuous (toProjectivization ∘ f) :=
  isEmbedding_toProjectivization.isInducing.continuous_iff

/-- Continuous homogeneous coordinates satisfying nonsingularity give a continuous map to the
native point type. No choice of normalized coordinates is needed. -/
theorem continuous_mk {X : Type*} [TopologicalSpace X] {P : X → Fin 3 → F}
    (hP : Continuous P) (hn : ∀ x, W.Nonsingular (P x)) :
    Continuous (fun x ↦ (Point.mk ((nonsingularLift_iff (P x)).mpr (hn x)) : W.Point)) := by
  rw [continuous_iff_toProjectivization]
  simpa only [Function.comp_def, toProjectivization_mk] using
    Projectivization.continuous_mk (K := F) hP (fun x ↦ ne_zero_of_nonsingular (hn x))

/-- A map to nonsingular points is continuous at a point if it locally has continuous
homogeneous coordinates. Nonsingularity and agreement are required only near the point. -/
theorem continuousAt_of_eventually_eq_mk {X : Type*} [TopologicalSpace X] {f : X → W.Point}
    {P : X → Fin 3 → F} {x₀ : X} (hP : ContinuousAt P x₀)
    (hf : ∀ᶠ x in nhds x₀, ∃ h : W.Nonsingular (P x),
      Point.mk ((nonsingularLift_iff (P x)).mpr h) = f x) : ContinuousAt f x₀ := by
  classical
  let Q : X → {v : Fin 3 → F // W.Nonsingular v} := fun x ↦
    if h : W.Nonsingular (P x) then ⟨P x, h⟩ else ⟨P x₀, hf.self_of_nhds.choose⟩
  have hQ : (fun x ↦ (Q x).val) =ᶠ[nhds x₀] P := by
    filter_upwards [hf] with x hx
    simp only [Q, dite_eq_left hx.choose]
  have hc : ContinuousAt Q x₀ :=
    tendsto_subtype_rng.mpr (hP.congr_of_eventuallyEq hQ)
  have hm := continuous_mk (W := W) continuous_subtype_val
    (fun v : {v : Fin 3 → F // W.Nonsingular v} ↦ v.property)
  apply (hm.continuousAt.comp hc).congr
  filter_upwards [hf] with x hx
  simpa only [Function.comp_def, Q, dite_eq_left hx.choose] using hx.choose_spec

end Topology

section Complex

variable (W : Projective ℂ) [W.IsElliptic]

/-- For a complex elliptic curve, the image of the native point type is the whole projective
zero locus of its Weierstrass polynomial. -/
theorem range_toProjectivization :
    Set.range (toProjectivization : W.Point → ℙ ℂ (Fin 3 → ℂ)) =
      TauCeti.complexProjectiveZeroLocus (fun _ : Unit ↦ W.polynomial) := by
  ext P
  induction P using Projectivization.ind with
  | h P hP =>
    rw [Set.mem_range, exists_toProjectivization_eq_mk_iff,
      TauCeti.complexProjectiveZeroLocus_mk_iff (fun _ ↦ W.isHomogeneous_polynomial)]
    simpa only [forall_const, Equation] using
      (equation_iff_nonsingular_of_ne_zero (W := W) hP).symm

/-- A complex elliptic curve embeds as a closed subset of the complex projective plane. -/
theorem isClosedEmbedding_toProjectivization :
    Topology.IsClosedEmbedding (toProjectivization : W.Point → ℙ ℂ (Fin 3 → ℂ)) :=
  ⟨isEmbedding_toProjectivization, by
    rw [range_toProjectivization]
    exact TauCeti.isClosed_complexProjectiveZeroLocus _⟩

/-- The native projective points of a complex elliptic curve, with their analytic topology,
form a compact space. -/
instance : CompactSpace W.Point :=
  (isClosedEmbedding_toProjectivization W).compactSpace

/-- Native points of a complex elliptic curve are homeomorphic to the zero locus of its
homogeneous equation, with the subspace topology in the complex projective plane. -/
noncomputable def homeomorphZeroLocus :
    W.Point ≃ₜ TauCeti.complexProjectiveZeroLocus (fun _ : Unit ↦ W.polynomial) :=
  isEmbedding_toProjectivization.toHomeomorph.trans
    (Homeomorph.setCongr (range_toProjectivization W))

/-- The zero-locus comparison preserves the point in projective space. -/
@[simp]
theorem coe_homeomorphZeroLocus_apply (P : W.Point) :
    (homeomorphZeroLocus W P : ℙ ℂ (Fin 3 → ℂ)) = P.toProjectivization :=
  (rfl)

end Complex

end WeierstrassCurve.Projective.Point
