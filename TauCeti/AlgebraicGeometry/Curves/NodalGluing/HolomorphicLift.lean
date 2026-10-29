/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.Lift
public import TauCeti.Geometry.Manifold.Complex.Analytic
public import TauCeti.Geometry.Manifold.Complex.Chart

/-!
# Holomorphic lifting across the branches of a node

A node-preserving homeomorphism of glued complex curves has a unique continuous lift to the
normalizations. If that lift is holomorphic away from the flag points, it is holomorphic
everywhere: the finitely many flag points are removable singularities. Its inverse is then
holomorphic as well, so the homeomorphism comes from an actual isomorphism of nodal curves.

The complex manifold hypotheses concern the disjoint normalizations themselves, with the
existing sigma charts. Neither compactness nor connectedness nor a finite set of components is
needed. Self-nodes and interchanges of the two branches are allowed. The topological punctured
neighbourhood hypotheses are the ones used by `liftHomeomorph`.

* `mdifferentiable_liftHomeomorph` extends holomorphy across the flag points.
* `Iso.ofHolomorphicLift` constructs the analytic nodal isomorphism from holomorphy of the
  forward lift away from the flag points; no regularity hypothesis on its inverse is needed.
* `existsUnique_iso_gluedCurveHomeomorph_eq_iff` characterizes which node-preserving
  homeomorphisms are induced by analytic nodal isomorphisms.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §2, for removable singularities.
* Joel W. Robbin and Dietmar A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. 8 (2006), 611–699, for biholomorphisms of nodal normalizations.
-/

public noncomputable section

open Filter Set Topology
open scoped Manifold ContDiff

namespace TauCeti.NodalGluing

variable {ι Flag : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  [∀ i, ChartedSpace ℂ (X i)] [∀ i, T2Space (X i)] [Finite Flag]
  {ι' Flag' : Type*} {X' : ι' → Type*} [∀ i, TopologicalSpace (X' i)]
  [∀ i, ChartedSpace ℂ (X' i)] [∀ i, T2Space (X' i)] [Finite Flag']
  [IsManifold 𝓘(ℂ) 1 (Σ i, X i)] [IsManifold 𝓘(ℂ) 1 (Σ i, X' i)]
  {d : FlagPairData ι Flag X} {d' : FlagPairData ι' Flag' X'}
  {h : GluedCurve d ≃ₜ GluedCurve d'}
  {hN : ∀ z, h z ∈ nodeSet d' ↔ z ∈ nodeSet d}
  {hX : ∀ x ∈ flagPointSet d, ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected (V \ {x})}
  {hX' : ∀ x ∈ flagPointSet d', ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected (V \ {x})}

/-- A continuous normalization lift holomorphic off the flag points is holomorphic everywhere.
The flags are isolated, so continuity removes each possible singularity. -/
theorem mdifferentiable_liftHomeomorph
    (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (liftHomeomorph h hN hX hX') (flagPointSet d)ᶜ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (liftHomeomorph h hN hX hX') :=
  (flagPointSet_finite d).mdifferentiable_of_continuous_of_compl
    (liftHomeomorph h hN hX hX').continuous hf

namespace Iso

/-- Lift a node-preserving homeomorphism to an analytic nodal isomorphism. Holomorphy of the
forward lift off the flags suffices; continuity removes the flag singularities, and the
holomorphic inverse theorem supplies the inverse. -/
def ofHolomorphicLift
    (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (liftHomeomorph h hN hX hX') (flagPointSet d)ᶜ) :
    Iso 𝓘(ℂ) ω d d' :=
  ofGluedCurveHomeomorph 𝓘(ℂ) ω h hN hX hX'
    (mdifferentiable_liftHomeomorph hf).contMDiff
    (by
      have hi := (liftHomeomorph h hN hX hX').isHomeomorph.mdifferentiable_symm
        (mdifferentiable_liftHomeomorph hf)
      have he : (liftHomeomorph h hN hX hX').isHomeomorph.homeomorph
          (liftHomeomorph h hN hX hX') = liftHomeomorph h hN hX hX' :=
        Homeomorph.ext fun _ ↦ by simp
      rw [he] at hi
      exact hi.contMDiff)

/-- The analytic lift has the same underlying map as the topological normalization lift. -/
@[simp]
theorem coe_ofHolomorphicLift
    (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (liftHomeomorph h hN hX hX') (flagPointSet d)ᶜ) :
    ⇑(ofHolomorphicLift hf) = liftHomeomorph h hN hX hX' :=
  coe_ofGluedCurveHomeomorph

/-- Descending the analytic lift recovers the original homeomorphism of glued curves. -/
@[simp]
theorem gluedCurveHomeomorph_ofHolomorphicLift
    (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (liftHomeomorph h hN hX hX') (flagPointSet d)ᶜ) :
    (ofHolomorphicLift hf).gluedCurveHomeomorph = h :=
  gluedCurveHomeomorph_ofGluedCurveHomeomorph

/-- Lifting the descent of an analytic nodal isomorphism recovers that isomorphism. -/
@[simp]
theorem ofHolomorphicLift_gluedCurveHomeomorph (e : Iso 𝓘(ℂ) ω d d')
    {hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      (liftHomeomorph e.gluedCurveHomeomorph e.gluedCurveHomeomorph_mem_nodeSet_iff hX hX')
      (flagPointSet d)ᶜ} :
    ofHolomorphicLift hf = e :=
  Iso.ext fun x ↦ by
    rw [coe_ofHolomorphicLift, liftHomeomorph_gluedCurveHomeomorph]

end Iso

/-- A node-preserving homeomorphism is induced by a unique analytic nodal isomorphism exactly
when its normalization lift is holomorphic away from the flag points. -/
theorem existsUnique_iso_gluedCurveHomeomorph_eq_iff :
    (∃! e : Iso 𝓘(ℂ) ω d d', e.gluedCurveHomeomorph = h) ↔
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (liftHomeomorph h hN hX hX') (flagPointSet d)ᶜ := by
  constructor
  · rintro ⟨e, rfl, -⟩
    rw [Iso.liftHomeomorph_gluedCurveHomeomorph]
    exact (e.toDiffeomorph.contMDiff.mdifferentiable (by simp)).mdifferentiableOn
  · intro hf
    refine ⟨Iso.ofHolomorphicLift hf, Iso.gluedCurveHomeomorph_ofHolomorphicLift hf, ?_⟩
    intro e rfl
    exact (Iso.ofHolomorphicLift_gluedCurveHomeomorph e).symm

end TauCeti.NodalGluing
