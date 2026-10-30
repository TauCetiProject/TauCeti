/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.ContinuousLevelSlice
public import TauCeti.Dynamics.Flow.ConnectingOrbit
public import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Quotient

/-!
# The topology of unparametrized connecting trajectories

The connecting set `Wᵘ(p) ∩ Wˢ(q)` carries the subspace topology. Its quotient by time
translation is homeomorphic to any level slice strictly between the endpoint values.
The inverse sends a point of the slice to its orbit class, so the homeomorphism identifies
the quotient topology with the topology inherited by the slice, rather than merely choosing
a bijection. This allows compactness and discreteness results for slices to be used for
unparametrized Morse trajectories.

The construction uses `Flow.IsNegativeGradient.exists_continuous_levelSlice` and Mathlib's
`Function.RightInverse.homeomorph` for a continuous retraction. No Morse nondegeneracy,
transversality, or finite-dimensionality is needed for this topological identification.

Use `φ.connectingOrbitSetoid p q` for the orbit relation and
`hφ.orbitQuotientHomeomorphLevelSlice hf hfp hfq hc` for the identification.
The characterization lemmas share their definitions' receiver namespaces.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2 (connecting trajectories modulo time translation).
-/

public section

open Set Topology

namespace Flow

namespace IsNegativeGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {φ : _root_.Flow ℝ E} {f : E → ℝ} {p q : E}

private theorem exists_homeomorph_levelSlice
    (hφ : IsNegativeGradient φ f)
    (hf : ∀ x ∈ unstableSet φ p ∩ stableSet φ q, DifferentiableAt ℝ f x)
    (hfp : ContinuousAt f p) (hfq : ContinuousAt f q)
    {c : ℝ} (hc : f q < c ∧ c < f p) :
    ∃ e : Quotient (connectingOrbitSetoid φ p q) ≃ₜ
        ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c}),
      ∀ x, e.symm x = Quotient.mk _ ⟨x.1, x.2.1⟩ := by
  obtain ⟨s, hs, horbit, hfix, hinvar⟩ :=
    hφ.exists_continuous_levelSlice hf hfp hfq hc
  let S := (unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c}
  let i : C(S, ↥(unstableSet φ p ∩ stableSet φ q)) :=
    ⟨fun x ↦ ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk _⟩
  let s' : C(↥(unstableSet φ p ∩ stableSet φ q), S) := ⟨s, hs⟩
  have hright : Function.RightInverse i s' := fun x ↦ Subtype.ext (hfix _ x.2.2)
  have hrel (x y : ↥(unstableSet φ p ∩ stableSet φ q)) :
      connectingOrbitSetoid φ p q x y ↔ Setoid.ker s' x y := by
    constructor
    · intro h
      obtain ⟨t, ht⟩ := connectingOrbitSetoid_apply x y |>.mp h
      have hxy : x = ⟨φ t y.1, ⟨isInvariant_unstableSet φ p t y.2.1,
          isInvariant_stableSet φ q t y.2.2⟩⟩ := Subtype.ext ht.symm
      rw [hxy]
      exact hinvar y t
    · intro h
      have horbit' (z : ↥(unstableSet φ p ∩ stableSet φ q)) :
          connectingOrbitSetoid φ p q (i (s' z)) z :=
        (connectingOrbitSetoid_apply _ _).mpr (φ.mem_orbit_iff.mp (horbit z))
      rw [Setoid.ker_def] at h
      exact (connectingOrbitSetoid φ p q).trans'
        ((connectingOrbitSetoid φ p q).symm' (horbit' x)) (h.symm ▸ horbit' y)
  let e := (Homeomorph.Quotient.congrRight hrel).trans hright.homeomorph
  refine ⟨e, fun x ↦ ?_⟩
  -- `Function.RightInverse.homeomorph` uses `Setoid.quotientKerEquivOfRightInverse`,
  -- whose inverse is `Quotient.mk` composed with `i`. The inverse of
  -- `Homeomorph.Quotient.congrRight` (via `Homeomorph.Quot.congr` and `Quot.congr`)
  -- preserves representatives, so their composite reduces to the displayed quotient class.
  rfl

/-- The orbit quotient of connecting negative-gradient trajectories is homeomorphic to an
intermediate level slice. Its inverse is the quotient map restricted to the slice. -/
noncomputable def orbitQuotientHomeomorphLevelSlice
    (hφ : IsNegativeGradient φ f)
    (hf : ∀ x ∈ unstableSet φ p ∩ stableSet φ q, DifferentiableAt ℝ f x)
    (hfp : ContinuousAt f p) (hfq : ContinuousAt f q)
    {c : ℝ} (hc : f q < c ∧ c < f p) :
    Quotient (connectingOrbitSetoid φ p q) ≃ₜ
      ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c}) :=
  Classical.choose (exists_homeomorph_levelSlice hφ hf hfp hfq hc)

/-- The inverse sends a point on the slice to its connecting orbit class. -/
@[simp]
theorem orbitQuotientHomeomorphLevelSlice_symm_apply
    (hφ : IsNegativeGradient φ f)
    (hf : ∀ x ∈ unstableSet φ p ∩ stableSet φ q, DifferentiableAt ℝ f x)
    (hfp : ContinuousAt f p) (hfq : ContinuousAt f q)
    {c : ℝ} (hc : f q < c ∧ c < f p)
    (x : ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c})) :
    (orbitQuotientHomeomorphLevelSlice hφ hf hfp hfq hc).symm x =
      Quotient.mk _ ⟨x.1, x.2.1⟩ :=
  Classical.choose_spec (exists_homeomorph_levelSlice hφ hf hfp hfq hc) x

/-- The image of a connecting orbit class is the unique point of that orbit on the slice. -/
@[simp]
theorem orbitQuotientHomeomorphLevelSlice_mk_eq_iff
    (hφ : IsNegativeGradient φ f)
    (hf : ∀ x ∈ unstableSet φ p ∩ stableSet φ q, DifferentiableAt ℝ f x)
    (hfp : ContinuousAt f p) (hfq : ContinuousAt f q)
    {c : ℝ} (hc : f q < c ∧ c < f p)
    (x : ↥(unstableSet φ p ∩ stableSet φ q))
    (y : ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c})) :
    orbitQuotientHomeomorphLevelSlice hφ hf hfp hfq hc (Quotient.mk _ x) = y ↔
      ∃ t : ℝ, φ t y.1 = x.1 := by
  rw [← Homeomorph.eq_symm_apply, orbitQuotientHomeomorphLevelSlice_symm_apply, Quotient.eq]
  exact connectingOrbitSetoid_apply _ _

end IsNegativeGradient

end Flow
