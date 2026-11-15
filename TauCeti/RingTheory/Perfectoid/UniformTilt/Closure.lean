/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.UniformTilt.Tate
public import TauCeti.RingTheory.Huber.Subring
public import TauCeti.RingTheory.Huber.Perfect
public import TauCeti.Topology.Algebra.IsUniformGroup.Subring
public import Mathlib.Algebra.CharP.Subring

/-!
# Perfectoid closures inside a tilt

The closure of the image of a perfect ring inside a tilt is perfectoid whenever the image
contains a compatible pseudouniformiser and its inverse. The source ring needs no topology.
The closure carries the subspace topology, not an abstract completion topology.

The algebraic input is that inverse Frobenius preserves the image of a perfect ring; continuity
then makes it preserve the closure. The general version of this input is proved for perfect
complete Tate rings in `RingHom.perfectRing_topologicalClosure_range`.

## References

* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors and the tilting equivalence*,
  Arizona Winter School 2017, Lemma 2.7.1(c).
-/

public section

open TauCeti.Huber TauCeti.Perfectoid TauCeti.Perfectoid.uniformTilt

namespace RingHom

variable {p : ℕ} [Fact p.Prime] {B : Type*} [CommRing B] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [Fact (IsTopologicallyNilpotent (p : B))]
  {A : Type*} [CommRing A] [PerfectRing A p]

/-- The closure of a perfect ring's image in a tilt is perfectoid if the image contains a unit
whose sharp is a pseudouniformiser, and contains its inverse. The original ring `B` need not
be perfectoid; zero rings are included. -/
theorem isPerfectoidTateRing_topologicalClosure_range (f : A →+* uniformTilt p B)
    (u : (uniformTilt p B)ˣ) (hu : IsPseudoUniformizer (coeff p B 0 u.val))
    (hmem : u.val ∈ f.range) (hinv : (u⁻¹).val ∈ f.range) :
    letI := isTateRing_of_sharp hu
    letI := f.range.topologicalClosure.isTateRing_of_isPseudoUniformizer u
      (isPseudoUniformizer_iff.mpr ⟨u.isUnit,
        isTopologicallyNilpotent_iff_coeff_zero.mpr hu.isTopologicallyNilpotent⟩)
      (f.range.le_topologicalClosure hmem) (f.range.le_topologicalClosure hinv)
    letI : CompleteSpace f.range.topologicalClosure :=
      f.range.isClosed_topologicalClosure.completeSpace_coe
    IsPerfectoidTateRing p f.range.topologicalClosure := by
  let S := f.range.topologicalClosure
  let := isTateRing_of_sharp hu
  let := S.isTateRing_of_isPseudoUniformizer u
    (isPseudoUniformizer_iff.mpr ⟨u.isUnit,
      isTopologicallyNilpotent_iff_coeff_zero.mpr hu.isTopologicallyNilpotent⟩)
    (f.range.le_topologicalClosure hmem) (f.range.le_topologicalClosure hinv)
  let : CompleteSpace S := f.range.isClosed_topologicalClosure.completeSpace_coe
  rcases subsingleton_or_nontrivial B with hB | hB
  · let := hB
    exact isPerfectoidTateRing_of_subsingleton p S
  · let := hB
    let := f.perfectRing_topologicalClosure_range p
    exact IsPerfectoidTateRing.of_perfectRing

end RingHom
