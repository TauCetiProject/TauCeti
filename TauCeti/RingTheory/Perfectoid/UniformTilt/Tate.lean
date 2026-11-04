/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.UniformTilt.Plus
public import TauCeti.RingTheory.Perfectoid.PerfectRing

/-!
# When the tilt of a uniform Tate ring is Tate

The integral tilt of a ring of integral elements is open and bounded for the inverse-limit
topology. Units and topological nilpotence can be tested on the zeroth coordinate. Consequently,
if a compatible system of roots has a pseudouniformiser as zeroth coordinate, the tilt is a Tate
ring. Since it is perfect of characteristic `p`, it is then perfectoid. No perfectoidness of the
original ring is needed, nor any divisibility condition on the pseudouniformiser.

This supplies the Tate-ring structure needed to use the integral tilt as a ring of definition.
It also identifies the power-bounded elements of the tilt by their zeroth coordinates.

## References

* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors and the tilting equivalence*,
  Arizona Winter School 2017, Lemma 2.7.1(a), (c).
* P. Scholze, *Étale cohomology of diamonds*, Lemma 3.10.
-/

public section

open Filter Topology Pointwise TauCeti.Huber

namespace TauCeti.Perfectoid.uniformTilt

variable {p : ℕ} [hp : Fact p.Prime] {B : Type*} [CommRing B] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [Fact (IsTopologicallyNilpotent (p : B))]

/-- A compatible system whose zeroth coordinate is a pseudouniformiser makes the tilt Tate. -/
theorem isTateRing_of_sharp {ϖ : uniformTilt p B}
    (hϖ : IsPseudoUniformizer (coeff p B 0 ϖ)) : IsTateRing (uniformTilt p B) :=
  IsTateRing.of_isOpen_isBounded
    (plusSubring p (isRingOfIntegralElements_powerBoundedSubring B))
    (isOpen_plusSubring _) (isBounded_plusSubring _)
    (isPseudoUniformizer_iff.mpr ⟨isUnit_iff_coeff_zero.mpr hϖ.isUnit,
      isTopologicallyNilpotent_iff_coeff_zero.mpr hϖ.isTopologicallyNilpotent⟩)

/-- Under the compatible-pseudouniformiser hypothesis, power-boundedness in the tilt is detected
by the zeroth coordinate. -/
theorem mem_powerBoundedSubring_iff {ϖ : uniformTilt p B}
    (hϖ : IsPseudoUniformizer (coeff p B 0 ϖ)) {x : uniformTilt p B} :
    letI := isTateRing_of_sharp hϖ
    x ∈ powerBoundedSubring (uniformTilt p B) ↔ coeff p B 0 x ∈ powerBoundedSubring B := by
  let := isTateRing_of_sharp hϖ
  let hB := isRingOfIntegralElements_powerBoundedSubring B
  constructor
  · intro hx
    have hnil : IsTopologicallyNilpotent ϖ :=
      isTopologicallyNilpotent_iff_coeff_zero.mpr hϖ.isTopologicallyNilpotent
    obtain ⟨N, hN⟩ := (isPowerBounded_iff.mp (mem_powerBoundedSubring.mp hx)).exists_pow_mul_subset
      hnil ((isOpen_plusSubring hB).mem_nhds (zero_mem _))
    have hpow (n : ℕ) : coeff p B 0 ϖ ^ N * coeff p B 0 x ^ n ∈ powerBoundedSubring B := by
      have := mem_plusSubring_iff_coeff_zero.mp
        (hN (Set.mul_mem_mul (Set.mem_singleton _) (Set.mem_range_self n)))
      simpa only [map_mul, map_pow] using this
    let u := (hϖ.isUnit.pow N).unit
    apply mem_powerBoundedSubring.mpr
    apply isPowerBounded_iff.mpr
    apply ((isBounded_singleton (↑u⁻¹ : B)).mul IsUniform.isBounded_powerBoundedSubring).subset
    rintro _ ⟨n, rfl⟩
    exact Set.mem_mul.mpr ⟨_, rfl, _, hpow n, (hϖ.isUnit.pow N).unit.inv_mul_cancel_left _⟩
  · intro hx
    exact mem_powerBoundedSubring.mpr ((isBounded_plusSubring hB).isPowerBounded_of_mem
      (mem_plusSubring_iff_coeff_zero.mpr hx))

/-- A tilt containing a compatible pseudouniformiser is perfectoid, even if the original complete
uniform Tate ring is not perfectoid. The zero ring is included. -/
theorem isPerfectoidTateRing_of_sharp {ϖ : uniformTilt p B}
    (hϖ : IsPseudoUniformizer (coeff p B 0 ϖ)) :
    letI := isTateRing_of_sharp hϖ
    IsPerfectoidTateRing p (uniformTilt p B) := by
  let := isTateRing_of_sharp hϖ
  rcases subsingleton_or_nontrivial B with hB | hB
  · let := hB
    exact isPerfectoidTateRing_of_subsingleton p _
  · let := hB
    exact IsPerfectoidTateRing.of_perfectRing

end TauCeti.Perfectoid.uniformTilt
