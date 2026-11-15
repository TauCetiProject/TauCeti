/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.UniformTilt.Tate
public import TauCeti.RingTheory.Perfectoid.PseudoUniformizerRoots.Existence

/-!
# Perfectoid tilts of uniform algebras

Let `A` be a perfectoid Tate ring and `B` a complete Hausdorff uniform Tate ring in which `p`
is topologically nilpotent. A continuous ring homomorphism `A → B` makes the tilt of `B` a
perfectoid Tate ring, even though `B` itself need not be perfectoid. Indeed, transport a
pseudouniformiser with compatible roots from `A` to `B`, then apply the compatible-parameter
criterion for the tilt.

The hypotheses on `B` are the standing hypotheses of `uniformTilt`'s ring structure. In
particular, no perfectoid base *field*, injectivity of the homomorphism, or nonzero-ring
hypothesis is required. The Tate structure can be installed using
`RingHom.isTateRing_uniformTilt`, after which `RingHom.isPerfectoidTateRing_uniformTilt` applies.

## References

* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors and the tilting equivalence*,
  Arizona Winter School 2017, Lemma 2.7.1(c).
* P. Scholze, *Étale cohomology of diamonds*, Lemma 3.10.
-/

public section

open TauCeti.Huber TauCeti.Perfectoid

namespace RingHom

variable {p : ℕ} [Fact p.Prime] {A B : Type*}
  [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsTateRing A] [CompleteSpace A] [T2Space A] [IsPerfectoidTateRing p A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [IsTateRing B] [CompleteSpace B] [T2Space B] [IsUniform B]
  [Fact (IsTopologicallyNilpotent (p : B))]

/-- Transport compatible roots of a pseudouniformiser to the target ring. -/
private theorem exists_parameter_uniformTilt (f : A →+* B) (hf : Continuous f) :
    ∃ ϖ : uniformTilt p B, IsPseudoUniformizer (uniformTilt.coeff p B 0 ϖ) := by
  obtain ⟨ϖ⟩ := PseudoUniformizerRoots.nonempty (p := p) (R := A)
  refine ⟨uniformTilt.mk (fun n ↦ f (ϖ.root n)) (fun n ↦ ?_), ?_⟩
  · rw [← map_pow, ϖ.root_succ_pow]
  · simpa only [uniformTilt.coeff_mk] using ϖ.isPseudoUniformizer_root_zero.map hf

/-- A complete uniform Tate ring receiving a continuous homomorphism from a perfectoid Tate
ring has a Tate tilt: the image of a compatible-root parameter is a parameter in its tilt. -/
theorem isTateRing_uniformTilt (f : A →+* B) (hf : Continuous f) :
    IsTateRing (uniformTilt p B) := by
  obtain ⟨ϖ, hϖ⟩ := f.exists_parameter_uniformTilt (p := p) hf
  exact uniformTilt.isTateRing_of_sharp hϖ

/-- The tilt of a complete uniform Tate ring receiving a continuous homomorphism from a
perfectoid Tate ring is perfectoid. The target ring itself need not be perfectoid, and may
be zero. -/
theorem isPerfectoidTateRing_uniformTilt (f : A →+* B) (hf : Continuous f) :
    letI := f.isTateRing_uniformTilt (p := p) hf
    IsPerfectoidTateRing p (uniformTilt p B) := by
  obtain ⟨ϖ, hϖ⟩ := f.exists_parameter_uniformTilt (p := p) hf
  exact uniformTilt.isPerfectoidTateRing_of_sharp hϖ

end RingHom
