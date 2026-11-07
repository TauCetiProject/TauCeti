/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.UniformTilt.Tate
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Quotient
import TauCeti.RingTheory.Huber.Reduction

/-!
# Tilting Huber pairs

For a complete Hausdorff uniform Tate ring `B` in which `p` is topologically nilpotent,
the integral tilt of a ring of integral elements `B⁺` is again a ring of integral elements,
provided the tilt is Tate. A compatible system with a pseudouniformiser as zeroth coordinate
supplies this Tate hypothesis.

The main issue is integral closedness: the sharp map is not additive. Modulo the ideal of
topologically nilpotent elements of `B°`, it is a ring homomorphism. That ideal lies in every
ring of integral elements, so integral closedness descends to the reduction and can be pulled
back along sharp. This constructs the plus ring needed to regard tilting as a construction
on Huber pairs. `Huber.Pair.tilt` and `Huber.Pair.Hom.tilt` give that construction and its
functoriality on continuous plus-preserving maps. The Tate hypotheses can be supplied by
`RingHom.isTateRing_uniformTilt` for algebras over a perfectoid Tate ring.

## References

* P. Scholze, *Étale cohomology of diamonds*, Lemma 3.11.
* P. Scholze and J. Weinstein, *Berkeley Lectures on p-adic Geometry*, Lemma 6.2.5.
-/

public section

open TauCeti.Huber

namespace TauCeti.Perfectoid.uniformTilt

variable {p : ℕ} [Fact p.Prime] {B : Type*} [CommRing B] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [Fact (IsTopologicallyNilpotent (p : B))]
  {Bplus : Subring B}

/-- If the tilt is Tate, the integral tilt of any ring of integral elements is integrally closed
in it. Perfectoidness of the original ring is not needed. -/
theorem isIntegrallyClosedIn_plusSubring [IsTateRing (uniformTilt p B)]
    (h : IsRingOfIntegralElements Bplus) :
    IsIntegrallyClosedIn (plusSubring p h) (uniformTilt p B) := by
  classical
  let h₀ := isRingOfIntegralElements_powerBoundedSubring B
  let A₀ := plusSubring p h₀
  let A := plusSubring p h
  let D := Bplus.comap (powerBoundedSubring B).subtype
  let I := topologicallyNilpotentIdeal B
  let q := Ideal.Quotient.mk I
  -- Integral closedness descends because every topologically nilpotent element lies in `B⁺`.
  have hker : (RingHom.ker q : Set (powerBoundedSubring B)) ⊆ D := by
    intro b hb
    exact h.mem_of_isTopologicallyNilpotent
      (mem_topologicallyNilpotentIdeal.mp (Ideal.Quotient.eq_zero_iff_mem.mp hb))
  let := h.isIntegrallyClosedIn
  have hD : IsIntegrallyClosedIn (D.map q) (CanonicalReduction B) :=
    D.isIntegrallyClosedIn_map_of_ker_le q Ideal.Quotient.mk_surjective hker
  have hA : A ≤ A₀ := plusSubring_mono h h₀ h.le_powerBoundedSubring
  have hbounded : A ≤ powerBoundedSubring (uniformTilt p B) :=
    fun _ hx ↦ mem_powerBoundedSubring.mpr ((isBounded_plusSubring h).isPowerBounded_of_mem hx)
  let i := A.inclusion hA
  have hpI : (p : powerBoundedSubring B) ∈ I :=
    mem_topologicallyNilpotentIdeal.mpr (Fact.out : IsTopologicallyNilpotent (p : B))
  let s := sharpQuot (p := p) h₀ I hpI
  let g : A →+* D.map q := (s.comp i).codRestrict (D.map q) fun a ↦ by
    refine ⟨plusSharp p h₀ (i a), ?_, (sharpQuot_apply h₀ I hpI (i a)).symm⟩
    apply Subring.mem_comap.mpr
    simpa only [Subring.subtype_apply, coe_plusSharp, i, Subring.coe_inclusion]
      using mem_plusSubring_iff_coeff_zero.mp a.2
  refine Subring.isIntegrallyClosedIn_iff.mpr fun x hx ↦ ?_
  -- First put the integral element in the integral tilt of `B°`, where sharp is additive
  -- after reduction; then descend its integrality to the image of `B⁺` in that reduction.
  have hxpb : IsIntegral (powerBoundedSubring (uniformTilt p B)) x :=
    RingHom.IsIntegralElem.of_comp (f := A.inclusion hbounded) hx
  have hx₀ : x ∈ A₀ := by
    obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := uniformTilt p B)
    have hsharp : IsPseudoUniformizer (coeff p B 0 ϖ) := isPseudoUniformizer_iff.mpr
      ⟨isUnit_iff_coeff_zero.mp hϖ.isUnit,
        isTopologicallyNilpotent_iff_coeff_zero.mp hϖ.isTopologicallyNilpotent⟩
    exact mem_plusSubring_iff_coeff_zero.mpr ((mem_powerBoundedSubring_iff hsharp).mp
      (mem_powerBoundedSubring.mpr (isPowerBounded_of_isIntegral hxpb)))
  let y : A₀ := ⟨x, hx₀⟩
  have hy : i.IsIntegralElem y :=
    RingHom.IsIntegralElem.of_map A₀.subtype_injective hx
  have hs : IsIntegral (D.map q) (s y) :=
    RingHom.IsIntegralElem.of_comp (f := g) (hy.map s)
  have hmem := Subring.isIntegrallyClosedIn_iff.mp hD hs
  have he := Subring.comap_map_eq_self hker
  have hsharp : plusSharp p h₀ y ∈ D := by
    rw [← he]
    simpa only [Subring.mem_comap, s, sharpQuot_apply] using hmem
  exact mem_plusSubring_iff_coeff_zero.mpr (by
    simpa only [D, Subring.mem_comap, Subring.subtype_apply, coe_plusSharp] using hsharp)

/-- The integral tilt is a ring of integral elements whenever the tilt is Tate. -/
theorem isRingOfIntegralElements_plusSubring [IsTateRing (uniformTilt p B)]
    (h : IsRingOfIntegralElements Bplus) :
    IsRingOfIntegralElements (plusSubring p h) where
  isOpen := isOpen_plusSubring h
  isIntegrallyClosedIn := isIntegrallyClosedIn_plusSubring h
  le_powerBoundedSubring := fun _ hx ↦ mem_powerBoundedSubring.mpr
    ((isBounded_plusSubring h).isPowerBounded_of_mem hx)

end TauCeti.Perfectoid.uniformTilt

namespace TauCeti.Huber.Pair

open TauCeti.Perfectoid

variable {p : ℕ} [Fact p.Prime] {B : Type*} [CommRing B] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [Fact (IsTopologicallyNilpotent (p : B))]
  [IsTateRing (uniformTilt p B)]

/-- The tilt of a Huber pair whose underlying uniform Tate ring has a Tate tilt. Its plus ring
consists of compatible sequences with zeroth coordinate in the original plus ring. -/
noncomputable def tilt (P : Pair B) : Pair (uniformTilt p B) where
  plus := uniformTilt.plusSubring p P.isRingOfIntegralElements
  isRingOfIntegralElements :=
    uniformTilt.isRingOfIntegralElements_plusSubring P.isRingOfIntegralElements

/-- The plus ring of the tilted pair is the integral tilt of the original plus ring. -/
@[simp]
theorem tilt_plus (P : Pair B) : (P.tilt (p := p)).plus =
    uniformTilt.plusSubring p P.isRingOfIntegralElements := (rfl)

variable {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
  [IsTopologicalRing C] [IsTateRing C] [CompleteSpace C] [T2Space C] [IsUniform C]
  [Fact (IsTopologicallyNilpotent (p : C))] [IsTateRing (uniformTilt p C)]

/-- A continuous plus-preserving ring homomorphism induces a morphism of tilted Huber pairs. -/
noncomputable def Hom.tilt {P : Pair B} {Q : Pair C} (f : Hom P Q) :
    Hom (P.tilt (p := p)) (Q.tilt (p := p)) where
  toRingHom := uniformTilt.map f.toRingHom f.continuous_toRingHom
  continuous_toRingHom := uniformTilt.continuous_map f.toRingHom f.continuous_toRingHom
  map_mem_plus x hx := by
    rw [tilt_plus, uniformTilt.mem_plusSubring_iff_coeff_zero] at hx ⊢
    rw [uniformTilt.coeff_map]
    exact f.map_mem_plus _ hx

/-- The underlying homomorphism of a tilted pair morphism acts coordinatewise. -/
@[simp]
theorem Hom.tilt_toRingHom {P : Pair B} {Q : Pair C} (f : Hom P Q) :
    (f.tilt (p := p)).toRingHom = uniformTilt.map f.toRingHom f.continuous_toRingHom := (rfl)

/-- Tilting preserves the identity morphism of a Huber pair. -/
@[simp]
theorem Hom.tilt_id (P : Pair B) : (Hom.id P).tilt (p := p) = Hom.id (P.tilt (p := p)) := by
  apply Hom.ext
  simp

variable {D : Type*} [CommRing D] [UniformSpace D] [IsUniformAddGroup D]
  [IsTopologicalRing D] [IsTateRing D] [CompleteSpace D] [T2Space D] [IsUniform D]
  [Fact (IsTopologicallyNilpotent (p : D))] [IsTateRing (uniformTilt p D)]

/-- Tilting preserves composition of Huber-pair morphisms. -/
@[simp]
theorem Hom.tilt_comp {P : Pair B} {Q : Pair C} {R : Pair D} (g : Hom Q R) (f : Hom P Q) :
    (g.comp f).tilt (p := p) = (g.tilt (p := p)).comp (f.tilt (p := p)) := by
  apply Hom.ext
  simpa only [Hom.tilt_toRingHom, Hom.toRingHom_comp] using
    uniformTilt.map_comp f.toRingHom f.continuous_toRingHom g.toRingHom g.continuous_toRingHom

end TauCeti.Huber.Pair
