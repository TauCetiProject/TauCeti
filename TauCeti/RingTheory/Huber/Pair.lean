/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import TauCeti.RingTheory.Huber.Basic

/-!
# Huber pairs

A *ring of integral elements* of a Huber ring `A` is an open subring `A⁺` which is integrally
closed in `A` and consists of power-bounded elements, and a *Huber pair* `(A, A⁺)` is a Huber
ring together with such a subring. Huber pairs are the affine objects of the theory: the adic
spectrum of the next layer is built from one.

A Huber ring has many rings of integral elements, so `A⁺` is carried as data rather than
selected by a typeclass; this is the roadmap's standing convention that the plus ring is
explicit.

## Main definitions

* `TauCeti.Huber.IsRingOfIntegralElements`: `A⁺` is open, integrally closed in `A`, and
  contained in `A°`.
* `TauCeti.Huber.Pair`: a Huber pair, that is, a choice of `A⁺`.
* `TauCeti.Huber.Pair.Hom`: a continuous ring homomorphism carrying `A⁺` into `B⁺`.

## Main results

* `TauCeti.Huber.IsRingOfIntegralElements.mem_of_isTopologicallyNilpotent`: `A°° ⊆ A⁺` for
  every ring of integral elements.
* `TauCeti.Huber.Pair.discrete`: a discrete ring is a Huber pair with `A⁺ = A`, so the
  definitions above are not vacuous.
* `TauCeti.Huber.Pair.Hom.id`, `TauCeti.Huber.Pair.Hom.comp`: morphisms of Huber pairs compose,
  associatively and unitally (`TauCeti.Huber.Pair.Hom.comp_assoc`,
  `TauCeti.Huber.Pair.Hom.id_comp`, `TauCeti.Huber.Pair.Hom.comp_id`).

## Provenance

The shape of these declarations follows the roadmap's own prototype in
`TauCetiRoadmap/AdicSpaces/Suggested.lean`, which fixes the design choice that the plus ring is
explicit data rather than a typeclass, and the selection of results follows AINTLIB's
`AffinoidRings.lean`; neither's proofs were used.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Definition 7.14 and Remark 7.15.
* [AINTLIB](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  `projects/AdicSpaces/Adic spaces/AffinoidRings.lean`.
-/

@[expose] public section

open Filter Topology

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- A subring `A⁺` of a nonarchimedean ring is a *ring of integral elements* if it is open,
integrally closed in `A`, and contained in the power-bounded subring `A°`. -/
structure IsRingOfIntegralElements [NonarchimedeanRing A] (Aplus : Subring A) : Prop where
  /-- `A⁺` is open in `A`. -/
  isOpen : IsOpen (Aplus : Set A)
  /-- `A⁺` is integrally closed in `A`. -/
  isIntegrallyClosed : ∀ x : A, IsIntegral Aplus x → x ∈ Aplus
  /-- Every element of `A⁺` is power-bounded. -/
  le_powerBoundedSubring : Aplus ≤ powerBoundedSubring A

omit [IsTopologicalRing A] in
/-- Wedhorn: an open integrally closed subring contains every topologically nilpotent element.

The powers of a topologically nilpotent `a` eventually land in the subring, which is a
neighbourhood of zero; from `aⁿ` in it with `n` positive, `a` is integral over it and integral
closedness finishes. Neither power-boundedness nor a nonarchimedean topology plays any part, so
this is stated for an arbitrary open integrally closed subring. -/
theorem mem_of_isTopologicallyNilpotent_of_isIntegrallyClosed {Aplus : Subring A}
    (hopen : IsOpen (Aplus : Set A)) (hclosed : ∀ x : A, IsIntegral Aplus x → x ∈ Aplus) {a : A}
    (ha : IsTopologicallyNilpotent a) : a ∈ Aplus := by
  obtain ⟨n, hmem, hn⟩ :=
    ((ha.eventually_mem (hopen.mem_nhds Aplus.zero_mem)).and (eventually_gt_atTop 0)).exists
  exact hclosed a (IsIntegral.of_pow hn (isIntegral_algebraMap (x := (⟨a ^ n, hmem⟩ : Aplus))))

omit [IsTopologicalRing A] in
/-- `A°° ⊆ A⁺` for every ring of integral elements. -/
theorem IsRingOfIntegralElements.mem_of_isTopologicallyNilpotent [NonarchimedeanRing A]
    {Aplus : Subring A} (h : IsRingOfIntegralElements Aplus) {a : A}
    (ha : IsTopologicallyNilpotent a) : a ∈ Aplus :=
  mem_of_isTopologicallyNilpotent_of_isIntegrallyClosed h.isOpen h.isIntegrallyClosed ha

variable (A) in
/-- A *Huber pair* `(A, A⁺)`: a Huber ring together with a ring of integral elements. Only the
noncanonical subring `A⁺` is stored; the Huber structure on `A` is a parameter. -/
structure Pair [IsHuberRing A] where
  /-- The ring of integral elements `A⁺`. -/
  plus : Subring A
  /-- `A⁺` really is a ring of integral elements. -/
  isRingOfIntegralElements : IsRingOfIntegralElements plus

namespace Pair

variable {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- A morphism of Huber pairs is a continuous ring homomorphism carrying `A⁺` into `B⁺`. -/
structure Hom [IsHuberRing A] [IsHuberRing B] (S : Pair A) (T : Pair B) where
  /-- The underlying ring homomorphism. -/
  toRingHom : A →+* B
  /-- The underlying ring homomorphism is continuous. -/
  continuous_toRingHom : Continuous toRingHom
  /-- The underlying ring homomorphism carries `A⁺` into `B⁺`. -/
  map_mem_plus : ∀ a ∈ S.plus, toRingHom a ∈ T.plus

variable {C : Type*} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
variable [IsHuberRing A] [IsHuberRing B] [IsHuberRing C]

/-- The identity morphism of a Huber pair. -/
def Hom.id (S : Pair A) : Hom S S where
  toRingHom := RingHom.id A
  continuous_toRingHom := continuous_id
  map_mem_plus _ ha := ha

/-- Morphisms of Huber pairs compose. -/
def Hom.comp {S : Pair A} {T : Pair B} {U : Pair C} (g : Hom T U) (f : Hom S T) : Hom S U where
  toRingHom := g.toRingHom.comp f.toRingHom
  continuous_toRingHom := g.continuous_toRingHom.comp f.continuous_toRingHom
  map_mem_plus _ ha := g.map_mem_plus _ (f.map_mem_plus _ ha)

@[simp]
theorem Hom.toRingHom_id (S : Pair A) : (Hom.id S).toRingHom = RingHom.id A := rfl

@[simp]
theorem Hom.toRingHom_comp {S : Pair A} {T : Pair B} {U : Pair C} (g : Hom T U) (f : Hom S T) :
    (g.comp f).toRingHom = g.toRingHom.comp f.toRingHom := rfl

@[ext]
theorem Hom.ext {S : Pair A} {T : Pair B} {f g : Hom S T}
    (h : f.toRingHom = g.toRingHom) : f = g := by
  cases f; cases g; congr

/-- Composition of morphisms of Huber pairs is associative. -/
theorem Hom.comp_assoc {D : Type*} [CommRing D] [TopologicalSpace D] [IsTopologicalRing D]
    [IsHuberRing D] {S : Pair A} {T : Pair B} {U : Pair C} {V : Pair D}
    (h : Hom U V) (g : Hom T U) (f : Hom S T) : (h.comp g).comp f = h.comp (g.comp f) := by
  ext; rfl

@[simp]
theorem Hom.id_comp {S : Pair A} {T : Pair B} (f : Hom S T) : (Hom.id T).comp f = f := by
  ext; rfl

@[simp]
theorem Hom.comp_id {S : Pair A} {T : Pair B} (f : Hom S T) : f.comp (Hom.id S) = f := by
  ext; rfl

variable (A) in
/-- A discrete ring is a Huber pair with `A⁺ = A`: every element is power-bounded, the whole
ring is open, and `⊤` is trivially integrally closed. This is the witness that the definitions
above are satisfiable. -/
def discrete [DiscreteTopology A] : Pair A where
  plus := ⊤
  isRingOfIntegralElements :=
    { isOpen := by simp
      isIntegrallyClosed := fun _ _ ↦ trivial
      le_powerBoundedSubring := by simp }

end Pair

end TauCeti.Huber
