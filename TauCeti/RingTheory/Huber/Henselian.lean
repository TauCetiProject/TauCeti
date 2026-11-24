/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Pair
public import TauCeti.RingTheory.Huber.RingOfDefinition
public import TauCeti.RingTheory.Henselian.Ideal
public import TauCeti.RingTheory.Henselian.Lifting

/-!
# Henselian subrings of complete Huber rings

Let `A` be a complete Hausdorff Huber ring. Every open subring `B ⊆ A°` is henselian along every
ideal of `B` whose elements are topologically nilpotent in `A`. In particular `(A°, A°°)` is a
henselian pair, as is `(A⁺, I)` for a ring of integral elements `A⁺` and any ideal `I ⊆ A°°`, and
`(B, ϖB)` for any topologically nilpotent `ϖ ∈ B`, for instance a pseudouniformizer of a Tate
ring. No noetherian, Tate or uniformity hypothesis is needed, and `A°` may be unbounded.

The argument uses rings of definition rather than completeness of `B`. For a pair of definition
`(A₀, J)` the radical of `J` consists of the elements of `A₀` that are topologically nilpotent in
`A`, and `A₀` is `J`-adically complete, hence henselian along `J` and so along its radical.
Finitely many coefficients and the witnesses to the simple-root conditions lie in a single ring
of definition inside `B`, where the root can be lifted. The same finite containment argument puts
the topologically nilpotent elements of `B` in its Jacobson radical.

## Main results

* `TauCeti.Huber.PairOfDefinition.henselianRing`: a ring of definition of a complete Hausdorff
  Huber ring is henselian along every ideal of topologically nilpotent elements.
* `TauCeti.Huber.henselianRing_of_isOpen_subring`: the same for open subrings of `A°`.
* `TauCeti.Huber.henselianRing_topologicallyNilpotentIdeal`: `(A°, A°°)` is henselian.

## References

* T. Wedhorn, *Adic Spaces*, Corollary 6.4 and Proposition 6.14.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, Lemma 7.2.3(5) and its proof.
* Stacks Project, Tag 0FWT, stability of henselian pairs under filtered colimits.
-/

public section

open Polynomial

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [IsHuberRing A] [CompleteSpace A] [T0Space A]

omit [IsTopologicalRing A] [IsHuberRing A] in
/-- A ring of definition of a complete Hausdorff Huber ring is henselian along every ideal whose
elements are topologically nilpotent in `A`. -/
theorem PairOfDefinition.henselianRing (P : PairOfDefinition A) {I : Ideal P.ringOfDefinition}
    (hI : ∀ x ∈ I, IsTopologicallyNilpotent (x : A)) :
    HenselianRing P.ringOfDefinition I :=
  Ideal.henselianRing_of_le (I := P.idealOfDefinition.radical)
    fun x hx ↦ P.mem_radical_idealOfDefinition_iff.mpr (hI x hx)

/-- An element of an open subring of the power-bounded elements of a complete Hausdorff Huber
ring that is topologically nilpotent in the ambient ring belongs to the Jacobson radical of that
subring. -/
theorem mem_jacobson_bot_of_isOpen_subring {B : Subring A}
    (hopen : IsOpen (B : Set A)) (hle : B ≤ powerBoundedSubring A)
    {x : B} (hx : IsTopologicallyNilpotent (x : A)) :
    x ∈ Ideal.jacobson (⊥ : Ideal B) := by
  classical
  rw [Ideal.jacobson_bot, Ring.mem_jacobson_iff]
  intro y
  obtain ⟨P, hPB, hs⟩ := exists_pairOfDefinition_finset_subset hopen {x, y}
    (fun z _ ↦ mem_powerBoundedSubring.mp (hle z.property))
  let x₀ : P.ringOfDefinition := ⟨x, hs x (by simp)⟩
  let y₀ : P.ringOfDefinition := ⟨y, hs y (by simp)⟩
  have hx₀ : x₀ ∈ Ring.jacobson P.ringOfDefinition :=
    HenselianRing.jac (I := P.idealOfDefinition.radical)
      (P.mem_radical_idealOfDefinition_iff (a := x₀) |>.mpr hx)
  exact (Ring.mem_jacobson_iff.mp hx₀ y₀).map (Subring.inclusion hPB)

/-- **Henselian subrings of complete Huber rings.** An open subring `B` of the power-bounded
elements of a complete Hausdorff Huber ring is henselian along every ideal whose elements are
topologically nilpotent in the ambient ring. No boundedness of `B`, adic separatedness of `B`,
or openness of the ideal is required. -/
theorem henselianRing_of_isOpen_subring {B : Subring A}
    (hopen : IsOpen (B : Set A)) (hle : B ≤ powerBoundedSubring A) {I : Ideal B}
    (hI : ∀ x ∈ I, IsTopologicallyNilpotent (x : A)) :
    HenselianRing B I := by
  classical
  refine ⟨fun x hx ↦ Ideal.jacobson_bot (R := B) ▸
    mem_jacobson_bot_of_isOpen_subring hopen hle (hI x hx),
    fun f hf a hfa hu ↦ ?_⟩
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hu
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hbc : f.derivative.eval a * b - 1 ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa using sub_eq_zero.mpr hb
  -- Put the approximate root, the inverse derivative and the coefficients in one ring.
  let s : Finset B := {a, b} ∪ f.coeffs
  obtain ⟨P, hPB, hs⟩ := exists_pairOfDefinition_finset_subset hopen s
    (fun x _ ↦ mem_powerBoundedSubring.mp (hle x.property))
  let ι := Subring.inclusion hPB
  have hrange (x : B) (hx : x ∈ s) : x ∈ Set.range ι :=
    ⟨⟨x, hs x hx⟩, Subtype.ext rfl⟩
  have hlift : f ∈ Polynomial.lifts ι := by
    rw [lifts_iff_coeffs_subset_range]
    exact fun x hx ↦ hrange x (Finset.mem_union_right _ hx)
  have := P.henselianRing (I := I.comap ι) fun x hx ↦ hI (ι x) hx
  exact HenselianRing.exists_isRoot_of_lifts hf hlift hfa hbc
    (hrange a (by simp [s])) (hrange b (by simp [s]))

/-- An open subring of the power-bounded elements of a complete Hausdorff Huber ring is
henselian along the principal ideal of any of its elements that is topologically nilpotent in the
ambient ring, for instance a pseudouniformizer of a Tate ring. -/
theorem henselianRing_span_singleton_of_isOpen_subring {B : Subring A}
    (hopen : IsOpen (B : Set A)) (hle : B ≤ powerBoundedSubring A)
    (ϖ : B) (hϖ : IsTopologicallyNilpotent (ϖ : A)) :
    HenselianRing B (Ideal.span {ϖ}) := by
  refine henselianRing_of_isOpen_subring hopen hle fun x hx ↦ ?_
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  exact (mem_powerBoundedSubring.mp (hle c.property)).isTopologicallyNilpotent_mul hϖ

/-- The power-bounded elements of a complete Hausdorff Huber ring are henselian along the
topologically nilpotent ones: `(A°, A°°)` is a henselian pair. -/
instance henselianRing_topologicallyNilpotentIdeal :
    HenselianRing (powerBoundedSubring A) (topologicallyNilpotentIdeal A) :=
  henselianRing_of_isOpen_subring (isOpen_powerBoundedSubring A) le_rfl fun _ hx ↦
    mem_topologicallyNilpotentIdeal.mp hx

/-- A ring of integral elements of a complete Hausdorff Huber ring is henselian along every ideal
whose elements are topologically nilpotent in the ambient ring. -/
theorem IsRingOfIntegralElements.henselianRing {Aplus : Subring A}
    (h : IsRingOfIntegralElements Aplus) {I : Ideal Aplus}
    (hI : ∀ x ∈ I, IsTopologicallyNilpotent (x : A)) :
    HenselianRing Aplus I :=
  henselianRing_of_isOpen_subring h.isOpen h.le_powerBoundedSubring hI

end TauCeti.Huber
