/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.RingOfDefinition
public import TauCeti.RingTheory.Henselian.Lifting

/-!
# Henselian subrings of complete Tate rings

An open subring of the power-bounded elements of a complete Hausdorff Tate ring is henselian
along any pseudouniformizer it contains. In particular, the power-bounded subring itself is
henselian. This supplies simple-root lifting even when that subring is not adically separated.

The argument uses rings of definition rather than completeness of the power-bounded subring:
finitely many coefficients and the witnesses to the simple-root conditions lie in a single
ring of definition inside the given open subring. That ring is adically complete and hence
henselian. The same finite containment argument puts the pseudouniformizer in the Jacobson
radical of the larger subring.

## References

* T. Wedhorn, *Adic Spaces*, Corollary 6.4 and Proposition 6.14.
* Stacks Project, Tag 0FWT, stability of henselian pairs under filtered colimits.
-/

public section

open Polynomial

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [IsHuberRing A] [CompleteSpace A] [T0Space A]

omit [IsHuberRing A] in
/-- A ring of definition of a complete Hausdorff Tate ring is henselian along every
pseudouniformizer it contains. -/
theorem PairOfDefinition.henselianRing (P : PairOfDefinition A)
    (ϖ : P.ringOfDefinition) (hϖ : IsPseudoUniformizer (ϖ : A)) :
    HenselianRing P.ringOfDefinition (Ideal.span {ϖ}) := by
  have := P.isAdicComplete_span_singleton ϖ hϖ
  infer_instance

/-- A pseudouniformizer in an open subring of the power-bounded elements of a complete
Hausdorff Tate ring belongs to the Jacobson radical of that subring. -/
theorem mem_jacobson_bot_of_isOpen_subring {B : Subring A}
    (hopen : IsOpen (B : Set A)) (hle : B ≤ powerBoundedSubring A)
    (ϖ : B) (hϖ : IsPseudoUniformizer (ϖ : A)) :
    ϖ ∈ Ideal.jacobson (⊥ : Ideal B) := by
  classical
  rw [Ideal.mem_jacobson_bot]
  intro y
  obtain ⟨P, hPB, hs⟩ := exists_pairOfDefinition_finset_subset hopen hle {ϖ, y}
  let π : P.ringOfDefinition := ⟨ϖ, hs ϖ (by simp)⟩
  let y₀ : P.ringOfDefinition := ⟨y, hs y (by simp)⟩
  have := P.henselianRing π hϖ
  have hπ : π ∈ Ideal.jacobson (⊥ : Ideal P.ringOfDefinition) :=
    HenselianRing.jac (Ideal.mem_span_singleton_self π)
  exact (Ideal.mem_jacobson_bot.mp hπ y₀).map (Subring.inclusion hPB)

/-- An open subring of the power-bounded subring of a complete Hausdorff Tate ring is
henselian along any pseudouniformizer it contains. No boundedness of the whole subring, or
adic separatedness of that subring, is required. -/
theorem henselianRing_of_isOpen_subring {B : Subring A}
    (hopen : IsOpen (B : Set A)) (hle : B ≤ powerBoundedSubring A)
    (ϖ : B) (hϖ : IsPseudoUniformizer (ϖ : A)) :
    HenselianRing B (Ideal.span {ϖ}) := by
  classical
  refine ⟨(Ideal.span_singleton_le_iff_mem _).mpr
    (mem_jacobson_bot_of_isOpen_subring hopen hle ϖ hϖ), fun f hf a hfa hu ↦ ?_⟩
  -- Record all the finite witnesses before choosing a ring of definition.
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hfa
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hu
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hbc : f.derivative.eval a * b - 1 ∈ Ideal.span {ϖ} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa using sub_eq_zero.mpr hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hbc
  -- Put the approximate root, inverse, divisibility witnesses and coefficients in one ring.
  let s : Finset B := {ϖ, a, b, c, d} ∪ f.coeffs
  obtain ⟨P, hPB, hs⟩ := exists_pairOfDefinition_finset_subset hopen hle s
  let ι := Subring.inclusion hPB
  have hinj : Function.Injective ι := Subring.inclusion_injective hPB
  have hrange (x : B) (hx : x ∈ s) : x ∈ Set.range ι :=
    ⟨⟨x, hs x hx⟩, Subtype.ext rfl⟩
  obtain ⟨π, hπ⟩ := hrange ϖ (by simp [s])
  have hlift : f ∈ Polynomial.lifts ι := by
    rw [lifts_iff_coeffs_subset_range]
    exact fun x hx ↦ hrange x (Finset.mem_union_right _ hx)
  have hnil : IsPseudoUniformizer (π : A) := by
    have heq : (π : A) = (ϖ : A) := congrArg (fun x : B ↦ (x : A)) hπ
    rwa [heq]
  have := P.henselianRing π hnil
  -- Transport the simple-root lift from the ring of definition to the open subring.
  simpa only [hπ] using HenselianRing.exists_isRoot_of_injective hinj (π := π) hf hlift
    (by simpa only [hπ] using hd) (by simpa only [hπ] using hc)
    (hrange a (by simp [s])) (hrange b (by simp [s]))
    (hrange c (by simp [s])) (hrange d (by simp [s]))

/-- The power-bounded elements of a complete Hausdorff Tate ring are henselian along a
pseudouniformizer, even when they are not adically separated. -/
theorem henselianRing_powerBoundedSubring (ϖ : powerBoundedSubring A)
    (hϖ : IsPseudoUniformizer (ϖ : A)) :
    HenselianRing (powerBoundedSubring A) (Ideal.span {ϖ}) :=
  henselianRing_of_isOpen_subring (isOpen_powerBoundedSubring A) le_rfl ϖ hϖ

end TauCeti.Huber
