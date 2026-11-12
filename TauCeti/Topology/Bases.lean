/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Separation.Basic
public import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Countable bases and cardinality

A second-countable `T₀` space has at most continuum many points, since a point is determined by
the basic open sets containing it. A connected space covered by second-countable open sets is
second countable if each member meets only countably many other members.

## Main results

* `TauCeti.mk_le_continuum_of_secondCountableTopology`: a second-countable `T₀` space has at most
  `𝔠` points; in particular so does every Polish space.

* `TauCeti.secondCountableTopology_of_starCountable_cover`: a connected space with a
  star-countable cover by second-countable open sets is second countable.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Corollary 6.3.
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Lemma 19.22, pp.503–504, for the finite-chain argument for countability of integral leaves.
-/

public section

open Set Function Cardinal TopologicalSpace

universe u

namespace TauCeti

/-- **A second-countable `T₀` space has at most continuum many points.** A point is determined
by the members of a countable basis containing it. In particular a Polish space has at most `𝔠`
points. -/
theorem mk_le_continuum_of_secondCountableTopology (X : Type u) [TopologicalSpace X]
    [SecondCountableTopology X] [T0Space X] : #X ≤ 𝔠 := by
  obtain ⟨b, hbc, hb⟩ := exists_countable_basis X
  have : Countable b := hbc.to_subtype
  have hinj : Injective fun x : X => {s : b | x ∈ (s : Set X)} := fun x y hxy =>
    hb.2.eq_iff.2 fun s hs => by simpa using congrArg (⟨s, hs⟩ ∈ ·) hxy
  calc #X ≤ #(Set b) := mk_le_of_injective hinj
    _ = 2 ^ #b := mk_set
    _ ≤ 2 ^ ℵ₀ := power_le_power_left two_ne_zero mk_le_aleph0
    _ = 𝔠 := two_power_aleph0

/-- A connected space covered by second-countable open sets is second countable if each member
of the cover meets only countably many other members. The indexing type need not be countable. -/
theorem secondCountableTopology_of_starCountable_cover {X : Type*} {P : Type*}
    [TopologicalSpace X] [ConnectedSpace X] (U : P → Set X)
    [∀ p, SecondCountableTopology (U p)] (ho : ∀ p, IsOpen (U p))
    (hcover : ⋃ p, U p = Set.univ) (hc : ∀ p, {q | (U p ∩ U q).Nonempty}.Countable) :
    SecondCountableTopology X := by
  let x : X := Classical.choice inferInstance
  obtain ⟨p, hp⟩ : ∃ p, x ∈ U p := mem_iUnion.mp (hcover.symm ▸ mem_univ x)
  let level : ℕ → Set P := Nat.rec {p} (fun _ S ↦ ⋃ q ∈ S, {r | (U q ∩ U r).Nonempty})
  have hlevel : ∀ n, (level n).Countable := by
    intro n
    induction n with
    | zero => exact countable_singleton p
    | succ n ih => exact ih.biUnion (fun q _ ↦ hc q)
  let S : Set P := ⋃ n, level n
  have hSc : S.Countable := countable_iUnion hlevel
  have hpS : p ∈ S := mem_iUnion.mpr ⟨0, mem_singleton p⟩
  have hS : ∀ q ∈ S, ∀ r, (U q ∩ U r).Nonempty → r ∈ S := by
    intro q hq r hqr
    obtain ⟨n, hn⟩ := mem_iUnion.mp hq
    exact mem_iUnion.mpr ⟨n + 1, mem_iUnion₂.mpr ⟨q, hn, hqr⟩⟩
  let V : Set X := ⋃ q ∈ S, U q
  have hv : IsOpen V := isOpen_iUnion fun q ↦ isOpen_iUnion fun _ ↦ ho q
  have hcomp : Vᶜ = ⋃ q ∈ Sᶜ, U q := by
    ext y
    constructor
    · intro hy
      obtain ⟨q, hq⟩ : ∃ q, y ∈ U q := mem_iUnion.mp (hcover.symm ▸ mem_univ y)
      refine mem_iUnion₂.mpr ⟨q, ?_, hq⟩
      intro hqS
      exact hy (mem_iUnion₂.mpr ⟨q, hqS, hq⟩)
    · intro hy hV
      obtain ⟨q, hqS, hyq⟩ := mem_iUnion₂.mp hy
      obtain ⟨r, hrS, hyr⟩ := mem_iUnion₂.mp hV
      exact hqS (hS r hrS q ⟨y, hyr, hyq⟩)
  have hvclosed : IsClosed V := isOpen_compl_iff.mp (by
    rw [hcomp]
    exact isOpen_iUnion fun q ↦ isOpen_iUnion fun _ ↦ ho q)
  have hfull : V = Set.univ := (show IsClopen V from ⟨hvclosed, hv⟩).eq_univ
    ⟨x, mem_iUnion₂.mpr ⟨p, hpS, hp⟩⟩
  let _ : Countable S := hSc.to_subtype
  let _ : ∀ q : S, SecondCountableTopology (U q.val) := fun q ↦ inferInstance
  apply secondCountableTopology_of_countable_cover (U := fun q : S ↦ U q.val)
  · exact fun q ↦ ho q.val
  · simpa only [iUnion_subtype] using hfull

end TauCeti
