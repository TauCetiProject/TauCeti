/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.UniformEllipticity

/-!
# Locality of uniform ellipticity on domains

The PDE roadmap keeps domain hypotheses explicit: estimates are stated on a set `Ω`, then
restricted to smaller balls or patched over local covers.  `UniformlyEllipticOn Ω a λ Λ` is
therefore a local-on-the-domain hypothesis.  This file records the small set-theoretic API that
later weak-form, maximum-principle, and interior-regularity arguments need in order to change
domains without unfolding the predicate.

The constants `λ` and `Λ` remain fixed throughout.  Patching lemmas such as
`UniformlyEllipticOn.union` require the same explicit constants on both pieces, matching the
roadmap convention that estimate constants are parameters rather than hidden existential data.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.congr_coeff`: replace a coefficient field by one that
  agrees on the domain.
* `TauCeti.PDE.UniformlyEllipticOn.union` and
  `TauCeti.PDE.uniformlyEllipticOn_union_iff`: patch uniform ellipticity over a binary union.
* `TauCeti.PDE.UniformlyEllipticOn.iUnion` and
  `TauCeti.PDE.uniformlyEllipticOn_iUnion_iff`: patch over an indexed union.
* `TauCeti.PDE.UniformlyEllipticOn.biUnion`: patch over a union indexed by points of a set.
-/

public section

namespace TauCeti

namespace PDE

open Matrix

variable {X n ι : Type*} [Fintype n] [DecidableEq n]
variable {Ω Ω' : Set X} {Ωs : ι → Set X} {a b : X → Matrix n n ℝ}
variable {lam Lam : ℝ}

namespace UniformlyEllipticOn

/-- Uniform ellipticity depends only on the coefficient values on the domain. -/
lemma congr_coeff (h : UniformlyEllipticOn Ω a lam Lam)
    (hab : ∀ ⦃x⦄, x ∈ Ω → b x = a x) : UniformlyEllipticOn Ω b lam Lam := by
  refine UniformlyEllipticOn.of_bounds h.pos h.le (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · rw [hab hx]
    exact h.lower_bound hx ξ
  · rw [hab hx]
    exact h.upper_bound hx η ξ

/-- Equal coefficient fields on the domain give equivalent uniform-ellipticity hypotheses. -/
lemma congr_coeff_iff (hab : ∀ ⦃x⦄, x ∈ Ω → a x = b x) :
    UniformlyEllipticOn Ω a lam Lam ↔ UniformlyEllipticOn Ω b lam Lam := by
  constructor
  · intro h
    exact h.congr_coeff (fun {x} hx => (hab hx).symm)
  · intro h
    exact h.congr_coeff hab

/-- Uniform ellipticity on the left side of an intersection, obtained by restriction. -/
lemma inter_left (h : UniformlyEllipticOn Ω a lam Lam) :
    UniformlyEllipticOn (Ω ∩ Ω') a lam Lam :=
  h.mono_set Set.inter_subset_left

/-- Uniform ellipticity on the right side of an intersection, obtained by restriction. -/
lemma inter_right (h : UniformlyEllipticOn Ω' a lam Lam) :
    UniformlyEllipticOn (Ω ∩ Ω') a lam Lam :=
  h.mono_set Set.inter_subset_right

/-- Uniform ellipticity patches over a binary union when the same constants work on both
pieces. -/
lemma union (hΩ : UniformlyEllipticOn Ω a lam Lam)
    (hΩ' : UniformlyEllipticOn Ω' a lam Lam) :
    UniformlyEllipticOn (Ω ∪ Ω') a lam Lam := by
  refine UniformlyEllipticOn.of_bounds hΩ.pos hΩ.le (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · rcases hx with hx | hx
    · exact hΩ.lower_bound hx ξ
    · exact hΩ'.lower_bound hx ξ
  · rcases hx with hx | hx
    · exact hΩ.upper_bound hx η ξ
    · exact hΩ'.upper_bound hx η ξ

/-- Uniform ellipticity patches over a nonempty indexed union when the same constants work on
every piece.  Nonemptiness is needed because `UniformlyEllipticOn` stores the side conditions
`0 < λ` and `λ ≤ Λ`, not only pointwise conditions on the domain. -/
lemma iUnion [Nonempty ι] (h : ∀ i, UniformlyEllipticOn (Ωs i) a lam Lam) :
    UniformlyEllipticOn (⋃ i, Ωs i) a lam Lam := by
  classical
  let i₀ := Classical.choice ‹Nonempty ι›
  refine UniformlyEllipticOn.of_bounds (h i₀).pos (h i₀).le (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
    exact (h i).lower_bound hi ξ
  · rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
    exact (h i).upper_bound hi η ξ

/-- Uniform ellipticity patches over a union indexed by points of a set. -/
lemma biUnion {s : Set ι} {Ωs : ι → Set X}
    (h : ∀ i ∈ s, UniformlyEllipticOn (Ωs i) a lam Lam)
    (hs : s.Nonempty) : UniformlyEllipticOn (⋃ i ∈ s, Ωs i) a lam Lam := by
  rcases hs with ⟨i₀, hi₀⟩
  refine UniformlyEllipticOn.of_bounds (h i₀ hi₀).pos (h i₀ hi₀).le
    (fun {x} hx ξ => ?_) (fun {x} hx η ξ => ?_)
  · rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hi, hxi⟩
    exact (h i hi).lower_bound hxi ξ
  · rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hi, hxi⟩
    exact (h i hi).upper_bound hxi η ξ

end UniformlyEllipticOn

/-- Binary-union characterization of uniform ellipticity with fixed constants. -/
lemma uniformlyEllipticOn_union_iff :
    UniformlyEllipticOn (Ω ∪ Ω') a lam Lam ↔
      UniformlyEllipticOn Ω a lam Lam ∧ UniformlyEllipticOn Ω' a lam Lam := by
  constructor
  · intro h
    exact ⟨h.mono_set Set.subset_union_left, h.mono_set Set.subset_union_right⟩
  · rintro ⟨hΩ, hΩ'⟩
    exact hΩ.union hΩ'

/-- Indexed-union characterization of uniform ellipticity with fixed constants, for nonempty
index types.  Nonemptiness is needed because `UniformlyEllipticOn` also stores the side
conditions `0 < λ` and `λ ≤ Λ`, which cannot be recovered from an empty family. -/
lemma uniformlyEllipticOn_iUnion_iff [Nonempty ι] :
    UniformlyEllipticOn (⋃ i, Ωs i) a lam Lam ↔
      ∀ i, UniformlyEllipticOn (Ωs i) a lam Lam := by
  constructor
  · intro h i
    exact h.mono_set (Set.subset_iUnion Ωs i)
  · intro h
    exact UniformlyEllipticOn.iUnion h

/-- Bounded-indexed-union characterization of uniform ellipticity with fixed constants. -/
lemma uniformlyEllipticOn_biUnion_iff {s : Set ι} {Ωs : ι → Set X} (hs : s.Nonempty) :
    UniformlyEllipticOn (⋃ i ∈ s, Ωs i) a lam Lam ↔
      ∀ i ∈ s, UniformlyEllipticOn (Ωs i) a lam Lam := by
  constructor
  · intro h i hi
    exact h.mono_set (by
      intro x hx
      exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, hx⟩⟩)
  · intro h
    exact UniformlyEllipticOn.biUnion h hs

end PDE

end TauCeti
