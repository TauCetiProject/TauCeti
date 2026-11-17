/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import TauCeti.GroupTheory.SurfaceGroup.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Fin
import TauCeti.GroupTheory.FreeGroup.Hopfian

/-!
# Closed surface groups are not free

The closed surface groups `S⁺(g, 0)` and `S⁻(g, 0)` of positive genus are not free groups, in
contrast with the surface groups with nonempty boundary. In particular no closed surface group of
Euler characteristic `χ ≤ 0`, that is `S⁺(g, 0)` with `g ≥ 1` or `S⁻(g, 0)` with `g ≥ 2`, is free;
neither is the projective-plane group `S⁻(1, 0)`. The hypothesis `g ≠ 0` is sharp, since
`S⁺(0, 0)` and `S⁻(0, 0)` are trivial.

Both cases follow Malcev's Hopfian argument. Every assignment of elements of `ℤ/2` to the
generators kills the relator, a product of commutators or of squares, so the closed surface
group has as many homomorphisms to `ℤ/2` as the free group on its generators; if it were free,
its rank would therefore be the number of generators. As free groups of finite rank are Hopfian,
the defining surjection from the free group on the generators would be injective
(`PresentedGroup.not_isFreeGroup`). It is not: the relator is a
nontrivial element of the free group, as one sees by sending `a₁` and `b₁` to two noncommuting
permutations, respectively every `cᵢ` to `1 ∈ ℤ`.

## Main results

* `TauCeti.SurfaceGroup.orientableRelator_ne_one` and
  `TauCeti.SurfaceGroup.nonorientableRelator_ne_one`: the relators of `S⁺(g, m)` and `S⁻(g, m)`
  are nontrivial unless `g = m = 0`.
* `TauCeti.SurfaceGroup.Orientable.not_isFreeGroup`: `S⁺(g, 0)` is not free for `g ≠ 0`.
* `TauCeti.SurfaceGroup.Nonorientable.not_isFreeGroup`: `S⁻(g, 0)` is not free for `g ≠ 0`.

## References

* A. I. Malcev, *On isomorphic matrix representations of infinite groups*, Mat. Sb. 8 (50)
  (1940), 405–422 (finitely generated residually finite groups are Hopfian).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, Section 1.2 (the presentations of the closed surface groups
  and their abelianisations).
* V. Guirardel, G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §5.1
  (surfaces with empty and nonempty boundary).
-/

public section

namespace TauCeti

namespace SurfaceGroup

variable {g m : ℕ}

/-- The defining relator of the orientable surface group `S⁺(g, m)` is a nontrivial element of
the free group on the generators unless `g = m = 0`. -/
theorem orientableRelator_ne_one (h : g ≠ 0 ∨ m ≠ 0) : orientableRelator g m ≠ 1 := by
  intro hr
  obtain ⟨n, rfl⟩ | hm := h.imp_left Nat.exists_eq_succ_of_ne_zero
  · -- Send `a₁` and `b₁` to two noncommuting permutations and every other generator to `1`.
    let f : FreeGroup (OrientableGenerator (n + 1) m) →* Equiv.Perm (Fin 3) := FreeGroup.lift fun
      | .a i => Fin.cons (α := fun _ ↦ Equiv.Perm (Fin 3)) (Equiv.swap 0 1) (fun _ ↦ 1) i
      | .b i => Fin.cons (α := fun _ ↦ Equiv.Perm (Fin 3)) (Equiv.swap 1 2) (fun _ ↦ 1) i
      | .peripheral _ => 1
    have hf : f (orientableRelator (n + 1) m) =
        Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 0 1 * Equiv.swap 1 2 := by
      rw [orientableRelator_def, map_orientableWord]
      simp [f, orientableWord_def, List.ofFn_const]
    rw [hr, map_one] at hf
    exact absurd hf (by decide)
  · -- Send every peripheral generator to `1 ∈ ℤ` and every other generator to `0`.
    have := congrArg (FreeGroup.lift fun
      | OrientableGenerator.peripheral _ => Multiplicative.ofAdd (1 : ℤ)
      | _ => 1) hr
    rw [orientableRelator_def, map_orientableWord,
      orientableWord_of_commute fun _ ↦ Commute.all _ _] at this
    simp [List.ofFn_const, ← ofAdd_nsmul] at this
    omega

/-- The defining relator of the nonorientable surface group `S⁻(g, m)` is a nontrivial element of
the free group on the generators unless `g = m = 0`. -/
theorem nonorientableRelator_ne_one (h : g ≠ 0 ∨ m ≠ 0) : nonorientableRelator g m ≠ 1 := by
  intro hr
  -- Send every generator to `1 ∈ ℤ`; the relator goes to `2g + m`.
  have := congrArg (FreeGroup.lift fun _ ↦ Multiplicative.ofAdd (1 : ℤ)) hr
  rw [nonorientableRelator_def, map_nonorientableWord, nonorientableWord_eq_pow_two_mul] at this
  simp [List.ofFn_const, ← ofAdd_nsmul, ← ofAdd_add] at this
  omega

namespace Orientable

/-- **Closed orientable surface groups of positive genus are not free.** For `g ≠ 0` the group
`S⁺(g, 0) = ⟨a₁, b₁, …, a_g, b_g | [a₁, b₁] ⋯ [a_g, b_g]⟩` is not a free group. -/
theorem not_isFreeGroup (hg : g ≠ 0) : ¬IsFreeGroup (Orientable g 0) := by
  refine PresentedGroup.not_isFreeGroup ?_ (Set.mem_singleton _)
    (orientableRelator_ne_one (.inl hg))
  -- A `ℤ/2`-valued assignment kills every commutator, hence the relator.
  rintro v _ rfl
  rw [orientableRelator_def, map_orientableWord, orientableWord_of_commute fun _ ↦ Commute.all _ _]
  simp

end Orientable

namespace Nonorientable

/-- **Closed nonorientable surface groups of positive genus are not free.** For `g ≠ 0` the group
`S⁻(g, 0) = ⟨c₁, …, c_g | c₁ ^ 2 ⋯ c_g ^ 2⟩` is not a free group. -/
theorem not_isFreeGroup (hg : g ≠ 0) : ¬IsFreeGroup (Nonorientable g 0) := by
  refine PresentedGroup.not_isFreeGroup ?_ (Set.mem_singleton _)
    (nonorientableRelator_ne_one (.inl hg))
  -- A `ℤ/2`-valued assignment kills every square, hence the relator.
  have hsq : ∀ x : Multiplicative (ZMod 2), x ^ 2 = 1 := by decide
  rintro v _ rfl
  rw [nonorientableRelator_def, map_nonorientableWord, nonorientableWord_eq_pow_two_mul]
  simp [hsq]

end Nonorientable

end SurfaceGroup

end TauCeti
