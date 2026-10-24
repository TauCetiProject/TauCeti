/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Diagonal.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.TorusGeneration

/-!
# Perfectness of the standard symplectic group

Over a field containing a nonzero element whose square is not one, the standard symplectic group
`Sp₂ₘ` is perfect in every rank. Conjugation by a diagonal torus element scales each root
subgroup through its root character, so the commutator of the torus element with a root element
`x_α(c)` is `x_α((α(t) - 1) c)`. Every root character is nontrivial on a suitable coordinate
torus element, hence every root element is a commutator. The root subgroups generate the
symplectic group over a field, so the commutator subgroup is everything.

The hypothesis holds over every infinite field. It excludes the small-field exceptions: for
instance `Sp₂(𝔽₂) ≅ S₃`, `Sp₂(𝔽₃) = SL₂(𝔽₃)` and `Sp₄(𝔽₂) ≅ S₆` are not perfect.

## Main results

* `TauCeti.GLSymplecticFin.commutatorElement_diagonal_rootSubgroup`: the commutator of a torus
  element with a root element, over every commutative ring.
* `TauCeti.GLSymplecticFin.RootSubgroupIndex.exists_character_ne_one`: every root character is
  nontrivial on some torus element once there is a unit whose square is not one.
* `TauCeti.GLSymplecticFin.rootSubgroup_mem_commutator`: every root element is in the commutator
  subgroup.
* `TauCeti.GLSymplecticFin.commutator_eq_top`: the standard symplectic group is perfect.

## References

* R. Steinberg, *Lectures on Chevalley Groups* (1968), §4.
* J. S. Milne, *Algebraic Groups* (2017), §6d.

The argument follows the special-linear perfectness proof
`Matrix.SpecialLinearGroup.commutator_eq_top`, with the torus conjugation formula
`TauCeti.GLSymplecticFin.diagonal_mul_rootSubgroup_mul_inv` in place of diagonal conjugation of
transvections and `TauCeti.GLSymplecticFin.eq_top_of_root_subgroups` for generation.
-/

public section

open scoped commutatorElement

namespace TauCeti.GLSymplecticFin

universe u

variable {m : ℕ}

/-- The commutator of a diagonal torus element with a root element is the root element whose
parameter is scaled by the root character minus one. -/
theorem commutatorElement_diagonal_rootSubgroup {R : Type u} [CommRing R]
    (root : RootSubgroupIndex m) (t : Fin m → Rˣ) (c : Multiplicative R) :
    ⁅diagonal t, root.hom c⁆ =
      root.hom (Multiplicative.ofAdd (((root.character t : R) - 1) * c.toAdd)) := by
  rw [commutatorElement_def, diagonal_mul_rootSubgroup_mul_inv, ← map_inv, ← map_mul]
  congr 1
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_ofAdd, toAdd_inv]
  ring

namespace RootSubgroupIndex

/-- **Root characters are nontrivial.** If the coefficient monoid has a unit whose square is not
one, then every root character takes a value different from one on the diagonal torus. -/
theorem exists_character_ne_one {R : Type u} [CommMonoid R] (root : RootSubgroupIndex m)
    {u : Rˣ} (hu : u * u ≠ 1) : ∃ t : Fin m → Rˣ, root.character t ≠ 1 := by
  classical
  have hu₁ : u ≠ 1 := by
    rintro rfl
    exact hu (mul_one 1)
  cases root with
  | positiveLong i => exact ⟨Pi.mulSingle i u, by simpa using hu⟩
  | negativeLong i =>
    exact ⟨Pi.mulSingle i u, by
      rw [character_negativeLong, Pi.mulSingle_eq_same]
      exact inv_ne_one.mpr hu⟩
  | difference i j hij =>
    exact ⟨Pi.mulSingle i u, by simpa [Pi.mulSingle_apply, hij.symm] using hu₁⟩
  | positiveSum i j hij =>
    exact ⟨Pi.mulSingle i u, by simpa [Pi.mulSingle_apply, hij.ne'] using hu₁⟩
  | negativeSum i j hij =>
    exact ⟨Pi.mulSingle i u, by simpa [Pi.mulSingle_apply, hij.ne'] using hu₁⟩

end RootSubgroupIndex

variable {K : Type u} [Field K]

/-- Every root element of the standard symplectic group is in the commutator subgroup if the
field contains a nonzero element whose square is not one. -/
theorem rootSubgroup_mem_commutator {a : K} (ha : a ≠ 0) (hasq : a ^ 2 ≠ 1)
    (root : RootSubgroupIndex m) (c : Multiplicative K) :
    root.hom c ∈ commutator (GLSymplecticFin m K) := by
  obtain ⟨t, ht⟩ := root.exists_character_ne_one (u := Units.mk0 a ha) (by
    rw [Ne, Units.ext_iff]
    simpa [pow_two] using hasq)
  have hχ : (root.character t : K) - 1 ≠ 0 :=
    sub_ne_zero.mpr (by simpa only [Ne, Units.val_eq_one] using ht)
  have hc : root.hom c =
      ⁅diagonal t, root.hom (Multiplicative.ofAdd (c.toAdd / ((root.character t : K) - 1)))⁆ := by
    rw [commutatorElement_diagonal_rootSubgroup, toAdd_ofAdd, mul_div_cancel₀ _ hχ, ofAdd_toAdd]
  rw [hc]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- **The standard symplectic group is perfect** over a field with a nonzero element whose square
is not one, in every rank, including rank zero. -/
theorem commutator_eq_top {a : K} (ha : a ≠ 0) (hasq : a ^ 2 ≠ 1) :
    commutator (GLSymplecticFin m K) = ⊤ :=
  eq_top_of_root_subgroups _ (rootSubgroup_mem_commutator ha hasq)

end TauCeti.GLSymplecticFin
