/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs
public import TauCeti.Algebra.Colimit.DirectLimit

/-!
# Abelianization commutes with directed colimits of groups

For a directed system of groups `G i` with transition homomorphisms `f i j h : G i →* G j`, the
abelianizations `Abelianization (G i)` form a directed system along the induced homomorphisms
`Abelianization.map (f i j h)`. Its direct limit is the abelianization of the direct limit of the
`G i` (`TauCeti.DirectLimit.abelianizationEquiv`): both are the universal commutative group
receiving compatible homomorphisms from the `G i`.

Consequently the commutator subgroup of the direct limit is the union of the images of the
commutator subgroups of the components (`TauCeti.DirectLimit.commutator_eq_iSup_map`), and an
element coming from `G i` is a product of commutators in the direct limit exactly when its image
in some later `G j` is a product of commutators there
(`TauCeti.DirectLimit.Monoid.of_mem_commutator_iff`).

The main application is to algebraic `K₁`, the abelianization of the stable general linear
group `GL_∞(A)`, which is the direct limit of the groups `GL (Fin n) A`. By the results here,
`K₁(A)` is the direct limit of the abelianizations of the `GL (Fin n) A`
(`TauCeti.AlgebraicK1.directLimitAbelianizationEquiv`).

## Main declarations

* `TauCeti.DirectLimit.abelianizationEquiv`: the abelianization of a directed colimit of groups
  is the directed colimit of their abelianizations.
* `TauCeti.DirectLimit.Monoid.of_mem_commutator_iff`: membership in the commutator subgroup of a
  directed colimit of groups is decided at a finite stage.
* `TauCeti.DirectLimit.commutator_eq_iSup_map`: the commutator subgroup of a directed colimit of
  groups is the supremum of the images of the commutator subgroups of the components.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §3.
* C. Weibel, *The K-book*, Graduate Studies in Mathematics 145 (2013), Chapter III, §1.
-/

public section

noncomputable section

namespace TauCeti

namespace DirectLimit

open _root_.DirectLimit

variable {ι : Type*} [Preorder ι] (G : ι → Type*) [∀ i, Group (G i)]
  (f : ∀ i j, i ≤ j → G i →* G j) [DirectedSystem G (f · · ·)]

/-- The abelianizations of a directed system of groups form a directed system along the induced
homomorphisms. -/
instance directedSystem_abelianization :
    DirectedSystem (fun i ↦ Group.Abelianization (G i))
      fun i j h ↦ Group.Abelianization.map (f i j h) where
  map_self _ x := by
    obtain ⟨x, rfl⟩ := Group.Abelianization.surjective_of _ x
    rw [Group.Abelianization.map_of, DirectedSystem.map_self' f]
  map_map _ _ _ _ _ x := by
    obtain ⟨x, rfl⟩ := Group.Abelianization.surjective_of _ x
    rw [Group.Abelianization.map_of, Group.Abelianization.map_of, Group.Abelianization.map_of,
      DirectedSystem.map_map' f]

variable [IsDirectedOrder ι] [Nonempty ι]

/-- **Abelianization commutes with directed colimits.** The abelianization of the direct limit of
a directed system of groups is the direct limit of their abelianizations, the class of `x : G i`
going to the class of its abelianization. -/
def abelianizationEquiv :
    Group.Abelianization (DirectLimit G f) ≃*
      DirectLimit (fun i ↦ Group.Abelianization (G i))
        fun i j h ↦ Group.Abelianization.map (f i j h) :=
  MonoidHom.toMulEquiv
    (Group.Abelianization.lift <|
      Monoid.lift G f (fun i ↦ (Monoid.of _ _ i).comp Group.Abelianization.of) fun i j h x ↦ by
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← Group.Abelianization.map_of,
          Monoid.of_f])
    (Monoid.lift _ _ (fun i ↦ Group.Abelianization.map (Monoid.of G f i)) fun i j h x ↦ by
      rw [Group.Abelianization.map_map_apply]
      exact congrArg (Group.Abelianization.map · x) (MonoidHom.ext (Monoid.of_f h)))
    (by ext; simp) (by ext; simp)

/-- The abelianization of a direct limit sends the class of `x : G i` to the class in the direct
limit of the abelianization of `x`. -/
theorem abelianizationEquiv_of (i : ι) (x : G i) :
    abelianizationEquiv G f (Group.Abelianization.of (Monoid.of G f i x)) =
      Monoid.of _ _ i (Group.Abelianization.of x) := by
  simp [abelianizationEquiv]

/-- `abelianizationEquiv_of`, in terms of the classes `⟦⟨i, x⟩⟧` of the direct limits. -/
@[simp]
theorem abelianizationEquiv_mk (i : ι) (x : G i) :
    abelianizationEquiv G f (Group.Abelianization.of ⟦⟨i, x⟩⟧) =
      ⟦⟨i, Group.Abelianization.of x⟩⟧ := by
  simpa only [Monoid.of_apply] using abelianizationEquiv_of G f i x

/-- The inverse of `abelianizationEquiv` sends the class of `x : Group.Abelianization (G i)` to its
image along the canonical homomorphism `G i →* DirectLimit G f`. -/
theorem abelianizationEquiv_symm_of (i : ι) (x : Group.Abelianization (G i)) :
    (abelianizationEquiv G f).symm (Monoid.of _ _ i x) =
      Group.Abelianization.map (Monoid.of G f i) x := by
  simp [abelianizationEquiv]

/-- `abelianizationEquiv_symm_of`, in terms of the classes `⟦⟨i, x⟩⟧` of the direct limit. -/
@[simp]
theorem abelianizationEquiv_symm_mk (i : ι) (x : Group.Abelianization (G i)) :
    (abelianizationEquiv G f).symm ⟦⟨i, x⟩⟧ = Group.Abelianization.map (Monoid.of G f i) x := by
  simpa only [Monoid.of_apply] using abelianizationEquiv_symm_of G f i x

variable {G f}

/-- An element coming from `G i` is a product of commutators in the direct limit exactly when its
image in some later `G j` is a product of commutators there. -/
theorem Monoid.of_mem_commutator_iff {i : ι} {x : G i} :
    Monoid.of G f i x ∈ commutator (DirectLimit G f) ↔
      ∃ j, ∃ h : i ≤ j, f i j h x ∈ commutator (G j) := by
  rw [← Group.Abelianization.ker_of, MonoidHom.mem_ker,
    ← (abelianizationEquiv G f).map_eq_one_iff, abelianizationEquiv_of, Monoid.of_apply,
    exists_eq_one]
  simp only [Group.Abelianization.map_of, ← MonoidHom.mem_ker, Group.Abelianization.ker_of]

variable (G f) in
/-- The commutator subgroup of a direct limit of groups is the supremum of the images of the
commutator subgroups of the components. -/
theorem commutator_eq_iSup_map :
    commutator (DirectLimit G f) = ⨆ i, (commutator (G i)).map (Monoid.of G f i) := by
  refine le_antisymm (fun x hx ↦ ?_) (iSup_le fun i ↦ ?_)
  · obtain ⟨i, x, rfl⟩ := exists_eq_mk (f · · ·) x
    rw [← Monoid.of_apply] at hx ⊢
    obtain ⟨j, h, hx⟩ := Monoid.of_mem_commutator_iff.1 hx
    exact Subgroup.mem_iSup_of_mem j ⟨f i j h x, hx, Monoid.of_f h x⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact Monoid.of_mem_commutator_iff.2 ⟨i, le_rfl, by rwa [DirectedSystem.map_self' f]⟩

end DirectLimit

end TauCeti
