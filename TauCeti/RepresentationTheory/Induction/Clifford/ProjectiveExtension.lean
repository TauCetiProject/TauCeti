/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Inertia
public import TauCeti.RepresentationTheory.ProjectiveRepresentation.Basic
import TauCeti.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Projective extension to the inertia group

An irreducible finite-dimensional representation of a normal subgroup over an algebraically
closed field extends to a normalized projective representation of its inertia group. The
extension agrees exactly with the original action on the normal subgroup, and its operators
implement conjugation on that subgroup.

Schur's lemma makes the discrepancy between two operators implementing the same conjugation
a nonzero scalar. Applying this to products gives the factor set. These operators are the
input to constructing the Clifford extension obstruction; the factor set here is on the
inertia group itself.

## References

I. M. Isaacs, *Character Theory of Finite Groups*, Chapters 6 and 11.
-/

public section

namespace TauCeti

open CategoryTheory _root_.Representation

universe u v

variable {k : Type u} {G : Type v} [Field k] [IsAlgClosed k] [Group G]
  {N : Subgroup G} [N.Normal] (A : FDRep k N) [Simple A]

/-- **Operators implementing conjugation on `N` form a projective representation.** Over an
algebraically closed field, a normalized family of automorphisms of `A`, indexed by the inertia
group, in which `ρ g` carries the action of `n` to the action of `g n g⁻¹`, is a projective
representation. -/
theorem exists_isProjectiveRep_of_apply_apply_conjNormal {ρ : inertia A → A ≃ₗ[k] A}
    (hone : ρ 1 = 1)
    (hinter : ∀ (g : inertia A) (n : N) (x : A),
      ρ g (A.ρ n x) = A.ρ (MulAut.conjNormal (g : G) n) (ρ g x)) :
    ∃ α : inertia A → inertia A → kˣ, IsProjectiveRep ρ α := by
  have hA := FDRep.isIrreducible_of_simple A
  have : Nontrivial A := hA.nontrivial
  -- By Schur's lemma `ρ g ∘ ρ h` and `ρ (g * h)` differ by a nonzero scalar, since both
  -- carry the action of `n` to the action of `(g * h) n (g * h)⁻¹`.
  have hmul (g h : inertia A) : ∃ c : kˣ, ∀ x,
      ρ g (ρ h x) = (c : k) • ρ (g * h) x := by
    refine IsIrreducible.exists_unit_smul_of_intertwines
      (σ := A.ρ.comp (MulAut.conjNormal ((g : G) * h)).toMonoidHom)
      ((ρ h).trans (ρ g)) (ρ (g * h)) (fun n x ↦ ?_) (hinter (g * h))
    have hc : MulAut.conjNormal ((g : G) * h) n =
        MulAut.conjNormal (g : G) (MulAut.conjNormal (h : G) n) := by
      simp [map_mul]
    rw [LinearEquiv.trans_apply, hinter, hinter, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, hc, LinearEquiv.trans_apply]
  choose α hα using hmul
  exact ⟨α, IsProjectiveRep.of_map_one_mul_apply hone hα⟩

/-- Every irreducible finite-dimensional representation of a normal subgroup over an
algebraically closed field extends projectively to its inertia group. The lift restricts
exactly to the original representation and implements the ambient conjugation action.
No finiteness assumption on `G`, and no restriction on the characteristic of `k`, is needed. -/
theorem exists_isProjectiveRep_inertia_restrict_eq :
    ∃ (ρ : inertia A → A ≃ₗ[k] A) (α : inertia A → inertia A → kˣ),
      IsProjectiveRep ρ α ∧
      (∀ (n : N) (x : A), ρ ⟨n, le_inertia A n.property⟩ x = A.ρ n x) ∧
      (∀ (g : inertia A) (n : N) (x : A),
        ρ g (A.ρ n x) = A.ρ (MulAut.conjNormal (g : G) n) (ρ g x)) := by
  classical
  let r : N →* (A ≃ₗ[k] A) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv k A).toMonoidHom.comp A.ρ.toHomUnits
  have hr (n : N) (x : A) : r n x = A.ρ n x := by simp [r]
  choose a ha using fun g : inertia A ↦ mem_inertia_iff_exists_linearEquiv.mp g.property
  let ρ (g : inertia A) : A ≃ₗ[k] A :=
    if h : (g : G) ∈ N then r ⟨g, h⟩ else a g
  have hres (n : N) (x : A) : ρ ⟨n, le_inertia A n.property⟩ x = A.ρ n x := by
    simp [ρ, hr, n.property]
  have hinter (g : inertia A) (n : N) (x : A) :
      ρ g (A.ρ n x) = A.ρ (MulAut.conjNormal (g : G) n) (ρ g x) := by
    dsimp only [ρ]
    split_ifs with h
    · rw [hr, hr]
      exact Representation.apply_conjNormal_coe A.ρ ⟨g, h⟩ n x
    · exact ha g n x
  have hone : ρ 1 = 1 := by
    simp only [ρ, Subgroup.coe_one, dite_eq_left N.one_mem]
    exact r.map_one
  obtain ⟨α, hα⟩ := exists_isProjectiveRep_of_apply_apply_conjNormal A hone hinter
  exact ⟨ρ, α, hα, hres, hinter⟩

end TauCeti
