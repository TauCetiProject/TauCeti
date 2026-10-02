/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Inertia
public import TauCeti.RepresentationTheory.ProjectiveRepresentation.Basic
import TauCeti.RepresentationTheory.AsModule
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

/-- Two invertible operators implementing the same conjugation differ by a unit scalar. -/
private theorem exists_unit_smul_of_intertwines_conj (g : G) (a b : A ≃ₗ[k] A)
    (ha : ∀ n x, a (A.ρ n x) = A.ρ (MulAut.conjNormal g n) (a x))
    (hb : ∀ n x, b (A.ρ n x) = A.ρ (MulAut.conjNormal g n) (b x)) :
    ∃ c : kˣ, ∀ x, a x = (c : k) • b x := by
  have := FDRep.isIrreducible_of_simple A
  have : Nontrivial A := IsIrreducible.nontrivial (FDRep.isIrreducible_of_simple A)
  let f : IntertwiningMap A.ρ A.ρ :=
    { toLinearMap := (a.trans b.symm).toLinearMap
      isIntertwining' n := by
        ext x
        apply b.injective
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
          LinearEquiv.apply_symm_apply]
        rw [ha, hb]
        simp }
  obtain ⟨c, hc⟩ :=
    (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := A.ρ)).surjective f
  have hf (x : A) : b.symm (a x) = c • x := by
    have hx := DFunLike.congr_fun hc x
    simpa [f, IntertwiningMap.algebraMap_apply] using hx.symm
  have hne : c ≠ 0 := by
    intro hzero
    obtain ⟨x, hx⟩ := exists_ne (0 : A)
    have h := hf x
    rw [hzero, zero_smul] at h
    exact hx ((a.trans b.symm).injective (by simpa using h))
  refine ⟨Units.mk0 c hne, fun x ↦ ?_⟩
  simpa using congrArg b (hf x)

omit [IsAlgClosed k] [Simple A] in
/-- An element of the inertia group is implemented by an invertible linear operator. -/
private theorem exists_intertwines_conj (g : inertia A) :
    ∃ a : A ≃ₗ[k] A, ∀ n x,
      a (A.ρ n x) = A.ρ (MulAut.conjNormal (g : G) n) (a x) := by
  obtain ⟨e⟩ := (nonempty_fdRepIso_iff.mp (mem_inertia_iff.mp g.property))
  have heq : (conjNormalFDRep (g : G) A).ρ =
      A.ρ.comp (MulAut.conjNormal (g : G)⁻¹).toMonoidHom :=
    MonoidHom.ext (conjNormalFDRep_ρ (g : G) A)
  rw [heq] at e
  refine ⟨e.toLinearEquiv, fun n x ↦ ?_⟩
  have h := IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap
    (MulAut.conjNormal (g : G) n) x
  -- The intertwining-map coercion and `FDRep.ρ` use the commutative-ring semiring
  -- instance. Expose evaluation before simplifying the inverse conjugation.
  change e.toLinearEquiv
    (A.ρ (MulAut.conjNormal (g : G)⁻¹ (MulAut.conjNormal (g : G) n)) x) =
      A.ρ (MulAut.conjNormal (g : G) n) (e.toLinearEquiv x) at h
  convert h using 1
  simp only [map_inv, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  rfl

/-- Every irreducible finite-dimensional representation of a normal subgroup over an
algebraically closed field extends projectively to its inertia group. The lift restricts
exactly to the original representation and implements the ambient conjugation action.
No finiteness or characteristic restriction on the group is needed. -/
theorem exists_isProjectiveRep_inertia :
    ∃ (ρ : inertia A → A ≃ₗ[k] A) (α : inertia A → inertia A → kˣ),
      IsProjectiveRep ρ α ∧
      (∀ (n : N) (x : A), ρ ⟨n, le_inertia A n.property⟩ x = A.ρ n x) ∧
      (∀ (g : inertia A) (n : N) (x : A),
        ρ g (A.ρ n x) = A.ρ (MulAut.conjNormal (g : G) n) (ρ g x)) := by
  classical
  have := FDRep.isIrreducible_of_simple A
  have : Nontrivial A := IsIrreducible.nontrivial (FDRep.isIrreducible_of_simple A)
  let r : N →* (A ≃ₗ[k] A) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv k A).toMonoidHom.comp A.ρ.toHomUnits
  have hr (n : N) (x : A) : r n x = A.ρ n x := rfl
  choose a ha using exists_intertwines_conj A
  let ρ (g : inertia A) : A ≃ₗ[k] A :=
    if h : (g : G) ∈ N then r ⟨g, h⟩ else a g
  have hres (n : N) (x : A) : ρ ⟨n, le_inertia A n.property⟩ x = A.ρ n x := by
    simp [ρ, hr, n.property]
  have hinter (g : inertia A) (n : N) (x : A) :
      ρ g (A.ρ n x) = A.ρ (MulAut.conjNormal (g : G) n) (ρ g x) := by
    dsimp only [ρ]
    split_ifs with h
    · rw [hr, hr, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      apply congrArg (fun n : N ↦ A.ρ n x)
      apply Subtype.ext
      simp [mul_assoc]
    · exact ha g n x
  have hone : ρ 1 = 1 := by
    simp only [ρ, Subgroup.coe_one, dite_eq_left N.one_mem]
    exact r.map_one
  have hmul (g h : inertia A) : ∃ c : kˣ, ∀ x,
      ρ g (ρ h x) = (c : k) • ρ (g * h) x := by
    apply exists_unit_smul_of_intertwines_conj A ((g : G) * h)
      ((ρ h).trans (ρ g)) (ρ (g * h))
    · intro n x
      simp only [LinearEquiv.trans_apply]
      rw [hinter, hinter]
      congr 2
      exact (congrArg (fun f : MulAut N ↦ f n) (MulAut.conjNormal.map_mul (g : G) h)).symm
    · exact hinter (g * h)
  choose α hα using hmul
  exact ⟨ρ, α, IsProjectiveRep.of_map_one_mul_apply hone hα, hres, hinter⟩

end TauCeti
