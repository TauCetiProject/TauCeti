/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Orthogonal

/-!
# Polarizable pure Hodge structures are semisimple

A polarization splits off every rational Hodge substructure, so the lattice of rational Hodge
substructures of a polarizable pure Hodge structure is complemented. Over a finite-dimensional
rational space that lattice is also modular and satisfies the descending chain condition, and the
two properties together give the classical decomposition: a polarizable pure Hodge structure is
the direct sum of finitely many **simple** rational Hodge substructures — the atoms of the lattice
— pairwise independent and spanning.

The complement itself is the orthogonal complement
`TauCeti.Hodge.RationalHodgeSubstructure.orthogonal` for a polarizing form; the decomposition is
then an induction on the dimension of the rational subspace, splitting off one atom at a time.
Only *some* polarizing form is used, never a chosen one, so the statements are about
`TauCeti.Hodge.IsPolarizable` structures: this is the semisimplicity of the polarizable Hodge
structures, for which the choice of a form is not part of the object.

Following Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1.2, and Peters–Steenbrink,
*Mixed Hodge Structures*, §2.

## Main declarations

* `TauCeti.Hodge.RationalHodgeSubstructure.complementedLattice_of_isPolarizable`: the lattice of
  rational Hodge substructures of a polarizable pure Hodge structure is complemented.
* `TauCeti.Hodge.RationalHodgeSubstructure.exists_finset_isAtom_sup_eq`: every rational Hodge
  substructure is the supremum of a finite independent family of simple substructures.
* `TauCeti.Hodge.exists_finset_isAtom_sup_eq_top`: **semisimplicity**, a polarizable pure Hodge
  structure is the direct sum of finitely many simple rational Hodge substructures.
-/

public section

namespace TauCeti.Hodge

universe u v w

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ]
variable [AddCommGroup Vℚ] [Module ℚ Vℚ]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}
variable {n : ℤ} {hs : HodgeStructure hℂ n} [Module.Finite ℚ Vℚ]

namespace RationalHodgeSubstructure

/-- A polarization makes the lattice of rational Hodge substructures complemented: the orthogonal
complement for its form is a lattice complement. -/
theorem complementedLattice (P : Polarization hℂ hs) :
    ComplementedLattice (RationalHodgeSubstructure hℚ hs) :=
  ⟨fun W ↦ ⟨orthogonal P W, isCompl_orthogonal P W⟩⟩

/-- **Every rational Hodge substructure of a polarizable pure Hodge structure is a direct
summand**: the lattice of rational Hodge substructures is complemented. -/
theorem complementedLattice_of_isPolarizable (h : IsPolarizable hℂ hs) :
    ComplementedLattice (RationalHodgeSubstructure hℚ hs) :=
  let ⟨P⟩ := isPolarizable_iff_nonempty.1 h
  complementedLattice P

/-- The inductive step behind `exists_finset_isAtom_sup_eq`: a rational Hodge substructure of
dimension at most `d` is a finite independent supremum of simple substructures. Splitting off one
atom at a time is what the bound on the dimension controls. -/
private theorem exists_finset_isAtom_sup_eq_aux (P : Polarization hℂ hs) (d : ℕ) :
    ∀ W : RationalHodgeSubstructure hℚ hs, Module.finrank ℚ W.WQ ≤ d →
      ∃ s : Finset (RationalHodgeSubstructure hℚ hs),
        (∀ U ∈ s, IsAtom U) ∧ s.SupIndep id ∧ s.sup id = W := by
  classical
  induction d with
  | zero =>
    intro W hW
    have hWbot : W = ⊥ :=
      RationalHodgeSubstructure.ext
        (by rw [bot_WQ, ← Submodule.finrank_eq_zero]; exact Nat.le_zero.1 hW)
    exact ⟨∅, by simp, Finset.supIndep_empty _, by simp [hWbot]⟩
  | succ d ih =>
    intro W hW
    rcases eq_or_ne W ⊥ with rfl | hWne
    · exact ⟨∅, by simp, Finset.supIndep_empty _, by simp⟩
    obtain ⟨U, hU, hUW⟩ := exists_isAtom_le hWne
    set U' := orthogonal P U ⊓ W with hU'
    have hinf : U ⊓ U' = ⊥ :=
      le_bot_iff.1 <| calc
        U ⊓ U' ≤ U ⊓ orthogonal P U := inf_le_inf_left _ inf_le_left
        _ = ⊥ := (isCompl_orthogonal P U).disjoint.eq_bot
    have hsup : U ⊔ U' = W := by
      rw [hU', ← sup_inf_assoc_of_le _ hUW, (isCompl_orthogonal P U).codisjoint.eq_top,
        top_inf_eq]
    -- the dimensions of the two summands add up to the dimension of `W`
    have hadd : Module.finrank ℚ U.WQ + Module.finrank ℚ U'.WQ = Module.finrank ℚ W.WQ := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq U.WQ U'.WQ
      rw [← sup_WQ, ← inf_WQ, hsup, hinf, bot_WQ, finrank_bot] at h
      omega
    have hUpos : Module.finrank ℚ U.WQ ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      exact fun h ↦ hU.1 (RationalHodgeSubstructure.ext (by rw [h, bot_WQ]))
    obtain ⟨s, hatom, hindep, hssup⟩ := ih U' (by omega)
    refine ⟨insert U s, ?_, hindep.insert ?_, ?_⟩
    · exact fun V hV ↦ (Finset.mem_insert.1 hV).elim (fun h ↦ h ▸ hU) (hatom V)
    · rw [hssup]
      exact disjoint_iff.2 hinf
    · rw [Finset.sup_insert, hssup, id_eq, hsup]

/-- **Every rational Hodge substructure of a polarized pure Hodge structure is a finite direct sum
of simple substructures**: it is the supremum of a finite family of atoms of the lattice of
rational Hodge substructures, pairwise independent. -/
theorem exists_finset_isAtom_sup_eq (P : Polarization hℂ hs) (W : RationalHodgeSubstructure hℚ hs) :
    ∃ s : Finset (RationalHodgeSubstructure hℚ hs),
      (∀ U ∈ s, IsAtom U) ∧ s.SupIndep id ∧ s.sup id = W :=
  exists_finset_isAtom_sup_eq_aux P _ W le_rfl

end RationalHodgeSubstructure

/-- **Semisimplicity of polarizable pure Hodge structures.** A polarizable pure Hodge structure on
a finite-dimensional rational space is the direct sum of finitely many simple rational Hodge
substructures: there is a finite independent family of atoms of the lattice of rational Hodge
substructures whose supremum is everything. -/
theorem exists_finset_isAtom_sup_eq_top (hℚ : IsBaseChange ℚ ιℚ) (h : IsPolarizable hℂ hs) :
    ∃ s : Finset (RationalHodgeSubstructure hℚ hs),
      (∀ U ∈ s, IsAtom U) ∧ s.SupIndep id ∧ s.sup id = ⊤ := by
  obtain ⟨P⟩ := isPolarizable_iff_nonempty.1 h
  exact RationalHodgeSubstructure.exists_finset_isAtom_sup_eq P ⊤

/-- **Semisimplicity, read on the rational space.** The rational subspaces of the simple
substructures produced by `exists_finset_isAtom_sup_eq_top` are independent and span. -/
theorem exists_finset_isAtom_sup_WQ_eq_top (hℚ : IsBaseChange ℚ ιℚ) (h : IsPolarizable hℂ hs) :
    ∃ s : Finset (RationalHodgeSubstructure hℚ hs),
      (∀ U ∈ s, IsAtom U) ∧ s.SupIndep id ∧ (s.sup fun U ↦ U.WQ) = ⊤ := by
  obtain ⟨s, hatom, hindep, hsup⟩ := exists_finset_isAtom_sup_eq_top hℚ h
  refine ⟨s, hatom, hindep, ?_⟩
  rw [← RationalHodgeSubstructure.finsetSup_WQ s, hsup, RationalHodgeSubstructure.top_WQ]

end TauCeti.Hodge
