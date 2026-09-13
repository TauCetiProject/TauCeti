/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.Finiteness.Basic
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.Basic

/-!
# Joins of subcoalgebras

This file adds suprema to the lightweight `Subcoalgebra` structure. The supremum of a family
of subcoalgebras has underlying submodule the supremum of the underlying submodules; the
comultiplication is stable because each summand lies in the inverse image under `Δ` of the
larger submodule's tensor square. The universal property of the submodule supremum then gives
the same containment for the join.

## Main declarations

* `Subcoalgebra.instCompleteSemilatticeSup`: arbitrary suprema of subcoalgebras.
* `Subcoalgebra.iSup_toSubmodule`, `Subcoalgebra.mem_iSup`, `Subcoalgebra.mem_sSup`:
  characteristic API for arbitrary joins.
* `Subcoalgebra.mem_iSup_of_directed`, `Subcoalgebra.coe_iSup_of_directed`:
  a nonempty directed supremum is the union of its members.
* `Subcoalgebra.mem_sSup_of_directedOn`, `Subcoalgebra.coe_sSup_of_directedOn`:
  the corresponding set-indexed directed-union results.
* `Subcoalgebra.sup_toSubmodule`, `Subcoalgebra.mem_sup`: characteristic API for binary joins.
* `Subcoalgebra.iSup_finite`, `Subcoalgebra.sup_finite`, `Subcoalgebra.finset_sup_finite`:
  finite generation is preserved by finite joins.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v

variable {R : Type u} {C : Type v}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

namespace Subcoalgebra

/-- The join of two subcoalgebras has underlying submodule the join of the underlying
submodules. -/
instance instMax : Max (Subcoalgebra R C) where
  max D E :=
    { carrier := D.toSubmodule ⊔ E.toSubmodule
      comul_mem' := by
        change D.toSubmodule ⊔ E.toSubmodule ≤
          (LinearMap.range (TensorProduct.map _ _)).comap Coalgebra.comul
        exact sup_le
          (fun _ hc ↦ TensorProduct.range_mapIncl_mono le_sup_left le_sup_left (D.comul_mem hc))
          (fun _ hc ↦ TensorProduct.range_mapIncl_mono le_sup_right le_sup_right (E.comul_mem hc)) }

/-- The supremum of a set of subcoalgebras has underlying submodule the supremum of the
underlying submodules. -/
instance instSupSet : SupSet (Subcoalgebra R C) where
  sSup S :=
    { carrier := ⨆ D : S, (D : Subcoalgebra R C).toSubmodule
      comul_mem' := by
        change (⨆ D : S, (D : Subcoalgebra R C).toSubmodule) ≤
          (LinearMap.range (TensorProduct.map _ _)).comap Coalgebra.comul
        exact iSup_le fun D _ hc ↦
          TensorProduct.range_mapIncl_mono (le_iSup _ D) (le_iSup _ D) (D.1.comul_mem hc) }

/-- The underlying submodule of the join is the join of the underlying submodules. -/
@[simp]
theorem sup_toSubmodule (D E : Subcoalgebra R C) :
    (D ⊔ E).toSubmodule = D.toSubmodule ⊔ E.toSubmodule :=
  rfl

/-- Membership in the join of two subcoalgebras. -/
theorem mem_sup {D E : Subcoalgebra R C} {c : C} :
    c ∈ D ⊔ E ↔ ∃ d ∈ D, ∃ e ∈ E, d + e = c := by
  rw [← mem_toSubmodule, sup_toSubmodule, Submodule.mem_sup]
  rfl

/-- Subcoalgebras form a semilattice under the join whose carrier is the supremum of the
underlying submodules. -/
instance instSemilatticeSup : SemilatticeSup (Subcoalgebra R C) where
  sup D E := D ⊔ E
  le_sup_left := fun D E ↦
    show D.toSubmodule ≤ D.toSubmodule ⊔ E.toSubmodule from le_sup_left
  le_sup_right := fun D E ↦
    show E.toSubmodule ≤ D.toSubmodule ⊔ E.toSubmodule from le_sup_right
  sup_le := fun D E F hD hE ↦
    show D.toSubmodule ⊔ E.toSubmodule ≤ F.toSubmodule from sup_le hD hE

/-- The underlying submodule of a supremum of a set of subcoalgebras is the supremum of the
underlying submodules indexed by that set. -/
@[simp]
theorem sSup_toSubmodule (S : Set (Subcoalgebra R C)) :
    (sSup S).toSubmodule = ⨆ D : S, (D : Subcoalgebra R C).toSubmodule :=
  rfl

/-- Membership in the supremum of a set of subcoalgebras. -/
theorem mem_sSup {S : Set (Subcoalgebra R C)} {c : C} :
    c ∈ sSup S ↔
      ∃ f : S →₀ C, (∀ D : S, f D ∈ (D : Subcoalgebra R C)) ∧
        f.sum (fun _ x => x) = c := by
  rw [← mem_toSubmodule, sSup_toSubmodule]
  exact Submodule.mem_iSup_iff_exists_finsupp
    (fun D : S => (D : Subcoalgebra R C).toSubmodule) c

/-- The underlying submodule of a supremum of subcoalgebras is the supremum of the
underlying submodules. -/
@[simp]
theorem iSup_toSubmodule {ι : Sort*} (D : ι → Subcoalgebra R C) :
    (⨆ i, D i).toSubmodule = ⨆ i, (D i).toSubmodule := by
  rw [iSup, sSup_toSubmodule]
  ext c
  simp [Submodule.mem_iSup]

/-- Membership in the supremum of a family of subcoalgebras. -/
theorem mem_iSup {ι : Type*} {D : ι → Subcoalgebra R C} {c : C} :
    c ∈ ⨆ i, D i ↔
      ∃ f : ι →₀ C, (∀ i, f i ∈ D i) ∧ f.sum (fun _ x => x) = c := by
  rw [← mem_toSubmodule, iSup_toSubmodule]
  exact Submodule.mem_iSup_iff_exists_finsupp (fun i => (D i).toSubmodule) c

/-- Membership in a nonempty directed supremum of subcoalgebras reduces to membership in one
member of the family. -/
theorem mem_iSup_of_directed {ι : Type*} [Nonempty ι] {D : ι → Subcoalgebra R C}
    (hD : Directed (· ≤ ·) D) {c : C} :
    c ∈ ⨆ i, D i ↔ ∃ i, c ∈ D i := by
  rw [← mem_toSubmodule, iSup_toSubmodule]
  apply Submodule.mem_iSup_of_directed
  intro i j
  obtain ⟨k, hik, hjk⟩ := hD i j
  exact ⟨k, toSubmodule_le_toSubmodule.2 hik, toSubmodule_le_toSubmodule.2 hjk⟩

/-- The carrier of a nonempty directed supremum of subcoalgebras is the union of their
carriers. -/
theorem coe_iSup_of_directed {ι : Type*} [Nonempty ι] {D : ι → Subcoalgebra R C}
    (hD : Directed (· ≤ ·) D) : ((⨆ i, D i : Subcoalgebra R C) : Set C) = ⋃ i, (D i : Set C) := by
  ext c
  simp only [SetLike.mem_coe, Set.mem_iUnion, mem_iSup_of_directed hD]

/-- Membership in the supremum of a nonempty directed set of subcoalgebras reduces to
membership in one member of the set. -/
theorem mem_sSup_of_directedOn {S : Set (Subcoalgebra R C)} (hne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) {c : C} :
    c ∈ sSup S ↔ ∃ D ∈ S, c ∈ D := by
  have : Nonempty S := hne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, SetCoe.exists, exists_prop]

/-- The carrier of the supremum of a nonempty directed set of subcoalgebras is the union of
their carriers. -/
theorem coe_sSup_of_directedOn {S : Set (Subcoalgebra R C)} (hne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set C) = ⋃ D ∈ S, (D : Set C) := by
  ext c
  simp [mem_sSup_of_directedOn hne hS]

/-- Subcoalgebras have arbitrary suprema, computed on underlying submodules. -/
instance instCompleteSemilatticeSup : CompleteSemilatticeSup (Subcoalgebra R C) where
  sSup := sSup
  isLUB_sSup S := by
    refine ⟨fun D hD ↦ ?_, fun D hD ↦ ?_⟩
    · change D.toSubmodule ≤ ⨆ E : S, (E : Subcoalgebra R C).toSubmodule
      exact le_iSup (fun E : S ↦ (E : Subcoalgebra R C).toSubmodule) ⟨D, hD⟩
    · change (⨆ E : S, (E : Subcoalgebra R C).toSubmodule) ≤ D.toSubmodule
      exact iSup_le fun E ↦ hD E.2

/-- The join of finitely generated subcoalgebras is finitely generated as an `R`-module. -/
theorem sup_finite (D E : Subcoalgebra R C)
    [Module.Finite R D.toSubmodule] [Module.Finite R E.toSubmodule] :
    Module.Finite R (D ⊔ E).toSubmodule := by
  rw [sup_toSubmodule, Module.Finite.iff_fg]
  exact (Module.Finite.iff_fg.mp inferInstance).sup (Module.Finite.iff_fg.mp inferInstance)

/-- The join of finitely generated subcoalgebras is finitely generated as an `R`-module. -/
instance instFiniteSup (D E : Subcoalgebra R C)
    [Module.Finite R D.toSubmodule] [Module.Finite R E.toSubmodule] :
    Module.Finite R (D ⊔ E).toSubmodule :=
  sup_finite D E

variable {ι : Type*}

/-- The underlying submodule of a finite join of subcoalgebras is the finite join of the
underlying submodules. -/
@[simp]
theorem finset_sup_toSubmodule (s : Finset ι) (D : ι → Subcoalgebra R C) :
    (s.sup D).toSubmodule = s.sup fun i => (D i).toSubmodule := by
  classical
  induction s using Finset.induction_on with
  | empty => exact bot_toSubmodule
  | insert a s _ ih =>
      rw [Finset.sup_insert, sup_toSubmodule, ih, Finset.sup_insert]

/-- Membership in a finite join of subcoalgebras. -/
theorem mem_finset_sup {s : Finset ι} {D : ι → Subcoalgebra R C} {c : C} :
    c ∈ s.sup D ↔ ∃ μ : ∀ i, (D i).toSubmodule, (∑ i ∈ s, (μ i : C)) = c := by
  rw [← mem_toSubmodule, finset_sup_toSubmodule]
  simpa only [Finset.sup_eq_iSup] using
    (Submodule.mem_iSup_finset_iff_exists_sum (fun i => (D i).toSubmodule) c)

/-- A finite supremum of finitely generated subcoalgebras is finitely generated as an
`R`-module. -/
theorem iSup_finite [Finite ι] (D : ι → Subcoalgebra R C)
    (hD : ∀ i, Module.Finite R (D i).toSubmodule) :
    Module.Finite R (⨆ i, D i).toSubmodule := by
  rw [iSup_toSubmodule, Module.Finite.iff_fg]
  exact Submodule.fg_iSup (fun i ↦ (D i).toSubmodule)
    fun i ↦ Module.Finite.iff_fg.mp (hD i)

/-- A finite join of finitely generated subcoalgebras is finitely generated as an
`R`-module. -/
theorem finset_sup_finite (s : Finset ι) (D : ι → Subcoalgebra R C)
    (hD : ∀ i ∈ s, Module.Finite R (D i).toSubmodule) :
    Module.Finite R (s.sup D).toSubmodule := by
  classical
  rw [finset_sup_toSubmodule, Module.Finite.iff_fg]
  exact Submodule.fg_finset_sup s (fun i => (D i).toSubmodule)
    fun i hi => Module.Finite.iff_fg.mp (hD i hi)

end Subcoalgebra

end TauCeti
