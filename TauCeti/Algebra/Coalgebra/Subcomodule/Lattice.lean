/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.Finiteness.Basic
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic

/-!
# Joins of subcomodules

This file adds suprema to the lightweight `Subcomodule` structure. The supremum of a family
of subcomodules has underlying submodule the supremum of the underlying submodules; the
coaction is stable because each summand lies in the inverse image under `ρ` of the tensor
product of the larger submodule with the coalgebra. The universal property of the submodule
supremum then gives the same containment for the join.

## Main declarations

* `Subcomodule.instCompleteSemilatticeSup`: arbitrary suprema of subcomodules.
* `Subcomodule.iSup_toSubmodule`, `Subcomodule.mem_iSup`, `Subcomodule.mem_sSup`:
  characteristic API for arbitrary joins.
* `Subcomodule.coe_iSup_of_directed`, `Subcomodule.mem_iSup_of_directed`:
  a nonempty directed join has carrier equal to the union of the carriers.
* `Subcomodule.sup_toSubmodule`, `Subcomodule.mem_sup`: characteristic API for binary joins.
* `Subcomodule.iSup_finite`, `Subcomodule.sup_finite`, `Subcomodule.finset_sup_finite`:
  finite generation is preserved by finite joins.
* `Subcomodule.map_sup`, `Subcomodule.map_iSup`: images preserve joins.

## References

The lattice construction is adapted from `TauCeti.Algebra.Coalgebra.Subcoalgebra.Lattice`,
and the image-join lemmas follow the corresponding map API in
`TauCeti.Algebra.Coalgebra.Subcoalgebra.Map`.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

namespace Subcomodule

/-- The join of two subcomodules has underlying submodule the join of the underlying
submodules. -/
instance instMax : Max (Subcomodule R C M) where
  max N P :=
    { carrier := N.toSubmodule ⊔ P.toSubmodule
      coact_mem' := by
        change N.toSubmodule ⊔ P.toSubmodule ≤
          (LinearMap.range (TensorProduct.map _ _)).comap (Comodule.coact (C := C))
        refine sup_le (fun _ hm ↦ ?_) (fun _ hm ↦ ?_)
        · exact TensorProduct.range_map_mono
            (by simp only [Submodule.range_subtype]; exact le_sup_left)
            le_rfl (N.coact_mem hm)
        · exact TensorProduct.range_map_mono
            (by simp only [Submodule.range_subtype]; exact le_sup_right)
            le_rfl (P.coact_mem hm) }

/-- The supremum of a set of subcomodules has underlying submodule the supremum of the
underlying submodules. -/
instance instSupSet : SupSet (Subcomodule R C M) where
  sSup S :=
    { carrier := ⨆ N : S, (N : Subcomodule R C M).toSubmodule
      coact_mem' := by
        change (⨆ N : S, (N : Subcomodule R C M).toSubmodule) ≤
          (LinearMap.range (TensorProduct.map _ _)).comap (Comodule.coact (C := C))
        refine iSup_le fun N _ hm ↦ ?_
        exact TensorProduct.range_map_mono
          (by
            simp only [Submodule.range_subtype]
            exact le_iSup (fun N : S ↦ (N : Subcomodule R C M).toSubmodule) N)
          le_rfl (N.1.coact_mem hm) }

/-- The underlying submodule of the join is the join of the underlying submodules. -/
@[simp]
theorem sup_toSubmodule (N P : Subcomodule R C M) :
    (N ⊔ P).toSubmodule = N.toSubmodule ⊔ P.toSubmodule :=
  rfl

/-- Membership in the join of two subcomodules. -/
theorem mem_sup {N P : Subcomodule R C M} {m : M} :
    m ∈ N ⊔ P ↔ ∃ n ∈ N, ∃ p ∈ P, n + p = m := by
  rw [← mem_toSubmodule, sup_toSubmodule, Submodule.mem_sup]
  rfl

/-- Subcomodules form a semilattice under the join whose carrier is the supremum of the
underlying submodules. -/
instance instSemilatticeSup : SemilatticeSup (Subcomodule R C M) where
  sup D E := D ⊔ E
  le_sup_left := fun N P ↦
    show N.toSubmodule ≤ N.toSubmodule ⊔ P.toSubmodule from le_sup_left
  le_sup_right := fun N P ↦
    show P.toSubmodule ≤ N.toSubmodule ⊔ P.toSubmodule from le_sup_right
  sup_le := fun N P Q hN hP ↦
    show N.toSubmodule ⊔ P.toSubmodule ≤ Q.toSubmodule from sup_le hN hP

/-- The underlying submodule of a supremum of a set of subcomodules is the supremum of the
underlying submodules indexed by that set. -/
@[simp]
theorem sSup_toSubmodule (S : Set (Subcomodule R C M)) :
    (sSup S).toSubmodule = ⨆ N : S, (N : Subcomodule R C M).toSubmodule :=
  rfl

/-- Membership in the supremum of a set of subcomodules. -/
theorem mem_sSup {S : Set (Subcomodule R C M)} {m : M} :
    m ∈ sSup S ↔
      ∃ f : S →₀ M, (∀ N : S, f N ∈ (N : Subcomodule R C M)) ∧
        f.sum (fun _ x => x) = m := by
  rw [← mem_toSubmodule, sSup_toSubmodule]
  exact Submodule.mem_iSup_iff_exists_finsupp
    (fun N : S => (N : Subcomodule R C M).toSubmodule) m

/-- The underlying submodule of a supremum of subcomodules is the supremum of the
underlying submodules. -/
@[simp]
theorem iSup_toSubmodule {ι : Sort*} (N : ι → Subcomodule R C M) :
    (⨆ i, N i).toSubmodule = ⨆ i, (N i).toSubmodule := by
  rw [iSup, sSup_toSubmodule]
  ext m
  simp [Submodule.mem_iSup]

/-- Membership in the supremum of a family of subcomodules. -/
theorem mem_iSup {ι : Type*} {N : ι → Subcomodule R C M} {m : M} :
    m ∈ ⨆ i, N i ↔
      ∃ f : ι →₀ M, (∀ i, f i ∈ N i) ∧ f.sum (fun _ x => x) = m := by
  rw [← mem_toSubmodule, iSup_toSubmodule]
  exact Submodule.mem_iSup_iff_exists_finsupp (fun i => (N i).toSubmodule) m

/-- Subcomodules have arbitrary suprema, computed on underlying submodules. -/
instance instCompleteSemilatticeSup : CompleteSemilatticeSup (Subcomodule R C M) where
  sSup := sSup
  isLUB_sSup S := by
    refine ⟨fun N hN ↦ ?_, fun N hN ↦ ?_⟩
    · change N.toSubmodule ≤ ⨆ P : S, (P : Subcomodule R C M).toSubmodule
      exact le_iSup (fun P : S ↦ (P : Subcomodule R C M).toSubmodule) ⟨N, hN⟩
    · change (⨆ P : S, (P : Subcomodule R C M).toSubmodule) ≤ N.toSubmodule
      exact iSup_le fun P ↦ hN P.2

/-- The carrier of a nonempty directed supremum of subcomodules is the union of their carriers. -/
@[simp]
theorem coe_iSup_of_directed {iota : Type*} [Nonempty iota]
    (N : iota → Subcomodule R C M) (hN : Directed (· ≤ ·) N) :
    ((↑(⨆ i, N i) : Set M)) = ⋃ i, (N i : Set M) := by
  have hN' : Directed (· ≤ ·) (fun i ↦ (N i).toSubmodule) := fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := hN i j
    exact ⟨k, toSubmodule_le_toSubmodule.2 hik, toSubmodule_le_toSubmodule.2 hjk⟩
  ext m
  rw [SetLike.mem_coe, ← mem_toSubmodule, iSup_toSubmodule, ← SetLike.mem_coe,
    Submodule.coe_iSup_of_directed _ hN']
  simp only [Set.mem_iUnion, SetLike.mem_coe, mem_toSubmodule]

/-- An element belongs to a nonempty directed supremum of subcomodules exactly when it belongs to
one member of the family. -/
@[simp]
theorem mem_iSup_of_directed {iota : Type*} [Nonempty iota]
    (N : iota → Subcomodule R C M) (hN : Directed (· ≤ ·) N) {m : M} :
    m ∈ ⨆ i, N i ↔ ∃ i, m ∈ N i := by
  rw [← SetLike.mem_coe, coe_iSup_of_directed N hN, Set.mem_iUnion]
  simp only [SetLike.mem_coe]

/-- The carrier of the supremum of a nonempty directed set of subcomodules is the union of its
carriers. -/
@[simp]
theorem coe_sSup_of_directedOn {S : Set (Subcomodule R C M)} (hS : S.Nonempty)
    (hdir : DirectedOn (· ≤ ·) S) :
    ((sSup S : Subcomodule R C M) : Set M) = ⋃ N : S, (N.1 : Set M) := by
  let : Nonempty S := hS.to_subtype
  rw [sSup_eq_iSup']
  exact coe_iSup_of_directed (fun N : S ↦ N.1) hdir.directed_val

/-- Membership in the supremum of a nonempty directed set of subcomodules reduces to membership
in one member of the set. -/
@[simp]
theorem mem_sSup_of_directedOn {S : Set (Subcomodule R C M)} (hS : S.Nonempty)
    (hdir : DirectedOn (· ≤ ·) S) {m : M} :
    m ∈ sSup S ↔ ∃ N ∈ S, m ∈ N := by
  let : Nonempty S := hS.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed (fun N : S ↦ N.1) hdir.directed_val,
    SetCoe.exists, exists_prop]

/-- The join of finitely generated subcomodules is finitely generated as an `R`-module. -/
theorem sup_finite (N P : Subcomodule R C M)
    [Module.Finite R N.toSubmodule] [Module.Finite R P.toSubmodule] :
    Module.Finite R (N ⊔ P).toSubmodule := by
  rw [sup_toSubmodule, Module.Finite.iff_fg]
  exact (Module.Finite.iff_fg.mp inferInstance).sup (Module.Finite.iff_fg.mp inferInstance)

/-- The join of finitely generated subcomodules is finitely generated as an `R`-module. -/
instance instFiniteSup (N P : Subcomodule R C M)
    [Module.Finite R N.toSubmodule] [Module.Finite R P.toSubmodule] :
    Module.Finite R (N ⊔ P).toSubmodule :=
  sup_finite N P

variable {ι : Type*}

/-- The underlying submodule of a finite join of subcomodules is the finite join of the
underlying submodules. -/
@[simp]
theorem finset_sup_toSubmodule (s : Finset ι) (N : ι → Subcomodule R C M) :
    (s.sup N).toSubmodule = s.sup fun i => (N i).toSubmodule := by
  classical
  induction s using Finset.induction_on with
  | empty => exact bot_toSubmodule
  | insert a s _ ih =>
      rw [Finset.sup_insert, sup_toSubmodule, ih, Finset.sup_insert]

/-- Membership in a finite join of subcomodules. -/
theorem mem_finset_sup {s : Finset ι} {N : ι → Subcomodule R C M} {m : M} :
    m ∈ s.sup N ↔ ∃ μ : ∀ i, (N i).toSubmodule, (∑ i ∈ s, (μ i : M)) = m := by
  rw [← mem_toSubmodule, finset_sup_toSubmodule]
  simpa only [Finset.sup_eq_iSup] using
    (Submodule.mem_iSup_finset_iff_exists_sum (fun i => (N i).toSubmodule) m)

/-- A finite supremum of finitely generated subcomodules is finitely generated as an
`R`-module. -/
theorem iSup_finite {ι : Sort*} [Finite ι] (N : ι → Subcomodule R C M)
    (hN : ∀ i, Module.Finite R (N i).toSubmodule) :
    Module.Finite R (⨆ i, N i).toSubmodule := by
  rw [iSup_toSubmodule, Module.Finite.iff_fg]
  exact Submodule.fg_iSup (fun i => (N i).toSubmodule)
    fun i => Module.Finite.iff_fg.mp (hN i)

/-- A finite join of finitely generated subcomodules is finitely generated as an
`R`-module. -/
theorem finset_sup_finite (s : Finset ι) (N : ι → Subcomodule R C M)
    (hN : ∀ i ∈ s, Module.Finite R (N i).toSubmodule) :
    Module.Finite R (s.sup N).toSubmodule := by
  classical
  rw [finset_sup_toSubmodule, Module.Finite.iff_fg]
  exact Submodule.fg_finset_sup s (fun i => (N i).toSubmodule)
    fun i hi => Module.Finite.iff_fg.mp (hN i hi)

section Map

variable {M' : Type*} [AddCommMonoid M'] [Module R M'] [Comodule R C M']

/-- The image of a binary join is the binary join of the images. -/
@[simp]
theorem map_sup (f : Comodule.Hom R C M M') (N P : Subcomodule R C M) :
    (N ⊔ P).map f = N.map f ⊔ P.map f := by
  ext m
  rw [← mem_toSubmodule, map_toSubmodule, sup_toSubmodule, Submodule.map_sup,
    ← map_toSubmodule N f, ← map_toSubmodule P f, ← sup_toSubmodule, mem_toSubmodule]

/-- The image of a supremum is the supremum of the images. -/
@[simp]
theorem map_iSup {ι : Sort*} (f : Comodule.Hom R C M M') (N : ι → Subcomodule R C M) :
    (⨆ i, N i).map f = ⨆ i, (N i).map f := by
  ext m
  rw [← mem_toSubmodule, map_toSubmodule, iSup_toSubmodule, Submodule.map_iSup]
  simp_rw [← map_toSubmodule (f := f)]
  rw [← iSup_toSubmodule, mem_toSubmodule]

/-- The image of a finite join is the finite join of the images. -/
@[simp]
theorem map_finset_sup (s : Finset ι) (f : Comodule.Hom R C M M') (N : ι → Subcomodule R C M) :
    (s.sup N).map f = s.sup fun i => (N i).map f := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sup_empty, Finset.sup_empty, map_bot]
  | cons i s hi ih => rw [Finset.sup_cons, Finset.sup_cons, map_sup, ih]

end Map

end Subcomodule

end TauCeti
