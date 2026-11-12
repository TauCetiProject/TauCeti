/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.CosetCover
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Nakayama

/-!
# Modules over a local ring with infinite residue field are not finite unions of submodules

A vector space over an infinite field is not a finite union of proper subspaces
(`Submodule.exists_forall_notMem_of_forall_ne_top`). This file proves the same for any module
over a local ring whose residue field is infinite. This is the general-position input for
choosing elements of a module that avoid finitely many proper submodules at once, for instance
elements whose images form bases of finitely many fibres simultaneously.

The proof reduces to the field case. Pick `yᵢ ∉ pᵢ` and let `L` be the finitely generated
submodule they span. By Nakayama's lemma, each `pᵢ ∩ L + 𝔪 L` is still a proper submodule of `L`,
so its image in the vector space `L / 𝔪 L` over the residue field is a proper subspace. An element
of `L` whose image avoids these finitely many subspaces avoids every `pᵢ`.

## Main results

* `Submodule.exists_forall_notMem_of_forall_ne_top_of_isLocalRing`: over a local ring with
  infinite residue field, a module is not the union of finitely many proper submodules.
* `AddMonoidHom.exists_forall_apply_notMem_of_span_eq_top`: an additive subgroup spanning a
  vector space in characteristic zero contains one vector outside a finite family of proper
  subspaces. This supplies a transverse direction in an integral lattice.

The latter specialization of B. H. Neumann's coset-cover lemma is adapted from
`Mei/Algebra/Module/Submodule/Union.lean` in [yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `9cf969cdee9748087aae45dbf4888a130890655c` (Apache 2.0).
Original author and copyright: Codex and Mei contributors, respectively.
-/

public section

open IsLocalRing

namespace Submodule

variable {ι R M : Type*} [CommRing R] [IsLocalRing R] [Infinite (ResidueField R)]
  [AddCommGroup M] [Module R M] [Finite ι]

/-- **A module over a local ring with infinite residue field is not a finite union of proper
submodules.** If `pᵢ` are finitely many proper submodules of `M`, some element of `M` lies in
none of them. -/
theorem exists_forall_notMem_of_forall_ne_top_of_isLocalRing (p : ι → Submodule R M)
    (h : ∀ i, p i ≠ ⊤) : ∃ x, ∀ i, x ∉ p i := by
  -- the finitely generated submodule `L` spanned by chosen elements `yᵢ ∉ pᵢ`
  choose y hy using fun i ↦ (IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr (h i)))
  set L := span R (Set.range y)
  have hL : (⊤ : Submodule R L).FG := by
    have : Module.Finite R L := Module.Finite.span_of_finite R (Set.finite_range y)
    exact Module.finite_def.mp this
  -- the image of `pᵢ ∩ L` in the vector space `L / 𝔪 L` over the residue field
  set I := maximalIdeal R
  let _ : Field (R ⧸ I) := Ideal.Quotient.field I
  set N := I • (⊤ : Submodule R L)
  have : Infinite (R ⧸ I) := ‹Infinite (ResidueField R)›
  let q (i : ι) : Submodule (R ⧸ I) (L ⧸ N) := span (R ⧸ I) (N.mkQ '' (p i).comap L.subtype)
  have hq (i : ι) : q i ≠ ⊤ := by
    intro hqi
    -- otherwise `pᵢ ∩ L + 𝔪 L = L`, so `yᵢ ∈ pᵢ` by Nakayama's lemma
    have hspan : (q i).restrictScalars R = span R (N.mkQ '' (p i).comap L.subtype) :=
      restrictScalars_span R (R ⧸ I) Ideal.Quotient.mk_surjective _
    rw [hqi, restrictScalars_top, span_image, span_eq] at hspan
    have hle : ⊤ ≤ (p i).comap L.subtype ⊔ I • ⊤ := by
      rw [sup_comm, ← comap_map_mkQ, ← hspan, comap_top]
    have hjac : I ≤ Ring.jacobson R := (ringJacobson_eq_maximalIdeal R).ge
    exact (hy i).2 (Submodule.le_of_le_smul_of_le_jacobson hL hjac hle
      (mem_top : (⟨y i, subset_span ⟨i, rfl⟩⟩ : L) ∈ ⊤))
  obtain ⟨x, hx⟩ := exists_forall_notMem_of_forall_ne_top q hq
  obtain ⟨x, rfl⟩ := N.mkQ_surjective x
  exact ⟨x, fun i hxi ↦ hx i (subset_span ⟨x, hxi, rfl⟩)⟩

end Submodule

noncomputable section

namespace AddMonoidHom

variable {N K V ι : Type*} [AddCommGroup N] [DivisionRing K] [CharZero K]
  [AddCommGroup V] [Module K V]

/-- A spanning additive subgroup of a vector space in characteristic zero contains
a vector outside any finite family of proper subspaces. The additive homomorphism
need not be injective, and the vector space need not be finite-dimensional. -/
theorem exists_forall_apply_notMem_of_span_eq_top (i : N →+ V)
    (hi : Submodule.span K (Set.range i) = ⊤) [Finite ι]
    (p : ι → Submodule K V) (hp : ∀ j, p j ≠ ⊤) :
    ∃ n : N, ∀ j, i n ∉ p j := by
  classical
  let := Fintype.ofFinite ι
  let q (j : ι) : Submodule ℤ N :=
    ((p j).restrictScalars ℤ).comap i.toIntLinearMap
  by_contra! hcover
  have hq : ⋃ j ∈ Finset.univ, (q j : Set N) = Set.univ := by
    ext n
    simpa [q] using hcover n
  obtain ⟨j, _, hj⟩ := Submodule.exists_finiteIndex_of_cover hq
  apply hp j
  apply top_unique
  rw [← hi, Submodule.span_le]
  rintro _ ⟨n, rfl⟩
  obtain ⟨a, ha, _, han⟩ :=
    (q j).toAddSubgroup.exists_nsmul_mem_of_index_ne_zero hj.index_ne_zero n
  have ham : (a : K) • i n ∈ p j := by
    simpa only [q, AddSubgroup.mem_carrier, Submodule.mem_toAddSubgroup,
      Submodule.mem_comap, Submodule.restrictScalars_mem,
      AddMonoidHom.coe_toIntLinearMap, map_nsmul, Nat.cast_smul_eq_nsmul] using han
  exact ((p j).smul_mem_iff (Nat.cast_ne_zero.mpr ha.ne')).mp ham

end AddMonoidHom
