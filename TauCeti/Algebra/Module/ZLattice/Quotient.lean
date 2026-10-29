/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.GroupTheory.IndexNSmul
public import TauCeti.Algebra.Module.Submodule.OrbitRelQuotient

/-!
# Quotients of a full lattice

Let `L : Submodule ℤ E` be a full lattice, `IsZLattice ℝ L`, in a finite-dimensional real normed
space `E`. The orbit space `AddAction.orbitRel.Quotient L E` of translation by `L`, with the
additive group structure of `E ⧸ L` (`Submodule.orbitRelQuotientAddEquiv`), is the image of a
compact fundamental parallelepiped of the lattice, so it is compact. For a complex vector space
`E` this is the compactness of the complex torus `E / L`.

For `c : ℕ`, the lattice `cL` is `(c : ℝ) • L`, read in `L` through `Submodule.submoduleOf`. The
quotient `L / cL` has `c ^ n` elements when `L` has rank `n`, so it is finite for `c ≠ 0`.

## Main results

* `Submodule.instCompactSpaceOrbitRelQuotient`: the quotient by a full lattice is compact.
* `ZLattice.card_quotient_smul_submoduleOf`: `L / cL` has `c ^ n` elements for a full lattice
  `L` of rank `n`; it is finite for `c ≠ 0`.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 1, Section 1.1.
-/

public section

/-- The quotient of a finite-dimensional real normed space by a full lattice is compact: it is the
image of a compact fundamental parallelepiped of the lattice. -/
instance Submodule.instCompactSpaceOrbitRelQuotient {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] : CompactSpace (AddAction.orbitRel.Quotient L E) := by
  refine isCompact_univ_iff.1 ?_
  rw [← Set.range_eq_univ.2 _root_.Quotient.mk_surjective]
  refine IsZLattice.isCompact_range_of_periodic L _ continuous_quotient_mk' fun z w hw ↦ ?_
  rw [Submodule.orbitRelQuotient_mk_add, (L.orbitRelQuotient_mk_eq_zero_iff).2 hw, add_zero]

/-! ### The quotient `L / cL` -/

open Module Submodule
open scoped Pointwise

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : Submodule ℤ E}

/-- A vector of `L` lies in `cL = (c : ℝ) • L` exactly when it is `c` times a vector of `L`. -/
theorem mem_smul_submoduleOf_iff {c : ℕ} {v : L} :
    v ∈ ((c : ℝ) • L).submoduleOf L ↔ ∃ w : L, c • w = v := by
  rw [submoduleOf, Submodule.mem_comap, subtype_apply, mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, hw, h⟩
    exact ⟨⟨w, hw⟩, Subtype.ext (by rw [← h, Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul])⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w, w.2, by rw [Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul]⟩

variable (L) [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L]

/-- The quotient `L / cL` of a full lattice of rank `n` has `c ^ n` elements. For `c = 0` this
reads `Nat.card L = 0 ^ n`: the lattice is infinite unless `n = 0`. -/
theorem card_quotient_smul_submoduleOf (c : ℕ) :
    Nat.card (L ⧸ ((c : ℝ) • L).submoduleOf L) = c ^ finrank ℝ E := by
  have h : (((c : ℝ) • L).submoduleOf L).toAddSubgroup = (nsmulAddMonoidHom (α := L) c).range := by
    ext v
    simp [mem_smul_submoduleOf_iff]
  rw [← ZLattice.rank ℝ L, ← AddSubgroup.index_range_nsmul L c, ← h]
  -- The quotient by a submodule is by definition the quotient by its additive subgroup, whose
  -- order is the index.
  rfl

instance (c : ℕ) [NeZero c] : Finite (L ⧸ ((c : ℝ) • L).submoduleOf L) :=
  Nat.finite_of_card_ne_zero <| by
    rw [card_quotient_smul_submoduleOf]
    exact pow_ne_zero _ (NeZero.ne c)

/-- The finite quotient `L / cL` as a `Fintype`, so that finite sums over it, such as the Gauss
sums of a lattice, elaborate for a full lattice and `c ≠ 0`. -/
noncomputable instance instFintypeQuotientSmulSubmoduleOf (c : ℕ) [NeZero c] :
    Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L) :=
  Fintype.ofFinite _

end ZLattice
