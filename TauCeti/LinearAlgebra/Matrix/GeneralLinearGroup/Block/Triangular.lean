/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Basic
public import TauCeti.LinearAlgebra.Matrix.LDU

/-!
# Block triangular, unitriangular, Levi, and parahoric subgroups of `GL n R`

Let `R` be a commutative ring and `n` a finite index type with decidable equality. For a level
function `lev : n → α` into a linear order `α`, or a labelling `τ : n → α`, we construct the
standard subgroups of `GL n R` cut out by entry conditions.

## Main definitions

* `TauCeti.agreeWithOneOn r R h_split`: the subgroup of invertible matrices agreeing with `1` at
  the entries `(i, j)` with `r i j`, for a relation `r` such that `r i j` implies `r i k` or
  `r k j`.
* `TauCeti.unitriangularSubgroup lev R`: the subgroup of `GL n R` of block upper unitriangular
  matrices for a level function `lev`, built from `Matrix.BlockUnitriangular`.
* `TauCeti.leviSubgroup τ R`: the block-diagonal matrices for a labelling `τ`.
* `TauCeti.parahoricSubgroup τ I`: the matrices whose entries `(i, j)` with `τ i < τ j` lie in an
  ideal `I`, i.e., that reduce modulo `I` to a block lower triangular matrix; for the ring of
  integers of a non-archimedean local field and its maximal ideal this is the standard parahoric
  subgroup attached to `τ`.

## Main results

* `TauCeti.unitriangularSubgroup_le_blockTriangularGroup`: block upper unitriangular matrices
  are block upper triangular.
* `TauCeti.conj_mem_unitriangularSubgroup`: block upper triangular matrices normalize the block
  upper unitriangular subgroup.
* `TauCeti.leviSubgroup_le_parahoricSubgroup`: the Levi subgroup is contained in the parahoric
  subgroup for any ideal `I`.

## References

The definitions are adapted from the Lean project grh-lean, also called riemann-hypothesis
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/General/Groups/BesselGroups.lean` (declarations `New.parabolic`, `New.agreeWithOneOn`,
`New.unitriangular`, `New.levi`, `New.parahoric`). Here the Levi and parahoric subgroups are
stated for any index type, commutative ring, and ideal.
-/

public section

open Matrix

namespace TauCeti

variable {R : Type*} [CommRing R]

/-! ### Block triangular and unitriangular subgroups -/

section Triangular

variable {n : Type*} [Fintype n] [DecidableEq n] {α : Type*} [LinearOrder α] (lev : n → α)

open scoped Classical in
/-- For a relation `r` such that `r i j` implies `r i k` or `r k j` for every `k`, the subgroup
of invertible matrices that agree with the identity matrix at every entry `(i, j)` with
`r i j`. -/
def agreeWithOneOn (r : n → n → Prop) (R : Type*) [CommRing R]
    (h_split : ∀ i k j : n, r i j → r i k ∨ r k j) : Subgroup (GL n R) :=
  Subgroup.ofDiv {u : GL n R | ∀ i j : n, r i j → u i j = (1 : Matrix n n R) i j} ⟨1, by simp⟩ <| by
    -- Compare `(x * y⁻¹) i j` with `(y * y⁻¹) i j` term by term. If `r i k` then `x i k = y i k`;
    -- otherwise `y⁻¹ k j = 0`, as `y` is block triangular for the level function that is `0`
    -- where `r i ·` holds and `1` elsewhere.
    intro x hx y hy i j hij
    have hy_inv : ((y⁻¹ : GL n R) : Matrix n n R).BlockTriangular
        fun k : n ↦ if r i k then (0 : ℕ) else 1 := by
      refine mem_blockTriangularGroup_iff.1 ((blockTriangularGroup R
          (fun k : n ↦ if r i k then (0 : ℕ) else 1)).inv_mem
        (mem_blockTriangularGroup_iff.2 fun a b hab ↦ ?_))
      obtain ⟨hib, hia⟩ : r i b ∧ ¬ r i a := by grind
      have hab_ne : a ≠ b := fun h_eq ↦ hia (by rwa [h_eq])
      exact (hy a b ((h_split i a b hib).resolve_left hia)).trans (one_apply_ne hab_ne)
    have h_term : ∀ k : n, x.val i k * y⁻¹.val k j = y.val i k * y⁻¹.val k j := fun k ↦ by
      by_cases hik : r i k
      · rw [hx i k hik, hy i k hik]
      · have h_zero : y⁻¹.val k j = 0 := hy_inv (by simp [hik, hij])
        rw [h_zero, mul_zero, mul_zero]
    calc (x.val * y⁻¹.val) i j = ∑ k : n, y.val i k * y⁻¹.val k j :=
          Finset.sum_congr rfl fun k _ ↦ h_term k
      _ = (1 : Matrix n n R) i j := by rw [← Matrix.mul_apply, y.mul_inv]

@[simp] theorem mem_agreeWithOneOn {r : n → n → Prop} {h_split : ∀ i k j : n, r i j → r i k ∨ r k j}
    {x : GL n R} :
    x ∈ agreeWithOneOn r R h_split ↔ ∀ i j : n, r i j → x i j = (1 : Matrix n n R) i j :=
  .rfl

/-- The subgroup of `GL n R` of block upper unitriangular matrices for the level function `lev`. -/
def unitriangularSubgroup (R : Type*) [CommRing R] : Subgroup (GL n R) where
  carrier := {g | (g : Matrix n n R).BlockUnitriangular lev}
  one_mem' := blockUnitriangular_one
  mul_mem' hg hh := hg.mul hh
  inv_mem' {g} hg := by
    simpa [Matrix.coe_units_inv] using hg.inv

@[simp] theorem mem_unitriangularSubgroup {g : GL n R} :
    g ∈ unitriangularSubgroup lev R ↔ (g : Matrix n n R).BlockUnitriangular lev := .rfl

theorem unitriangularSubgroup_le_blockTriangularGroup :
    unitriangularSubgroup lev R ≤ blockTriangularGroup R lev :=
  fun _ h ↦ mem_blockTriangularGroup_iff.2 h.blockTriangular

variable {lev}

/-- If `d` is block upper triangular and `u` is block upper unitriangular for `lev`, then
`d⁻¹ * u * d` is block upper unitriangular for `lev`. -/
theorem conj_mem_unitriangularSubgroup {u d : GL n R} (hd : d ∈ blockTriangularGroup R lev)
    (hu : u ∈ unitriangularSubgroup lev R) : d⁻¹ * u * d ∈ unitriangularSubgroup lev R := by
  -- In a nonzero term `d⁻¹ i k * u k l * d l j` with `lev j ≤ lev i` we have
  -- `lev l ≤ lev j ≤ lev i ≤ lev k`, so `u k l` is the entry of `1`.
  refine blockUnitriangular_of_apply_eq_one_apply_of_not_lt fun i j hij ↦ ?_
  have hd_bt : (d : Matrix n n R).BlockTriangular lev := mem_blockTriangularGroup_iff.1 hd
  have hd_inv : ((d⁻¹ : GL n R) : Matrix n n R).BlockTriangular lev :=
    mem_blockTriangularGroup_iff.1 ((blockTriangularGroup R lev).inv_mem hd)
  have hu_entry : ∀ k l : n, lev l ≤ lev k → u.val k l = (1 : Matrix n n R) k l := fun k l h ↦ by
    rcases h.lt_or_eq with hlt | heq
    · rw [hu.blockTriangular hlt, one_apply_ne fun hkl ↦ hlt.ne (congrArg lev hkl.symm)]
    · exact hu.apply_of_eq heq.symm
  have h_term : ∀ k l : n, d⁻¹.val i k * u.val k l * d.val l j =
      d⁻¹.val i k * (1 : Matrix n n R) k l * d.val l j := fun k l ↦ by
    grind [@hd_inv i k, @hd_bt l j, hu_entry k l, not_le, not_lt]
  calc (d⁻¹ * u * d).val i j = (d⁻¹.val * (1 : Matrix n n R) * d.val) i j := by
        simp only [Units.val_mul, Matrix.mul_apply, Finset.sum_mul, h_term]
    _ = (1 : Matrix n n R) i j := by simp

end Triangular

/-! ### Levi and parahoric subgroups -/

section Parahoric

variable {n : Type*} [Fintype n] [DecidableEq n] {α : Type*} (τ : n → α)

/-- The Levi subgroup of a labelling `τ`: the invertible matrices whose entry `(i, j)` vanishes
whenever `τ i ≠ τ j`. -/
def leviSubgroup (R : Type*) [CommRing R] : Subgroup (GL n R) :=
  (agreeWithOneOn (fun i j : n ↦ τ i ≠ τ j) R fun _ l _ hij ↦
      (hij.ne_or_ne (τ l)).imp_right Ne.symm).copy
    {g | ∀ i j : n, τ i ≠ τ j → (g : Matrix n n R) i j = 0} <| by
    ext g
    simp +contextual [ne_of_apply_ne τ]

@[simp] theorem mem_leviSubgroup {g : GL n R} :
    g ∈ leviSubgroup τ R ↔ ∀ i j : n, τ i ≠ τ j → (g : Matrix n n R) i j = 0 := .rfl

/-- The preimage modulo an ideal `I` of the block lower triangular subgroup for a labelling `τ`:
the invertible matrices whose entry `(i, j)` lies in `I` whenever `τ i < τ j`. For the ring of
integers of a non-archimedean local field and its maximal ideal this is the standard parahoric
subgroup attached to `τ`. -/
def parahoricSubgroup [LinearOrder α] (I : Ideal R) : Subgroup (GL n R) :=
  (blockTriangularGroup (R ⧸ I) (OrderDual.toDual ∘ τ)).comap
    (GeneralLinearGroup.map (Ideal.Quotient.mk I))

@[simp] theorem mem_parahoricSubgroup [LinearOrder α] (I : Ideal R) {g : GL n R} :
    g ∈ parahoricSubgroup τ I ↔ ∀ i j : n, τ i < τ j → (g : Matrix n n R) i j ∈ I := by
  simp [parahoricSubgroup, BlockTriangular, Ideal.Quotient.eq_zero_iff_mem]

theorem leviSubgroup_le_parahoricSubgroup [LinearOrder α] (I : Ideal R) :
    leviSubgroup τ R ≤ parahoricSubgroup τ I := fun _ hg ↦
  (mem_parahoricSubgroup τ I).2 fun i j hij ↦ hg i j hij.ne ▸ I.zero_mem

end Parahoric

end TauCeti
