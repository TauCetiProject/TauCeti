/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Cone
public import TauCeti.LinearAlgebra.LinearIndependent.NatSpan
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Lattice

/-!
# The root lattice, the positive root cone and dominance

Let `R` be a realization of a matrix, with simple coroots `hᵢ ∈ H` and simple roots
`αᵢ ∈ H*`. This file defines the root lattice `Q = ⊕ᵢ ℤ αᵢ` and the positive root cone
`Q₊ = ⊕ᵢ ℕ αᵢ` inside the full dual `H*`, the height `ht(∑ᵢ nᵢ αᵢ) = ∑ᵢ nᵢ` on `Q₊`, the order
`μ ≤ λ ↔ λ - μ ∈ Q₊` on weights and the dominance predicate `λ(hᵢ) ≥ 0`. Over a field of
characteristic zero the simple roots are independent over `ℕ`, so `Q₊` is pointed, the order is
antisymmetric, and for a finite index set the weights `μ ≤ λ` with `ht(λ - μ) ≤ n` form a finite
set. The independence used is that of the simple roots in the full dual space, so none of this
needs the matrix to be nonsingular: in affine type `A₁⁽¹⁾` the null root `δ = α₀ + α₁` vanishes
on both coroots and is nevertheless a nonzero element of `Q₊`.

These are the cone facts on which the weight theory of a Kac–Moody algebra rests: the weights of a
Verma module lie in `λ - Q₊`, category `O` is cut out by finitely many such cones, and the
finite-height intervals make characters supported on them multiplicable. For a rational
realization of an integral matrix the root lattice lies in every weight lattice
`TauCeti.CartanRealization.CoweightLattice.weightLattice`, and a weight is dominant exactly when its
integral coroot coordinates are nonnegative, so dominance is decidable on the weight lattice.

## Main definitions

* `TauCeti.CartanRealization.rootLattice`: the root lattice `Q`.
* `TauCeti.CartanRealization.posRootCone`: the positive root cone `Q₊`.
* `TauCeti.CartanRealization.height`: the height on `Q₊`.
* `TauCeti.CartanRealization.RootLE`: the order `μ ≤ λ` given by `λ - μ ∈ Q₊`.
* `TauCeti.CartanRealization.IsDominant`: the dominance predicate `λ(hᵢ) ≥ 0` for all `i`.

## Main results

* `TauCeti.CartanRealization.linearIndependent_nat_root`: the simple roots are independent over
  `ℕ`, so `Q₊` is the natural span of an independent family.
* `TauCeti.CartanRealization.isPointed_posRootCone`: `Q₊ ∩ (-Q₊) = 0`.
* `TauCeti.CartanRealization.height_eq_sum`: `ht(∑ᵢ nᵢ αᵢ) = ∑ᵢ nᵢ`.
* `TauCeti.CartanRealization.RootLE.antisymm`: the order on weights is antisymmetric.
* `TauCeti.CartanRealization.finite_setOf_rootLE_height_le`: **finite-height intervals**, the set
  of `μ ≤ λ` with `ht(λ - μ) ≤ n` is finite.
* `TauCeti.CartanRealization.CoweightLattice.rootLattice_le_weightLattice`: `Q ⊆ P`.
* `TauCeti.CartanRealization.CoweightLattice.isDominant_coe_iff`: dominance of an integral weight
  is nonnegativity of its coroot coordinates.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, §1.1 (the root lattice `Q`, the
  cone `Q₊`, height and the order `λ ≥ μ`) and §10.1 (dominant integral weights `P₊`).
-/

public section

open Module

namespace TauCeti

namespace CartanRealization

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I K}
  (R : CartanRealization A H)

/-! ### The root lattice and the positive root cone -/

/-- The **root lattice** `Q`: the integral span of the simple roots in the dual of the
realization. -/
def rootLattice : Submodule ℤ (Dual K H) :=
  Submodule.span ℤ (Set.range R.root)

theorem rootLattice_def : R.rootLattice = Submodule.span ℤ (Set.range R.root) := (rfl)

theorem root_mem_rootLattice (i : I) : R.root i ∈ R.rootLattice :=
  Submodule.subset_span (Set.mem_range_self i)

/-- The elements of the root lattice are the integral combinations of the simple roots. -/
theorem mem_rootLattice_iff [Fintype I] {φ : Dual K H} :
    φ ∈ R.rootLattice ↔ ∃ c : I → ℤ, ∑ i, c i • R.root i = φ :=
  Submodule.mem_span_range_iff_exists_fun ℤ

/-- The **positive root cone** `Q₊`: the natural span of the simple roots in the dual of the
realization. -/
def posRootCone : Submodule ℕ (Dual K H) :=
  Submodule.span ℕ (Set.range R.root)

theorem posRootCone_def : R.posRootCone = Submodule.span ℕ (Set.range R.root) := (rfl)

theorem root_mem_posRootCone (i : I) : R.root i ∈ R.posRootCone :=
  Submodule.subset_span (Set.mem_range_self i)

/-- The elements of the positive root cone are the natural combinations of the simple roots. -/
theorem mem_posRootCone_iff [Fintype I] {φ : Dual K H} :
    φ ∈ R.posRootCone ↔ ∃ c : I → ℕ, ∑ i, c i • R.root i = φ :=
  Submodule.mem_span_range_iff_exists_fun ℕ

/-- The positive root cone lies in the root lattice. -/
theorem posRootCone_le_rootLattice : R.posRootCone ≤ R.rootLattice.restrictScalars ℕ :=
  Submodule.span_le_restrictScalars ℕ ℤ _

/-- With no simple roots, the root lattice is zero. -/
@[simp]
theorem rootLattice_eq_bot [IsEmpty I] : R.rootLattice = ⊥ := by
  simp [rootLattice]

/-- With no simple roots, the positive root cone is zero. -/
@[simp]
theorem posRootCone_eq_bot [IsEmpty I] : R.posRootCone = ⊥ := by
  simp [posRootCone]

section CharZero

variable [CharZero K]

/-- Over a field of characteristic zero the simple roots are independent over `ℕ`, so the
positive root cone is the natural span of an independent family. -/
theorem linearIndependent_nat_root : LinearIndependent ℕ R.root :=
  R.root_linearIndependent.restrict_scalars' ℕ

/-- **The positive root cone is pointed**: `Q₊ ∩ (-Q₊) = 0`, even for a singular matrix. -/
theorem isPointed_posRootCone : R.posRootCone.toAddSubmonoid.IsPointed :=
  fun _ h h' ↦ R.linearIndependent_nat_root.eq_zero_of_mem_natSpan_of_neg_mem h h'

/-- The **height** `ht(∑ᵢ nᵢ αᵢ) = ∑ᵢ nᵢ` of an element of the positive root cone, the sum of its
unique natural coordinates in the simple roots. -/
noncomputable def height : R.posRootCone →+ ℕ :=
  R.linearIndependent_nat_root.natSpanHeight

/-- The height is the `LinearIndependent.natSpanHeight` of the simple roots. -/
theorem height_apply (x : R.posRootCone) :
    R.height x = R.linearIndependent_nat_root.natSpanHeight ⟨x, R.posRootCone_def ▸ x.2⟩ :=
  (rfl)

/-- The height of a natural combination of the simple roots is the sum of its coefficients. -/
theorem height_eq_sum [Fintype I] (x : R.posRootCone) (c : I → ℕ)
    (hc : ∑ i, c i • R.root i = x) : R.height x = ∑ i, c i := by
  let c' := Finsupp.equivFunOnFinite.symm c
  have hx : (R.linearIndependent_nat_root.linearCombinationEquiv c' : R.posRootCone) = x := by
    refine Subtype.ext (hc ▸ ?_)
    simp [c', Finsupp.linearCombination_apply, Finsupp.sum_fintype]
  have key : R.height (R.linearIndependent_nat_root.linearCombinationEquiv c') = c'.degree :=
    R.linearIndependent_nat_root.natSpanHeight_linearCombinationEquiv c'
  rw [← hx, key, Finsupp.degree_eq_sum]
  simp [c']

/-- Each simple root has height one. -/
@[simp]
theorem height_root (i : I) : R.height ⟨R.root i, R.root_mem_posRootCone i⟩ = 1 :=
  R.linearIndependent_nat_root.natSpanHeight_generator i

/-- Zero is the only element of the positive root cone of height zero. -/
@[simp]
theorem height_eq_zero_iff (x : R.posRootCone) : R.height x = 0 ↔ x = 0 :=
  R.linearIndependent_nat_root.natSpanHeight_eq_zero_iff x

end CharZero

/-! ### The order on weights -/

/-- The **order on weights**: `μ ≤ λ` when `λ - μ` lies in the positive root cone. -/
def RootLE (μ lam : Dual K H) : Prop :=
  lam - μ ∈ R.posRootCone

variable {R}

theorem rootLE_iff {μ lam : Dual K H} : R.RootLE μ lam ↔ lam - μ ∈ R.posRootCone := Iff.rfl

@[refl]
theorem rootLE_refl (lam : Dual K H) : R.RootLE lam lam := by
  simp [rootLE_iff]

theorem RootLE.trans {μ ν lam : Dual K H} (h₁ : R.RootLE μ ν) (h₂ : R.RootLE ν lam) :
    R.RootLE μ lam := by
  rw [rootLE_iff, ← sub_add_sub_cancel lam ν μ]
  exact add_mem h₂ h₁

/-- **The order on weights is antisymmetric**, even for a singular matrix. -/
theorem RootLE.antisymm [CharZero K] {μ lam : Dual K H} (h₁ : R.RootLE μ lam)
    (h₂ : R.RootLE lam μ) : μ = lam :=
  R.linearIndependent_nat_root.eq_of_sub_mem_natSpan_of_sub_mem h₂ h₁

instance : IsPreorder (Dual K H) R.RootLE where
  refl := rootLE_refl
  trans _ _ _ := RootLE.trans

instance [CharZero K] : IsPartialOrder (Dual K H) R.RootLE where
  antisymm _ _ := RootLE.antisymm

/-- The order on weights is the partial order on `Dual K H` with positive cone `Q₊`. It is kept
as a named relation because one dual space carries the orders of several realizations. -/
theorem rootLE_eq_ofAddSubmonoid_le [CharZero K] :
    R.RootLE = (PartialOrder.ofAddSubmonoid R.isPointed_posRootCone).le := by
  ext μ lam
  simp [rootLE_iff]

/-- The order on weights is invariant under translation. -/
@[simp]
theorem rootLE_add_right_iff {μ lam : Dual K H} (ν : Dual K H) :
    R.RootLE (μ + ν) (lam + ν) ↔ R.RootLE μ lam := by
  simp [rootLE_iff]

variable (R) in
/-- Subtracting a simple root lowers a weight. -/
theorem rootLE_sub_root (lam : Dual K H) (i : I) : R.RootLE (lam - R.root i) lam := by
  simpa [rootLE_iff] using R.root_mem_posRootCone i

/-- With no simple roots, the order on weights is equality. -/
@[simp]
theorem rootLE_iff_eq [IsEmpty I] {μ lam : Dual K H} : R.RootLE μ lam ↔ μ = lam := by
  simp [rootLE_iff, sub_eq_zero, eq_comm]

variable (R) in
/-- **Finite-height intervals.** For a finite index set, only finitely many weights `μ ≤ λ` have
`ht(λ - μ) ≤ n`. -/
theorem finite_setOf_rootLE_height_le [Finite I] [CharZero K] (lam : Dual K H) (n : ℕ) :
    {μ | ∃ h : R.RootLE μ lam, R.height ⟨lam - μ, rootLE_iff.mp h⟩ ≤ n}.Finite :=
  (R.linearIndependent_nat_root.finite_sub_natSpanHeight_le lam n).subset
    fun μ ⟨h, hn⟩ ↦ ⟨⟨lam - μ, h⟩, (sub_sub_cancel lam μ).symm, hn⟩

/-! ### Dominance -/

section Dominance

variable (R)

/-- A weight is **dominant** if it takes a nonnegative value on every simple coroot. -/
def IsDominant [LE K] (lam : Dual K H) : Prop :=
  ∀ i, 0 ≤ lam (R.coroot i)

variable {R}

theorem isDominant_iff [LE K] {lam : Dual K H} : R.IsDominant lam ↔ ∀ i, 0 ≤ lam (R.coroot i) :=
  Iff.rfl

instance [Fintype I] [LE K] [DecidableLE K] : DecidablePred R.IsDominant :=
  fun _ ↦ decidable_of_iff _ isDominant_iff.symm

/-- With no simple coroots, every weight is dominant. -/
theorem isDominant_of_isEmpty [IsEmpty I] [LE K] (lam : Dual K H) : R.IsDominant lam :=
  isEmptyElim

/-- The zero weight is dominant. -/
theorem isDominant_zero [Preorder K] : R.IsDominant 0 := fun _ ↦ le_rfl

/-- Dominant weights are closed under addition. -/
theorem IsDominant.add [PartialOrder K] [IsOrderedAddMonoid K] {lam μ : Dual K H}
    (hlam : R.IsDominant lam) (hμ : R.IsDominant μ) : R.IsDominant (lam + μ) :=
  fun i ↦ add_nonneg (hlam i) (hμ i)

end Dominance

/-! ### Integral weights -/

namespace CoweightLattice

variable [Module ℚ H] {A : Matrix I I ℤ} {R : CartanRealization (A.map (Int.cast : ℤ → ℚ)) H}
  (L : R.CoweightLattice)

/-- The root lattice lies in every weight lattice: `Q ⊆ P`. -/
theorem rootLattice_le_weightLattice : R.rootLattice ≤ L.weightLattice :=
  L.weightLattice_def ▸ Submodule.span_le.mpr (Set.range_subset_iff.mpr L.root_mem_dualLattice)

/-- An integral weight is dominant exactly when its coroot coordinates are nonnegative. -/
theorem isDominant_coe_iff (lam : L.weightLattice) :
    R.IsDominant (lam : Dual ℚ H) ↔ 0 ≤ L.corootCoordinates lam := by
  simp only [isDominant_iff, Pi.le_def, Pi.zero_apply, corootCoordinates_apply]
  refine forall_congr' fun i ↦ ?_
  rw [← L.coe_coroot i, ← L.cast_pairing, Int.cast_nonneg_iff]

end CoweightLattice

end CartanRealization

end TauCeti
