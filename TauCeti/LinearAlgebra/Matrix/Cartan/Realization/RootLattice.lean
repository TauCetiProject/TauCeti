/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Cone
public import Mathlib.Data.Finsupp.Order
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
* `TauCeti.CartanRealization.restrictRootLatticeEquiv`: restriction of functionals identifies `Q`
  with the root lattice of any sub-realization supplementing the Cartan center.
* `TauCeti.CartanRealization.height`: the height on `Q₊`.
* `TauCeti.CartanRealization.RootLE`: the order `μ ≤ λ` given by `λ - μ ∈ Q₊`.
* `TauCeti.CartanRealization.IsDominant`: the dominance predicate `λ(hᵢ) ≥ 0` for all `i`.

## Main results

* `TauCeti.CartanRealization.eval_eq_zero_of_mem_rootLattice`: elements of `Q` vanish on the Cartan
  center.
* `TauCeti.CartanRealization.linearIndependent_nat_root`: the simple roots are independent over
  `ℕ`, so `Q₊` is the natural span of an independent family.
* `TauCeti.CartanRealization.rootLinearCombination_injective` and
  `TauCeti.CartanRealization.rootLinearCombination_mem_posRootCone_iff`: integral combinations of
  simple roots have unique coordinates and lie in `Q₊` iff their coordinates are nonnegative.
* `TauCeti.CartanRealization.isPointed_posRootCone`: `Q₊ ∩ (-Q₊) = 0`.
* `TauCeti.CartanRealization.height_eq_sum`: `ht(∑ᵢ nᵢ αᵢ) = ∑ᵢ nᵢ`.
* `TauCeti.CartanRealization.RootLE.antisymm`: the order on weights is antisymmetric.
* `TauCeti.CartanRealization.finite_setOf_rootLE_height_le`: **finite-height intervals**, the set
  of `μ ≤ λ` with `ht(λ - μ) ≤ n` is finite.
* `TauCeti.CartanRealization.exists_intCast_eval_coroot_of_mem_rootLattice`: for an integral
  matrix, elements of `Q` take integer-cast values on simple coroots.
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

/-- Every element of `R.rootLattice` vanishes on the Cartan center. -/
theorem eval_eq_zero_of_mem_rootLattice {φ : Dual K H} (hφ : φ ∈ R.rootLattice)
    {z : H} (hz : z ∈ R.cartanCenter) : φ z = 0 := by
  rw [R.rootLattice_def] at hφ
  induction hφ using Submodule.span_induction with
  | mem _ hx => obtain ⟨i, rfl⟩ := hx; exact (R.mem_cartanCenter_iff z).mp hz i
  | zero => rfl
  | add _ _ _ _ ihx ihy => simp [ihx, ihy]
  | smul n _ _ ihx => simp [ihx]

/-- Restriction of functionals from `H` to `M` identifies `R.rootLattice` with
`(R.restrict M hc hs).rootLattice` as `ℤ`-modules. -/
noncomputable def restrictRootLatticeEquiv (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) :
    R.rootLattice ≃ₗ[ℤ] (R.restrict M hc hs).rootLattice := by
  let f : Dual K H →ₗ[ℤ] Dual K M := M.subtype.dualMap.restrictScalars ℤ
  have hcomp : f ∘ R.root = (R.restrict M hc hs).root := by ext i m; simp [f]
  have hmap : R.rootLattice.map f = (R.restrict M hc hs).rootLattice := by
    rw [R.rootLattice_def, (R.restrict M hc hs).rootLattice_def, Submodule.map_span,
      ← Set.range_comp, hcomp]
  let g : R.rootLattice →ₗ[ℤ] (R.restrict M hc hs).rootLattice :=
    (f.domRestrict R.rootLattice).codRestrict (R.restrict M hc hs).rootLattice
      fun φ ↦ hmap ▸ Submodule.mem_map_of_mem φ.2
  refine LinearEquiv.ofBijective g ⟨fun φ₁ φ₂ h12 ↦ Subtype.ext ?_, fun ψ ↦ ?_⟩
  · rw [← sub_eq_zero]
    ext x
    obtain ⟨m, hm, z, hz, rfl⟩ := Submodule.mem_sup.mp (hs ▸ Submodule.mem_top : x ∈ _)
    have hm' : (φ₁.1 - φ₂.1) m = 0 := by
      simpa [g, f, sub_eq_zero] using
        congrArg (fun ξ : Dual K M ↦ ξ ⟨m, hm⟩) (congrArg Subtype.val h12)
    rw [map_add, hm', R.eval_eq_zero_of_mem_rootLattice (sub_mem φ₁.2 φ₂.2) hz, add_zero,
      LinearMap.zero_apply]
  · obtain ⟨φ, hφ, hφψ⟩ := Submodule.mem_map.mp (hmap.symm ▸ ψ.2 : ψ.1 ∈ R.rootLattice.map f)
    exact ⟨⟨φ, hφ⟩, Subtype.ext hφψ⟩

/-- Coercing `R.restrictRootLatticeEquiv` to `Dual K M` is `M.subtype.dualMap`. -/
@[simp]
theorem coe_restrictRootLatticeEquiv (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) (φ : R.rootLattice) :
    ((R.restrictRootLatticeEquiv M hc hs φ : (R.restrict M hc hs).rootLattice) : Dual K M) =
      M.subtype.dualMap φ := (rfl)

section CharZero

variable [CharZero K]

/-- Over a field of characteristic zero the simple roots are independent over `ℕ`, so the
positive root cone is the natural span of an independent family. -/
theorem linearIndependent_nat_root : LinearIndependent ℕ R.root :=
  R.root_linearIndependent.restrict_scalars' ℕ

/-- Over a field of characteristic zero, `Finsupp.linearCombination ℤ R.root` is injective, so
elements of the root lattice have unique integral coordinates in the simple roots. -/
theorem rootLinearCombination_injective :
    Function.Injective (Finsupp.linearCombination ℤ R.root) :=
  (R.root_linearIndependent.restrict_scalars' ℤ).finsuppLinearCombination_injective

/-- An integral combination of simple roots lies in `R.posRootCone` iff its coordinates are
nonnegative. -/
theorem rootLinearCombination_mem_posRootCone_iff (x : I →₀ ℤ) :
    Finsupp.linearCombination ℤ R.root x ∈ R.posRootCone ↔ 0 ≤ x := by
  let castNat : (I →₀ ℕ) →+ (I →₀ ℤ) := Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)
  have hcast_apply (y : I →₀ ℕ) (i : I) : castNat y i = (y i : ℤ) := by simp [castNat]
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · rw [R.posRootCone_def] at hx
    have hex : ∀ φ ∈ Submodule.span ℕ (Set.range R.root),
        ∃ y : I →₀ ℕ, Finsupp.linearCombination ℤ R.root (castNat y) = φ := by
      intro φ hφ
      induction hφ using Submodule.span_induction with
      | mem _ h => obtain ⟨i, rfl⟩ := h; exact ⟨Finsupp.single i 1, by simp [castNat]⟩
      | zero => exact ⟨0, by simp⟩
      | add _ _ _ _ ih₁ ih₂ =>
        obtain ⟨y₁, hy₁⟩ := ih₁; obtain ⟨y₂, hy₂⟩ := ih₂
        exact ⟨y₁ + y₂, by rw [map_add, map_add, hy₁, hy₂]⟩
      | smul n _ _ ih => obtain ⟨y, hy⟩ := ih; exact ⟨n • y, by rw [map_nsmul, map_nsmul, hy]⟩
    obtain ⟨y, hy⟩ := hex _ hx
    rw [← R.rootLinearCombination_injective hy]
    intro i; rw [hcast_apply]; exact Nat.cast_nonneg (y i)
  · let y : I →₀ ℕ := x.mapRange Int.toNat rfl
    have hyx : castNat y = x := by ext i; rw [hcast_apply]; exact Int.toNat_of_nonneg (hx i)
    rw [← hyx]
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y₁ y₂ ih₁ ih₂ => rw [map_add, map_add]; exact add_mem ih₁ ih₂
    | single i n =>
      have hsingle : castNat (Finsupp.single i n) = Finsupp.single i (n : ℤ) := by simp [castNat]
      rw [hsingle, Finsupp.linearCombination_single, natCast_zsmul]
      exact Submodule.smul_mem _ n (R.root_mem_posRootCone i)

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

/-! ### Integral matrices and integral weights -/

section IntegralMatrix

variable {A : Matrix I I ℤ} (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-- Every functional in `R.rootLattice` takes integer-cast values on simple coroots. -/
theorem exists_intCast_eval_coroot_of_mem_rootLattice {φ : Dual K H} (hφ : φ ∈ R.rootLattice)
    (i : I) : ∃ n : ℤ, (n : K) = φ (R.coroot i) := by
  rw [R.rootLattice_def] at hφ
  induction hφ using Submodule.span_induction with
  | mem _ hx => obtain ⟨j, rfl⟩ := hx; exact ⟨A i j, by simp⟩
  | zero => exact ⟨0, by simp⟩
  | add _ _ _ _ ihx ihy =>
    obtain ⟨nx, hnx⟩ := ihx; obtain ⟨ny, hny⟩ := ihy
    exact ⟨nx + ny, by simp [← hnx, ← hny]⟩
  | smul c _ _ ihx => obtain ⟨nx, hnx⟩ := ihx; exact ⟨c * nx, by simp [← hnx]⟩

end IntegralMatrix

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
