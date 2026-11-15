/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
import Mathlib.Tactic.LinearCombination

/-!
# Exterior creation and contraction in the coordinates of an exterior basis

Let `b` be a basis of `M` indexed by a finite linearly ordered type `I`. The exterior algebra
`⋀ M` then has the basis `b.ExteriorAlgebra`, indexed by `Finset I`, whose vector for
`s = {i₁ < ⋯ < iₖ}` is `b i₁ ∧ ⋯ ∧ b iₖ`, so an element of `⋀ M` is the same thing as its
coordinate vector in `Finset I → R`. This file transports the two basic operators on `⋀ M` to
coordinate vectors:

* **creation** `εᵢ`, left exterior multiplication by `b i`
  (`Module.Basis.exteriorCreation`), and
* **contraction** `ιᵢ`, contraction by the coordinate functional `b.coord i`
  (`Module.Basis.exteriorContraction`).

In coordinates `εᵢ` moves the coefficient of `s` to `insert i s` and `ιᵢ` moves the coefficient of
`s` to `s.erase i`, each with the shuffle sign `TauCeti.ExteriorAlgebra.basisEraseSign` that moves
`i` to the front (`Module.Basis.exteriorCreation_apply`, `Module.Basis.exteriorContraction_apply`).
They satisfy the canonical anticommutation relation `εᵢ ιⱼ + ιⱼ εᵢ = δᵢⱼ`
(`Module.Basis.exteriorCreation_mul_exteriorContraction_add_swap`), creations anticommute among
themselves (`Module.Basis.exteriorCreation_mul_exteriorCreation_add_swap`), so a double sum
`∑ⱼ ∑ᵢ εⱼ εᵢ Xⱼᵢ` with symmetric coefficients vanishes
(`Module.Basis.sum_sum_exteriorCreation_exteriorCreation_eq_zero`), and contractions anticommute
too (`Module.Basis.exteriorContraction_mul_exteriorContraction_add_swap`). The product `εᵢ ιᵢ` is
the occupation projection onto the coordinates `s` containing `i`
(`Module.Basis.exteriorCreation_mul_exteriorContraction_self_apply`), so the commutator
`⁅εᵢ, ιᵢ⁆` multiplies the coefficient of `s` by `1` if `i ∈ s` and by `-1` otherwise
(`Module.Basis.lie_exteriorCreation_exteriorContraction_self_apply`), and `ιᵢ` is the transpose
of `εᵢ` for the standard pairing of coordinate vectors
(`Module.Basis.sum_exteriorCreation_apply_mul`). Hence `|ιᵢ φ|² + |εᵢ φ|² = |φ|²`
(`Module.Basis.sum_exteriorContraction_apply_sq_add_sum_exteriorCreation_apply_sq`), and over an
ordered ring the commutator `⁅εᵢ, ιⱼ⁆` has quadratic form bounded by `|φ|²`
(`Module.Basis.abs_sum_lie_exteriorCreation_exteriorContraction_apply_mul_le`), so a combination
`∑ᵢⱼ Hᵢⱼ ⁅εᵢ, ιⱼ⁆` has quadratic form bounded by `(∑ᵢⱼ |Hᵢⱼ|) |φ|²`
(`Module.Basis.abs_sum_sum_sum_smul_lie_exteriorCreation_exteriorContraction_apply_mul_le`).
Combining the anticommutation relation with these commutators, a double sum of products `εᵢ ιⱼ`
and `ιⱼ εᵢ` reduces to a diagonal term plus commutators
(`TauCeti.sum_creation_contraction_of_anticommutator`).
For an orthonormal basis of a Euclidean space the standard pairing is the induced inner product on
`⋀ M`, so `ιᵢ` is the adjoint of `εᵢ`.

Coordinate vectors are what one differentiates: a differential form on `ℝⁿ` is a function with
values in the coordinate space `Finset (Fin n) → ℝ`, a finite-dimensional normed space, and the
exterior derivative, its formal adjoint and their deformations are sums of these operators applied
to partial derivatives.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, §6.1.
* E. Witten, *Supersymmetry and Morse theory*, J. Differential Geom. **17** (1982), §2, for the
  creation and annihilation operators on forms.
-/

public section

open CliffordAlgebra TauCeti.ExteriorAlgebra

namespace Module.Basis

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M] [LinearOrder I] [Fintype I]
  (b : Module.Basis I R M)

/-- **Exterior creation in coordinates**: left exterior multiplication by `b i` on `⋀ M`, written in
the coordinates of the exterior basis `b.ExteriorAlgebra`. -/
noncomputable def exteriorCreation (i : I) : Module.End R (Finset I → R) :=
  b.ExteriorAlgebra.equivFun.conj (LinearMap.mulLeft R (ExteriorAlgebra.ι R (b i)))

/-- **Exterior contraction in coordinates**: contraction by the coordinate functional `b.coord i`
on `⋀ M`, written in the coordinates of the exterior basis `b.ExteriorAlgebra`. -/
noncomputable def exteriorContraction (i : I) : Module.End R (Finset I → R) :=
  b.ExteriorAlgebra.equivFun.conj (contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i))

/-- Exterior creation in coordinates is conjugate to left multiplication by `b i`. -/
theorem exteriorCreation_equivFun (i : I) (x : _root_.ExteriorAlgebra R M) :
    b.exteriorCreation i (b.ExteriorAlgebra.equivFun x) =
      b.ExteriorAlgebra.equivFun (ExteriorAlgebra.ι R (b i) * x) := by
  simp [exteriorCreation, LinearEquiv.conj_apply]

/-- Exterior contraction in coordinates is conjugate to contraction by `b.coord i`. -/
theorem exteriorContraction_equivFun (i : I) (x : _root_.ExteriorAlgebra R M) :
    b.exteriorContraction i (b.ExteriorAlgebra.equivFun x) =
      b.ExteriorAlgebra.equivFun (contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) x) := by
  simp [exteriorContraction, LinearEquiv.conj_apply]

/-- **The coordinates of an exterior creation**: the coefficient of `s` in `εᵢ φ` is the coefficient
of `s.erase i` in `φ`, with the sign that moves `i` to the front of `s`, when `i ∈ s`, and zero
otherwise. -/
@[simp]
theorem exteriorCreation_apply (i : I) (φ : Finset I → R) (s : Finset I) :
    b.exteriorCreation i φ s = if i ∈ s then basisEraseSign i s • φ (s.erase i) else 0 := by
  classical
  obtain ⟨x, rfl⟩ := b.ExteriorAlgebra.equivFun.surjective φ
  rw [exteriorCreation_equivFun, ← b.ExteriorAlgebra.sum_repr x, Finset.mul_sum]
  simp only [Algebra.mul_smul_comm, map_sum, map_smul, TauCeti.ExteriorAlgebra.ι_mul_basis,
    apply_ite, map_zero, map_zsmul_unit, Basis.equivFun_apply, Basis.repr_self, Finset.sum_apply,
    Pi.smul_apply, smul_zero, Finsupp.single_apply]
  split_ifs with hi
  · rw [Finset.sum_eq_single (s.erase i)]
    · simp [Finset.insert_erase hi]
    · intro t _ hts
      split_ifs with hit
      · rfl
      · have : insert i t ≠ s := fun h ↦ hts (by rw [← h, Finset.erase_insert hit])
        simp [this]
    · simp
  · refine Finset.sum_eq_zero fun t _ ↦ ?_
    split_ifs with hit
    · rfl
    · have : insert i t ≠ s := fun h ↦ hi (h ▸ Finset.mem_insert_self i t)
      simp [this]

/-- **The coordinates of an exterior contraction**: the coefficient of `s` in `ιᵢ φ` is the
coefficient of `insert i s` in `φ`, with the sign that moves `i` to the front of `insert i s`, when
`i ∉ s`, and zero otherwise. -/
@[simp]
theorem exteriorContraction_apply (i : I) (φ : Finset I → R) (s : Finset I) :
    b.exteriorContraction i φ s =
      if i ∈ s then 0 else basisEraseSign i (insert i s) • φ (insert i s) := by
  classical
  obtain ⟨x, rfl⟩ := b.ExteriorAlgebra.equivFun.surjective φ
  rw [exteriorContraction_equivFun, ← b.ExteriorAlgebra.sum_repr x]
  simp only [map_sum, map_smul, TauCeti.ExteriorAlgebra.contractLeft_coord_basis,
    apply_ite, map_zero, map_zsmul_unit, Basis.equivFun_apply, Basis.repr_self, Finset.sum_apply,
    Pi.smul_apply, smul_zero, Finsupp.single_apply]
  split_ifs with hi
  · refine Finset.sum_eq_zero fun t _ ↦ ?_
    split_ifs with hit
    · have : t.erase i ≠ s := fun h ↦ Finset.notMem_erase i t (h ▸ hi)
      simp [this]
    · rfl
  · rw [Finset.sum_eq_single (insert i s)]
    · simp [Finset.erase_insert hi]
    · intro t _ hts
      split_ifs with hit
      · have : t.erase i ≠ s := fun h ↦ hts (by rw [← h, Finset.insert_erase hit])
        simp [this]
      · rfl
    · simp

/-- **The canonical anticommutation relation**: `εᵢ ιⱼ + ιⱼ εᵢ` is the identity when `i = j` and
zero otherwise. -/
theorem exteriorCreation_mul_exteriorContraction_add_swap (i j : I) :
    b.exteriorCreation i * b.exteriorContraction j +
        b.exteriorContraction j * b.exteriorCreation i =
      if i = j then 1 else 0 := by
  classical
  refine LinearMap.ext fun φ ↦ ?_
  obtain ⟨x, rfl⟩ := b.ExteriorAlgebra.equivFun.surjective φ
  simp only [LinearMap.add_apply, mul_apply_eq_comp, exteriorContraction_equivFun,
    exteriorCreation_equivFun, contractLeft_ι_mul, ← map_add, add_sub_cancel,
    Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  split_ifs with h
  · subst h
    simp
  · simp

/-- **Exterior creations anticommute**: `εᵢ εⱼ + εⱼ εᵢ = 0`. -/
theorem exteriorCreation_mul_exteriorCreation_add_swap (i j : I) :
    b.exteriorCreation i * b.exteriorCreation j + b.exteriorCreation j * b.exteriorCreation i =
      0 := by
  refine LinearMap.ext fun φ ↦ ?_
  obtain ⟨x, rfl⟩ := b.ExteriorAlgebra.equivFun.surjective φ
  simp only [LinearMap.add_apply, mul_apply_eq_comp, exteriorCreation_equivFun, ← map_add,
    ← mul_assoc, ← add_mul, ExteriorAlgebra.ι_add_mul_swap, zero_mul, map_zero,
    LinearMap.zero_apply]

/-- A double sum `∑ⱼ ∑ᵢ εⱼ εᵢ Xⱼᵢ` with symmetric coefficients vanishes, since creations
anticommute and square to zero. -/
theorem sum_sum_exteriorCreation_exteriorCreation_eq_zero (X : I → I → Finset I → R)
    (hX : ∀ i j, X i j = X j i) :
    ∑ j, ∑ i, b.exteriorCreation j (b.exteriorCreation i (X j i)) = 0 := by
  rw [← Fintype.sum_prod_type']
  refine Finset.sum_involution (fun p _ ↦ p.swap) (fun ⟨j, i⟩ _ ↦ ?_)
    (fun ⟨j, i⟩ _ h hp ↦ h ?_) (fun p _ ↦ Finset.mem_univ _) (fun p _ ↦ p.swap_swap)
  · rw [Prod.swap_prod_mk, hX i j]
    exact congr($(b.exteriorCreation_mul_exteriorCreation_add_swap j i) (X j i))
  · obtain rfl : i = j := congrArg Prod.fst hp
    obtain ⟨x, hx⟩ := b.ExteriorAlgebra.equivFun.surjective (X i i)
    rw [← hx, exteriorCreation_equivFun, exteriorCreation_equivFun, ← mul_assoc,
      ExteriorAlgebra.ι_sq_zero, zero_mul, map_zero]

/-- **Exterior contractions anticommute**: `ιᵢ ιⱼ + ιⱼ ιᵢ = 0`. -/
theorem exteriorContraction_mul_exteriorContraction_add_swap (i j : I) :
    b.exteriorContraction i * b.exteriorContraction j +
        b.exteriorContraction j * b.exteriorContraction i =
      0 := by
  refine LinearMap.ext fun φ ↦ ?_
  obtain ⟨x, rfl⟩ := b.ExteriorAlgebra.equivFun.surjective φ
  simp only [LinearMap.add_apply, mul_apply_eq_comp, exteriorContraction_equivFun, ← map_add,
    contractLeft_comm (b.coord i) (b.coord j), neg_add_cancel, map_zero, LinearMap.zero_apply]

/-- **The occupation projection**: `εᵢ ιᵢ` keeps the coefficients of the index sets containing `i`
and kills the others. -/
theorem exteriorCreation_mul_exteriorContraction_self_apply (i : I) (φ : Finset I → R)
    (s : Finset I) :
    (b.exteriorCreation i * b.exteriorContraction i) φ s = if i ∈ s then φ s else 0 := by
  classical
  rw [mul_apply_eq_comp, exteriorCreation_apply]
  split_ifs with hi
  · rw [exteriorContraction_apply, ite_eq_right (Finset.notMem_erase i s), Finset.insert_erase hi,
      smul_smul, ← sq, Int.units_sq, one_smul]
  · rfl

/-- **The commutator `⁅εᵢ, ιᵢ⁆`** multiplies the coefficient of an index set by `1` if it contains
`i` and by `-1` otherwise. -/
theorem lie_exteriorCreation_exteriorContraction_self_apply (i : I) (φ : Finset I → R)
    (s : Finset I) :
    ⁅b.exteriorCreation i, b.exteriorContraction i⁆ φ s = if i ∈ s then φ s else -φ s := by
  have h := congr($(b.exteriorCreation_mul_exteriorContraction_add_swap i i) φ s)
  simp only [LinearMap.add_apply, Pi.add_apply, ↓reduceIte, one_apply_eq_self] at h
  rw [Ring.lie_def, LinearMap.sub_apply, Pi.sub_apply]
  have hp := b.exteriorCreation_mul_exteriorContraction_self_apply i φ s
  split_ifs at hp ⊢ <;> linear_combination 2 * hp - h

/-- `ιᵢ` is the transpose of `εᵢ` for the standard pairing `∑ s, φ s * ψ s` of coordinate
vectors. -/
theorem sum_exteriorCreation_apply_mul (i : I) (φ ψ : Finset I → R) :
    ∑ s, b.exteriorCreation i φ s * ψ s = ∑ s, φ s * b.exteriorContraction i ψ s := by
  classical
  simp only [exteriorCreation_apply, exteriorContraction_apply, ite_mul, zero_mul, mul_ite,
    mul_zero]
  rw [← Finset.sum_filter]
  simp only [← ite_not _ _ (0 : R)]
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun s ↦ s.erase i) (fun s ↦ insert i s) ?_ ?_ ?_ ?_ ?_
  · simp
  · simp
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    exact Finset.insert_erase hs
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    exact Finset.erase_insert hs
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    rw [Finset.insert_erase hs, Units.smul_def, Units.smul_def, zsmul_eq_mul, zsmul_eq_mul]
    ring

/-- **Creation and contraction split the squared norm.** For the standard pairing of coordinate
vectors, `|ιᵢ φ|² + |εᵢ φ|² = |φ|²`: this is the canonical anticommutation relation
`εᵢ ιᵢ + ιᵢ εᵢ = 1` paired with `φ`, since `ιᵢ` is the transpose of `εᵢ`. -/
theorem sum_exteriorContraction_apply_sq_add_sum_exteriorCreation_apply_sq (i : I)
    (φ : Finset I → R) :
    ∑ s, b.exteriorContraction i φ s ^ 2 + ∑ s, b.exteriorCreation i φ s ^ 2 = ∑ s, φ s ^ 2 := by
  have h := congr($(b.exteriorCreation_mul_exteriorContraction_add_swap i i) φ)
  simp only [LinearMap.add_apply, mul_apply_eq_comp, ↓reduceIte, one_apply_eq_self] at h
  have h₁ : ∑ s, b.exteriorContraction i φ s ^ 2 =
      ∑ s, b.exteriorCreation i (b.exteriorContraction i φ) s * φ s := by
    simp only [sq, b.sum_exteriorCreation_apply_mul]
  have h₂ : ∑ s, b.exteriorCreation i φ s ^ 2 =
      ∑ s, b.exteriorContraction i (b.exteriorCreation i φ) s * φ s := by
    simp only [sq, b.sum_exteriorCreation_apply_mul, mul_comm]
  rw [h₁, h₂, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [← add_mul, ← Pi.add_apply, h, sq]

/-- **The quadratic form of the commutator `⁅εᵢ, ιⱼ⁆` is bounded by the squared norm.** For
coordinates in an ordered ring, `|⟨⁅εᵢ, ιⱼ⁆ φ, φ⟩| ≤ |φ|²` for the standard pairing. Indeed
`⟨⁅εᵢ, ιⱼ⁆ φ, φ⟩ = ⟨ιⱼ φ, ιᵢ φ⟩ - ⟨εⱼ φ, εᵢ φ⟩`, and `|ιₖ φ|² + |εₖ φ|² = |φ|²` for `k = i, j`.
This bounds the quadratic form only: for `i ≠ j` the operator `⁅εᵢ, ιⱼ⁆ = 2 εᵢ ιⱼ` is not a
contraction. -/
theorem abs_sum_lie_exteriorCreation_exteriorContraction_apply_mul_le [LinearOrder R]
    [IsStrictOrderedRing R] (i j : I) (φ : Finset I → R) :
    |∑ s, ⁅b.exteriorCreation i, b.exteriorContraction j⁆ φ s * φ s| ≤ ∑ s, φ s ^ 2 := by
  have hj := b.sum_exteriorContraction_apply_sq_add_sum_exteriorCreation_apply_sq j φ
  have hi := b.sum_exteriorContraction_apply_sq_add_sum_exteriorCreation_apply_sq i φ
  set a := b.exteriorContraction j φ
  set c := b.exteriorContraction i φ
  set d := b.exteriorCreation j φ
  set e := b.exteriorCreation i φ
  have key : ∑ s, ⁅b.exteriorCreation i, b.exteriorContraction j⁆ φ s * φ s =
      ∑ s, (a s * c s - d s * e s) := by
    simp only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, Pi.sub_apply, sub_mul,
      Finset.sum_sub_distrib, b.sum_exteriorCreation_apply_mul]
    congr 1
    rw [Finset.sum_congr rfl fun s _ ↦ mul_comm _ _, ← b.sum_exteriorCreation_apply_mul]
  have hup : ∑ s, 2 * (a s * c s - d s * e s) ≤ ∑ s, (a s ^ 2 + d s ^ 2 + (c s ^ 2 + e s ^ 2)) :=
    Finset.sum_le_sum fun s _ ↦ by nlinarith [sq_nonneg (a s - c s), sq_nonneg (d s + e s)]
  have hlow : -∑ s, (a s ^ 2 + d s ^ 2 + (c s ^ 2 + e s ^ 2)) ≤
      ∑ s, 2 * (a s * c s - d s * e s) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun s _ ↦ by nlinarith [sq_nonneg (a s + c s), sq_nonneg (d s - e s)]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, hi, hj] at hup hlow
  rw [key, abs_le]
  constructor <;> linarith

/-- **The quadratic form of a weighted sum of commutators `⁅εᵢ, ιⱼ⁆` is bounded by the
weights.** For coordinates in an ordered ring and any coefficients `Hᵢⱼ`,
`|⟨∑ᵢⱼ Hᵢⱼ ⁅εᵢ, ιⱼ⁆ φ, φ⟩| ≤ (∑ᵢⱼ |Hᵢⱼ|) |φ|²`, by the triangle inequality and the bound for the
quadratic form of a single commutator. -/
theorem abs_sum_sum_sum_smul_lie_exteriorCreation_exteriorContraction_apply_mul_le
    [LinearOrder R] [IsStrictOrderedRing R] (H : I → I → R) (φ : Finset I → R) :
    |∑ s, (∑ i, ∑ j, H i j • ⁅b.exteriorCreation i, b.exteriorContraction j⁆ φ) s * φ s| ≤
      (∑ i, ∑ j, |H i j|) * ∑ s, φ s ^ 2 := by
  have h : ∑ s, (∑ i, ∑ j, H i j • ⁅b.exteriorCreation i, b.exteriorContraction j⁆ φ) s * φ s =
      ∑ i, ∑ j, H i j * ∑ s, ⁅b.exteriorCreation i, b.exteriorContraction j⁆ φ s * φ s := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
      mul_assoc]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
  rw [h, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (b.abs_sum_lie_exteriorCreation_exteriorContraction_apply_mul_le i j φ) (abs_nonneg _)

end Module.Basis

namespace TauCeti

variable {R V I : Type*} [CommRing R] [AddCommGroup V] [Module R V] [Fintype I] [DecidableEq I]

/-- **A frame identity for creation and contraction operators.** For families `εᵢ`, `ιⱼ` of
operators satisfying the canonical anticommutation relation `εᵢ ιⱼ + ιⱼ εᵢ = δᵢⱼ`, such as
`Module.Basis.exteriorCreation` and `Module.Basis.exteriorContraction`, the double sum of
`εᵢ ιⱼ (Zᵢⱼ + Wᵢⱼ) + ιⱼ εᵢ (Zᵢⱼ - Wᵢⱼ)` is the diagonal `∑ᵢ Zᵢᵢ` plus the commutators
`⁅εᵢ, ιⱼ⁆` applied to `Wᵢⱼ`. -/
theorem sum_creation_contraction_of_anticommutator (ε κ : I → Module.End R V)
    (hcar : ∀ i j, ε i * κ j + κ j * ε i = if i = j then 1 else 0) (Z W : I → I → V) :
    ∑ i, ∑ j, ε i (κ j (Z i j + W i j)) + ∑ i, ∑ j, κ j (ε i (Z i j - W i j)) =
      ∑ i, Z i i + ∑ i, ∑ j, ⁅ε i, κ j⁆ (W i j) := by
  have key : ∀ i j, ε i (κ j (Z i j + W i j)) + κ j (ε i (Z i j - W i j)) =
      (if i = j then Z i j else 0) + ⁅ε i, κ j⁆ (W i j) := by
    intro i j
    have h := congr($(hcar i j) (Z i j))
    simp only [LinearMap.add_apply, mul_apply_eq_comp] at h
    simp only [map_add, map_sub, Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp]
    have h' : (if i = j then Z i j else 0) = ε i (κ j (Z i j)) + κ j (ε i (Z i j)) := by
      rw [h]
      split_ifs <;> simp
    rw [h']
    abel
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib, key, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

end TauCeti
