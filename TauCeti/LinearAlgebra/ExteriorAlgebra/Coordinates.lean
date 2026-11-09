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
(`Module.Basis.exteriorCreation_mul_exteriorContraction_add`), the product `εᵢ ιᵢ` is the
occupation projection onto the coordinates `s` containing `i`
(`Module.Basis.exteriorCreation_mul_exteriorContraction_self_apply`), so the commutator
`⁅εᵢ, ιᵢ⁆` multiplies the coefficient of `s` by `1` if `i ∈ s` and by `-1` otherwise
(`Module.Basis.lie_exteriorCreation_exteriorContraction_self_apply`), and `ιᵢ` is the transpose
of `εᵢ` for the standard pairing of coordinate vectors
(`Module.Basis.sum_exteriorCreation_apply_mul`). Combining the anticommutation relation with
these commutators, a double sum of products `εᵢ ιⱼ` and `ιⱼ εᵢ` reduces to a diagonal term plus
commutators (`TauCeti.sum_creation_contraction_of_anticommutator`). For an orthonormal basis of a
Euclidean space the standard pairing is the induced inner product on `⋀ M`, so `ιᵢ` is the adjoint
of `εᵢ`.

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
theorem exteriorCreation_mul_exteriorContraction_add (i j : I) :
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
  have h := congr($(b.exteriorCreation_mul_exteriorContraction_add i i) φ s)
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
