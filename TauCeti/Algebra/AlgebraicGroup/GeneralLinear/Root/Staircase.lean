/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Base
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Vector

/-!
# The staircase character of the general linear group

For the diagonal torus of `GL_(n+1)`, with the upper-triangular positive roots `e_i - e_j`
(`i < j`) of `TauCeti.GeneralLinear.diagonalRootBase`, the half-sum of the positive roots is

```text
ρ = (n/2, n/2 - 1, …, -n/2),
```

which is not a character when `n` is odd. The **staircase** `δ = (n, n - 1, …, 0)` is a character,
and it pairs to `1` with every simple coroot, as `ρ` does. The two differ by `n/2` times the
determinant character `(1, …, 1)`, which the Weyl group fixes. This file computes the sum of the
positive roots, `2ρ = (n, n - 2, …, -n)`, and so `2δ - 2ρ = (n, …, n)`. Consequently the staircase
moves under the Weyl group exactly as `ρ` does,
`w δ - δ = -∑_{α > 0, w⁻¹ α < 0} α`, and the shifted Weyl action `x ↦ w (x + δ) - δ` is the dot
action `x ↦ w (x + ρ) - ρ`, written without fractional characters.

## Main declarations

* `TauCeti.GeneralLinear.diagonalStaircase`: the staircase character `δ = (n, n - 1, …, 0)` of the
  diagonal torus of `GL_(n+1)`.
* `TauCeti.GeneralLinear.coroot'_diagonalStaircase`: `δ` pairs to `1` with every simple coroot.
* `TauCeti.GeneralLinear.twoWeylVector_diagonalRootBase_apply`: the sum of the positive roots is
  `2ρ = (n, n - 2, …, -n)`, so `2δ - 2ρ` is the constant character with value `n`.
* `TauCeti.GeneralLinear.smul_diagonalStaircase_sub_diagonalStaircase`: a Weyl-group element `w`
  moves `δ` by `-∑_{α > 0, w⁻¹ α < 0} α`, the shift of `ρ`.
* `TauCeti.GeneralLinear.smul_add_diagonalStaircase_sub_diagonalStaircase`: the `δ`-shifted Weyl
  action `w (x + δ) - δ` is `w x - ∑_{α > 0, w⁻¹ α < 0} α`, the integral form of the dot action.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate I, for the positive roots and
  the half-sum `ρ` in type `A_n`.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Ch. I, §3, for the
  staircase `δ` and the bialternant formula `s_λ = a_{λ + δ} / a_δ`, in which `δ` plays the role
  of `ρ`.
-/

public section

open RootPairing

namespace TauCeti.GeneralLinear

universe u

noncomputable section

/-- **The staircase character** `δ = (n, n - 1, …, 0)` of the diagonal torus of `GL_(n+1)`: its
coordinate at `a` is `n - a`. -/
noncomputable def diagonalStaircase (n : ℕ) : ULift.{u} (Fin (n + 1)) →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm fun a ↦ (n : ℤ) - (a.down : ℕ)

/-- The coordinate of the staircase character at `a` is `n - a`. -/
@[simp]
theorem diagonalStaircase_apply (n : ℕ) (a : ULift.{u} (Fin (n + 1))) :
    diagonalStaircase n a = (n : ℤ) - (a.down : ℕ) := by
  rw [diagonalStaircase, Finsupp.coe_equivFunOnFinite_symm]

/-- **The staircase pairs to `1` with every simple coroot**, as the Weyl vector does: consecutive
coordinates of `δ` differ by `1`. -/
theorem coroot'_diagonalStaircase (n : ℕ) {p : DiagonalRootIndex.{u} (n + 1)}
    (hp : p ∈ (diagonalRootBase.{u} n).support) :
    (diagonalRootDatum (n + 1)).coroot' p (diagonalStaircase n) = 1 := by
  obtain ⟨i, rfl⟩ := (mem_diagonalRootBase_support n p).1 hp
  rw [diagonalRootDatum_coroot'_apply]
  simp [Fin.val_succ]

/-- A character killed by every simple coroot has all its coordinates equal. -/
private theorem apply_eq_apply_zero_of_forall_coroot'_eq_zero (n : ℕ)
    {x : ULift.{u} (Fin (n + 1)) →₀ ℤ}
    (hx : ∀ p ∈ (diagonalRootBase.{u} n).support, (diagonalRootDatum (n + 1)).coroot' p x = 0)
    (a : ULift.{u} (Fin (n + 1))) : x a = x (ULift.up 0) := by
  obtain ⟨a⟩ := a
  induction a using Fin.induction with
  | zero => rfl
  | succ i ih =>
    have h := hx _ ((mem_diagonalRootBase_support n _).2 ⟨i, rfl⟩)
    rw [diagonalRootDatum_coroot'_apply] at h
    simp only [diagonalSimpleRootIndex_fst, diagonalSimpleRootIndex_snd] at h
    rw [← ih]
    omega

/-- The coordinates of the sum of the positive roots add up to `0`, since those of each root
`e_i - e_j` do. -/
private theorem sum_twoWeylVector_diagonalRootBase_apply (n : ℕ) :
    ∑ a, twoWeylVector (diagonalRootDatum.{u} (n + 1)) (diagonalRootBase n) a = 0 := by
  classical
  rw [twoWeylVector_def]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun p _ ↦ ?_
  simp [diagonalRootDatum_root, diagonalRoot_apply, Finset.sum_sub_distrib]

/-- Twice the sum of the coordinates of the staircase is `n (n + 1)`. -/
private theorem two_mul_sum_diagonalStaircase_apply (n : ℕ) :
    2 * ∑ a, diagonalStaircase.{u} n a = n * (n + 1) := by
  simp only [diagonalStaircase_apply]
  rw [← Equiv.ulift.symm.sum_comp]
  simp only [Equiv.ulift_symm_apply]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ (n : ℤ) - i), Finset.sum_sub_distrib]
  have h : ((∑ i ∈ Finset.range (n + 1), i : ℕ) : ℤ) * 2 = (n + 1) * n := by
    exact_mod_cast Finset.sum_range_id_mul_two (n + 1)
  push_cast at h
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  linear_combination -h

/-- The staircase and the Weyl vector differ by a multiple of the determinant: every coordinate
of `2δ - 2ρ` is `n`. -/
private theorem two_smul_diagonalStaircase_sub_twoWeylVector_apply (n : ℕ)
    (a : ULift.{u} (Fin (n + 1))) :
    ((2 : ℤ) • diagonalStaircase n -
      twoWeylVector (diagonalRootDatum.{u} (n + 1)) (diagonalRootBase n)) a = n := by
  -- `z = 2δ - 2ρ` is killed by the simple coroots, hence constant, and the sum of its
  -- coordinates is `n (n + 1)`.
  set z := (2 : ℤ) • diagonalStaircase n -
      twoWeylVector (diagonalRootDatum.{u} (n + 1)) (diagonalRootBase n)
  have hz : ∀ p ∈ (diagonalRootBase.{u} n).support,
      (diagonalRootDatum (n + 1)).coroot' p z = 0 := fun _ hp ↦
    coroot'_two_smul_sub_twoWeylVector_eq_zero _ _ hp (coroot'_diagonalStaircase n hp)
  have hconst := apply_eq_apply_zero_of_forall_coroot'_eq_zero n hz
  have hsum : ∑ b, z b = (n + 1) * z (ULift.up 0) := by
    rw [Finset.sum_congr rfl fun b _ ↦ hconst b, Finset.sum_const, Finset.card_univ,
      Fintype.card_ulift, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hsum' : ∑ b, z b = n * (n + 1) := by
    simp only [z, Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_sub_distrib, ← Finset.mul_sum, sum_twoWeylVector_diagonalRootBase_apply,
      sub_zero]
    exact two_mul_sum_diagonalStaircase_apply n
  rw [hconst a]
  apply mul_left_cancel₀ (by positivity : (n : ℤ) + 1 ≠ 0)
  rw [← hsum, hsum']
  ring

/-- **The sum of the positive roots of `GL_(n+1)`** is `2ρ = (n, n - 2, …, -n)`: its coordinate at
`a` is `n - 2a`. Thus `2δ - 2ρ` is the constant character `(n, …, n)`, and by
`TauCeti.smul_two_smul_sub_twoWeylVector_of_forall_coroot'_eq_one` it is fixed by the Weyl
group. -/
theorem twoWeylVector_diagonalRootBase_apply (n : ℕ) (a : ULift.{u} (Fin (n + 1))) :
    twoWeylVector (diagonalRootDatum.{u} (n + 1)) (diagonalRootBase n) a =
      n - 2 * (a.down : ℕ) := by
  have h := two_smul_diagonalStaircase_sub_twoWeylVector_apply n a
  rw [Finsupp.sub_apply, Finsupp.smul_apply, diagonalStaircase_apply, smul_eq_mul] at h
  linear_combination -h

/-- **The staircase moves under the Weyl group as the Weyl vector does**:
`w δ - δ = -∑_{α > 0, w⁻¹ α < 0} α`. -/
theorem smul_diagonalStaircase_sub_diagonalStaircase (n : ℕ)
    (w : (diagonalRootDatum.{u} (n + 1)).weylGroup) :
    w • diagonalStaircase n - diagonalStaircase n =
      -∑ i ∈ inversionsFinset (diagonalRootDatum (n + 1)) (diagonalRootBase n) w⁻¹,
        (diagonalRootDatum (n + 1)).root i :=
  smul_sub_eq_neg_sum_inversionsFinset_of_forall_coroot'_eq_one _ _
    (fun _ hp ↦ coroot'_diagonalStaircase n hp) (IsSMulRegular.of_ne_zero two_ne_zero) w

/-- **The staircase-shifted Weyl action is the dot action**: `w (x + δ) - δ` is
`w x - ∑_{α > 0, w⁻¹ α < 0} α`, which is `w (x + ρ) - ρ` computed without leaving the character
lattice. -/
theorem smul_add_diagonalStaircase_sub_diagonalStaircase (n : ℕ)
    (w : (diagonalRootDatum.{u} (n + 1)).weylGroup) (x : ULift.{u} (Fin (n + 1)) →₀ ℤ) :
    w • (x + diagonalStaircase n) - diagonalStaircase n =
      w • x - ∑ i ∈ inversionsFinset (diagonalRootDatum (n + 1)) (diagonalRootBase n) w⁻¹,
        (diagonalRootDatum (n + 1)).root i := by
  rw [smul_add, add_sub_assoc, smul_diagonalStaircase_sub_diagonalStaircase, sub_eq_add_neg]

end

end TauCeti.GeneralLinear
