/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TauCeti.Analysis.Matrix.UnitaryGroup.Basic
import TauCeti.Analysis.Matrix.Eigenvalues.UnitEigenvector
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic
import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Pairs of special unitary matrices with a central commutator

Let `ζ` be a primitive `r`-th root of unity, `r = card n`. This file shows that the twisted
commutator relation `[A, B] = A B A⁻¹ B⁻¹ = ζ • 1` has a solution in `SU(n)`, unique up to
simultaneous conjugation by `SU(n)`. Such pairs are the holonomies of flat `SU(r)`-connections
on the once-punctured torus with central holonomy `ζ` around the puncture, so this is the
statement that the twisted representation space of the torus, the genus-one fixed-determinant
moduli space of rank `r` and degree coprime to `r`, is a single point.

Existence uses the clock and shift matrices. For uniqueness, `A B = ζ • (B A)` says that `B`
maps each eigenvector of `A` to an eigenvector with the eigenvalue multiplied by `ζ`; starting
from a unit eigenvector `v`, the vectors `v, B v, …, B ^ (r - 1) v` are an orthonormal eigenbasis
of `A`, in which `A` is diagonal and `B` is a cyclic shift. The determinant fixes both the
eigenvalues of `A` up to a power of `ζ` and the scalar `B ^ r`, so two solutions have the same
normal form and the change of eigenbasis conjugates one into the other.

## Main results

* `Matrix.coe_commutatorElement_eq_smul_one_iff`: `⁅A, B⁆ = ζ • 1` exactly when `A B = ζ • (B A)`.
* `Matrix.coe_pow_card_eq_of_coe_commutatorElement_eq_smul_one`: for a solution `(A, B)` in
  `SU(n)`, `A ^ r = B ^ r = (-1) ^ (r + 1) • 1`.
* `Matrix.exists_coe_commutatorElement_eq_smul_one`: the twisted relation has a solution in
  `SU(n)`.
* `Matrix.exists_conj_eq_of_coe_commutatorElement_eq_smul_one`: any two solutions are conjugate
  by a single element of `SU(n)`.

## References

* K. Wehrheim and C. Woodward, *Floer field theory for coprime rank and degree*,
  Theorem 3.3.3(c) and Remark 3.3.7.
-/

public section

namespace Matrix

open scoped commutatorElement

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The twisted commutator relation.** For special unitary matrices, the group commutator
`⁅A, B⁆ = A B A⁻¹ B⁻¹` is the scalar matrix `ζ • 1` exactly when `A B = ζ • (B A)`. -/
theorem coe_commutatorElement_eq_smul_one_iff {α : Type*} [CommRing α] [StarRing α]
    {A B : specialUnitaryGroup n α} {ζ : α} :
    ((⁅A, B⁆ : specialUnitaryGroup n α) : Matrix n n α) = ζ • 1 ↔
      (A : Matrix n n α) * B = ζ • ((B : Matrix n n α) * A) := by
  have h : A * B = ⁅A, B⁆ * (B * A) := by rw [commutatorElement_def]; group
  have hc : ((⁅A, B⁆ : specialUnitaryGroup n α) : Matrix n n α) =
      (A : Matrix n n α) * B * star (A : Matrix n n α) * star (B : Matrix n n α) := by
    rw [commutatorElement_def, ← star_eq_inv, ← star_eq_inv]
    simp only [Submonoid.coe_mul, specialUnitaryGroup.coe_star]
  constructor
  · intro hAB
    rw [← Submonoid.coe_mul, h, Submonoid.coe_mul, hAB, smul_one_mul, Submonoid.coe_mul]
  · intro hAB
    rw [hc, hAB, smul_mul_assoc, smul_mul_assoc, mul_assoc (B : Matrix n n α),
      Unitary.mul_star_self_of_mem (specialUnitaryGroup_le_unitaryGroup A.property), mul_one,
      Unitary.mul_star_self_of_mem (specialUnitaryGroup_le_unitaryGroup B.property)]

section Eigenframe

/-! ### The eigenframe of a twisted pair -/

/-- The frame whose columns are `B ^ k v` for `k < card n`, indexed through `Fintype.equivFin`. -/
private noncomputable def eigenframe (B : Matrix n n ℂ) (v : n → ℂ) : Matrix n n ℂ :=
  of fun i k => (B ^ (Fintype.equivFin n k : ℕ) *ᵥ v) i

private theorem eigenframe_mulVec_single (B : Matrix n n ℂ) (v : n → ℂ) (k : n) :
    eigenframe B v *ᵥ Pi.single k 1 = B ^ (Fintype.equivFin n k : ℕ) *ᵥ v := by
  ext i
  simp [eigenframe]

variable {A B : Matrix n n ℂ} {ζ μ : ℂ} {v : n → ℂ}

/-- For a unit eigenvector `v` of `A`, the frame `v, B v, …, B ^ (card n - 1) v` is unitary. -/
private theorem eigenframe_mem_unitaryGroup (hA : A ∈ unitaryGroup n ℂ)
    (hB : B ∈ unitaryGroup n ℂ) (h : A * B = ζ • (B * A))
    (hζ : IsPrimitiveRoot ζ (Fintype.card n)) (hv : A *ᵥ v = μ • v) (hvv : star v ⬝ᵥ v = 1) :
    eigenframe B v ∈ unitaryGroup n ℂ := by
  have hμ : μ ≠ 0 := by
    rintro rfl
    have := star_mulVec_dotProduct_mulVec_of_mem_unitaryGroup hA v v
    simp [hv, hvv] at this
  -- The columns are unit vectors, as `B` is unitary, and eigenvectors of `A` with the pairwise
  -- distinct eigenvalues `μ ζ ^ k`, as `ζ` is a primitive `card n`-th root of unity.
  rw [mem_unitaryGroup_iff']
  ext j k
  have hjk : (star (eigenframe B v) * eigenframe B v) j k =
      star (B ^ (Fintype.equivFin n j : ℕ) *ᵥ v) ⬝ᵥ (B ^ (Fintype.equivFin n k : ℕ) *ᵥ v) := by
    rw [Matrix.mul_apply]
    simp [eigenframe, dotProduct]
  rw [hjk, Matrix.one_apply]
  split_ifs with hjk'
  · subst hjk'
    rw [star_mulVec_dotProduct_mulVec_of_mem_unitaryGroup (pow_mem hB _), hvv]
  · refine star_dotProduct_eq_zero_of_mem_unitaryGroup hA
      (mulVec_pow_mulVec_of_mul_eq_smul_mul h hv _) (mulVec_pow_mulVec_of_mul_eq_smul_mul h hv _)
      fun he => hjk' ?_
    have := hζ.pow_inj (Fintype.equivFin n j).isLt (Fintype.equivFin n k).isLt
      (mul_left_cancel₀ hμ he)
    exact (Fintype.equivFin n).injective (Fin.ext this)

/-- In the eigenframe, `A` is the diagonal matrix with entries `μ ζ ^ k`. -/
private theorem mul_eigenframe (h : A * B = ζ • (B * A)) (hv : A *ᵥ v = μ • v) :
    A * eigenframe B v =
      eigenframe B v * diagonal fun k => μ * ζ ^ (Fintype.equivFin n k : ℕ) := by
  refine ext_of_mulVec_single fun k => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, eigenframe_mulVec_single, diagonal_mulVec_single,
    ← smul_eq_mul _ (1 : ℂ), Pi.single_smul, mulVec_smul, eigenframe_mulVec_single,
    mulVec_pow_mulVec_of_mul_eq_smul_mul h hv]

/-- The matrix form of `Matrix.coe_pow_card_eq_of_coe_commutatorElement_eq_smul_one`: if `A` and
`B` are unitary, `det A = 1` and `A B = ζ • (B A)`, then `A ^ card n = (-1) ^ (card n + 1) • 1`. -/
private theorem pow_card_eq_of_mul_eq_smul_mul {A B : Matrix n n ℂ} {ζ : ℂ}
    (hA : A ∈ unitaryGroup n ℂ) (hB : B ∈ unitaryGroup n ℂ) (hdet : A.det = 1)
    (h : A * B = ζ • (B * A)) (hζ : IsPrimitiveRoot ζ (Fintype.card n)) :
    A ^ Fintype.card n = (-1 : ℂ) ^ (Fintype.card n + 1) • (1 : Matrix n n ℂ) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact Subsingleton.elim _ _
  obtain ⟨μ, v, hv, hvv⟩ := exists_mulVec_eq_smul_and_star_dotProduct_self_eq_one A
  have hU := eigenframe_mem_unitaryGroup hA hB h hζ hv hvv
  have hAU := mul_eigenframe h hv
  have hUunit : IsUnit (eigenframe B v) := Unitary.isUnit_coe (U := ⟨_, hU⟩)
  -- In the eigenframe `A` is diagonal with entries `μ ζ ^ k`, so the determinant pins down
  -- `μ ^ card n` via `∏ ζ ^ k = (-1) ^ (card n + 1)`.
  have hμ : μ ^ Fintype.card n * (-1) ^ (Fintype.card n + 1) = 1 := by
    have hd := congrArg det hAU
    rw [det_mul, det_mul, det_diagonal, hdet, one_mul, mul_comm] at hd
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Equiv.prod_comp (Fintype.equivFin n) fun i : Fin (Fintype.card n) => ζ ^ (i : ℕ),
      Fin.prod_univ_eq_prod_range (fun i => ζ ^ i),
      hζ.prod_range_pow_eq_neg_one_pow Fintype.card_pos] at hd
    exact mul_right_cancel₀ ((isUnit_iff_isUnit_det _).mp hUunit).ne_zero
      (hd.symm.trans (one_mul _).symm)
  have hμ' : μ ^ Fintype.card n = (-1) ^ (Fintype.card n + 1) := by
    have hsign : ((-1 : ℂ) ^ (Fintype.card n + 1)) * (-1) ^ (Fintype.card n + 1) = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨_, rfl⟩
    calc μ ^ Fintype.card n
        = μ ^ Fintype.card n * (-1) ^ (Fintype.card n + 1) * (-1) ^ (Fintype.card n + 1) := by
          rw [mul_assoc, hsign, mul_one]
      _ = (-1) ^ (Fintype.card n + 1) := by rw [hμ, one_mul]
  -- Powers of `A` are diagonal in the eigenframe, and `(μ ζ ^ k) ^ card n = μ ^ card n`.
  have hpow : eigenframe B v * (diagonal fun k => μ * ζ ^ (Fintype.equivFin n k : ℕ)) ^
      Fintype.card n = A ^ Fintype.card n * eigenframe B v :=
    SemiconjBy.pow_right hAU.symm (Fintype.card n)
  have hdiag : ((fun k => μ * ζ ^ (Fintype.equivFin n k : ℕ)) ^ Fintype.card n) =
      fun _ => μ ^ Fintype.card n := by
    ext k
    rw [Pi.pow_apply, mul_pow, ← pow_mul, mul_comm (Fintype.equivFin n k : ℕ), pow_mul,
      hζ.pow_eq_one, one_pow, mul_one]
  rw [diagonal_pow, hdiag, ← smul_one_eq_diagonal, hμ', Matrix.mul_smul, mul_one,
    ← smul_one_mul] at hpow
  exact (hUunit.mul_left_inj.mp hpow).symm

/-- Two twisted pairs with the same scalar `B ^ card n` and unit eigenvectors `v`, `v'` of `A`,
`A'` for the same eigenvalue are conjugate by the unitary matrix `W` sending the eigenframe
`B ^ k v` to the eigenframe `B' ^ k v'`. -/
private theorem exists_unitary_conj_of_eigenframe [Nonempty n] {A B A' B' : Matrix n n ℂ}
    {ζ μ s : ℂ} {v v' : n → ℂ} (hA : A ∈ unitaryGroup n ℂ) (hB : B ∈ unitaryGroup n ℂ)
    (hA' : A' ∈ unitaryGroup n ℂ) (hB' : B' ∈ unitaryGroup n ℂ) (h : A * B = ζ • (B * A))
    (h' : A' * B' = ζ • (B' * A')) (hζ : IsPrimitiveRoot ζ (Fintype.card n))
    (hBs : B ^ Fintype.card n = s • 1) (hB's : B' ^ Fintype.card n = s • 1)
    (hv : A *ᵥ v = μ • v) (hvv : star v ⬝ᵥ v = 1) (hv' : A' *ᵥ v' = μ • v')
    (hvv' : star v' ⬝ᵥ v' = 1) :
    ∃ W ∈ unitaryGroup n ℂ, W * A = A' * W ∧ W * B = B' * W := by
  have hU := eigenframe_mem_unitaryGroup hA hB h hζ hv hvv
  have hU' := eigenframe_mem_unitaryGroup hA' hB' h' hζ hv' hvv'
  generalize hW : eigenframe B' v' * star (eigenframe B v) = W
  refine ⟨W, hW ▸ mul_mem hU' (Unitary.star_mem hU), ?_⟩
  have hWU : W * eigenframe B v = eigenframe B' v' := by
    rw [← hW, mul_assoc, mem_unitaryGroup_iff'.mp hU, mul_one]
  -- `W` sends `B ^ k v` to `B' ^ k v'` for every `k`: for `k < card n` these are the columns of
  -- the two eigenframes, and beyond that both sides are multiplied by the same scalar `s`.
  have hcol (k : ℕ) : W *ᵥ (B ^ k *ᵥ v) = B' ^ k *ᵥ v' := by
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      by_cases hk : k < Fintype.card n
      · obtain ⟨j, hj⟩ : ∃ j, (Fintype.equivFin n j : ℕ) = k :=
          ⟨(Fintype.equivFin n).symm ⟨k, hk⟩, by simp⟩
        rw [← hj, ← eigenframe_mulVec_single, mulVec_mulVec, hWU, eigenframe_mulVec_single]
      · obtain ⟨m, rfl⟩ : ∃ m, k = Fintype.card n + m := ⟨k - Fintype.card n, by omega⟩
        rw [pow_add, pow_add, hBs, hB's, smul_one_mul, smul_one_mul, smul_mulVec, smul_mulVec,
          mulVec_smul, ih m (by have := Fintype.card_pos (α := n); omega)]
  -- Two matrices agreeing on the eigenframe `B ^ k v`, `k < card n`, are equal.
  have hext (X Y : Matrix n n ℂ)
      (hXY : ∀ k : ℕ, X *ᵥ (B ^ k *ᵥ v) = Y *ᵥ (B ^ k *ᵥ v)) : X = Y := by
    have hXYU : X * eigenframe B v = Y * eigenframe B v := ext_of_mulVec_single fun k => by
      rw [← mulVec_mulVec, ← mulVec_mulVec, eigenframe_mulVec_single, hXY]
    exact (Unitary.isUnit_coe (U := ⟨_, hU⟩)).mul_left_inj.mp hXYU
  refine ⟨hext _ _ fun k => ?_, hext _ _ fun k => ?_⟩
  · rw [← mulVec_mulVec, ← mulVec_mulVec, mulVec_pow_mulVec_of_mul_eq_smul_mul h hv, mulVec_smul,
      hcol, mulVec_pow_mulVec_of_mul_eq_smul_mul h' hv']
  · have hsucc (C : Matrix n n ℂ) (x : n → ℂ) : C *ᵥ (C ^ k *ᵥ x) = C ^ (k + 1) *ᵥ x := by
      rw [mulVec_mulVec, ← pow_succ']
    rw [← mulVec_mulVec, ← mulVec_mulVec, hsucc, hcol, hcol, hsucc]

end Eigenframe

/-- **The `r`-th powers of a twisted pair.** If `A, B ∈ SU(n)` satisfy `⁅A, B⁆ = ζ • 1` for a
primitive `r`-th root of unity `ζ`, `r = card n`, then `A ^ r` and `B ^ r` are both the scalar
matrix `(-1) ^ (r + 1) • 1`. -/
theorem coe_pow_card_eq_of_coe_commutatorElement_eq_smul_one {A B : specialUnitaryGroup n ℂ}
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Fintype.card n))
    (h : ((⁅A, B⁆ : specialUnitaryGroup n ℂ) : Matrix n n ℂ) = ζ • 1) :
    (A : Matrix n n ℂ) ^ Fintype.card n = (-1 : ℂ) ^ (Fintype.card n + 1) • (1 : Matrix n n ℂ) ∧
      (B : Matrix n n ℂ) ^ Fintype.card n =
        (-1 : ℂ) ^ (Fintype.card n + 1) • (1 : Matrix n n ℂ) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hAB := coe_commutatorElement_eq_smul_one_iff.mp h
  have hζ0 : ζ ≠ 0 := hζ.ne_zero Fintype.card_ne_zero
  have hBA : (B : Matrix n n ℂ) * A = ζ⁻¹ • ((A : Matrix n n ℂ) * B) := by
    rw [hAB, smul_smul, inv_mul_cancel₀ hζ0, one_smul]
  have hA := specialUnitaryGroup_le_unitaryGroup A.property
  have hB := specialUnitaryGroup_le_unitaryGroup B.property
  exact ⟨pow_card_eq_of_mul_eq_smul_mul hA hB (mem_specialUnitaryGroup_iff.mp A.property).2
    hAB hζ, pow_card_eq_of_mul_eq_smul_mul hB hA (mem_specialUnitaryGroup_iff.mp B.property).2
    hBA hζ.inv⟩

/-- **Existence of twisted pairs.** For a primitive `r`-th root of unity `ζ`, `r = card n`, there
are `A, B ∈ SU(n)` with `⁅A, B⁆ = ζ • 1`: suitable scalar multiples of the shift matrix
`e_k ↦ e_(k-1)` and the clock matrix `diag(1, ζ, …, ζ ^ (r - 1))`. -/
theorem exists_coe_commutatorElement_eq_smul_one {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (Fintype.card n)) :
    ∃ A B : specialUnitaryGroup n ℂ,
      ((⁅A, B⁆ : specialUnitaryGroup n ℂ) : Matrix n n ℂ) = ζ • 1 := by
  set e := Fintype.equivFin n
  let π : Equiv.Perm n := (e.trans (finRotate _)).trans e.symm
  -- The clock exponent increases by one along the cyclic permutation `π`.
  have hπ (i : n) : ζ ^ (e (π i) : ℕ) = ζ * ζ ^ (e i : ℕ) := by
    have : Nonempty n := ⟨i⟩
    have : NeZero (Fintype.card n) := ⟨Fintype.card_ne_zero⟩
    simp only [π, Equiv.trans_apply, Equiv.apply_symm_apply, finRotate_apply, Fin.val_add,
      Fin.val_one']
    rw [← pow_eq_pow_mod _ hζ.pow_eq_one, pow_add, ← pow_eq_pow_mod _ hζ.pow_eq_one, pow_one,
      mul_comm]
  have hPC : π.permMatrix ℂ * diagonal (fun i => ζ ^ (e i : ℕ)) =
      ζ • (diagonal (fun i => ζ ^ (e i : ℕ)) * π.permMatrix ℂ) := by
    ext i j
    rw [mul_diagonal, Matrix.smul_apply, diagonal_mul]
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply]
    split_ifs with hij
    · rw [hij, hπ, smul_eq_mul]
      ring
    · simp
  have hP : π.permMatrix ℂ ∈ unitaryGroup n ℂ := permMatrix_mem_unitary π
  have hC : diagonal (fun i => ζ ^ (e i : ℕ)) ∈ unitaryGroup n ℂ := by
    refine diagonal_mem_unitary.mpr (Pi.mem_unitary_iff.mpr fun i => pow_mem ?_ _)
    have : Nonempty n := ⟨i⟩
    exact Circle.coe_mem_unitary
      ⟨ζ, mem_sphere_zero_iff_norm.mpr (hζ.norm'_eq_one Fintype.card_ne_zero)⟩
  obtain ⟨a, ha⟩ := exists_circle_smul_mem_specialUnitaryGroup ⟨_, hP⟩
  obtain ⟨b, hb⟩ := exists_circle_smul_mem_specialUnitaryGroup ⟨_, hC⟩
  refine ⟨⟨_, ha⟩, ⟨_, hb⟩, coe_commutatorElement_eq_smul_one_iff.mpr ?_⟩
  simp only [smul_mul_smul_comm, hPC, smul_smul, mul_comm]

/-- **Uniqueness of twisted pairs.** For a primitive `r`-th root of unity `ζ`, `r = card n`, any two
pairs `(A, B)`, `(A', B')` in `SU(n)` with `⁅A, B⁆ = ⁅A', B'⁆ = ζ • 1` are conjugate by a single
element of `SU(n)`. -/
theorem exists_conj_eq_of_coe_commutatorElement_eq_smul_one {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (Fintype.card n)) {A B A' B' : specialUnitaryGroup n ℂ}
    (h : ((⁅A, B⁆ : specialUnitaryGroup n ℂ) : Matrix n n ℂ) = ζ • 1)
    (h' : ((⁅A', B'⁆ : specialUnitaryGroup n ℂ) : Matrix n n ℂ) = ζ • 1) :
    ∃ g : specialUnitaryGroup n ℂ, g * A * g⁻¹ = A' ∧ g * B * g⁻¹ = B' := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have : NeZero (Fintype.card n) := ⟨Fintype.card_ne_zero⟩
  have hA := specialUnitaryGroup_le_unitaryGroup A.property
  have hB := specialUnitaryGroup_le_unitaryGroup B.property
  have hA' := specialUnitaryGroup_le_unitaryGroup A'.property
  have hB' := specialUnitaryGroup_le_unitaryGroup B'.property
  obtain ⟨hAr, hBr⟩ := coe_pow_card_eq_of_coe_commutatorElement_eq_smul_one hζ h
  obtain ⟨hA'r, hB'r⟩ := coe_pow_card_eq_of_coe_commutatorElement_eq_smul_one hζ h'
  have hAB := coe_commutatorElement_eq_smul_one_iff.mp h
  -- Unit eigenvectors of `A` and `A'`; their eigenvalues are `card n`-th roots of the same sign.
  obtain ⟨μ, v, hv, hvv⟩ := exists_mulVec_eq_smul_and_star_dotProduct_self_eq_one (A : Matrix n n ℂ)
  obtain ⟨μ', v', hv', hvv'⟩ :=
    exists_mulVec_eq_smul_and_star_dotProduct_self_eq_one (A' : Matrix n n ℂ)
  have hne {x : n → ℂ} (hxx : star x ⬝ᵥ x = 1) : x ≠ 0 := by rintro rfl; simp at hxx
  have hμ := pow_eq_of_pow_eq_smul_one_of_mulVec_eq_smul hAr hv (hne hvv)
  have hsign : (-1 : ℂ) ^ (Fintype.card n + 1) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow Fintype.card_ne_zero] at hμ
    exact hsign hμ.symm
  -- Shift `v` along `B` until its eigenvalue is `μ'`.
  obtain ⟨m, -, hm⟩ := hζ.eq_pow_of_pow_eq_one (ξ := μ' / μ)
    (by rw [div_pow, hμ, pow_eq_of_pow_eq_smul_one_of_mulVec_eq_smul hA'r hv' (hne hvv'),
      div_self hsign])
  have hv₁ : (A : Matrix n n ℂ) *ᵥ ((B : Matrix n n ℂ) ^ m *ᵥ v) =
      μ' • ((B : Matrix n n ℂ) ^ m *ᵥ v) := by
    rw [mulVec_pow_mulVec_of_mul_eq_smul_mul hAB hv, hm, mul_div_cancel₀ _ hμ0]
  have hvv₁ : star ((B : Matrix n n ℂ) ^ m *ᵥ v) ⬝ᵥ ((B : Matrix n n ℂ) ^ m *ᵥ v) = 1 := by
    rw [star_mulVec_dotProduct_mulVec_of_mem_unitaryGroup (pow_mem hB m), hvv]
  obtain ⟨W, hW, hWA, hWB⟩ := exists_unitary_conj_of_eigenframe hA hB hA' hB' hAB
    (coe_commutatorElement_eq_smul_one_iff.mp h') hζ hBr hB'r hv₁ hvv₁ hv' hvv'
  -- Rescale `W` into `SU(n)`; conjugation does not see the scalar.
  obtain ⟨c, hc⟩ := exists_circle_smul_mem_specialUnitaryGroup ⟨W, hW⟩
  refine ⟨⟨_, hc⟩, ?_, ?_⟩ <;> rw [mul_inv_eq_iff_eq_mul] <;> apply Subtype.ext
  · simp only [Submonoid.coe_mul, smul_mul_assoc, mul_smul_comm, hWA]
  · simp only [Submonoid.coe_mul, smul_mul_assoc, mul_smul_comm, hWB]

end Matrix
