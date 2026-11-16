/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.GaugeModuli.RelationModel.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Topology.Homeomorph.Lemmas
import TauCeti.Analysis.Matrix.Normal
import TauCeti.Analysis.Matrix.UnitaryGroup.Basic
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic

/-!
# Genus-one coprime `SU(r)` moduli and clock–shift normal form

Let `ζ : ℂ` be a primitive `r`-th root of unity. At genus one, the twisted relation
`⁅A, B⁆ = ζ • 1` in `SU(r)` is equivalent to the Weyl commutation relation `A * B = ζ • (B * A)`.
Rescaling the unitary clock matrix `C₀ = diag(1, ζ, …, ζ^{r-1})` and cyclic shift matrix `S₀` into
`SU(r)` yields an explicit solution, and every solution in `SU(r)` is simultaneously
`SU(r)`-conjugate to this clock–shift pair. Consequently, the genus-one representation model
`relationModuli r ζ 1` is a single point (`TauCeti.GaugeModuli.relationModuli_genus_one`), hence
simply connected, and the effective `PSU(r)` action identifies `PSU(r)` homeomorphically with
`relationSet r ζ 1` (`TauCeti.GaugeModuli.psuOrbitHomeomorphGenusOne`).

As immediate consequences we also deduce nonemptiness of `relationSet r ζ g` and
`relationModuli r ζ g` for every positive genus `g ≥ 1`, triviality of the central-twist
`H¹(T²; μ_r)` action at genus one, and explicit rank-two checks: for `r = 2`, `ζ = -1`, the
Pauli-type pair `A = diag(i, -i)`, `B = !![0, 1; -1, 0]` satisfies `⁅A, B⁆ = -1`, `B A B⁻¹ = -A`,
and `A B A⁻¹ = -B` (witnessing non-freeness of the `H¹(X; ℤ/2)` action), whereas at the
non-coprime parameter `r = 2`, `ζ = 1`, `g = 1` the moduli is not a subsingleton and admits
non-central stabilizers.

## Main definitions

* `TauCeti.GaugeModuli.psuOrbitHomeomorphGenusOne`: for a primitive `r`-th root of unity `ζ`
  and any basepoint `x₀ : relationSet r ζ 1`, the orbit homeomorphism
  `PSU(r) ≃ₜ relationSet r ζ 1`.
* `TauCeti.GaugeModuli.rankTwoClock` and `TauCeti.GaugeModuli.rankTwoShift`: the explicit `SU(2)`
  witness pair `diag(i, -i)` and `!![0, 1; -1, 0]` for `r = 2`, `ζ = -1`.

## Main results

* `TauCeti.GaugeModuli.nonempty_relationSet_genus_one` and
  `TauCeti.GaugeModuli.relationModuli_genus_one`: existence and uniqueness up to simultaneous
  `SU(r)`-conjugation of a solution to `⁅A, B⁆ = ζ • 1`.
* `TauCeti.GaugeModuli.simplyConnectedSpace_relationModuli_genus_one`: simple connectivity of the
  genus-one moduli.
* `TauCeti.GaugeModuli.nonempty_relationSet_of_pos` and
  `TauCeti.GaugeModuli.nonempty_relationModuli_of_pos`: nonemptiness of the relation set and moduli
  for every genus `g ≥ 1`.
* `TauCeti.GaugeModuli.centerTwist_smul_relationModuli_genus_one`: the central-twist action is
  trivial at genus one.
* `TauCeti.GaugeModuli.rankTwoPair_mem_relationSet`,
  `TauCeti.GaugeModuli.exists_ne_one_centerTwist_fix_rankTwo_genus_one`, and
  `TauCeti.GaugeModuli.not_subsingleton_relationModuli_two_one_one`: explicit rank-two checks
  for `ζ = -1` and the non-coprime contrast `ζ = 1`.

## References

* Katrin Wehrheim and Chris T. Woodward, *Floer field theory for coprime rank and degree*,
  arXiv:1601.04924, §3 (Theorem 3.3.3(c) and Remark 3.3.7).
* Aliakbar Daemi, Kenji Fukaya, and Maksim Lipyanskiy, *Lagrangians, SO(3)-instantons and the
  Atiyah–Floer conjecture*, arXiv:2109.07032, Remark 2.2 and Lemma 2.43.
-/

public section

open Matrix Matrix.specialUnitaryGroup
open scoped commutatorElement

namespace TauCeti

namespace GaugeModuli

section ClockAndShift

/-- The unitary clock matrix `C₀ = diag(1, ζ, …, ζ^{r-1}) ∈ U(r)`. -/
private def clockUnitary {r : ℕ} [NeZero r] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r) :
    Matrix.unitaryGroup (Fin r) ℂ :=
  ⟨Matrix.diagonal fun k : Fin r => ζ ^ (k : ℕ), by
    have hζu : ζ ∈ unitary ℂ :=
      Circle.coe_mem_unitary ⟨ζ, mem_sphere_zero_iff_norm.mpr (hζ.norm'_eq_one (NeZero.ne r))⟩
    rw [Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
    exact fun k => Submonoid.pow_mem _ hζu k.val⟩

/-- The unitary cyclic shift matrix `S₀ ∈ U(r)` sending `e_j ↦ e_{j + 1}`. -/
private def shiftUnitary (r : ℕ) [NeZero r] : Matrix.unitaryGroup (Fin r) ℂ :=
  Matrix.permutationUnitary (R := ℂ) (Equiv.addRight (1 : Fin r))

/-- Entry formula for the cyclic shift matrix: `(S₀) i j = 1` iff `i = j + 1`. -/
private theorem shiftUnitary_apply (r : ℕ) [NeZero r] (i j : Fin r) :
    (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ) i j = if i = j + 1 then 1 else 0 := by
  simp only [shiftUnitary, Matrix.coe_permutationUnitary, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Equiv.Perm.inv_def, Option.mem_def,
    Option.some.injEq]
  simp [add_neg_eq_iff_eq_add]

/-- The Weyl commutation relation `C₀ * S₀ = ζ • (S₀ * C₀)` for the clock and shift matrices. -/
private theorem clock_mul_shift {r : ℕ} [NeZero r] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r) :
    (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ) * (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ) =
      ζ • ((shiftUnitary r : Matrix (Fin r) (Fin r) ℂ) *
        (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ)) := by
  ext i j
  simp only [clockUnitary, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul,
    shiftUnitary_apply]
  split_ifs with h
  · subst h
    have hval : ((j + 1 : Fin r) : ℕ) = (j.val + 1) % r := by
      rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (NeZero.ne r)) with hr1 | hr1
      · subst hr1; simp
      · simp [Fin.val_add, Nat.mod_eq_of_lt hr1]
    have hpow : ζ ^ ((j.val + 1) % r) = ζ ^ (j.val + 1) :=
      (congrArg (fun n => ζ ^ ((j.val + 1) % n)) hζ.eq_orderOf).trans (pow_mod_orderOf _ _)
    rw [hval, hpow, pow_succ', mul_one, one_mul]
  · simp

/-- Existence of rescaled clock and shift matrices `A₀ = c₁ • C₀`, `B₀ = c₂ • S₀` in `SU(r)`
satisfying `⁅A₀, B₀⁆ = ζ • 1`. -/
private theorem exists_clock_shift_su {r : ℕ} [NeZero r] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r) :
    ∃ (c₁ c₂ : Circle) (A₀ B₀ : Matrix.specialUnitaryGroup (Fin r) ℂ),
      (A₀ : Matrix (Fin r) (Fin r) ℂ) = (c₁ : ℂ) • (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ) ∧
      (B₀ : Matrix (Fin r) (Fin r) ℂ) = (c₂ : ℂ) • (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ) ∧
      ((⁅A₀, B₀⁆ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = ζ • 1 := by
  obtain ⟨c₁, hc₁⟩ := Matrix.exists_circle_smul_mem_specialUnitaryGroup (clockUnitary hζ)
  obtain ⟨c₂, hc₂⟩ := Matrix.exists_circle_smul_mem_specialUnitaryGroup (shiftUnitary r)
  let A₀ : Matrix.specialUnitaryGroup (Fin r) ℂ := ⟨_, hc₁⟩
  let B₀ : Matrix.specialUnitaryGroup (Fin r) ℂ := ⟨_, hc₂⟩
  refine ⟨c₁, c₂, A₀, B₀, rfl, rfl, ?_⟩
  have hAB : (A₀ : Matrix (Fin r) (Fin r) ℂ) * (B₀ : Matrix (Fin r) (Fin r) ℂ) =
      ζ • ((B₀ : Matrix (Fin r) (Fin r) ℂ) * (A₀ : Matrix (Fin r) (Fin r) ℂ)) := by
    dsimp only [A₀, B₀]
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, clock_mul_shift hζ,
      smul_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  have hAA : (A₀ : Matrix (Fin r) (Fin r) ℂ) *
      ((A₀⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = 1 :=
    congrArg Subtype.val (mul_inv_cancel A₀)
  have hBB : (B₀ : Matrix (Fin r) (Fin r) ℂ) *
      ((B₀⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = 1 :=
    congrArg Subtype.val (mul_inv_cancel B₀)
  rw [commutatorElement_def]
  simp only [Submonoid.coe_mul]
  rw [hAB, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc (B₀ : Matrix (Fin r) (Fin r) ℂ),
    hAA, Matrix.mul_one, hBB]

/-- Iterated conjugation of `S₀` by `C₀^n` multiplies `S₀` by `ζ^n`. -/
private theorem clock_pow_conj_shift {r : ℕ} [NeZero r] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    (n : ℕ) :
    (((clockUnitary hζ) ^ n : Matrix.unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
        (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ) *
        star (((clockUnitary hζ) ^ n : Matrix.unitaryGroup (Fin r) ℂ) :
          Matrix (Fin r) (Fin r) ℂ) =
      ζ ^ n • (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ) := by
  set C := clockUnitary hζ
  set S := shiftUnitary r
  have hSCinv : (C : Matrix (Fin r) (Fin r) ℂ) * (S : Matrix (Fin r) (Fin r) ℂ) *
      star (C : Matrix (Fin r) (Fin r) ℂ) = ζ • (S : Matrix (Fin r) (Fin r) ℂ) := by
    rw [clock_mul_shift hζ, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff.mp C.2,
      Matrix.mul_one]
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ((C ^ (n + 1) : Matrix.unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
        (C : Matrix (Fin r) (Fin r) ℂ) *
          ((C ^ n : Matrix.unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
      rw [pow_succ']
      rfl
    rw [h1, star_mul]
    calc
      (C : Matrix (Fin r) (Fin r) ℂ) * ((C ^ n : Matrix.unitaryGroup (Fin r) ℂ) :
          Matrix (Fin r) (Fin r) ℂ) * (S : Matrix (Fin r) (Fin r) ℂ) *
          (star ((C ^ n : Matrix.unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
            star (C : Matrix (Fin r) (Fin r) ℂ))
        = (C : Matrix (Fin r) (Fin r) ℂ) *
            (((C ^ n : Matrix.unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
              (S : Matrix (Fin r) (Fin r) ℂ) *
              star ((C ^ n : Matrix.unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) *
            star (C : Matrix (Fin r) (Fin r) ℂ) := by simp only [Matrix.mul_assoc]
      _ = ζ ^ (n + 1) • (S : Matrix (Fin r) (Fin r) ℂ) := by
            rw [ih, Matrix.mul_smul, Matrix.smul_mul, hSCinv, smul_smul, pow_succ]

/-- Iterated conjugation of `C₀` by `(S₀⁻¹)^n` multiplies `C₀` by `ζ^n`. -/
private theorem shift_inv_pow_conj_clock {r : ℕ} [NeZero r] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    (n : ℕ) :
    ((((shiftUnitary r)⁻¹) ^ n : Matrix.unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
        (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ) *
        star ((((shiftUnitary r)⁻¹) ^ n : Matrix.unitaryGroup (Fin r) ℂ) :
          Matrix (Fin r) (Fin r) ℂ) =
      ζ ^ n • (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ) := by
  set C := clockUnitary hζ
  set S := shiftUnitary r
  have hSinvC : star (S : Matrix (Fin r) (Fin r) ℂ) * (C : Matrix (Fin r) (Fin r) ℂ) *
      (S : Matrix (Fin r) (Fin r) ℂ) = ζ • (C : Matrix (Fin r) (Fin r) ℂ) := by
    rw [Matrix.mul_assoc, clock_mul_shift hζ, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mem_unitaryGroup_iff'.mp S.2, Matrix.one_mul]
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (((S⁻¹) ^ (n + 1) : Matrix.unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
        star (S : Matrix (Fin r) (Fin r) ℂ) *
          (((S⁻¹) ^ n : Matrix.unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
      rw [pow_succ']
      rfl
    rw [h1, star_mul, star_star]
    calc
      star (S : Matrix (Fin r) (Fin r) ℂ) *
          (((S⁻¹) ^ n : Matrix.unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
          (C : Matrix (Fin r) (Fin r) ℂ) *
          (star (((S⁻¹) ^ n : Matrix.unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
            (S : Matrix (Fin r) (Fin r) ℂ))
        = star (S : Matrix (Fin r) (Fin r) ℂ) *
            ((((S⁻¹) ^ n : Matrix.unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
              (C : Matrix (Fin r) (Fin r) ℂ) *
              star (((S⁻¹) ^ n : Matrix.unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) *
            (S : Matrix (Fin r) (Fin r) ℂ) := by simp only [Matrix.mul_assoc]
      _ = ζ ^ (n + 1) • (C : Matrix (Fin r) (Fin r) ℂ) := by
            rw [ih, Matrix.mul_smul, Matrix.smul_mul, hSinvC, smul_smul, pow_succ]

/-- Conjugating `α • C₀` and `b • S₀` by `P = C₀^q * (S₀⁻¹)^p` shifts them by `ζ^p` and `ζ^q`. -/
private theorem clock_shift_phase_conj {r : ℕ} [NeZero r] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    (p q : ℕ) (α b : ℂ) :
    let P : Matrix.unitaryGroup (Fin r) ℂ := (clockUnitary hζ) ^ q * ((shiftUnitary r)⁻¹) ^ p
    (P : Matrix (Fin r) (Fin r) ℂ) * (α • (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ)) *
        star (P : Matrix (Fin r) (Fin r) ℂ) =
      (ζ ^ p * α) • (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ) ∧
    (P : Matrix (Fin r) (Fin r) ℂ) * (b • (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ)) *
        star (P : Matrix (Fin r) (Fin r) ℂ) =
      (ζ ^ q * b) • (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ) := by
  intro P
  set C := clockUnitary hζ
  set S := shiftUnitary r
  have hCcomm : ((C ^ q : Matrix.unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
      (C : Matrix (Fin r) (Fin r) ℂ) *
      star ((C ^ q : Matrix.unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      (C : Matrix (Fin r) (Fin r) ℂ) :=
    congrArg Subtype.val (by rw [← pow_succ, pow_succ', mul_inv_cancel_right] :
      (C ^ q : Matrix.unitaryGroup (Fin r) ℂ) * C * (C ^ q)⁻¹ = C)
  have hScomm : (((S⁻¹) ^ p : Matrix.unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
      (S : Matrix (Fin r) (Fin r) ℂ) *
      star (((S⁻¹) ^ p : Matrix.unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      (S : Matrix (Fin r) (Fin r) ℂ) := by
    have hc : Commute ((S⁻¹) ^ p) S := (Commute.inv_left (Commute.refl S)).pow_left p
    exact congrArg Subtype.val (by rw [hc.eq, mul_inv_cancel_right] :
      ((S⁻¹) ^ p : Matrix.unitaryGroup (Fin r) ℂ) * S * ((S⁻¹) ^ p)⁻¹ = S)
  have hassoc (X Y M : Matrix (Fin r) (Fin r) ℂ) :
      (X * Y) * M * (star Y * star X) = X * (Y * M * star Y) * star X := by
    simp only [Matrix.mul_assoc]
  constructor
  · simp only [P, Submonoid.coe_mul, star_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [hassoc, shift_inv_pow_conj_clock hζ p, Matrix.mul_smul, Matrix.smul_mul, hCcomm,
      smul_smul, mul_comm]
  · simp only [P, Submonoid.coe_mul, star_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [hassoc, hScomm, clock_pow_conj_shift hζ q, smul_smul, mul_comm]

/-- Given `A₁ = diagonal d` and `B₁` in `U(r)` with `A₁ * B₁ = ζ • (B₁ * A₁)`, the orbit vectors
`vNat m = B₁^m *ᵥ e₀` are unit eigenvectors of `A₁` with eigenvalues `ζ^m * d 0`, pairwise
orthogonal for distinct `ζ`-powers, and form a unitary matrix `Vmat`. -/
private theorem eigenvectorOrbit_mem_unitary {r : ℕ} [NeZero r] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    {d : Fin r → ℂ} {A₁ B₁ : Matrix.unitaryGroup (Fin r) ℂ}
    (hA₁ : (A₁ : Matrix (Fin r) (Fin r) ℂ) = Matrix.diagonal d)
    (hrel : (A₁ : Matrix (Fin r) (Fin r) ℂ) * (B₁ : Matrix (Fin r) (Fin r) ℂ) =
      ζ • ((B₁ : Matrix (Fin r) (Fin r) ℂ) * (A₁ : Matrix (Fin r) (Fin r) ℂ))) :
    let vNat (m : ℕ) : Fin r → ℂ := ((B₁ : Matrix (Fin r) (Fin r) ℂ) ^ m) *ᵥ Pi.single 0 1
    let Vmat : Matrix (Fin r) (Fin r) ℂ := fun i k => vNat k.val i
    (d 0 ≠ 0) ∧
    (∀ m, (A₁ : Matrix (Fin r) (Fin r) ℂ) *ᵥ vNat m = (ζ ^ m * d 0) • vNat m) ∧
    (∀ {m₁ m₂}, ζ ^ m₁ ≠ ζ ^ m₂ → dotProduct (star (vNat m₁)) (vNat m₂) = 0) ∧
    (∀ m, dotProduct (star (vNat m)) (vNat m) = 1) ∧
    (Vmat ∈ Matrix.unitaryGroup (Fin r) ℂ) := by
  intro vNat Vmat
  have hζu : ζ ∈ unitary ℂ :=
    Circle.coe_mem_unitary ⟨ζ, mem_sphere_zero_iff_norm.mpr (hζ.norm'_eq_one (NeZero.ne r))⟩
  have hαu : d 0 ∈ unitary ℂ :=
    Pi.mem_unitary_iff.mp (Matrix.diagonal_mem_unitary.mp (hA₁ ▸ A₁.2)) 0
  have hαne : d 0 ≠ 0 := fun h0 =>
    zero_ne_one (α := ℂ) (by simpa [h0] using (Unitary.mem_iff.mp hαu).1)
  have hv_eig (m : ℕ) : (A₁ : Matrix (Fin r) (Fin r) ℂ) *ᵥ vNat m = (ζ ^ m * d 0) • vNat m := by
    induction m with
    | zero =>
      simp only [vNat, pow_zero, Matrix.one_mulVec, one_mul, hA₁]
      ext i
      by_cases hi : i = 0 <;> simp [hi]
    | succ m ih =>
      have hstep : vNat (m + 1) = (B₁ : Matrix (Fin r) (Fin r) ℂ) *ᵥ vNat m := by
        simp only [vNat, pow_succ', Matrix.mulVec_mulVec]
      rw [hstep, Matrix.mulVec_mulVec, hrel, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ih,
        Matrix.mulVec_smul, smul_smul, ← mul_assoc, pow_succ']
  have hv_orth {m₁ m₂ : ℕ} (hne : ζ ^ m₁ ≠ ζ ^ m₂) :
      dotProduct (star (vNat m₁)) (vNat m₂) = 0 := by
    have hdot : dotProduct (star ((A₁ : Matrix (Fin r) (Fin r) ℂ) *ᵥ vNat m₁))
        ((A₁ : Matrix (Fin r) (Fin r) ℂ) *ᵥ vNat m₂) = dotProduct (star (vNat m₁)) (vNat m₂) := by
      rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
        ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp A₁.2, Matrix.vecMul_one]
    rw [hv_eig m₁, hv_eig m₂, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, ← mul_assoc] at hdot
    have hcoeff : star (ζ ^ m₁ * d 0) * (ζ ^ m₂ * d 0) ≠ 1 := fun h1 => hne <| by
      have hz := (Unitary.mem_iff.mp (Submonoid.pow_mem _ hζu m₁)).2
      have hd := (Unitary.mem_iff.mp hαu).1
      rw [star_mul] at h1
      linear_combination -ζ ^ m₁ * h1 + ζ ^ m₂ * (star (d 0) * d 0) * hz + ζ ^ m₂ * hd
    exact (mul_eq_zero.mp (by linear_combination hdot)).resolve_left (sub_ne_zero.mpr hcoeff)
  have hv_norm (m : ℕ) : dotProduct (star (vNat m)) (vNat m) = 1 := by
    dsimp only [vNat]
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp (Submonoid.pow_mem _ B₁.2 m),
      Matrix.vecMul_one]
    simp [dotProduct, Pi.single_apply]
  have hVu : Vmat ∈ Matrix.unitaryGroup (Fin r) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext k l
    have hentry : (star Vmat * Vmat) k l = dotProduct (star (vNat k.val)) (vNat l.val) := by
      rw [Matrix.mul_apply, dotProduct]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Matrix.star_apply, Pi.star_apply]
    rw [hentry]
    by_cases hkl : k = l
    · subst hkl; simp [hv_norm]
    · simp [hkl, hv_orth (fun h => hkl (Fin.ext (hζ.pow_inj k.isLt l.isLt h)))]
  exact ⟨hαne, hv_eig, hv_orth, hv_norm, hVu⟩

/-- The `r`-th orbit vector `vNat r` returns to a unit-modulus scalar multiple of `vNat 0`. -/
private theorem eigenvectorOrbit_return {r : ℕ} [NeZero r] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    {vNat : ℕ → Fin r → ℂ}
    (hv_orth : ∀ {m₁ m₂}, ζ ^ m₁ ≠ ζ ^ m₂ → dotProduct (star (vNat m₁)) (vNat m₂) = 0)
    (hv_norm : ∀ m, dotProduct (star (vNat m)) (vNat m) = 1)
    (hVu : (fun i (k : Fin r) => vNat k.val i) ∈ Matrix.unitaryGroup (Fin r) ℂ) :
    ∃ β : Circle, vNat r = (β : ℂ) • vNat 0 := by
  let Vmat : Matrix (Fin r) (Fin r) ℂ := fun i k => vNat k.val i
  let β : ℂ := dotProduct (star (vNat 0)) (vNat r)
  have hVr : star Vmat *ᵥ vNat r = β • Pi.single 0 1 := by
    ext k
    have hL : (star Vmat *ᵥ vNat r) k = dotProduct (star (vNat k.val)) (vNat r) := by
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Matrix.star_apply, Pi.star_apply]
    rw [hL, Pi.smul_apply, smul_eq_mul]
    by_cases hk : k = 0
    · subst hk; simp [β]
    · have hne : ζ ^ k.val ≠ ζ ^ r := by
        rw [hζ.pow_eq_one]
        intro h1
        have hdvd := (hζ.pow_eq_one_iff_dvd k.val).mp h1
        exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero (Fin.val_ne_of_ne hk)) hdvd)
          (not_le_of_gt k.isLt)
      simp [hk, hv_orth hne]
  have hv_r : vNat r = β • vNat 0 := by
    have h1 := congrArg (Vmat *ᵥ ·) hVr
    rw [Matrix.mulVec_mulVec, Matrix.mem_unitaryGroup_iff.mp hVu, Matrix.one_mulVec,
      Matrix.mulVec_smul] at h1
    have hVe0 : Vmat *ᵥ Pi.single 0 1 = vNat 0 := by
      ext i
      simp [Vmat, Matrix.mulVec, dotProduct, Pi.single_apply]
    rwa [hVe0] at h1
  have hβnorm : ‖β‖ = 1 := by
    have h1 := hv_norm r
    rw [hv_r, star_smul, smul_dotProduct, dotProduct_smul, hv_norm 0, smul_eq_mul, smul_eq_mul,
      mul_one] at h1
    have hns : Complex.normSq β = 1 := by
      rw [← Complex.ofReal_inj]
      simpa [Complex.normSq_eq_conj_mul_self] using h1
    rw [Complex.norm_def, hns, Real.sqrt_one]
  exact ⟨⟨β, mem_sphere_zero_iff_norm.mpr hβnorm⟩, hv_r⟩

/-- Entrywise check that rescaling the unitary orbit matrix `Vmat` by `diag(b⁻ᵏ)` intertwines
`B₁` with `b • S₀` whenever `b^r = β` and `vNat r = β • vNat 0`. -/
private theorem shift_intertwine_of_orbit {r : ℕ} [NeZero r]
    (B₁ : Matrix.unitaryGroup (Fin r) ℂ) (b β : Circle) (hbpow : (b : ℂ) ^ r = β)
    (vNat : ℕ → Fin r → ℂ)
    (hv_step : ∀ m, (B₁ : Matrix (Fin r) (Fin r) ℂ) *ᵥ vNat m = vNat (m + 1))
    (hv_r : vNat r = (β : ℂ) • vNat 0)
    (W : Matrix.unitaryGroup (Fin r) ℂ)
    (hW_entry : ∀ i (k : Fin r),
      (W : Matrix (Fin r) (Fin r) ℂ) i k = vNat k.val i * ((b⁻¹ : Circle) : ℂ) ^ k.val) :
    (B₁ : Matrix (Fin r) (Fin r) ℂ) * (W : Matrix (Fin r) (Fin r) ℂ) =
      (W : Matrix (Fin r) (Fin r) ℂ) * ((b : ℂ) • (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ)) := by
  ext i k
  have hcol : (fun j => (W : Matrix (Fin r) (Fin r) ℂ) j k) =
      (((b⁻¹ : Circle) : ℂ) ^ k.val) • vNat k.val := by
    ext j; simp [hW_entry, mul_comm]
  have hL : ((B₁ : Matrix (Fin r) (Fin r) ℂ) * (W : Matrix (Fin r) (Fin r) ℂ)) i k =
      ((B₁ : Matrix (Fin r) (Fin r) ℂ) *ᵥ (fun j => (W : Matrix (Fin r) (Fin r) ℂ) j k)) i := rfl
  have hR : ((W : Matrix (Fin r) (Fin r) ℂ) *
      ((b : ℂ) • (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ))) i k =
      (b : ℂ) * (W : Matrix (Fin r) (Fin r) ℂ) i (k + 1) := by
    rw [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
    congr 1
    simp [Matrix.mul_apply, shiftUnitary_apply]
  rw [hL, hcol, Matrix.mulVec_smul, hv_step k.val, hR, hW_entry]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hbb : (b : ℂ) * ((b⁻¹ : Circle) : ℂ) = 1 := by
    rw [Circle.coe_inv_eq_conj]
    exact (Unitary.mem_iff.mp b.coe_mem_unitary).2
  by_cases hlt : k.val + 1 < r
  · have hk1 : ((k + 1 : Fin r) : ℕ) = k.val + 1 := by
      rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < r), Nat.mod_eq_of_lt hlt]
    rw [hk1, pow_succ']
    calc ((b⁻¹ : Circle) : ℂ) ^ k.val * vNat (k.val + 1) i
        = ((b : ℂ) * ((b⁻¹ : Circle) : ℂ)) *
            (((b⁻¹ : Circle) : ℂ) ^ k.val * vNat (k.val + 1) i) := by rw [hbb, one_mul]
      _ = (b : ℂ) * (vNat (k.val + 1) i * (((b⁻¹ : Circle) : ℂ) *
            ((b⁻¹ : Circle) : ℂ) ^ k.val)) := by ring
  · have heq : k.val + 1 = r := by omega
    have hk1 : ((k + 1 : Fin r) : ℕ) = 0 := by
      rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (NeZero.ne r)) with hr1 | hr1
      · subst hr1; simp
      · rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt hr1, heq, Nat.mod_self]
    have hbr : (b : ℂ) ^ r = (b : ℂ) ^ k.val * (b : ℂ) :=
      (congrArg ((b : ℂ) ^ ·) heq.symm).trans (pow_succ _ _)
    have hpow_cancel : ((b⁻¹ : Circle) : ℂ) ^ k.val * (b : ℂ) ^ k.val = 1 := by
      rw [← mul_pow, mul_comm, hbb, one_pow]
    have hv_r_i : vNat r i = (β : ℂ) * vNat 0 i := congrFun hv_r i
    rw [heq, hv_r_i, hk1, pow_zero, mul_one, ← hbpow, hbr]
    calc ((b⁻¹ : Circle) : ℂ) ^ k.val * ((b : ℂ) ^ k.val * (b : ℂ) * vNat 0 i)
        = (((b⁻¹ : Circle) : ℂ) ^ k.val * (b : ℂ) ^ k.val) * ((b : ℂ) * vNat 0 i) := by ring
      _ = (b : ℂ) * vNat 0 i := by rw [hpow_cancel, one_mul]

/-- Given unitary matrices `A₁ = diagonal d` and `B₁` with `A₁ * B₁ = ζ • (B₁ * A₁)`, there is a
unitary matrix `W` simultaneously conjugating `(A₁, B₁)` to `(α • C₀, b • S₀)`. -/
private theorem exists_unitary_conj_diagonal_to_clock_shift {r : ℕ} [NeZero r] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) {d : Fin r → ℂ} {A₁ B₁ : Matrix.unitaryGroup (Fin r) ℂ}
    (hA₁ : (A₁ : Matrix (Fin r) (Fin r) ℂ) = Matrix.diagonal d)
    (hrel : (A₁ : Matrix (Fin r) (Fin r) ℂ) * (B₁ : Matrix (Fin r) (Fin r) ℂ) =
      ζ • ((B₁ : Matrix (Fin r) (Fin r) ℂ) * (A₁ : Matrix (Fin r) (Fin r) ℂ))) :
    ∃ (W : Matrix.unitaryGroup (Fin r) ℂ) (α b : ℂ), α ≠ 0 ∧ b ≠ 0 ∧
      star (W : Matrix (Fin r) (Fin r) ℂ) * (A₁ : Matrix (Fin r) (Fin r) ℂ) *
        (W : Matrix (Fin r) (Fin r) ℂ) = α • (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ) ∧
      star (W : Matrix (Fin r) (Fin r) ℂ) * (B₁ : Matrix (Fin r) (Fin r) ℂ) *
        (W : Matrix (Fin r) (Fin r) ℂ) = b • (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ) := by
  let vNat (m : ℕ) : Fin r → ℂ := ((B₁ : Matrix (Fin r) (Fin r) ℂ) ^ m) *ᵥ Pi.single 0 1
  let Vmat : Matrix (Fin r) (Fin r) ℂ := fun i k => vNat k.val i
  obtain ⟨hαne, hv_eig, hv_orth, hv_norm, hVu⟩ := eigenvectorOrbit_mem_unitary hζ hA₁ hrel
  obtain ⟨β, hv_r⟩ := eigenvectorOrbit_return hζ hv_orth hv_norm hVu
  obtain ⟨θ, hθ⟩ := Circle.exp_surjective β
  let b : Circle := Circle.exp (θ / r)
  have hbpow : (b : ℂ) ^ r = β := by
    rw [← Circle.coe_pow, ← Circle.exp_natCast_mul,
      mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne r)), hθ]
  let Dmat : Matrix (Fin r) (Fin r) ℂ :=
    Matrix.diagonal fun k : Fin r => ((b⁻¹ : Circle) : ℂ) ^ k.val
  have hDu : Dmat ∈ Matrix.unitaryGroup (Fin r) ℂ := by
    rw [Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
    exact fun k => Submonoid.pow_mem _ (b⁻¹).coe_mem_unitary k.val
  let W : Matrix.unitaryGroup (Fin r) ℂ := ⟨Vmat, hVu⟩ * ⟨Dmat, hDu⟩
  have hW_entry (i k : Fin r) : (W : Matrix (Fin r) (Fin r) ℂ) i k =
      vNat k.val i * ((b⁻¹ : Circle) : ℂ) ^ k.val := by
    simp only [W, Submonoid.coe_mul, Dmat, Matrix.mul_diagonal]
    rfl
  have hAW : (A₁ : Matrix (Fin r) (Fin r) ℂ) * (W : Matrix (Fin r) (Fin r) ℂ) =
      (W : Matrix (Fin r) (Fin r) ℂ) * (d 0 • (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ)) := by
    ext i k
    have hcol : (fun j => (W : Matrix (Fin r) (Fin r) ℂ) j k) =
        (((b⁻¹ : Circle) : ℂ) ^ k.val) • vNat k.val := by
      ext j; simp [hW_entry, mul_comm]
    have hL : ((A₁ : Matrix (Fin r) (Fin r) ℂ) * (W : Matrix (Fin r) (Fin r) ℂ)) i k =
        ((A₁ : Matrix (Fin r) (Fin r) ℂ) *ᵥ (fun j => (W : Matrix (Fin r) (Fin r) ℂ) j k)) i := rfl
    rw [hL, hcol, Matrix.mulVec_smul, hv_eig k.val]
    simp only [Pi.smul_apply, smul_eq_mul, clockUnitary, Matrix.mul_smul, Matrix.mul_diagonal,
      Matrix.smul_apply, hW_entry]
    ring
  have hBW := shift_intertwine_of_orbit B₁ b β hbpow vNat
    (fun m => by simp only [vNat, pow_succ', Matrix.mulVec_mulVec]) hv_r W hW_entry
  refine ⟨W, d 0, b, hαne, Circle.coe_ne_zero b, ?_, ?_⟩
  · rw [Matrix.mul_assoc, hAW, ← Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff'.mp W.2,
      Matrix.one_mul]
  · rw [Matrix.mul_assoc, hBW, ← Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff'.mp W.2,
      Matrix.one_mul]

/-- The group-commutator equation `⁅A, B⁆ = ζ • 1` in `SU(r)` is equivalent to the Weyl relation
`A * B = ζ • (B * A)`. -/
private theorem mul_eq_smul_mul_of_commutator_eq_smul {r : ℕ} {ζ : ℂ}
    {A B : Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hAB : ((⁅A, B⁆ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      ζ • 1) :
    (A : Matrix (Fin r) (Fin r) ℂ) * (B : Matrix (Fin r) (Fin r) ℂ) =
      ζ • ((B : Matrix (Fin r) (Fin r) ℂ) * (A : Matrix (Fin r) (Fin r) ℂ)) := by
  have hmul := congrArg (· * ((B : Matrix (Fin r) (Fin r) ℂ) * (A : Matrix (Fin r) (Fin r) ℂ))) hAB
  have hAA : ((A⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
      (A : Matrix (Fin r) (Fin r) ℂ) = 1 := congrArg Subtype.val (inv_mul_cancel A)
  have hBB : ((B⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
      (B : Matrix (Fin r) (Fin r) ℂ) = 1 := congrArg Subtype.val (inv_mul_cancel B)
  have hL : ((⁅A, B⁆ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
      ((B : Matrix (Fin r) (Fin r) ℂ) * (A : Matrix (Fin r) (Fin r) ℂ)) =
      (A : Matrix (Fin r) (Fin r) ℂ) * (B : Matrix (Fin r) (Fin r) ℂ) := by
    rw [commutatorElement_def]
    simp only [Submonoid.coe_mul]
    calc
      (A : Matrix (Fin r) (Fin r) ℂ) * (B : Matrix (Fin r) (Fin r) ℂ) *
          ((A⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
          ((B⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
          ((B : Matrix (Fin r) (Fin r) ℂ) * (A : Matrix (Fin r) (Fin r) ℂ))
        = (A : Matrix (Fin r) (Fin r) ℂ) * (B : Matrix (Fin r) (Fin r) ℂ) *
            (((A⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
            ((((B⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
              (B : Matrix (Fin r) (Fin r) ℂ)) * (A : Matrix (Fin r) (Fin r) ℂ))) := by
            simp only [Matrix.mul_assoc]
      _ = (A : Matrix (Fin r) (Fin r) ℂ) * (B : Matrix (Fin r) (Fin r) ℂ) := by
            rw [hBB, Matrix.one_mul, hAA, Matrix.mul_one]
  rw [hL, Matrix.smul_mul, Matrix.one_mul] at hmul
  exact hmul

/-- If `A, B ∈ SU(r)` satisfy `⁅A, B⁆ = ζ • 1`, then some unitary `U₂` simultaneously conjugates
`(A, B)` to `(α • C₀, b • S₀)` with `α, b ≠ 0`. -/
private theorem exists_unitary_conj_to_clock_shift {r : ℕ} [NeZero r] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) (A B : Matrix.specialUnitaryGroup (Fin r) ℂ)
    (hAB : ((⁅A, B⁆ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      ζ • 1) :
    ∃ (U₂ : Matrix.unitaryGroup (Fin r) ℂ) (α b : ℂ), α ≠ 0 ∧ b ≠ 0 ∧
      star (U₂ : Matrix (Fin r) (Fin r) ℂ) * (A : Matrix (Fin r) (Fin r) ℂ) *
        (U₂ : Matrix (Fin r) (Fin r) ℂ) = α • (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ) ∧
      star (U₂ : Matrix (Fin r) (Fin r) ℂ) * (B : Matrix (Fin r) (Fin r) ℂ) *
        (U₂ : Matrix (Fin r) (Fin r) ℂ) = b • (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ) := by
  have hrel := mul_eq_smul_mul_of_commutator_eq_smul hAB
  have : IsStarNormal (A : Matrix (Fin r) (Fin r) ℂ) :=
    Unitary.coe_isStarNormal
      ⟨(A : Matrix (Fin r) (Fin r) ℂ), (mem_specialUnitaryGroup_iff.mp A.2).1⟩
  obtain ⟨U₁mat, hU₁u, d, hd⟩ :=
    Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal (A : Matrix (Fin r) (Fin r) ℂ)
  let U₁ : Matrix.unitaryGroup (Fin r) ℂ := ⟨U₁mat, hU₁u⟩
  let A₁ : Matrix.unitaryGroup (Fin r) ℂ :=
    U₁⁻¹ * ⟨A, (mem_specialUnitaryGroup_iff.mp A.2).1⟩ * U₁
  let B₁ : Matrix.unitaryGroup (Fin r) ℂ :=
    U₁⁻¹ * ⟨B, (mem_specialUnitaryGroup_iff.mp B.2).1⟩ * U₁
  have hU₁inv : ((U₁⁻¹ : Matrix.unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = star U₁mat :=
    rfl
  have hrel₁ : (A₁ : Matrix (Fin r) (Fin r) ℂ) * (B₁ : Matrix (Fin r) (Fin r) ℂ) =
      ζ • ((B₁ : Matrix (Fin r) (Fin r) ℂ) * (A₁ : Matrix (Fin r) (Fin r) ℂ)) := by
    have hconjMul (X Y : Matrix (Fin r) (Fin r) ℂ) :
        (star U₁mat * X * U₁mat) * (star U₁mat * Y * U₁mat) = star U₁mat * (X * Y) * U₁mat := by
      calc (star U₁mat * X * U₁mat) * (star U₁mat * Y * U₁mat)
          = star U₁mat * X * (U₁mat * star U₁mat) * Y * U₁mat := by simp only [Matrix.mul_assoc]
        _ = star U₁mat * (X * Y) * U₁mat := by
            rw [Matrix.mem_unitaryGroup_iff.mp hU₁u, Matrix.mul_one]
            simp only [Matrix.mul_assoc]
    simp only [A₁, B₁, Submonoid.coe_mul, hU₁inv, U₁]
    rw [hconjMul, hconjMul, hrel, Matrix.mul_smul, Matrix.smul_mul]
  obtain ⟨W, α, b, hαne, hbne, hWA, hWB⟩ :=
    exists_unitary_conj_diagonal_to_clock_shift hζ hd hrel₁
  refine ⟨U₁ * W, α, b, hαne, hbne, ?_, ?_⟩
  · rw [← hWA]
    simp only [A₁, Submonoid.coe_mul, hU₁inv, U₁, star_mul, Matrix.mul_assoc]
  · rw [← hWB]
    simp only [B₁, Submonoid.coe_mul, hU₁inv, U₁, star_mul, Matrix.mul_assoc]

/-- Determinant comparison: if `X, X₀ ∈ SU(r)` are unitarily conjugate to `s • M` and `c • M`
respectively (for `M ∈ U(r)`), then `c / s` is a power of the primitive `r`-th root `ζ`. -/
private theorem exists_pow_mul_eq_circle_of_unitary_conj {r : ℕ} [NeZero r] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) {U₂ M : Matrix.unitaryGroup (Fin r) ℂ}
    {X X₀ : Matrix.specialUnitaryGroup (Fin r) ℂ} {s : ℂ} (hs : s ≠ 0) {c : Circle}
    (h1 : star (U₂ : Matrix (Fin r) (Fin r) ℂ) * (X : Matrix (Fin r) (Fin r) ℂ) *
      (U₂ : Matrix (Fin r) (Fin r) ℂ) = s • (M : Matrix (Fin r) (Fin r) ℂ))
    (h2 : (X₀ : Matrix (Fin r) (Fin r) ℂ) = (c : ℂ) • (M : Matrix (Fin r) (Fin r) ℂ)) :
    ∃ k < r, ζ ^ k * s = c := by
  have hdetU₂ : ((U₂ : Matrix (Fin r) (Fin r) ℂ).det) *
      (star (U₂ : Matrix (Fin r) (Fin r) ℂ)).det = 1 := by
    rw [← Matrix.det_mul, Matrix.mem_unitaryGroup_iff.mp U₂.2, Matrix.det_one]
  have hdetM : (M : Matrix (Fin r) (Fin r) ℂ).det ≠ 0 := fun h0 => by
    have hnorm := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary M.2)
    rw [h0, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hd1 : s ^ r * (M : Matrix (Fin r) (Fin r) ℂ).det = 1 := by
    have hd := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, Fintype.card_fin,
      (mem_specialUnitaryGroup_iff.mp X.2).2, mul_one, mul_comm, hdetU₂] at hd
    exact hd.symm
  have hd2 : (c : ℂ) ^ r * (M : Matrix (Fin r) (Fin r) ℂ).det = 1 := by
    have hd := congrArg Matrix.det h2
    rw [Matrix.det_smul, Fintype.card_fin, (mem_specialUnitaryGroup_iff.mp X₀.2).2] at hd
    exact hd.symm
  have hpow : ((c : ℂ) * s⁻¹) ^ r = 1 := by
    have heq : (c : ℂ) ^ r = s ^ r := mul_right_cancel₀ hdetM (hd2.trans hd1.symm)
    rw [mul_pow, inv_pow, heq, mul_inv_cancel₀ (pow_ne_zero r hs)]
  obtain ⟨k, hk, hζk⟩ := hζ.eq_pow_of_pow_eq_one hpow
  exact ⟨k, hk, by rw [hζk, inv_mul_cancel_right₀ hs]⟩

/-- Any solution `A, B ∈ SU(r)` of `⁅A, B⁆ = ζ • 1` is simultaneously `SU(r)`-conjugate to the
rescaled clock–shift pair `(A₀, B₀)`. -/
private theorem exists_su_conj_to_clock_shift {r : ℕ} [NeZero r] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) {c₁ c₂ : Circle} {A₀ B₀ : Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hA₀ : (A₀ : Matrix (Fin r) (Fin r) ℂ) =
      (c₁ : ℂ) • (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ))
    (hB₀ : (B₀ : Matrix (Fin r) (Fin r) ℂ) =
      (c₂ : ℂ) • (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ))
    (A B : Matrix.specialUnitaryGroup (Fin r) ℂ)
    (hAB : ((⁅A, B⁆ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      ζ • 1) :
    ∃ u : Matrix.specialUnitaryGroup (Fin r) ℂ,
      ConjAct.toConjAct u • A = A₀ ∧ ConjAct.toConjAct u • B = B₀ := by
  obtain ⟨U₂, α, b, hαne, hbne, hU₂A, hU₂B⟩ := exists_unitary_conj_to_clock_shift hζ A B hAB
  obtain ⟨p, _, hc₁⟩ := exists_pow_mul_eq_circle_of_unitary_conj hζ hαne hU₂A hA₀
  obtain ⟨q, _, hc₂⟩ := exists_pow_mul_eq_circle_of_unitary_conj hζ hbne hU₂B hB₀
  let P : Matrix.unitaryGroup (Fin r) ℂ := (clockUnitary hζ) ^ q * ((shiftUnitary r)⁻¹) ^ p
  have ⟨hPA, hPB⟩ := clock_shift_phase_conj hζ p q α b
  let U : Matrix.unitaryGroup (Fin r) ℂ := P * U₂⁻¹
  obtain ⟨c, hc⟩ := Matrix.exists_circle_smul_mem_specialUnitaryGroup U
  let u : Matrix.specialUnitaryGroup (Fin r) ℂ := ⟨(c : ℂ) • (U : Matrix (Fin r) (Fin r) ℂ), hc⟩
  have hu (X : Matrix.specialUnitaryGroup (Fin r) ℂ) :
      ((ConjAct.toConjAct u • X : Matrix.specialUnitaryGroup (Fin r) ℂ) :
          Matrix (Fin r) (Fin r) ℂ) =
        (U : Matrix (Fin r) (Fin r) ℂ) * (X : Matrix (Fin r) (Fin r) ℂ) *
          star (U : Matrix (Fin r) (Fin r) ℂ) := by
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, ← Matrix.star_eq_inv]
    simp only [Submonoid.coe_mul, Matrix.specialUnitaryGroup.coe_star, u, star_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, (Unitary.mem_iff.mp c.coe_mem_unitary).1,
      one_smul]
  have hUinv : ((U₂⁻¹ : Matrix.unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      star (U₂ : Matrix (Fin r) (Fin r) ℂ) := rfl
  refine ⟨u, Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [hu A, hA₀, ← hc₁, ← hPA, ← hU₂A]
    simp only [U, P, Submonoid.coe_mul, hUinv, star_mul, star_star, Matrix.mul_assoc]
  · rw [hu B, hB₀, ← hc₂, ← hPB, ← hU₂B]
    simp only [U, P, Submonoid.coe_mul, hUinv, star_mul, star_star, Matrix.mul_assoc]

end ClockAndShift

section GenusOneTheorems

/-- For every primitive `r`-th root of unity `ζ`, the genus-one twisted relation set
`relationSet r ζ 1` is nonempty. -/
theorem nonempty_relationSet_genus_one (r : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r) :
    Nonempty (relationSet r ζ 1) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨⟨1, mem_relationSet_one_iff.mpr (Subsingleton.elim _ _)⟩⟩
  have : NeZero r := ⟨by omega⟩
  obtain ⟨_, _, A₀, B₀, _, _, hAB⟩ := exists_clock_shift_su hζ
  exact ⟨⟨fun _ => (A₀, B₀), by simpa [mem_relationSet_one_iff] using hAB⟩⟩

/-- **Genus-one representation model.** For a primitive `r`-th root of unity `ζ`, the twisted
relation `⁅A, B⁆ = ζ • 1` has a solution in `SU(r)`, unique up to simultaneous `SU(r)`-conjugation,
so the genus-one moduli space `relationModuli r ζ 1` is a single point. -/
theorem relationModuli_genus_one (r : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r) :
    Nonempty (relationModuli r ζ 1) ∧ Subsingleton (relationModuli r ζ 1) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨⟨Quotient.mk _ ⟨1, mem_relationSet_one_iff.mpr (Subsingleton.elim _ _)⟩⟩,
      ⟨fun a b => Quotient.inductionOn₂ a b fun x y => by rw [Subsingleton.elim x y]⟩⟩
  have : NeZero r := ⟨by omega⟩
  obtain ⟨c₁, c₂, A₀, B₀, hA₀, hB₀, hAB₀⟩ := exists_clock_shift_su hζ
  let x₀ : relationSet r ζ 1 := ⟨fun _ => (A₀, B₀), by simpa [mem_relationSet_one_iff] using hAB₀⟩
  have hconj (x : relationSet r ζ 1) :
      (Quotient.mk _ x : relationModuli r ζ 1) = Quotient.mk _ x₀ := by
    rw [quotient_mk_relationModuli_eq_iff]
    obtain ⟨u, huA, huB⟩ := exists_su_conj_to_clock_shift hζ hA₀ hB₀ (x.1 0).1 (x.1 0).2
      (mem_relationSet_one_iff.mp x.2)
    refine ⟨u, funext fun j => ?_⟩
    fin_cases j
    exact Prod.ext huA huB
  exact ⟨⟨Quotient.mk _ x₀⟩, ⟨fun a b => Quotient.inductionOn₂ a b fun x y =>
    (hconj x).trans (hconj y).symm⟩⟩

/-- At genus one, for a primitive `r`-th root of unity `ζ`, `relationModuli r ζ 1` is simply
connected. -/
theorem simplyConnectedSpace_relationModuli_genus_one (r : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r) :
    SimplyConnectedSpace (relationModuli r ζ 1) := by
  obtain ⟨hne, hsub⟩ := relationModuli_genus_one r ζ hζ
  exact SimplyConnectedSpace.ofContractible _

/-- **Genus-one orbit homeomorphism.** For a primitive `r`-th root of unity `ζ` and any basepoint
`x₀ : relationSet r ζ 1`, the effective `PSU(r)` action induces a homeomorphism
`PSU(r) ≃ₜ relationSet r ζ 1`. -/
noncomputable def psuOrbitHomeomorphGenusOne {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    (x₀ : relationSet r ζ 1) :
    (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range ≃ₜ relationSet r ζ 1 := by
  haveI : CompactSpace (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range :=
    isCompact_iff_compactSpace.mp isCompact_range_toPSL
  have hbij : Function.Bijective (fun p : (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range => p • x₀) := by
    constructor
    · intro p q hpq
      dsimp only at hpq
      have hfix : (q⁻¹ * p) • x₀ = x₀ := by
        rw [mul_smul, hpq, inv_smul_smul]
      have h1 : q⁻¹ * p = 1 := (psu_smul_relationSet_eq_self_iff hζ x₀ (q⁻¹ * p)).mp hfix
      exact (inv_mul_eq_one.mp h1).symm
    · intro x
      have hsub := (relationModuli_genus_one r ζ hζ).2
      have hq : (Quotient.mk _ x₀ : relationModuli r ζ 1) = Quotient.mk _ x :=
        Subsingleton.elim _ _
      obtain ⟨u, hu⟩ := (quotient_mk_relationModuli_eq_iff x₀ x).mp hq
      refine ⟨toPSL.rangeRestrict u, ?_⟩
      dsimp only
      rw [toPSL_rangeRestrict_smul_relationSet]
      exact Subtype.ext hu
  exact (continuous_id.smul continuous_const).homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ hbij)

@[simp]
theorem psuOrbitHomeomorphGenusOne_apply {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    (x₀ : relationSet r ζ 1)
    (p : (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range) :
    psuOrbitHomeomorphGenusOne hζ x₀ p = p • x₀ :=
  (rfl)

/-- For every positive genus `g ≥ 1` and primitive `r`-th root of unity `ζ`, the twisted relation
set `relationSet r ζ g` is nonempty. -/
theorem nonempty_relationSet_of_pos (r : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r)
    (g : ℕ) (hg : 1 ≤ g) : Nonempty (relationSet r ζ g) := by
  obtain ⟨g', rfl⟩ := Nat.exists_eq_add_of_le' hg
  obtain ⟨⟨x₁, hx₁⟩⟩ := nonempty_relationSet_genus_one r ζ hζ
  let tuple : Fin (g' + 1) →
      Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ :=
    Fin.cons (x₁ 0) (fun _ : Fin g' => (1, 1))
  refine ⟨⟨tuple, ?_⟩⟩
  rw [mem_relationSet_iff]
  have hprod : (List.ofFn fun j : Fin (g' + 1) => ⁅(tuple j).1, (tuple j).2⁆).prod =
      ⁅(x₁ 0).1, (x₁ 0).2⁆ := by
    rw [List.ofFn_succ, List.prod_cons]
    simp [tuple, List.ofFn_const]
  rw [hprod]
  exact mem_relationSet_one_iff.mp hx₁

/-- For every positive genus `g ≥ 1` and primitive `r`-th root of unity `ζ`, the representation
model `relationModuli r ζ g` is nonempty. -/
theorem nonempty_relationModuli_of_pos (r : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r)
    (g : ℕ) (hg : 1 ≤ g) : Nonempty (relationModuli r ζ g) := by
  obtain ⟨x⟩ := nonempty_relationSet_of_pos r ζ hζ g hg
  exact ⟨Quotient.mk _ x⟩

/-- At genus one, the central-twist `H¹(T²; μ_r)` action on `relationModuli r ζ 1` is trivial. -/
theorem centerTwist_smul_relationModuli_genus_one (r : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r)
    (ε : Fin 1 → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
    (q : relationModuli r ζ 1) : ε • q = q := by
  have := (relationModuli_genus_one r ζ hζ).2
  exact Subsingleton.elim _ _

end GenusOneTheorems

section RankTwoChecks

/-- The diagonal matrix `diag(i, -i) ∈ SU(2)`. -/
def rankTwoClock : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  ⟨!![Complex.I, 0; 0, -Complex.I], mem_specialUnitaryGroup_iff.mpr ⟨by
    rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply], by
    simp [Matrix.det_fin_two]⟩⟩

/-- The rotation matrix `!![0, 1; -1, 0] ∈ SU(2)`. -/
def rankTwoShift : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  ⟨!![(0 : ℂ), 1; -1, 0], mem_specialUnitaryGroup_iff.mpr ⟨by
    rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply], by
    simp [Matrix.det_fin_two]⟩⟩

/-- The central element `-1 ∈ Z(SU(2))`. -/
def negOneSU2 : Subgroup.center (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  ⟨⟨-1, mem_specialUnitaryGroup_iff.mpr ⟨by
    rw [Matrix.mem_unitaryGroup_iff']
    simp, by simp [Matrix.det_fin_two]⟩⟩, by
    rw [Matrix.specialUnitaryGroup.mem_center_iff]
    refine ⟨-1, by norm_num, ?_⟩
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]⟩

/-- The central element `-1 ∈ Z(SU(2))` is nontrivial. -/
theorem negOneSU2_ne_one : negOneSU2 ≠ 1 := by
  intro h
  have h00 := congr_fun₂ (congrArg (fun z : Subgroup.center
    (Matrix.specialUnitaryGroup (Fin 2) ℂ) => (z.1 : Matrix (Fin 2) (Fin 2) ℂ)) h) 0 0
  simp only [negOneSU2, OneMemClass.coe_one, Matrix.neg_apply, Matrix.one_apply_eq] at h00
  norm_num at h00

/-- For `r = 2`, `ζ = -1`, the pair `(rankTwoClock, rankTwoShift)` satisfies
`⁅A, B⁆ = -1` and hence belongs to `relationSet 2 (-1) 1`. -/
theorem rankTwoPair_mem_relationSet :
    (fun _ : Fin 1 => (rankTwoClock, rankTwoShift)) ∈ relationSet 2 (-1) 1 := by
  rw [mem_relationSet_one_iff, commutatorElement_def, ← Matrix.star_eq_inv rankTwoClock,
    ← Matrix.star_eq_inv rankTwoShift]
  simp only [Submonoid.coe_mul, Matrix.specialUnitaryGroup.coe_star]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankTwoClock, rankTwoShift, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.star_apply]

/-- Conjugating `rankTwoClock` by `rankTwoShift` multiplies it by `-1`. -/
theorem rankTwoShift_conj_rankTwoClock :
    ConjAct.toConjAct rankTwoShift • rankTwoClock = negOneSU2.1 * rankTwoClock := by
  apply Subtype.ext
  rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, ← Matrix.star_eq_inv rankTwoShift]
  simp only [Submonoid.coe_mul, Matrix.specialUnitaryGroup.coe_star]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankTwoClock, rankTwoShift, negOneSU2, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_apply]

/-- Conjugating `rankTwoShift` by `rankTwoClock` multiplies it by `-1`. -/
theorem rankTwoClock_conj_rankTwoShift :
    ConjAct.toConjAct rankTwoClock • rankTwoShift = negOneSU2.1 * rankTwoShift := by
  apply Subtype.ext
  rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, ← Matrix.star_eq_inv rankTwoClock]
  simp only [Submonoid.coe_mul, Matrix.specialUnitaryGroup.coe_star]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankTwoClock, rankTwoShift, negOneSU2, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_apply]

/-- The central-twist `H¹(T²; ℤ/2)` action on `relationModuli 2 (-1) 1` is not free: the
nontrivial sign twist `(-1, 1)` fixes the class of `(rankTwoClock, rankTwoShift)`. -/
theorem exists_ne_one_centerTwist_fix_rankTwo_genus_one :
    ∃ (ε : Fin 1 → Subgroup.center (Matrix.specialUnitaryGroup (Fin 2) ℂ) ×
        Subgroup.center (Matrix.specialUnitaryGroup (Fin 2) ℂ))
      (q : relationModuli 2 (-1) 1), ε ≠ 1 ∧ ε • q = q := by
  let ε : Fin 1 → Subgroup.center (Matrix.specialUnitaryGroup (Fin 2) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    fun _ => (negOneSU2, 1)
  let x : relationSet 2 (-1) 1 :=
    ⟨fun _ => (rankTwoClock, rankTwoShift), rankTwoPair_mem_relationSet⟩
  refine ⟨ε, Quotient.mk _ x, ?_, ?_⟩
  · intro h
    have h0 := congrArg Prod.fst (congrFun h 0)
    exact negOneSU2_ne_one h0
  · rw [centerTwist_smul_relationModuli_mk]
    symm
    rw [quotient_mk_relationModuli_eq_iff]
    refine ⟨rankTwoShift, funext fun j => ?_⟩
    fin_cases j
    refine Prod.ext rankTwoShift_conj_rankTwoClock ?_
    simp [ε, x, ConjAct.smul_def]

/-- `rankTwoClock` is not central in `SU(2)`. Since it commutes with `(1, 1) ∈ relationSet 2 1 1`,
this shows that the primitive-root hypothesis cannot be omitted from
`relationSet_stabilizer_central`. -/
theorem rankTwoClock_not_mem_center :
    rankTwoClock ∉ Subgroup.center (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  rw [Matrix.specialUnitaryGroup.mem_center_iff]
  rintro ⟨c, _, hc⟩
  have h00 := congr_fun₂ hc 0 0
  have h11 := congr_fun₂ hc 1 1
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, rankTwoClock, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one] at h00 h11
  have him := congrArg Complex.im (h00.symm.trans h11)
  norm_num at him

/-- At the non-coprime parameter `r = 2`, `ζ = 1`, `g = 1`, the moduli space `relationModuli 2 1 1`
is not a subsingleton (distinguishing the classes of `(1, 1)` and `(rankTwoClock, 1)`). -/
theorem not_subsingleton_relationModuli_two_one_one : ¬ Subsingleton (relationModuli 2 1 1) := by
  intro hsub
  let x₁ : relationSet 2 1 1 := ⟨1, one_mem_relationSet 2 1⟩
  let x₂ : relationSet 2 1 1 := ⟨fun _ => (rankTwoClock, 1), by
    rw [mem_relationSet_one_iff]
    simp⟩
  have heq : (Quotient.mk _ x₁ : relationModuli 2 1 1) = Quotient.mk _ x₂ :=
    Subsingleton.elim _ _
  obtain ⟨u, hu⟩ := (quotient_mk_relationModuli_eq_iff x₁ x₂).mp heq
  have h0 : ConjAct.toConjAct u • (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) = rankTwoClock :=
    congrArg Prod.fst (congrFun hu 0)
  rw [smul_one] at h0
  have h00 := congr_fun₂ (congrArg Subtype.val h0) 0 0
  simp only [OneMemClass.coe_one, Matrix.one_apply_eq, rankTwoClock, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one] at h00
  have him := congrArg Complex.im h00
  norm_num at him

end RankTwoChecks

end GaugeModuli

end TauCeti
