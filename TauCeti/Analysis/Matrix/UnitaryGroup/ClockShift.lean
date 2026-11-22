/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.Analysis.Matrix.UnitaryGroup.Basic
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.Algebra.Star.Basic
import TauCeti.Analysis.Complex.Circle
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Analysis.Matrix.Normal
import TauCeti.Analysis.RCLike.Basic
import TauCeti.LinearAlgebra.UnitaryGroup

/-!
# Unitary clock and shift matrices and the finite Stone–von Neumann theorem

For a positive integer `r` and a primitive `r`-th root of unity `ζ : ℂ`, the **clock matrix**
`C₀ = diag(1, ζ, …, ζ^{r-1})` (`Matrix.clockUnitary`) and the cyclic **shift matrix**
`S₀` sending `e_j ↦ e_{j + 1}` (`Matrix.shiftUnitary`) are unitary `r × r` matrices satisfying the
finite **Weyl commutation relation**

`C₀ * S₀ = ζ • (S₀ * C₀)`

(`Matrix.clockUnitary_mul_shiftUnitary`). Conversely, every pair of unitary matrices `A, B ∈ U(r)`
satisfying `A * B = ζ • (B * A)` is simultaneously unitarily conjugate to a scalar rescaling
`(α • C₀, b • S₀)` with `α, b ∈ Circle` (`Matrix.exists_unitary_conj_to_clock_shift`), a
finite-dimensional version of the Stone–von Neumann uniqueness theorem for the discrete
Heisenberg–Weyl relation.

Rescaling `C₀` and `S₀` by elements of the unit circle yields a special unitary pair
`(A₀, B₀)` in `SU(r)` with group commutator `⁅A₀, B₀⁆ = ζ • 1`
(`Matrix.exists_clock_shift_specialUnitaryGroup`), and determinant comparison combined with
conjugation by powers of `C₀` and `S₀` shows that every solution `A, B ∈ SU(r)` of
`⁅A, B⁆ = ζ • 1` is simultaneously `SU(r)`-conjugate to `(A₀, B₀)`
(`Matrix.exists_specialUnitaryGroup_conj_to_clock_shift`).

## Main definitions

* `Matrix.clockUnitary`: the unitary clock matrix `C₀ = diag(1, ζ, …, ζ^{r-1}) ∈ U(r)`.
* `Matrix.shiftUnitary`: the unitary cyclic shift matrix `S₀ ∈ U(r)` sending `e_j ↦ e_{j + 1}`.

## Main results

* `Matrix.clockUnitary_mul_shiftUnitary`: the Weyl relation `C₀ * S₀ = ζ • (S₀ * C₀)`.
* `Matrix.clockUnitary_pow_conj_shiftUnitary`, `Matrix.shiftUnitary_inv_pow_conj_clockUnitary`,
  and `Matrix.clockUnitary_shiftUnitary_phase_conj`: phase-shifting conjugation formulas for
  powers of `C₀` and `S₀`.
* `Matrix.exists_unitary_conj_to_clock_shift`: finite Stone–von Neumann uniqueness of unitary
  Weyl pairs up to simultaneous unitary conjugation and unit-circle rescaling.
* `Matrix.exists_clock_shift_specialUnitaryGroup`,
  `Matrix.exists_pow_mul_eq_of_unitary_conj_specialUnitaryGroup` (determinant comparison), and
  `Matrix.exists_specialUnitaryGroup_conj_to_clock_shift`: existence and uniqueness up to
  simultaneous `SU(r)`-conjugation of special unitary solutions to `⁅A, B⁆ = ζ • 1`.

## References

* J. J. Sylvester, *Lectures on the Principles of Universal Algebra*, American Journal of
  Mathematics 6 (1884), 270–286 (nonions and clock–shift matrices).
* Katrin Wehrheim and Chris T. Woodward, *Floer field theory for coprime rank and degree*,
  arXiv:1601.04924, §3 (clock–shift normal form for `⁅A, B⁆ = ζ • 1` in `SU(r)`).
-/

public section

open scoped commutatorElement

namespace Matrix

/-- The unitary clock matrix `C₀ = diag(1, ζ, …, ζ^{r-1}) ∈ U(r)`. -/
def clockUnitary {r : ℕ} [NeZero r] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r) :
    unitaryGroup (Fin r) ℂ :=
  ⟨diagonal fun k : Fin r => ζ ^ (k : ℕ), by
    have hζu : ζ ∈ unitary ℂ :=
      RCLike.mem_unitary_iff_norm_eq_one.mpr (hζ.norm'_eq_one (NeZero.ne r))
    rw [diagonal_mem_unitary, Pi.mem_unitary_iff]
    exact fun k => Submonoid.pow_mem _ hζu k.val⟩

@[simp]
theorem coe_clockUnitary {r : ℕ} [NeZero r] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r) :
    (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ) = diagonal fun k : Fin r => ζ ^ (k : ℕ) :=
  (rfl)

/-- The unitary cyclic shift matrix `S₀ ∈ U(r)` sending `e_j ↦ e_{j + 1}`. -/
def shiftUnitary (r : ℕ) [NeZero r] : unitaryGroup (Fin r) ℂ :=
  permutationUnitary (R := ℂ) (Equiv.addRight (1 : Fin r))

/-- Entry formula for the cyclic shift matrix: `(S₀) i j = 1` iff `i = j + 1`. -/
@[simp]
theorem shiftUnitary_apply (r : ℕ) [NeZero r] (i j : Fin r) :
    (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ) i j = if i = j + 1 then 1 else 0 := by
  simp only [shiftUnitary, coe_permutationUnitary, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Equiv.Perm.inv_def, Option.mem_def,
    Option.some.injEq]
  simp [add_neg_eq_iff_eq_add]

/-- The Weyl commutation relation `C₀ * S₀ = ζ • (S₀ * C₀)` for the clock and shift matrices. -/
theorem clockUnitary_mul_shiftUnitary {r : ℕ} [NeZero r] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r) :
    (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ) * (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ) =
      ζ • ((shiftUnitary r : Matrix (Fin r) (Fin r) ℂ) *
        (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne r)
  ext i j
  simp only [coe_clockUnitary, diagonal_mul, mul_diagonal, Matrix.smul_apply, smul_eq_mul,
    shiftUnitary_apply]
  split_ifs with h
  · subst h
    rw [Fin.val_add_one]
    split_ifs with hj
    · subst hj
      simp [← pow_succ', hζ.pow_eq_one]
    · rw [pow_succ', mul_one, one_mul]
  · simp

/-- Iterated conjugation of `S₀` by `C₀^n` multiplies `S₀` by `ζ^n`. -/
theorem clockUnitary_pow_conj_shiftUnitary {r : ℕ} [NeZero r] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    (n : ℕ) :
    (((clockUnitary hζ) ^ n : unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
        (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ) *
        star (((clockUnitary hζ) ^ n : unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      ζ ^ n • (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ) := by
  have hSCinv : (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ) *
      (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ) *
      star (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ) =
      ζ • (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ) := by
    rw [clockUnitary_mul_shiftUnitary hζ, Matrix.smul_mul, Matrix.mul_assoc,
      mem_unitaryGroup_iff.mp (clockUnitary hζ).property, Matrix.mul_one]
  simpa only [SubmonoidClass.coe_pow] using
    TauCeti.pow_mul_mul_star_pow_of_mul_mul_star_eq_smul hSCinv n

/-- Iterated conjugation of `C₀` by `(S₀⁻¹)^n` multiplies `C₀` by `ζ^n`. -/
theorem shiftUnitary_inv_pow_conj_clockUnitary {r : ℕ} [NeZero r] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) (n : ℕ) :
    ((((shiftUnitary r)⁻¹) ^ n : unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
        (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ) *
        star ((((shiftUnitary r)⁻¹) ^ n : unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      ζ ^ n • (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ) := by
  have hSinvC : (((shiftUnitary r)⁻¹ : unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
      (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ) *
      star (((shiftUnitary r)⁻¹ : unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      ζ • (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ) := by
    rw [UnitaryGroup.inv_val, star_star, Matrix.mul_assoc, clockUnitary_mul_shiftUnitary hζ,
      Matrix.mul_smul, ← Matrix.mul_assoc, mem_unitaryGroup_iff'.mp (shiftUnitary r).property,
      Matrix.one_mul]
  simpa only [SubmonoidClass.coe_pow] using
    TauCeti.pow_mul_mul_star_pow_of_mul_mul_star_eq_smul hSinvC n

/-- Conjugating `α • C₀` and `b • S₀` by `P = C₀^q * (S₀⁻¹)^p` shifts them by `ζ^p` and `ζ^q`. -/
theorem clockUnitary_shiftUnitary_phase_conj {r : ℕ} [NeZero r] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    (p q : ℕ) (α b : ℂ) :
    let P : unitaryGroup (Fin r) ℂ := (clockUnitary hζ) ^ q * ((shiftUnitary r)⁻¹) ^ p
    (P : Matrix (Fin r) (Fin r) ℂ) * (α • (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ)) *
        star (P : Matrix (Fin r) (Fin r) ℂ) =
      (ζ ^ p * α) • (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ) ∧
    (P : Matrix (Fin r) (Fin r) ℂ) * (b • (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ)) *
        star (P : Matrix (Fin r) (Fin r) ℂ) =
      (ζ ^ q * b) • (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ) := by
  intro P
  set C := clockUnitary hζ
  set S := shiftUnitary r
  have hsplit (X Y M : Matrix (Fin r) (Fin r) ℂ) :
      (X * Y) * M * (star Y * star X) = X * (Y * M * star Y) * star X := by
    simp only [Matrix.mul_assoc]
  have hCq :
      (((C ^ q : unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
          (C : Matrix (Fin r) (Fin r) ℂ) *
          star ((C ^ q : unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) = C :=
    (commute_unitary_iff_star_right_conjugate (C ^ q).property).mp
      (((Commute.refl C).pow_left q).map (unitaryGroup (Fin r) ℂ).subtype)
  have hSp :
      ((((S⁻¹ ^ p : unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) *
          (S : Matrix (Fin r) (Fin r) ℂ) *
          star ((S⁻¹ ^ p : unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) = S :=
    (commute_unitary_iff_star_right_conjugate (S⁻¹ ^ p).property).mp
      (((Commute.refl S).inv_left.pow_left p).map (unitaryGroup (Fin r) ℂ).subtype)
  constructor
  · simp only [P, Submonoid.coe_mul, star_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [hsplit, shiftUnitary_inv_pow_conj_clockUnitary hζ p, Matrix.mul_smul, Matrix.smul_mul,
      hCq, smul_smul, mul_comm α (ζ ^ p)]
  · simp only [P, Submonoid.coe_mul, star_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [hsplit, hSp, clockUnitary_pow_conj_shiftUnitary hζ q, smul_smul, mul_comm b (ζ ^ q)]

/-- Given `A₁ = diagonal d` and `B₁` in `U(r)` with `A₁ * B₁ = ζ • (B₁ * A₁)`, the orbit vectors
`vNat m = B₁^m *ᵥ e₀` are unit eigenvectors of `A₁` with eigenvalues `ζ^m * d 0`, pairwise
orthogonal for distinct `ζ`-powers, and form a unitary matrix `Vmat`. -/
private theorem eigenvectorOrbit_mem_unitary {r : ℕ} [NeZero r] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    {d : Fin r → ℂ} {A₁ B₁ : unitaryGroup (Fin r) ℂ}
    (hA₁ : (A₁ : Matrix (Fin r) (Fin r) ℂ) = diagonal d)
    (hrel : (A₁ : Matrix (Fin r) (Fin r) ℂ) * (B₁ : Matrix (Fin r) (Fin r) ℂ) =
      ζ • ((B₁ : Matrix (Fin r) (Fin r) ℂ) * (A₁ : Matrix (Fin r) (Fin r) ℂ))) :
    let vNat (m : ℕ) : Fin r → ℂ := ((B₁ : Matrix (Fin r) (Fin r) ℂ) ^ m) *ᵥ Pi.single 0 1
    let Vmat : Matrix (Fin r) (Fin r) ℂ := fun i k => vNat k.val i
    (d 0 ∈ unitary ℂ) ∧
    (∀ m, (A₁ : Matrix (Fin r) (Fin r) ℂ) *ᵥ vNat m = (ζ ^ m * d 0) • vNat m) ∧
    (∀ {m₁ m₂}, ζ ^ m₁ ≠ ζ ^ m₂ → dotProduct (star (vNat m₁)) (vNat m₂) = 0) ∧
    (∀ m, dotProduct (star (vNat m)) (vNat m) = 1) ∧
    (Vmat ∈ unitaryGroup (Fin r) ℂ) := by
  intro vNat Vmat
  have hζu : ζ ∈ unitary ℂ :=
    RCLike.mem_unitary_iff_norm_eq_one.mpr (hζ.norm'_eq_one (NeZero.ne r))
  have hαu : d 0 ∈ unitary ℂ :=
    Pi.mem_unitary_iff.mp (diagonal_mem_unitary.mp (hA₁ ▸ A₁.property)) 0
  have hv_eig (m : ℕ) : (A₁ : Matrix (Fin r) (Fin r) ℂ) *ᵥ vNat m = (ζ ^ m * d 0) • vNat m := by
    induction m with
    | zero =>
      simp only [vNat, pow_zero, one_mulVec, one_mul, hA₁]
      ext i
      by_cases hi : i = 0 <;> simp [hi]
    | succ m ih =>
      have hstep : vNat (m + 1) = (B₁ : Matrix (Fin r) (Fin r) ℂ) *ᵥ vNat m := by
        simp only [vNat, pow_succ', mulVec_mulVec]
      rw [hstep, mulVec_mulVec, hrel, smul_mulVec, ← mulVec_mulVec, ih, mulVec_smul, smul_smul,
        ← mul_assoc, pow_succ']
  have hunitary_dot {M : Matrix (Fin r) (Fin r) ℂ} (hM : M ∈ unitaryGroup (Fin r) ℂ)
      (x y : Fin r → ℂ) :
      dotProduct (star (M *ᵥ x)) (M *ᵥ y) = dotProduct (star x) y := by
    have hinner := (mem_unitaryGroup_iff_inner_toEuclideanCLM.mp hM)
      (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa [toEuclideanCLM_apply, PiLp.inner_apply, dotProduct, mul_comm] using hinner
  have hv_orth {m₁ m₂ : ℕ} (hne : ζ ^ m₁ ≠ ζ ^ m₂) :
      dotProduct (star (vNat m₁)) (vNat m₂) = 0 := by
    have hdot := hunitary_dot A₁.property (vNat m₁) (vNat m₂)
    rw [hv_eig m₁, hv_eig m₂, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, ← mul_assoc] at hdot
    have hcoeff : star (ζ ^ m₁ * d 0) * (ζ ^ m₂ * d 0) ≠ 1 := fun h1 => hne <| by
      have hz := (Unitary.mem_iff.mp (Submonoid.pow_mem _ hζu m₁)).2
      have hd := (Unitary.mem_iff.mp hαu).1
      rw [star_mul] at h1
      linear_combination -ζ ^ m₁ * h1 + ζ ^ m₂ * (star (d 0) * d 0) * hz + ζ ^ m₂ * hd
    exact (mul_eq_zero.mp (by linear_combination hdot)).resolve_left (sub_ne_zero.mpr hcoeff)
  have hv_norm (m : ℕ) : dotProduct (star (vNat m)) (vNat m) = 1 := by
    simpa [vNat, dotProduct, Pi.single_apply] using
      hunitary_dot (Submonoid.pow_mem _ B₁.property m) (Pi.single 0 1) (Pi.single 0 1)
  have hVu : Vmat ∈ unitaryGroup (Fin r) ℂ := by
    rw [mem_unitaryGroup_iff']
    ext k l
    have hentry : (star Vmat * Vmat) k l = dotProduct (star (vNat k.val)) (vNat l.val) := by
      rw [Matrix.mul_apply, dotProduct]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [star_apply, Pi.star_apply]
    rw [hentry]
    by_cases hkl : k = l
    · subst hkl; simp [hv_norm]
    · simp [hkl, hv_orth (fun h => hkl (Fin.ext (hζ.pow_inj k.isLt l.isLt h)))]
  exact ⟨hαu, hv_eig, hv_orth, hv_norm, hVu⟩

/-- The `r`-th orbit vector `vNat r` returns to a unit-modulus scalar multiple of `vNat 0`. -/
private theorem eigenvectorOrbit_return {r : ℕ} [NeZero r] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    {vNat : ℕ → Fin r → ℂ}
    (hv_orth : ∀ {m₁ m₂}, ζ ^ m₁ ≠ ζ ^ m₂ → dotProduct (star (vNat m₁)) (vNat m₂) = 0)
    (hv_norm : ∀ m, dotProduct (star (vNat m)) (vNat m) = 1)
    (hVu : (fun i (k : Fin r) => vNat k.val i) ∈ unitaryGroup (Fin r) ℂ) :
    ∃ β : Circle, vNat r = (β : ℂ) • vNat 0 := by
  let Vmat : Matrix (Fin r) (Fin r) ℂ := fun i k => vNat k.val i
  let β : ℂ := dotProduct (star (vNat 0)) (vNat r)
  have hVr : star Vmat *ᵥ vNat r = β • Pi.single 0 1 := by
    ext k
    have hL : (star Vmat *ᵥ vNat r) k = dotProduct (star (vNat k.val)) (vNat r) := by
      rw [mulVec, dotProduct]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [star_apply, Pi.star_apply]
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
    rw [mulVec_mulVec, mem_unitaryGroup_iff.mp hVu, one_mulVec, mulVec_smul] at h1
    have hVe0 : Vmat *ᵥ Pi.single 0 1 = vNat 0 := by
      ext i
      simp [Vmat, mulVec, dotProduct, Pi.single_apply]
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
    (B₁ : unitaryGroup (Fin r) ℂ) (b β : Circle) (hbpow : (b : ℂ) ^ r = β)
    (vNat : ℕ → Fin r → ℂ)
    (hv_step : ∀ m, (B₁ : Matrix (Fin r) (Fin r) ℂ) *ᵥ vNat m = vNat (m + 1))
    (hv_r : vNat r = (β : ℂ) • vNat 0)
    (W : unitaryGroup (Fin r) ℂ)
    (hW_col : ∀ k : Fin r,
      (W : Matrix (Fin r) (Fin r) ℂ).col k = (((b⁻¹ : Circle) : ℂ) ^ k.val) • vNat k.val) :
    (B₁ : Matrix (Fin r) (Fin r) ℂ) * (W : Matrix (Fin r) (Fin r) ℂ) =
      (W : Matrix (Fin r) (Fin r) ℂ) * ((b : ℂ) • (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne r)
  ext i k
  have hW_entry (j k : Fin (m + 1)) :
      (W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) j k =
        (((b⁻¹ : Circle) : ℂ) ^ k.val) * vNat k.val j := by
    rw [← Matrix.col_apply (W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) k j,
      hW_col k, Pi.smul_apply, smul_eq_mul]
  have hL : ((B₁ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) *
      (W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) i k =
      ((B₁ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) *ᵥ
        (W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).col k) i :=
    (Matrix.col_apply _ k i).symm.trans (congrFun Matrix.col_mul_eq_mulVec_col i)
  have hR : ((W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) *
      ((b : ℂ) • (shiftUnitary (m + 1) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ))) i k =
      (b : ℂ) * (W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) i (k + 1) := by
    rw [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
    congr 1
    rw [shiftUnitary, coe_permutationUnitary, Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv]
    simp [Equiv.addRight_symm]
  rw [hL, hW_col k, mulVec_smul, hv_step k.val, hR, hW_entry]
  simp only [Pi.smul_apply, smul_eq_mul, Fin.val_add_one, Circle.coe_inv]
  have hb0 : (b : ℂ) ≠ 0 := Circle.coe_ne_zero b
  split_ifs with hk
  · subst hk
    have hv_r_i : vNat (m + 1) i = (β : ℂ) * vNat 0 i := congrFun hv_r i
    have hpow : (b : ℂ)⁻¹ ^ m * (b : ℂ) ^ m = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hb0, one_pow]
    simp only [Fin.val_last, hv_r_i, pow_zero, ← hbpow, pow_succ]
    linear_combination (b : ℂ) * vNat 0 i * hpow
  · rw [pow_succ']
    linear_combination -((b : ℂ)⁻¹ ^ k.val * vNat (k.val + 1) i) * mul_inv_cancel₀ hb0

/-- Given unitary matrices `A₁ = diagonal d` and `B₁` with `A₁ * B₁ = ζ • (B₁ * A₁)`, there is a
unitary matrix `W` simultaneously conjugating `(A₁, B₁)` to `(α • C₀, b • S₀)` for unit-modulus
scalars `α, b : Circle`. -/
private theorem exists_unitary_conj_diagonal_to_clock_shift {r : ℕ} [NeZero r] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) {d : Fin r → ℂ} {A₁ B₁ : unitaryGroup (Fin r) ℂ}
    (hA₁ : (A₁ : Matrix (Fin r) (Fin r) ℂ) = diagonal d)
    (hrel : (A₁ : Matrix (Fin r) (Fin r) ℂ) * (B₁ : Matrix (Fin r) (Fin r) ℂ) =
      ζ • ((B₁ : Matrix (Fin r) (Fin r) ℂ) * (A₁ : Matrix (Fin r) (Fin r) ℂ))) :
    ∃ (W : unitaryGroup (Fin r) ℂ) (α b : Circle),
      star (W : Matrix (Fin r) (Fin r) ℂ) * (A₁ : Matrix (Fin r) (Fin r) ℂ) *
        (W : Matrix (Fin r) (Fin r) ℂ) = (α : ℂ) • (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ) ∧
      star (W : Matrix (Fin r) (Fin r) ℂ) * (B₁ : Matrix (Fin r) (Fin r) ℂ) *
        (W : Matrix (Fin r) (Fin r) ℂ) = (b : ℂ) • (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ) := by
  let vNat (m : ℕ) : Fin r → ℂ := ((B₁ : Matrix (Fin r) (Fin r) ℂ) ^ m) *ᵥ Pi.single 0 1
  let Vmat : Matrix (Fin r) (Fin r) ℂ := fun i k => vNat k.val i
  obtain ⟨hαu, hv_eig, hv_orth, hv_norm, hVu⟩ := eigenvectorOrbit_mem_unitary hζ hA₁ hrel
  let α : Circle := ⟨d 0, mem_sphere_zero_iff_norm.mpr (CStarRing.norm_of_mem_unitary hαu)⟩
  obtain ⟨β, hv_r⟩ := eigenvectorOrbit_return hζ hv_orth hv_norm hVu
  obtain ⟨b, hb⟩ := β.exists_pow_nat_eq (NeZero.ne r)
  have hbpow : (b : ℂ) ^ r = β := by rw [← Circle.coe_pow, hb]
  let Dmat : Matrix (Fin r) (Fin r) ℂ :=
    diagonal fun k : Fin r => ((b⁻¹ : Circle) : ℂ) ^ k.val
  have hDu : Dmat ∈ unitaryGroup (Fin r) ℂ := by
    rw [diagonal_mem_unitary, Pi.mem_unitary_iff]
    exact fun k => Submonoid.pow_mem _ (b⁻¹).coe_mem_unitary k.val
  let W : unitaryGroup (Fin r) ℂ := ⟨Vmat, hVu⟩ * ⟨Dmat, hDu⟩
  have hW_entry (i k : Fin r) : (W : Matrix (Fin r) (Fin r) ℂ) i k =
      vNat k.val i * ((b⁻¹ : Circle) : ℂ) ^ k.val := by
    dsimp only [W, Dmat]
    rw [Submonoid.coe_mul, mul_diagonal]
  have hW_col (k : Fin r) :
      (W : Matrix (Fin r) (Fin r) ℂ).col k = (((b⁻¹ : Circle) : ℂ) ^ k.val) • vNat k.val := by
    ext j
    simp [Matrix.col_apply, hW_entry, mul_comm]
  have hAW : (A₁ : Matrix (Fin r) (Fin r) ℂ) * (W : Matrix (Fin r) (Fin r) ℂ) =
      (W : Matrix (Fin r) (Fin r) ℂ) *
        ((α : ℂ) • (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ)) := by
    ext i k
    have hL : ((A₁ : Matrix (Fin r) (Fin r) ℂ) * (W : Matrix (Fin r) (Fin r) ℂ)) i k =
        ((A₁ : Matrix (Fin r) (Fin r) ℂ) *ᵥ (W : Matrix (Fin r) (Fin r) ℂ).col k) i :=
      (Matrix.col_apply _ k i).symm.trans (congrFun Matrix.col_mul_eq_mulVec_col i)
    rw [hL, hW_col k, mulVec_smul, hv_eig k.val]
    simp only [Pi.smul_apply, smul_eq_mul, coe_clockUnitary, Matrix.mul_smul, mul_diagonal,
      Matrix.smul_apply, hW_entry, α]
    ring
  have hBW := shift_intertwine_of_orbit B₁ b β hbpow vNat
    (fun m => by simp only [vNat, pow_succ', mulVec_mulVec]) hv_r W hW_col
  refine ⟨W, α, b, ?_, ?_⟩
  · rw [Matrix.mul_assoc, hAW, ← Matrix.mul_assoc, mem_unitaryGroup_iff'.mp W.property,
      Matrix.one_mul]
  · rw [Matrix.mul_assoc, hBW, ← Matrix.mul_assoc, mem_unitaryGroup_iff'.mp W.property,
      Matrix.one_mul]

/-- **Finite Stone–von Neumann uniqueness for unitary Weyl pairs.** If `A, B ∈ U(r)` satisfy the
Weyl relation `A * B = ζ • (B * A)` for a primitive `r`-th root of unity `ζ`, then some unitary
matrix `U` simultaneously conjugates `(A, B)` to `(α • C₀, b • S₀)` with `α, b : Circle`. -/
theorem exists_unitary_conj_to_clock_shift {r : ℕ} [NeZero r] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) (A B : unitaryGroup (Fin r) ℂ)
    (hrel : (A : Matrix (Fin r) (Fin r) ℂ) * (B : Matrix (Fin r) (Fin r) ℂ) =
      ζ • ((B : Matrix (Fin r) (Fin r) ℂ) * (A : Matrix (Fin r) (Fin r) ℂ))) :
    ∃ (U : unitaryGroup (Fin r) ℂ) (α b : Circle),
      star (U : Matrix (Fin r) (Fin r) ℂ) * (A : Matrix (Fin r) (Fin r) ℂ) *
        (U : Matrix (Fin r) (Fin r) ℂ) = (α : ℂ) • (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ) ∧
      star (U : Matrix (Fin r) (Fin r) ℂ) * (B : Matrix (Fin r) (Fin r) ℂ) *
        (U : Matrix (Fin r) (Fin r) ℂ) = (b : ℂ) • (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ) := by
  have : IsStarNormal (A : Matrix (Fin r) (Fin r) ℂ) := Unitary.coe_isStarNormal A
  obtain ⟨U₁mat, hU₁u, d, hd⟩ :=
    exists_mem_unitaryGroup_star_mul_mul_eq_diagonal (A : Matrix (Fin r) (Fin r) ℂ)
  let U₁ : unitaryGroup (Fin r) ℂ := ⟨U₁mat, hU₁u⟩
  let A₁ : unitaryGroup (Fin r) ℂ := U₁⁻¹ * A * U₁
  let B₁ : unitaryGroup (Fin r) ℂ := U₁⁻¹ * B * U₁
  have hrel₁ : (A₁ : Matrix (Fin r) (Fin r) ℂ) * (B₁ : Matrix (Fin r) (Fin r) ℂ) =
      ζ • ((B₁ : Matrix (Fin r) (Fin r) ℂ) * (A₁ : Matrix (Fin r) (Fin r) ℂ)) := by
    let φ := Unitary.conjStarAlgAut ℂ (Matrix (Fin r) (Fin r) ℂ) U₁⁻¹
    have hφ (X : unitaryGroup (Fin r) ℂ) :
        ((U₁⁻¹ : unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
          (X : Matrix (Fin r) (Fin r) ℂ) * (U₁ : Matrix (Fin r) (Fin r) ℂ) = φ X := by
      simp only [φ, Unitary.conjStarAlgAut_apply, UnitaryGroup.inv_val, star_star]
    simp only [A₁, B₁, Submonoid.coe_mul]
    rw [hφ A, hφ B, ← map_mul, hrel, map_smul, map_mul]
  have hA₁ : (A₁ : Matrix (Fin r) (Fin r) ℂ) = diagonal d := by
    simpa only [A₁, Submonoid.coe_mul, UnitaryGroup.inv_val, U₁] using hd
  obtain ⟨W, α, b, hWA, hWB⟩ := exists_unitary_conj_diagonal_to_clock_shift hζ hA₁ hrel₁
  refine ⟨U₁ * W, α, b, ?_, ?_⟩
  · rw [← hWA]
    simp only [A₁, Submonoid.coe_mul, UnitaryGroup.inv_val, U₁, star_mul, Matrix.mul_assoc]
  · rw [← hWB]
    simp only [B₁, Submonoid.coe_mul, UnitaryGroup.inv_val, U₁, star_mul, Matrix.mul_assoc]

/-- Existence of rescaled clock and shift matrices `A₀ = c₁ • C₀`, `B₀ = c₂ • S₀` in `SU(r)`
satisfying `⁅A₀, B₀⁆ = ζ • 1`. -/
theorem exists_clock_shift_specialUnitaryGroup {r : ℕ} [NeZero r] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) :
    ∃ (c₁ c₂ : Circle) (A₀ B₀ : specialUnitaryGroup (Fin r) ℂ),
      (A₀ : Matrix (Fin r) (Fin r) ℂ) = (c₁ : ℂ) • (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ) ∧
      (B₀ : Matrix (Fin r) (Fin r) ℂ) = (c₂ : ℂ) • (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ) ∧
      ((⁅A₀, B₀⁆ : specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = ζ • 1 := by
  obtain ⟨c₁, hc₁⟩ := exists_circle_smul_mem_specialUnitaryGroup (clockUnitary hζ)
  obtain ⟨c₂, hc₂⟩ := exists_circle_smul_mem_specialUnitaryGroup (shiftUnitary r)
  let A₀ : specialUnitaryGroup (Fin r) ℂ := ⟨_, hc₁⟩
  let B₀ : specialUnitaryGroup (Fin r) ℂ := ⟨_, hc₂⟩
  refine ⟨c₁, c₂, A₀, B₀, rfl, rfl, specialUnitaryGroup.commutatorElement_eq_smul_one_iff.mpr ?_⟩
  simp only [A₀, B₀, Matrix.smul_mul, Matrix.mul_smul, clockUnitary_mul_shiftUnitary hζ, smul_smul]
  congr 1
  ring

/-- Determinant comparison: if `X ∈ SU(r)` is unitarily conjugate to `s • M` and `X₀ ∈ SU(r)`
equals `c • M` (for `M ∈ U(r)` and `s ≠ 0`), then `c / s` is a power of the primitive `r`-th
root `ζ`. -/
theorem exists_pow_mul_eq_of_unitary_conj_specialUnitaryGroup {r : ℕ} [NeZero r] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) {U M : unitaryGroup (Fin r) ℂ}
    {X X₀ : specialUnitaryGroup (Fin r) ℂ} {s c : ℂ} (hs : s ≠ 0)
    (h1 : star (U : Matrix (Fin r) (Fin r) ℂ) * (X : Matrix (Fin r) (Fin r) ℂ) *
      (U : Matrix (Fin r) (Fin r) ℂ) = s • (M : Matrix (Fin r) (Fin r) ℂ))
    (h2 : (X₀ : Matrix (Fin r) (Fin r) ℂ) = c • (M : Matrix (Fin r) (Fin r) ℂ)) :
    ∃ k < r, ζ ^ k * s = c := by
  have hdetM : (M : Matrix (Fin r) (Fin r) ℂ).det ≠ 0 := fun h0 => by
    have hnorm := CStarRing.norm_of_mem_unitary (det_of_mem_unitary M.property)
    rw [h0, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hd1 : s ^ r * (M : Matrix (Fin r) (Fin r) ℂ).det = 1 := by
    have hdet1 := congrArg det h1
    rw [det_conj_of_mul_eq_one (mem_unitaryGroup_iff'.mp U.property)
        (mem_unitaryGroup_iff.mp U.property),
      (mem_specialUnitaryGroup_iff.mp X.property).2, det_smul, Fintype.card_fin] at hdet1
    exact hdet1.symm
  have hd2 : c ^ r * (M : Matrix (Fin r) (Fin r) ℂ).det = 1 := by
    simpa [det_smul, (mem_specialUnitaryGroup_iff.mp X₀.property).2] using (congrArg det h2).symm
  have hpow : (c * s⁻¹) ^ r = 1 := by
    have heq : c ^ r = s ^ r := mul_right_cancel₀ hdetM (hd2.trans hd1.symm)
    rw [mul_pow, inv_pow, heq, mul_inv_cancel₀ (pow_ne_zero r hs)]
  obtain ⟨k, hk, hζk⟩ := hζ.eq_pow_of_pow_eq_one hpow
  exact ⟨k, hk, by rw [hζk, inv_mul_cancel_right₀ hs]⟩

/-- Any solution `A, B ∈ SU(r)` of `⁅A, B⁆ = ζ • 1` is simultaneously `SU(r)`-conjugate to any
rescaled clock–shift pair `(A₀, B₀)` in `SU(r)`. -/
theorem exists_specialUnitaryGroup_conj_to_clock_shift {r : ℕ} [NeZero r] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) {c₁ c₂ : ℂ} {A₀ B₀ : specialUnitaryGroup (Fin r) ℂ}
    (hA₀ : (A₀ : Matrix (Fin r) (Fin r) ℂ) =
      c₁ • (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ))
    (hB₀ : (B₀ : Matrix (Fin r) (Fin r) ℂ) =
      c₂ • (shiftUnitary r : Matrix (Fin r) (Fin r) ℂ))
    (A B : specialUnitaryGroup (Fin r) ℂ)
    (hAB : ((⁅A, B⁆ : specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = ζ • 1) :
    ∃ u : specialUnitaryGroup (Fin r) ℂ,
      ConjAct.toConjAct u • A = A₀ ∧ ConjAct.toConjAct u • B = B₀ := by
  have hrel := specialUnitaryGroup.commutatorElement_eq_smul_one_iff.mp hAB
  obtain ⟨U₂, α, b, hU₂A, hU₂B⟩ := exists_unitary_conj_to_clock_shift hζ
    ⟨A, (mem_specialUnitaryGroup_iff.mp A.property).1⟩
    ⟨B, (mem_specialUnitaryGroup_iff.mp B.property).1⟩ hrel
  obtain ⟨p, _, hc₁⟩ := exists_pow_mul_eq_of_unitary_conj_specialUnitaryGroup hζ
    (Circle.coe_ne_zero α) hU₂A hA₀
  obtain ⟨q, _, hc₂⟩ := exists_pow_mul_eq_of_unitary_conj_specialUnitaryGroup hζ
    (Circle.coe_ne_zero b) hU₂B hB₀
  let P : unitaryGroup (Fin r) ℂ := (clockUnitary hζ) ^ q * ((shiftUnitary r)⁻¹) ^ p
  have ⟨hPA, hPB⟩ := clockUnitary_shiftUnitary_phase_conj hζ p q α b
  let U : unitaryGroup (Fin r) ℂ := P * U₂⁻¹
  obtain ⟨c, hc⟩ := exists_circle_smul_mem_specialUnitaryGroup U
  let u : specialUnitaryGroup (Fin r) ℂ := ⟨(c : ℂ) • (U : Matrix (Fin r) (Fin r) ℂ), hc⟩
  have hu (X : specialUnitaryGroup (Fin r) ℂ) :
      ((ConjAct.toConjAct u • X : specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
        (U : Matrix (Fin r) (Fin r) ℂ) * (X : Matrix (Fin r) (Fin r) ℂ) *
          star (U : Matrix (Fin r) (Fin r) ℂ) := by
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, ← star_eq_inv]
    simp only [Submonoid.coe_mul, specialUnitaryGroup.coe_star, u, star_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, (Unitary.mem_iff.mp c.coe_mem_unitary).1, one_smul]
  refine ⟨u, Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [hu A, hA₀, ← hc₁, ← hPA, ← hU₂A]
    simp only [U, P, Submonoid.coe_mul, UnitaryGroup.inv_val, star_mul, star_star, Matrix.mul_assoc]
  · rw [hu B, hB₀, ← hc₂, ← hPB, ← hU₂B]
    simp only [U, P, Submonoid.coe_mul, UnitaryGroup.inv_val, star_mul, star_star, Matrix.mul_assoc]

end Matrix
