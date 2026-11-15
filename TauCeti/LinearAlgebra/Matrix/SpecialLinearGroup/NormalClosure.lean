/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection
import Mathlib.Tactic.LinearCombination
import TauCeti.Data.ZMod.StableRange

/-!
# Normal closures of transvections and congruence kernels in `SL(2, R)`

Let `H` be a normal subgroup of `SL(2, R)` over a commutative ring `R`, and let `I` be an ideal of
`R` such that the upper transvection `1 + x E₀₁` lies in `H` for every `x ∈ I`. Conjugation by the
Weyl element `!![0, -1; 1, 0]` puts the lower transvections `1 + x E₁₀` into `H`, a Whitehead-type
conjugation identity puts every unit diagonal `diag(u, u⁻¹)` with `u - 1 ∈ I` into `H`, and Gauss
elimination puts into `H` every `g ∈ SL(2, R)` with `g 0 0` a unit and
`g 0 0 - 1, g 0 1, g 1 0 ∈ I`.

Specializing to `R = ZMod M` for `M ≠ 0`, Bass stable range one (`ZMod.exists_isUnit_add_mul`)
allows shifting the first row of any matrix congruent to `1` modulo `(t)` by a `t`-transvection so
that its `(0, 0)` entry becomes a unit. Consequently, for every divisor `d ∣ M`, the normal closure
in `SL(2, ZMod M)` of the single upper transvection `1 + d E₀₁` equals the congruence kernel
`ker (SL(2, ZMod M) → SL(2, ZMod d))`. This is the finite-quotient reduction behind Wohlfahrt's
theorem and its strict lift form due to Kiming, Schütt, and Verrill.

## Main results

* `Matrix.SpecialLinearGroup.transvection_one_zero_mem_of_normal`: a normal subgroup containing all
  upper transvections with parameter in `I` also contains all lower transvections with parameter in
  `I`.
* `Matrix.SpecialLinearGroup.diag2nUnit_mem_of_normal`: such a normal subgroup contains
  `diag2nUnit zero_ne_one u` whenever `(u : R) - 1 ∈ I`.
* `Matrix.SpecialLinearGroup.mem_of_isUnit_apply_zero_zero_of_normal`: such a normal subgroup
  contains every `g ∈ SL(2, R)` with `IsUnit (g 0 0)` and `g 0 0 - 1, g 0 1, g 1 0 ∈ I`.
* `Matrix.SpecialLinearGroup.mem_normalClosure_transvection_of_mem_span`: in `SL(2, ZMod M)` for
  `M ≠ 0`, every matrix congruent to `1` modulo `Ideal.span {t}` lies in the normal closure of
  `transvection zero_ne_one t`.
* `Matrix.SpecialLinearGroup.normalClosure_transvection_natCast_eq_ker_map_castHom`: for `d ∣ M`
  and `M ≠ 0`, `normalClosure {transvection zero_ne_one (d : ZMod M)}` is the kernel of reduction
  `SL(2, ZMod M) →* SL(2, ZMod d)`.
* `Matrix.SpecialLinearGroup.normalClosure_transvection_one_eq_top`: for `M ≠ 0`, `SL(2, ZMod M)`
  is the normal closure of `transvection zero_ne_one 1`.

## References

* K. Wohlfahrt, *An extension of F. Klein's level concept*, Illinois J. Math. 8 (1964), 529–535.
* I. Kiming, M. Schütt, and H. A. Verrill, *Lifts of projective congruence groups*,
  J. London Math. Soc. (2) 83 (2011), 96–120, §3, Lemma 7 and Proposition 3.
-/

public section

open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

section CommRing

variable {R : Type*} [CommRing R] {I : Ideal R} {H : Subgroup SL(2, R)} [H.Normal]

/-- Conjugating an upper transvection by `!![0, -1; 1, 0]` produces a lower transvection, so any
normal subgroup of `SL(2, R)` containing upper `I`-transvections also contains lower
`I`-transvections. -/
theorem transvection_one_zero_mem_of_normal
    (hH : ∀ x ∈ I, transvection (zero_ne_one : (0 : Fin 2) ≠ 1) x ∈ H)
    {x : R} (hx : x ∈ I) :
    transvection (one_ne_zero : (1 : Fin 2) ≠ 0) x ∈ H := by
  let w : SL(2, R) := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
  have hw_inv : w⁻¹ = ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩ := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    change (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) R) * !![0, 1; -1, 0] = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hconj : w * transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (-x) * w⁻¹ =
      transvection (one_ne_zero : (1 : Fin 2) ≠ 0) x := by
    rw [hw_inv]
    apply Subtype.ext
    change (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) R) *
        (transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (-x) : Matrix (Fin 2) (Fin 2) R) *
        !![0, 1; -1, 0] = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [transvection_coe, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  rw [← hconj]
  exact ‹H.Normal›.conj_mem _ (hH (-x) (I.neg_mem hx)) w

/-- **Whitehead factorization modulo `I`.** Any normal subgroup of `SL(2, R)` containing upper
`I`-transvections contains `diag(u, u⁻¹)` for every unit `u : Rˣ` with `(u : R) - 1 ∈ I`. -/
theorem diag2nUnit_mem_of_normal
    (hH : ∀ x ∈ I, transvection (zero_ne_one : (0 : Fin 2) ≠ 1) x ∈ H)
    {u : Rˣ} (hu : (u : R) - 1 ∈ I) :
    diag2nUnit (zero_ne_one : (0 : Fin 2) ≠ 1) u ∈ H := by
  let x : R := (u : R) - 1
  let σ : SL(2, R) := transvection (one_ne_zero : (1 : Fin 2) ≠ 0) 1
  have hrel : diag2nUnit (zero_ne_one : (0 : Fin 2) ≠ 1) u *
      transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (↑u⁻¹ * x) =
      transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (x * ↑u⁻¹) *
        (σ⁻¹ * transvection (zero_ne_one : (0 : Fin 2) ≠ 1) x * σ) := by
    have hinv : σ⁻¹ = transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (-1) := by
      apply inv_eq_of_mul_eq_one_right
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [σ, coe_mul, transvection_coe, Matrix.mul_apply, Matrix.single_apply]
    have hu_inv : (u : R) * ↑u⁻¹ = 1 := Units.mul_inv u
    rw [hinv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [σ, x, diag2nUnit_coe, coe_mul, transvection_coe, Fin.zero_eta, Fin.isValue,
        Fin.mk_one, Matrix.diagonal_apply, ↓reduceIte, zero_ne_one, one_ne_zero,
        Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, and_self, and_false, false_and,
        add_zero, zero_add, mul_zero, zero_mul, mul_one, one_mul, Matrix.mul_apply,
        Fin.sum_univ_two]
    · ring
    · linear_combination (norm := ring) ((u : R) - 1) * hu_inv
    · linear_combination (norm := ring) -((u : R) - 1) * hu_inv
    · linear_combination (norm := ring) (2 - (u : R)) * hu_inv
  have hprod : diag2nUnit (zero_ne_one : (0 : Fin 2) ≠ 1) u *
      transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (↑u⁻¹ * x) ∈ H := by
    rw [hrel]
    exact mul_mem (transvection_one_zero_mem_of_normal hH (I.mul_mem_right _ hu))
      (by simpa only [inv_inv] using ‹H.Normal›.conj_mem _ (hH x hu) σ⁻¹)
  simpa using mul_mem hprod (inv_mem (hH (↑u⁻¹ * x) (I.mul_mem_left ↑u⁻¹ hu)))

/-- **Gauss elimination modulo `I`.** Any normal subgroup of `SL(2, R)` containing upper
`I`-transvections contains every `g ∈ SL(2, R)` whose `(0, 0)` entry is a unit congruent to `1`
modulo `I` and whose off-diagonal entries lie in `I`. -/
theorem mem_of_isUnit_apply_zero_zero_of_normal
    (hH : ∀ x ∈ I, transvection (zero_ne_one : (0 : Fin 2) ≠ 1) x ∈ H)
    {g : SL(2, R)} (hu : IsUnit (g 0 0)) (h00 : g 0 0 - 1 ∈ I) (h01 : g 0 1 ∈ I)
    (h10 : g 1 0 ∈ I) : g ∈ H := by
  obtain ⟨u, hu_eq⟩ := hu
  have hdet : (u : R) * g 1 1 - g 0 1 * g 1 0 = 1 := by
    rw [hu_eq, ← Matrix.det_fin_two, det_coe]
  have hu_inv : (u : R) * ↑u⁻¹ = 1 := Units.mul_inv u
  have hrel : transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (-(g 1 0 * ↑u⁻¹)) * g =
      diag2nUnit (zero_ne_one : (0 : Fin 2) ≠ 1) u *
        transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (↑u⁻¹ * g 0 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [diag2nUnit_coe, coe_mul, transvection_coe, Fin.zero_eta, Fin.isValue,
        Fin.mk_one, Matrix.diagonal_apply, ↓reduceIte, zero_ne_one, one_ne_zero,
        Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, and_self, and_false, false_and,
        add_zero, zero_add, mul_zero, zero_mul, mul_one, one_mul, Matrix.mul_apply,
        Fin.sum_univ_two]
    · exact hu_eq.symm
    · linear_combination (norm := ring) -g 0 1 * hu_inv
    · rw [← hu_eq]
      linear_combination (norm := ring) -g 1 0 * hu_inv
    · linear_combination (norm := ring) -g 1 1 * hu_inv + ↑u⁻¹ * hdet
  have hprod : transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (-(g 1 0 * ↑u⁻¹)) * g ∈ H := by
    rw [hrel]
    exact mul_mem (diag2nUnit_mem_of_normal hH (hu_eq.symm ▸ h00))
      (hH _ (I.mul_mem_left _ h01))
  have hlow : transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (-(g 1 0 * ↑u⁻¹)) ∈ H :=
    transvection_one_zero_mem_of_normal hH (I.neg_mem (I.mul_mem_right _ h10))
  simpa using mul_mem (inv_mem hlow) hprod

end CommRing

section ZMod

/-- In `SL(2, ZMod M)`, the normal closure of `transvection zero_ne_one t` contains every upper
transvection with parameter in `Ideal.span {t}`. -/
private lemma transvection_mem_normalClosure_of_mem_span {M : ℕ} {t x : ZMod M}
    (hx : x ∈ Ideal.span ({t} : Set (ZMod M))) :
    transvection (zero_ne_one : (0 : Fin 2) ≠ 1) x ∈
      Subgroup.normalClosure {transvection (zero_ne_one : (0 : Fin 2) ≠ 1) t} := by
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective r
  have hzpow : transvection (zero_ne_one : (0 : Fin 2) ≠ 1) ((m : ZMod M) * t) =
      transvection (zero_ne_one : (0 : Fin 2) ≠ 1) t ^ m := by
    rw [transvection_zpow, zsmul_eq_mul]
  rw [hzpow]
  exact zpow_mem (Subgroup.subset_normalClosure rfl) m

/-- In `SL(2, ZMod M)` for `M ≠ 0`, every matrix with `g 0 0 - 1`, `g 0 1`, `g 1 0` in
`Ideal.span {t}` lies in the normal closure of `transvection zero_ne_one t`. -/
theorem mem_normalClosure_transvection_of_mem_span {M : ℕ} [NeZero M] {t : ZMod M}
    {g : SL(2, ZMod M)} (h00 : g 0 0 - 1 ∈ Ideal.span ({t} : Set (ZMod M)))
    (h01 : g 0 1 ∈ Ideal.span ({t} : Set (ZMod M)))
    (h10 : g 1 0 ∈ Ideal.span ({t} : Set (ZMod M))) :
    g ∈ Subgroup.normalClosure {transvection (zero_ne_one : (0 : Fin 2) ≠ 1) t} := by
  let I : Ideal (ZMod M) := Ideal.span ({t} : Set (ZMod M))
  have hcop_t : IsCoprime (g 0 0) t := by
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp h00
    exact ⟨1, -r, by linear_combination (norm := ring) -hr⟩
  have hcop_10 : IsCoprime (g 0 0) (g 1 0) := by
    have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
      rw [← Matrix.det_fin_two, det_coe]
    exact ⟨g 1 1, -g 0 1, by linear_combination (norm := ring) hdet⟩
  obtain ⟨k, hk⟩ := ZMod.exists_isUnit_add_mul (hcop_t.mul_right hcop_10)
  let τ : SL(2, ZMod M) := transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (k * t)
  have hτ : τ ∈ Subgroup.normalClosure {transvection (zero_ne_one : (0 : Fin 2) ≠ 1) t} :=
    transvection_mem_normalClosure_of_mem_span (Ideal.mem_span_singleton'.mpr ⟨k, rfl⟩)
  have hτg_00 : (τ * g) 0 0 = g 0 0 + k * (t * g 1 0) := by
    simp [τ, coe_mul, transvection_coe, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply,
      mul_assoc]
  have hτg_01 : (τ * g) 0 1 = g 0 1 + k * t * g 1 1 := by
    simp [τ, coe_mul, transvection_coe, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]
  have hτg_10 : (τ * g) 1 0 = g 1 0 := by
    simp [τ, coe_mul, transvection_coe, Matrix.mul_apply, Fin.sum_univ_two]
  have hτg_mem : τ * g ∈
      Subgroup.normalClosure {transvection (zero_ne_one : (0 : Fin 2) ≠ 1) t} := by
    refine mem_of_isUnit_apply_zero_zero_of_normal (I := I)
      (fun _ hx ↦ transvection_mem_normalClosure_of_mem_span hx)
      (hτg_00 ▸ hk) ?_ ?_ (hτg_10 ▸ h10)
    · rw [hτg_00]
      have hsub : g 0 0 + k * (t * g 1 0) - 1 = (g 0 0 - 1) + k * g 1 0 * t := by ring
      rw [hsub]
      exact I.add_mem h00 (Ideal.mem_span_singleton'.mpr ⟨k * g 1 0, rfl⟩)
    · rw [hτg_01]
      have hterm : k * t * g 1 1 = (k * g 1 1) * t := by ring
      rw [hterm]
      exact I.add_mem h01 (Ideal.mem_span_singleton'.mpr ⟨k * g 1 1, rfl⟩)
  simpa using mul_mem (inv_mem hτ) hτg_mem

/-- **Normal-closure generation of modular congruence kernels.** For `M ≠ 0` and `d ∣ M`, the
normal closure in `SL(2, ZMod M)` of the upper transvection `1 + d E₀₁` is the kernel of the
reduction homomorphism `SL(2, ZMod M) →* SL(2, ZMod d)`. -/
theorem normalClosure_transvection_natCast_eq_ker_map_castHom {d M : ℕ} [NeZero M]
    (hdM : d ∣ M) :
    Subgroup.normalClosure {transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (d : ZMod M)} =
      (map (ZMod.castHom hdM (ZMod d))).ker := by
  refine le_antisymm ?_ fun g hg ↦ ?_
  · refine Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr ?_)
    simp [SetLike.mem_coe, MonoidHom.mem_ker, map_transvection]
  · rw [MonoidHom.mem_ker] at hg
    have hspan (x : ZMod M) (hx : ZMod.castHom hdM (ZMod d) x = 0) :
        x ∈ Ideal.span ({(d : ZMod M)} : Set (ZMod M)) := by
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hx
      obtain ⟨q, hq⟩ := hx
      refine Ideal.mem_span_singleton'.mpr ⟨(q : ZMod M), ?_⟩
      calc
        (q : ZMod M) * (d : ZMod M) = ((d * q : ℕ) : ZMod M) := by push_cast; ring
        _ = x := by rw [← hq, ZMod.natCast_zmod_val]
    have hg00 : ZMod.castHom hdM (ZMod d) (g 0 0 - 1) = 0 := by
      have h00 := congrArg (fun m : SL(2, ZMod d) ↦ m 0 0) hg
      simp only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, coe_one,
        Matrix.one_apply_eq] at h00
      rw [map_sub, map_one, h00, sub_self]
    have hg01 : ZMod.castHom hdM (ZMod d) (g 0 1) = 0 := by
      simpa using congrArg (fun m : SL(2, ZMod d) ↦ m 0 1) hg
    have hg10 : ZMod.castHom hdM (ZMod d) (g 1 0) = 0 := by
      simpa using congrArg (fun m : SL(2, ZMod d) ↦ m 1 0) hg
    exact mem_normalClosure_transvection_of_mem_span
      (hspan _ hg00) (hspan _ hg01) (hspan _ hg10)

/-- For `M ≠ 0`, `SL(2, ZMod M)` is normally generated by the single upper transvection
`1 + E₀₁`. -/
@[simp]
theorem normalClosure_transvection_one_eq_top (M : ℕ) [NeZero M] :
    Subgroup.normalClosure {transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (1 : ZMod M)} = ⊤ := by
  have h := normalClosure_transvection_natCast_eq_ker_map_castHom (one_dvd M)
  rw [Nat.cast_one] at h
  rw [h, eq_top_iff]
  intro g _
  rw [MonoidHom.mem_ker]
  ext i j
  exact Subsingleton.elim _ _

end ZMod

end Matrix.SpecialLinearGroup
