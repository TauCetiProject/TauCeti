/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.GraphAutomorphism
public import TauCeti.LinearAlgebra.Projectivization.AffineChart
public import TauCeti.FieldTheory.Finite.PowAddSelf
import Mathlib.FieldTheory.Finite.Basic

/-!
# Coordinates on the rank-one unitary isotropic points

For the signed reversal form in dimension three, every isotropic point other than
`[1 : 0 : 0]` has unique coordinates `[z : x : 1]`, with
`z + σ(z) = σ(x) x`. This identifies the permutation domain of the rank-one unitary
group with a point at infinity and an affine trace equation. The coordinates describe
the point orbits used in the rank-one unitary Bruhat decomposition, without assuming
that the field has odd characteristic. The parametrization works for any field
endomorphism; involutivity is needed only to interpret the form as a unitary form.
Over a field of order `q²` with the `q`-power involution, there are exactly `q³ + 1`
isotropic points.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Chapter 13 (the unitary groups).
* D. E. Taylor, *The Geometry of the Classical Groups*, Chapter 10.
-/

public section

open Matrix
open scoped LinearAlgebra.Projectivization

namespace TauCeti.UnitaryRankOne

/-- The sesquilinear pairing for the signed reversal form in dimension three. -/
theorem pairing_eq (K : Type*) [CommRing K] (σ : K →+* K) (v w : Fin 3 → K) :
    (σ ∘ v) ⬝ᵥ ((typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K) *ᵥ w) =
      σ (v 0) * w 2 - σ (v 1) * w 1 + σ (v 2) * w 0 := by
  simp [dotProduct, mulVec, Fin.sum_univ_succ, typeAGraphConjugator_apply]
  ring

variable (K : Type*) [Field K] (σ : K →+* K)

/-- The distinguished isotropic point `[1 : 0 : 0]`. -/
def infinity : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ :=
  ⟨Projectivization.mk K ![1, 0, 0] (by simp), by
    rw [Matrix.mk_mem_isotropicPoints_iff, pairing_eq]
    simp⟩

/-- An affine isotropic point `[z : x : 1]`, with its trace equation. -/
def point (c : {c : K × K // c.1 + σ c.1 = σ c.2 * c.2}) :
    (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ :=
  ⟨Projectivization.mk K ![c.1.1, c.1.2, 1] (by
    intro h
    have := congrFun h 2
    simp at this), by
    rw [Matrix.mk_mem_isotropicPoints_iff, pairing_eq]
    dsimp
    simp only [map_one, mul_one, one_mul]
    linear_combination c.2⟩

/-- The homogeneous coordinates of the point at infinity. -/
@[simp]
theorem coe_infinity :
    (infinity K σ : ℙ K (Fin 3 → K)) = Projectivization.mk K ![1, 0, 0] (by simp) := (rfl)

/-- The homogeneous coordinates of an affine isotropic point. -/
@[simp]
theorem coe_point (c : {c : K × K // c.1 + σ c.1 = σ c.2 * c.2}) :
    (point K σ c : ℙ K (Fin 3 → K)) =
      Projectivization.mk K ![c.1.1, c.1.2, 1] (by
        intro h
        have := congrFun h 2
        simp at this) := (rfl)

/-- The last standard affine chart recovers the two coordinates of an affine isotropic point. -/
@[simp↓]
theorem affineChart_point (c : {c : K × K // c.1 + σ c.1 = σ c.2 * c.2}) :
    Projectivization.affineChart 2 (point K σ c : ℙ K (Fin 3 → K)) = ![c.1.1, c.1.2] := by
  ext i
  fin_cases i <;> simp [point, Fin.succAbove]

/-- The affine parametrization is injective, so the normalized coordinates are unique. -/
theorem point_injective : Function.Injective (point K σ) := by
  intro c d h
  have hc := congrArg (fun p :
      (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ =>
    Projectivization.affineChart 2 (p : ℙ K (Fin 3 → K))) h
  rw [affineChart_point, affineChart_point] at hc
  apply Subtype.ext
  exact Prod.ext (by simpa using congrFun hc 0) (by simpa using congrFun hc 1)

/-- No affine isotropic point is the point at infinity. -/
@[simp]
theorem point_ne_infinity (c : {c : K × K // c.1 + σ c.1 = σ c.2 * c.2}) :
    point K σ c ≠ infinity K σ := by
  intro h
  have hp : (point K σ c : ℙ K (Fin 3 → K)) ∈ Projectivization.affineOpen 2 := by
    simp [point]
  rw [h] at hp
  simp [infinity] at hp

/-- The complement of the last affine chart consists of the single point at infinity. -/
theorem eq_infinity_iff (p :
    (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ) :
    p = infinity K σ ↔ (p : ℙ K (Fin 3 → K)) ∉ Projectivization.affineOpen 2 := by
  constructor
  · rintro rfl
    simp [infinity]
  · intro hp
    obtain ⟨p, hpiso⟩ := p
    induction p using Projectivization.ind with | h v hv => ?_
    rw [Projectivization.mk_mem_affineOpen_iff, not_not] at hp
    rw [Matrix.mk_mem_isotropicPoints_iff, pairing_eq] at hpiso
    have hv1 : v 1 = 0 := by
      have : σ (v 1) * v 1 = 0 := by simpa [hp] using hpiso
      exact (mul_eq_zero.mp this).elim (fun h => (map_eq_zero σ).mp h) id
    apply Subtype.ext
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨v 0, ?_⟩
    ext i
    fin_cases i <;> simp [hp, hv1]

/-- Every non-infinite isotropic point has normalized affine coordinates satisfying the trace
equation. No condition on `σ` beyond being a field endomorphism is needed. -/
theorem exists_point (p :
    (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ)
    (hp : p ≠ infinity K σ) : ∃ c, point K σ c = p := by
  have hopen := not_not.mp (mt (eq_infinity_iff K σ p).mpr hp)
  let a := Projectivization.affineChart 2 (p : ℙ K (Fin 3 → K))
  have ha : (Projectivization.affineChart 2).symm a = (p : ℙ K (Fin 3 → K)) :=
    (Projectivization.affineChart 2).left_inv (by simpa using hopen)
  have hvec : Fin.insertNth (α := fun _ ↦ K) (2 : Fin 3) 1 a = ![a 0, a 1, 1] := by
    apply Fin.insertNth_eq_iff.mpr
    refine ⟨rfl, ?_⟩
    ext i
    fin_cases i <;> simp [Fin.removeNth, Fin.succAbove]
  have hiso : a 0 + σ (a 0) = σ (a 1) * a 1 := by
    have hi := p.2
    rw [← ha, Projectivization.affineChart_symm_apply,
      Matrix.mk_mem_isotropicPoints_iff, pairing_eq, hvec] at hi
    dsimp at hi
    simp only [map_one, mul_one, one_mul] at hi
    linear_combination hi
  refine ⟨⟨(a 0, a 1), hiso⟩, Subtype.ext ?_⟩
  rw [← ha, Projectivization.affineChart_symm_apply]
  simp only [point]
  congr 1
  exact hvec.symm

/-- The isotropic points of the dimension-three signed reversal form are exactly the affine
trace-equation solutions together with one point at infinity. -/
noncomputable def pointsEquiv :
    Option {c : K × K // c.1 + σ c.1 = σ c.2 * c.2} ≃
      (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ :=
  Equiv.ofBijective (fun c => c.elim (infinity K σ) (point K σ)) ⟨by
    rintro (_ | c) (_ | d) h
    · rfl
    · exact (point_ne_infinity K σ d h.symm).elim
    · exact (point_ne_infinity K σ c h).elim
    · exact congrArg some (point_injective K σ h), by
    intro p
    by_cases hp : p = infinity K σ
    · exact ⟨none, hp.symm⟩
    · obtain ⟨c, hc⟩ := exists_point K σ p hp
      exact ⟨some c, hc⟩⟩

@[simp]
theorem pointsEquiv_none : pointsEquiv K σ none = infinity K σ := (rfl)

@[simp]
theorem pointsEquiv_some (c : {c : K × K // c.1 + σ c.1 = σ c.2 * c.2}) :
    pointsEquiv K σ (some c) = point K σ c := (rfl)

/-- Over a field of order `q²`, the rank-one unitary permutation domain has `q³ + 1` points,
including its point at infinity. This also includes characteristic two. -/
theorem natCard_isotropicPoints {p n : ℕ} [ExpChar K p]
    (hK : Nat.card K = (p ^ n) ^ 2) (hσ : ∀ a, σ a = a ^ p ^ n) :
    Nat.card ((typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ) =
      (p ^ n) ^ 3 + 1 := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ (expChar_pos K p).ne'))
  let := Fintype.ofFinite K
  have hpow (a : K) : a ^ (p ^ n) ^ 2 = a := by
    rw [← hK, Nat.card_eq_fintype_card]
    exact _root_.FiniteField.pow_card a
  have hfib (x : K) : Nat.card {z : K // z ^ p ^ n + z = x ^ p ^ n * x} = p ^ n := by
    apply FiniteField.natCard_pow_add_self_eq hK
    rw [mul_pow, ← pow_mul, ← sq, hpow, mul_comm]
  have hcoords : Nat.card {c : K × K // c.1 + σ c.1 = σ c.2 * c.2} = (p ^ n) ^ 3 := by
    let e : {c : K × K // c.1 + σ c.1 = σ c.2 * c.2} ≃
        {c : K × K // c.2 ^ p ^ n + c.2 = c.1 ^ p ^ n * c.1} :=
      Equiv.subtypeEquiv (Equiv.prodComm K K) (by intro c; simp [hσ, add_comm])
    rw [Nat.card_congr e,
      Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
        fun x z : K => z ^ p ^ n + z = x ^ p ^ n * x), Nat.card_sigma]
    simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [← Nat.card_eq_fintype_card, hK]
    ring
  rw [← Nat.card_congr (pointsEquiv K σ)]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_option] using
    congrArg (· + 1) hcoords

end TauCeti.UnitaryRankOne
