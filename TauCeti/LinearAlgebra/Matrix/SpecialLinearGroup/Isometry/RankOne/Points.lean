/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.GraphAutomorphism
public import TauCeti.LinearAlgebra.Projectivization.AffineChart
import TauCeti.FieldTheory.Finite.PowAddSelf

/-!
# Coordinates on the rank-one unitary isotropic points

For the signed reversal form in dimension three, every isotropic point other than
`[1 : 0 : 0]` has unique coordinates `[z : x : 1]`, with
`z + σ(z) = σ(x) x`. This identifies the isotropic-point permutation domain of `SU₃`
(type `²A₂`, twisted rank one) with a point at infinity and an affine trace equation.
In the finite unitary setting, these two parts are the Borel orbits used in the Bruhat
decomposition, including in characteristic two. The parametrization works for any field
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

variable {K : Type*} [Field K] {σ : K →+* K}

variable (K σ) in
/-- The distinguished isotropic point `[1 : 0 : 0]`. -/
def infinity : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ :=
  ⟨Projectivization.mk K ![1, 0, 0] (by simp), by
    rw [Matrix.mk_mem_isotropicPoints_iff, dotProduct_typeAGraphConjugator_two_mulVec]
    simp⟩

variable (K σ) in
/-- An affine isotropic point `[z : x : 1]`, with its trace equation. -/
def point (c : {c : K × K // c.1 + σ c.1 = σ c.2 * c.2}) :
    (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ :=
  ⟨Projectivization.mk K ![c.1.1, c.1.2, 1] (by
    intro h
    have := congrFun h 2
    simp at this), by
    rw [Matrix.mk_mem_isotropicPoints_iff, dotProduct_typeAGraphConjugator_two_mulVec]
    dsimp
    simp only [map_one, mul_one, one_mul]
    linear_combination c.2⟩

variable (K σ) in
/-- The homogeneous coordinates of the point at infinity. -/
theorem coe_infinity :
    (infinity K σ : ℙ K (Fin 3 → K)) = Projectivization.mk K ![1, 0, 0] (by simp) := (rfl)

/-- The homogeneous coordinates of an affine isotropic point. -/
theorem coe_point (c : {c : K × K // c.1 + σ c.1 = σ c.2 * c.2}) :
    (point K σ c : ℙ K (Fin 3 → K)) =
      Projectivization.mk K ![c.1.1, c.1.2, 1] (by
        intro h
        have := congrFun h 2
        simp at this) := (rfl)

/-- The last standard affine chart recovers the two coordinates of an affine isotropic point. -/
@[simp]
theorem affineChart_point (c : {c : K × K // c.1 + σ c.1 = σ c.2 * c.2}) :
    Projectivization.affineChart 2 (point K σ c : ℙ K (Fin 3 → K)) = ![c.1.1, c.1.2] := by
  ext i
  fin_cases i <;> simp [point, Fin.succAbove]

variable (K σ) in
/-- The affine parametrization is injective, so the normalized coordinates are unique. -/
theorem point_injective : Function.Injective (point K σ) := by
  intro c d h
  have hc := congrArg (fun p :
      (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ =>
    Projectivization.affineChart 2 (p : ℙ K (Fin 3 → K))) h
  rw [affineChart_point, affineChart_point] at hc
  apply Subtype.ext
  exact Prod.ext (by simpa using congrFun hc 0) (by simpa using congrFun hc 1)

/-- Equality of affine isotropic points is equality of their normalized coordinates. -/
@[simp]
theorem point_inj {c d : {c : K × K // c.1 + σ c.1 = σ c.2 * c.2}} :
    point K σ c = point K σ d ↔ c = d :=
  (point_injective K σ).eq_iff

/-- No affine isotropic point is the point at infinity. -/
@[simp]
theorem point_ne_infinity (c : {c : K × K // c.1 + σ c.1 = σ c.2 * c.2}) :
    point K σ c ≠ infinity K σ := by
  intro h
  have hp : (point K σ c : ℙ K (Fin 3 → K)) ∈ Projectivization.affineOpen 2 := by
    simp [point]
  rw [h] at hp
  simp [infinity] at hp

/-- The point at infinity is not an affine isotropic point. -/
@[simp]
theorem infinity_ne_point (c : {c : K × K // c.1 + σ c.1 = σ c.2 * c.2}) :
    infinity K σ ≠ point K σ c :=
  (point_ne_infinity c).symm

/-- An isotropic point lies outside the last standard affine chart exactly when it is the
point at infinity. -/
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
    rw [Matrix.mk_mem_isotropicPoints_iff,
      dotProduct_typeAGraphConjugator_two_mulVec] at hpiso
    have hv1 : v 1 = 0 := by
      have : σ (v 1) * v 1 = 0 := by simpa [hp] using hpiso
      exact (mul_eq_zero.mp this).elim (fun h => (map_eq_zero σ).mp h) id
    apply Subtype.ext
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨v 0, ?_⟩
    ext i
    fin_cases i <;> simp [hp, hv1]

/-- An isotropic point lies in the last standard affine chart exactly when it is not infinity. -/
@[simp]
theorem coe_mem_affineOpen_two_iff (p :
    (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ) :
    (p : ℙ K (Fin 3 → K)) ∈ Projectivization.affineOpen 2 ↔ p ≠ infinity K σ := by
  rw [ne_eq, eq_infinity_iff]
  exact not_not.symm

/-- The last affine chart of any isotropic point satisfies the trace equation. -/
theorem affineChart_add_map_eq (p :
    (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ) :
    let a := Projectivization.affineChart 2 (p : ℙ K (Fin 3 → K))
    a 0 + σ (a 0) = σ (a 1) * a 1 := by
  rcases eq_or_ne p (infinity K σ) with rfl | hp
  · simp [coe_infinity]
  have hopen := not_not.mp (mt (eq_infinity_iff p).mpr hp)
  let a := Projectivization.affineChart 2 (p : ℙ K (Fin 3 → K))
  have ha : (Projectivization.affineChart 2).symm a = (p : ℙ K (Fin 3 → K)) :=
    (Projectivization.affineChart 2).left_inv (by simpa using hopen)
  have hvec : Fin.insertNth (α := fun _ ↦ K) (2 : Fin 3) 1 a = ![a 0, a 1, 1] := by
    apply Fin.insertNth_eq_iff.mpr
    refine ⟨rfl, ?_⟩
    ext i
    fin_cases i <;> simp [Fin.removeNth, Fin.succAbove]
  have hi := p.2
  rw [← ha, Projectivization.affineChart_symm_apply,
    Matrix.mk_mem_isotropicPoints_iff, dotProduct_typeAGraphConjugator_two_mulVec, hvec] at hi
  dsimp at hi
  simp only [map_one, mul_one, one_mul] at hi
  linear_combination hi

/-- Reconstructing a non-infinite isotropic point from its last affine chart recovers it. -/
@[simp]
theorem point_affineChart {p :
    (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ}
    (hp : p ≠ infinity K σ) :
    point K σ ⟨((Projectivization.affineChart 2 (p : ℙ K (Fin 3 → K))) 0,
      (Projectivization.affineChart 2 (p : ℙ K (Fin 3 → K))) 1),
      affineChart_add_map_eq p⟩ = p := by
  apply Subtype.ext
  apply (Projectivization.affineChart 2).injOn
  · simp [point]
  · simpa using not_not.mp (mt (eq_infinity_iff p).mpr hp)
  · rw [affineChart_point]
    ext i
    fin_cases i <;> rfl

/-- Every non-infinite isotropic point has normalized affine coordinates satisfying the trace
equation. No condition on `σ` beyond being a field endomorphism is needed. -/
theorem exists_point {p :
    (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ}
    (hp : p ≠ infinity K σ) : ∃ c, point K σ c = p :=
  ⟨_, point_affineChart hp⟩

variable (K σ) in
/-- The isotropic points of the dimension-three signed reversal form are exactly the affine
trace-equation solutions together with one point at infinity. -/
noncomputable def isotropicPointsEquiv :
    Option {c : K × K // c.1 + σ c.1 = σ c.2 * c.2} ≃
      (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ :=
  Equiv.ofBijective (fun c => c.elim (infinity K σ) (point K σ)) ⟨by
    rintro (_ | c) (_ | d) h
    · rfl
    · exact (point_ne_infinity d h.symm).elim
    · exact (point_ne_infinity c h).elim
    · exact congrArg some (point_injective K σ h), by
    intro p
    by_cases hp : p = infinity K σ
    · exact ⟨none, hp.symm⟩
    · obtain ⟨c, hc⟩ := exists_point hp
      exact ⟨some c, hc⟩⟩

variable (K σ) in
@[simp]
theorem isotropicPointsEquiv_none : isotropicPointsEquiv K σ none = infinity K σ := (rfl)

@[simp]
theorem isotropicPointsEquiv_some (c : {c : K × K // c.1 + σ c.1 = σ c.2 * c.2}) :
    isotropicPointsEquiv K σ (some c) = point K σ c := (rfl)

variable (K σ) in
@[simp]
theorem isotropicPointsEquiv_symm_infinity :
    (isotropicPointsEquiv K σ).symm (infinity K σ) = none :=
  (isotropicPointsEquiv K σ).symm_apply_apply none

@[simp]
theorem isotropicPointsEquiv_symm_point
    (c : {c : K × K // c.1 + σ c.1 = σ c.2 * c.2}) :
    (isotropicPointsEquiv K σ).symm (point K σ c) = some c :=
  (isotropicPointsEquiv K σ).symm_apply_apply (some c)

/-- Away from infinity, the inverse parametrization is given by the last affine chart. -/
theorem isotropicPointsEquiv_symm_apply_of_ne_infinity {p :
    (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ}
    (hp : p ≠ infinity K σ) :
    (isotropicPointsEquiv K σ).symm p =
      some ⟨((Projectivization.affineChart 2 (p : ℙ K (Fin 3 → K))) 0,
        (Projectivization.affineChart 2 (p : ℙ K (Fin 3 → K))) 1),
        affineChart_add_map_eq p⟩ := by
  rw [Equiv.symm_apply_eq, isotropicPointsEquiv_some, point_affineChart hp]

/-- Over a field of order `q²` with `σ(a) = a ^ q`, the dimension-three signed reversal form
has `q³ + 1` isotropic points, the permutation domain for `SU₃(q)` (twisted rank one).
This includes its point at infinity and also holds in characteristic two. -/
theorem natCard_isotropicPoints {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hσ : ∀ a, σ a = a ^ q) :
    Nat.card ((typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ) =
      q ^ 3 + 1 := by
  have hq : q ≠ 0 := by
    intro hq
    simpa [hq] using hσ 0
  have : Finite K := Nat.finite_of_card_ne_zero (hK ▸ pow_ne_zero 2 hq)
  rw [← Nat.card_congr (isotropicPointsEquiv K σ), Finite.card_option]
  simp_rw [hσ]
  rw [FiniteField.natCard_add_pow_eq_pow_mul hK]

end TauCeti.UnitaryRankOne
