/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import TauCeti.Algebra.Star.Rosati.Basic
public import TauCeti.LinearAlgebra.Matrix.PosDef.Quaternion
import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.Central.Matrix
import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.RingTheory.SimpleRing.Matrix
import TauCeti.Algebra.Central.Quaternion
import TauCeti.Algebra.CentralSimple.SkolemNoether.Star
import TauCeti.Algebra.Quaternion.Basic
import TauCeti.Algebra.Star.Equiv
import TauCeti.Algebra.Star.Positive
import TauCeti.Algebra.Star.Rosati.Matrix.Trace
import TauCeti.Algebra.Star.Rosati.SquareRoot
import TauCeti.Algebra.Star.SelfAdjoint
import TauCeti.Algebra.Star.SelfAdjoint.LinearMap
import TauCeti.LinearAlgebra.Matrix.ConjTranspose
import TauCeti.LinearAlgebra.Matrix.Hermitian.Quaternion

/-!
# Positive involutions on simple real matrix algebras

For `D ∈ {ℝ, ℂ, ℍ[ℝ]}` and an `ℝ`-star algebra `A` with `φ : A ≃ₐ[ℝ] Matrix n n D` and cyclic
`t : A →ₗ[ℝ] ℝ` strictly positive on `x * star x`, constructs `e : A ≃⋆ₐ[ℝ] Matrix n n D`
matching `TauCeti.IsRosatiPositive t` with `Matrix.PosDef` or `Matrix.QuatPosDef`
(`AlgEquiv.exists_starAlgEquiv_matrix_real`, `AlgEquiv.exists_starAlgEquiv_matrix_complex`,
`AlgEquiv.exists_starAlgEquiv_matrix_quaternion`).

## References

* J. Voight, *Quaternion Algebras*, GTM 288, Springer (2021), §8.4.
* M. Lipnowski and J. Tsimerman, *How large is A_g(F_q)?*, arXiv:1511.02212v1, §4.3.2.
-/

public section

open scoped Matrix ComplexOrder _root_.Quaternion

namespace TauCeti

section SharedNormalization

variable {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A] {n : Type*} [Fintype n] [DecidableEq n]

private theorem comp_traceLinearMap_conj_pos_of_trace_eq {D : Type*} [Ring D] [Algebra ℝ D]
    [StarRing D] {rePart : D →ₗ[ℝ] ℝ} (φ : A ≃ₐ[ℝ] Matrix n n D) (t : A →ₗ[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c)
    (ht : ∀ x, t x = c * (rePart.comp (Matrix.traceLinearMap n ℝ D)) (φ x))
    (hpos : ∀ x, x ≠ 0 → 0 < t (x * star x)) (u : (Matrix n n D)ˣ)
    (hσ : ∀ x, φ (star x) = (u : Matrix n n D) * (φ x)ᴴ * (↑u⁻¹ : Matrix n n D))
    (X : Matrix n n D) (hX : X ≠ 0) :
    0 < (rePart.comp (Matrix.traceLinearMap n ℝ D))
      (X * (u : Matrix n n D) * Xᴴ * (↑u⁻¹ : Matrix n n D)) := by
  have h1 := hpos (φ.symm X) fun h ↦ hX (by simpa using congrArg φ h)
  rw [ht, map_mul, hσ, AlgEquiv.apply_symm_apply] at h1
  simpa only [mul_assoc] using pos_of_mul_pos_right h1 hc.le

private theorem exists_starAlgEquiv_matrix_of_hermitian_unit {D : Type*} [DivisionRing D]
    [Algebra ℝ D] [StarRing D] [Module.Finite ℝ D] [Nonempty n] {rePart : D →ₗ[ℝ] ℝ}
    (hre_cyc : ∀ a b : D, rePart (a * b) = rePart (b * a))
    (hre_pos : ∀ a : D, a ≠ 0 → 0 < rePart (a * star a))
    (hre_sa : ∀ a : D, IsSelfAdjoint a → a = algebraMap ℝ D (rePart a))
    (φ : A ≃ₐ[ℝ] Matrix n n D) (t : A →ₗ[ℝ] ℝ) (c : ℝ) (hc : 0 < c)
    (ht : ∀ x, t x = c * (rePart.comp (Matrix.traceLinearMap n ℝ D)) (φ x))
    (hpos : ∀ x, x ≠ 0 → 0 < t (x * star x)) (u : (Matrix n n D)ˣ)
    (huH : (u : Matrix n n D)ᴴ = u)
    (hσ : ∀ x, φ (star x) = (u : Matrix n n D) * (φ x)ᴴ * (↑u⁻¹ : Matrix n n D)) :
    ∃ e : A ≃⋆ₐ[ℝ] Matrix n n D, ∀ s : A, IsRosatiPositive t s ↔
      IsRosatiPositive (rePart.comp (Matrix.traceLinearMap n ℝ D)) (e s) := by
  let T := rePart.comp (Matrix.traceLinearMap n ℝ D)
  have huinvH : (↑u⁻¹ : Matrix n n D)ᴴ = ↑u⁻¹ := IsSelfAdjoint.of_mul_eq_one huH u.mul_inv
  have hre1 : rePart 1 = 1 :=
    ((algebraMap ℝ D).injective (by simpa using hre_sa 1 (IsSelfAdjoint.one D))).symm
  let v₀ : n → D := Pi.single (Classical.arbitrary n) 1
  have hv₀ : v₀ ≠ 0 := fun h ↦ by simpa [v₀] using congrFun h (Classical.arbitrary n)
  set α : ℝ := rePart (star v₀ ⬝ᵥ ((↑u⁻¹ : Matrix n n D) *ᵥ v₀))
  have hprod (w : n → D) (hw : w ≠ 0) : 0 < α * rePart (star w ⬝ᵥ ((u : Matrix n n D) *ᵥ w)) := by
    have h1 := comp_traceLinearMap_conj_pos_of_trace_eq φ t c hc ht hpos u hσ
      (Matrix.vecMulVec v₀ (star w)) (by simp [hv₀, hw])
    rwa [LinearMap.comp_traceLinearMap_vecMulVec_mul_mul_conjTranspose_mul hre_cyc,
      hre_sa _ (Matrix.IsHermitian.star_dotProduct_mulVec_comm huinvH v₀ v₀),
      hre_sa _ (Matrix.IsHermitian.star_dotProduct_mulVec_comm huH w w), ← map_mul,
      Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, hre1, mul_one] at h1
  let a : (Matrix n n D)ˣ := if α < 0 then -u else u
  have haPos : IsRosatiPositive T (a : Matrix n n D) := by
    refine (Matrix.isRosatiPositive_comp_traceLinearMap_iff _ hre_cyc).mpr ⟨by
      dsimp only [a]; split_ifs <;> [exact Matrix.IsHermitian.neg huH; exact huH],
      fun w hw ↦ ?_⟩
    have hp := hprod w hw; dsimp only [a]; split_ifs with hlt
    · rw [Units.val_neg, Matrix.neg_mulVec, dotProduct_neg, map_neg]; nlinarith
    · exact pos_of_mul_pos_right hp (not_lt.mp hlt)
  obtain ⟨_, r, hrPos, hrsq, -, -, -, -⟩ := rosatiPositiveSquareRoot T
    (LinearMap.comp_traceLinearMap_cyclic hre_cyc)
    (fun _ hX ↦ LinearMap.comp_traceLinearMap_mul_star_pos hre_pos hX) (a : Matrix n n D) haPos
  have hrH : (r : Matrix n n D)ᴴ = r := hrPos.isSelfAdjoint
  have hrInvH : (↑r⁻¹ : Matrix n n D)ᴴ = ↑r⁻¹ := IsSelfAdjoint.of_mul_eq_one hrH r.mul_inv
  let eAlg := φ.trans (MulSemiringAction.toAlgEquiv ℝ _ (ConjAct.toConjAct r⁻¹))
  have he x : eAlg x = (↑r⁻¹ : Matrix n n D) * φ x * r := by simp [eAlg, ConjAct.units_smul_def]
  let e : A ≃⋆ₐ[ℝ] Matrix n n D := StarAlgEquiv.ofAlgEquiv eAlg fun x ↦ by
    have haConj : (a : Matrix n n D) * (φ x)ᴴ * (↑a⁻¹ : Matrix n n D) =
        (u : Matrix n n D) * (φ x)ᴴ * (↑u⁻¹ : Matrix n n D) := by
      dsimp only [a]; split_ifs <;> simp
    have haUnit : a = r * r := Units.ext hrsq.symm
    simp [he, Matrix.star_eq_conjTranspose, hσ, ← haConj, haUnit, hrH, hrInvH, mul_assoc]
  refine ⟨e, fun s ↦ ?_⟩
  rw [show t = (c • T).comp e.toAlgEquiv.toLinearMap by
      ext x
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul,
        AlgEquiv.toLinearMap_apply, e, StarAlgEquiv.coe_toAlgEquiv, StarAlgEquiv.ofAlgEquiv_apply]
      rw [ht x, he x, LinearMap.comp_traceLinearMap_cyclic hre_cyc _ (r : Matrix n n D),
        ← mul_assoc, r.mul_inv, one_mul],
    e.isRosatiPositive_comp_iff, isRosatiPositive_iff, isRosatiPositive_iff]
  exact and_congr_right fun _ ↦ forall₂_congr fun _ _ ↦
    ⟨fun h ↦ pos_of_mul_pos_right h hc.le, fun h ↦ mul_pos hc h⟩

private theorem exists_cyclic_trace_pos {D : Type*} [Ring D] [Nontrivial D] [Algebra ℝ D]
    [Nonempty n] (φ : A ≃ₐ[ℝ] Matrix n n D) (t : A →ₗ[ℝ] ℝ)
    (hcyc : ∀ x y, t (x * y) = t (y * x)) (hpos : ∀ x, x ≠ 0 → 0 < t (x * star x)) :
    ∃ τ : D →ₗ[ℝ] ℝ, 0 < τ 1 ∧ (∀ a b, τ (a * b) = τ (b * a)) ∧
      ∀ x, t x = τ (Matrix.trace (φ x)) := by
  obtain ⟨τ, hτ_cyc, hτ⟩ := LinearMap.exists_eq_comp_matrixTrace_of_cyclic
    (t.comp φ.symm.toLinearMap) fun _ _ ↦ by simp [hcyc]
  have htpos : 0 < (Fintype.card n : ℝ) * τ 1 := by
    have h := hτ 1
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_one, Matrix.trace_one] at h
    rw [← nsmul_one (Fintype.card n), ← Nat.cast_smul_eq_nsmul ℝ, map_smul, smul_eq_mul] at h
    exact h ▸ by simpa using hpos 1 fun h0 ↦
      (one_ne_zero : (1 : Matrix n n D) ≠ 0) (by simpa using congrArg φ h0)
  exact ⟨τ, pos_of_mul_pos_right htpos (Nat.cast_pos.mpr Fintype.card_pos).le, hτ_cyc,
    fun x ↦ by simpa using hτ (φ x)⟩

private theorem exists_starAlgEquiv_empty {D : Type*} [Ring D] [Algebra ℝ D] [StarRing D]
    [IsEmpty n] (φ : A ≃ₐ[ℝ] Matrix n n D) (t : A →ₗ[ℝ] ℝ) (P : Matrix n n D → Prop)
    (hP : ∀ X, P X) : ∃ e : A ≃⋆ₐ[ℝ] Matrix n n D, ∀ s : A, IsRosatiPositive t s ↔ P (e s) :=
  have : Subsingleton A := φ.injective.subsingleton
  ⟨StarAlgEquiv.ofAlgEquiv φ fun _ ↦ Subsingleton.elim _ _, fun _ ↦
    ⟨fun _ ↦ hP _, fun _ ↦ isRosatiPositive_iff.mpr
      ⟨Subsingleton.elim _ _, fun x hx ↦ absurd (Subsingleton.elim x 0) hx⟩⟩⟩

private theorem exists_starAlgEquiv_trivial_star {D : Type*} [DivisionRing D] [Algebra ℝ D]
    [StarRing D] [StarModule ℝ D] [Algebra.IsCentral ℝ D] [Module.Finite ℝ D]
    (rePart : D →ₗ[ℝ] ℝ) (hre_cyc : ∀ a b : D, rePart (a * b) = rePart (b * a))
    (hre_pos : ∀ a : D, a ≠ 0 → 0 < rePart (a * star a))
    (hre_sa : ∀ a : D, IsSelfAdjoint a → a = algebraMap ℝ D (rePart a))
    (hD_cyc : ∀ τ : D →ₗ[ℝ] ℝ, (∀ a b, τ (a * b) = τ (b * a)) → ∀ a, τ a = τ 1 * rePart a)
    (hno_skew : ∀ [Nonempty n] (u : (Matrix n n D)ˣ), (u : Matrix n n D)ᴴ = -u →
      (∀ X ≠ 0, 0 < (rePart.comp (Matrix.traceLinearMap n ℝ D))
        (X * (u : Matrix n n D) * Xᴴ * (↑u⁻¹ : Matrix n n D))) → False)
    (φ : A ≃ₐ[ℝ] Matrix n n D) (t : A →ₗ[ℝ] ℝ)
    (hcyc : ∀ x y, t (x * y) = t (y * x)) (hpos : ∀ x, x ≠ 0 → 0 < t (x * star x)) :
    ∃ e : A ≃⋆ₐ[ℝ] Matrix n n D, ∀ s : A, IsRosatiPositive t s ↔
      IsRosatiPositive (rePart.comp (Matrix.traceLinearMap n ℝ D)) (e s) := by
  rcases isEmpty_or_nonempty n with _ | _
  · exact exists_starAlgEquiv_empty φ t _ fun _ ↦
      (Matrix.isRosatiPositive_comp_traceLinearMap_iff _ hre_cyc).mpr
        ⟨Matrix.ext fun i _ ↦ isEmptyElim i, fun _ hv ↦ absurd (funext fun i ↦ isEmptyElim i) hv⟩
  have : StarModule ℝ A := starModule_of_trace_mul_star_pos t hpos
  obtain ⟨τ, hc, hτ_cyc, hτ⟩ := exists_cyclic_trace_pos φ t hcyc hpos
  have ht x : t x = τ 1 * (rePart.comp (Matrix.traceLinearMap n ℝ D)) (φ x) := by
    rw [hτ x, hD_cyc τ hτ_cyc, LinearMap.comp_apply, Matrix.traceLinearMap_apply]
  let α := φ.starConjAlgEquiv ℝ fun r ↦ by simp [Algebra.algebraMap_eq_smul_one, star_smul]
  obtain ⟨u, huSign, hu⟩ := exists_unit_conj_star_eq_self_or_neg_of_central ℝ α fun X ↦ by simp [α]
  have hσ x : φ (star x) = (u : Matrix n n D) * (φ x)ᴴ * (↑u⁻¹ : Matrix n n D) := by
    simpa [α, Matrix.star_eq_conjTranspose] using hu (φ x)ᴴ
  exact exists_starAlgEquiv_matrix_of_hermitian_unit hre_cyc hre_pos hre_sa φ t (τ 1) hc ht
    hpos u ((by simpa [Matrix.star_eq_conjTranspose] using huSign :
      (u : Matrix n n D)ᴴ = u ∨ (u : Matrix n n D)ᴴ = -u).resolve_right fun hskew ↦
      hno_skew u hskew (comp_traceLinearMap_conj_pos_of_trace_eq φ t (τ 1) hc ht hpos u hσ)) hσ

end SharedNormalization

section RealFactor

private theorem not_pos_of_skewSymmetric_real {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (u : (Matrix n n ℝ)ˣ) (hskew : (u : Matrix n n ℝ)ᴴ = -u)
    (hpos : ∀ X : Matrix n n ℝ, X ≠ 0 →
      0 < ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).comp (Matrix.traceLinearMap n ℝ ℝ))
        (X * (u : Matrix n n ℝ) * Xᴴ * (↑u⁻¹ : Matrix n n ℝ))) : False := by
  let v₀ : n → ℝ := Pi.single (Classical.arbitrary n) 1
  have hposX := hpos (Matrix.vecMulVec v₀ (star v₀))
    (by simp [show v₀ ≠ 0 from fun h ↦ by simpa [v₀] using congrFun h (Classical.arbitrary n)])
  have hsa := Matrix.star_dotProduct_mulVec_self_of_skewHermitian hskew v₀
  rw [star_trivial] at hsa
  rw [LinearMap.comp_traceLinearMap_vecMulVec_mul_mul_conjTranspose_mul mul_comm, show
      star v₀ ⬝ᵥ ((u : Matrix n n ℝ) *ᵥ v₀) = 0 by linarith, mul_zero, map_zero] at hposX
  exact lt_irrefl 0 hposX

end RealFactor

section ComplexFactor

private theorem star_I_smul_one_eq_neg {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] (φ : A ≃ₐ[ℝ] Matrix n n ℂ)
    (t : A →ₗ[ℝ] ℝ) (hpos : ∀ x, x ≠ 0 → 0 < t (x * star x)) :
    φ (star (φ.symm (Complex.I • (1 : Matrix n n ℂ)))) = -(Complex.I • (1 : Matrix n n ℂ)) := by
  let M := Matrix n n ℂ; let z : M := Complex.I • 1; let w : M := φ (star (φ.symm z))
  have hw : w ∈ Subalgebra.center ℂ M := Subalgebra.mem_center_iff.mpr fun Y ↦ by
    have hcomm : φ (star (φ.symm Y)) * z = z * φ (star (φ.symm Y)) := by simp [z]
    simpa [w, map_mul, star_mul] using (congrArg (fun X ↦ φ (star (φ.symm X))) hcomm).symm
  rw [Algebra.IsCentral.center_eq_bot ℂ M, Algebra.mem_bot] at hw; obtain ⟨c, hc⟩ := hw
  have hc_sq : c * c = -1 := (algebraMap ℂ M).injective <| by
    have hz2 : z * z = -1 := by simp [z, smul_smul, Complex.I_mul_I]
    simpa [hc, w] using congrArg (fun X ↦ φ (star (φ.symm X))) hz2
  rcases (mul_eq_zero.mp (by linear_combination hc_sq - Complex.I_mul_I :
      (c - Complex.I) * (c + Complex.I) = 0)).imp sub_eq_zero.mp eq_neg_of_add_eq_zero_left with
      rfl | rfl
  · have h1 := hpos (φ.symm z) fun h0 ↦ Complex.I_ne_zero <| by
      simpa [z, M] using congrFun (congrFun (congrArg φ h0)
        (Classical.arbitrary n)) (Classical.arbitrary n)
    have h2 : φ.symm z * star (φ.symm z) = -1 := φ.injective <| by
      simpa [w, z, smul_smul, Algebra.algebraMap_eq_smul_one] using congrArg (z * ·) hc.symm
    have hone : 0 < t 1 := by
      simpa using hpos 1 fun h0 ↦ one_ne_zero (α := M) (by simpa using congrArg φ h0)
    rw [h2, map_neg] at h1; linarith
  · simpa [w, z, Algebra.algebraMap_eq_smul_one, neg_smul] using hc.symm

private theorem trace_eq_mul_comp_traceLinearMap_complex {A : Type*} [Ring A] [Algebra ℝ A]
    [StarRing A] {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (φ : A ≃ₐ[ℝ] Matrix n n ℂ)
    (hI : φ (star (φ.symm (Complex.I • (1 : Matrix n n ℂ)))) =
      -(Complex.I • (1 : Matrix n n ℂ)))
    (t' : A →ₗ[ℝ] ℝ) (hcyc' : ∀ x y, t' (x * y) = t' (y * x))
    (hstar' : ∀ x, t' (star x) = t' x) (hpos' : ∀ x, x ≠ 0 → 0 < t' (x * star x)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ x, t' x = c * (Complex.reLm.comp (Matrix.traceLinearMap n ℝ ℂ)) (φ x) := by
  obtain ⟨τ, hc, -, hτ⟩ := exists_cyclic_trace_pos φ t' hcyc' hpos'
  have hτI : τ Complex.I = 0 := by
    have h2 : t' (φ.symm (Complex.I • 1)) = -t' (φ.symm (Complex.I • 1)) := by
      conv_lhs => rw [← hstar', ← AlgEquiv.symm_apply_apply φ (star _), hI, map_neg, map_neg]
    rw [hτ, AlgEquiv.apply_symm_apply, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul,
      mul_comm, ← Complex.ofReal_natCast, ← Complex.real_smul, map_smul, smul_eq_mul] at h2
    exact (mul_eq_zero.mp (by linarith : (Fintype.card n : ℝ) * τ Complex.I = 0)).resolve_left
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  refine ⟨τ 1, hc, fun x ↦ ?_⟩
  have htr : Matrix.trace (φ x) =
      (Matrix.trace (φ x)).re • (1 : ℂ) + (Matrix.trace (φ x)).im • Complex.I := by
    simp [Complex.real_smul, Complex.re_add_im]
  rw [hτ x, htr, map_add, map_smul, map_smul, hτI, smul_zero, add_zero, smul_eq_mul, mul_comm]
  simp only [LinearMap.comp_apply, Matrix.traceLinearMap_apply, Complex.reLm_coe]

end ComplexFactor

section QuaternionFactor

private theorem not_pos_of_skewHermitian_quaternion {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (u : (Matrix n n ℍ[ℝ])ˣ) (hskew : (u : Matrix n n ℍ[ℝ])ᴴ = -u)
    (hpos : ∀ X : Matrix n n ℍ[ℝ], X ≠ 0 →
      0 < ((QuaternionAlgebra.reₗ (-1) 0 (-1)).comp (Matrix.traceLinearMap n ℝ ℍ[ℝ]))
        (X * (u : Matrix n n ℍ[ℝ]) * Xᴴ * (↑u⁻¹ : Matrix n n ℍ[ℝ]))) : False := by
  set Uinv : Matrix n n ℍ[ℝ] := (↑u⁻¹ : Matrix n n ℍ[ℝ])
  have huinv_skew : Uinvᴴ = -Uinv := by
    have h := congrArg (fun M ↦ M * (-Uinv)) (congrArg Matrix.conjTranspose u.mul_inv)
    rw [Matrix.conjTranspose_mul, hskew, Matrix.conjTranspose_one] at h
    simpa [Uinv, mul_assoc] using h
  let i₀ : n := Classical.arbitrary n; let v₀ : n → ℍ[ℝ] := Pi.single i₀ 1
  have hv₀ : v₀ ≠ 0 := fun h ↦ by simpa [v₀] using congrFun h i₀
  set r : ℍ[ℝ] := star v₀ ⬝ᵥ (Uinv *ᵥ v₀)
  set s : ℍ[ℝ] := star v₀ ⬝ᵥ ((u : Matrix n n ℍ[ℝ]) *ᵥ v₀)
  have hpos0 : 0 < (r * s).re := by
    have h := hpos (Matrix.vecMulVec v₀ (star v₀)) (by simp [hv₀])
    rwa [LinearMap.comp_traceLinearMap_vecMulVec_mul_mul_conjTranspose_mul
      (rePart := QuaternionAlgebra.reₗ (-1) 0 (-1)) Quaternion.re_mul_comm
      (u : Matrix n n ℍ[ℝ]) Uinv v₀ v₀] at h
  obtain ⟨q, hq0, _, hqconj⟩ := Quaternion.exists_pure_neg_conj r
    (Matrix.re_dotProduct_mulVec_eq_zero_of_skewHermitian huinv_skew v₀)
  let v₁ : n → ℍ[ℝ] := fun i ↦ v₀ i * q
  have hv₁ : v₁ ≠ 0 := fun h ↦ by have := congrFun h i₀; simp [v₁, v₀, hq0] at this
  have hpos1 : 0 < (-(Quaternion.normSq q • r) * s).re := by
    have h := hpos (Matrix.vecMulVec v₁ (star v₀)) (by simp [hv₁, hv₀])
    rwa [LinearMap.comp_traceLinearMap_vecMulVec_mul_mul_conjTranspose_mul
        (rePart := QuaternionAlgebra.reₗ (-1) 0 (-1)) Quaternion.re_mul_comm
        (u : Matrix n n ℍ[ℝ]) Uinv v₁ v₀,
      show star v₁ ⬝ᵥ (Uinv *ᵥ v₁) = star q * r * q by
        simp only [dotProduct, Matrix.mulVec, v₁, r, Pi.star_apply, star_mul, Finset.mul_sum,
          Finset.sum_mul, mul_assoc], hqconj] at h
  have hnq : 0 < Quaternion.normSq q := lt_of_not_ge fun h ↦ hq0 (Quaternion.normSq_le_zero.mp h)
  simp only [neg_mul, QuaternionAlgebra.re_neg, smul_mul_assoc, QuaternionAlgebra.re_smul,
    smul_eq_mul] at hpos1; nlinarith

end QuaternionFactor

end TauCeti

namespace AlgEquiv

open TauCeti

/-- Existence of a star-preserving `ℝ`-algebra isomorphism `e : A ≃⋆ₐ[ℝ] Matrix n n ℝ`
identifying `TauCeti.IsRosatiPositive t` with `Matrix.PosDef`. -/
theorem exists_starAlgEquiv_matrix_real {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    {n : Type*} [Fintype n] [DecidableEq n] (φ : A ≃ₐ[ℝ] Matrix n n ℝ)
    (t : A →ₗ[ℝ] ℝ) (hcyclic : ∀ x y : A, t (x * y) = t (y * x))
    (hpos : ∀ x : A, x ≠ 0 → 0 < t (x * star x)) :
    ∃ e : A ≃⋆ₐ[ℝ] Matrix n n ℝ, ∀ s : A, IsRosatiPositive t s ↔ (e s).PosDef := by
  obtain ⟨e, he⟩ := exists_starAlgEquiv_trivial_star (LinearMap.id : ℝ →ₗ[ℝ] ℝ) mul_comm
    (fun a ha ↦ by simpa using mul_self_pos.mpr ha) (fun _ _ ↦ rfl)
    (fun τ _ a ↦ by simpa [mul_comm] using τ.map_smul a (1 : ℝ))
    not_pos_of_skewSymmetric_real φ t hcyclic hpos
  exact ⟨e, fun s ↦ by simpa using he s⟩

/-- Existence of a star-preserving `ℝ`-algebra isomorphism `e : A ≃⋆ₐ[ℝ] Matrix n n ℂ`
identifying `TauCeti.IsRosatiPositive t` with `Matrix.PosDef`. -/
theorem exists_starAlgEquiv_matrix_complex {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    {n : Type*} [Fintype n] [DecidableEq n] (φ : A ≃ₐ[ℝ] Matrix n n ℂ)
    (t : A →ₗ[ℝ] ℝ) (hcyclic : ∀ x y : A, t (x * y) = t (y * x))
    (hpos : ∀ x : A, x ≠ 0 → 0 < t (x * star x)) :
    ∃ e : A ≃⋆ₐ[ℝ] Matrix n n ℂ, ∀ s : A, IsRosatiPositive t s ↔ (e s).PosDef := by
  rcases isEmpty_or_nonempty n with _ | _
  · exact exists_starAlgEquiv_empty φ t _ fun _ ↦ Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨Subsingleton.elim _ _, fun v hv ↦ absurd (Subsingleton.elim v 0) hv⟩
  · -- Normalize the star-symmetrized functional `t' x = (t x + t (star x)) / 2`, which has the
    -- same Rosati-positive cone as `t`.
    have : StarModule ℝ A := starModule_of_trace_mul_star_pos t hpos
    let t' : A →ₗ[ℝ] ℝ := (t.comp (selfAdjoint.submodule ℝ A).subtype).comp (selfAdjointPart ℝ)
    have hpos' (x : A) (hx : x ≠ 0) : 0 < t' (x * star x) :=
      LinearMap.comp_selfAdjointPart_mul_star_pos hpos hx
    have hI := star_I_smul_one_eq_neg φ t' hpos'
    obtain ⟨c, hc, ht⟩ := trace_eq_mul_comp_traceLinearMap_complex φ hI t'
      (LinearMap.comp_selfAdjointPart_cyclic hcyclic) t.comp_selfAdjointPart_star hpos'
    let α := φ.starConjAlgEquiv ℂ fun z ↦ by
      have hz1 (w : ℂ) : w • (1 : Matrix n n ℂ) =
          w.re • (1 : Matrix n n ℂ) + w.im • (Complex.I • (1 : Matrix n n ℂ)) := by
        conv_lhs => rw [← Complex.re_add_im w]
        rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
      rw [Algebra.algebraMap_eq_smul_one, star_smul, star_one, hz1 (star z), hz1 z]
      simp [hI, neg_smul]
    obtain ⟨u, μ, hu, huμ, hμsq⟩ := exists_unit_conj_star_of_central ℂ α fun X ↦ by simp [α]
    obtain ⟨u', hu'sa, hu'conj⟩ := u.exists_isSelfAdjoint_conj_eq_of_star_eq_smul μ huμ hμsq
    have hσ x : φ (star x) = (u' : Matrix n n ℂ) * (φ x)ᴴ * (↑u'⁻¹ : Matrix n n ℂ) := by
      rw [hu'conj]; simpa [α, Matrix.star_eq_conjTranspose] using hu (φ x)ᴴ
    obtain ⟨e, hePos⟩ := exists_starAlgEquiv_matrix_of_hermitian_unit (rePart := Complex.reLm)
      (fun a b ↦ by rw [mul_comm])
      (fun a ha ↦ by simpa [Complex.normSq_apply] using Complex.normSq_pos.mpr ha)
      (fun a ha ↦ Complex.ext rfl (by
        simp [(congrArg Complex.im (Complex.conj_eq_iff_re.mp ha.star_eq)).symm]))
      φ t' c hc ht hpos' u' (Matrix.isHermitian_iff_isSelfAdjoint.mpr hu'sa) hσ
    exact ⟨e, fun s ↦ by
      rw [← isRosatiPositive_iff_of_symmetrize
          (fun x ↦ by simpa [t', div_eq_inv_mul] using LinearMap.comp_selfAdjointPart_apply t x)
          hcyclic, hePos]; simp⟩

/-- Existence of a star-preserving `ℝ`-algebra isomorphism `e : A ≃⋆ₐ[ℝ] Matrix n n ℍ[ℝ]`
identifying `TauCeti.IsRosatiPositive t` with `Matrix.QuatPosDef`. -/
theorem exists_starAlgEquiv_matrix_quaternion {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    {n : Type*} [Fintype n] [DecidableEq n] (φ : A ≃ₐ[ℝ] Matrix n n ℍ[ℝ])
    (t : A →ₗ[ℝ] ℝ) (hcyclic : ∀ x y : A, t (x * y) = t (y * x))
    (hpos : ∀ x : A, x ≠ 0 → 0 < t (x * star x)) :
    ∃ e : A ≃⋆ₐ[ℝ] Matrix n n ℍ[ℝ], ∀ s : A, IsRosatiPositive t s ↔ (e s).QuatPosDef := by
  obtain ⟨e, he⟩ := exists_starAlgEquiv_trivial_star (QuaternionAlgebra.reₗ (-1) 0 (-1))
    Quaternion.re_mul_comm (fun _ ha ↦ Quaternion.re_mul_star_pos ha)
    (fun _ ha ↦ Quaternion.star_eq_self.mp ha)
    (fun τ hcyc q ↦ LinearMap.apply_eq_map_one_mul_re_of_cyclic τ hcyc q)
    not_pos_of_skewHermitian_quaternion φ t hcyclic hpos
  exact ⟨e, fun s ↦ by simpa using he s⟩

end AlgEquiv
