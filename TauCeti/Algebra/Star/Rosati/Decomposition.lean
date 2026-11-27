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
import Mathlib.Algebra.Algebra.Prod
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import TauCeti.Algebra.CentralSimple.Real
import TauCeti.Algebra.Star.Basic
import TauCeti.Algebra.Star.Pi
import TauCeti.Algebra.Star.Positive
import TauCeti.Algebra.Star.Rosati.Matrix.Factor
import TauCeti.RingTheory.CentralIdempotent
import TauCeti.RingTheory.Semisimple.Star.Basic

/-!
# Real Rosati decomposition and positivity comparison

A finite-dimensional real star algebra `E` with a cyclic functional `t : E →ₗ[ℝ] ℝ` strictly
positive on `x * star x` decomposes into a finite product of real, complex, and quaternionic
matrix algebras carrying their standard adjoints, matching `TauCeti.IsRosatiPositive t` with
`Matrix.PosDef` and `Matrix.QuatPosDef` in every factor (`TauCeti.realRosatiDecomposition`).

## References

* J. Voight, *Quaternion Algebras*, GTM 288, Springer (2021), §8.4.
* M. Lipnowski and J. Tsimerman, *How large is A_g(F_q)?*, arXiv:1511.02212v1, §4.3.2, Prop. 4.10.
-/

public section

open scoped Matrix ComplexOrder _root_.Quaternion

namespace TauCeti

section FactorAssembly

private inductive FactorNormalForm (A : Type*) [Ring A] [Algebra ℝ A] [StarRing A]
    (t : A →ₗ[ℝ] ℝ) (d : ℕ) where
  | real (e : A ≃⋆ₐ[ℝ] Matrix (Fin d) (Fin d) ℝ)
      (hp : ∀ s, IsRosatiPositive t s ↔ (e s).PosDef)
  | complex (e : A ≃⋆ₐ[ℝ] Matrix (Fin d) (Fin d) ℂ)
      (hp : ∀ s, IsRosatiPositive t s ↔ (e s).PosDef)
  | quaternion (e : A ≃⋆ₐ[ℝ] Matrix (Fin d) (Fin d) ℍ[ℝ])
      (hp : ∀ s, IsRosatiPositive t s ↔ (e s).QuatPosDef)

private theorem nonempty_factorNormalForm {A D : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    [DivisionRing D] [Algebra ℝ D] [Module.Finite ℝ D] {d : ℕ}
    (φ : A ≃ₐ[ℝ] Matrix (Fin d) (Fin d) D) (t : A →ₗ[ℝ] ℝ)
    (hcyc : ∀ x y, t (x * y) = t (y * x)) (hpos : ∀ x, x ≠ 0 → 0 < t (x * star x)) :
    Nonempty (FactorNormalForm A t d) := by
  rcases nonempty_algEquiv_real_or_complex_or_quaternion D with ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩
  · exact ⟨.real _ ((φ.trans ψ.mapMatrix).exists_starAlgEquiv_matrix_real t hcyc hpos).choose_spec⟩
  · exact ⟨.complex _
      ((φ.trans ψ.mapMatrix).exists_starAlgEquiv_matrix_complex t hcyc hpos).choose_spec⟩
  · exact ⟨.quaternion _
      ((φ.trans ψ.mapMatrix).exists_starAlgEquiv_matrix_quaternion t hcyc hpos).choose_spec⟩

section
variable {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A] {t : A →ₗ[ℝ] ℝ} {d : ℕ}
private def FactorNormalForm.tag : FactorNormalForm A t d → Fin 3
  | .real .. => 0 | .complex .. => 1 | .quaternion .. => 2
private theorem FactorNormalForm.tag_eq_two_of_ne {nf : FactorNormalForm A t d}
    (h0 : nf.tag ≠ 0) (h1 : nf.tag ≠ 1) : nf.tag = 2 := by
  have := nf.tag.isLt; omega
private def FactorNormalForm.realEquiv : (nf : FactorNormalForm A t d) → nf.tag = 0 →
    { e : A ≃⋆ₐ[ℝ] Matrix (Fin d) (Fin d) ℝ // ∀ s, IsRosatiPositive t s ↔ (e s).PosDef }
  | .real e hp, _ => ⟨e, hp⟩ | .complex .., h | .quaternion .., h => nomatch h
private def FactorNormalForm.complexEquiv : (nf : FactorNormalForm A t d) → nf.tag = 1 →
    { e : A ≃⋆ₐ[ℝ] Matrix (Fin d) (Fin d) ℂ // ∀ s, IsRosatiPositive t s ↔ (e s).PosDef }
  | .complex e hp, _ => ⟨e, hp⟩ | .real .., h | .quaternion .., h => nomatch h
private def FactorNormalForm.quatEquiv : (nf : FactorNormalForm A t d) → nf.tag = 2 →
    { e : A ≃⋆ₐ[ℝ] Matrix (Fin d) (Fin d) ℍ[ℝ] // ∀ s, IsRosatiPositive t s ↔ (e s).QuatPosDef }
  | .quaternion e hp, _ => ⟨e, hp⟩ | .real .., h | .complex .., h => nomatch h
end

section SplitReindex

private abbrev Mat (d : ℕ) (D : Type*) := Matrix (Fin d) (Fin d) D

private def piSplitTagAlgEquiv {n : ℕ} {A : Fin n → Type*} [∀ i, Ring (A i)]
    [∀ i, Algebra ℝ (A i)] [∀ i, StarRing (A i)] {t : ∀ i, A i →ₗ[ℝ] ℝ} {d : Fin n → ℕ}
    (nf : ∀ i, FactorNormalForm (A i) (t i) (d i)) :
    (∀ i, A i) ≃ₐ[ℝ]
      ((∀ i : {i // (nf i).tag = 0}, A i.val) ×
        (∀ i : {i // (nf i).tag = 1}, A i.val) ×
        (∀ i : {i // (nf i).tag = 2}, A i.val)) where
  toFun x := (fun i ↦ x i.val, fun i ↦ x i.val, fun i ↦ x i.val)
  invFun y i :=
    if h0 : (nf i).tag = 0 then y.1 ⟨i, h0⟩
    else if h1 : (nf i).tag = 1 then y.2.1 ⟨i, h1⟩
    else y.2.2 ⟨i, FactorNormalForm.tag_eq_two_of_ne h0 h1⟩
  left_inv x := funext fun i ↦ by dsimp only; split_ifs <;> rfl
  right_inv y := Prod.ext (funext fun ⟨i, hi⟩ ↦ by dsimp only; split_ifs <;> rfl)
    (Prod.ext
      (funext fun ⟨i, hi⟩ ↦ by dsimp only; split_ifs <;> first | rfl | omega)
      (funext fun ⟨i, hi⟩ ↦ by dsimp only; split_ifs <;> first | rfl | omega))
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

private theorem piSplitTagAlgEquiv_apply {n : ℕ} {A : Fin n → Type*} [∀ i, Ring (A i)]
    [∀ i, Algebra ℝ (A i)] [∀ i, StarRing (A i)] {t : ∀ i, A i →ₗ[ℝ] ℝ} {d : Fin n → ℕ}
    (nf : ∀ i, FactorNormalForm (A i) (t i) (d i)) (x : ∀ i, A i) :
    piSplitTagAlgEquiv nf x =
      (fun i : {i // (nf i).tag = 0} ↦ x i.val, fun i : {i // (nf i).tag = 1} ↦ x i.val,
        fun i : {i // (nf i).tag = 2} ↦ x i.val) := rfl

private noncomputable def splitReindexEquiv {n nR nC nH : ℕ} {A : Fin n → Type*}
    [∀ i, Ring (A i)] [∀ i, Algebra ℝ (A i)] [∀ i, StarRing (A i)]
    {t : ∀ i, A i →ₗ[ℝ] ℝ} {d : Fin n → ℕ} (nf : ∀ i, FactorNormalForm (A i) (t i) (d i))
    (eR : {i // (nf i).tag = 0} ≃ Fin nR) (eC : {i // (nf i).tag = 1} ≃ Fin nC)
    (eH : {i // (nf i).tag = 2} ≃ Fin nH) :
    (∀ i, A i) ≃⋆ₐ[ℝ]
      ((∀ i : Fin nR, Mat (d (eR.symm i).val) ℝ) ×
        (∀ i : Fin nC, Mat (d (eC.symm i).val) ℂ) ×
        (∀ i : Fin nH, Mat (d (eH.symm i).val) ℍ[ℝ])) :=
  let mR := (AlgEquiv.piCongrRight fun i : {i // (nf i).tag = 0} ↦
      ((nf i.val).realEquiv i.property).val.toAlgEquiv).trans
    (AlgEquiv.piCongrLeft' ℝ (fun i : {i // (nf i).tag = 0} ↦ Mat (d i.val) ℝ) eR)
  let mC := (AlgEquiv.piCongrRight fun i : {i // (nf i).tag = 1} ↦
      ((nf i.val).complexEquiv i.property).val.toAlgEquiv).trans
    (AlgEquiv.piCongrLeft' ℝ (fun i : {i // (nf i).tag = 1} ↦ Mat (d i.val) ℂ) eC)
  let mH := (AlgEquiv.piCongrRight fun i : {i // (nf i).tag = 2} ↦
      ((nf i.val).quatEquiv i.property).val.toAlgEquiv).trans
    (AlgEquiv.piCongrLeft' ℝ (fun i : {i // (nf i).tag = 2} ↦ Mat (d i.val) ℍ[ℝ]) eH)
  StarAlgEquiv.ofAlgEquiv ((piSplitTagAlgEquiv nf).trans (mR.prodCongr (mC.prodCongr mH)))
    fun x ↦ Prod.ext
      (funext fun j ↦ by
        simp only [mR, AlgEquiv.trans_apply, AlgEquiv.prodCongr_apply, Equiv.prodCongr_apply,
          EquivLike.coe_coe, Prod.map_fst, AlgEquiv.piCongrLeft'_apply, Equiv.piCongrLeft'_apply,
          AlgEquiv.piCongrRight_apply, piSplitTagAlgEquiv_apply, Prod.fst_star, Pi.star_apply,
          StarAlgEquiv.coe_toAlgEquiv, map_star])
      (Prod.ext
        (funext fun j ↦ by
          simp only [mC, AlgEquiv.trans_apply, AlgEquiv.prodCongr_apply, Equiv.prodCongr_apply,
            EquivLike.coe_coe, Prod.map_snd, Prod.map_fst, AlgEquiv.piCongrLeft'_apply,
            Equiv.piCongrLeft'_apply, AlgEquiv.piCongrRight_apply, piSplitTagAlgEquiv_apply,
            Prod.snd_star, Prod.fst_star, Pi.star_apply, StarAlgEquiv.coe_toAlgEquiv, map_star])
        (funext fun j ↦ by
          simp only [mH, AlgEquiv.trans_apply, AlgEquiv.prodCongr_apply, Equiv.prodCongr_apply,
            EquivLike.coe_coe, Prod.map_snd, AlgEquiv.piCongrLeft'_apply, Equiv.piCongrLeft'_apply,
            AlgEquiv.piCongrRight_apply, piSplitTagAlgEquiv_apply, Prod.snd_star, Pi.star_apply,
            StarAlgEquiv.coe_toAlgEquiv, map_star]))

private theorem splitReindexEquiv_apply_1 {n nR nC nH : ℕ} {A : Fin n → Type*}
    [∀ i, Ring (A i)] [∀ i, Algebra ℝ (A i)] [∀ i, StarRing (A i)]
    {t : ∀ i, A i →ₗ[ℝ] ℝ} {d : Fin n → ℕ} (nf : ∀ i, FactorNormalForm (A i) (t i) (d i))
    (eR : {i // (nf i).tag = 0} ≃ Fin nR) (eC : {i // (nf i).tag = 1} ≃ Fin nC)
    (eH : {i // (nf i).tag = 2} ≃ Fin nH) (x : ∀ i, A i) (j : Fin nR) :
    (splitReindexEquiv nf eR eC eH x).1 j =
      ((nf (eR.symm j).val).realEquiv (eR.symm j).property).val (x (eR.symm j).val) := by
  simp [splitReindexEquiv, piSplitTagAlgEquiv_apply]

private theorem splitReindexEquiv_apply_2_1 {n nR nC nH : ℕ} {A : Fin n → Type*}
    [∀ i, Ring (A i)] [∀ i, Algebra ℝ (A i)] [∀ i, StarRing (A i)]
    {t : ∀ i, A i →ₗ[ℝ] ℝ} {d : Fin n → ℕ} (nf : ∀ i, FactorNormalForm (A i) (t i) (d i))
    (eR : {i // (nf i).tag = 0} ≃ Fin nR) (eC : {i // (nf i).tag = 1} ≃ Fin nC)
    (eH : {i // (nf i).tag = 2} ≃ Fin nH) (x : ∀ i, A i) (j : Fin nC) :
    (splitReindexEquiv nf eR eC eH x).2.1 j =
      ((nf (eC.symm j).val).complexEquiv (eC.symm j).property).val (x (eC.symm j).val) := by
  simp [splitReindexEquiv, piSplitTagAlgEquiv_apply]

private theorem splitReindexEquiv_apply_2_2 {n nR nC nH : ℕ} {A : Fin n → Type*}
    [∀ i, Ring (A i)] [∀ i, Algebra ℝ (A i)] [∀ i, StarRing (A i)]
    {t : ∀ i, A i →ₗ[ℝ] ℝ} {d : Fin n → ℕ} (nf : ∀ i, FactorNormalForm (A i) (t i) (d i))
    (eR : {i // (nf i).tag = 0} ≃ Fin nR) (eC : {i // (nf i).tag = 1} ≃ Fin nC)
    (eH : {i // (nf i).tag = 2} ≃ Fin nH) (x : ∀ i, A i) (j : Fin nH) :
    (splitReindexEquiv nf eR eC eH x).2.2 j =
      ((nf (eH.symm j).val).quatEquiv (eH.symm j).property).val (x (eH.symm j).val) := by
  simp [splitReindexEquiv, piSplitTagAlgEquiv_apply]

private theorem splitReindexEquiv_pos {n nR nC nH : ℕ} {A : Fin n → Type*}
    [∀ i, Ring (A i)] [∀ i, Algebra ℝ (A i)] [∀ i, StarRing (A i)]
    {t : ∀ i, A i →ₗ[ℝ] ℝ} {d : Fin n → ℕ} (nf : ∀ i, FactorNormalForm (A i) (t i) (d i))
    (eR : {i // (nf i).tag = 0} ≃ Fin nR) (eC : {i // (nf i).tag = 1} ≃ Fin nC)
    (eH : {i // (nf i).tag = 2} ≃ Fin nH) (x : ∀ i, A i) :
    (∀ i, IsRosatiPositive (t i) (x i)) ↔
      (∀ i, ((splitReindexEquiv nf eR eC eH x).1 i).PosDef) ∧
      (∀ i, ((splitReindexEquiv nf eR eC eH x).2.1 i).PosDef) ∧
      (∀ i, ((splitReindexEquiv nf eR eC eH x).2.2 i).QuatPosDef) := by
  refine ⟨fun hx ↦ ⟨
    fun j ↦ (splitReindexEquiv_apply_1 nf eR eC eH x j).symm ▸
      (((nf (eR.symm j).val).realEquiv (eR.symm j).property).property _).mp (hx _),
    fun j ↦ (splitReindexEquiv_apply_2_1 nf eR eC eH x j).symm ▸
      (((nf (eC.symm j).val).complexEquiv (eC.symm j).property).property _).mp (hx _),
    fun j ↦ (splitReindexEquiv_apply_2_2 nf eR eC eH x j).symm ▸
      (((nf (eH.symm j).val).quatEquiv (eH.symm j).property).property _).mp (hx _)⟩,
    fun ⟨hR, hC, hH⟩ i ↦ ?_⟩
  have hR' : ∀ k : {i // (nf i).tag = 0}, IsRosatiPositive (t k.val) (x k.val) :=
    eR.symm.surjective.forall.mpr fun j ↦
      (((nf (eR.symm j).val).realEquiv (eR.symm j).property).property _).mpr
        (splitReindexEquiv_apply_1 nf eR eC eH x j ▸ hR j)
  have hC' : ∀ k : {i // (nf i).tag = 1}, IsRosatiPositive (t k.val) (x k.val) :=
    eC.symm.surjective.forall.mpr fun j ↦
      (((nf (eC.symm j).val).complexEquiv (eC.symm j).property).property _).mpr
        (splitReindexEquiv_apply_2_1 nf eR eC eH x j ▸ hC j)
  have hH' : ∀ k : {i // (nf i).tag = 2}, IsRosatiPositive (t k.val) (x k.val) :=
    eH.symm.surjective.forall.mpr fun j ↦
      (((nf (eH.symm j).val).quatEquiv (eH.symm j).property).property _).mpr
        (splitReindexEquiv_apply_2_2 nf eR eC eH x j ▸ hH j)
  by_cases h0 : (nf i).tag = 0
  · exact hR' ⟨i, h0⟩
  · by_cases h1 : (nf i).tag = 1
    · exact hC' ⟨i, h1⟩
    · exact hH' ⟨i, FactorNormalForm.tag_eq_two_of_ne h0 h1⟩

private theorem realRosatiDecomposition_of_starPiEquiv {E : Type*} [Ring E] [Algebra ℝ E]
    [StarRing E] {n : ℕ} {D : Fin n → Type*} [∀ i, DivisionRing (D i)]
    [∀ i, Algebra ℝ (D i)] [∀ i, Module.Finite ℝ (D i)] {d : Fin n → ℕ} (hd : ∀ i, 0 < d i)
    {B : Fin n → Type*} [∀ i, Ring (B i)] [∀ i, Algebra ℝ (B i)] [∀ i, StarRing (B i)]
    (eWrap : E ≃⋆ₐ[ℝ] ∀ i, B i) (φ : ∀ i, B i ≃ₐ[ℝ] Matrix (Fin (d i)) (Fin (d i)) (D i))
    (t : E →ₗ[ℝ] ℝ) (hcyclic : ∀ x y : E, t (x * y) = t (y * x))
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) :
    ∃ (nR nC nH : ℕ) (dR : Fin nR → ℕ) (dC : Fin nC → ℕ) (dH : Fin nH → ℕ),
      (∀ i, 0 < dR i) ∧ (∀ i, 0 < dC i) ∧ (∀ i, 0 < dH i) ∧
      ∃ e : E ≃⋆ₐ[ℝ] ((∀ i : Fin nR, Mat (dR i) ℝ) ×
          (∀ i : Fin nC, Mat (dC i) ℂ) × (∀ i : Fin nH, Mat (dH i) ℍ[ℝ])),
        ∀ s : E, IsRosatiPositive t s ↔ (∀ i, ((e s).1 i).PosDef) ∧
          (∀ i, ((e s).2.1 i).PosDef) ∧ (∀ i, ((e s).2.2 i).QuatPosDef) := by
  let tPi : (∀ i : Fin n, B i) →ₗ[ℝ] ℝ := t.comp eWrap.symm.toAlgEquiv.toLinearMap
  obtain ⟨nf⟩ :
      Nonempty (∀ i, FactorNormalForm (B i) (tPi.comp (LinearMap.single ℝ B i)) (d i)) :=
    ⟨fun i ↦ Classical.choice (nonempty_factorNormalForm (φ i) (tPi.comp (LinearMap.single ℝ B i))
      (LinearMap.comp_single_cyclic tPi (fun x y ↦ by simp [tPi, hcyclic]) i)
      ((LinearMap.comp_single_mul_star_pos tPi fun x hx ↦ by
        simpa [tPi, map_star] using
          hpos (eWrap.symm x) fun h0 ↦ hx (by simpa using congrArg eWrap h0)) i))⟩
  let eR := Fintype.equivFin {i : Fin n // (nf i).tag = 0}
  let eC := Fintype.equivFin {i : Fin n // (nf i).tag = 1}
  let eH := Fintype.equivFin {i : Fin n // (nf i).tag = 2}
  refine ⟨_, _, _, fun i ↦ d (eR.symm i).val, fun i ↦ d (eC.symm i).val,
    fun i ↦ d (eH.symm i).val, fun i ↦ hd _, fun i ↦ hd _, fun i ↦ hd _,
    eWrap.trans (splitReindexEquiv nf eR eC eH), fun s ↦ ?_⟩
  rw [show t = tPi.comp eWrap.toAlgEquiv.toLinearMap by ext x; simp [tPi],
    eWrap.isRosatiPositive_comp_iff, isRosatiPositive_pi_iff]
  exact splitReindexEquiv_pos nf eR eC eH (eWrap s)

end SplitReindex

end FactorAssembly

section MainTheorem

/-- **Real Rosati decomposition and positivity comparison.** A finite-dimensional real star
algebra with a cyclic linear functional `t : E →ₗ[ℝ] ℝ` strictly positive on `x * star x` is
isomorphic as a real star algebra to a finite product of real, complex, and quaternionic matrix
algebras of positive sizes carrying their standard adjoints (transpose on `ℝ`, conjugate
transpose on `ℂ` and `ℍ[ℝ]`), in such a way that `IsRosatiPositive t` agrees with positive
definiteness (`Matrix.PosDef` and `Matrix.QuatPosDef`) in every factor. -/
theorem realRosatiDecomposition {E : Type*} [Ring E] [Algebra ℝ E] [StarRing E]
    [Module.Finite ℝ E] (t : E →ₗ[ℝ] ℝ)
    (hcyclic : ∀ x y : E, t (x * y) = t (y * x))
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) :
    ∃ (nR nC nH : ℕ) (dR : Fin nR → ℕ) (dC : Fin nC → ℕ) (dH : Fin nH → ℕ),
      (∀ i, 0 < dR i) ∧ (∀ i, 0 < dC i) ∧ (∀ i, 0 < dH i) ∧
      ∃ e : E ≃⋆ₐ[ℝ]
          ((∀ i : Fin nR, Matrix (Fin (dR i)) (Fin (dR i)) ℝ) ×
            (∀ i : Fin nC, Matrix (Fin (dC i)) (Fin (dC i)) ℂ) ×
            (∀ i : Fin nH, Matrix (Fin (dH i)) (Fin (dH i)) ℍ[ℝ])),
        ∀ s : E, IsRosatiPositive t s ↔
          (∀ i, ((e s).1 i).PosDef) ∧ (∀ i, ((e s).2.1 i).PosDef) ∧
          (∀ i, ((e s).2.2 i).QuatPosDef) := by
  have : IsProperStar E := isProperStar_of_forall_pos_mul_star t.toAddMonoidHom hpos
  have : IsSemisimpleRing E := isSemisimpleRing_of_trace_mul_star_pos t hpos
  obtain ⟨n, D, d, _, _, _, hd, ⟨eW⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite ℝ E
  have hδ := eW.toRingEquiv.star_symm_single_one
  let _ : ∀ i : Fin n, StarRing (ULift.{0} (Matrix (Fin (d i)) (Fin (d i)) (D i))) :=
    fun i ↦ eW.toRingEquiv.coordStarRing i (hδ i)
  exact realRosatiDecomposition_of_starPiEquiv (fun i ↦ Nat.pos_of_ne_zero (hd i).out)
    (eW.starPiULift hδ)
    (fun i ↦ ULift.algEquiv (R := ℝ) (A := Matrix (Fin (d i)) (Fin (d i)) (D i))) t hcyclic hpos

end MainTheorem

end TauCeti
