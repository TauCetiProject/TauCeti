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

private def piSplitTagStarAlgEquiv {n : ℕ} {A : Fin n → Type*} [∀ i, Ring (A i)]
    [∀ i, Algebra ℝ (A i)] [∀ i, StarRing (A i)] {t : ∀ i, A i →ₗ[ℝ] ℝ} {d : Fin n → ℕ}
    (nf : ∀ i, FactorNormalForm (A i) (t i) (d i)) :
    (∀ i, A i) ≃⋆ₐ[ℝ]
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
  map_smul' _ _ := rfl
  map_star' _ := rfl

private def starAlgEquivProdCongr {R A₁ B₁ A₂ B₂ : Type*} [CommSemiring R]
    [Semiring A₁] [Algebra R A₁] [StarRing A₁] [Semiring B₁] [Algebra R B₁] [StarRing B₁]
    [Semiring A₂] [Algebra R A₂] [StarRing A₂] [Semiring B₂] [Algebra R B₂] [StarRing B₂]
    (e₁ : A₁ ≃⋆ₐ[R] B₁) (e₂ : A₂ ≃⋆ₐ[R] B₂) : (A₁ × A₂) ≃⋆ₐ[R] (B₁ × B₂) :=
  StarAlgEquiv.ofAlgEquiv (e₁.toAlgEquiv.prodCongr e₂.toAlgEquiv) fun x ↦
    Prod.ext (map_star e₁ x.1) (map_star e₂ x.2)

private noncomputable def reindexBlockEquiv {ι : Type*} {nK : ℕ} {A' B : ι → Type*}
    [∀ i, Ring (A' i)] [∀ i, Algebra ℝ (A' i)] [∀ i, StarRing (A' i)]
    [∀ i, Ring (B i)] [∀ i, Algebra ℝ (B i)] [∀ i, StarRing (B i)]
    (φ : ∀ i, A' i ≃⋆ₐ[ℝ] B i) (eK : ι ≃ Fin nK) :
    (∀ i, A' i) ≃⋆ₐ[ℝ] (∀ j : Fin nK, B (eK.symm j)) :=
  StarAlgEquiv.ofAlgEquiv
    ((AlgEquiv.piCongrRight fun i ↦ (φ i).toAlgEquiv).trans (AlgEquiv.piCongrLeft' ℝ B eK))
    fun x ↦ funext fun j ↦ by simp [map_star]

private theorem reindexBlockEquiv_apply {ι : Type*} {nK : ℕ} {A' B : ι → Type*}
    [∀ i, Ring (A' i)] [∀ i, Algebra ℝ (A' i)] [∀ i, StarRing (A' i)]
    [∀ i, Ring (B i)] [∀ i, Algebra ℝ (B i)] [∀ i, StarRing (B i)]
    (φ : ∀ i, A' i ≃⋆ₐ[ℝ] B i) (eK : ι ≃ Fin nK) (y : ∀ i, A' i) (j : Fin nK) :
    reindexBlockEquiv φ eK y j = φ (eK.symm j) (y (eK.symm j)) := by
  simp [reindexBlockEquiv]

private theorem reindexBlockEquiv_pos_iff {ι : Type*} {nK : ℕ} {A' B : ι → Type*}
    [∀ i, Ring (A' i)] [∀ i, Algebra ℝ (A' i)] [∀ i, StarRing (A' i)]
    [∀ i, Ring (B i)] [∀ i, Algebra ℝ (B i)] [∀ i, StarRing (B i)]
    {t : ∀ i, A' i →ₗ[ℝ] ℝ} (φ : ∀ i, A' i ≃⋆ₐ[ℝ] B i) (eK : ι ≃ Fin nK)
    (P : ∀ i, B i → Prop) (hp : ∀ i s, IsRosatiPositive (t i) s ↔ P i (φ i s))
    (y : ∀ i, A' i) :
    (∀ i, IsRosatiPositive (t i) (y i)) ↔
      ∀ j : Fin nK, P (eK.symm j) (reindexBlockEquiv φ eK y j) := by
  simp only [reindexBlockEquiv_apply]
  exact ⟨fun hy j ↦ (hp _ _).mp (hy _),
    fun hj ↦ eK.symm.surjective.forall.mpr fun j ↦ (hp _ _).mpr (hj j)⟩

private noncomputable def splitReindexEquiv {n nR nC nH : ℕ} {A : Fin n → Type*}
    [∀ i, Ring (A i)] [∀ i, Algebra ℝ (A i)] [∀ i, StarRing (A i)]
    {t : ∀ i, A i →ₗ[ℝ] ℝ} {d : Fin n → ℕ} (nf : ∀ i, FactorNormalForm (A i) (t i) (d i))
    (eR : {i // (nf i).tag = 0} ≃ Fin nR) (eC : {i // (nf i).tag = 1} ≃ Fin nC)
    (eH : {i // (nf i).tag = 2} ≃ Fin nH) :
    (∀ i, A i) ≃⋆ₐ[ℝ]
      ((∀ i : Fin nR, Mat (d (eR.symm i).val) ℝ) ×
        (∀ i : Fin nC, Mat (d (eC.symm i).val) ℂ) ×
        (∀ i : Fin nH, Mat (d (eH.symm i).val) ℍ[ℝ])) :=
  (piSplitTagStarAlgEquiv nf).trans
    (starAlgEquivProdCongr (reindexBlockEquiv (fun i ↦ ((nf i.val).realEquiv i.property).val) eR)
      (starAlgEquivProdCongr
        (reindexBlockEquiv (fun i ↦ ((nf i.val).complexEquiv i.property).val) eC)
        (reindexBlockEquiv (fun i ↦ ((nf i.val).quatEquiv i.property).val) eH)))

private theorem splitReindexEquiv_pos {n nR nC nH : ℕ} {A : Fin n → Type*}
    [∀ i, Ring (A i)] [∀ i, Algebra ℝ (A i)] [∀ i, StarRing (A i)]
    {t : ∀ i, A i →ₗ[ℝ] ℝ} {d : Fin n → ℕ} (nf : ∀ i, FactorNormalForm (A i) (t i) (d i))
    (eR : {i // (nf i).tag = 0} ≃ Fin nR) (eC : {i // (nf i).tag = 1} ≃ Fin nC)
    (eH : {i // (nf i).tag = 2} ≃ Fin nH) (x : ∀ i, A i) :
    (∀ i, IsRosatiPositive (t i) (x i)) ↔
      (∀ i, ((splitReindexEquiv nf eR eC eH x).1 i).PosDef) ∧
      (∀ i, ((splitReindexEquiv nf eR eC eH x).2.1 i).PosDef) ∧
      (∀ i, ((splitReindexEquiv nf eR eC eH x).2.2 i).QuatPosDef) := by
  have hsplit : (∀ i, IsRosatiPositive (t i) (x i)) ↔
      (∀ i : {i // (nf i).tag = 0}, IsRosatiPositive (t i.val) (x i.val)) ∧
      (∀ i : {i // (nf i).tag = 1}, IsRosatiPositive (t i.val) (x i.val)) ∧
      (∀ i : {i // (nf i).tag = 2}, IsRosatiPositive (t i.val) (x i.val)) :=
    ⟨fun hx ↦ ⟨fun i ↦ hx i.val, fun i ↦ hx i.val, fun i ↦ hx i.val⟩,
     fun ⟨h0, h1, h2⟩ i ↦ by
       by_cases hi0 : (nf i).tag = 0
       · exact h0 ⟨i, hi0⟩
       · by_cases hi1 : (nf i).tag = 1
         · exact h1 ⟨i, hi1⟩
         · exact h2 ⟨i, FactorNormalForm.tag_eq_two_of_ne hi0 hi1⟩⟩
  rw [hsplit]
  exact and_congr
    (reindexBlockEquiv_pos_iff (fun i ↦ ((nf i.val).realEquiv i.property).val) eR
      (fun _ M ↦ M.PosDef) (fun i ↦ ((nf i.val).realEquiv i.property).property) _)
    (and_congr
      (reindexBlockEquiv_pos_iff (fun i ↦ ((nf i.val).complexEquiv i.property).val) eC
        (fun _ M ↦ M.PosDef) (fun i ↦ ((nf i.val).complexEquiv i.property).property) _)
      (reindexBlockEquiv_pos_iff (fun i ↦ ((nf i.val).quatEquiv i.property).val) eH
        (fun _ M ↦ M.QuatPosDef) (fun i ↦ ((nf i.val).quatEquiv i.property).property) _))

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
