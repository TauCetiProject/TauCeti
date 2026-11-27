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

section InducedPi

variable {ι : Type*} [DecidableEq ι] {B : ι → Type*} [∀ i, Ring (B i)] [∀ i, Algebra ℝ (B i)]

private theorem factorTrace_cyclic (t : (∀ i, B i) →ₗ[ℝ] ℝ)
    (hcyc : ∀ x y, t (x * y) = t (y * x)) (i : ι) (x y : B i) :
    (t.comp (LinearMap.single ℝ B i)) (x * y) = (t.comp (LinearMap.single ℝ B i)) (y * x) := by
  simp only [LinearMap.comp_apply, LinearMap.single_apply]; rw [Pi.single_mul, Pi.single_mul, hcyc]

variable [∀ i, StarRing (B i)]

private theorem factorTrace_pos (t : (∀ i, B i) →ₗ[ℝ] ℝ)
    (hpos : ∀ x, x ≠ 0 → 0 < t (x * star x)) (i : ι) (x : B i) (hx : x ≠ 0) :
    0 < (t.comp (LinearMap.single ℝ B i)) (x * star x) := by
  have hst : star (Pi.single i x) = Pi.single i (star x) :=
    funext fun j ↦ by rcases eq_or_ne j i with rfl | h <;> [simp; simp [h]]
  simpa [LinearMap.single_apply, Pi.single_mul, hst] using
    hpos (Pi.single i x) fun h0 ↦ hx (by simpa using congrFun h0 i)

private theorem isRosatiPositive_pi_iff [Finite ι] (t : (∀ i, B i) →ₗ[ℝ] ℝ) (s : ∀ i, B i) :
    IsRosatiPositive t s ↔ ∀ i : ι, IsRosatiPositive (t.comp (LinearMap.single ℝ B i)) (s i) := by
  cases nonempty_fintype ι
  have hsum (y : ∀ i, B i) :
      t (s * y * star y) = ∑ i : ι, t (Pi.single i (s i * y i * star (y i))) := by
    rw [← map_sum, ← LinearMap.sum_single_apply B (s * y * star y)]; rfl
  have hsa : IsSelfAdjoint s ↔ ∀ i : ι, IsSelfAdjoint (s i) := ⟨fun h i ↦ congrFun h i, funext⟩
  rw [isRosatiPositive_iff]; simp only [isRosatiPositive_iff, forall_and, ← hsa]
  refine and_congr_right fun _ ↦ ⟨fun h i a ha ↦ ?_, fun h x hx ↦ ?_⟩
  · have h1 := h (Pi.single i a) fun h0 ↦ ha (by simpa using congrFun h0 i)
    rw [hsum, Finset.sum_eq_single i (fun j _ hji ↦ by simp [Pi.single_eq_of_ne hji])
      (fun hi ↦ absurd (Finset.mem_univ i) hi)] at h1; simpa [LinearMap.single_apply] using h1
  · rw [hsum]; obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
    refine Finset.sum_pos' (fun i _ ↦ ?_) ⟨i₀, Finset.mem_univ i₀, h i₀ (x i₀) hi₀⟩
    rcases eq_or_ne (x i) 0 with h0 | hne <;> [simp [h0]; exact (h i (x i) hne).le]

end InducedPi

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
  · exact ⟨.real _ ((φ.trans ψ.mapMatrix).exists_star_algEquiv_matrix_real t hcyc hpos).choose_spec⟩
  · exact ⟨.complex _
      ((φ.trans ψ.mapMatrix).exists_star_algEquiv_matrix_complex t hcyc hpos).choose_spec⟩
  · exact ⟨.quaternion _
      ((φ.trans ψ.mapMatrix).exists_star_algEquiv_matrix_quaternion t hcyc hpos).choose_spec⟩

section
variable {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A] {t : A →ₗ[ℝ] ℝ} {d : ℕ}
private def FactorNormalForm.tag : FactorNormalForm A t d → Fin 3
  | .real .. => 0 | .complex .. => 1 | .quaternion .. => 2
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

private theorem cast_sub_apply {n n' : ℕ} {P : Fin n → Prop} (F : Fin n → Type*)
    (e : Subtype P ≃ Fin n') (f : ∀ k : Fin n', F (e.symm k).val) (j : Fin n')
    (hT : F (e.symm (e ⟨(e.symm j).val, (e.symm j).property⟩)).val = F (e.symm j).val) :
    cast hT (f (e ⟨(e.symm j).val, (e.symm j).property⟩)) = f j := by
  have hk := e.apply_symm_apply j
  generalize e ⟨(e.symm j).val, (e.symm j).property⟩ = k at hk hT; subst hk; rfl

private theorem sub_cast_apply {n n' : ℕ} {P : Fin n → Prop} (F : Fin n → Type*)
    (e : Subtype P ≃ Fin n') (g : ∀ k : Subtype P, F k.val) (i : Fin n) (hi : P i)
    (hT : F (e.symm (e ⟨i, hi⟩)).val = F i) :
    cast hT (g (e.symm (e ⟨i, hi⟩))) = g ⟨i, hi⟩ := by
  have hp := e.symm_apply_apply ⟨i, hi⟩
  generalize e.symm (e ⟨i, hi⟩) = p at hp hT; subst hp; rfl

private noncomputable def splitReindexEquiv {n nR nC nH : ℕ} {A : Fin n → Type*}
    [∀ i, Ring (A i)] [∀ i, Algebra ℝ (A i)] [∀ i, StarRing (A i)]
    {t : ∀ i, A i →ₗ[ℝ] ℝ} {d : Fin n → ℕ} (nf : ∀ i, FactorNormalForm (A i) (t i) (d i))
    (eR : {i // (nf i).tag = 0} ≃ Fin nR) (eC : {i // (nf i).tag = 1} ≃ Fin nC)
    (eH : {i // (nf i).tag = 2} ≃ Fin nH) :
    (∀ i, A i) ≃⋆ₐ[ℝ]
      ((∀ i : Fin nR, Mat (d (eR.symm i).val) ℝ) ×
        (∀ i : Fin nC, Mat (d (eC.symm i).val) ℂ) ×
        (∀ i : Fin nH, Mat (d (eH.symm i).val) ℍ[ℝ])) where
  toFun x :=
    (fun j ↦ ((nf (eR.symm j).val).realEquiv (eR.symm j).property).val (x (eR.symm j).val),
     fun j ↦ ((nf (eC.symm j).val).complexEquiv (eC.symm j).property).val (x (eC.symm j).val),
     fun j ↦ ((nf (eH.symm j).val).quatEquiv (eH.symm j).property).val (x (eH.symm j).val))
  invFun y i :=
    if h0 : (nf i).tag = 0 then ((nf i).realEquiv h0).val.symm <|
      cast (congrArg (fun k ↦ Mat (d k) ℝ) (congrArg Subtype.val (eR.symm_apply_apply ⟨i, h0⟩)))
        (y.1 (eR ⟨i, h0⟩))
    else if h1 : (nf i).tag = 1 then ((nf i).complexEquiv h1).val.symm <|
      cast (congrArg (fun k ↦ Mat (d k) ℂ) (congrArg Subtype.val (eC.symm_apply_apply ⟨i, h1⟩)))
        (y.2.1 (eC ⟨i, h1⟩))
    else ((nf i).quatEquiv (by have := (nf i).tag.isLt; omega)).val.symm <|
      cast (congrArg (fun k ↦ Mat (d k) ℍ[ℝ]) (congrArg Subtype.val
        (eH.symm_apply_apply ⟨i, by have := (nf i).tag.isLt; omega⟩)))
        (y.2.2 (eH ⟨i, by have := (nf i).tag.isLt; omega⟩))
  left_inv x := funext fun i ↦ by
    dsimp only; by_cases h0 : (nf i).tag = 0
    · rw [dite_eq_left h0, sub_cast_apply (fun k ↦ Mat (d k) ℝ) eR
        (fun k ↦ ((nf k.val).realEquiv k.property).val (x k.val)) i h0]
      exact ((nf i).realEquiv h0).val.symm_apply_apply (x i)
    · by_cases h1 : (nf i).tag = 1
      · rw [dite_eq_right h0, dite_eq_left h1, sub_cast_apply (fun k ↦ Mat (d k) ℂ) eC
          (fun k ↦ ((nf k.val).complexEquiv k.property).val (x k.val)) i h1]
        exact ((nf i).complexEquiv h1).val.symm_apply_apply (x i)
      · have h2 : (nf i).tag = 2 := by have := (nf i).tag.isLt; omega
        rw [dite_eq_right h0, dite_eq_right h1, sub_cast_apply (fun k ↦ Mat (d k) ℍ[ℝ]) eH
          (fun k ↦ ((nf k.val).quatEquiv k.property).val (x k.val)) i h2]
        exact ((nf i).quatEquiv h2).val.symm_apply_apply (x i)
  right_inv y := Prod.ext
    (funext fun j ↦ by
      dsimp only; rw [dite_eq_left (eR.symm j).property, StarAlgEquiv.apply_symm_apply]
      exact cast_sub_apply (fun k ↦ Mat (d k) ℝ) eR y.1 j _)
    (Prod.ext
      (funext fun j ↦ by
        dsimp only; rw [dite_eq_right (show (nf (eC.symm j).val).tag ≠ 0 by
            have := (eC.symm j).property; omega),
          dite_eq_left (eC.symm j).property, StarAlgEquiv.apply_symm_apply]
        exact cast_sub_apply (fun k ↦ Mat (d k) ℂ) eC y.2.1 j _)
      (funext fun j ↦ by
        have hj := (eH.symm j).property; dsimp only
        rw [dite_eq_right (show (nf (eH.symm j).val).tag ≠ 0 by omega),
          dite_eq_right (show (nf (eH.symm j).val).tag ≠ 1 by omega),
          StarAlgEquiv.apply_symm_apply]
        exact cast_sub_apply (fun k ↦ Mat (d k) ℍ[ℝ]) eH y.2.2 j _))
  map_mul' _ _ := Prod.ext (funext fun _ ↦ map_mul ..)
    (Prod.ext (funext fun _ ↦ map_mul ..) (funext fun _ ↦ map_mul ..))
  map_add' _ _ := Prod.ext (funext fun _ ↦ map_add ..)
    (Prod.ext (funext fun _ ↦ map_add ..) (funext fun _ ↦ map_add ..))
  map_smul' _ _ := Prod.ext (funext fun _ ↦ map_smul ..)
    (Prod.ext (funext fun _ ↦ map_smul ..) (funext fun _ ↦ map_smul ..))
  map_star' _ := Prod.ext (funext fun _ ↦ map_star ..)
    (Prod.ext (funext fun _ ↦ map_star ..) (funext fun _ ↦ map_star ..))

private theorem prop_of_sub_eq {n n' : ℕ} {P : Fin n → Prop} (e : Subtype P ≃ Fin n')
    (Q : ∀ i, P i → Prop) (hQ : ∀ j, Q (e.symm j).val (e.symm j).property)
    (i : Fin n) (hi : P i) : Q i hi := by
  have hp := e.symm_apply_apply ⟨i, hi⟩; have h := hQ (e ⟨i, hi⟩)
  generalize e.symm (e ⟨i, hi⟩) = p at hp h; subst hp; exact h

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
    fun j ↦ (((nf (eR.symm j).val).realEquiv (eR.symm j).property).property _).mp (hx _),
    fun j ↦ (((nf (eC.symm j).val).complexEquiv (eC.symm j).property).property _).mp (hx _),
    fun j ↦ (((nf (eH.symm j).val).quatEquiv (eH.symm j).property).property _).mp (hx _)⟩,
    fun ⟨hR, hC, hH⟩ i ↦ ?_⟩
  by_cases h0 : (nf i).tag = 0
  · exact (((nf i).realEquiv h0).property _).mpr
      (prop_of_sub_eq eR (fun k hk ↦ (((nf k).realEquiv hk).val (x k)).PosDef) hR i h0)
  · by_cases h1 : (nf i).tag = 1
    · exact (((nf i).complexEquiv h1).property _).mpr
        (prop_of_sub_eq eC (fun k hk ↦ (((nf k).complexEquiv hk).val (x k)).PosDef) hC i h1)
    · have h2 : (nf i).tag = 2 := by have := (nf i).tag.isLt; omega
      exact (((nf i).quatEquiv h2).property _).mpr
        (prop_of_sub_eq eH (fun k hk ↦ (((nf k).quatEquiv hk).val (x k)).QuatPosDef) hH i h2)

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
      (factorTrace_cyclic tPi (fun x y ↦ by simp [tPi, hcyclic]) i)
      ((factorTrace_pos tPi fun x hx ↦ by
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
