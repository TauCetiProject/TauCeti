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
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Matrix
import TauCeti.Algebra.CentralSimple.Real
import TauCeti.Algebra.Star.Pi
import TauCeti.Algebra.Star.Rosati.MatrixFactor
import TauCeti.RingTheory.CentralIdempotent
import TauCeti.RingTheory.Semisimple.Star

/-!
# Real Rosati decomposition and positivity comparison

A finite-dimensional real star algebra `E` equipped with a cyclic linear functional
`t : E →ₗ[ℝ] ℝ` satisfying `t (x * star x) > 0` for all `x ≠ 0` is semisimple and decomposes
into a finite product of real, complex, and quaternionic matrix algebras carrying their standard
adjoints, via a star-algebra isomorphism matching `TauCeti.IsRosatiPositive t` with
`Matrix.PosDef` and `Matrix.QuatPosDef` in every factor.

## Main results

* `TauCeti.realRosatiDecomposition`: the real Rosati normal form (`E ≃⋆ₐ[ℝ] ...`) and factorwise
  positivity comparison.

## Implementation notes

Combines `TauCeti.isSemisimpleRing_of_trace_mul_star_pos` and Wedderburn–Artin to split `E`, fixes
coordinate idempotents via `TauCeti.star_coord_idempotent_eq_self`, restricts `star` via
`RingEquiv.apply_star_eq_coord`/`apply_star_single`, and standardizes factors with
`TauCeti.nonempty_algEquiv_real_or_complex_or_quaternion` and
`TauCeti.exists_star_algEquiv_matrix_*`.

## References

* J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer (2021), §8.4.
* M. Lipnowski and J. Tsimerman, *How large is A_g(F_q)?*, arXiv:1511.02212v1, §4.3.2 and
  Proposition 4.10.
-/

public section

open scoped Matrix ComplexOrder _root_.Quaternion

namespace TauCeti

section FactorAssembly

private def FactorCopy (A : Type*) := A
private def FactorCopy.mk {A : Type*} (x : A) : FactorCopy A := x
private def FactorCopy.val {A : Type*} (x : FactorCopy A) : A := x
@[simp] private theorem FactorCopy.val_mk {A : Type*} (x : A) : (FactorCopy.mk x).val = x := rfl
@[ext] private theorem FactorCopy.ext {A : Type*} {x y : FactorCopy A}
    (h : x.val = y.val) : x = y := h

private instance {A : Type*} [Ring A] : Ring (FactorCopy A) := inferInstanceAs (Ring A)
private instance {A : Type*} [Ring A] [Algebra ℝ A] : Algebra ℝ (FactorCopy A) :=
  inferInstanceAs (Algebra ℝ A)
@[simp] private theorem FactorCopy.val_zero {A : Type*} [Ring A] : (0 : FactorCopy A).val = 0 := rfl
@[simp] private theorem FactorCopy.val_mul {A : Type*} [Ring A] (x y : FactorCopy A) :
    (x * y).val = x.val * y.val := rfl

private def factorCopyEquiv (A : Type*) [Ring A] [Algebra ℝ A] : FactorCopy A ≃ₐ[ℝ] A :=
  AlgEquiv.refl
@[simp] private theorem factorCopyEquiv_symm_val {A : Type*} [Ring A] [Algebra ℝ A] (x : A) :
    ((factorCopyEquiv A).symm x).val = x := rfl

section InducedPi

variable {E : Type*} [Ring E] [Algebra ℝ E] {ι : Type*} [DecidableEq ι] {A : ι → Type*}
  [∀ i, Ring (A i)] [∀ i, Algebra ℝ (A i)]

/-- Induced `StarRing` structure on `FactorCopy (A i)`. The axioms unfold `FactorCopy.mk`/`val`
and the ring operations inside the constructor to reduce to identities on `e.toRingEquiv`. -/
private abbrev inducedFactorStarRing [StarRing E] (e : E ≃ₐ[ℝ] ∀ i, A i)
    (hδ : ∀ i : ι, star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1))
    (i : ι) : StarRing (FactorCopy (A i)) where
  star x := FactorCopy.mk (e (star (e.symm (Pi.single i x.val))) i)
  star_involutive x := FactorCopy.ext <| by
    have hsingle := e.toRingEquiv.apply_star_single hδ i x.val
    simp only [AlgEquiv.coe_toRingEquiv, AlgEquiv.toRingEquiv_symm] at hsingle
    change e (star (e.symm (Pi.single i (e (star (e.symm (Pi.single i x.val))) i)))) i = x.val
    rw [← hsingle, AlgEquiv.symm_apply_apply, star_star, AlgEquiv.apply_symm_apply,
      Pi.single_eq_same]
  star_mul x y := FactorCopy.ext <| by
    have hmul := e.toRingEquiv.symm_single_mul i x.val y.val
    simp only [AlgEquiv.coe_toRingEquiv, AlgEquiv.toRingEquiv_symm] at hmul
    change e (star (e.symm (Pi.single i (x.val * y.val)))) i =
      e (star (e.symm (Pi.single i y.val))) i * e (star (e.symm (Pi.single i x.val))) i
    rw [hmul, star_mul, map_mul, Pi.mul_apply]
  star_add x y := FactorCopy.ext <| by
    change e (star (e.symm (Pi.single i (x.val + y.val)))) i =
      e (star (e.symm (Pi.single i x.val))) i + e (star (e.symm (Pi.single i y.val))) i
    rw [Pi.single_add, map_add, star_add, map_add, Pi.add_apply]

/-- Evaluation of `star` on `FactorCopy (A i)` by definitional unfolding of the instance. -/
@[simp] private theorem inducedFactorStarRing_star_val [StarRing E] (e : E ≃ₐ[ℝ] ∀ i, A i)
    (hδ : ∀ i : ι, star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1))
    (i : ι) (x : FactorCopy (A i)) :
    letI := inducedFactorStarRing e hδ i
    (star x).val = e (star (e.symm (Pi.single i x.val))) i := rfl

/-- Restriction of a linear functional `t : E →ₗ[ℝ] ℝ` to `FactorCopy (A i)`. -/
private def factorTrace (e : E ≃ₐ[ℝ] ∀ i, A i) (t : E →ₗ[ℝ] ℝ) (i : ι) :
    FactorCopy (A i) →ₗ[ℝ] ℝ :=
  (t.comp e.symm.toLinearMap).comp
    ((LinearMap.single ℝ A i).comp (factorCopyEquiv (A i)).toLinearMap)

@[simp] private theorem factorTrace_apply (e : E ≃ₐ[ℝ] ∀ i, A i) (t : E →ₗ[ℝ] ℝ) (i : ι)
    (x : FactorCopy (A i)) : factorTrace e t i x = t (e.symm (Pi.single i x.val)) := rfl

private theorem factorTrace_cyclic (e : E ≃ₐ[ℝ] ∀ i, A i) (t : E →ₗ[ℝ] ℝ)
    (hcyclic : ∀ x y : E, t (x * y) = t (y * x)) (i : ι) (x y : FactorCopy (A i)) :
    factorTrace e t i (x * y) = factorTrace e t i (y * x) := by
  have h1 := e.toRingEquiv.symm_single_mul i x.val y.val
  have h2 := e.toRingEquiv.symm_single_mul i y.val x.val
  simp only [AlgEquiv.coe_toRingEquiv, AlgEquiv.toRingEquiv_symm] at h1 h2
  simp only [factorTrace_apply, FactorCopy.val_mul]; rw [h1, h2, hcyclic]

private theorem factorTrace_pos [StarRing E] (e : E ≃ₐ[ℝ] ∀ i, A i)
    (hδ : ∀ i : ι, star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1))
    (t : E →ₗ[ℝ] ℝ) (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) (i : ι) :
    letI := inducedFactorStarRing e hδ i
    ∀ x : FactorCopy (A i), x ≠ 0 → 0 < factorTrace e t i (x * star x) := by
  let _ := inducedFactorStarRing e hδ i; intro x hx
  have hne : e.symm (Pi.single i x.val) ≠ 0 :=
    fun h0 ↦ hx (FactorCopy.ext (by simpa using congrFun (congrArg e h0) i))
  have hsingle := e.toRingEquiv.apply_star_single hδ i x.val
  simp only [AlgEquiv.coe_toRingEquiv, AlgEquiv.toRingEquiv_symm] at hsingle
  have hmul : e.symm (Pi.single i (x * star x).val) =
      e.symm (Pi.single i x.val) * star (e.symm (Pi.single i x.val)) := by
    apply e.injective; funext j
    rw [FactorCopy.val_mul, inducedFactorStarRing_star_val, map_mul, AlgEquiv.apply_symm_apply,
      AlgEquiv.apply_symm_apply, hsingle, Pi.mul_apply]
    by_cases hji : j = i
    · subst hji; simp
    · simp [Pi.single_eq_of_ne hji]
  rw [factorTrace_apply, hmul]; exact hpos _ hne

private theorem trace_mul_mul_star_eq_sum_factorTrace [StarRing E] [Fintype ι]
    (e : E ≃ₐ[ℝ] ∀ i, A i)
    (hδ : ∀ i : ι, star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1))
    (t : E →ₗ[ℝ] ℝ) (s x : E) :
    letI := inducedFactorStarRing e hδ
    t (s * x * star x) = ∑ i : ι, factorTrace e t i
        (FactorCopy.mk (e s i) * FactorCopy.mk (e x i) * star (FactorCopy.mk (e x i))) := by
  let _ := inducedFactorStarRing e hδ
  have hcoord (i : ι) : e (star x) i = e (star (e.symm (Pi.single i (e x i)))) i := by
    simpa [AlgEquiv.coe_toRingEquiv, AlgEquiv.toRingEquiv_symm] using
      e.toRingEquiv.apply_star_eq_coord hδ x i
  have heq : s * x * star x = ∑ i : ι,
      e.symm (Pi.single i (e s i * e x i * e (star (e.symm (Pi.single i (e x i)))) i)) := by
    apply e.injective; rw [map_sum]
    simp_rw [AlgEquiv.apply_symm_apply, ← hcoord, ← Pi.mul_apply, ← map_mul]
    exact (LinearMap.sum_single_apply A (e (s * x * star x))).symm
  conv_lhs => rw [heq, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by
    simp only [factorTrace_apply, FactorCopy.val_mul, inducedFactorStarRing_star_val,
      FactorCopy.val_mk]

private theorem isRosatiPositive_pi_iff [StarRing E] (e : E ≃ₐ[ℝ] ∀ i, A i)
    (hδ : ∀ i : ι, star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1))
    [Finite ι] (t : E →ₗ[ℝ] ℝ) (s : E) :
    letI := inducedFactorStarRing e hδ
    IsRosatiPositive t s ↔
      ∀ i : ι, IsRosatiPositive (factorTrace e t i) (FactorCopy.mk (e s i)) := by
  let _ := Fintype.ofFinite ι; let _ := inducedFactorStarRing e hδ
  have hcoord (i : ι) : e (star s) i = e (star (e.symm (Pi.single i (e s i)))) i := by
    simpa [AlgEquiv.coe_toRingEquiv, AlgEquiv.toRingEquiv_symm] using
      e.toRingEquiv.apply_star_eq_coord hδ s i
  have hsa : IsSelfAdjoint s ↔ ∀ i : ι, IsSelfAdjoint (FactorCopy.mk (e s i)) :=
    ⟨fun hs i ↦ FactorCopy.ext (by
        rw [inducedFactorStarRing_star_val, FactorCopy.val_mk, ← hcoord i, hs.star_eq]),
      fun hs ↦ e.injective (funext fun i ↦ by
        rw [hcoord i]; simpa [inducedFactorStarRing_star_val] using congrArg FactorCopy.val (hs i))⟩
  rw [isRosatiPositive_iff]; simp only [isRosatiPositive_iff, forall_and, ← hsa]
  refine and_congr_right fun _ ↦ ⟨fun h i a ha ↦ ?_, fun h x hx ↦ ?_⟩
  · have h1 := h (e.symm (Pi.single i a.val))
      (fun h0 ↦ ha (FactorCopy.ext (by simpa using congrFun (congrArg e h0) i)))
    rw [trace_mul_mul_star_eq_sum_factorTrace e hδ, Finset.sum_eq_single i] at h1
    · rw [AlgEquiv.apply_symm_apply, Pi.single_eq_same] at h1; exact h1
    · intro j _ hji
      rw [show FactorCopy.mk (e (e.symm (Pi.single i a.val)) j) = 0 from
        FactorCopy.ext (by simp [Pi.single_eq_of_ne hji]), mul_zero, zero_mul, map_zero]
    · exact fun hi ↦ absurd (Finset.mem_univ i) hi
  · rw [trace_mul_mul_star_eq_sum_factorTrace e hδ]
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ : ι, FactorCopy.mk (e x i₀) ≠ 0 := by
      by_contra hall; push Not at hall
      exact hx (e.injective (by
        rw [map_zero]; exact funext fun i ↦ congrArg FactorCopy.val (hall i)))
    refine Finset.sum_pos' (fun i _ ↦ ?_)
      ⟨i₀, Finset.mem_univ i₀, h i₀ (FactorCopy.mk (e x i₀)) hi₀⟩
    rcases eq_or_ne (FactorCopy.mk (e x i)) 0 with h0 | hne
    · rw [h0, mul_zero, zero_mul, map_zero]
    · exact (h i (FactorCopy.mk (e x i)) hne).le

end InducedPi

private inductive FactorNormalForm (A : Type*) [Ring A] [Algebra ℝ A] [StarRing A]
    (t : A →ₗ[ℝ] ℝ) (d : ℕ) where
  | real (e : A ≃⋆ₐ[ℝ] Matrix (Fin d) (Fin d) ℝ)
      (hpos : ∀ s : A, IsRosatiPositive t s ↔ (e s).PosDef)
  | complex (e : A ≃⋆ₐ[ℝ] Matrix (Fin d) (Fin d) ℂ)
      (hpos : ∀ s : A, IsRosatiPositive t s ↔ (e s).PosDef)
  | quaternion (e : A ≃⋆ₐ[ℝ] Matrix (Fin d) (Fin d) ℍ[ℝ])
      (hpos : ∀ s : A, IsRosatiPositive t s ↔ (e s).QuatPosDef)

private theorem nonempty_factorNormalForm {A D : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    [DivisionRing D] [Algebra ℝ D] [Module.Finite ℝ D] {d : ℕ}
    (φ : A ≃ₐ[ℝ] Matrix (Fin d) (Fin d) D) (t : A →ₗ[ℝ] ℝ)
    (hcyclic : ∀ x y : A, t (x * y) = t (y * x))
    (hpos : ∀ x : A, x ≠ 0 → 0 < t (x * star x)) : Nonempty (FactorNormalForm A t d) := by
  rcases nonempty_algEquiv_real_or_complex_or_quaternion D with ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩
  · exact ⟨.real (exists_star_algEquiv_matrix_real (φ.trans ψ.mapMatrix) t hcyclic hpos).choose
      (exists_star_algEquiv_matrix_real (φ.trans ψ.mapMatrix) t hcyclic hpos).choose_spec⟩
  · exact ⟨.complex
      (exists_star_algEquiv_matrix_complex (φ.trans ψ.mapMatrix) t hcyclic hpos).choose
      (exists_star_algEquiv_matrix_complex (φ.trans ψ.mapMatrix) t hcyclic hpos).choose_spec⟩
  · exact ⟨.quaternion
      (exists_star_algEquiv_matrix_quaternion (φ.trans ψ.mapMatrix) t hcyclic hpos).choose
      (exists_star_algEquiv_matrix_quaternion (φ.trans ψ.mapMatrix) t hcyclic hpos).choose_spec⟩

section

variable {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A] {t : A →ₗ[ℝ] ℝ} {d : ℕ}

private def FactorNormalForm.tag : FactorNormalForm A t d → Fin 3
  | .real .. => 0 | .complex .. => 1 | .quaternion .. => 2

private def FactorNormalForm.realEquiv :
    (nf : FactorNormalForm A t d) → nf.tag = 0 → A ≃⋆ₐ[ℝ] Matrix (Fin d) (Fin d) ℝ
  | .real e _, _ => e | .complex .., h | .quaternion .., h => nomatch h

private def FactorNormalForm.complexEquiv :
    (nf : FactorNormalForm A t d) → nf.tag = 1 → A ≃⋆ₐ[ℝ] Matrix (Fin d) (Fin d) ℂ
  | .complex e _, _ => e | .real .., h | .quaternion .., h => nomatch h

private def FactorNormalForm.quatEquiv :
    (nf : FactorNormalForm A t d) → nf.tag = 2 → A ≃⋆ₐ[ℝ] Matrix (Fin d) (Fin d) ℍ[ℝ]
  | .quaternion e _, _ => e | .real .., h | .complex .., h => nomatch h

private theorem FactorNormalForm.realEquiv_eq {nf : FactorNormalForm A t d}
    {e : A ≃⋆ₐ[ℝ] Matrix (Fin d) (Fin d) ℝ} {hp} (h : nf = .real e hp) (h0 : nf.tag = 0) :
    nf.realEquiv h0 = e := by subst h; rfl

private theorem FactorNormalForm.complexEquiv_eq {nf : FactorNormalForm A t d}
    {e : A ≃⋆ₐ[ℝ] Matrix (Fin d) (Fin d) ℂ} {hp} (h : nf = .complex e hp) (h1 : nf.tag = 1) :
    nf.complexEquiv h1 = e := by subst h; rfl

private theorem FactorNormalForm.quatEquiv_eq {nf : FactorNormalForm A t d}
    {e : A ≃⋆ₐ[ℝ] Matrix (Fin d) (Fin d) ℍ[ℝ]} {hp} (h : nf = .quaternion e hp)
    (h2 : nf.tag = 2) : nf.quatEquiv h2 = e := by subst h; rfl

end

section SplitProduct

variable {n : ℕ} {A : Fin n → Type*} [∀ i, Ring (A i)] [∀ i, Algebra ℝ (A i)]
  [∀ i, StarRing (A i)] {t : ∀ i, A i →ₗ[ℝ] ℝ} {d : Fin n → ℕ}

/-- Splitting a product of standardized factors `(∀ i, A i)` into real, complex, and quaternionic
matrix blocks. `map_star` unfolds `AlgEquiv.trans`, `RingEquiv.piEquivPiSubtypeProd`,
`AlgEquiv.piCongrLeft`, and `AlgEquiv.piCongrRight` on each block component. -/
private noncomputable def splitProductEquiv (nf : ∀ i, FactorNormalForm (A i) (t i) (d i)) :
    (∀ i, A i) ≃⋆ₐ[ℝ]
      ((∀ i : {i // (nf i).tag = 0}, Matrix (Fin (d i.1)) (Fin (d i.1)) ℝ) ×
        (∀ i : {i // (nf i).tag = 1}, Matrix (Fin (d i.1)) (Fin (d i.1)) ℂ) ×
        (∀ i : {i // (nf i).tag = 2}, Matrix (Fin (d i.1)) (Fin (d i.1)) ℍ[ℝ])) :=
  let s1 := AlgEquiv.ofRingEquiv
    (f := RingEquiv.piEquivPiSubtypeProd (fun i ↦ (nf i).tag = 0) A) fun _ ↦ rfl
  let s2 := AlgEquiv.ofRingEquiv
    (f := RingEquiv.piEquivPiSubtypeProd (fun i : {i // (nf i).tag ≠ 0} ↦ (nf i.1).tag = 1)
      (fun i ↦ A i.1)) fun _ ↦ rfl
  let e1 : {i : {i // (nf i).tag ≠ 0} // (nf i.1).tag = 1} ≃ {i // (nf i).tag = 1} :=
    ⟨fun x ↦ ⟨x.1.1, x.2⟩, fun x ↦ ⟨⟨x.1, by simp [x.2]⟩, x.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  let e2 : {i : {i // (nf i).tag ≠ 0} // (nf i.1).tag ≠ 1} ≃ {i // (nf i).tag = 2} :=
    ⟨fun x ↦ ⟨x.1.1, by have := x.1.2; have := x.2; omega⟩,
      fun x ↦ ⟨⟨x.1, by simp [x.2]⟩, by simp [x.2]⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  let blocks := AlgEquiv.prodCongr
    (AlgEquiv.piCongrRight fun i ↦ ((nf i.1).realEquiv i.2).toAlgEquiv)
    (AlgEquiv.prodCongr
      (AlgEquiv.piCongrRight fun i ↦ ((nf i.1).complexEquiv i.2).toAlgEquiv)
      (AlgEquiv.piCongrRight fun i ↦ ((nf i.1).quatEquiv i.2).toAlgEquiv))
  let alg := (s1.trans (AlgEquiv.prodCongr AlgEquiv.refl (s2.trans (AlgEquiv.prodCongr
    (AlgEquiv.piCongrLeft ℝ (fun i : {i // (nf i).tag = 1} ↦ A i.1) e1)
    (AlgEquiv.piCongrLeft ℝ (fun i : {i // (nf i).tag = 2} ↦ A i.1) e2))))).trans blocks
  StarAlgEquiv.ofAlgEquiv alg fun x ↦ Prod.ext
    (funext fun i ↦ by dsimp [alg, blocks, s1]; exact map_star ((nf i.1).realEquiv i.2) (x i.1))
    (Prod.ext
      (funext fun i ↦ by
        dsimp [alg, blocks, s1, s2, e1]; exact map_star ((nf i.1).complexEquiv i.2) (x i.1))
      (funext fun i ↦ by
        dsimp [alg, blocks, s1, s2, e2]; exact map_star ((nf i.1).quatEquiv i.2) (x i.1)))

/-- Real-block projection of `splitProductEquiv` (by definitional unfolding of the split). -/
private theorem splitProductEquiv_fst (nf : ∀ i, FactorNormalForm (A i) (t i) (d i)) (x : ∀ i, A i)
    (i : {i // (nf i).tag = 0}) : (splitProductEquiv nf x).1 i = (nf i.1).realEquiv i.2 (x i.1) :=
  rfl

/-- Complex-block projection of `splitProductEquiv` (by definitional unfolding of the split). -/
private theorem splitProductEquiv_snd_fst (nf : ∀ i, FactorNormalForm (A i) (t i) (d i))
    (x : ∀ i, A i) (i : {i // (nf i).tag = 1}) :
    (splitProductEquiv nf x).2.1 i = (nf i.1).complexEquiv i.2 (x i.1) := rfl

/-- Quaternionic-block projection of `splitProductEquiv` (by definitional unfolding). -/
private theorem splitProductEquiv_snd_snd (nf : ∀ i, FactorNormalForm (A i) (t i) (d i))
    (x : ∀ i, A i) (i : {i // (nf i).tag = 2}) :
    (splitProductEquiv nf x).2.2 i = (nf i.1).quatEquiv i.2 (x i.1) := rfl

private theorem splitProductEquiv_pos (nf : ∀ i, FactorNormalForm (A i) (t i) (d i))
    (x : ∀ i, A i) :
    (∀ i, IsRosatiPositive (t i) (x i)) ↔
      (∀ i, ((splitProductEquiv nf x).1 i).PosDef) ∧
      (∀ i, ((splitProductEquiv nf x).2.1 i).PosDef) ∧
      (∀ i, ((splitProductEquiv nf x).2.2 i).QuatPosDef) := by
  refine ⟨fun hx ↦ ⟨fun ⟨i, hi⟩ ↦ ?_, fun ⟨i, hi⟩ ↦ ?_, fun ⟨i, hi⟩ ↦ ?_⟩,
      fun ⟨hR, hC, hH⟩ i ↦ ?_⟩
  · cases h : nf i with
    | real _ hp =>
      rw [splitProductEquiv_fst, FactorNormalForm.realEquiv_eq h]; exact (hp (x i)).mp (hx i)
    | _ => simp [FactorNormalForm.tag, h] at hi
  · cases h : nf i with
    | complex _ hp =>
      rw [splitProductEquiv_snd_fst, FactorNormalForm.complexEquiv_eq h]; exact (hp (x i)).mp (hx i)
    | _ => simp [FactorNormalForm.tag, h] at hi
  · cases h : nf i with
    | quaternion _ hp =>
      rw [splitProductEquiv_snd_snd, FactorNormalForm.quatEquiv_eq h]; exact (hp (x i)).mp (hx i)
    | _ => simp [FactorNormalForm.tag, h] at hi
  · cases h : nf i with
    | real _ hp =>
      have h' := hR ⟨i, by simp [FactorNormalForm.tag, h]⟩
      rw [splitProductEquiv_fst, FactorNormalForm.realEquiv_eq h] at h'; exact (hp (x i)).mpr h'
    | complex _ hp =>
      have h' := hC ⟨i, by simp [FactorNormalForm.tag, h]⟩
      rw [splitProductEquiv_snd_fst, FactorNormalForm.complexEquiv_eq h] at h'
      exact (hp (x i)).mpr h'
    | quaternion _ hp =>
      have h' := hH ⟨i, by simp [FactorNormalForm.tag, h]⟩
      rw [splitProductEquiv_snd_snd, FactorNormalForm.quatEquiv_eq h] at h'
      exact (hp (x i)).mpr h'

end SplitProduct

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
          (∀ i, ((e s).1 i).PosDef) ∧
          (∀ i, ((e s).2.1 i).PosDef) ∧
          (∀ i, ((e s).2.2 i).QuatPosDef) := by
  have : IsProperStar E := isProperStar_of_trace_mul_star_pos t (map_zero t) hpos
  have : IsSemisimpleRing E := isSemisimpleRing_of_trace_mul_star_pos t hpos
  obtain ⟨n, D, d, _, _, _, hd, ⟨eW⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite ℝ E
  let A : Fin n → Type _ := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) (D i)
  have hδ : ∀ i : Fin n, star (eW.symm (Pi.single i 1)) = eW.symm (Pi.single i 1) :=
    fun i ↦ star_coord_idempotent_eq_self A eW.toRingEquiv i
  let _ : ∀ i : Fin n, StarRing (FactorCopy (A i)) := inducedFactorStarRing eW hδ
  let nf : ∀ i : Fin n, FactorNormalForm (FactorCopy (A i)) (factorTrace eW t i) (d i) := fun i ↦
    Classical.choice (nonempty_factorNormalForm (factorCopyEquiv (A i)) (factorTrace eW t i)
      (factorTrace_cyclic eW t hcyclic i) (factorTrace_pos eW hδ t hpos i))
  let eR := Fintype.equivFin {i : Fin n // (nf i).tag = 0}
  let eC := Fintype.equivFin {i : Fin n // (nf i).tag = 1}
  let eH := Fintype.equivFin {i : Fin n // (nf i).tag = 2}
  let eWrapAlg := eW.trans (AlgEquiv.piCongrRight fun i ↦ (factorCopyEquiv (A i)).symm)
  let eWrap : E ≃⋆ₐ[ℝ] ∀ i : Fin n, FactorCopy (A i) :=
    StarAlgEquiv.ofAlgEquiv eWrapAlg fun x ↦ funext fun i ↦ FactorCopy.ext <| by
      simpa [eWrapAlg, inducedFactorStarRing_star_val, AlgEquiv.coe_toRingEquiv,
        AlgEquiv.toRingEquiv_symm] using eW.toRingEquiv.apply_star_eq_coord hδ x i
  let eReindex := StarAlgEquiv.ofAlgEquiv (AlgEquiv.prodCongr
    (AlgEquiv.piCongrLeft' ℝ (fun i : {i // (nf i).tag = 0} ↦
      Matrix (Fin (d i.1)) (Fin (d i.1)) ℝ) eR)
    (AlgEquiv.prodCongr
      (AlgEquiv.piCongrLeft' ℝ (fun i : {i // (nf i).tag = 1} ↦
        Matrix (Fin (d i.1)) (Fin (d i.1)) ℂ) eC)
      (AlgEquiv.piCongrLeft' ℝ (fun i : {i // (nf i).tag = 2} ↦
        Matrix (Fin (d i.1)) (Fin (d i.1)) ℍ[ℝ]) eH))) fun _ ↦ rfl
  let e : E ≃⋆ₐ[ℝ] _ := (eWrap.trans (splitProductEquiv nf)).trans eReindex
  refine ⟨_, _, _, fun i ↦ d (eR.symm i).1, fun i ↦ d (eC.symm i).1, fun i ↦ d (eH.symm i).1,
    fun i ↦ Nat.pos_of_ne_zero (hd (eR.symm i).1).out,
    fun i ↦ Nat.pos_of_ne_zero (hd (eC.symm i).1).out,
    fun i ↦ Nat.pos_of_ne_zero (hd (eH.symm i).1).out, e, fun s ↦ ?_⟩
  rw [isRosatiPositive_pi_iff eW hδ t s]
  exact (splitProductEquiv_pos nf (eWrap s)).trans (and_congr eR.symm.forall_congr_right.symm
    (and_congr eC.symm.forall_congr_right.symm eH.symm.forall_congr_right.symm))

end MainTheorem

end TauCeti
