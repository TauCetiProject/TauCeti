/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Centralizer
public import TauCeti.RepresentationTheory.Induction.LinearCharacter
-- `AddChar` occurs in the public construction.
public import Mathlib.Algebra.Group.AddChar
-- Non-public: conjugacy of non-scalar `2 × 2` matrices is used to identify the Jordan
-- elements which occur in the induced-character sum.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ConjugacyClasses
-- Non-public: fixed cosets are identified through their representatives.
import TauCeti.GroupTheory.QuotientGroup.Basic
-- Non-public: the sum of a nontrivial additive character over the nonzero field elements is used
-- in the Jordan computation.
import TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality

/-!
# Induction from the scalar--unipotent subgroup of `GL₂(𝔽_q)`

Let `Z U = TauCeti.GL2ScalarUnipotent F`, the subgroup of matrices
`!![a, b; 0, a]`.  A multiplicative character `μ : Fˣ → ℂˣ` and a nontrivial additive
character `ψ : F → ℂ` define the linear character

`(a, t) ↦ μ(a) ψ(t)`

under the isomorphism `Fˣ × (F, +) ≃ Z U`.  This file constructs that character and the
representation it induces to `GL₂(F)`.  It also computes its degree and its values on the four
families of conjugacy classes:

* `(q² - 1) μ(a)` on the scalar matrix `a I`;
* `0` on split regular semisimple and elliptic elements;
* `-μ(a)` on a nontrivial Jordan block with eigenvalue `a`.

The Jordan value is the only weighted computation.  The fixed cosets are indexed by `Fˣ` via
`diag(1,d)`; their values are `μ(a) ψ(a⁻¹bd)`.  Thus their sum is `μ(a)` times the sum of
`ψ` over the nonzero elements of `F`, namely `-1`.

Together with `TauCeti.GL2NonSplitTorus.indClassFun_gl2NonSplitTorusHom`, this supplies the two
induced class functions whose difference is the cuspidal character of `GL₂(𝔽_q)`.

## Main definitions

* `TauCeti.GL2ScalarUnipotent.linearChar`: the character `(a,t) ↦ μ(a)ψ(t)` of `Z U`.
* `TauCeti.GL2ScalarUnipotentRep`: its one-dimensional complex representation.
* `TauCeti.GL2ScalarUnipotentInduction`: the representation induced from `Z U` to `GL₂(F)`.

## Main results

* `TauCeti.finrank_GL2ScalarUnipotentInduction`: the induced representation has dimension
  `q² - 1`.
* `TauCeti.character_GL2ScalarUnipotentInduction_scalar`,
  `TauCeti.character_GL2ScalarUnipotentInduction_diagGL`,
  `TauCeti.character_GL2ScalarUnipotentInduction_jordanGL`, and
  `TauCeti.character_GL2ScalarUnipotentInduction_gl2NonSplitTorusHom`: its four character values.

## References

* C. Bonnafé, *Representations of `SL₂(𝔽_q)`*, Springer (2011), Chapter 6.
* I. Piatetski-Shapiro, *Complex Representations of `GL(2, K)` for Finite Fields `K`*,
  Contemporary Mathematics 16, AMS (1983), §5.
-/

public section

open Matrix

namespace TauCeti

universe u

namespace GL2ScalarUnipotent

section LinearCharacter

variable {F : Type u} [Field F]

/-- **The scalar--unipotent linear character** attached to a multiplicative character `μ` and
an additive character `ψ`.  In the coordinates `Fˣ × (F,+) ≃ Z U` it is
`(a,t) ↦ μ(a)ψ(t)`. -/
noncomputable def linearChar (μ : Fˣ →* ℂˣ) (ψ : AddChar F ℂ) :
    GL2ScalarUnipotent F →* ℂˣ :=
  (μ.coprod ψ.toMonoidHom.toHomUnits).comp (mulEquiv F).symm.toMonoidHom

/-- Evaluation of the scalar--unipotent character in product coordinates. -/
@[simp]
theorem linearChar_mulEquiv (μ : Fˣ →* ℂˣ) (ψ : AddChar F ℂ)
    (a : Fˣ) (t : Multiplicative F) :
    linearChar μ ψ (mulEquiv F (a, t)) = μ a * ψ.toMonoidHom.toHomUnits t := by
  simp [linearChar]

/-- The complex value of the scalar--unipotent character on a Jordan block. -/
@[simp]
theorem coe_linearChar_jordanGL (μ : Fˣ →* ℂˣ) (ψ : AddChar F ℂ) (a : Fˣ) (b : F) :
    ((linearChar μ ψ ⟨jordanGL a b, jordanGL_mem_gl2ScalarUnipotent a b⟩ : ℂˣ) : ℂ) =
      (μ a : ℂ) * ψ ((a⁻¹ : Fˣ) * b) := by
  let t : Multiplicative F := Multiplicative.ofAdd ((a⁻¹ : Fˣ) * b)
  have h : (mulEquiv F (a, t) : GL (Fin 2) F) = jordanGL a b := by
    simp [t]
  have hs : mulEquiv F (a, t) =
      ⟨jordanGL a b, jordanGL_mem_gl2ScalarUnipotent a b⟩ := Subtype.ext h
  rw [← hs, linearChar_mulEquiv, Units.val_mul, MonoidHom.coe_toHomUnits]
  rfl

end LinearCharacter

end GL2ScalarUnipotent

section Representations

variable (F : Type u) [Field F]

/-- The one-dimensional representation of `Z U` carrying
`TauCeti.GL2ScalarUnipotent.linearChar μ ψ`. -/
noncomputable def GL2ScalarUnipotentRep (μ : Fˣ →* ℂˣ) (ψ : AddChar F ℂ) :
    FDRep ℂ (GL2ScalarUnipotent F) :=
  FDRep.ofLinearCharacter (GL2ScalarUnipotent.linearChar μ ψ)

/-- The scalar--unipotent representation is one-dimensional. -/
@[simp]
theorem finrank_GL2ScalarUnipotentRep (μ : Fˣ →* ℂˣ) (ψ : AddChar F ℂ) :
    Module.finrank ℂ (GL2ScalarUnipotentRep F μ ψ) = 1 := by
  rw [GL2ScalarUnipotentRep, FDRep.finrank_ofLinearCharacter]

/-- The character of the scalar--unipotent line is its defining linear character. -/
@[simp]
theorem character_GL2ScalarUnipotentRep (μ : Fˣ →* ℂˣ) (ψ : AddChar F ℂ)
    (g : GL2ScalarUnipotent F) :
    (GL2ScalarUnipotentRep F μ ψ).character g =
      (GL2ScalarUnipotent.linearChar μ ψ g : ℂ) :=
  FDRep.char_ofLinearCharacter _ g

variable [Fintype F]

/-- **The scalar--unipotent induction for `GL₂(F)` with central character `μ`**: induce the
character `(a,t) ↦ μ(a)ψ(t)` from `Z U` to `GL₂(F)`. -/
noncomputable def GL2ScalarUnipotentInduction (μ : Fˣ →* ℂˣ) (ψ : AddChar F ℂ) :
    FDRep ℂ (GL (Fin 2) F) :=
  indFDRep (GL2ScalarUnipotentRep F μ ψ)

/-- The scalar--unipotent induction has dimension `q² - 1`, the index of `Z U`. -/
@[simp]
theorem finrank_GL2ScalarUnipotentInduction (μ : Fˣ →* ℂˣ) (ψ : AddChar F ℂ) :
    Module.finrank ℂ (GL2ScalarUnipotentInduction F μ ψ) = Fintype.card F ^ 2 - 1 := by
  rw [GL2ScalarUnipotentInduction, GL2ScalarUnipotentRep,
    finrank_indFDRep_ofLinearCharacter, index_gl2ScalarUnipotent]

end Representations

section CharacterValues

variable {F : Type u} [Field F] [Fintype F]
variable (μ : Fˣ →* ℂˣ) (ψ : AddChar F ℂ)

private theorem character_GL2ScalarUnipotentInduction_eq_indClassFun (g : GL (Fin 2) F) :
    (GL2ScalarUnipotentInduction F μ ψ).character g =
      indClassFun (GL2ScalarUnipotent F) (GL2ScalarUnipotentRep F μ ψ).character g := by
  rw [GL2ScalarUnipotentInduction, ← indClassFun_ofFDRep_character]

omit [Fintype F] in
private theorem character_GL2ScalarUnipotentRep_mem_classFunction :
    (GL2ScalarUnipotentRep F μ ψ).character ∈ ClassFunction ℂ (GL2ScalarUnipotent F) :=
  ClassFunction.mem_iff.mpr fun g h => (GL2ScalarUnipotentRep F μ ψ).char_conj g h

omit [Fintype F] in
private theorem indTerm_out_eq (g x : GL (Fin 2) F) :
    indTerm (GL2ScalarUnipotentRep F μ ψ).character g
        (Quotient.out (QuotientGroup.mk x : GL (Fin 2) F ⧸ GL2ScalarUnipotent F)) =
      indTerm (GL2ScalarUnipotentRep F μ ψ).character g x :=
  indTerm_eq_of_mk_eq (character_GL2ScalarUnipotentRep_mem_classFunction μ ψ) _ _ _
    (QuotientGroup.out_eq' _)

/-- **The scalar--unipotent induced character at a scalar matrix** is `(q² - 1) μ(a)`: every coset
contributes the value of the inducing character at the unchanged scalar. -/
@[simp]
theorem character_GL2ScalarUnipotentInduction_scalar (a : Fˣ) :
    (GL2ScalarUnipotentInduction F μ ψ).character
        (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      (Fintype.card F ^ 2 - 1 : ℂ) * (μ a : ℂ) := by
  classical
  let _ : Fintype (GL (Fin 2) F ⧸ GL2ScalarUnipotent F) := Fintype.ofFinite _
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ GL2ScalarUnipotent F := by
    simpa using jordanGL_mem_gl2ScalarUnipotent a (0 : F)
  have hconj : ∀ x : GL (Fin 2) F,
      x⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a * x =
        Matrix.GeneralLinearGroup.scalar (Fin 2) a := fun x => by
    rw [mul_assoc, Matrix.GeneralLinearGroup.scalar_commute a x, ← mul_assoc,
      inv_mul_cancel, one_mul]
  have hvalue : (GL2ScalarUnipotentRep F μ ψ).character
      ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) a, hmem⟩ = (μ a : ℂ) := by
    rw [character_GL2ScalarUnipotentRep]
    have hsub :
        (⟨Matrix.GeneralLinearGroup.scalar (Fin 2) a, hmem⟩ : GL2ScalarUnipotent F) =
          ⟨jordanGL a 0, jordanGL_mem_gl2ScalarUnipotent _ _⟩ :=
      Subtype.ext (jordanGL_zero a).symm
    rw [hsub, GL2ScalarUnipotent.coe_linearChar_jordanGL]
    simp
  rw [character_GL2ScalarUnipotentInduction_eq_indClassFun,
    indClassFun_eq_sum_of_smul_eq_self_mem _ _ Finset.univ
      (fun t _ => Finset.mem_univ t)]
  simp_rw [indTerm_apply, hconj, dite_eq_left hmem, hvalue]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Subgroup.index_eq_card, index_gl2ScalarUnipotent, nsmul_eq_mul]
  have hle : 1 ≤ Fintype.card F ^ 2 :=
    Nat.one_le_pow 2 (Fintype.card F) Fintype.card_pos
  rw [Nat.cast_sub hle]
  push_cast
  rfl

private def jordanConjugator (d : Fˣ) : GL (Fin 2) F := diagGL ![1, d]

omit [Fintype F] in
private theorem jordanConjugator_inv (d : Fˣ) :
    (jordanConjugator d)⁻¹ = diagGL ![1, d⁻¹] := by
  rw [jordanConjugator, ← map_inv]
  congr 1
  funext i
  fin_cases i <;> simp

omit [Fintype F] in
private theorem inv_jordanConjugator_mul_jordanGL_mul (a : Fˣ) (b : F) (d : Fˣ) :
    (jordanConjugator d)⁻¹ * jordanGL a b * jordanConjugator d =
      jordanGL a (b * (d : F)) := by
  rw [jordanConjugator_inv, jordanConjugator]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagGL_coe, coe_jordanGL, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

omit [Fintype F] in
private theorem jordanConjugator_normalizes (d : Fˣ) (g : GL (Fin 2) F)
    (hg : g ∈ GL2ScalarUnipotent F) :
    (jordanConjugator d)⁻¹ * g * jordanConjugator d ∈ GL2ScalarUnipotent F := by
  obtain ⟨a, b, rfl⟩ := mem_gl2ScalarUnipotent_iff.mp hg
  rw [inv_jordanConjugator_mul_jordanGL_mul]
  exact jordanGL_mem_gl2ScalarUnipotent _ _

omit [Fintype F] in
private theorem jordanConjugator_injective_quotient : Function.Injective
    (fun d : Fˣ => (jordanConjugator d : GL (Fin 2) F ⧸ GL2ScalarUnipotent F)) := by
  intro d e h
  rw [QuotientGroup.eq] at h
  rw [jordanConjugator_inv, jordanConjugator] at h
  obtain ⟨a, b, hab⟩ := mem_gl2ScalarUnipotent_iff.mp h
  have h00 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) hab
  have h11 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 1 1) hab
  have ha : a = 1 := Units.ext (by
    simpa [diagGL_coe, coe_jordanGL, Matrix.mul_apply, Fin.sum_univ_two] using h00.symm)
  apply Units.ext
  have hde : (d : F)⁻¹ * (e : F) = 1 := by
    simpa [ha, diagGL_coe, coe_jordanGL, Matrix.mul_apply, Fin.sum_univ_two] using h11
  exact (inv_mul_eq_one₀ d.ne_zero).mp hde

omit [Fintype F] in
private theorem jordanConjugator_conj_mem (a : Fˣ) (b : F) (d : Fˣ) :
    (jordanConjugator d)⁻¹ * jordanGL a b * jordanConjugator d ∈
      GL2ScalarUnipotent F := by
  rw [inv_jordanConjugator_mul_jordanGL_mul]
  exact jordanGL_mem_gl2ScalarUnipotent _ _

omit [Fintype F] in
private theorem quotient_eq_jordanConjugator_of_conj_mem (a : Fˣ) {b : F} (hb : b ≠ 0)
    {x : GL (Fin 2) F}
    (hx : x⁻¹ * jordanGL a b * x ∈ GL2ScalarUnipotent F) :
    ∃ d : Fˣ, (x : GL (Fin 2) F ⧸ GL2ScalarUnipotent F) = jordanConjugator d := by
  obtain ⟨c, y, hxy⟩ := mem_gl2ScalarUnipotent_iff.mp hx
  have hconj : IsConj (jordanGL a b) (jordanGL c y) :=
    isConj_iff.mpr ⟨x⁻¹, by simpa using hxy⟩
  have hy : y ≠ 0 := by
    intro hy
    have hscalar : (jordanGL c y : Matrix (Fin 2) (Fin 2) F) ∈
        Set.range (Matrix.scalar (Fin 2)) := by
      rw [hy, jordanGL_zero]
      exact ⟨(c : F), rfl⟩
    have heq := eq_of_mem_range_scalar_of_isConj hscalar hconj.symm
    have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) heq
    exact hb (by simpa [hy, coe_jordanGL, Matrix.scalar_apply] using this.symm)
  have hac : (a : F) = (c : F) := by
    have htr := trace_val_eq_of_isConj hconj
    have hdet : (Matrix.GeneralLinearGroup.det (jordanGL a b) : Fˣ) =
        Matrix.GeneralLinearGroup.det (jordanGL c y) :=
      isConj_iff_eq.mp (Matrix.GeneralLinearGroup.det.map_isConj hconj)
    have hsq : (a : F) ^ 2 = (c : F) ^ 2 := by
      simpa using congrArg Units.val hdet
    have hz : ((a : F) - (c : F)) ^ 2 = 0 := by
      rw [trace_jordanGL, trace_jordanGL] at htr
      calc
        ((a : F) - (c : F)) ^ 2 = (a : F) ^ 2 - (2 * (a : F)) * (c : F) + (c : F) ^ 2 := by
          ring
        _ = (c : F) ^ 2 - (2 * (c : F)) * (c : F) + (c : F) ^ 2 := by
          rw [hsq, htr]
        _ = 0 := by ring
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  have hacu : a = c := Units.ext hac
  subst c
  let d : Fˣ := Units.mk0 (b⁻¹ * y) (mul_ne_zero (inv_ne_zero hb) hy)
  have hbd : b * (d : F) = y := by simp [d, hb]
  refine ⟨d, QuotientGroup.eq.mpr ?_⟩
  have heqconj : x⁻¹ * jordanGL a b * x =
      (jordanConjugator d)⁻¹ * jordanGL a b * jordanConjugator d := by
    rw [hxy, inv_jordanConjugator_mul_jordanGL_mul, hbd]
  have hcentral : x * (jordanConjugator d)⁻¹ ∈
      Subgroup.centralizer {jordanGL a b} := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    calc
      jordanGL a b * (x * (jordanConjugator d)⁻¹) =
          x * (x⁻¹ * jordanGL a b * x) * (jordanConjugator d)⁻¹ := by group
      _ = x * ((jordanConjugator d)⁻¹ * jordanGL a b * jordanConjugator d) *
          (jordanConjugator d)⁻¹ := by rw [heqconj]
      _ = (x * (jordanConjugator d)⁻¹) * jordanGL a b := by group
  have hH : x * (jordanConjugator d)⁻¹ ∈ GL2ScalarUnipotent F := by
    rw [← centralizer_jordanGL (IsRegular.of_ne_zero hb).left]
    exact hcentral
  have hconjH := jordanConjugator_normalizes d _ hH
  have hDx : (jordanConjugator d)⁻¹ * x ∈ GL2ScalarUnipotent F := by
    convert hconjH using 1
    group
  exact (GL2ScalarUnipotent F).inv_mem hDx

omit [Fintype F] in
private theorem indTerm_jordanConjugator (a : Fˣ) (b : F) (d : Fˣ) :
    indTerm (GL2ScalarUnipotentRep F μ ψ).character (jordanGL a b)
        (jordanConjugator d) = (μ a : ℂ) * ψ ((a⁻¹ : Fˣ) * (b * (d : F))) := by
  rw [indTerm_apply, dite_eq_left (jordanConjugator_conj_mem a b d)]
  have hsub :
      (⟨(jordanConjugator d)⁻¹ * jordanGL a b * jordanConjugator d,
        jordanConjugator_conj_mem a b d⟩ : GL2ScalarUnipotent F) =
        ⟨jordanGL a (b * (d : F)), jordanGL_mem_gl2ScalarUnipotent _ _⟩ :=
    Subtype.ext (inv_jordanConjugator_mul_jordanGL_mul a b d)
  rw [hsub]
  rw [character_GL2ScalarUnipotentRep]
  exact GL2ScalarUnipotent.coe_linearChar_jordanGL μ ψ a _

omit [Fintype F] in
private theorem indClassFun_eq_zero_of_conj_notMem [Finite F]
    (f : GL2ScalarUnipotent F → ℂ) (g : GL (Fin 2) F)
    (h : ∀ x : GL (Fin 2) F, x⁻¹ * g * x ∉ GL2ScalarUnipotent F) :
    indClassFun (GL2ScalarUnipotent F) f g = 0 := by
  classical
  rw [indClassFun_apply]
  exact Finset.sum_eq_zero fun t _ => dite_eq_right (h _)

omit [Fintype F] in
private theorem conj_notMem_gl2ScalarUnipotent_diagGL {t : Fin 2 → Fˣ} (ht : t 0 ≠ t 1)
    (x : GL (Fin 2) F) :
    x⁻¹ * diagGL t * x ∉ GL2ScalarUnipotent F := by
  intro hx
  obtain ⟨c, y, hxy⟩ := mem_gl2ScalarUnipotent_iff.mp hx
  have hconj : IsConj (diagGL t) (jordanGL c y) :=
    isConj_iff.mpr ⟨x⁻¹, by simpa using hxy⟩
  have htr := trace_val_eq_of_isConj hconj
  have htr' : (t 0 : F) + (t 1 : F) = 2 * (c : F) := by
    simpa [diagGL_coe, Matrix.trace_fin_two_of, trace_jordanGL, two_mul] using htr
  have hdet : Matrix.GeneralLinearGroup.det (diagGL t) =
      Matrix.GeneralLinearGroup.det (jordanGL c y) :=
    isConj_iff_eq.mp (Matrix.GeneralLinearGroup.det.map_isConj hconj)
  have hdet' : (t 0 : F) * (t 1 : F) = (c : F) ^ 2 := by
    have := congrArg Units.val hdet
    simpa [Fin.prod_univ_two] using this
  have hsquare : ((t 0 : F) - (t 1 : F)) ^ 2 = 0 := by
    calc
      ((t 0 : F) - (t 1 : F)) ^ 2 =
          ((t 0 : F) + (t 1 : F)) ^ 2 - 4 * ((t 0 : F) * (t 1 : F)) := by ring
      _ = (2 * (c : F)) ^ 2 - 4 * (c : F) ^ 2 := by rw [htr', hdet']
      _ = 0 := by ring
  exact ht (Units.ext (sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)))

/-- **The scalar--unipotent induced character vanishes on split regular semisimple elements.** -/
@[simp]
theorem character_GL2ScalarUnipotentInduction_diagGL {t : Fin 2 → Fˣ} (ht : t 0 ≠ t 1) :
    (GL2ScalarUnipotentInduction F μ ψ).character (diagGL t) = 0 := by
  rw [character_GL2ScalarUnipotentInduction_eq_indClassFun]
  exact indClassFun_eq_zero_of_conj_notMem _ _
    (conj_notMem_gl2ScalarUnipotent_diagGL ht)

section Elliptic

variable {E : Type*} [Field E] [Algebra F E] (hE : Module.finrank F E = 2)

/-- **The scalar--unipotent induced character vanishes on elliptic elements.** -/
@[simp]
theorem character_GL2ScalarUnipotentInduction_gl2NonSplitTorusHom {z : Eˣ}
    (hz : (z : E) ∉ Set.range (algebraMap F E)) :
    (GL2ScalarUnipotentInduction F μ ψ).character (GL2NonSplitTorusHom F E hE z) = 0 := by
  rw [character_GL2ScalarUnipotentInduction_eq_indClassFun]
  refine indClassFun_eq_zero_of_conj_notMem _ _ fun x hx => ?_
  obtain ⟨a, b, hab⟩ := mem_gl2ScalarUnipotent_iff.mp hx
  apply GL2NonSplitTorus.conj_notMem_gl2Borel hE hz x⁻¹
  rw [inv_inv]
  rw [hab]
  exact jordanGL_mem_gl2Borel _ _

end Elliptic

/-- **The scalar--unipotent induced character at a nontrivial Jordan block** is `-μ(a)`. -/
@[simp]
theorem character_GL2ScalarUnipotentInduction_jordanGL
    (hψ : ψ ≠ 1) (a : Fˣ) {b : F} (hb : b ≠ 0) :
    (GL2ScalarUnipotentInduction F μ ψ).character (jordanGL a b) = -(μ a : ℂ) := by
  classical
  let T : Finset (GL (Fin 2) F ⧸ GL2ScalarUnipotent F) :=
    Finset.univ.map ⟨fun d : Fˣ => jordanConjugator d, jordanConjugator_injective_quotient⟩
  rw [character_GL2ScalarUnipotentInduction_eq_indClassFun]
  refine (indClassFun_eq_sum_of_smul_eq_self_mem _ _ T ?_).trans ?_
  · intro t ht
    rw [← QuotientGroup.out_eq' t] at ht ⊢
    obtain ⟨d, hd⟩ := quotient_eq_jordanConjugator_of_conj_mem a hb
      ((smul_quotientGroup_mk_eq_self_iff _ _ _).mp ht)
    exact Finset.mem_map.mpr ⟨d, Finset.mem_univ d, hd.symm⟩
  · have hsum :
        (∑ d : Fˣ,
          indTerm (GL2ScalarUnipotentRep F μ ψ).character (jordanGL a b)
            (Quotient.out
              (jordanConjugator d : GL (Fin 2) F ⧸ GL2ScalarUnipotent F))) = -(μ a : ℂ) := by
      have hterm (d : Fˣ) :
          indTerm (GL2ScalarUnipotentRep F μ ψ).character (jordanGL a b)
              (Quotient.out
                (jordanConjugator d : GL (Fin 2) F ⧸ GL2ScalarUnipotent F)) =
            (μ a : ℂ) * ψ ((a⁻¹ : Fˣ) * (b * (d : F))) :=
        (indTerm_out_eq μ ψ _ _).trans (indTerm_jordanConjugator μ ψ a b d)
      simp_rw [hterm]
      have harg : ∀ d : Fˣ, (a⁻¹ : Fˣ) * (b * (d : F)) =
          ((a⁻¹ * Units.mk0 b hb : Fˣ) : F) * (d : F) := by
        intro d
        simp
        ring
      simp_rw [harg]
      rw [← Finset.mul_sum,
        AddChar.sum_units_mul_eq_neg_one ψ hψ (a⁻¹ * Units.mk0 b hb)]
      ring
    simpa only [T, Finset.sum_map, Function.Embedding.coeFn_mk] using hsum

end CharacterValues

end TauCeti
