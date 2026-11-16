/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import TauCeti.LinearAlgebra.ExteriorPower.Basic
public import TauCeti.RingTheory.DeRham.Basic

/-!
# The ordinary algebraic de Rham differential and cochain complex

Using the differential-symbol presentation from `TauCeti.RingTheory.DeRham.Basic`, this file
constructs the ordinary algebraic de Rham differential
`d : Forms A B n →ₗ[A] Forms A B (n + 1)` by descending the free-symbol rule
`[c; v₁, …, vₙ] ↦ Dc ∧ Dv₁ ∧ ⋯ ∧ Dvₙ` along `symbolQuotEquiv`.

We establish the characteristic laws of `d`: its value on elementary forms (`d_elementary`),
uniqueness from that rule (`d_unique`), identification with the universal derivation
`KaehlerDifferential.D` in degree `0` (`d_zero_degree`), the square-zero identity (`d_d`,
`d_squared`), the graded Leibniz rule for the exterior wedge product (`d_leibniz`), and the
scalar Leibniz rule (`d_smul`). Assembling the modules `Forms A B n` and differentials `d A B n`
yields the nonnegative cochain complex `TauCeti.DeRham.complex A B` in
`CochainComplex (ModuleCat A) ℕ`.

## Main definitions

* `TauCeti.DeRham.freeDifferential`: the `A`-linear differential on formal symbols
  `Symbols A B n →ₗ[A] Forms A B (n + 1)`.
* `TauCeti.DeRham.d`: the ordinary algebraic de Rham differential
  `Forms A B n →ₗ[A] Forms A B (n + 1)`.
* `TauCeti.DeRham.complex`: the ordinary algebraic de Rham cochain complex `Ω•_(B/A)` in
  `CochainComplex (ModuleCat A) ℕ`.

## Main results

* `TauCeti.DeRham.freeDifferential_relations`:
  `symbolRelations A B n ≤ LinearMap.ker (freeDifferential A B n)`.
* `TauCeti.DeRham.d_elementary` and `TauCeti.DeRham.d_unique`: characterization of `d` on
  elementary forms.
* `TauCeti.DeRham.d_zero_degree`: `d 0` identifies with `KaehlerDifferential.D` via
  `exteriorPower.zeroEquiv` and `exteriorPower.oneEquiv`.
* `TauCeti.DeRham.d_d` and `TauCeti.DeRham.d_squared`: `d (n + 1) ∘ d n = 0`.
* `TauCeti.DeRham.d_leibniz`: graded Leibniz rule
  `d (α ∧ β) = d α ∧ β + (-1) ^ m • (α ∧ d β)` in `ExteriorAlgebra B Ω[B⁄A]`.
* `TauCeti.DeRham.d_smul`: scalar Leibniz rule `d (b • ω) = Db ∧ ω + b • d ω`.

## References

* [Stacks Project, Tag 0FKE](https://stacks.math.columbia.edu/tag/0FKE), Section 10.132.
* Joël Riou's presentation design for the algebraic de Rham complex.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti.DeRham

section FreeDifferential

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]

/-- The `A`-linear differential on formal differential `n`-symbols, sending `[c; v₁, …, vₙ]` to
`Dc ∧ Dv₁ ∧ ⋯ ∧ Dvₙ`. -/
def freeDifferential (n : ℕ) : Symbols A B n →ₗ[A] Forms A B (n + 1) :=
  Finsupp.linearCombination A fun p : B × (Fin n → B) =>
    elementary A B (n + 1) 1 (Fin.cons p.1 p.2)

@[simp]
theorem freeDifferential_single (n : ℕ) (c : B) (v : Fin n → B) (a : A) :
    freeDifferential A B n (Finsupp.single (c, v) a) =
      a • elementary A B (n + 1) 1 (Fin.cons c v) :=
  Finsupp.linearCombination_single (R := A)
    (v := fun p : B × (Fin n → B) => elementary A B (n + 1) 1 (Fin.cons p.1 p.2)) a (c, v)

@[simp]
theorem freeDifferential_sym (n : ℕ) (c : B) (v : Fin n → B) :
    freeDifferential A B n (sym A B n c v) = elementary A B (n + 1) 1 (Fin.cons c v) := by
  rw [sym_def, freeDifferential_single, one_smul]

private theorem cons_D_update (n : ℕ) (c : B) (v : Fin n → B) (i : Fin n) (z : B) :
    KaehlerDifferential.D A B ∘ Fin.cons c (Function.update v i z) =
      Function.update (KaehlerDifferential.D A B ∘ Fin.cons c v) i.succ
        (KaehlerDifferential.D A B z) := by
  rw [Fin.cons_update, Function.comp_update]

private theorem cons_D_head (n : ℕ) (c : B) (v : Fin n → B) :
    KaehlerDifferential.D A B ∘ Fin.cons c v =
      Function.update (KaehlerDifferential.D A B ∘ Fin.cons (0 : B) v) 0
        (KaehlerDifferential.D A B c) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp
  · simp

/-- Characteristic-free verification that `freeDifferential` annihilates the slot Leibniz
relation: the `x • (Dc ∧ ⋯ ∧ Dy)` and `y • (Dc ∧ ⋯ ∧ Dx)` terms cancel, leaving
`- c • (Dx ∧ ⋯ ∧ Dy + Dy ∧ ⋯ ∧ Dx) = 0` by `AlternatingMap.map_swap`. -/
private theorem freeDifferential_slot_mul (n : ℕ) (c : B) (v : Fin n → B) (i : Fin n) (x y : B) :
    elementary A B (n + 1) 1 (Fin.cons c (Function.update v i (x * y))) -
      elementary A B (n + 1) 1 (Fin.cons (c * x) (Function.update v i y)) -
      elementary A B (n + 1) 1 (Fin.cons (c * y) (Function.update v i x)) = 0 := by
  let ι := exteriorPower.ιMulti B (n + 1) (M := KaehlerDifferential A B)
  let D := KaehlerDifferential.D A B
  have hL : elementary A B (n + 1) 1 (Fin.cons c (Function.update v i (x * y))) =
      x • ι (D ∘ Fin.cons c (Function.update v i y)) +
        y • ι (D ∘ Fin.cons c (Function.update v i x)) := by
    rw [elementary_one_coeff, cons_D_update, Derivation.leibniz,
      AlternatingMap.map_update_add, AlternatingMap.map_update_smul,
      AlternatingMap.map_update_smul, ← cons_D_update, ← cons_D_update]
  have hcx : elementary A B (n + 1) 1 (Fin.cons (c * x) (Function.update v i y)) =
      c • ι (D ∘ Fin.cons x (Function.update v i y)) +
        x • ι (D ∘ Fin.cons c (Function.update v i y)) := by
    rw [elementary_one_coeff, cons_D_head, Derivation.leibniz,
      AlternatingMap.map_update_add, AlternatingMap.map_update_smul,
      AlternatingMap.map_update_smul, ← cons_D_head, ← cons_D_head]
  have hcy : elementary A B (n + 1) 1 (Fin.cons (c * y) (Function.update v i x)) =
      c • ι (D ∘ Fin.cons y (Function.update v i x)) +
        y • ι (D ∘ Fin.cons c (Function.update v i x)) := by
    rw [elementary_one_coeff, cons_D_head, Derivation.leibniz,
      AlternatingMap.map_update_add, AlternatingMap.map_update_smul,
      AlternatingMap.map_update_smul, ← cons_D_head, ← cons_D_head]
  have hswap : D ∘ Fin.cons y (Function.update v i x) =
      (D ∘ Fin.cons x (Function.update v i y)) ∘ Equiv.swap 0 i.succ := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [Equiv.swap_apply_left, (Fin.succ_ne_zero i).symm]
    · by_cases hji : j = i
      · subst hji; simp [Equiv.swap_apply_right, (Fin.succ_ne_zero j).symm]
      · simp only [Function.comp_apply, Fin.cons_succ, Function.update_of_ne hji,
          Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero j) ((Fin.succ_injective n).ne hji)]
  have halt : ι (D ∘ Fin.cons y (Function.update v i x)) =
      -ι (D ∘ Fin.cons x (Function.update v i y)) := by
    rw [hswap]
    exact ι.map_swap (D ∘ Fin.cons x (Function.update v i y)) (Fin.succ_ne_zero i).symm
  rw [hL, hcx, hcy, halt, smul_neg]
  abel

/-- Every differential-symbol relation lies in the kernel of `freeDifferential`. -/
theorem freeDifferential_relations (n : ℕ) :
    symbolRelations A B n ≤ LinearMap.ker (freeDifferential A B n) := by
  rw [symbolRelations_eq_span, Submodule.span_le]
  intro s hs
  rw [mem_relationSet_iff] at hs
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  cases hs with
  | coeff_add c e v =>
    rw [map_sub, map_sub, freeDifferential_sym, freeDifferential_sym, freeDifferential_sym,
      elementary_one_coeff, elementary_one_coeff, elementary_one_coeff, cons_D_head, map_add,
      AlternatingMap.map_update_add, ← cons_D_head, ← cons_D_head, add_sub_cancel_left, sub_self]
  | coeff_smul a c v =>
    rw [map_sub, map_smul, freeDifferential_sym, freeDifferential_sym, elementary_one_coeff,
      elementary_one_coeff, cons_D_head, (KaehlerDifferential.D A B).map_smul,
      ← algebraMap_smul B a, AlternatingMap.map_update_smul, ← cons_D_head, algebraMap_smul,
      sub_self]
  | slot_add c v i x y =>
    rw [map_sub, map_sub, freeDifferential_sym, freeDifferential_sym, freeDifferential_sym,
      elementary_one_coeff, elementary_one_coeff, elementary_one_coeff, cons_D_update, map_add,
      AlternatingMap.map_update_add, ← cons_D_update, ← cons_D_update, add_sub_cancel_left,
      sub_self]
  | slot_mul c v i x y =>
    rw [map_sub, map_sub, freeDifferential_sym, freeDifferential_sym, freeDifferential_sym]
    exact freeDifferential_slot_mul A B n c v i x y
  | slot_algebraMap c v i a =>
    rw [freeDifferential_sym, elementary_one_coeff, cons_D_update, Derivation.map_algebraMap,
      AlternatingMap.map_update_zero]
  | slot_eq c v i j hij hv =>
    rw [freeDifferential_sym]
    exact elementary_eq_zero_of_eq (n + 1) 1 (Fin.cons c v) ((Fin.succ_injective n).ne hij)
      (by simpa using hv)

end FreeDifferential

section Differential

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]

/-- The ordinary algebraic de Rham differential `dₙ : Ωⁿ_(B/A) →ₗ[A] Ωⁿ⁺¹_(B/A)`, obtained by
descending `freeDifferential A B n` along the differential-symbol presentation. It is uniquely
characterized by `dₙ (c · Dv₁ ∧ ⋯ ∧ Dvₙ) = Dc ∧ Dv₁ ∧ ⋯ ∧ Dvₙ` (`d_elementary`, `d_unique`). -/
def d (n : ℕ) : Forms A B n →ₗ[A] Forms A B (n + 1) :=
  ((symbolRelations A B n).liftQ (freeDifferential A B n) (freeDifferential_relations A B n)).comp
    (symbolQuotEquiv A B n).symm.toLinearMap

/-- On an elementary differential form, `d (c · Dv₁ ∧ ⋯ ∧ Dvₙ) = Dc ∧ Dv₁ ∧ ⋯ ∧ Dvₙ`. -/
@[simp]
theorem d_elementary (n : ℕ) (c : B) (v : Fin n → B) :
    d A B n (elementary A B n c v) = elementary A B (n + 1) 1 (Fin.cons c v) := by
  rw [d, LinearMap.comp_apply, LinearEquiv.coe_coe, symbolQuotEquiv_symm_elementary,
    Submodule.liftQ_apply, freeDifferential_sym]

/-- An `A`-linear map `Forms A B n →ₗ[A] Forms A B (n + 1)` satisfying the elementary-form formula
equals `d A B n`. -/
theorem d_unique (n : ℕ) {f : Forms A B n →ₗ[A] Forms A B (n + 1)}
    (hf : ∀ (c : B) (v : Fin n → B),
      f (elementary A B n c v) = elementary A B (n + 1) 1 (Fin.cons c v)) :
    f = d A B n := by
  apply LinearMap.ext
  intro ω
  induction ω using induction_elementary with
  | zero => rw [map_zero, map_zero]
  | add ω₁ ω₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | elem c v => rw [hf, d_elementary]

/-- In degree `0`, transporting `d A B 0` along `exteriorPower.zeroEquiv` and
`exteriorPower.oneEquiv` recovers the universal derivation `KaehlerDifferential.D A B`. -/
@[simp]
theorem d_zero_degree (b : B) :
    exteriorPower.oneEquiv B (KaehlerDifferential A B)
        (d A B 0 ((exteriorPower.zeroEquiv B (KaehlerDifferential A B)).symm b)) =
      KaehlerDifferential.D A B b := by
  rw [← elementary_zero_eq_zeroEquiv_symm b Fin.elim0, d_elementary, oneEquiv_elementary,
    Fin.cons_zero, one_smul]

/-- The degree-`0` de Rham differential annihilates constants from the base ring `A`. -/
@[simp]
theorem d_algebraMap (a : A) :
    d A B 0 ((exteriorPower.zeroEquiv B (KaehlerDifferential A B)).symm (algebraMap A B a)) =
      0 := by
  apply (exteriorPower.oneEquiv B (KaehlerDifferential A B)).injective
  rw [d_zero_degree, Derivation.map_algebraMap, map_zero]

/-- **Square-zero law (pointwise)**: `d (n + 1) (d n ω) = 0`. -/
@[simp]
theorem d_d (n : ℕ) (ω : Forms A B n) : d A B (n + 1) (d A B n ω) = 0 := by
  induction ω using induction_elementary with
  | zero => rw [map_zero, map_zero]
  | add ω₁ ω₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, add_zero]
  | elem c v =>
    rw [d_elementary, d_elementary, elementary_one_coeff]
    exact (exteriorPower.ιMulti B (n + 2)).map_coord_zero (0 : Fin (n + 2)) (by simp)

/-- **Square-zero law (map level)**: `d (n + 1) ∘ d n = 0`. -/
@[simp]
theorem d_squared (n : ℕ) : (d A B (n + 1)).comp (d A B n) = 0 := by
  apply LinearMap.ext
  intro ω
  exact d_d A B n ω

private theorem coe_elementary_cons_one (n : ℕ) (c : B) (v : Fin n → B) :
    (elementary A B (n + 1) 1 (Fin.cons c v) : ExteriorAlgebra B (KaehlerDifferential A B)) =
      ExteriorAlgebra.ι B (KaehlerDifferential.D A B c) *
        ExteriorAlgebra.ιMulti B n (KaehlerDifferential.D A B ∘ v) := by
  rw [elementary_one_coeff, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply]
  simp [Matrix.vecTail, Function.comp_def]

private theorem d_leibniz_elementary {m n : ℕ} (c c' : B) (u : Fin m → B) (v : Fin n → B) :
    (d A B (m + n) (exteriorPower.wedge B (KaehlerDifferential A B) m n
        (elementary A B m c u) (elementary A B n c' v)) :
      ExteriorAlgebra B (KaehlerDifferential A B)) =
      (d A B m (elementary A B m c u) : ExteriorAlgebra B (KaehlerDifferential A B)) *
          (elementary A B n c' v : ExteriorAlgebra B (KaehlerDifferential A B)) +
        (-1 : ℤ) ^ m •
          ((elementary A B m c u : ExteriorAlgebra B (KaehlerDifferential A B)) *
            (d A B n (elementary A B n c' v) : ExteriorAlgebra B (KaehlerDifferential A B))) := by
  let D := KaehlerDifferential.D A B
  have happend : ExteriorAlgebra.ιMulti B (m + n) (D ∘ Fin.append u v) =
      ExteriorAlgebra.ιMulti B m (D ∘ u) * ExteriorAlgebra.ιMulti B n (D ∘ v) := by
    symm
    rw [ExteriorAlgebra.ιMulti_mul_ιMulti]
    congr 1
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [Fin.append_left]
    · simp [Fin.append_right]
  have hanti : ExteriorAlgebra.ι B (D c') * ExteriorAlgebra.ιMulti B m (D ∘ u) =
      (-1 : ℤ) ^ m • (ExteriorAlgebra.ιMulti B m (D ∘ u) * ExteriorAlgebra.ι B (D c')) := by
    rw [ExteriorAlgebra.ι_mul_ιMulti_anticomm, Units.smul_def, Units.val_pow_eq_pow_val,
      Units.val_neg, Units.val_one]
  rw [wedge_elementary, d_elementary, d_elementary, d_elementary, coe_elementary_cons_one,
    coe_elementary_cons_one, coe_elementary_cons_one, happend]
  simp only [elementary_def, Submodule.coe_smul_of_tower, exteriorPower.ιMulti_apply_coe]
  rw [Derivation.leibniz, map_add, map_smul, map_smul, add_mul, smul_mul_assoc, smul_mul_assoc,
    ← mul_assoc (ExteriorAlgebra.ι B (D c')), hanti, mul_assoc (ExteriorAlgebra.ι B (D c)),
    add_comm]
  congr 1
  · rw [← mul_assoc, ← mul_smul_comm, mul_assoc]
  · rw [smul_mul_assoc, smul_comm c ((-1 : ℤ) ^ m), smul_mul_assoc, mul_assoc]

/-- **Graded Leibniz rule**: inside `ExteriorAlgebra B Ω[B⁄A]`,
`d (α ∧ β) = d α ∧ β + (-1) ^ m • (α ∧ d β)` for `α : Forms A B m` and `β : Forms A B n`. -/
theorem d_leibniz {m n : ℕ} (α : Forms A B m) (β : Forms A B n) :
    (d A B (m + n) (exteriorPower.wedge B (KaehlerDifferential A B) m n α β) :
      ExteriorAlgebra B (KaehlerDifferential A B)) =
      (d A B m α : ExteriorAlgebra B (KaehlerDifferential A B)) * β +
        (-1 : ℤ) ^ m • ((α : ExteriorAlgebra B (KaehlerDifferential A B)) * d A B n β) := by
  induction α using induction_elementary with
  | zero => simp only [map_zero, LinearMap.zero_apply, ZeroMemClass.coe_zero, zero_mul, smul_zero,
      add_zero]
  | add α₁ α₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add, add_mul, smul_add, h₁, h₂]
    abel
  | elem c u =>
    induction β using induction_elementary with
    | zero => simp only [map_zero, ZeroMemClass.coe_zero, mul_zero, smul_zero, add_zero]
    | add β₁ β₂ h₁ h₂ =>
      simp only [map_add, Submodule.coe_add, mul_add, smul_add, h₁, h₂]
      abel
    | elem c' v => exact d_leibniz_elementary A B c c' u v

/-- **Scalar Leibniz rule**: for `b : B` and `ω : Forms A B n`,
`d (b • ω) = Db ∧ ω + b • d ω`. -/
theorem d_smul (n : ℕ) (b : B) (ω : Forms A B n) :
    d A B n (b • ω) =
      TauCeti.ExteriorAlgebra.wedgeLeft (KaehlerDifferential.D A B b) n ω + b • d A B n ω := by
  induction ω using induction_elementary with
  | zero => simp
  | add ω₁ ω₂ h₁ h₂ =>
    simp only [smul_add, map_add, h₁, h₂]
    abel
  | elem c v =>
    apply Subtype.ext
    rw [elementary_smul_coeff, d_elementary, d_elementary, Submodule.coe_add,
      TauCeti.ExteriorAlgebra.coe_wedgeLeft_apply, Submodule.coe_smul_of_tower,
      coe_elementary_cons_one, coe_elementary_cons_one, elementary_def,
      Submodule.coe_smul_of_tower, exteriorPower.ιMulti_apply_coe, Derivation.leibniz,
      map_add, map_smul, map_smul, add_mul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
      add_comm]

end Differential

section Complex

universe u v

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

-- The terms must reduce to `ModuleCat.of A (Forms A B n)` to typecheck `complex_d` and
-- `complexMap`.
/-- The ordinary algebraic de Rham complex `Ω•_(B/A)` as a nonnegative cochain complex of
`A`-modules, with `Forms A B n` in degree `n` and differential `d A B n`. -/
@[expose]
def complex : CochainComplex (ModuleCat.{v} A) ℕ :=
  CochainComplex.of
    (fun n => ModuleCat.of A (Forms A B n))
    (fun n => ModuleCat.ofHom (d A B n))
    (fun n => ModuleCat.hom_ext (d_squared A B n))

/-- The degree-`n` term of `complex A B` is `ModuleCat.of A (Forms A B n)`. -/
@[simp]
theorem complex_X (n : ℕ) : (complex A B).X n = ModuleCat.of A (Forms A B n) :=
  (rfl)

/-- The differential of `complex A B` from degree `n` to `n + 1` is `ModuleCat.ofHom (d A B n)`. -/
@[simp]
theorem complex_d (n : ℕ) : (complex A B).d n (n + 1) = ModuleCat.ofHom (d A B n) := by
  apply CochainComplex.of_d

/-- Pointwise evaluation of the differential of `complex A B` from degree `n` to `n + 1`. -/
theorem complex_d_apply (n : ℕ) (ω : Forms A B n) :
    (complex A B).d n (n + 1) ω = d A B n ω := by
  rw [complex_d]
  rfl

/-- Differentials of `complex A B` vanish outside adjacent degrees `i ↦ i + 1`. -/
theorem complex_d_ne {i j : ℕ} (h : i + 1 ≠ j) : (complex A B).d i j = 0 := by
  apply CochainComplex.of_d_ne
  exact h

end Complex

end TauCeti.DeRham
