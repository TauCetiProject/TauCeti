/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.Multilinear.DFinsupp
import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing

/-!
# Algebraic differential forms and their differential-symbol presentation

For a commutative `A`-algebra `B`, the module of ordinary algebraic differential `n`-forms of `B`
over `A` is the `n`-th exterior power `⋀[B]^n Ω[B⁄A]` of the module of Kähler differentials,
regarded as an `A`-module via the scalar tower `A → B → ExteriorAlgebra B Ω[B⁄A]`.

To construct `A`-linear maps out of `⋀[B]^n Ω[B⁄A]` that are not `B`-linear — in particular the
de Rham differential `d : Ωⁿ_(B/A) →ₗ[A] Ωⁿ⁺¹_(B/A)` — this file establishes a characteristic-free
`A`-module presentation of `⋀[B]^n Ω[B⁄A]` by formal differential symbols `[c; v₁, …, vₙ]` spanning
the free `A`-module `(B × (Fin n → B)) →₀ A` modulo six explicit families of relations:
coefficient additivity, coefficient `A`-linearity, slot additivity, slot Leibniz, vanishing on
base-ring constants in a differential slot, and strict alternation on repeated slots (without
dividing by `2`, so valid in every characteristic including characteristic `2`, and uniformly in
degree `0`).

## Main definitions

* `TauCeti.DeRham.Forms A B n`: abbreviation for `⋀[B]^n Ω[B⁄A]`.
* `TauCeti.DeRham.Symbols A B n`: the free `A`-module `(B × (Fin n → B)) →₀ A` of formal
  differential `n`-symbols.
* `TauCeti.DeRham.sym A B n c v`: the basis symbol `[c; v]` in `Symbols A B n`.
* `TauCeti.DeRham.elementary A B n c v`: the elementary `n`-form `c • (Dv₁ ∧ ⋯ ∧ Dvₙ)`.
* `TauCeti.DeRham.IsSymbolRelation`, `TauCeti.DeRham.relationSet`, and
  `TauCeti.DeRham.symbolRelations`: the six generating relation families and the `A`-submodule they
  span.
* `TauCeti.DeRham.symbolMap`: the `A`-linear evaluation map `Symbols A B n →ₗ[A] Forms A B n`.
* `TauCeti.DeRham.symbolQuotEquiv`: the canonical `A`-linear isomorphism
  `(Symbols A B n ⧸ symbolRelations A B n) ≃ₗ[A] Forms A B n`.

## Main results

* `TauCeti.DeRham.symbolMap_surjective`: `symbolMap A B n` is surjective for every `n`.
* `TauCeti.DeRham.induction_elementary`: additive induction principle on `Forms A B n` from
  elementary forms.
* `TauCeti.DeRham.symbolRelations_ker`: `LinearMap.ker (symbolMap A B n) = symbolRelations A B n`,
  proved by endowing `Symbols A B n ⧸ symbolRelations A B n` with a `B`-module structure and
  descending an alternating `B`-multilinear map on `B →₀ B` along Mathlib's presentation of
  `KaehlerDifferential A B`.

## References

* [Stacks Project, Tag 0FKE](https://stacks.math.columbia.edu/tag/0FKE), Section 10.132,
  construction of the algebraic de Rham complex.
* Joël Riou's presentation design for `exteriorPower` and algebraic differential forms.
-/

public section

noncomputable section

namespace TauCeti.DeRham

section Carriers

/-- The module of ordinary algebraic differential `n`-forms of `B` over `A`, namely
`⋀[B]^n Ω[B⁄A]`. It carries a `B`-module structure, an `A`-module structure, and the scalar tower
`IsScalarTower A B (Forms A B n)` inherited from `ExteriorAlgebra B Ω[B⁄A]`. -/
abbrev Forms (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) :=
  ⋀[B]^n (KaehlerDifferential A B)

/-- The free `A`-module of formal differential `n`-symbols `[c; v₁, …, vₙ]` with `c : B` and
`v : Fin n → B`. -/
abbrev Symbols (A B : Type*) [Zero A] (n : ℕ) :=
  (B × (Fin n → B)) →₀ A

/-- The basis symbol `[c; v]` in `Symbols A B n`. -/
def sym (A B : Type*) [Zero A] [One A] (n : ℕ) (c : B) (v : Fin n → B) :
    Symbols A B n :=
  Finsupp.single (c, v) (1 : A)

/-- Defining equation of a basis symbol `[c; v]`. -/
theorem sym_def {A B : Type*} [Zero A] [One A] (n : ℕ) (c : B) (v : Fin n → B) :
    sym A B n c v = Finsupp.single (c, v) (1 : A) :=
  (rfl)

/-- The elementary differential `n`-form `c · Dv₁ ∧ ⋯ ∧ Dvₙ` in `Forms A B n`. -/
def elementary (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (n : ℕ) (c : B) (v : Fin n → B) : Forms A B n :=
  c • exteriorPower.ιMulti B n (KaehlerDifferential.D A B ∘ v)

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

theorem elementary_def (n : ℕ) (c : B) (v : Fin n → B) :
    elementary A B n c v = c • exteriorPower.ιMulti B n (KaehlerDifferential.D A B ∘ v) :=
  (rfl)

@[simp]
theorem elementary_zero_coeff (n : ℕ) (v : Fin n → B) :
    elementary A B n 0 v = 0 := by
  rw [elementary_def, zero_smul]

theorem elementary_one_coeff (n : ℕ) (v : Fin n → B) :
    elementary A B n 1 v = exteriorPower.ιMulti B n (KaehlerDifferential.D A B ∘ v) := by
  rw [elementary_def, one_smul]

theorem elementary_add_coeff (n : ℕ) (c e : B) (v : Fin n → B) :
    elementary A B n (c + e) v = elementary A B n c v + elementary A B n e v := by
  rw [elementary_def, elementary_def, elementary_def, add_smul]

theorem elementary_smul_coeff (n : ℕ) (b c : B) (v : Fin n → B) :
    b • elementary A B n c v = elementary A B n (b * c) v := by
  rw [elementary_def, elementary_def, smul_smul]

theorem elementary_base_smul_coeff (n : ℕ) (a : A) (c : B) (v : Fin n → B) :
    a • elementary A B n c v = elementary A B n (a • c) v := by
  rw [elementary_def, elementary_def, smul_assoc]

theorem elementary_eq_zero_of_eq (n : ℕ) (c : B) (v : Fin n → B) {i j : Fin n}
    (hij : i ≠ j) (hv : v i = v j) :
    elementary A B n c v = 0 := by
  rw [elementary_def,
    (exteriorPower.ιMulti B n).map_eq_zero_of_eq _ (congrArg (KaehlerDifferential.D A B) hv) hij,
    smul_zero]

@[simp]
theorem zeroEquiv_elementary (c : B) (v : Fin 0 → B) :
    exteriorPower.zeroEquiv B (KaehlerDifferential A B) (elementary A B 0 c v) = c := by
  simp [elementary_def]

theorem elementary_zero_eq_zeroEquiv_symm (c : B) (v : Fin 0 → B) :
    elementary A B 0 c v = (exteriorPower.zeroEquiv B (KaehlerDifferential A B)).symm c := by
  apply (exteriorPower.zeroEquiv B (KaehlerDifferential A B)).injective
  simp

@[simp]
theorem oneEquiv_elementary (c : B) (v : Fin 1 → B) :
    exteriorPower.oneEquiv B (KaehlerDifferential A B) (elementary A B 1 c v) =
      c • KaehlerDifferential.D A B (v 0) := by
  simp [elementary_def]

/-- The wedge product of two elementary differential forms multiplies their coefficients and
concatenates their differential slots. -/
theorem wedge_elementary {m n : ℕ} (c c' : B) (u : Fin m → B) (v : Fin n → B) :
    exteriorPower.wedge B (KaehlerDifferential A B) m n
        (elementary A B m c u) (elementary A B n c' v) =
      elementary A B (m + n) (c * c') (Fin.append u v) := by
  simp only [elementary_def, map_smul, LinearMap.smul_apply, exteriorPower.wedge_ιMulti,
    smul_smul, mul_comm c' c]
  congr 2
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Fin.append_left]
  · simp [Fin.append_right]

end Carriers

section Relations

/-- The six generating families of differential-symbol relations in degree `n`:
1. coefficient additivity `[c + e; v] - [c; v] - [e; v]`,
2. coefficient `A`-linearity `[a • c; v] - a • [c; v]`,
3. slot additivity `[c; v(i ↦ x + y)] - [c; v(i ↦ x)] - [c; v(i ↦ y)]`,
4. slot Leibniz `[c; v(i ↦ x * y)] - [c * x; v(i ↦ y)] - [c * y; v(i ↦ x)]`,
5. vanishing on base-ring constants `[c; v(i ↦ algebraMap A B a)]`,
6. strict alternation `[c; v]` whenever `v i = v j` for `i ≠ j`. -/
inductive IsSymbolRelation (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) :
    Symbols A B n → Prop
  | coeff_add (c e : B) (v : Fin n → B) :
      IsSymbolRelation A B n (sym A B n (c + e) v - sym A B n c v - sym A B n e v)
  | coeff_smul (a : A) (c : B) (v : Fin n → B) :
      IsSymbolRelation A B n (sym A B n (a • c) v - a • sym A B n c v)
  | slot_add (c : B) (v : Fin n → B) (i : Fin n) (x y : B) :
      IsSymbolRelation A B n
        (sym A B n c (Function.update v i (x + y)) -
          sym A B n c (Function.update v i x) -
          sym A B n c (Function.update v i y))
  | slot_mul (c : B) (v : Fin n → B) (i : Fin n) (x y : B) :
      IsSymbolRelation A B n
        (sym A B n c (Function.update v i (x * y)) -
          sym A B n (c * x) (Function.update v i y) -
          sym A B n (c * y) (Function.update v i x))
  | slot_algebraMap (c : B) (v : Fin n → B) (i : Fin n) (a : A) :
      IsSymbolRelation A B n (sym A B n c (Function.update v i (algebraMap A B a)))
  | slot_eq (c : B) (v : Fin n → B) (i j : Fin n) (hij : i ≠ j) (hv : v i = v j) :
      IsSymbolRelation A B n (sym A B n c v)

/-- The set of generating differential-symbol relations in degree `n`. -/
def relationSet (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) :
    Set (Symbols A B n) :=
  {s | IsSymbolRelation A B n s}

theorem mem_relationSet_iff {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}
    {s : Symbols A B n} :
    s ∈ relationSet A B n ↔ IsSymbolRelation A B n s :=
  Iff.rfl

/-- The `A`-submodule of relations among ordinary differential `n`-symbols. -/
def symbolRelations (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) :
    Submodule A (Symbols A B n) :=
  Submodule.span A (relationSet A B n)

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]

theorem symbolRelations_eq_span (n : ℕ) :
    symbolRelations A B n = Submodule.span A (relationSet A B n) :=
  (rfl)

theorem symbolRelations_coeff_add (n : ℕ) (c e : B) (v : Fin n → B) :
    sym A B n (c + e) v - sym A B n c v - sym A B n e v ∈ symbolRelations A B n :=
  Submodule.subset_span (.coeff_add c e v)

theorem symbolRelations_coeff_smul (n : ℕ) (a : A) (c : B) (v : Fin n → B) :
    sym A B n (a • c) v - a • sym A B n c v ∈ symbolRelations A B n :=
  Submodule.subset_span (.coeff_smul a c v)

theorem symbolRelations_slot_add (n : ℕ) (c : B) (v : Fin n → B) (i : Fin n) (x y : B) :
    sym A B n c (Function.update v i (x + y)) -
      sym A B n c (Function.update v i x) -
      sym A B n c (Function.update v i y) ∈ symbolRelations A B n :=
  Submodule.subset_span (.slot_add c v i x y)

theorem symbolRelations_slot_mul (n : ℕ) (c : B) (v : Fin n → B) (i : Fin n) (x y : B) :
    sym A B n c (Function.update v i (x * y)) -
      sym A B n (c * x) (Function.update v i y) -
      sym A B n (c * y) (Function.update v i x) ∈ symbolRelations A B n :=
  Submodule.subset_span (.slot_mul c v i x y)

theorem symbolRelations_slot_algebraMap (n : ℕ) (c : B) (v : Fin n → B) (i : Fin n) (a : A) :
    sym A B n c (Function.update v i (algebraMap A B a)) ∈ symbolRelations A B n :=
  Submodule.subset_span (.slot_algebraMap c v i a)

theorem symbolRelations_slot_eq (n : ℕ) (c : B) (v : Fin n → B) {i j : Fin n}
    (hij : i ≠ j) (hv : v i = v j) :
    sym A B n c v ∈ symbolRelations A B n :=
  Submodule.subset_span (.slot_eq c v i j hij hv)

end Relations

section Evaluation

/-- Left multiplication of the coefficient slot of a formal differential symbol by `b : B`. -/
private def mulCoeff (A B : Type*) [Semiring A] [Mul B] (n : ℕ) (b : B) :
    Symbols A B n →ₗ[A] Symbols A B n :=
  Finsupp.lmapDomain A A (Prod.map (b * ·) id)

private theorem mulCoeff_single (A B : Type*) [Semiring A] [Mul B] (n : ℕ) (b c : B)
    (v : Fin n → B) (a : A) :
    mulCoeff A B n b (Finsupp.single (c, v) a) = Finsupp.single (b * c, v) a :=
  Finsupp.mapDomain_single

private theorem mulCoeff_sym (A B : Type*) [Semiring A] [Mul B] (n : ℕ) (b c : B)
    (v : Fin n → B) :
    mulCoeff A B n b (sym A B n c v) = sym A B n (b * c) v :=
  mulCoeff_single A B n b c v 1

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]

/-- The `A`-linear evaluation map sending a formal differential symbol `[c; v]` to the elementary
differential `n`-form `c · Dv₁ ∧ ⋯ ∧ Dvₙ`. -/
def symbolMap (n : ℕ) : Symbols A B n →ₗ[A] Forms A B n :=
  Finsupp.linearCombination A fun p : B × (Fin n → B) => elementary A B n p.1 p.2

@[simp]
theorem symbolMap_single (n : ℕ) (c : B) (v : Fin n → B) (a : A) :
    symbolMap A B n (Finsupp.single (c, v) a) = a • elementary A B n c v :=
  Finsupp.linearCombination_single (R := A)
    (v := fun p : B × (Fin n → B) => elementary A B n p.1 p.2) a (c, v)

@[simp]
theorem symbolMap_sym (n : ℕ) (c : B) (v : Fin n → B) :
    symbolMap A B n (sym A B n c v) = elementary A B n c v := by
  rw [sym_def, symbolMap_single, one_smul]

private theorem symbolMap_mulCoeff (n : ℕ) (b : B) (s : Symbols A B n) :
    symbolMap A B n (mulCoeff A B n b s) = b • symbolMap A B n s := by
  induction s using Finsupp.induction with
  | zero => simp
  | single_add p a s _ _ ih =>
    rw [map_add, map_add, map_add, smul_add, ih, mulCoeff_single, symbolMap_single,
      symbolMap_single, smul_comm, elementary_smul_coeff]

/-- Every differential `n`-form is an `A`-linear combination of elementary forms
`c · Dv₁ ∧ ⋯ ∧ Dvₙ`. -/
theorem symbolMap_surjective (n : ℕ) : Function.Surjective (symbolMap A B n) := by
  intro ω
  have hω : ω ∈ Submodule.span B
      (exteriorPower.ιMulti B n '' {u | Set.range u ⊆ Set.range (KaehlerDifferential.D A B)}) := by
    rw [exteriorPower.ιMulti_span_of_span B n (KaehlerDifferential A B)
      (KaehlerDifferential.span_range_derivation A B)]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := Set.range_subset_range_iff_exists_comp.mp hu
    exact ⟨sym A B n 1 v, by rw [symbolMap_sym, elementary_one_coeff]⟩
  | zero => exact ⟨0, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨sx, rfl⟩ := hx
    obtain ⟨sy, rfl⟩ := hy
    exact ⟨sx + sy, map_add _ sx sy⟩
  | smul b x _ hx =>
    obtain ⟨s, rfl⟩ := hx
    exact ⟨mulCoeff A B n b s, symbolMap_mulCoeff A B n b s⟩

/-- Additive induction principle on `Forms A B n`: a predicate holding on `0`, closed under
addition, and holding on every elementary form `c · Dv₁ ∧ ⋯ ∧ Dvₙ` holds on all `n`-forms. -/
theorem induction_elementary {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}
    {P : Forms A B n → Prop} (zero : P 0) (add : ∀ ω₁ ω₂, P ω₁ → P ω₂ → P (ω₁ + ω₂))
    (elem : ∀ (c : B) (v : Fin n → B), P (elementary A B n c v)) (ω : Forms A B n) :
    P ω := by
  obtain ⟨s, rfl⟩ := symbolMap_surjective A B n ω
  induction s using Finsupp.induction with
  | zero => simpa using zero
  | single_add p a s _ _ ih =>
    rw [map_add, symbolMap_single, elementary_base_smul_coeff]
    exact add _ _ (elem (a • p.1) p.2) ih

end Evaluation

section Presentation

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]

private theorem symbolRelations_le_ker (n : ℕ) :
    symbolRelations A B n ≤ LinearMap.ker (symbolMap A B n) := by
  rw [symbolRelations_eq_span, Submodule.span_le]
  intro s hs
  rw [mem_relationSet_iff] at hs
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  cases hs with
  | coeff_add c e v =>
    simp only [map_sub, symbolMap_sym, elementary_add_coeff, add_sub_cancel_left, sub_self]
  | coeff_smul a c v =>
    simp only [map_sub, map_smul, symbolMap_sym, elementary_base_smul_coeff, sub_self]
  | slot_add c v i x y =>
    simp only [map_sub, symbolMap_sym, elementary_def, Function.comp_update, map_add,
      AlternatingMap.map_update_add, smul_add, add_sub_cancel_left, sub_self]
  | slot_mul c v i x y =>
    simp only [map_sub, symbolMap_sym, elementary_def, Function.comp_update, Derivation.leibniz,
      AlternatingMap.map_update_add, AlternatingMap.map_update_smul, smul_add, smul_smul,
      add_sub_cancel_left, sub_self]
  | slot_algebraMap c v i a =>
    simp only [symbolMap_sym, elementary_def, Function.comp_update, Derivation.map_algebraMap,
      AlternatingMap.map_update_zero, smul_zero]
  | slot_eq c v i j hij hv =>
    rw [symbolMap_sym, elementary_eq_zero_of_eq n c v hij hv]

private theorem mulCoeff_le_comap (n : ℕ) (b : B) :
    symbolRelations A B n ≤ (symbolRelations A B n).comap (mulCoeff A B n b) := by
  conv_lhs => rw [symbolRelations_eq_span]
  rw [Submodule.span_le]
  intro s hs
  rw [mem_relationSet_iff] at hs
  rw [SetLike.mem_coe, Submodule.mem_comap]
  cases hs with
  | coeff_add c e v =>
    simpa only [map_sub, mulCoeff_sym, mul_add] using
      symbolRelations_coeff_add A B n (b * c) (b * e) v
  | coeff_smul a c v =>
    simpa only [map_sub, map_smul, mulCoeff_sym, mul_smul_comm] using
      symbolRelations_coeff_smul A B n a (b * c) v
  | slot_add c v i x y =>
    simpa only [map_sub, mulCoeff_sym] using
      symbolRelations_slot_add A B n (b * c) v i x y
  | slot_mul c v i x y =>
    simpa only [map_sub, mulCoeff_sym, mul_assoc] using
      symbolRelations_slot_mul A B n (b * c) v i x y
  | slot_algebraMap c v i a =>
    simpa only [mulCoeff_sym] using
      symbolRelations_slot_algebraMap A B n (b * c) v i a
  | slot_eq c v i j hij hv =>
    simpa only [mulCoeff_sym] using
      symbolRelations_slot_eq A B n (b * c) v hij hv

private theorem mkQ_sym_zero_coeff (n : ℕ) (v : Fin n → B) :
    (symbolRelations A B n).mkQ (sym A B n 0 v) = 0 := by
  have h := symbolRelations_coeff_smul A B n (0 : A) 0 v
  rw [zero_smul, zero_smul, sub_zero] at h
  exact (Submodule.Quotient.mk_eq_zero _).mpr h

private theorem mkQ_sym_add_coeff (n : ℕ) (c e : B) (v : Fin n → B) :
    (symbolRelations A B n).mkQ (sym A B n (c + e) v) =
      (symbolRelations A B n).mkQ (sym A B n c v) +
        (symbolRelations A B n).mkQ (sym A B n e v) := by
  have h := (Submodule.Quotient.mk_eq_zero _).mpr (symbolRelations_coeff_add A B n c e v)
  rw [← Submodule.mkQ_apply, map_sub, map_sub, sub_eq_zero, sub_eq_iff_eq_add] at h
  exact h.trans (add_comm _ _)

private theorem mkQ_sym_base_smul_coeff (n : ℕ) (a : A) (c : B) (v : Fin n → B) :
    (symbolRelations A B n).mkQ (sym A B n (a • c) v) =
      a • (symbolRelations A B n).mkQ (sym A B n c v) := by
  have h := (Submodule.Quotient.mk_eq_zero _).mpr (symbolRelations_coeff_smul A B n a c v)
  rw [← Submodule.mkQ_apply, map_sub, map_smul, sub_eq_zero] at h
  exact h

private theorem mkQ_sym_slot_add (n : ℕ) (c : B) (v : Fin n → B) (i : Fin n) (x y : B) :
    (symbolRelations A B n).mkQ (sym A B n c (Function.update v i (x + y))) =
      (symbolRelations A B n).mkQ (sym A B n c (Function.update v i x)) +
        (symbolRelations A B n).mkQ (sym A B n c (Function.update v i y)) := by
  have h := (Submodule.Quotient.mk_eq_zero _).mpr (symbolRelations_slot_add A B n c v i x y)
  rw [← Submodule.mkQ_apply, map_sub, map_sub, sub_eq_zero, sub_eq_iff_eq_add] at h
  exact h.trans (add_comm _ _)

private theorem mkQ_sym_slot_mul (n : ℕ) (c : B) (v : Fin n → B) (i : Fin n) (x y : B) :
    (symbolRelations A B n).mkQ (sym A B n c (Function.update v i (x * y))) =
      (symbolRelations A B n).mkQ (sym A B n (c * x) (Function.update v i y)) +
        (symbolRelations A B n).mkQ (sym A B n (c * y) (Function.update v i x)) := by
  have h := (Submodule.Quotient.mk_eq_zero _).mpr (symbolRelations_slot_mul A B n c v i x y)
  rw [← Submodule.mkQ_apply, map_sub, map_sub, sub_eq_zero, sub_eq_iff_eq_add] at h
  exact h.trans (add_comm _ _)

/-- Characteristic-free swap antisymmetry in `Symbols A B n ⧸ symbolRelations A B n`, deduced from
slot additivity and strict alternation on repeated slots. -/
private theorem mkQ_sym_add_swap (n : ℕ) (c : B) (v : Fin n → B) {i j : Fin n} (hij : i ≠ j) :
    (symbolRelations A B n).mkQ (sym A B n c v) +
      (symbolRelations A B n).mkQ (sym A B n c (v ∘ Equiv.swap i j)) = 0 := by
  let w := Function.update (Function.update v i (v i + v j)) j (v i + v j)
  have hzero : (symbolRelations A B n).mkQ (sym A B n c w) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr <|
      symbolRelations_slot_eq A B n c w hij (by simp [w, hij])
  have h1 : (symbolRelations A B n).mkQ
      (sym A B n c (Function.update (Function.update v j (v i)) i (v i))) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr <|
      symbolRelations_slot_eq A B n c _ hij (by simp [hij.symm])
  have h2 : (symbolRelations A B n).mkQ (sym A B n c (Function.update v i (v j))) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr <|
      symbolRelations_slot_eq A B n c _ hij (by simp [hij.symm])
  have hswap : Function.update (Function.update v j (v i)) i (v j) = v ∘ Equiv.swap i j := by
    funext k
    by_cases hki : k = i
    · subst hki; simp [Equiv.swap_apply_left]
    · by_cases hkj : k = j
      · subst hkj; simp [hki, Equiv.swap_apply_right]
      · simp [hki, hkj, Equiv.swap_apply_of_ne_of_ne]
  have hself : Function.update (Function.update v i (v i + v j)) j (v j) =
      Function.update v i (v i + v j) := by
    rw [Function.update_comm hij, Function.update_eq_self]
  rw [mkQ_sym_slot_add, Function.update_comm hij, mkQ_sym_slot_add, hself, mkQ_sym_slot_add,
    h1, h2, hswap, Function.update_eq_self, zero_add, add_zero, add_comm] at hzero
  exact hzero

/-- The descended `B`-scalar action on `Symbols A B n ⧸ symbolRelations A B n`. -/
private def quotSMulMap (n : ℕ) (b : B) :
    (Symbols A B n ⧸ symbolRelations A B n) →ₗ[A] (Symbols A B n ⧸ symbolRelations A B n) :=
  Submodule.mapQ (symbolRelations A B n) (symbolRelations A B n)
    (mulCoeff A B n b) (mulCoeff_le_comap A B n b)

private theorem quotSMulMap_mkQ_sym (n : ℕ) (b c : B) (v : Fin n → B) :
    quotSMulMap A B n b ((symbolRelations A B n).mkQ (sym A B n c v)) =
      (symbolRelations A B n).mkQ (sym A B n (b * c) v) := by
  rw [quotSMulMap, Submodule.mkQ_apply, Submodule.mapQ_apply, ← Submodule.mkQ_apply, mulCoeff_sym]

private theorem quot_eq_of_mkQ_sym {n : ℕ}
    {f g : (Symbols A B n ⧸ symbolRelations A B n) →ₗ[A]
      (Symbols A B n ⧸ symbolRelations A B n)}
    (h : ∀ c v, f ((symbolRelations A B n).mkQ (sym A B n c v)) =
      g ((symbolRelations A B n).mkQ (sym A B n c v))) : f = g := by
  apply Submodule.linearMap_qext
  apply Finsupp.lhom_ext'
  rintro ⟨c, v⟩
  apply LinearMap.ext_ring
  simpa only [LinearMap.comp_apply, Finsupp.lsingle_apply, ← sym_def] using h c v

/-- The `B`-module structure on `Symbols A B n ⧸ symbolRelations A B n` induced by `mulCoeff`. -/
@[instance_reducible]
private def quotModuleB (n : ℕ) :
    Module B (Symbols A B n ⧸ symbolRelations A B n) where
  smul b q := quotSMulMap A B n b q
  one_smul q :=
    LinearMap.congr_fun
      (quot_eq_of_mkQ_sym A B (f := quotSMulMap A B n 1) (g := LinearMap.id) fun c v => by
        rw [quotSMulMap_mkQ_sym, one_mul, LinearMap.id_apply]) q
  mul_smul b₁ b₂ q :=
    LinearMap.congr_fun
      (quot_eq_of_mkQ_sym A B
        (f := quotSMulMap A B n (b₁ * b₂))
        (g := (quotSMulMap A B n b₁).comp (quotSMulMap A B n b₂)) fun c v => by
        rw [LinearMap.comp_apply, quotSMulMap_mkQ_sym, quotSMulMap_mkQ_sym, quotSMulMap_mkQ_sym,
          mul_assoc]) q
  smul_zero b := map_zero (quotSMulMap A B n b)
  smul_add b q₁ q₂ := map_add (quotSMulMap A B n b) q₁ q₂
  add_smul b₁ b₂ q :=
    LinearMap.congr_fun
      (quot_eq_of_mkQ_sym A B
        (f := quotSMulMap A B n (b₁ + b₂))
        (g := quotSMulMap A B n b₁ + quotSMulMap A B n b₂) fun c v => by
        rw [LinearMap.add_apply, quotSMulMap_mkQ_sym, quotSMulMap_mkQ_sym, quotSMulMap_mkQ_sym,
          add_mul, mkQ_sym_add_coeff]) q
  zero_smul q :=
    LinearMap.congr_fun
      (quot_eq_of_mkQ_sym A B (f := quotSMulMap A B n 0) (g := 0) fun c v => by
        rw [LinearMap.zero_apply, quotSMulMap_mkQ_sym, zero_mul, mkQ_sym_zero_coeff]) q

private theorem quotModuleB_smul_mkQ_sym (n : ℕ) (b c : B) (v : Fin n → B) :
    let : Module B (Symbols A B n ⧸ symbolRelations A B n) := quotModuleB A B n
    b • (symbolRelations A B n).mkQ (sym A B n c v) =
      (symbolRelations A B n).mkQ (sym A B n (b * c) v) :=
  quotSMulMap_mkQ_sym A B n b c v

private theorem quotIsScalarTower (n : ℕ) :
    let : Module B (Symbols A B n ⧸ symbolRelations A B n) := quotModuleB A B n
    IsScalarTower A B (Symbols A B n ⧸ symbolRelations A B n) := by
  let : Module B (Symbols A B n ⧸ symbolRelations A B n) := quotModuleB A B n
  refine IsScalarTower.of_algebraMap_smul fun a q => ?_
  exact LinearMap.congr_fun
    (quot_eq_of_mkQ_sym A B
      (f := quotSMulMap A B n (algebraMap A B a))
      (g := a • LinearMap.id) fun c v => by
      rw [LinearMap.smul_apply, LinearMap.id_apply, quotSMulMap_mkQ_sym, ← Algebra.smul_def,
        mkQ_sym_base_smul_coeff]) q

/-- The canonical `B`-multilinear map `(Fin n → (B →₀ B)) →ₘₗ[B] Q` sending
`fun i => single (v i) (r i)` to `(∏ i, r i) • [1; v]`. -/
private def freeMultilinear (n : ℕ) :
    letI : Module B (Symbols A B n ⧸ symbolRelations A B n) := quotModuleB A B n
    (Fin n → (B →₀ B)) →ₘₗ[B] (Symbols A B n ⧸ symbolRelations A B n) :=
  letI : Module B (Symbols A B n ⧸ symbolRelations A B n) := quotModuleB A B n
  letI : DecidableEq B := Classical.decEq B
  (MultilinearMap.fromDFinsuppEquiv (fun _ : Fin n => B) (RingHom.id B)
    (fun v : Fin n → B =>
      MultilinearMap.mkPiRing B (Fin n)
        ((symbolRelations A B n).mkQ (sym A B n 1 v)))).compLinearMap
    fun _ => (finsuppLequivDFinsupp B).toLinearMap

private theorem freeMultilinear_single (n : ℕ) (v r : Fin n → B) :
    let : Module B (Symbols A B n ⧸ symbolRelations A B n) := quotModuleB A B n
    freeMultilinear A B n (fun i => Finsupp.single (v i) (r i)) =
      (∏ i, r i) • (symbolRelations A B n).mkQ (sym A B n 1 v) := by
  let : Module B (Symbols A B n ⧸ symbolRelations A B n) := quotModuleB A B n
  classical
  simp [freeMultilinear, MultilinearMap.compLinearMap_apply]

private theorem freeMultilinear_apply (n : ℕ) (f : Fin n → (B →₀ B)) :
    let : Module B (Symbols A B n ⧸ symbolRelations A B n) := quotModuleB A B n
    freeMultilinear A B n f =
      ∑ v ∈ Fintype.piFinset (fun i => (f i).support),
        (∏ i, f i (v i)) • (symbolRelations A B n).mkQ (sym A B n 1 v) := by
  let : Module B (Symbols A B n ⧸ symbolRelations A B n) := quotModuleB A B n
  classical
  rw [freeMultilinear, MultilinearMap.compLinearMap_apply, MultilinearMap.fromDFinsuppEquiv_apply]
  refine Finset.sum_congr ?_ fun v _ => by simp
  ext v
  simp [Fintype.mem_piFinset]

/-- `freeMultilinear` vanishes whenever two slots are equal, in every characteristic. -/
private theorem freeMultilinear_eq_zero_of_eq (n : ℕ) (f : Fin n → (B →₀ B))
    {i j : Fin n} (hf : f i = f j) (hij : i ≠ j) :
    let : Module B (Symbols A B n ⧸ symbolRelations A B n) := quotModuleB A B n
    freeMultilinear A B n f = 0 := by
  let : Module B (Symbols A B n ⧸ symbolRelations A B n) := quotModuleB A B n
  classical
  rw [freeMultilinear_apply]
  have hswap_f : ∀ k : Fin n, f (Equiv.swap i j k) = f k := fun k => by
    by_cases hki : k = i
    · subst hki; simp [Equiv.swap_apply_left, hf]
    · by_cases hkj : k = j
      · subst hkj; simp [Equiv.swap_apply_right, hf]
      · simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
  refine Finset.sum_involution (fun v _ => v ∘ Equiv.swap i j) ?_ ?_ ?_ ?_
  · intro v _
    have hprod : ∏ k : Fin n, f k (v (Equiv.swap i j k)) = ∏ k : Fin n, f k (v k) := by
      conv_lhs =>
        arg 2; ext k
        rw [← hswap_f k]
      exact Equiv.prod_comp (Equiv.swap i j) (fun k => f k (v k))
    simp_rw [Function.comp_apply]
    rw [hprod, ← smul_add, mkQ_sym_add_swap A B n 1 v hij, smul_zero]
  · intro v _ hne hEq
    have hvij : v i = v j := by
      have := congrFun hEq i
      simpa [Equiv.swap_apply_left] using this.symm
    have hzero : (symbolRelations A B n).mkQ (sym A B n 1 v) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (symbolRelations_slot_eq A B n 1 v hij hvij)
    exact hne (by rw [hzero, smul_zero])
  · intro v hv
    rw [Fintype.mem_piFinset] at hv ⊢
    intro k
    simpa [hswap_f k] using hv (Equiv.swap i j k)
  · intro v _
    ext k
    simp

/-- `freeMultilinear` vanishes when a generator `t` of `KaehlerDifferential.kerTotal` is substituted
into slot `i` of a singleton family. -/
private theorem freeMultilinear_update_kerTotal_gen (n : ℕ) (i : Fin n) (v : Fin n → B)
    {t : B →₀ B}
    (ht : t ∈ (((Set.range fun x : B × B =>
        Finsupp.single x.1 1 + Finsupp.single x.2 1 - Finsupp.single (x.1 + x.2) 1) ∪
      Set.range fun x : B × B =>
        Finsupp.single x.2 x.1 + Finsupp.single x.1 x.2 - Finsupp.single (x.1 * x.2) 1) ∪
      Set.range fun x : A => Finsupp.single (algebraMap A B x) 1)) :
    let : Module B (Symbols A B n ⧸ symbolRelations A B n) := quotModuleB A B n
    freeMultilinear A B n (Function.update (fun k => Finsupp.single (v k) 1) i t) = 0 := by
  let : Module B (Symbols A B n ⧸ symbolRelations A B n) := quotModuleB A B n
  have hsingle : ∀ x r : B,
      freeMultilinear A B n
          (Function.update (fun k => Finsupp.single (v k) 1) i (Finsupp.single x r)) =
        (symbolRelations A B n).mkQ (sym A B n r (Function.update v i x)) := fun x r => by
    have hfun : Function.update (fun k => Finsupp.single (v k) 1) i (Finsupp.single x r) =
        fun k => Finsupp.single (Function.update v i x k)
          (Function.update (fun _ => (1 : B)) i r k) := by
      funext k
      by_cases hk : k = i <;> simp [hk]
    rw [hfun, freeMultilinear_single, Finset.prod_update_of_mem (Finset.mem_univ i),
      Finset.prod_const_one, mul_one, quotModuleB_smul_mkQ_sym, mul_one]
  rcases ht with (⟨⟨x, y⟩, rfl⟩ | ⟨⟨x, y⟩, rfl⟩) | ⟨a, rfl⟩
  · rw [MultilinearMap.map_update_sub, MultilinearMap.map_update_add,
      hsingle, hsingle, hsingle, mkQ_sym_slot_add, sub_self]
  · rw [MultilinearMap.map_update_sub, MultilinearMap.map_update_add,
      hsingle, hsingle, hsingle, mkQ_sym_slot_mul]
    simp only [one_mul, sub_self]
  · rw [hsingle]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (symbolRelations_slot_algebraMap A B n 1 v i a)

/-- If substituting `t : B →₀ B` into slot `i` kills `freeMultilinear` on every singleton tuple,
then substituting `t` into slot `i` kills `freeMultilinear` on every tuple. -/
private theorem freeMultilinear_update_eq_zero_of_single (n : ℕ) (f : Fin n → (B →₀ B))
    (i : Fin n) (t : B →₀ B)
    (ht : ∀ v : Fin n → B,
      let : Module B (Symbols A B n ⧸ symbolRelations A B n) := quotModuleB A B n
      freeMultilinear A B n (Function.update (fun k => Finsupp.single (v k) 1) i t) = 0) :
    let : Module B (Symbols A B n ⧸ symbolRelations A B n) := quotModuleB A B n
    freeMultilinear A B n (Function.update f i t) = 0 := by
  let : Module B (Symbols A B n ⧸ symbolRelations A B n) := quotModuleB A B n
  classical
  let K : (B →₀ B) →ₗ[B] (B →₀ B) := Finsupp.linearCombination B (fun _ : B => t)
  let G : (Fin n → (B →₀ B)) →ₘₗ[B] (Symbols A B n ⧸ symbolRelations A B n) :=
    (freeMultilinear A B n).compLinearMap (Function.update (fun _ => LinearMap.id) i K)
  have hG_zero : G = 0 := by
    have hG' : G.compLinearMap (fun _ => (finsuppLequivDFinsupp B).symm.toLinearMap) = 0 := by
      apply MultilinearMap.dfinsupp_ext
      intro v
      apply MultilinearMap.ext
      intro r
      simp only [G, MultilinearMap.compLinearMap_apply, zero_apply,
        LinearEquiv.coe_coe, DFinsupp.lsingle_apply, finsuppLequivDFinsupp_symm_apply,
        DFinsupp.toFinsupp_single]
      have hupd :
          (fun k => Function.update (fun _ => LinearMap.id) i K k (Finsupp.single (v k) (r k))) =
            Function.update (fun k => r k • Finsupp.single (v k) 1) i (r i • t) := by
        funext k
        by_cases hk : k = i
        · subst hk; simp [K, Finsupp.linearCombination_single]
        · simp [hk, Finsupp.smul_single]
      have harg_smul : Function.update (fun k => r k • Finsupp.single (v k) 1) i t =
          fun k => Function.update r i 1 k •
            Function.update (fun k => Finsupp.single (v k) 1) i t k := by
        funext k
        by_cases hk : k = i <;> simp [hk]
      rw [hupd, MultilinearMap.map_update_smul, harg_smul, MultilinearMap.map_smul_univ, ht v,
        smul_zero, smul_zero]
    ext g
    have := MultilinearMap.congr_fun hG' (fun k => finsuppLequivDFinsupp B (g k))
    simpa [MultilinearMap.compLinearMap_apply] using this
  have hval := MultilinearMap.congr_fun hG_zero (Function.update f i (Finsupp.single 0 1))
  have harg : (fun k => Function.update (fun _ => LinearMap.id) i K k
      (Function.update f i (Finsupp.single 0 1) k)) = Function.update f i t := by
    funext k
    by_cases hk : k = i
    · subst hk; simp [K, Finsupp.linearCombination_single]
    · simp [hk]
  simpa [G, MultilinearMap.compLinearMap_apply, harg] using hval

/-- `freeMultilinear` vanishes whenever any slot belongs to `KaehlerDifferential.kerTotal A B`. -/
private theorem freeMultilinear_eq_zero_of_mem_kerTotal (n : ℕ) (f : Fin n → (B →₀ B))
    (i : Fin n) (hf : f i ∈ KaehlerDifferential.kerTotal A B) :
    let : Module B (Symbols A B n ⧸ symbolRelations A B n) := quotModuleB A B n
    freeMultilinear A B n f = 0 := by
  let : Module B (Symbols A B n ⧸ symbolRelations A B n) := quotModuleB A B n
  have hker : KaehlerDifferential.kerTotal A B ≤
      LinearMap.ker ((freeMultilinear A B n).toLinearMap f i) := by
    rw [KaehlerDifferential.kerTotal, Submodule.span_le]
    intro t ht
    rw [SetLike.mem_coe, LinearMap.mem_ker, MultilinearMap.toLinearMap_apply]
    exact freeMultilinear_update_eq_zero_of_single A B n f i t
      (fun v => freeMultilinear_update_kerTotal_gen A B n i v ht)
  simpa using hker hf

private theorem freeMultilinear_congr (n : ℕ) {f g : Fin n → (B →₀ B)}
    (h : ∀ i, Finsupp.linearCombination B (KaehlerDifferential.D A B) (f i) =
      Finsupp.linearCombination B (KaehlerDifferential.D A B) (g i)) :
    let : Module B (Symbols A B n ⧸ symbolRelations A B n) := quotModuleB A B n
    freeMultilinear A B n f = freeMultilinear A B n g := by
  let : Module B (Symbols A B n ⧸ symbolRelations A B n) := quotModuleB A B n
  classical
  suffices ∀ s : Finset (Fin n),
      freeMultilinear A B n (s.piecewise g f) = freeMultilinear A B n f by
    simpa using (this Finset.univ).symm
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    set u := s.piecewise g f
    have huj : u j = f j := Finset.piecewise_eq_of_notMem _ _ _ hj
    rw [Finset.piecewise_insert, ← ih]
    have hdiff : g j - f j ∈ KaehlerDifferential.kerTotal A B := by
      rw [← KaehlerDifferential.kerTotal_eq, LinearMap.mem_ker, map_sub, h j, sub_self]
    have hzero := freeMultilinear_eq_zero_of_mem_kerTotal A B n
      (Function.update u j (g j - f j)) j (by simpa using hdiff)
    rw [MultilinearMap.map_update_sub, sub_eq_zero, ← huj, Function.update_eq_self] at hzero
    exact hzero

/-- The descended alternating `B`-linear map
`Ω[B⁄A] [⋀^Fin n]→ₗ[B] (Symbols A B n ⧸ symbolRelations A B n)`. -/
private def quotAlternatingMap (n : ℕ) :
    letI : Module B (Symbols A B n ⧸ symbolRelations A B n) := quotModuleB A B n
    AlternatingMap B (KaehlerDifferential A B)
      (Symbols A B n ⧸ symbolRelations A B n) (Fin n) :=
  letI : Module B (Symbols A B n ⧸ symbolRelations A B n) := quotModuleB A B n
  let q := Finsupp.linearCombination B (KaehlerDifferential.D A B)
  let hq := KaehlerDifferential.linearCombination_surjective A B
  have hlift : ∀ [DecidableEq (Fin n)] (ω : Fin n → KaehlerDifferential A B) (i : Fin n)
      (y : KaehlerDifferential A B) (t : B →₀ B), q t = y →
      freeMultilinear A B n (fun k => (hq (Function.update ω i y k)).choose) =
        freeMultilinear A B n (Function.update (fun k => (hq (ω k)).choose) i t) := by
    intro _ ω i y t ht
    refine freeMultilinear_congr A B n fun k => ?_
    rw [(hq _).choose_spec]
    by_cases hk : k = i
    · subst hk; simpa using ht.symm
    · simp [hk, (hq (ω k)).choose_spec]
  { toFun := fun ω => freeMultilinear A B n (fun k => (hq (ω k)).choose)
    map_update_add' := fun ω i x y => by
      rw [hlift ω i (x + y) ((hq x).choose + (hq y).choose)
            (by rw [map_add, (hq x).choose_spec, (hq y).choose_spec]),
          hlift ω i x (hq x).choose (hq x).choose_spec,
          hlift ω i y (hq y).choose (hq y).choose_spec,
          MultilinearMap.map_update_add]
    map_update_smul' := fun ω i b x => by
      rw [hlift ω i (b • x) (b • (hq x).choose) (by rw [map_smul, (hq x).choose_spec]),
          hlift ω i x (hq x).choose (hq x).choose_spec,
          MultilinearMap.map_update_smul]
    map_eq_zero_of_eq' := fun ω i j hω hij =>
      freeMultilinear_eq_zero_of_eq A B n (fun k => (hq (ω k)).choose)
        (by rw [hω]) hij }

/-- **The differential-symbol presentation**: for every degree `n` (including `n = 0` and in
characteristic `2`), the kernel of `symbolMap A B n` is precisely `symbolRelations A B n`. -/
theorem symbolRelations_ker (n : ℕ) :
    LinearMap.ker (symbolMap A B n) = symbolRelations A B n := by
  refine le_antisymm ?_ (symbolRelations_le_ker A B n)
  let : Module B (Symbols A B n ⧸ symbolRelations A B n) := quotModuleB A B n
  have : IsScalarTower A B (Symbols A B n ⧸ symbolRelations A B n) := quotIsScalarTower A B n
  let ψ : Forms A B n →ₗ[B] (Symbols A B n ⧸ symbolRelations A B n) :=
    exteriorPower.alternatingMapLinearEquiv (quotAlternatingMap A B n)
  have hcomp : (ψ.restrictScalars A).comp (symbolMap A B n) = (symbolRelations A B n).mkQ := by
    apply Finsupp.lhom_ext'
    rintro ⟨c, v⟩
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, ← sym_def, symbolMap_sym,
      LinearMap.coe_restrictScalars, elementary_def, map_smul, ψ,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    have hD : quotAlternatingMap A B n (KaehlerDifferential.D A B ∘ v) =
        (symbolRelations A B n).mkQ (sym A B n 1 v) := by
      have hq := KaehlerDifferential.linearCombination_surjective A B
      have hcongr := freeMultilinear_congr A B n
        (f := fun k => (hq (KaehlerDifferential.D A B (v k))).choose)
        (g := fun k => Finsupp.single (v k) 1)
        (fun k => by simp [(hq (KaehlerDifferential.D A B (v k))).choose_spec])
      simpa [quotAlternatingMap, freeMultilinear_single] using hcongr
    rw [hD, quotModuleB_smul_mkQ_sym, mul_one]
  calc
    LinearMap.ker (symbolMap A B n)
      ≤ LinearMap.ker ((ψ.restrictScalars A).comp (symbolMap A B n)) :=
        LinearMap.ker_le_ker_comp _ _
    _ = LinearMap.ker (symbolRelations A B n).mkQ := by rw [hcomp]
    _ = symbolRelations A B n := Submodule.ker_mkQ _

/-- The canonical `A`-linear isomorphism `(Symbols A B n ⧸ symbolRelations A B n) ≃ₗ[A] Forms A B n`
presenting ordinary differential `n`-forms by formal differential symbols. -/
def symbolQuotEquiv (n : ℕ) :
    (Symbols A B n ⧸ symbolRelations A B n) ≃ₗ[A] Forms A B n :=
  LinearEquiv.ofBijective
    ((symbolRelations A B n).liftQ (symbolMap A B n) (symbolRelations_ker A B n).ge)
    ⟨LinearMap.ker_eq_bot.mp (by
        rw [Submodule.ker_liftQ, symbolRelations_ker, Submodule.mkQ_map_self]),
      fun ω => let ⟨s, hs⟩ := symbolMap_surjective A B n ω; ⟨Submodule.Quotient.mk s, hs⟩⟩

@[simp]
theorem symbolQuotEquiv_mk (n : ℕ) (s : Symbols A B n) :
    symbolQuotEquiv A B n (Submodule.Quotient.mk s) = symbolMap A B n s :=
  (rfl)

@[simp]
theorem symbolQuotEquiv_symm_elementary (n : ℕ) (c : B) (v : Fin n → B) :
    (symbolQuotEquiv A B n).symm (elementary A B n c v) =
      Submodule.Quotient.mk (sym A B n c v) := by
  apply (symbolQuotEquiv A B n).injective
  simp

end Presentation

end TauCeti.DeRham
