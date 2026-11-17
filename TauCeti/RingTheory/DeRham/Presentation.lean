/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Algebra.DirectSum.Module

/-!
# The differential-symbol presentation of differential forms

For an `A`-algebra `B`, the module of differential `n`-forms is
`Ωⁿ = ⋀[B]^n Ω[B⁄A]`, regarded as an `A`-module by restriction of scalars. This file presents
`Ωⁿ` **as an `A`-module** by generators and relations. The generators are the *differential
symbols* `[c; v]`, for `c : B` and `v : Fin n → B`, which stand for the elementary forms
`c • dv₀ ∧ ⋯ ∧ dvₙ₋₁`. The relations `Rₙ` are the `A`-span of six families:

* coefficient additivity, `[c + e; v] - [c; v] - [e; v]`;
* coefficient `A`-linearity, `[a • c; v] - a • [c; v]` for `a : A`;
* slot additivity, `[c; v(i ↦ x + y)] - [c; v(i ↦ x)] - [c; v(i ↦ y)]`;
* the slot Leibniz rule, `[c; v(i ↦ x * y)] - [c * x; v(i ↦ y)] - [c * y; v(i ↦ x)]`;
* constant slots, `[c; v(i ↦ algebraMap A B a)]`;
* repeated slots, `[c; v]` when `v i = v j` for `i ≠ j`.

No `B`-linearity in the coefficient is imposed. This is the point of the presentation: the
de Rham differential `c • dv₀ ∧ ⋯ ∧ dvₙ₋₁ ↦ dc ∧ dv₀ ∧ ⋯ ∧ dvₙ₋₁` is `A`-linear but not
`B`-linear, so it descends along the quotient map `Sₙ → Sₙ ⧸ Rₙ ≃ Ωⁿ` once it kills the
relations, and these relations are checked one symbol at a time.

## Main definitions

* `TauCeti.DeRham.Forms A B n`: the `A`-module `⋀[B]^n Ω[B⁄A]`.
* `TauCeti.DeRham.Symbols A B n`: the free `A`-module `Sₙ` on pairs `(c, v)`.
* `TauCeti.DeRham.sym A c v`: the basis symbol `[c; v]`.
* `TauCeti.DeRham.elementary A c v`: the elementary form `c • dv₀ ∧ ⋯ ∧ dvₙ₋₁`.
* `TauCeti.DeRham.relationSet A B n`, `TauCeti.DeRham.symbolRelations A B n`: the six relation
  families and their `A`-span `Rₙ`.
* `TauCeti.DeRham.symbolMap A B n`: the evaluation `Sₙ →ₗ[A] Ωⁿ`, `[c; v] ↦ c • dv₀ ∧ ⋯ ∧ dvₙ₋₁`.
* `TauCeti.DeRham.symbolQuotientEquiv A B n`: the resulting `A`-linear equivalence
  `Sₙ ⧸ Rₙ ≃ₗ[A] Ωⁿ`.

## Main results

* `TauCeti.DeRham.symbolRelations_le`: a submodule containing the six relation families
  contains `Rₙ`.
* `TauCeti.DeRham.symbolMap_surjective`: the elementary forms span `Ωⁿ` over `A`.
* `TauCeti.DeRham.symbolRelations_ker`: the kernel of `symbolMap` is exactly `Rₙ`, for every
  `n`, including `n = 0` and in characteristic two.

## Implementation notes

The inclusion `ker symbolMap ≤ Rₙ` is proved by constructing a left inverse of `symbolMap`
modulo `Rₙ`. Multiplying coefficients makes each `Sₙ ⧸ Rₙ` a `B`-module, and prepending a slot,
`[c; v] ↦ [c; b, v]`, gives operators `ε_b` on `⨁ₙ Sₙ ⧸ Rₙ`. The relations make `b ↦ ε_b` an
`A`-derivation with values in the `B`-algebra of `B`-linear endomorphisms, whose induced map on
`Ω[B⁄A]` squares to zero. The universal property of the exterior algebra then yields an action
of `⋀[B] Ω[B⁄A]` on `⨁ₙ Sₙ ⧸ Rₙ`, and evaluating it at `[1; ()]` inverts `symbolMap`.

## References

* The Stacks Project, Section 10.132 (Tag 0FKF), the construction of the de Rham complex.
-/

namespace TauCeti.DeRham

open KaehlerDifferential Function

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ)

public section

/-- The `A`-module of differential `n`-forms of `B` over `A`: the `n`-th exterior power over `B`
of the Kähler differentials `Ω[B⁄A]`, with `A` acting by restriction of scalars. -/
abbrev Forms : Type _ := ⋀[B]^n Ω[B⁄A]

/-- The free `A`-module `Sₙ` on the differential symbols `[c; v]`, for `c : B` and
`v : Fin n → B`. -/
abbrev Symbols : Type _ := (B × (Fin n → B)) →₀ A

variable {B n}

/-- The basis differential symbol `[c; v]` of `Symbols A B n`, standing for the form
`c • dv₀ ∧ ⋯ ∧ dvₙ₋₁`. -/
noncomputable def sym (c : B) (v : Fin n → B) : Symbols A B n :=
  Finsupp.single (c, v) 1

/-- The elementary differential form `c • dv₀ ∧ ⋯ ∧ dvₙ₋₁` in `Forms A B n`. -/
noncomputable def elementary (c : B) (v : Fin n → B) : Forms A B n :=
  c • exteriorPower.ιMulti B n fun i => D A B (v i)

omit [CommRing B] [Algebra A B] in
/-- The basis symbol `[c; v]` is the basis vector of `Symbols A B n` at `(c, v)`. -/
theorem single_eq_sym (c : B) (v : Fin n → B) : Finsupp.single (c, v) (1 : A) = sym A c v :=
  (rfl)

/-- The defining formula of `elementary`. -/
theorem elementary_def (c : B) (v : Fin n → B) :
    elementary A c v = c • exteriorPower.ιMulti B n fun i => D A B (v i) :=
  (rfl)

omit [CommRing B] [Algebra A B] in
variable {A} in
/-- `A`-linear maps out of the symbols agree once they agree on every basis symbol `[c; v]`. -/
@[ext]
theorem symbols_hom_ext {M : Type*} [AddCommGroup M] [Module A M]
    {f g : Symbols A B n →ₗ[A] M} (h : ∀ (c : B) (v : Fin n → B), f (sym A c v) = g (sym A c v)) :
    f = g :=
  Finsupp.lhom_ext' fun p => LinearMap.ext_ring (h p.1 p.2)

variable (B n)

/-- The six families of relations among differential symbols: coefficient additivity,
coefficient `A`-linearity, slot additivity, the slot Leibniz rule, constant slots and repeated
slots. -/
noncomputable def relationSet : Set (Symbols A B n) :=
  {s | (∃ (c e : B) (v : Fin n → B), s = sym A (c + e) v - sym A c v - sym A e v) ∨
    (∃ (a : A) (c : B) (v : Fin n → B), s = sym A (a • c) v - a • sym A c v) ∨
    (∃ (c : B) (v : Fin n → B) (i : Fin n) (x y : B),
      s = sym A c (update v i (x + y)) - sym A c (update v i x) - sym A c (update v i y)) ∨
    (∃ (c : B) (v : Fin n → B) (i : Fin n) (x y : B),
      s = sym A c (update v i (x * y)) - sym A (c * x) (update v i y) -
        sym A (c * y) (update v i x)) ∨
    (∃ (c : B) (v : Fin n → B) (i : Fin n) (a : A), s = sym A c (update v i (algebraMap A B a))) ∨
    (∃ (c : B) (v : Fin n → B) (i j : Fin n), v i = v j ∧ i ≠ j ∧ s = sym A c v)}

/-- The submodule `Rₙ` of relations among differential symbols: the `A`-span of
`relationSet A B n`. -/
noncomputable def symbolRelations : Submodule A (Symbols A B n) :=
  Submodule.span A (relationSet A B n)

/-- The evaluation of differential symbols, `[c; v] ↦ c • dv₀ ∧ ⋯ ∧ dvₙ₋₁`, an `A`-linear map
`Symbols A B n →ₗ[A] Forms A B n`. -/
noncomputable def symbolMap : Symbols A B n →ₗ[A] Forms A B n :=
  Finsupp.linearCombination A fun p : B × (Fin n → B) => elementary A p.1 p.2

/-- `Rₙ` is the `A`-span of the six relation families. -/
theorem symbolRelations_eq_span : symbolRelations A B n = Submodule.span A (relationSet A B n) :=
  (rfl)

variable {A B n}

/-- `symbolMap` evaluates `[c; v]` to the elementary form `c • dv₀ ∧ ⋯ ∧ dvₙ₋₁`. -/
@[simp]
theorem symbolMap_sym (c : B) (v : Fin n → B) : symbolMap A B n (sym A c v) = elementary A c v := by
  simp [symbolMap, ← single_eq_sym]

/-- Coefficient additivity is a relation. -/
theorem symbolRelations_coeff_add (c e : B) (v : Fin n → B) :
    sym A (c + e) v - sym A c v - sym A e v ∈ symbolRelations A B n :=
  Submodule.subset_span (Or.inl ⟨c, e, v, rfl⟩)

/-- Coefficient `A`-linearity is a relation. -/
theorem symbolRelations_coeff_smul (a : A) (c : B) (v : Fin n → B) :
    sym A (a • c) v - a • sym A c v ∈ symbolRelations A B n :=
  Submodule.subset_span (Or.inr (Or.inl ⟨a, c, v, rfl⟩))

/-- Slot additivity is a relation. -/
theorem symbolRelations_slot_add (c : B) (v : Fin n → B) (i : Fin n) (x y : B) :
    sym A c (update v i (x + y)) - sym A c (update v i x) - sym A c (update v i y) ∈
      symbolRelations A B n :=
  Submodule.subset_span (Or.inr (Or.inr (Or.inl ⟨c, v, i, x, y, rfl⟩)))

/-- The slot Leibniz rule is a relation, in every slot. -/
theorem symbolRelations_slot_mul (c : B) (v : Fin n → B) (i : Fin n) (x y : B) :
    sym A c (update v i (x * y)) - sym A (c * x) (update v i y) - sym A (c * y) (update v i x) ∈
      symbolRelations A B n :=
  Submodule.subset_span (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, v, i, x, y, rfl⟩))))

/-- A slot filled with an element of `A` gives a relation. -/
theorem symbolRelations_slot_algebraMap (c : B) (v : Fin n → B) (i : Fin n) (a : A) :
    sym A c (update v i (algebraMap A B a)) ∈ symbolRelations A B n :=
  Submodule.subset_span (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, v, i, a, rfl⟩)))))

/-- A symbol with two equal slots is a relation. -/
theorem symbolRelations_of_eq (c : B) {v : Fin n → B} {i j : Fin n} (hv : v i = v j)
    (hij : i ≠ j) : sym A c v ∈ symbolRelations A B n :=
  Submodule.subset_span (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨c, v, i, j, hv, hij, rfl⟩)))))

/-- **Elimination for the relations among symbols.** A submodule of `Sₙ` contains `Rₙ` once it
contains each of the six relation families. -/
theorem symbolRelations_le {p : Submodule A (Symbols A B n)}
    (coeff_add : ∀ (c e : B) (v : Fin n → B), sym A (c + e) v - sym A c v - sym A e v ∈ p)
    (coeff_smul : ∀ (a : A) (c : B) (v : Fin n → B), sym A (a • c) v - a • sym A c v ∈ p)
    (slot_add : ∀ (c : B) (v : Fin n → B) (i : Fin n) (x y : B),
      sym A c (update v i (x + y)) - sym A c (update v i x) - sym A c (update v i y) ∈ p)
    (slot_mul : ∀ (c : B) (v : Fin n → B) (i : Fin n) (x y : B),
      sym A c (update v i (x * y)) - sym A (c * x) (update v i y) -
        sym A (c * y) (update v i x) ∈ p)
    (slot_algebraMap : ∀ (c : B) (v : Fin n → B) (i : Fin n) (a : A),
      sym A c (update v i (algebraMap A B a)) ∈ p)
    (of_eq : ∀ (c : B) (v : Fin n → B) (i j : Fin n), v i = v j → i ≠ j → sym A c v ∈ p) :
    symbolRelations A B n ≤ p := by
  rw [symbolRelations_eq_span, Submodule.span_le]
  rintro s (⟨c, e, v, rfl⟩ | ⟨a, c, v, rfl⟩ | ⟨c, v, i, x, y, rfl⟩ | ⟨c, v, i, x, y, rfl⟩ |
      ⟨c, v, i, a, rfl⟩ | ⟨c, v, i, j, hv, hij, rfl⟩)
  exacts [coeff_add c e v, coeff_smul a c v, slot_add c v i x y, slot_mul c v i x y,
    slot_algebraMap c v i a, of_eq c v i j hv hij]

/-- A symbol with zero coefficient is a relation. -/
theorem symbolRelations_coeff_zero (v : Fin n → B) : sym A 0 v ∈ symbolRelations A B n := by
  simpa using neg_mem (symbolRelations_coeff_add (A := A) (0 : B) 0 v)

/-- The evaluation of symbols kills every relation. -/
theorem symbolRelations_le_ker : symbolRelations A B n ≤ LinearMap.ker (symbolMap A B n) := by
  refine symbolRelations_le (fun c e v => ?_) (fun a c v => ?_) (fun c v i x y => ?_)
    (fun c v i x y => ?_) (fun c v i a => ?_) (fun c v i j hv hij => ?_) <;>
    simp only [LinearMap.mem_ker, map_sub, map_smul, symbolMap_sym, elementary_def]
  · rw [add_smul, sub_sub, sub_self]
  · rw [smul_assoc, sub_self]
  · simp only [apply_update (fun _ => D A B), map_add, AlternatingMap.map_update_add, smul_add,
      sub_sub, sub_self]
  · simp only [apply_update (fun _ => D A B), Derivation.leibniz, AlternatingMap.map_update_add,
      AlternatingMap.map_update_smul, smul_add, mul_smul, sub_sub, sub_self]
  · simp [apply_update (fun _ => D A B)]
  · rw [AlternatingMap.map_eq_zero_of_eq _ (fun k => D A B (v k)) (congrArg (D A B) hv) hij,
      smul_zero]

variable (A B n)

/-- The elementary forms `c • dv₀ ∧ ⋯ ∧ dvₙ₋₁` span `Forms A B n` as an `A`-module, so the
evaluation of differential symbols is surjective. -/
theorem symbolMap_surjective : Surjective (symbolMap A B n) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  have hspan := exteriorPower.ιMulti_span_of_span B n _ (span_range_derivation A B)
  rw [← Submodule.restrictScalars_eq_top_iff A, ← Submodule.span_smul_of_span_eq_top
    (Submodule.span_univ (R := A) (M := B))] at hspan
  rw [← hspan, Submodule.span_le]
  rintro _ ⟨c, -, _, ⟨w, hw, rfl⟩, rfl⟩
  choose v hv using fun i => hw ⟨i, rfl⟩
  refine ⟨sym A c v, ?_⟩
  simp only [symbolMap_sym, elementary_def, hv]

end

/-! ### The inverse of the evaluation of symbols -/

/-- Multiplication of the coefficients of symbols by `b : B`. -/
private noncomputable def coeffMul (b : B) : Symbols A B n →ₗ[A] Symbols A B n :=
  Finsupp.lmapDomain A A fun p => (b * p.1, p.2)

variable {A B n}

omit [Algebra A B] in
private lemma coeffMul_sym (b c : B) (v : Fin n → B) :
    coeffMul A B n b (sym A c v) = sym A (b * c) v := by
  rw [← single_eq_sym, ← single_eq_sym]
  simp [coeffMul]

private lemma symbolRelations_le_comap_coeffMul (b : B) :
    symbolRelations A B n ≤ (symbolRelations A B n).comap (coeffMul A B n b) := by
  refine symbolRelations_le (fun c e v => ?_) (fun a c v => ?_) (fun c v i x y => ?_)
    (fun c v i x y => ?_) (fun c v i a => ?_) (fun c v i j hv hij => ?_) <;>
    simp only [Submodule.mem_comap, map_sub, map_smul, coeffMul_sym]
  · simpa only [mul_add] using symbolRelations_coeff_add (b * c) (b * e) v
  · simpa only [mul_smul_comm] using symbolRelations_coeff_smul a (b * c) v
  · exact symbolRelations_slot_add (b * c) v i x y
  · simpa only [mul_assoc] using symbolRelations_slot_mul (b * c) v i x y
  · exact symbolRelations_slot_algebraMap (b * c) v i a
  · exact symbolRelations_of_eq (b * c) hv hij

variable (A B n) in
/-- The quotient `Sₙ ⧸ Rₙ`, as a type synonym carrying the `B`-module structure given by
multiplication of coefficients. -/
private abbrev CoeffQuot : Type _ := Symbols A B n ⧸ symbolRelations A B n

/- Direct instances, so that they are found for the family `fun n => CoeffQuot A B n`. -/
private noncomputable instance : AddCommGroup (CoeffQuot A B n) := Submodule.Quotient.addCommGroup _

private noncomputable instance : Module A (CoeffQuot A B n) := Submodule.Quotient.module _

variable (A B n) in
/-- The quotient map `Sₙ → Sₙ ⧸ Rₙ` into the synonym `CoeffQuot`. -/
private noncomputable def mkC : Symbols A B n →ₗ[A] CoeffQuot A B n :=
  (symbolRelations A B n).mkQ

private lemma mkC_eq_zero_iff (s : Symbols A B n) :
    mkC A B n s = 0 ↔ s ∈ symbolRelations A B n :=
  Submodule.Quotient.mk_eq_zero _

private lemma mkC_sym_coeff_add (c e : B) (v : Fin n → B) :
    mkC A B n (sym A (c + e) v) = mkC A B n (sym A c v) + mkC A B n (sym A e v) := by
  rw [← sub_eq_zero, ← map_add, ← map_sub, mkC_eq_zero_iff, ← sub_sub]
  exact symbolRelations_coeff_add c e v

private lemma mkC_sym_coeff_zero (v : Fin n → B) : mkC A B n (sym A (0 : B) v) = 0 :=
  (mkC_eq_zero_iff _).2 (symbolRelations_coeff_zero v)

/-- `A`-linear maps out of `Sₙ ⧸ Rₙ` agree once they agree on the classes of the symbols. -/
private lemma coeffQuot_hom_ext {M : Type*} [AddCommGroup M] [Module A M]
    {f g : CoeffQuot A B n →ₗ[A] M}
    (h : ∀ (c : B) (v : Fin n → B), f (mkC A B n (sym A c v)) = g (mkC A B n (sym A c v))) :
    f = g :=
  Submodule.linearMap_qext _ <| symbols_hom_ext h

variable (A B n) in
/-- Multiplication of coefficients, as a ring homomorphism `B →+* Module.End A (Sₙ ⧸ Rₙ)`. -/
private noncomputable def coeffAction : B →+* Module.End A (CoeffQuot A B n) where
  toFun b := (symbolRelations A B n).mapQ _ (coeffMul A B n b)
    (symbolRelations_le_comap_coeffMul b)
  map_one' := coeffQuot_hom_ext fun c v => by
    simp [mkC, coeffMul_sym]
  map_mul' b b' := coeffQuot_hom_ext fun c v => by
    simp [mkC, coeffMul_sym, mul_assoc]
  map_zero' := coeffQuot_hom_ext fun c v => by
    simpa [mkC, coeffMul_sym] using mkC_sym_coeff_zero (A := A) v
  map_add' b b' := coeffQuot_hom_ext fun c v => by
    simpa [mkC, coeffMul_sym, add_mul] using mkC_sym_coeff_add (A := A) (b * c) (b' * c) v

private lemma coeffAction_mkC (b : B) (s : Symbols A B n) :
    coeffAction A B n b (mkC A B n s) = mkC A B n (coeffMul A B n b s) :=
  rfl

/-- The `B`-module structure on `Sₙ ⧸ Rₙ` given by multiplication of coefficients. It is only a
local instance, so that it cannot clash with the `A`-module structure when `B = A`. -/
@[instance_reducible]
private noncomputable def coeffModule : Module B (CoeffQuot A B n) :=
  Module.compHom (CoeffQuot A B n) (coeffAction A B n)

attribute [local instance] coeffModule

private lemma smul_mkC_sym (b c : B) (v : Fin n → B) :
    b • mkC A B n (sym A c v) = mkC A B n (sym A (b * c) v) := by
  rw [← coeffMul_sym, ← coeffAction_mkC]
  rfl

private lemma coeffAction_algebraMap (a : A) :
    coeffAction A B n (algebraMap A B a) = a • 1 :=
  coeffQuot_hom_ext fun c v => by
    rw [coeffAction_mkC, coeffMul_sym, LinearMap.smul_apply, Module.End.one_eq_id,
      LinearMap.id_apply, ← Algebra.smul_def, ← map_smul, ← sub_eq_zero, ← map_sub,
      mkC_eq_zero_iff]
    exact symbolRelations_coeff_smul a c v

private lemma coeffQuot_isScalarTower : IsScalarTower A B (CoeffQuot A B n) :=
  IsScalarTower.of_algebraMap_smul fun a x => by
    -- `algebraMap A B a • x` unfolds to `coeffAction A B n (algebraMap A B a) x`.
    change coeffAction A B n (algebraMap A B a) x = a • x
    rw [coeffAction_algebraMap]
    rfl

attribute [local instance] coeffQuot_isScalarTower

/-- `B`-linear maps out of `Sₙ ⧸ Rₙ` agree once they agree on the classes of the symbols. -/
private lemma coeffQuot_hom_ext_B {M : Type*} [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] {f g : CoeffQuot A B n →ₗ[B] M}
    (h : ∀ (c : B) (v : Fin n → B), f (mkC A B n (sym A c v)) = g (mkC A B n (sym A c v))) :
    f = g :=
  LinearMap.restrictScalars_injective A (coeffQuot_hom_ext h)

/-- Prepending the slot `b` to symbols, `[c; v] ↦ [c; b, v]`. -/
private noncomputable def consSlot (b : B) : Symbols A B n →ₗ[A] Symbols A B (n + 1) :=
  Finsupp.lmapDomain A A fun p => (p.1, Fin.cons b p.2)

omit [CommRing B] [Algebra A B] in
private lemma consSlot_sym (b c : B) (v : Fin n → B) :
    consSlot b (sym A c v) = sym A c (Fin.cons b v) := by
  rw [← single_eq_sym, ← single_eq_sym]
  simp [consSlot]

private lemma symbolRelations_le_comap_consSlot (b : B) :
    symbolRelations A B n ≤ (symbolRelations A B (n + 1)).comap (consSlot b) := by
  refine symbolRelations_le (fun c e v => ?_) (fun a c v => ?_) (fun c v i x y => ?_)
    (fun c v i x y => ?_) (fun c v i a => ?_) (fun c v i j hv hij => ?_) <;>
    simp only [Submodule.mem_comap, map_sub, map_smul, consSlot_sym,
      Fin.cons_update]
  · exact symbolRelations_coeff_add c e _
  · exact symbolRelations_coeff_smul a c _
  · exact symbolRelations_slot_add c _ i.succ x y
  · exact symbolRelations_slot_mul c _ i.succ x y
  · exact symbolRelations_slot_algebraMap c _ i.succ a
  · exact symbolRelations_of_eq c (i := i.succ) (j := j.succ) (by simpa using hv)
      (Fin.succ_injective _ |>.ne hij)

private lemma mapQ_mkC (b : B) (s : Symbols A B n) :
    (symbolRelations A B n).mapQ (symbolRelations A B (n + 1)) (consSlot b)
      (symbolRelations_le_comap_consSlot b) (mkC A B n s) = mkC A B (n + 1) (consSlot b s) :=
  rfl

/-- Prepending the slot `b`, as a `B`-linear map `Sₙ ⧸ Rₙ → Sₙ₊₁ ⧸ Rₙ₊₁`. -/
private noncomputable def wedgeD (b : B) : CoeffQuot A B n →ₗ[B] CoeffQuot A B (n + 1) where
  toFun := (symbolRelations A B n).mapQ (symbolRelations A B (n + 1)) (consSlot b)
    (symbolRelations_le_comap_consSlot b)
  map_add' := map_add _
  map_smul' b' x := by
    refine LinearMap.congr_fun (f := ((symbolRelations A B n).mapQ (symbolRelations A B (n + 1))
      (consSlot b) (symbolRelations_le_comap_consSlot b)).comp (coeffAction A B n b'))
      (g := (coeffAction A B (n + 1) b').comp ((symbolRelations A B n).mapQ
        (symbolRelations A B (n + 1)) (consSlot b) (symbolRelations_le_comap_consSlot b)))
      (coeffQuot_hom_ext fun c v => ?_) x
    simp only [LinearMap.comp_apply, coeffAction_mkC, coeffMul_sym, mapQ_mkC, consSlot_sym]

private lemma wedgeD_mkC_sym (b c : B) (v : Fin n → B) :
    wedgeD b (mkC A B n (sym A c v)) = mkC A B (n + 1) (sym A c (Fin.cons b v)) := by
  rw [← consSlot_sym]
  rfl

private lemma mkC_sym_cons_add (c x y : B) (w : Fin n → B) :
    mkC A B (n + 1) (sym A c (Fin.cons (x + y) w)) =
      mkC A B (n + 1) (sym A c (Fin.cons x w)) + mkC A B (n + 1) (sym A c (Fin.cons y w)) := by
  rw [← sub_eq_zero, ← map_add, ← map_sub, mkC_eq_zero_iff, ← sub_sub]
  simpa only [Fin.update_cons_zero] using
    symbolRelations_slot_add (A := A) c (Fin.cons 0 w) 0 x y

private lemma wedgeD_add (x y : B) :
    wedgeD (A := A) (n := n) (x + y) = wedgeD x + wedgeD y :=
  coeffQuot_hom_ext_B fun c v => by
    rw [LinearMap.add_apply, wedgeD_mkC_sym, wedgeD_mkC_sym, wedgeD_mkC_sym, mkC_sym_cons_add]

private lemma wedgeD_mul (x y : B) :
    wedgeD (A := A) (n := n) (x * y) = x • wedgeD y + y • wedgeD x :=
  coeffQuot_hom_ext_B fun c v => by
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, wedgeD_mkC_sym,
      wedgeD_mkC_sym, wedgeD_mkC_sym, smul_mkC_sym, smul_mkC_sym, ← sub_eq_zero, ← map_add,
      ← map_sub, mkC_eq_zero_iff, ← sub_sub, mul_comm x c, mul_comm y c]
    simpa only [Fin.update_cons_zero] using
      symbolRelations_slot_mul (A := A) c (Fin.cons 0 v) 0 x y

private lemma wedgeD_algebraMap (a : A) : wedgeD (A := A) (n := n) (algebraMap A B a) = 0 :=
  coeffQuot_hom_ext_B fun c v => by
    rw [wedgeD_mkC_sym, LinearMap.zero_apply, mkC_eq_zero_iff]
    simpa only [Fin.update_cons_zero] using
      symbolRelations_slot_algebraMap (A := A) c (Fin.cons 0 v) 0 a

private lemma wedgeD_wedgeD_self (x : B) (m : CoeffQuot A B n) : wedgeD x (wedgeD x m) = 0 := by
  refine LinearMap.congr_fun (f := (wedgeD (A := A) x).comp (wedgeD x)) (g := 0)
    (coeffQuot_hom_ext_B fun c v => ?_) m
  rw [LinearMap.comp_apply, wedgeD_mkC_sym, wedgeD_mkC_sym, LinearMap.zero_apply,
    mkC_eq_zero_iff]
  exact symbolRelations_of_eq c (i := 0) (j := 1) rfl Fin.zero_ne_one

variable (A B) in
/-- The direct sum `⨁ₙ Sₙ ⧸ Rₙ`. -/
private abbrev Tot : Type _ := DirectSum ℕ (CoeffQuot A B)

variable (A) in
/-- Prepending the slot `b` on `⨁ₙ Sₙ ⧸ Rₙ`. -/
private noncomputable def wedgeTot (b : B) : Module.End B (Tot A B) :=
  DirectSum.toModule B ℕ (Tot A B) fun n =>
    (DirectSum.lof B ℕ (CoeffQuot A B) (n + 1)).comp (wedgeD (n := n) b)

private lemma wedgeTot_lof (b : B) (m : CoeffQuot A B n) :
    wedgeTot A b (DirectSum.lof B ℕ (CoeffQuot A B) n m) =
      DirectSum.lof B ℕ (CoeffQuot A B) (n + 1) (wedgeD b m) := by
  simp [wedgeTot]

private lemma wedgeTot_add (x y : B) : wedgeTot A (x + y) = wedgeTot A x + wedgeTot A y :=
  DirectSum.linearMap_ext B fun n => LinearMap.ext fun m => by
    simp [wedgeTot_lof, wedgeD_add]

private lemma wedgeTot_mul (x y : B) :
    wedgeTot A (x * y) = x • wedgeTot A y + y • wedgeTot A x :=
  DirectSum.linearMap_ext B fun n => LinearMap.ext fun m => by
    simp [wedgeTot_lof, wedgeD_mul]

private lemma wedgeTot_algebraMap (a : A) : wedgeTot A (algebraMap A B a) = 0 :=
  DirectSum.linearMap_ext B fun n => LinearMap.ext fun m => by
    simp [wedgeTot_lof, wedgeD_algebraMap]

private lemma wedgeTot_mul_self (x : B) : wedgeTot A x * wedgeTot A x = 0 :=
  DirectSum.linearMap_ext B fun n => LinearMap.ext fun m => by
    simp [Module.End.mul_eq_comp, wedgeTot_lof, wedgeD_wedgeD_self]

private lemma wedgeTot_anticomm (x y : B) :
    wedgeTot A x * wedgeTot A y + wedgeTot A y * wedgeTot A x = 0 := by
  have h := wedgeTot_mul_self (A := A) (x + y)
  rw [wedgeTot_add, add_mul, mul_add, mul_add, wedgeTot_mul_self, wedgeTot_mul_self, zero_add,
    add_zero] at h
  exact h

variable (A B) in
/-- Prepending a slot is an `A`-derivation of `B` into the endomorphisms of `⨁ₙ Sₙ ⧸ Rₙ`. -/
private noncomputable def wedgeDerivation : Derivation A B (Module.End B (Tot A B)) where
  toFun := wedgeTot A
  map_add' := wedgeTot_add
  map_smul' a b := by
    rw [RingHom.id_apply, Algebra.smul_def, wedgeTot_mul, wedgeTot_algebraMap, smul_zero,
      add_zero, algebraMap_smul]
  map_one_eq_zero' := by simpa using wedgeTot_algebraMap (A := A) (B := B) 1
  leibniz' := wedgeTot_mul

variable (A B) in
/-- The `B`-linear map `Ω[B⁄A] → Module.End B (⨁ₙ Sₙ ⧸ Rₙ)`, `db ↦ (prepend the slot b)`. -/
private noncomputable def wedgeOmega : Ω[B⁄A] →ₗ[B] Module.End B (Tot A B) :=
  @Derivation.liftKaehlerDifferential A B _ _ _ (Module.End B (Tot A B)) _ _ _ _
    (wedgeDerivation A B)

private lemma wedgeDerivation_apply (b : B) : wedgeDerivation A B b = wedgeTot A b :=
  rfl

private lemma wedgeOmega_D (b : B) : wedgeOmega A B (D A B b) = wedgeTot A b := by
  rw [wedgeOmega, Derivation.liftKaehlerDifferential_comp_D, wedgeDerivation_apply]

private lemma wedgeOmega_anticomm (ω ω' : Ω[B⁄A]) :
    wedgeOmega A B ω * wedgeOmega A B ω' + wedgeOmega A B ω' * wedgeOmega A B ω = 0 := by
  have h₁ (b : B) (ω' : Ω[B⁄A]) :
      wedgeOmega A B (D A B b) * wedgeOmega A B ω' +
        wedgeOmega A B ω' * wedgeOmega A B (D A B b) = 0 := by
    refine LinearMap.congr_fun (f := (LinearMap.mulLeft B (wedgeOmega A B (D A B b)) +
      LinearMap.mulRight B (wedgeOmega A B (D A B b))) ∘ₗ wedgeOmega A B) (g := 0)
      (LinearMap.ext_on_range (span_range_derivation A B) fun b' => ?_) ω'
    simp [wedgeOmega_D, wedgeTot_anticomm]
  refine LinearMap.congr_fun (f := (LinearMap.mulRight B (wedgeOmega A B ω') +
    LinearMap.mulLeft B (wedgeOmega A B ω')) ∘ₗ wedgeOmega A B) (g := 0)
    (LinearMap.ext_on_range (span_range_derivation A B) fun b => ?_) ω
  simpa using h₁ b ω'

private lemma wedgeOmega_mul_self (ω : Ω[B⁄A]) : wedgeOmega A B ω * wedgeOmega A B ω = 0 := by
  have hω : ω ∈ Submodule.span B (Set.range (D A B)) := by
    rw [span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨b, rfl⟩ := h
    rw [wedgeOmega_D, wedgeTot_mul_self]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, add_mul, mul_add, mul_add, hx, hy, zero_add, add_zero, wedgeOmega_anticomm]
  | smul b x _ hx => rw [map_smul, smul_mul_smul_comm, hx, smul_zero]

variable (A B) in
/-- The action of the exterior algebra `⋀[B] Ω[B⁄A]` on `⨁ₙ Sₙ ⧸ Rₙ` by prepending slots. -/
private noncomputable def wedgeAction : ExteriorAlgebra B Ω[B⁄A] →ₐ[B] Module.End B (Tot A B) :=
  ExteriorAlgebra.lift B ⟨wedgeOmega A B, wedgeOmega_mul_self⟩

variable (A B) in
/-- The class of the unit symbol `[1; ()]` in degree zero. -/
private noncomputable def unitSymbol : Tot A B :=
  DirectSum.lof B ℕ (CoeffQuot A B) 0 (mkC A B 0 (sym A 1 ![]))

private lemma wedgeAction_ιMulti (v : Fin n → B) :
    wedgeAction A B (ExteriorAlgebra.ιMulti B n fun i => D A B (v i)) (unitSymbol A B) =
      DirectSum.lof B ℕ (CoeffQuot A B) n (mkC A B n (sym A 1 v)) := by
  induction n with
  | zero =>
    rw [ExteriorAlgebra.ιMulti_zero_apply, map_one, Module.End.one_eq_id, LinearMap.id_apply,
      Subsingleton.elim v ![]]
    rfl
  | succ n ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul, Module.End.mul_eq_comp, LinearMap.comp_apply,
      wedgeAction, ExteriorAlgebra.lift_ι_apply, ← wedgeAction]
    erw [ih (Fin.tail v)]
    rw [wedgeOmega_D, wedgeTot_lof, wedgeD_mkC_sym, Fin.cons_self_tail]

variable (A B n) in
/-- The left inverse of `symbolMap` modulo `Rₙ`, as a `B`-linear map `Ωⁿ → Sₙ ⧸ Rₙ`. -/
private noncomputable def invMap : Forms A B n →ₗ[B] CoeffQuot A B n :=
  DirectSum.component B ℕ (CoeffQuot A B) n ∘ₗ LinearMap.applyₗ (unitSymbol A B) ∘ₗ
    (wedgeAction A B).toLinearMap ∘ₗ (⋀[B]^n Ω[B⁄A]).subtype

private lemma invMap_symbolMap (s : Symbols A B n) :
    invMap A B n (symbolMap A B n s) = mkC A B n s := by
  refine LinearMap.congr_fun (f := (invMap A B n).restrictScalars A ∘ₗ symbolMap A B n)
    (g := mkC A B n) (symbols_hom_ext fun c v => ?_) s
  rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, symbolMap_sym, elementary_def,
    map_smul]
  simp only [invMap, LinearMap.comp_apply, Submodule.subtype_apply,
    exteriorPower.ιMulti_apply_coe, AlgHom.toLinearMap_apply, LinearMap.applyₗ_apply_apply,
    wedgeAction_ιMulti, DirectSum.component.lof_self, smul_mkC_sym, mul_one]

variable (A B n)

/-- **The differential-symbol presentation of differential forms.** The kernel of the evaluation
`[c; v] ↦ c • dv₀ ∧ ⋯ ∧ dvₙ₋₁` of differential symbols is exactly the span `Rₙ` of the six
relation families, for every `n`. -/
public theorem symbolRelations_ker : LinearMap.ker (symbolMap A B n) = symbolRelations A B n := by
  refine le_antisymm (fun s hs => ?_) symbolRelations_le_ker
  rw [← mkC_eq_zero_iff, ← invMap_symbolMap, LinearMap.mem_ker.1 hs, map_zero]

/-- The `A`-linear equivalence `Sₙ ⧸ Rₙ ≃ₗ[A] Ωⁿ` induced by the evaluation of differential
symbols. -/
public noncomputable def symbolQuotientEquiv :
    (Symbols A B n ⧸ symbolRelations A B n) ≃ₗ[A] Forms A B n :=
  (Submodule.quotEquivOfEq _ _ (symbolRelations_ker A B n).symm).trans
    ((symbolMap A B n).quotKerEquivOfSurjective (symbolMap_surjective A B n))

variable {A B n}

/-- `symbolQuotientEquiv` sends the class of a symbol to its evaluation. -/
@[simp]
public theorem symbolQuotientEquiv_mk (s : Symbols A B n) :
    symbolQuotientEquiv A B n (Submodule.Quotient.mk s) = symbolMap A B n s := by
  simp [symbolQuotientEquiv]

end TauCeti.DeRham
