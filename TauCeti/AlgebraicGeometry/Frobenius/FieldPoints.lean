/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import TauCeti.AlgebraicGeometry.Frobenius.GroupScheme
import TauCeti.AlgebraicGeometry.RationalPoint.FixedField
import TauCeti.FieldTheory.Finite.FrobeniusFixed

/-!
# Frobenius on field-valued points

For a scheme over a finite field `k` of cardinality `q`, the points over `k` can be recovered
inside the points over any extension field `E` as the fixed points of the `q`-power Frobenius.
We use descent of scheme points along a fixed field (`AlgHom.fromSpecOverEquivOfRangeEq`)
and the fixed-element criterion `TauCeti.FiniteField.pow_natCard_eq_self_iff_mem_range_algebraMap`.

Over an algebraic extension, the same scheme endomorphism and its iterates are induced by
Mathlib's arithmetic Frobenius automorphism. This identifies its inverse on geometric points.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] (a : ℕ)
  (ha : Nat.card k = p ^ a)
variable (E : Type u) [Field E] [Algebra k E]

/-- On the spectrum of an algebraic extension, the iterated scheme Frobenius is induced by
the corresponding power of the arithmetic Frobenius field automorphism. -/
theorem qPowerFrobeniusOver_pow_left_eq_SpecMap [Fintype k] [Algebra.IsAlgebraic k E] (n : ℕ) :
    (End.of (qPowerFrobeniusOver k a ha (Over.mk (Spec.algebraMap k E))) ^ n).asHom.left =
      Spec.map (CommRingCat.ofHom ((FiniteField.frobeniusAlgEquivOfAlgebraic k E ^ n : E ≃ₐ[k] E) :
        E →+* E)) := by
  have : CharP E p := charP_of_injective_algebraMap (algebraMap k E).injective p
  rw [qPowerFrobeniusOver_pow_asHom_left]
  refine (Spec_map_iterateFrobenius E (p := p) (a * n)).symm.trans ?_
  congr 2
  ext z
  calc
    _ = z ^ (Fintype.card k ^ n) := by
      rw [iterateFrobenius_def, ← Nat.card_eq_fintype_card, ha, pow_mul]
    _ = (FiniteField.frobeniusAlgEquivOfAlgebraic k E ^ n) z := by
      rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]

/-- An `E`-point of a `k`-scheme is defined over the finite field `k` exactly when
precomposition with the `q`-power Frobenius of `Spec E` fixes it. -/
theorem exists_toUnit_comp_eq_iff_qPowerFrobeniusOver_comp_eq
    {X : Over (Spec (.of k))} (x : Over.mk (Spec.algebraMap k E) ⟶ X) :
    (∃ y : 𝟙_ (Over (Spec (.of k))) ⟶ X, toUnit _ ≫ y = x) ↔
      qPowerFrobeniusOver k a ha _ ≫ x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [← Category.assoc, comp_toUnit]
  · intro hx
    have : CharP E p := charP_of_injective_algebraMap (algebraMap k E).injective p
    have : Finite k := Nat.finite_of_card_ne_zero (ha ▸ pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    let σ := _root_.iterateFrobenius E p a
    have hσ : Set.range (algebraMap k E) = {z | ∀ f ∈ ({σ} : Set (E →+* E)), f z = z} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq, σ, iterateFrobenius_def]
      rw [← ha, TauCeti.FiniteField.pow_natCard_eq_self_iff_mem_range_algebraMap]
    have hx' : ∀ f ∈ ({σ} : Set (E →+* E)), Spec.map (CommRingCat.ofHom f) ≫ x.left = x.left := by
      rintro f ⟨⟩
      simpa only [Over.comp_left, qPowerFrobeniusOver_left, qPowerFrobenius_eq_iterated,
        Over.mk_left, ← Spec_map_iterateFrobenius] using congrArg Over.Hom.left hx
    let y := ((Algebra.ofId k E).fromSpecOverEquivOfRangeEq {σ} hσ X.hom).symm
      ⟨x.left, Over.w x, hx'⟩
    exact ⟨Over.homMk y.val (by simpa using y.property), Over.OverMorphism.ext
      ((Algebra.ofId k E).SpecMap_comp_fromSpecOverEquivOfRangeEq_symm_apply {σ} hσ X.hom
        ⟨x.left, Over.w x, hx'⟩)⟩

end AlgebraicGeometry.Scheme
