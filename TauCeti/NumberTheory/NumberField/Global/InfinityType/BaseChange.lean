/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import TauCeti.NumberTheory.NumberField.Global.InfinityType.IdentityComponent

import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Base change of infinity types

Let `L / K` be an extension of fields. A character of `K_vˣ` at an infinite place `v` of `K`
pulls back along the local norm `N_{L_w/K_v}` to a character of `L_wˣ` at each place `w ∣ v`.
This file records the effect on archimedean parameters, for each of the three carriers of
infinity types.

* `ContinuousInfinityType.baseChange`: at a real place `w` over the real place `v` the parameters
  `(s_v, ε_v)` are unchanged. At a complex place `w` over a real place `v`, the norm is
  `z ↦ |z|²`, so the modulus exponent doubles to `2 s_v` and the angular frequency is `0`. At a
  complex place `w` over a complex place `v`, the modulus exponent `s_v` is unchanged and the
  angular frequency is `k_v` or `-k_v`, according as `w.embedding` or its conjugate extends
  `v.embedding`.
* `AlgebraicInfinityType.baseChange`: the exponent at an embedding `τ : L → ℂ` is the exponent
  at its restriction `τ|_K`.
* `FiniteOrderInfinityType.baseChange`: the sign at a real place of `L` is the sign at the real
  place below it.

The algebraic and finite-order base changes are compatible with the passage to continuous
parameters. Hence base change preserves algebraicity on the identity component.

## Main definitions

* `TauCeti.GlobalNumberFields.ContinuousInfinityType.baseChange`,
  `TauCeti.GlobalNumberFields.AlgebraicInfinityType.baseChange`,
  `TauCeti.GlobalNumberFields.FiniteOrderInfinityType.baseChange`: base change of infinity
  types from `K` to `L`.

## Main results

* `TauCeti.GlobalNumberFields.AlgebraicInfinityType.toContinuous_baseChange`,
  `TauCeti.GlobalNumberFields.FiniteOrderInfinityType.toContinuous_baseChange`: base change
  commutes with the passage to continuous parameters.
* `TauCeti.GlobalNumberFields.ContinuousInfinityType.IsAlgebraicOnIdentityComponent.baseChange`:
  base change preserves algebraicity on the identity component.

## References

* A. Weil, *Basic Number Theory*, Chapter VII, §3.
-/

public section
noncomputable section

open NumberField NumberField.InfinitePlace NumberField.ComplexEmbedding

namespace TauCeti.GlobalNumberFields

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

namespace ContinuousInfinityType

variable (L) in
open scoped Classical in
/-- **Base change of continuous infinity types** from `K` to `L`: the archimedean parameters of
the pullback of a character along the local norms. At a complex place `w` of `L` over a real
place the modulus exponent doubles and the angular frequency vanishes. At a complex place over a
complex place the angular frequency changes sign exactly when the conjugate of `w.embedding`,
rather than `w.embedding`, extends the embedding of the place below. -/
def baseChange : ContinuousInfinityType K →+ ContinuousInfinityType L where
  toFun t :=
    { realExponent := fun w ↦ t.realExponent ⟨w.1.comap (algebraMap K L), w.2.comap _⟩
      realParity := fun w ↦ t.realParity ⟨w.1.comap (algebraMap K L), w.2.comap _⟩
      complexExponent := fun w ↦
        if h : (w.1.comap (algebraMap K L)).IsReal then 2 * t.realExponent ⟨_, h⟩
        else t.complexExponent ⟨_, not_isReal_iff_isComplex.mp h⟩
      complexAngularFrequency := fun w ↦
        if h : (w.1.comap (algebraMap K L)).IsReal then 0
        else if w.1.embedding.comp (algebraMap K L) = (w.1.comap (algebraMap K L)).embedding
          then t.complexAngularFrequency ⟨_, not_isReal_iff_isComplex.mp h⟩
          else -t.complexAngularFrequency ⟨_, not_isReal_iff_isComplex.mp h⟩ }
  map_zero' := by
    ext w <;> simp
  map_add' t u := by
    ext w
    · rfl
    · rfl
    · simp only [add_complexExponent, add_realExponent, Pi.add_apply]
      split_ifs <;> ring
    · simp only [add_complexAngularFrequency, Pi.add_apply]
      split_ifs <;> ring

/-- At a real place, the base-changed modulus exponent is the modulus exponent at the real place
below. -/
@[simp]
theorem baseChange_realExponent (t : ContinuousInfinityType K)
    (w : {w : InfinitePlace L // w.IsReal}) :
    (baseChange L t).realExponent w = t.realExponent ⟨w.1.comap (algebraMap K L), w.2.comap _⟩ :=
  (rfl)

/-- At a real place, the base-changed parity is the parity at the real place below. -/
@[simp]
theorem baseChange_realParity (t : ContinuousInfinityType K)
    (w : {w : InfinitePlace L // w.IsReal}) :
    (baseChange L t).realParity w = t.realParity ⟨w.1.comap (algebraMap K L), w.2.comap _⟩ :=
  (rfl)

/-- At a complex place over a real place, the base-changed modulus exponent is twice the modulus
exponent below. -/
theorem baseChange_complexExponent_of_isReal (t : ContinuousInfinityType K)
    (w : {w : InfinitePlace L // w.IsComplex}) (h : (w.1.comap (algebraMap K L)).IsReal) :
    (baseChange L t).complexExponent w = 2 * t.realExponent ⟨_, h⟩ := by
  simp [baseChange, h]

/-- At a complex place over a complex place, the base-changed modulus exponent is the modulus
exponent below. -/
theorem baseChange_complexExponent_of_isComplex (t : ContinuousInfinityType K)
    (w : {w : InfinitePlace L // w.IsComplex}) (h : (w.1.comap (algebraMap K L)).IsComplex) :
    (baseChange L t).complexExponent w = t.complexExponent ⟨_, h⟩ := by
  simp [baseChange, not_isReal_iff_isComplex.mpr h]

/-- At a complex place over a real place, the base-changed angular frequency is zero. -/
theorem baseChange_complexAngularFrequency_of_isReal (t : ContinuousInfinityType K)
    (w : {w : InfinitePlace L // w.IsComplex}) (h : (w.1.comap (algebraMap K L)).IsReal) :
    (baseChange L t).complexAngularFrequency w = 0 := by
  simp [baseChange, h]

/-- At a complex place `w` over a complex place whose embedding is extended by `w.embedding`,
the base-changed angular frequency is the angular frequency below. -/
theorem baseChange_complexAngularFrequency_of_comp_eq (t : ContinuousInfinityType K)
    (w : {w : InfinitePlace L // w.IsComplex}) (h : (w.1.comap (algebraMap K L)).IsComplex)
    (he : w.1.embedding.comp (algebraMap K L) = (w.1.comap (algebraMap K L)).embedding) :
    (baseChange L t).complexAngularFrequency w = t.complexAngularFrequency ⟨_, h⟩ := by
  simp [baseChange, not_isReal_iff_isComplex.mpr h, he]

/-- At a complex place `w` over a complex place whose embedding is extended by the conjugate of
`w.embedding`, the base-changed angular frequency is the negated angular frequency below. -/
theorem baseChange_complexAngularFrequency_of_conjugate_comp_eq (t : ContinuousInfinityType K)
    (w : {w : InfinitePlace L // w.IsComplex}) (h : (w.1.comap (algebraMap K L)).IsComplex)
    (he : (conjugate w.1.embedding).comp (algebraMap K L) =
      (w.1.comap (algebraMap K L)).embedding) :
    (baseChange L t).complexAngularFrequency w = -t.complexAngularFrequency ⟨_, h⟩ := by
  -- Both `w.embedding` and its conjugate cannot extend the embedding of a complex place.
  have hne : w.1.embedding.comp (algebraMap K L) ≠ (w.1.comap (algebraMap K L)).embedding := by
    intro he'
    refine (isComplex_iff.mp h) (ComplexEmbedding.isReal_iff.mpr ?_)
    rw [← he', ← conjugate_comp, he, he']
  simp [baseChange, not_isReal_iff_isComplex.mpr h, hne]

end ContinuousInfinityType

namespace AlgebraicInfinityType

variable (L) in
/-- **Base change of algebraic infinity types** from `K` to `L`: the exponent at an embedding
`τ : L → ℂ` is the exponent at its restriction to `K`. -/
def baseChange : AlgebraicInfinityType K →+ AlgebraicInfinityType L :=
  (LinearMap.funLeft ℤ ℤ fun τ : L →+* ℂ ↦ τ.comp (algebraMap K L)).toAddMonoidHom

/-- The base-changed exponent at `τ` is the exponent at the restriction of `τ`. -/
@[simp]
theorem baseChange_apply (n : AlgebraicInfinityType K) (τ : L →+* ℂ) :
    baseChange L n τ = n (τ.comp (algebraMap K L)) :=
  (rfl)

/-- **Base change commutes with the passage to continuous parameters** for algebraic infinity
types. -/
theorem toContinuous_baseChange (n : AlgebraicInfinityType K) :
    toContinuous (baseChange L n) = (toContinuous n).baseChange L := by
  ext w
  · rw [toContinuous_realExponent, ContinuousInfinityType.baseChange_realExponent,
      toContinuous_realExponent, baseChange_apply, ← comap_embedding_of_isReal _ (w.2.comap _)]
  · rw [toContinuous_realParity, ContinuousInfinityType.baseChange_realParity,
      toContinuous_realParity, baseChange_apply, ← comap_embedding_of_isReal _ (w.2.comap _)]
  · rw [toContinuous_complexExponent, baseChange_apply, baseChange_apply]
    by_cases hv : (w.1.comap (algebraMap K L)).IsReal
    · have he := comap_embedding_of_isReal (algebraMap K L) hv
      rw [ContinuousInfinityType.baseChange_complexExponent_of_isReal _ _ hv,
        toContinuous_realExponent, conjugate_comp, ← he,
        ComplexEmbedding.isReal_iff.mp (isReal_iff.mp hv)]
      push_cast
      ring
    · have hv' := not_isReal_iff_isComplex.mp hv
      rw [ContinuousInfinityType.baseChange_complexExponent_of_isComplex _ _ hv',
        toContinuous_complexExponent]
      rcases InfinitePlace.LiesOver.embedding_comp_eq_and_conjugate_embedding_comp_eq_or w.1
        (w.1.comap (algebraMap K L)) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h₁, h₂]
      · rw [h₁, h₂, add_comm]
  · rw [toContinuous_complexAngularFrequency, baseChange_apply, baseChange_apply]
    by_cases hv : (w.1.comap (algebraMap K L)).IsReal
    · have he := comap_embedding_of_isReal (algebraMap K L) hv
      rw [ContinuousInfinityType.baseChange_complexAngularFrequency_of_isReal _ _ hv,
        conjugate_comp, ← he, ComplexEmbedding.isReal_iff.mp (isReal_iff.mp hv), sub_self]
    · have hv' := not_isReal_iff_isComplex.mp hv
      rcases InfinitePlace.LiesOver.embedding_comp_eq_and_conjugate_embedding_comp_eq_or w.1
        (w.1.comap (algebraMap K L)) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [ContinuousInfinityType.baseChange_complexAngularFrequency_of_comp_eq _ _ hv' h₁,
          toContinuous_complexAngularFrequency, h₁, h₂]
      · rw [ContinuousInfinityType.baseChange_complexAngularFrequency_of_conjugate_comp_eq _ _ hv'
          h₂, toContinuous_complexAngularFrequency, h₁, h₂, neg_sub]

end AlgebraicInfinityType

namespace FiniteOrderInfinityType

variable (L) in
/-- **Base change of finite-order infinity types** from `K` to `L`: the sign at a real place of
`L` is the sign at the real place below it. -/
def baseChange : FiniteOrderInfinityType K →+ FiniteOrderInfinityType L :=
  (LinearMap.funLeft (ZMod 2) (ZMod 2) fun w : {w : InfinitePlace L // w.IsReal} ↦
    (⟨w.1.comap (algebraMap K L), w.2.comap _⟩ : {v : InfinitePlace K // v.IsReal})).toAddMonoidHom

/-- The base-changed sign at a real place is the sign at the real place below. -/
@[simp]
theorem baseChange_apply (ε : FiniteOrderInfinityType K) (w : {w : InfinitePlace L // w.IsReal}) :
    baseChange L ε w = ε ⟨w.1.comap (algebraMap K L), w.2.comap _⟩ :=
  (rfl)

/-- **Base change commutes with the passage to continuous parameters** for finite-order infinity
types. -/
theorem toContinuous_baseChange (ε : FiniteOrderInfinityType K) :
    toContinuous (baseChange L ε) = (toContinuous ε).baseChange L := by
  ext w
  · simp
  · simp
  · by_cases hv : (w.1.comap (algebraMap K L)).IsReal
    · simp [ContinuousInfinityType.baseChange_complexExponent_of_isReal _ _ hv]
    · simp [ContinuousInfinityType.baseChange_complexExponent_of_isComplex _ _
        (not_isReal_iff_isComplex.mp hv)]
  · by_cases hv : (w.1.comap (algebraMap K L)).IsReal
    · simp [ContinuousInfinityType.baseChange_complexAngularFrequency_of_isReal _ _ hv]
    · have hv' := not_isReal_iff_isComplex.mp hv
      rcases LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w.1
        (w.1.comap (algebraMap K L)) with h | h
      · simp [ContinuousInfinityType.baseChange_complexAngularFrequency_of_comp_eq _ _ hv' h]
      · simp [ContinuousInfinityType.baseChange_complexAngularFrequency_of_conjugate_comp_eq _ _
          hv' h]

end FiniteOrderInfinityType

/-- **Base change preserves algebraicity on the identity component**: an algebraic infinity type
twisted by real signs base changes to the base change of the algebraic type twisted by the base
change of the signs. -/
theorem ContinuousInfinityType.IsAlgebraicOnIdentityComponent.baseChange
    {t : ContinuousInfinityType K} (ht : t.IsAlgebraicOnIdentityComponent) :
    (t.baseChange L).IsAlgebraicOnIdentityComponent := by
  rw [isAlgebraicOnIdentityComponent_iff] at ht ⊢
  obtain ⟨n, ε, rfl⟩ := ht
  exact ⟨n.baseChange L, ε.baseChange L, by
    rw [map_add, AlgebraicInfinityType.toContinuous_baseChange,
      FiniteOrderInfinityType.toContinuous_baseChange]⟩

end TauCeti.GlobalNumberFields
