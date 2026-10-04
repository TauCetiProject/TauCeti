/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Norm.Unramified
import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# The norm quotient of an unramified local extension

Let `L/K` be a finite unramified extension of nonarchimedean local fields. The field norm has
normalized valuation divisible by `[L : K]`, and every element of `Kˣ` whose valuation is divisible
by `[L : K]` is a norm. Consequently normalized valuation induces an equivalence

`Kˣ / N_{L/K}(Lˣ) ≃ ℤ / [L : K]ℤ`.

Under this equivalence the class of every uniformizer maps to `1`. This is the arithmetic input
that identifies the finite local Artin symbol of a uniformizer with arithmetic Frobenius.

## Main result

* `TauCeti.ClassFieldTheory.localNormQuotientEquivZMod_unramified`: the unramified norm quotient is
  cyclic of order `[L : K]`, with the class of a uniformizer as the distinguished generator.

## References

* J.-P. Serre, *Local Fields*, Chapter V, §2 and Chapter XI, §3.
-/

public section

noncomputable section

open ValuativeRel

namespace TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [FiniteDimensional K L]

/-- Normalized valuation modulo `n`, written as a multiplicative homomorphism. -/
private def normalizedValuationModMul (n : ℕ) : Kˣ →* Multiplicative (ZMod n) :=
  AddMonoidHom.toMultiplicativeRight (normalizedValuationMod K n)

/-- Normalized valuation modulo `n` is surjective. -/
private theorem normalizedValuationModMul_surjective (n : ℕ) :
    Function.Surjective (normalizedValuationModMul K n) := by
  intro x
  obtain ⟨a, ha⟩ := normalizedValuationMod_surjective (K := K) n x.toAdd
  exact ⟨a.toMul, Multiplicative.toAdd.injective (by simpa [normalizedValuationModMul] using ha)⟩

/-- The kernel of normalized valuation modulo the degree of an unramified extension is its norm
subgroup. -/
private theorem normGroup_eq_ker_normalizedValuationMod [IsUnramified K L] :
    normGroup K L = (normalizedValuationModMul K (Module.finrank K L)).ker := by
  ext x
  rw [MonoidHom.mem_ker]
  simp only [normalizedValuationModMul, AddMonoidHom.coe_toMultiplicativeRight,
    Function.comp_apply]
  constructor
  · intro hx
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd, toAdd_one, normalizedValuationMod_ofMul,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [← IsUnramified.inertiaDegree_eq_finrank]
    exact mem_normGroup_iff_dvd_normalizedValuation.mp hx
  · intro hx
    apply mem_normGroup_iff_dvd_normalizedValuation.mpr
    rw [IsUnramified.inertiaDegree_eq_finrank, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hx' := congrArg Multiplicative.toAdd hx
    simpa only [toAdd_ofAdd, toAdd_one, normalizedValuationMod_ofMul] using hx'

/-- In an unramified extension of degree `n`, the norm quotient is cyclic of order `n`, generated
by the class of a uniformizer. -/
theorem localNormQuotientEquivZMod_unramified
    (h : ramificationIndex K L = 1) (π : 𝒪[K]) (hπ : Irreducible π)
    (hπ0 : (π : K) ≠ 0) :
    ∃ e : Additive (Kˣ ⧸ normGroup K L) ≃+ ZMod (Module.finrank K L),
      e (Additive.ofMul (QuotientGroup.mk (Units.mk0 (π : K) hπ0))) = 1 := by
  have : IsUnramified K L := (isUnramified_iff_ramificationIndex_eq_one K L).2 h
  let f : Kˣ →* Multiplicative (ZMod (Module.finrank K L)) :=
    normalizedValuationModMul K (Module.finrank K L)
  have hf : Function.Surjective f := normalizedValuationModMul_surjective K _
  let e : Additive (Kˣ ⧸ normGroup K L) ≃+ ZMod (Module.finrank K L) :=
    MulEquiv.toAdditiveLeft <|
      (QuotientGroup.quotientMulEquivOfEq
        (normGroup_eq_ker_normalizedValuationMod K L)).trans <|
        QuotientGroup.quotientKerEquivOfSurjective f hf
  refine ⟨e, ?_⟩
  dsimp only [e]
  -- Expose the additive and multiplicative type tags so the two quotient-equivalence evaluation
  -- lemmas apply without unfolding their noncomputable first-isomorphism constructions.
  change Multiplicative.toAdd
    (((QuotientGroup.quotientMulEquivOfEq
      (normGroup_eq_ker_normalizedValuationMod K L)).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hf))
      (QuotientGroup.mk (Units.mk0 (π : K) hπ0))) = 1
  rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk]
  dsimp only [f]
  simp only [normalizedValuationModMul, AddMonoidHom.coe_toMultiplicativeRight,
    Function.comp_apply, toAdd_ofAdd, normalizedValuationMod_ofMul]
  rw [normalizedValuation_irreducible (K := K) hπ, toAdd_ofAdd, Int.cast_one]

end TauCeti.ClassFieldTheory
