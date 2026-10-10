/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Artin–Schreier extensions

A root of `X ^ p - X - u` in characteristic `p` generates a Galois extension whose
automorphisms translate the root by elements of the prime field. If `u` is not of the
form `w ^ p - w` in the base field, the extension has degree `p` and its Galois group
is the additive group of `ZMod p`. This supplies the field-theoretic input for the
ramification theory of Artin–Schreier covers.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.7.8.
* Mathlib: `Subfield.splits_bot` and `IsGalois.card_aut_eq_finrank`.
-/

public section

open Polynomial
open scoped IntermediateField

namespace TauCeti.ArtinSchreier

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {p : ℕ} [Fact p.Prime]
variable {u : K}

private theorem monic_polynomial (u : K) : (X ^ p - X - C u : K[X]).Monic := by
  have h : (X + C u).degree < ↑p := by
    rw [degree_X_add_C]
    exact_mod_cast (Fact.out : p.Prime).one_lt
  convert monic_X_pow_sub h using 1
  ring

private theorem exists_zmod_cast_of_pow_eq_self [CharP L p] {x : L} (hx : x ^ p = x) :
    ∃ c : ZMod p, (ZMod.cast c : L) = x := by
  rw [← Subfield.mem_bot_iff_pow_eq_self L p, ← ZMod.fieldRange_castHom_eq_bot p] at hx
  exact hx

omit [Fact p.Prime] in
private theorem gal_fixes_zmod_cast [NeZero p] (σ : Gal(L/K)) (c : ZMod p) :
    σ (ZMod.cast c : L) = (ZMod.cast c : L) := by
  rw [ZMod.cast_eq_val]
  exact map_natCast σ c.val

-- `y` is a root of `X ^ p - X - u` in `L`, a field extension of `K`.
variable {y : L} (hy : y ^ p - y = algebraMap K L u)
include hy

private theorem integral_root : IsIntegral K y := by
  have := p
  refine ⟨X ^ p - X - C u, monic_polynomial u, ?_⟩
  simp [hy]

variable [CharP K p]

/-- An Artin–Schreier polynomial splits in any field containing one of its roots. -/
theorem splits : ((X ^ p - X - C u).map (algebraMap K L)).Splits := by
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have h0 : (X ^ p - X : L[X]).Splits := by
    simpa using (Subfield.splits_bot L p).map (Subfield.subtype _)
  have he : (X ^ p - X : L[X]).comp (X - C y) = (X ^ p - X - C u).map (algebraMap K L) := by
    simp only [sub_comp, pow_comp, X_comp, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]
    rw [Polynomial.map_C, sub_pow_char, ← C_pow, ← hy, map_sub]
    ring
  rw [← he]
  exact h0.comp_X_sub_C y

private theorem exists_translation (σ : Gal(L/K)) : ∃ c : ZMod p, (ZMod.cast c : L) = σ y - y := by
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hp : (σ y - y) ^ p = σ y - y := by
    rw [sub_pow_char, ← map_pow, sub_eq_sub_iff_sub_eq_sub, ← map_sub, hy, AlgEquiv.commutes]
  exact exists_zmod_cast_of_pow_eq_self hp

private noncomputable def translation (σ : Gal(L/K)) : ZMod p := (exists_translation hy σ).choose

private theorem translation_spec (σ : Gal(L/K)) : (ZMod.cast (translation hy σ) : L) = σ y - y :=
  (exists_translation hy σ).choose_spec

/-- The translation character sends an automorphism to the prime-field displacement of a chosen
Artin–Schreier root. The parameters `u` and `y` specify the equation and root, with `hy` witnessing
the root equation; for fixed `u`, the character is independent of the chosen root. The
multiplicative type tag matches composition in `Gal`. -/
noncomputable def translationHom : Gal(L/K) →* Multiplicative (ZMod p) where
  toFun σ := Multiplicative.ofAdd (translation hy σ)
  map_one' := by
    have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
    apply congrArg Multiplicative.ofAdd
    apply (ZMod.castHom (m := p) dvd_rfl L).injective
    simp [translation_spec]
  map_mul' σ τ := by
    have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
    apply congrArg Multiplicative.ofAdd
    apply (ZMod.castHom (m := p) dvd_rfl L).injective
    simp only [map_add, ZMod.castHom_apply, toAdd_ofAdd, translation_spec]
    have hfix := gal_fixes_zmod_cast σ (translation hy τ)
    rw [translation_spec] at hfix
    simp only [AlgEquiv.mul_apply, map_sub] at hfix ⊢
    linear_combination hfix

/-- The translation character computes the action on the chosen root. -/
theorem aut_apply_eq_add_translationHom (σ : Gal(L/K)) :
    σ y = y + (ZMod.cast (translationHom hy σ).toAdd : L) := by
  simp [translationHom, translation_spec]

/-- The translation character is independent of the chosen root of the Artin–Schreier equation. -/
theorem translationHom_eq_of_same_u {z : L} (hz : z ^ p - z = algebraMap K L u) :
    translationHom hy = translationHom hz := by
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hpow : (y - z) ^ p = y - z := by
    rw [sub_pow_char]
    linear_combination hy - hz
  obtain ⟨c, hc⟩ := exists_zmod_cast_of_pow_eq_self hpow
  ext σ
  have h := gal_fixes_zmod_cast σ c
  apply (ZMod.castHom dvd_rfl L).injective
  simp only [ZMod.castHom_apply]
  rw [hc, map_sub, aut_apply_eq_add_translationHom hy σ, aut_apply_eq_add_translationHom hz σ] at h
  linear_combination h

variable (hgen : K⟮y⟯ = ⊤)
include hgen

/-- A field generated by an Artin–Schreier root is its polynomial's splitting field. -/
theorem isSplittingField : IsSplittingField K L (X ^ p - X - C u) := by
  have hint := integral_root hy
  refine ⟨splits hy, top_unique ?_⟩
  rw [← IntermediateField.top_toSubalgebra, ← hgen,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
  apply Algebra.adjoin_mono
  rw [Set.singleton_subset_iff, mem_rootSet_of_ne (monic_polynomial u).ne_zero]
  simp [hy]

/-- A generated Artin–Schreier extension is Galois, including the trivial case. -/
theorem isGalois : IsGalois K L := by
  let := isSplittingField hy hgen
  apply IsGalois.of_separable_splitting_field (p := X ^ p - X - C u)
  simpa [sub_eq_add_neg] using
    separable_C_mul_X_pow_add_C_mul_X_add_C' p p (1 : K) (-1) (-u) dvd_rfl (by simp)

/-- An automorphism of a generated Artin–Schreier extension is determined by its
translation of the generator. -/
theorem translationHom_injective : Function.Injective (translationHom hy) := by
  intro σ τ h
  apply AlgEquiv.coe_toAlgHom_injective
  apply (PowerBasis.ofAdjoinSimpleEqTop (integral_root hy) hgen).algHom_ext
  simp only [PowerBasis.ofAdjoinSimpleEqTop_gen, AlgEquiv.coe_toAlgHom]
  rw [aut_apply_eq_add_translationHom hy σ, aut_apply_eq_add_translationHom hy τ, h]

/-- Every generated Artin–Schreier extension has a cyclic Galois group. -/
theorem isCyclic : IsCyclic Gal(L/K) :=
  isCyclic_of_injective (translationHom hy) (translationHom_injective hy hgen)

-- The extension L/K is nontrivial
variable (hu : ∀ w : K, w ^ p - w ≠ u)
include hu

/-- A nontrivial Artin–Schreier class gives an extension of degree exactly `p`. -/
theorem finrank_eq : Module.finrank K L = p := by
  let := isSplittingField hy hgen
  have := IsSplittingField.finiteDimensional L (X ^ p - X - C u)
  have := isGalois hy hgen
  have hd := Subgroup.card_dvd_of_injective (translationHom hy) (translationHom_injective hy hgen)
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, IsGalois.card_aut_eq_finrank] at hd
  rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hd with h | h
  · exfalso
    obtain ⟨w, hw⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h).2 y
    apply hu w
    apply (algebraMap K L).injective
    simpa [hw] using hy
  · exact h

/-- For a nontrivial Artin–Schreier class, every prime-field translation occurs as a
unique automorphism. -/
noncomputable def autEquivZmod : Gal(L/K) ≃* Multiplicative (ZMod p) := by
  let := isSplittingField hy hgen
  have := IsSplittingField.finiteDimensional L (X ^ p - X - C u)
  have := isGalois hy hgen
  apply MulEquiv.ofBijective (translationHom hy)
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨translationHom_injective hy hgen, ?_⟩
  rw [IsGalois.card_aut_eq_finrank, finrank_eq hy hgen hu,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

/-- The Galois-group equivalence is the translation character of the chosen root. -/
@[simp]
theorem autEquivZmod_apply (σ : Gal(L/K)) : autEquivZmod hy hgen hu σ = translationHom hy σ := (rfl)

/-- The inverse Galois-group equivalence translates the generator by its argument. -/
@[simp]
theorem autEquivZmod_symm_apply (c : Multiplicative (ZMod p)) :
    (autEquivZmod hy hgen hu).symm c y = y + (ZMod.cast c.toAdd : L) := by
  rw [aut_apply_eq_add_translationHom hy, ← autEquivZmod_apply hy hgen hu,
    MulEquiv.apply_symm_apply]

end TauCeti.ArtinSchreier
