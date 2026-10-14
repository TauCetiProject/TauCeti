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
-- Non-public: `Polynomial.natDegree_X_pow_sub_X_sub_C` is the degree of an Artin–Schreier
-- polynomial, in the proof of the criterion only.
import TauCeti.Algebra.Polynomial.XPowSubXSubC

/-!
# Artin–Schreier extensions

A root of `X ^ p - X - u` in characteristic `p` generates a Galois extension whose
automorphisms translate the root by elements of the prime field. If `u` is not of the
form `w ^ p - w` in the base field, the extension has degree `p` and its Galois group
is the additive group of `ZMod p`. This supplies the field-theoretic input for the
ramification theory of Artin–Schreier covers.

The degree computation also settles irreducibility of the polynomial itself:
`X ^ p - X - u` is irreducible exactly when `u` is not of the form `w ^ p - w`
(`TauCeti.ArtinSchreier.irreducible_polynomial_iff`). That is what constructs an Artin–Schreier
extension of a given field from a given class, the theory above describing only extensions already
carrying a root.

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

omit hy in
/-- Two solutions of the same Artin–Schreier equation differ by a prime-field element: their
difference is fixed by the Frobenius. -/
private theorem exists_zmod_cast_eq_sub {z w : L} (hz : z ^ p - z = algebraMap K L u)
    (hw : w ^ p - w = algebraMap K L u) : ∃ c : ZMod p, (ZMod.cast c : L) = z - w := by
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hpow : (z - w) ^ p = z - w := by
    rw [sub_pow_char]
    linear_combination hz - hw
  rw [← Subfield.mem_bot_iff_pow_eq_self L p, ← ZMod.fieldRange_castHom_eq_bot p] at hpow
  exact hpow

private theorem exists_translation (σ : Gal(L/K)) : ∃ c : ZMod p, (ZMod.cast c : L) = σ y - y := by
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hp : (σ y - y) ^ p = σ y - y := by
    rw [sub_pow_char, ← map_pow, sub_eq_sub_iff_sub_eq_sub, ← map_sub, hy, AlgEquiv.commutes]
  rw [← Subfield.mem_bot_iff_pow_eq_self L p, ← ZMod.fieldRange_castHom_eq_bot p] at hp
  exact hp

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
    have hfix := map_natCast σ (translation hy τ).val
    rw [← ZMod.cast_eq_val, translation_spec] at hfix
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
  obtain ⟨c, hc⟩ := exists_zmod_cast_eq_sub hy hz
  ext σ
  have h := map_natCast σ c.val
  rw [← ZMod.cast_eq_val, hc, map_sub, aut_apply_eq_add_translationHom hy σ,
    aut_apply_eq_add_translationHom hz σ] at h
  apply (ZMod.castHom dvd_rfl L).injective
  simp only [ZMod.castHom_apply]
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

omit hy hgen hu in
/-- **The Artin–Schreier criterion**: over a field of characteristic `p`, the polynomial
`X ^ p - X - u` is irreducible exactly when `u` is not of the form `w ^ p - w`.  This is what builds
an Artin–Schreier extension of degree `p` out of a class of `u`: the quotient by an irreducible
polynomial is a field, and the theory above then applies to the image of `X` in it. -/
theorem irreducible_polynomial_iff (u : K) :
    Irreducible (X ^ p - X - C u : K[X]) ↔ ∀ w : K, w ^ p - w ≠ u := by
  classical
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hmonic : (X ^ p - X - C u : K[X]).Monic := monic_polynomial u
  have hdeg : (X ^ p - X - C u : K[X]).natDegree = p :=
    natDegree_X_pow_sub_X_sub_C hp1 u
  constructor
  · -- A root of an irreducible polynomial of degree `p > 1` is impossible.
    intro hirr w hw
    have hroot : (X ^ p - X - C u : K[X]).IsRoot w := by simp [IsRoot, hw]
    obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hroot
    have hq0 : q ≠ 0 := fun h0 ↦ hmonic.ne_zero (by rw [hq, h0, mul_zero])
    rcases hirr.isUnit_or_isUnit hq with h | h
    · simpa using natDegree_eq_zero_of_isUnit h
    · rw [hq, natDegree_mul (X_sub_C_ne_zero w) hq0, natDegree_X_sub_C,
        natDegree_eq_zero_of_isUnit h] at hdeg
      omega
  · -- Without a root the polynomial is the minimal polynomial of a root in its splitting field.
    intro hu
    set L := (X ^ p - X - C u : K[X]).SplittingField with hL
    set g : L[X] := (X ^ p - X - C u : K[X]).map (algebraMap K L) with hg
    have hmap : g.natDegree = p := by
      rw [hg, natDegree_map_eq_of_injective (algebraMap K L).injective, hdeg]
    have hg0 : g ≠ 0 := fun h0 ↦ by rw [h0, natDegree_zero] at hmap; omega
    obtain ⟨y, hymem⟩ : ∃ y : L, y ∈ g.roots := by
      refine Multiset.card_pos_iff_exists_mem.mp ?_
      have hcard := (IsSplittingField.splits L (X ^ p - X - C u)).natDegree_eq_card_roots
      rw [← hg, hmap] at hcard
      omega
    have hyroot : g.IsRoot y := (mem_roots hg0).mp hymem
    have hy : y ^ p - y = algebraMap K L u := by
      have h := hyroot
      rw [hg] at h
      simp only [IsRoot, eval_map, ← aeval_def, map_sub, map_pow, aeval_X, aeval_C] at h
      linear_combination h
    -- Every root differs from `y` by a prime-field element, so `y` generates the splitting field.
    have hgen : K⟮y⟯ = ⊤ := by
      refine top_unique fun x _ ↦ ?_
      have hsub : Algebra.adjoin K ((X ^ p - X - C u : K[X]).rootSet L) ≤
          (K⟮y⟯).toSubalgebra := by
        refine Algebra.adjoin_le fun r hr ↦ ?_
        have hrroot : r ^ p - r = algebraMap K L u := by
          have h := (mem_rootSet.mp hr).2
          simp only [aeval_def, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
          linear_combination h
        obtain ⟨c, hc⟩ := exists_zmod_cast_eq_sub hrroot hy
        have hr' : r = y + ((c.val : ℕ) : L) := by
          rw [← ZMod.natCast_val] at hc
          linear_combination -hc
        rw [hr']
        exact add_mem (IntermediateField.mem_adjoin_simple_self K y)
          (Subalgebra.natCast_mem _ _)
      rw [IsSplittingField.adjoin_rootSet (L := L) (X ^ p - X - C u)] at hsub
      exact hsub Algebra.mem_top
    have hint : IsIntegral K y := integral_root hy
    have hmindeg : (minpoly K y).natDegree = p := by
      rw [← IntermediateField.adjoin.finrank hint, hgen, IntermediateField.finrank_top',
        finrank_eq hy hgen hu]
    have haeval : Polynomial.aeval y (X ^ p - X - C u : K[X]) = 0 := by
      simp only [map_sub, map_pow, aeval_X, aeval_C]
      linear_combination hy
    have hdvd : minpoly K y ∣ (X ^ p - X - C u : K[X]) := minpoly.dvd K y haeval
    have heq := Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmonic hdvd
      (by omega)
    rw [heq]
    exact minpoly.irreducible hint

end TauCeti.ArtinSchreier
