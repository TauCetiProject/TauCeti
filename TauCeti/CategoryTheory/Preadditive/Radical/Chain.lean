/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Basic
public import TauCeti.CategoryTheory.Preadditive.Radical.Basic
import TauCeti.CategoryTheory.ComposableArrows.Basic

/-!
# Powers of the radical and chains of non-isomorphisms

A chain of `n` composable morphisms `X₀ ⟶ X₁ ⟶ ⋯ ⟶ Xₙ` is encoded as Mathlib's
`CategoryTheory.ComposableArrows C n`. Between objects with local endomorphism rings the radical
morphisms are the non-isomorphisms, so the composite of a chain of `n` non-isomorphisms between such
objects lies in the `n`-th power of the radical
(`CategoryTheory.ComposableArrows.hom_mem_jacobsonRadicalIdeal_pow`).

In a Krull-Schmidt category these composites detect the powers of the radical: `radⁿ` vanishes
exactly when every composite of a chain of `n` non-isomorphisms between objects with local
endomorphism rings vanishes (`TauCeti.jacobsonRadicalIdeal_pow_eq_bot_iff`). This is the form in
which the Harada–Sai lemma, a statement about such chains between objects of bounded length in an
abelian category, bounds the nilpotency index of the radical
(`TauCeti.jacobsonRadicalIdeal_pow_eq_bot_of_length_le`).

## Main results

* `CategoryTheory.ComposableArrows.hom_mem_jacobsonRadicalIdeal_pow`: a chain of `n`
  non-isomorphisms between objects with local endomorphism rings has its composite in `radⁿ`.
* `TauCeti.jacobsonRadicalIdeal_pow_eq_bot_iff`: in a Krull-Schmidt category, `radⁿ = 0` exactly
  when all such composites of length `n` vanish.

## Implementation notes

For the converse direction, decompose the target of a morphism of `radⁿ` into objects with local
endomorphism rings, and prove by induction on `j` that a morphism of `radʲ` followed by the
composite of a chain of `n - j` non-isomorphisms vanishes. A generator `g ≫ h` of `radʲ⁺¹` with
`h` radical splits, along a decomposition of the middle object into objects with local
endomorphism rings, as a sum of composites `gₖ ≫ hₖ` with `hₖ` a non-isomorphism, which is
prepended to the chain.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Chapter V, Section 7 and Chapter VI, Section 1.
-/

public section

universe v u

namespace CategoryTheory.ComposableArrows

open TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- **A chain of non-isomorphisms lies in a power of the radical**: the composite of a chain of `n`
morphisms that are not isomorphisms, between objects with local endomorphism rings, lies in the
`n`-th power of the radical. -/
theorem hom_mem_jacobsonRadicalIdeal_pow :
    ∀ {n : ℕ} (F : ComposableArrows C n), (∀ i, IsLocalRing (End (F.obj i))) →
      (∀ (i : ℕ) (hi : i < n), ¬ IsIso (F.map' i (i + 1))) →
      F.hom ∈ (jacobsonRadicalIdeal C ^ n).hom F.left F.right
  | 0, F, _, _ => by
    rw [pow_zero, MorphismIdeal.one_eq_top]
    exact MorphismIdeal.mem_top _
  | n + 1, F, hF, hf => by
    have := hF 0
    have := hF 1
    have hcomp : F.hom = F.map' 0 1 ≫ F.map' 1 (n + 1) := F.map'_comp 0 1 (n + 1)
    rw [hcomp, pow_succ]
    refine MorphismIdeal.comp_mem_mul ?_ ?_
    · rw [jacobsonRadicalIdeal_hom, mem_jacobsonRadical_iff_not_isIso]
      exact hf 0 (by omega)
    · exact F.δ₀.hom_mem_jacobsonRadicalIdeal_pow (fun i ↦ hF _) fun i hi ↦ hf (i + 1) (by omega)

end CategoryTheory.ComposableArrows

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]

variable [HasFiniteBiproducts C] [IsKrullSchmidt C]

/-- The induction behind `TauCeti.jacobsonRadicalIdeal_pow_eq_bot_iff`. If every composite of a
chain of `n` non-isomorphisms between objects with local endomorphism rings vanishes, then a
morphism of `radʲ` followed by the composite of such a chain of `m` links vanishes whenever
`j + m = n`. -/
private theorem comp_hom_eq_zero_of_mem_pow {n : ℕ}
    (hn : ∀ F : ComposableArrows C n, (∀ i, IsLocalRing (End (F.obj i))) →
      (∀ (i : ℕ) (hi : i < n), ¬ IsIso (F.map' i (i + 1))) → F.hom = 0) :
    ∀ (j m : ℕ), j + m = n → ∀ (G : ComposableArrows C m), (∀ i, IsLocalRing (End (G.obj i))) →
      (∀ (i : ℕ) (hi : i < m), ¬ IsIso (G.map' i (i + 1))) →
      ∀ {X : C} (f : X ⟶ G.left), f ∈ (jacobsonRadicalIdeal C ^ j).hom X G.left →
        f ≫ G.hom = 0
  | 0, m, hm, G, hG, hl, X, f, _ => by
    obtain rfl : m = n := by omega
    rw [hn G hG hl, comp_zero]
  | j + 1, m, hm, G, hG, hl, X, f, hf => by
    rw [pow_succ'] at hf
    refine (MorphismIdeal.mul_hom_le_iff (K := (Preadditive.rightComp X G.hom).ker)).mpr ?_ hf
    intro Z g h hg hh
    simp only [AddMonoidHom.mem_ker, Preadditive.rightComp, AddMonoidHom.mk'_apply]
    -- Split `g ≫ h` along a decomposition of `Z` into objects with local endomorphism rings.
    obtain ⟨r, P, hP, ⟨e⟩⟩ := IsKrullSchmidt.exists_iso_biproduct Z
    have hsum : (g ≫ h) ≫ G.hom = ∑ k, (g ≫ e.hom ≫ biproduct.π P k) ≫
        (G.precomp (biproduct.ι P k ≫ e.inv ≫ h)).hom := by
      have hk (k : Fin r) : (G.precomp (biproduct.ι P k ≫ e.inv ≫ h)).hom =
          (biproduct.ι P k ≫ e.inv ≫ h) ≫ G.hom :=
        G.precomp_map_zero_succ _ (Fin.last m)
      calc (g ≫ h) ≫ G.hom =
          g ≫ e.hom ≫ (∑ k, biproduct.π P k ≫ biproduct.ι P k) ≫ e.inv ≫ h ≫ G.hom := by
            simp only [biproduct.total, Category.id_comp, Iso.hom_inv_id_assoc, Category.assoc]
        _ = _ := by simp only [hk, Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
    rw [hsum]
    refine Finset.sum_eq_zero fun k _ ↦ comp_hom_eq_zero_of_mem_pow hn j (m + 1) (by omega)
      (G.precomp (biproduct.ι P k ≫ e.inv ≫ h)) ?_ ?_ _
      ((jacobsonRadicalIdeal C ^ j).comp_mem_right _ hg)
    · rintro ⟨_ | i, hi⟩
      exacts [hP k, hG _]
    · have := hP k
      have := hG 0
      rintro (_ | i) hi
      · simp only [ComposableArrows.precomp_map'_zero_one]
        -- The first two vertices of the prepended string are `P k` and `G.left`.
        refine (mem_jacobsonRadical_iff_not_isIso (X := P k) (Y := G.left)).1 ?_
        rw [← jacobsonRadicalIdeal_hom]
        exact (jacobsonRadicalIdeal C).comp_mem_left _ ((jacobsonRadicalIdeal C).comp_mem_left _ hh)
      · exact hl i (by omega)

/-- **The powers of the radical are detected by chains of non-isomorphisms.** In a Krull-Schmidt
category, the `n`-th power of the radical vanishes exactly when the composite of every chain of `n`
morphisms that are not isomorphisms, between objects with local endomorphism rings, vanishes. -/
theorem jacobsonRadicalIdeal_pow_eq_bot_iff (n : ℕ) :
    jacobsonRadicalIdeal C ^ n = ⊥ ↔
      ∀ F : ComposableArrows C n, (∀ i, IsLocalRing (End (F.obj i))) →
        (∀ (i : ℕ) (hi : i < n), ¬ IsIso (F.map' i (i + 1))) → F.hom = 0 := by
  refine ⟨fun h F hF hf ↦ ?_, fun h ↦ le_antisymm (MorphismIdeal.le_def.mpr fun X Y f hf ↦ ?_)
    bot_le⟩
  · have := F.hom_mem_jacobsonRadicalIdeal_pow hF hf
    rwa [h, MorphismIdeal.mem_bot] at this
  rw [MorphismIdeal.mem_bot]
  -- Test `f` against the projections onto a decomposition of `Y`.
  obtain ⟨r, Q, hQ, ⟨e⟩⟩ := IsKrullSchmidt.exists_iso_biproduct Y
  rw [← cancel_mono e.hom, zero_comp]
  refine biproduct.hom_ext _ _ fun k ↦ ?_
  rw [zero_comp, Category.assoc]
  have := comp_hom_eq_zero_of_mem_pow h n 0 n.add_zero (ComposableArrows.mk₀ (Q k))
    (fun _ ↦ hQ k) (fun i hi ↦ absurd hi (Nat.not_lt_zero i)) (f ≫ e.hom ≫ biproduct.π Q k)
    ((jacobsonRadicalIdeal C ^ n).comp_mem_right _ hf)
  exact (Category.comp_id _).symm.trans this

end TauCeti
