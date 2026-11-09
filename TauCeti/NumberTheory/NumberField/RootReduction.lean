/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.FieldTheory.Separable

/-!
# Reducing the roots of an integer polynomial along a ring homomorphism

Let `f` be a monic integer polynomial which splits in a field `M` of characteristic zero, and let
`R` be a commutative ring over which `f` is separable. The roots of `f` in `M` are algebraic
integers, so any ring homomorphism `ρ : 𝓞 M →+* k` to a domain `k` over `R` can be applied to
them. Their images are all the roots of `f` in `k`, counted with multiplicity, and these are
distinct because `f` is separable over `R`. So `f` splits in `k`, and reduction along `ρ` is a
bijection between the root sets.

The main case is `R = 𝔽_p` with `M` a number field and `k` a residue field of `𝓞 M`: there `f` is
separable as soon as `f mod p` is squarefree, as `𝔽_p` is perfect.

## Main results

* `TauCeti.NumberField.exists_multiset_map_algebraMap_eq_roots`: a monic integer polynomial which
  splits in a field `M` of characteristic zero factors over `𝓞 M` into linear factors whose
  roots map onto the roots in `M`.
* `TauCeti.NumberField.splits_and_exists_rootSet_equiv_of_separable_map`: `f` splits in `k`, and
  reduction along `ρ` is a bijection from the roots of `f` in `M` onto the roots of `f` in `k`.
-/

public section

open Polynomial
open scoped NumberField

namespace TauCeti.NumberField

variable {M : Type*} [Field M] [CharZero M] {f : ℤ[X]}

/-- The two ways of viewing an integer polynomial over a field of characteristic zero agree. -/
private theorem map_map_intCast_rat (f : ℤ[X]) :
    (f.map (Int.castRingHom ℚ)).map (algebraMap ℚ M) =
      (f.map (algebraMap ℤ (𝓞 M))).map (algebraMap (𝓞 M) M) := by
  simp only [Polynomial.map_map]
  congr 1
  exact RingHom.ext_int _ _

/-- The roots of a monic integer polynomial `f` which splits in `M` are algebraic integers: there is
a multiset `t` in `𝓞 M` with `f = ∏ (X - a)` over `a ∈ t` in `(𝓞 M)[X]` and whose image in `M` is
the multiset of roots of `f` in `M`. -/
theorem exists_multiset_map_algebraMap_eq_roots (hf : f.Monic)
    (hsplit : ((f.map (Int.castRingHom ℚ)).map (algebraMap ℚ M)).Splits) :
    ∃ t : Multiset (𝓞 M), t.map (algebraMap (𝓞 M) M) =
        ((f.map (Int.castRingHom ℚ)).map (algebraMap ℚ M)).roots ∧
      f.map (algebraMap ℤ (𝓞 M)) = (t.map fun a => X - C a).prod := by
  classical
  set fM := (f.map (Int.castRingHom ℚ)).map (algebraMap ℚ M) with hfM
  -- Along the tower `ℤ → ℚ → M`, being a root of `f` over `ℚ` is being a root of `f` itself.
  have hint : ∀ x ∈ fM.roots, IsIntegral ℤ x := fun x hx =>
    ⟨f, hf, by
      rw [← aeval_def, ← aeval_map_algebraMap (A := ℚ), algebraMap_int_eq, ← eval_map_algebraMap]
      exact (mem_roots'.mp hx).2⟩
  obtain ⟨t, ht⟩ : ∃ t : Multiset (𝓞 M), t.map (algebraMap (𝓞 M) M) = fM.roots :=
    ⟨fM.roots.attach.map fun x => IsIntegralClosure.mk' (𝓞 M) x.1 (hint x.1 x.2), by
      simp [Multiset.map_map, IsIntegralClosure.algebraMap_mk']⟩
  refine ⟨t, ht, ?_⟩
  refine Polynomial.map_injective _ (FaithfulSMul.algebraMap_injective (𝓞 M) M) ?_
  rw [← map_map_intCast_rat, ← hfM, hsplit.eq_prod_roots_of_monic ((hf.map _).map _), ← ht]
  simp [Polynomial.map_multiset_prod, Multiset.map_map]

/-- **Reducing the roots of `f` along a ring homomorphism.** Let `f` be monic, split in `M`, and
separable over a commutative ring `R`, and let `ρ : 𝓞 M →+* k` be a ring homomorphism to a domain
`k` over `R`. Then `f` splits in `k`, and reduction along `ρ` is a bijection from the roots of `f`
in `M` onto the roots of `f` in `k`. -/
theorem splits_and_exists_rootSet_equiv_of_separable_map (hf : f.Monic)
    {R : Type*} [CommRing R] (hsep : (f.map (Int.castRingHom R)).Separable)
    (hsplit : ((f.map (Int.castRingHom ℚ)).map (algebraMap ℚ M)).Splits)
    {k : Type*} [CommRing k] [IsDomain k] [Algebra R k] (ρ : 𝓞 M →+* k) :
    ((f.map (Int.castRingHom R)).map (algebraMap R k)).Splits ∧
      ∃ e : (f.map (Int.castRingHom ℚ)).rootSet M ≃ (f.map (Int.castRingHom R)).rootSet k,
        ∀ (x : (f.map (Int.castRingHom ℚ)).rootSet M) (y : 𝓞 M),
          algebraMap (𝓞 M) M y = x → (e x : k) = ρ y := by
  classical
  obtain ⟨t, ht, hfO⟩ := exists_multiset_map_algebraMap_eq_roots hf hsplit
  -- Reducing, `f` over `k` is the product of the `X - ρ a` over `a ∈ t`.
  have hk : (f.map (Int.castRingHom R)).map (algebraMap R k) =
      ((t.map ρ).map fun a => X - C a).prod := by
    rw [Polynomial.map_map,
      RingHom.ext_int ((algebraMap R k).comp (Int.castRingHom R))
        (ρ.comp (algebraMap ℤ (𝓞 M))),
      ← Polynomial.map_map, hfO]
    simp [Polynomial.map_multiset_prod, Multiset.map_map]
  have hroots : ((f.map (Int.castRingHom R)).map (algebraMap R k)).roots = t.map ρ := by
    rw [hk, roots_multiset_prod_X_sub_C]
  -- `f` is separable over `R`, so the reductions of the roots are distinct.
  have hnodup : (t.map ρ).Nodup := hroots ▸ nodup_roots hsep.map
  have hmem : ∀ x, x ∈ (f.map (Int.castRingHom ℚ)).rootSet M ↔
      ∃ a ∈ t, algebraMap (𝓞 M) M a = x := fun x => by
    rw [rootSet_def, Finset.mem_coe, Multiset.mem_toFinset, aroots_def, ← ht,
      Multiset.mem_map]
  have hmemk : ∀ z, z ∈ (f.map (Int.castRingHom R)).rootSet k ↔ z ∈ t.map ρ :=
    fun z => by rw [rootSet_def, Finset.mem_coe, Multiset.mem_toFinset, aroots_def, hroots]
  -- Reduction of a root, as a map of root sets.
  let red (x : (f.map (Int.castRingHom ℚ)).rootSet M) :
      (f.map (Int.castRingHom R)).rootSet k :=
    ⟨ρ ((hmem x).mp x.2).choose,
      (hmemk _).mpr (Multiset.mem_map_of_mem _ ((hmem x).mp x.2).choose_spec.1)⟩
  have hred (x : (f.map (Int.castRingHom ℚ)).rootSet M) (y : 𝓞 M)
      (hy : algebraMap (𝓞 M) M y = x) : (red x : k) = ρ y := by
    obtain rfl : ((hmem x).mp x.2).choose = y :=
      FaithfulSMul.algebraMap_injective (𝓞 M) M (((hmem x).mp x.2).choose_spec.2.trans hy.symm)
    rfl
  have hbij : Function.Bijective red := by
    refine ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ hxy => ?_, fun z => ?_⟩
    · obtain ⟨a, ha, rfl⟩ := (hmem x).mp hx
      obtain ⟨b, hb, rfl⟩ := (hmem y).mp hy
      rw [Subtype.ext_iff, hred _ a rfl, hred _ b rfl] at hxy
      obtain rfl := Multiset.inj_on_of_nodup_map hnodup a ha b hb hxy
      rfl
    · obtain ⟨a, ha, hz⟩ := Multiset.mem_map.mp ((hmemk z).mp z.2)
      refine ⟨⟨_, (hmem _).mpr ⟨a, ha, rfl⟩⟩, Subtype.ext ?_⟩
      rw [hred _ a rfl, hz]
  refine ⟨hk ▸ Splits.multisetProd fun g hg => ?_, Equiv.ofBijective red hbij, hred⟩
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hg
  exact Splits.X_sub_C a

end TauCeti.NumberField
