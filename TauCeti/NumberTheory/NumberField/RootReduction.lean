/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Perfect

/-!
# Reducing the roots of an integer polynomial modulo a prime

Let `f` be a monic integer polynomial which splits in a number field `M` and is squarefree modulo
a prime `p`. The roots of `f` in `M` are algebraic integers, so any ring homomorphism
`ρ : 𝓞 M →+* k` to a field `k` over `𝔽_p` can be applied to them. Their images are all the roots
of `f mod p` in `k`, counted with multiplicity, and these are distinct because `f mod p` is
squarefree over the perfect field `𝔽_p`. So `f mod p` splits in `k`, and reduction along `ρ` is
a bijection between the root sets.

## Main results

* `TauCeti.NumberField.splits_and_exists_rootSet_equiv_of_squarefree_map_zmod`: `f mod p` splits
  in `k`, and reduction along `ρ` is a bijection from the roots of `f` in `M` onto the roots of
  `f mod p` in `k`.
-/

public section

open Polynomial
open scoped NumberField

namespace TauCeti.NumberField

variable {M : Type*} [Field M] [NumberField M] {f : ℤ[X]} {p : ℕ} [Fact p.Prime]

/-- The two ways of viewing an integer polynomial over a number field agree. -/
private theorem map_map_intCast_rat (f : ℤ[X]) :
    (f.map (Int.castRingHom ℚ)).map (algebraMap ℚ M) =
      (f.map (algebraMap ℤ (𝓞 M))).map (algebraMap (𝓞 M) M) := by
  rw [Polynomial.map_map, Polynomial.map_map,
    RingHom.ext_int ((algebraMap ℚ M).comp (Int.castRingHom ℚ))
      ((algebraMap (𝓞 M) M).comp (algebraMap ℤ (𝓞 M)))]

/-- **Reducing the roots of `f` modulo a prime.** Let `f` be monic, split in `M`, and squarefree
modulo `p`, and let `ρ : 𝓞 M →+* k` be a ring homomorphism to a field `k` over `𝔽_p`. Then
`f mod p` splits in `k`, and reduction along `ρ` is a bijection from the roots of `f` in `M` onto
the roots of `f mod p` in `k`. -/
theorem splits_and_exists_rootSet_equiv_of_squarefree_map_zmod (hf : f.Monic)
    (hsq : Squarefree (f.map (Int.castRingHom (ZMod p))))
    (hsplit : ((f.map (Int.castRingHom ℚ)).map (algebraMap ℚ M)).Splits)
    {k : Type*} [Field k] [Algebra (ZMod p) k] (ρ : 𝓞 M →+* k) :
    ((f.map (Int.castRingHom (ZMod p))).map (algebraMap (ZMod p) k)).Splits ∧
      ∃ e : (f.map (Int.castRingHom ℚ)).rootSet M ≃
          (f.map (Int.castRingHom (ZMod p))).rootSet k,
        ∀ (x : (f.map (Int.castRingHom ℚ)).rootSet M) (y : 𝓞 M),
          algebraMap (𝓞 M) M y = x → (e x : k) = ρ y := by
  classical
  set fM := (f.map (Int.castRingHom ℚ)).map (algebraMap ℚ M) with hfM
  -- The roots of `f` in `M` are algebraic integers, so they form a multiset `t` of `𝓞 M`.
  -- Along the tower `ℤ → ℚ → M`, being a root of `f` over `ℚ` is being a root of `f` itself.
  have hint : ∀ x ∈ fM.roots, IsIntegral ℤ x := fun x hx =>
    ⟨f, hf, by
      rw [← aeval_def, ← aeval_map_algebraMap (A := ℚ), algebraMap_int_eq, ← eval_map_algebraMap]
      exact (mem_roots'.mp hx).2⟩
  obtain ⟨t, ht⟩ : ∃ t : Multiset (𝓞 M), t.map (algebraMap (𝓞 M) M) = fM.roots :=
    ⟨fM.roots.attach.map fun x => IsIntegralClosure.mk' (𝓞 M) x.1 (hint x.1 x.2), by
      simp [Multiset.map_map, IsIntegralClosure.algebraMap_mk']⟩
  have hfO : f.map (algebraMap ℤ (𝓞 M)) = (t.map fun a => X - C a).prod := by
    refine Polynomial.map_injective _ (FaithfulSMul.algebraMap_injective (𝓞 M) M) ?_
    rw [← map_map_intCast_rat, ← hfM]
    conv_lhs => rw [hsplit.eq_prod_roots_of_monic ((hf.map _).map _)]
    rw [← ht, Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
    simp
  -- Reducing, `f mod p` is the product of the `X - ρ a` over `a ∈ t`.
  have hk : (f.map (Int.castRingHom (ZMod p))).map (algebraMap (ZMod p) k) =
      ((t.map ρ).map fun a => X - C a).prod := by
    rw [Polynomial.map_map,
      RingHom.ext_int ((algebraMap (ZMod p) k).comp (Int.castRingHom (ZMod p)))
        (ρ.comp (algebraMap ℤ (𝓞 M))),
      ← Polynomial.map_map, hfO, Polynomial.map_multiset_prod, Multiset.map_map,
      Multiset.map_map]
    simp
  have hroots : ((f.map (Int.castRingHom (ZMod p))).map (algebraMap (ZMod p) k)).roots =
      t.map ρ := by
    rw [hk, roots_multiset_prod_X_sub_C]
  -- `f mod p` is separable, so the reductions of the roots are distinct.
  have hnodup : (t.map ρ).Nodup :=
    hroots ▸ nodup_roots ((PerfectField.separable_iff_squarefree.mpr hsq).map)
  have hmem : ∀ x, x ∈ (f.map (Int.castRingHom ℚ)).rootSet M ↔
      ∃ a ∈ t, algebraMap (𝓞 M) M a = x := fun x => by
    rw [rootSet_def, Finset.mem_coe, Multiset.mem_toFinset, aroots_def, ← hfM, ← ht,
      Multiset.mem_map]
  have hmemk : ∀ z, z ∈ (f.map (Int.castRingHom (ZMod p))).rootSet k ↔ z ∈ t.map ρ :=
    fun z => by rw [rootSet_def, Finset.mem_coe, Multiset.mem_toFinset, aroots_def, hroots]
  -- Reduction of a root, as a map of root sets.
  let red (x : (f.map (Int.castRingHom ℚ)).rootSet M) :
      (f.map (Int.castRingHom (ZMod p))).rootSet k :=
    ⟨ρ ((hmem x).mp x.2).choose,
      (hmemk _).mpr (Multiset.mem_map_of_mem _ ((hmem x).mp x.2).choose_spec.1)⟩
  have hred (x : (f.map (Int.castRingHom ℚ)).rootSet M) (y : 𝓞 M)
      (hy : algebraMap (𝓞 M) M y = x) : (red x : k) = ρ y := by
    obtain rfl : ((hmem x).mp x.2).choose = y :=
      FaithfulSMul.algebraMap_injective (𝓞 M) M (((hmem x).mp x.2).choose_spec.2.trans hy.symm)
    rfl
  have hbij : Function.Bijective red := by
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · have h := Multiset.inj_on_of_nodup_map hnodup _ ((hmem x).mp x.2).choose_spec.1 _
        ((hmem y).mp y.2).choose_spec.1 (congrArg Subtype.val hxy)
      exact Subtype.ext (((hmem x).mp x.2).choose_spec.2.symm.trans
        ((congrArg (algebraMap (𝓞 M) M) h).trans ((hmem y).mp y.2).choose_spec.2))
    · obtain ⟨a, ha, hz⟩ := Multiset.mem_map.mp ((hmemk z).mp z.2)
      refine ⟨⟨_, (hmem _).mpr ⟨a, ha, rfl⟩⟩, Subtype.ext ?_⟩
      rw [hred _ a rfl, hz]
  refine ⟨hk ▸ Splits.multisetProd fun g hg => ?_, Equiv.ofBijective red hbij, hred⟩
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hg
  exact Splits.X_sub_C a

end TauCeti.NumberField
