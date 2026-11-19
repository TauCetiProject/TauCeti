/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Flat.Tensor
import TauCeti.RingTheory.Ideal.ArtinRees
import TauCeti.RingTheory.Ideal.KrullIntersection
import TauCeti.RingTheory.Ideal.TensorProduct

/-!
# Flatness from bijections on infinitesimal quotients

Let `A → B` be a homomorphism of noetherian rings. Suppose that for every maximal ideal `𝔫` of
`B`, with contraction `𝔪 = 𝔫 ∩ A`, the induced maps `A ⧸ 𝔪ᵏ → B ⧸ 𝔪ᵏ B` are bijective for every
`k`. Then `B` is flat over `A`. The contraction `𝔪` need not be maximal, and no completion or
localisation of `A` or `B` enters the statement.

This is the criterion through which restriction maps of affinoid subdomains are flat: there the
bijections `A ⧸ 𝔪ᵏ ≃ B ⧸ 𝔪ᵏ B` come from the universal property alone.

## Implementation notes

By Mathlib's ideal criterion it suffices that `B ⊗[A] I → B` is injective for every ideal `I` of
`A`. Let `z` be in its kernel and fix a maximal ideal `𝔫` of `B` with contraction `𝔪`, and `j > 0`.
Artin–Rees gives `c` with `𝔪ᵏ ∩ I ⊆ 𝔪ʲ I` for `k = j + c`. Surjectivity of `A → B ⧸ 𝔪ᵏ B` writes
`z = 1 ⊗ i + w` with `i ∈ I` and `w ∈ 𝔪ᵏ (B ⊗[A] I)`. The image of `z` in `B` vanishes, so the
image of `i` lies in `𝔪ᵏ B`, and injectivity of `A ⧸ 𝔪ᵏ → B ⧸ 𝔪ᵏ B` puts `i` in `𝔪ᵏ ∩ I ⊆ 𝔪ʲ I`.
Hence `z ∈ 𝔫ʲ (B ⊗[A] I)`. Since `B ⊗[A] I` is a finite `B`-module and `𝔫` and `j` were arbitrary,
the separation of finite modules by powers of all maximal ideals gives `z = 0`.
-/

public section

open TensorProduct

namespace Module.Flat

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [IsNoetherianRing A] [IsNoetherianRing B]

/-- **Flatness from bijections on infinitesimal quotients.** If, for every maximal ideal `𝔫` of
`B` with contraction `𝔪` to `A`, the maps `A ⧸ 𝔪ᵏ → B ⧸ 𝔪ᵏ B` are bijective for all `k`, then
`B` is flat over `A`. -/
theorem of_bijective_quotientMap_pow
    (h : ∀ (n : Ideal B), n.IsMaximal → ∀ k : ℕ,
      Function.Bijective (Ideal.quotientMap ((n.comap (algebraMap A B) ^ k).map (algebraMap A B))
        (algebraMap A B) Ideal.le_comap_map)) :
    Module.Flat A B := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  rw [injective_iff_map_eq_zero]
  intro z hz
  -- The multiplication map `B ⊗[A] I → B`, as a `B`-linear map.
  let μ : B ⊗[A] I →ₗ[B] B :=
    (AlgebraTensorModule.rid A B B).toLinearMap ∘ₗ AlgebraTensorModule.lTensor B B I.subtype
  have hμz : μ z = 0 := by
    simp only [μ, LinearMap.coe_comp, Function.comp_apply, AlgebraTensorModule.coe_lTensor, hz,
      map_zero]
  have hμ (b : B) (i : I) : μ (b ⊗ₜ i) = algebraMap A B i * b := by
    simp [μ, Algebra.smul_def]
  suffices hz' : z ∈ (⨅ (n : Ideal B) (_ : n.IsMaximal) (j : ℕ) (_ : 0 < j),
      n ^ j • ⊤ : Submodule B (B ⊗[A] I)) by
    rwa [Ideal.iInf_isMaximal_pow_smul_eq_bot, Submodule.mem_bot] at hz'
  simp only [Submodule.mem_iInf]
  intro n hn j _
  set m := n.comap (algebraMap A B)
  have hmn : m.map (algebraMap A B) ≤ n := Ideal.map_comap_le
  obtain ⟨c, hc⟩ := TauCeti.ArtinRees.exists_controlled_lift m I
  set J := (m ^ (j + c)).map (algebraMap A B) with hJdef
  have hJ : J ≤ n ^ j := by
    rw [hJdef, Ideal.map_pow]
    exact (Ideal.pow_le_pow_right (Nat.le_add_right j c)).trans (Ideal.pow_right_mono hmn j)
  obtain ⟨hinj, hsurj⟩ := h n hn (j + c)
  -- Every element of `B ⊗[A] I` is `1 ⊗ i` modulo `J (B ⊗[A] I)`.
  obtain ⟨i, hi⟩ := exists_sub_one_tmul_mem_smul_top (fun b ↦ by
    obtain ⟨q, rfl⟩ := hsurj b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨a, by rw [RingHom.comp_apply, Ideal.quotientMap_mk]⟩) z
  -- The image of `i` in `B` lies in `J`, so `i ∈ 𝔪^(j + c)` by injectivity.
  have hiJ : algebraMap A B i ∈ J := by
    have hmap := Submodule.mem_map_of_mem (f := μ) hi
    rw [Submodule.map_smul''] at hmap
    have : μ (z - 1 ⊗ₜ i) ∈ J := by
      simpa [Ideal.smul_eq_mul] using
        IsConcreteLE.le_iff.mp (smul_mono_right J le_top) hmap
    simpa [hμz, hμ] using J.neg_mem_iff.mpr this
  have him : (i : A) ∈ m ^ (j + c) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply hinj
    rw [Ideal.quotientMap_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact hiJ
  -- Artin–Rees puts `i` into `𝔪ʲ I`.
  obtain ⟨i', hiI, hi'⟩ := hc LinearMap.id Function.surjective_id j i
    (by simpa [Ideal.smul_eq_mul] using him)
  rw [LinearMap.id_apply] at hi'
  rw [hi'] at hiI
  -- Hence `1 ⊗ i ∈ 𝔫ʲ (B ⊗[A] I)`.
  have h1i : (1 : B) ⊗ₜ[A] i ∈ (n ^ j • ⊤ : Submodule B (B ⊗[A] I)) := by
    refine Submodule.smul_mono_left ?_ (one_tmul_mem_map_smul_top hiI)
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hmn j
  have := add_mem (Submodule.smul_mono_left hJ hi) h1i
  rwa [sub_add_cancel] at this

end Module.Flat

namespace RingHom.Flat

variable {A B : Type*} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]

/-- **Flatness from bijections on infinitesimal quotients**, for a ring homomorphism. If, for
every maximal ideal `𝔫` of `B` with contraction `𝔪` along `f`, the maps `A ⧸ 𝔪ᵏ → B ⧸ 𝔪ᵏ B`
induced by `f` are bijective for all `k`, then `f` is flat. -/
theorem of_bijective_quotientMap_pow {f : A →+* B}
    (h : ∀ (n : Ideal B), n.IsMaximal → ∀ k : ℕ,
      Function.Bijective (Ideal.quotientMap ((n.comap f ^ k).map f) f Ideal.le_comap_map)) :
    f.Flat := by
  algebraize [f]
  exact Module.Flat.of_bijective_quotientMap_pow h

end RingHom.Flat
