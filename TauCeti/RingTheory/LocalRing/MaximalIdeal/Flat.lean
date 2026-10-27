/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.SpanRankOperations
public import Mathlib.RingTheory.Ideal.CotangentBaseChange

/-!
# Generators of the maximal ideal along flat local homomorphisms

Let `R → S` be a flat homomorphism of Noetherian local rings under which the maximal ideal `𝔪_R`
of `R` generates the maximal ideal `𝔪_S` of `S`. Then `𝔪_R` and `𝔪_S` need the same number of
generators. One inequality holds without flatness, since the images of generators of `𝔪_R`
generate `𝔪_S`. For the other, the images of elements of `𝔪_R` that are linearly independent in
`𝔪_R / 𝔪_R²` remain linearly independent in `𝔪_S / 𝔪_S²`. This follows from Mathlib's flat base
change of cotangent spaces, `Ideal.tensorCotangentHom_injective_of_flat`: a relation modulo
`𝔪_S² = 𝔪_R² S` among them gives a vanishing element of `S ⊗[R] 𝔪_R / 𝔪_R²`, whose coefficients
all lie in `𝔪_R S = 𝔪_S`.

The basic example is the completion of a Noetherian local ring at its maximal ideal, where Mathlib
proves the same equality as `AdicCompletion.spanFinrank_maximalIdeal_eq`.

## Main results

* `TauCeti.IsLocalRing.spanFinrank_maximalIdeal_eq_of_flat_of_map_maximalIdeal_eq`: the maximal
  ideals of `R` and `S` have the same minimal number of generators.
-/

public section

namespace TauCeti.IsLocalRing

open _root_.IsLocalRing TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]

/-- Along a flat homomorphism of Noetherian local rings under which the maximal ideal of `R`
generates the maximal ideal of `S`, the two maximal ideals have the same minimal number of
generators. -/
theorem spanFinrank_maximalIdeal_eq_of_flat_of_map_maximalIdeal_eq [IsNoetherianRing R]
    [IsNoetherianRing S] [Module.Flat R S]
    (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    (maximalIdeal S).spanFinrank = (maximalIdeal R).spanFinrank := by
  refine le_antisymm (h ▸ Ideal.spanFinrank_map_le_of_fg _ (maximalIdeal R).fg_of_isNoetherianRing)
    ?_
  have : IsLocalHom (algebraMap R S) := ((local_hom_TFAE (algebraMap R S)).out 1 3).mpr h.le
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
    spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  -- Lift a basis of `𝔪_R / 𝔪_R²` to elements `xᵢ ∈ 𝔪_R`.
  let b := Module.finBasis (ResidueField R) (CotangentSpace R)
  choose x hx using fun i ↦ (maximalIdeal R).toCotangent_surjective (b i)
  have hxS (i) : algebraMap R S (x i) ∈ maximalIdeal S := h ▸ Ideal.mem_map_of_mem _ (x i).2
  -- The images of the `xᵢ` in `𝔪_S / 𝔪_S²` are linearly independent.
  suffices LinearIndependent (ResidueField S)
      fun i ↦ (maximalIdeal S).toCotangent ⟨_, hxS i⟩ by
    simpa using this.fintype_card_le_finrank
  refine Fintype.linearIndependent_iff.mpr fun g hg i ↦ ?_
  choose s hs using fun i ↦ residue_surjective (g i)
  have hsum : ∑ i, s i * algebraMap R S (x i) ∈ maximalIdeal S ^ 2 := by
    simp only [← hs, ← ResidueField.algebraMap_eq, algebraMap_smul, ← map_smul, ← map_sum,
      Ideal.toCotangent_eq_zero] at hg
    simpa using hg
  -- By flat base change of cotangent spaces, `∑ sᵢ ⊗ xᵢ` vanishes in `S ⊗[R] 𝔪_R / 𝔪_R²`.
  have ht : ∑ j, s j ⊗ₜ[R] (maximalIdeal R).toCotangent (x j) = 0 := by
    apply Ideal.tensorCotangentHom_injective_of_flat R S (maximalIdeal R)
    simp only [map_sum, map_zero, Ideal.tensorCotangentHom_tmul, ← LinearMap.map_smul_of_tower]
    rw [← map_sum, Ideal.toCotangent_eq_zero, Submodule.coe_sum]
    -- Transport the membership along `S ⊗[R] R ≃ S`.
    let e := (Algebra.TensorProduct.rid R S S).toRingEquiv
    have he : (e : S ⊗[R] R →+* S).comp Algebra.TensorProduct.includeRight.toRingHom =
        algebraMap R S := by ext; simp [e, Algebra.smul_def]
    have hJ : ((maximalIdeal R).map Algebra.TensorProduct.includeRight.toRingHom ^ 2).map e =
        maximalIdeal S ^ 2 := by
      rw [Ideal.map_pow, ← h, ← he, ← Ideal.map_map, Ideal.map_coe]
    rw [← Ideal.apply_mem_of_equiv_iff (f := e), hJ]
    simp only [Submodule.coe_smul_of_tower, TensorProduct.smul_tmul', smul_eq_mul, mul_one, map_sum]
    simpa [e, Algebra.smul_def, mul_comm] using hsum
  -- Its `i`-th coordinate is the residue of `sᵢ`.
  let φ : CotangentSpace R →ₗ[R] ResidueField S :=
    ((Algebra.linearMap (ResidueField R) (ResidueField S)) ∘ₗ b.coord i).restrictScalars R
  have := congr(LinearMap.liftBaseChange S φ $ht)
  simp only [LinearMap.restrictScalars_comp, hx, map_sum, LinearMap.liftBaseChange_tmul,
    LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
    Algebra.linearMap_apply, MonoidWithZeroHom.map_ite_one_zero, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, map_zero, φ] at this
  rwa [← hs, ← ResidueField.algebraMap_eq, ← mul_one (algebraMap _ _ _), ← Algebra.smul_def]

end TauCeti.IsLocalRing
