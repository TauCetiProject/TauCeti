/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Finite projective dimension over a local ring of depth zero

Let `R` be a Noetherian local ring whose maximal ideal `𝔪` is an associated prime of `R`, that is,
of depth zero: some nonzero `s ∈ R` satisfies `𝔪 s = 0`. Then every finite `R`-module of finite
projective dimension is free. This is the depth-zero case of the Auslander–Buchsbaum formula
`pd M + depth M = depth R`.

The embedding `κ → R`, `1 ↦ s`, of the residue field stays injective after tensoring with a flat
module, so `κ ⊗ -` preserves injectivity of maps out of flat modules. For a presentation
`0 → K → F → M → 0` with `F` finite free and `K` free by induction on the projective dimension,
`κ ⊗ K → κ ⊗ F` is therefore injective, and `M` is free by Nakayama's lemma.

This is the base case of Serre's theorem that a Noetherian local ring whose residue field has
finite projective dimension is regular.

## Main results

* `LinearMap.lTensor_residueField_injective_of_maximalIdeal_mem_associatedPrimes`: over a local
  ring of depth zero, `κ ⊗ -` preserves injectivity of linear maps out of flat modules.
* `Module.free_of_hasProjectiveDimensionLE_of_maximalIdeal_mem_associatedPrimes`: over a
  Noetherian local ring of depth zero, a finite module of finite projective dimension is free.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 19.1 (the Auslander–Buchsbaum formula).
-/

public section

universe v u

open CategoryTheory IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Over a local ring whose maximal ideal is an associated prime, tensoring with the residue
field preserves injectivity of linear maps out of flat modules. -/
theorem LinearMap.lTensor_residueField_injective_of_maximalIdeal_mem_associatedPrimes
    (hm : maximalIdeal R ∈ associatedPrimes R R)
    {K F : Type*} [AddCommGroup K] [Module R K] [Module.Flat R K] [AddCommGroup F] [Module R F]
    {l : K →ₗ[R] F} (hl : Function.Injective l) :
    Function.Injective (l.lTensor (ResidueField R)) := by
  obtain ⟨-, ι, hι⟩ := (isAssociatedPrime_iff_exists_injective_linearMap _ _).mp hm
  -- `κ ⊗ K → κ ⊗ F → R ⊗ F` equals `κ ⊗ K → R ⊗ K → R ⊗ F`, injective as `K` is flat.
  have h := (Module.Flat.lTensor_preserves_injective_linearMap (M := R) l hl).comp
    (Module.Flat.rTensor_preserves_injective_linearMap (M := K) ι hι)
  rw [← LinearMap.coe_comp, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
    LinearMap.coe_comp] at h
  exact h.of_comp

/-- **Finite projective dimension in depth zero.** Over a Noetherian local ring whose maximal
ideal is an associated prime, a finite module of finite projective dimension is free. -/
theorem Module.free_of_hasProjectiveDimensionLE_of_maximalIdeal_mem_associatedPrimes
    [Small.{v} R] (hm : maximalIdeal R ∈ associatedPrimes R R) (n : ℕ)
    (M : ModuleCat.{v} R) [Module.Finite R M] [HasProjectiveDimensionLE M n] :
    Module.Free R M := by
  induction n generalizing M with
  | zero =>
    have : CategoryTheory.Projective M := projective_iff_hasProjectiveDimensionLT_one.mpr ‹_›
    have : Module.Projective R M := M.projective_of_module_projective
    exact Module.free_of_flat_of_isLocalRing
  | succ n ih =>
    -- A presentation `0 → K → F → M → 0` with `F` finite free; `K` is free by induction.
    obtain ⟨F, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
    have hS := LinearMap.shortExact_shortComplexKer hf
    have : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker f)) n :=
      hS.hasProjectiveDimensionLT_X₁ (n + 1) inferInstance ‹_›
    have := ih (ModuleCat.of R (LinearMap.ker f))
    exact Module.free_of_lTensor_residueField_injective _ f hf f.exact_subtype_ker_map
      (LinearMap.lTensor_residueField_injective_of_maximalIdeal_mem_associatedPrimes hm
        (LinearMap.ker f).injective_subtype)
