/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Module
public import TauCeti.LinearAlgebra.TensorProduct.TensorKer
import TauCeti.LinearAlgebra.Exact
import TauCeti.RingTheory.LocalRing.Module

/-!
# Cohomology and base change over a local ring

Let `R` be a local ring with residue field `κ`, and let `f : M →ₗ[R] N` be a linear map from a
finite module to a finite projective module. This file proves the algebraic theorem on
cohomology and base change for the kernel of `f`, the comparison maps being Mathlib's
`LinearMap.tensorKer`, `P ⊗[R] ker f → ker (P ⊗ f)`:

* the comparison map for `P = κ` is surjective exactly when the cokernel `N ⧸ range f` is free;
* if it is surjective for `P = κ`, then it is bijective for every module `P`;
* in that case `M` is free exactly when `ker f` is free.

Applied to a complex `K₀ → K₁ → K₂ → K₃` with `K₁` finite and `K₂`, `K₃` finite projective, with
`f` the map `K₂ ⧸ range d₁ → K₃` induced by the last differential, `ker f` is the homology at
`K₂`, and `ker (P ⊗ f)` is the homology of the complex tensored with `P`
(`LinearMap.map_ker_lTensor_liftQ`), so `tensorKer` is the base change map on homology. The
results then read as Hartshorne's Theorem III.12.11 for the homology of a complex of finite
projective modules, such as Mumford's complex computing the cohomology of the fibres of a proper
flat family over the spectrum of a local ring:

* if the base change map `Hⁱ ⊗ κ → Hⁱ(K ⊗ κ)` is surjective, then `Hⁱ ⊗ P → Hⁱ(K ⊗ P)` is an
  isomorphism for every `P`;
* if this holds, the base change map `Hⁱ⁻¹ ⊗ κ → Hⁱ⁻¹(K ⊗ κ)` is surjective exactly when `Hⁱ`
  is free (`LinearMap.surjective_tensorKer_residueField_liftQ_iff_free_ker_liftQ`).

No Noetherian hypothesis is needed: finite generation of the source of `f` is what Nakayama's
lemma uses. The key input is Mathlib's `Module.free_of_lTensor_residueField_injective`: over a
local ring, a module with a finite presentation `range f → N → N ⧸ range f` whose first map stays
injective after tensoring with `κ` is free.

## Main results

* `LinearMap.surjective_tensorKer_residueField_iff_free_quotient_range`:
  `κ ⊗ ker f → ker (κ ⊗ f)` is surjective if and only if `N ⧸ range f` is free.
* `LinearMap.projective_range_of_surjective_tensorKer_residueField`: if it is surjective, then
  `range f` is projective.
* `LinearMap.bijective_tensorKer_of_surjective_tensorKer_residueField`: if
  `κ ⊗ ker f → ker (κ ⊗ f)` is surjective, then `P ⊗ ker f → ker (P ⊗ f)` is bijective for
  every `P`.
* `LinearMap.free_iff_free_ker_of_surjective_tensorKer_residueField`: if
  `κ ⊗ ker f → ker (κ ⊗ f)` is surjective, then `M` is free if and only if `ker f` is free.
* `LinearMap.surjective_tensorKer_residueField_liftQ_iff_free_ker_liftQ`: the second half of
  the theorem on cohomology and base change, for a complex of modules.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.12.11.
* D. Mumford, *Abelian Varieties*, Tata Institute, 1970, §5.
-/

public section

open TensorProduct IsLocalRing

namespace LinearMap

variable {R : Type*} [CommRing R] [IsLocalRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N] [Module.Projective R N]
  (f : M →ₗ[R] N)

/-- **The base change map to the residue field is surjective exactly when the cokernel is free.**
Over a local ring `R` with residue field `κ`, for a linear map `f : M → N` from a finite module to
a finite projective module, the comparison map `κ ⊗[R] ker f → ker (κ ⊗ f)` is surjective if and
only if the cokernel `N ⧸ range f` is free. -/
theorem surjective_tensorKer_residueField_iff_free_quotient_range :
    Function.Surjective (f.tensorKer (ResidueField R) (ResidueField R)) ↔
      Module.Free R (N ⧸ range f) := by
  have : Module.Free R N := Module.free_of_projective_of_isLocalRing
  rw [surjective_tensorKer_iff]
  exact ⟨Module.free_of_lTensor_residueField_injective _ _ (range f).mkQ_surjective
      (exact_subtype_mkQ _),
    fun _ ↦ lTensor_injective_of_exact_of_flat _ (range f).mkQ_surjective _
      (range f).injective_subtype (exact_subtype_mkQ _) _⟩

/-- **The image is projective when the base change map to the residue field is surjective.**
Over a local ring `R` with residue field `κ`, for a linear map `f : M → N` from a finite module to
a finite projective module, if `κ ⊗[R] ker f → ker (κ ⊗ f)` is surjective then `range f` is a
direct summand of `N`, hence projective. -/
theorem projective_range_of_surjective_tensorKer_residueField
    (h : Function.Surjective (f.tensorKer (ResidueField R) (ResidueField R))) :
    Module.Projective R (range f) := by
  have : Module.Free R N := Module.free_of_projective_of_isLocalRing
  obtain ⟨r, hr⟩ := (split_injective_iff_lTensor_residueField_injective (range f).subtype).mpr
    ((surjective_tensorKer_iff _ _ f).mp h)
  exact Module.Projective.of_split _ r hr

/-- **Cohomology and base change: surjectivity at the residue field gives bijectivity.** Over a
local ring `R` with residue field `κ`, let `f : M → N` be a linear map from a finite module to a
finite projective module. If the comparison map `κ ⊗[R] ker f → ker (κ ⊗ f)` is surjective, then
`P ⊗[R] ker f → ker (P ⊗ f)` is bijective for every module `P`. -/
theorem bijective_tensorKer_of_surjective_tensorKer_residueField
    (h : Function.Surjective (f.tensorKer (ResidueField R) (ResidueField R)))
    (S P : Type*) [CommRing S] [Algebra R S] [AddCommGroup P] [Module R P] [Module S P]
    [IsScalarTower R S P] :
    Function.Bijective (f.tensorKer S P) := by
  have := (surjective_tensorKer_residueField_iff_free_quotient_range f).mp h
  have := projective_range_of_surjective_tensorKer_residueField f h
  exact bijective_tensorKer_of_flat S P f

/-- **Cohomology and base change: freeness of the kernel.** Over a local ring `R` with residue
field `κ`, let `f : M → N` be a linear map from a finite module to a finite projective module such
that the comparison map `κ ⊗[R] ker f → ker (κ ⊗ f)` is surjective. Then `M` is free if and only
if `ker f` is free: the image of `f` is projective, so `M ≅ ker f × range f`. -/
theorem free_iff_free_ker_of_surjective_tensorKer_residueField
    (h : Function.Surjective (f.tensorKer (ResidueField R) (ResidueField R))) :
    Module.Free R M ↔ Module.Free R (ker f) := by
  have := projective_range_of_surjective_tensorKer_residueField f h
  -- The surjection `M → range f` onto a projective module splits, so `M ≅ ker f × range f`.
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f.rangeRestrict LinearMap.id
    f.surjective_rangeRestrict
  let e : M ≃ₗ[R] ker f × range f :=
    ((exact_subtype_rangeRestrict f).splitSurjectiveEquiv (ker f).injective_subtype ⟨s, hs⟩).val
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have : Module.Projective R (ker f) :=
      .of_split (e.symm.toLinearMap ∘ₗ inl R _ _) (fst R _ _ ∘ₗ e.toLinearMap) (by ext; simp)
    have : Module.Finite R (ker f) :=
      .of_surjective (fst R _ _ ∘ₗ e.toLinearMap) fun x ↦ ⟨e.symm (x, 0), by simp⟩
    exact Module.free_of_projective_of_isLocalRing
  · have : Module.Projective R M := .of_equiv e.symm
    exact Module.free_of_projective_of_isLocalRing

variable {K₀ K₁ K₂ K₃ : Type*} [AddCommGroup K₀] [Module R K₀] [AddCommGroup K₁] [Module R K₁]
  [AddCommGroup K₂] [Module R K₂] [AddCommGroup K₃] [Module R K₃] [Module.Finite R K₁]
  [Module.Finite R K₂] [Module.Projective R K₂] [Module.Finite R K₃] [Module.Projective R K₃]
  (d₀ : K₀ →ₗ[R] K₁) (d₁ : K₁ →ₗ[R] K₂) (d₂ : K₂ →ₗ[R] K₃)

/-- **Cohomology and base change for a complex: the previous degree.** Over a local ring `R`
with residue field `κ`, let `K₀ → K₁ → K₂ → K₃` be a complex with differentials `d₀`, `d₁`, `d₂`,
with `K₁` finite and `K₂`, `K₃` finite projective. The homology at `K₂` is the kernel of the map
`K₂ ⧸ range d₁ → K₃` induced by `d₂`, and that at `K₁` the kernel of the map `K₁ ⧸ range d₀ → K₂`
induced by `d₁`; for each, `LinearMap.tensorKer` is the base change map on homology. If the base
change map `κ ⊗ H(K₂) → H(κ ⊗ K₂)` is surjective, then the base change map
`κ ⊗ H(K₁) → H(κ ⊗ K₁)` is surjective if and only if the homology `H(K₂)` is free. -/
theorem surjective_tensorKer_residueField_liftQ_iff_free_ker_liftQ (h₀₁ : range d₀ ≤ ker d₁)
    (h₁₂ : range d₁ ≤ ker d₂)
    (h : Function.Surjective
      (((range d₁).liftQ d₂ h₁₂).tensorKer (ResidueField R) (ResidueField R))) :
    Function.Surjective
        (((range d₀).liftQ d₁ h₀₁).tensorKer (ResidueField R) (ResidueField R)) ↔
      Module.Free R (ker ((range d₁).liftQ d₂ h₁₂)) := by
  rw [surjective_tensorKer_residueField_iff_free_quotient_range, Submodule.range_liftQ,
    free_iff_free_ker_of_surjective_tensorKer_residueField _ h]

end LinearMap
