/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Support

/-!
# Surjectivity and bijectivity of linear maps on fibres

For a prime `p` of a commutative ring `R`, the fibre of an `R`-module `M` at `p` is
`κ(p) ⊗[R] M`, with `κ(p)` the residue field. A linear map into a finite module is surjective iff
it is surjective on every fibre: the cokernel is finite with zero fibres, so it vanishes by
Nakayama's lemma (`Module.subsingleton_iff_forall_subsingleton_residueField_tensorProduct`,
`LinearMap.surjective_iff_forall_surjective_lTensor_residueField`).

If moreover the target is projective, the same holds for bijectivity
(`LinearMap.bijective_iff_forall_bijective_lTensor_residueField`): a surjection onto a projective
module splits, so its kernel is a finite direct summand of the source whose fibres are the kernels
of the fibre maps. Thus a map between finite projective modules, for instance a bilinear pairing
read as a map into the dual, is an isomorphism exactly when it is one at every point of
`Spec R`.

## References

* The Stacks Project, Lemma 10.20.1 (00DV), Nakayama's lemma.
-/

public section

open scoped TensorProduct

namespace Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A finite module is zero iff its fibres at all primes vanish. -/
theorem subsingleton_iff_forall_subsingleton_residueField_tensorProduct [Module.Finite R M] :
    Subsingleton M ↔ ∀ p : PrimeSpectrum R, Subsingleton (p.asIdeal.ResidueField ⊗[R] M) := by
  refine ⟨fun _ _ ↦ inferInstance, fun h ↦ ?_⟩
  refine (support_eq_empty_iff (R := R)).mp (Set.eq_empty_iff_forall_notMem.mpr fun p hp ↦ ?_)
  rw [mem_support_iff_nontrivial_residueField_tensorProduct] at hp
  exact not_nontrivial_iff_subsingleton.mpr (h p) hp

end Module

namespace LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A linear map into a finite module is surjective iff it is surjective on the fibre at every
prime. -/
theorem surjective_iff_forall_surjective_lTensor_residueField [Module.Finite R N]
    (f : M →ₗ[R] N) :
    Function.Surjective f ↔
      ∀ p : PrimeSpectrum R, Function.Surjective (f.lTensor p.asIdeal.ResidueField) := by
  refine ⟨fun hf p ↦ lTensor_surjective _ hf, fun h ↦ ?_⟩
  -- The cokernel of `f` is finite, and its fibres vanish by right exactness of `κ(p) ⊗ -`.
  rw [← range_eq_top, ← Submodule.Quotient.subsingleton_iff]
  refine (Module.subsingleton_iff_forall_subsingleton_residueField_tensorProduct (R := R)).mpr
    fun p ↦ ⟨fun x y ↦ ?_⟩
  have hzero (z : p.asIdeal.ResidueField ⊗[R] (N ⧸ range f)) : z = 0 := by
    obtain ⟨n, rfl⟩ := lTensor_surjective p.asIdeal.ResidueField (range f).mkQ_surjective z
    obtain ⟨m, rfl⟩ := h p n
    rw [← comp_apply, ← lTensor_comp, range_mkQ_comp, lTensor_zero, LinearMap.zero_apply]
  rw [hzero x, hzero y]

/-- A linear map from a finite module to a finite projective module is bijective iff it is
bijective on the fibre at every prime. -/
theorem bijective_iff_forall_bijective_lTensor_residueField [Module.Finite R M] [Module.Finite R N]
    [Module.Projective R N] (f : M →ₗ[R] N) :
    Function.Bijective f ↔
      ∀ p : PrimeSpectrum R, Function.Bijective (f.lTensor p.asIdeal.ResidueField) := by
  refine ⟨fun hf p ↦ ((LinearEquiv.ofBijective f hf).lTensor p.asIdeal.ResidueField).bijective,
    fun h ↦ ?_⟩
  have hsurj : Function.Surjective f :=
    (surjective_iff_forall_surjective_lTensor_residueField f).mpr fun p ↦ (h p).2
  refine ⟨?_, hsurj⟩
  -- `f` has a section `s` since `N` is projective, so `x ↦ x - s (f x)` retracts `M` onto the
  -- kernel `K` of `f`. Hence `κ(p) ⊗ K → κ(p) ⊗ M` is injective, and its composite with the
  -- injective map `κ(p) ⊗ f` vanishes, so the finite module `K` has zero fibres.
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hsurj
  have : Module.FinitePresentation R N := Module.finitePresentation_of_projective R N
  have : Module.Finite R (ker f) :=
    Module.Finite.iff_fg.mpr (Module.FinitePresentation.fg_ker f hsurj)
  let r : M →ₗ[R] ker f := codRestrict (ker f) (LinearMap.id - s ∘ₗ f) fun x ↦ by
    simp [← comp_apply f s, hs]
  have hr : r ∘ₗ (ker f).subtype = LinearMap.id := by
    ext ⟨x, hx⟩
    simp [r, mem_ker.mp hx]
  rw [← ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
  refine (Module.subsingleton_iff_forall_subsingleton_residueField_tensorProduct (R := R)).mpr
    fun p ↦ ?_
  have hinj : Function.Injective ((ker f).subtype.lTensor p.asIdeal.ResidueField) := by
    refine Function.LeftInverse.injective (g := r.lTensor p.asIdeal.ResidueField) fun z ↦ ?_
    rw [← comp_apply, ← lTensor_comp, hr, lTensor_id, id_apply]
  have hzero : f.lTensor p.asIdeal.ResidueField ∘ₗ (ker f).subtype.lTensor p.asIdeal.ResidueField
      = 0 := by
    rw [← lTensor_comp, comp_ker_subtype, lTensor_zero]
  refine ⟨fun x y ↦ hinj ((h p).1 ?_)⟩
  rw [← comp_apply (f.lTensor _), ← comp_apply (f.lTensor _), hzero, LinearMap.zero_apply,
    LinearMap.zero_apply]

end LinearMap
