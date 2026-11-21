/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Generator.Cogenerator
public import TauCeti.RingTheory.DominantDimension

import TauCeti.Algebra.Module.Injective.Envelope.Existence
import TauCeti.Algebra.Subalgebra.Center
import TauCeti.LinearAlgebra.Exact
import TauCeti.RingTheory.Artinian.Subalgebra
import TauCeti.RingTheory.MatlisDuality.Cogenerator

/-!
# The endomorphism ring of a generator-cogenerator has dominant dimension at least two

Let `A` be an Artin algebra and `M` a generator-cogenerator of `mod A`, with endomorphism ring
`Γ = Module.End A M` acting on `M` by evaluation. This file proves the forward direction of the
Morita-Tachikawa correspondence: `Γ` has dominant dimension at least two
(`TauCeti.two_le_dominantDimension_end`).

The proof follows Müller. As a generator, `M` is a finitely generated projective `Γ`-module
(`TauCeti.Module.IsGenerator.finite_end` and `TauCeti.Module.IsGenerator.projective_end`). As a
cogenerator, `M` is an injective `Γ`-module
(`TauCeti.IsInjectiveEnvelope.injective_end_of_isCoseparator`), being the Matlis dual of the
projective right `Γ`-module `D M` (`TauCeti.MatlisDual.injective_end_of_sum_comp_eq_id`). A
presentation `Aᵐ → Aⁿ → M → 0` and the left exact functor `Hom_A(-, M)` then give an exact sequence
`0 → Γ → Hom_A(Aⁿ, M) → Hom_A(Aᵐ, M)` of `Γ`-modules, whose last two terms are isomorphic to `Mⁿ`
and `Mᵐ`, hence finitely generated, projective and injective. This last step holds for a finitely
generated generator over any left Noetherian ring
(`TauCeti.two_le_dominantDimension_end_of_isGenerator`).

## Main results

* `TauCeti.two_le_dominantDimension_end_of_isGenerator`: over a left Noetherian ring, the
  endomorphism ring of a finitely generated generator that is injective over it has dominant
  dimension at least two.
* `TauCeti.IsInjectiveEnvelope.injective_end_of_isCoseparator`: a coseparator of `mod A` is an
  injective module over its endomorphism ring.
* `TauCeti.two_le_dominantDimension_end`: **the Morita-Tachikawa correspondence, forward
  direction**: the endomorphism ring of a generator-cogenerator has dominant dimension at least
  two.

## References

* B. J. Müller, *The classification of algebras by dominant dimension*, Canad. J. Math. 20 (1968),
  398–409, Theorem 2.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  Studies in Advanced Mathematics 36, CUP (1995), Proposition VI.5.4(a).
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory

universe u v

section Artin

attribute [local instance] ModuleCat.moduleOfAlgebra ModuleCat.isScalarTower_moduleOfAlgebra

variable {R : Type u} [CommRing R] [IsArtinianRing R] {E : Type v} [AddCommGroup E] [Module R E]
  [Small.{v} R] {f : R ⧸ Ring.jacobson R →ₗ[R] E} {A : Type v} [Ring A] [Algebra R A]
  [Module.Finite R A]

/-- **A coseparator is injective over its endomorphism ring**: for a coseparator `M` of `mod A`,
`M` is an injective module over `Module.End A M`. This is the dual of the statement that a
generator is projective over its endomorphism ring. -/
theorem IsInjectiveEnvelope.injective_end_of_isCoseparator (hf : IsInjectiveEnvelope f)
    {M : FGModuleCat.{v} A} (hM : IsCoseparator M) :
    Module.Injective (Module.End A M.obj) M.obj := by
  have := hf.moduleInjective
  obtain ⟨n, a, b, hab⟩ := additiveClosure_iff_exists_sum_comp_eq_id.1
    ((hf.isCoseparator_iff_additiveClosure M).1 hM)
  let e := hf.fgModuleCatMatlisDualRegularEquiv (A := A)
  refine MatlisDual.injective_end_of_sum_comp_eq_id hf.length_quotient_linearMap_eq_one
    (isFiniteLength_of_finite_trans R A M.obj) (fun j ↦ (a j).hom.hom ∘ₗ e.symm.toLinearMap)
    (fun j ↦ e.toLinearMap ∘ₗ (b j).hom.hom) (LinearMap.ext fun x ↦ ?_)
  -- The forgetful functor to `ModuleCat A` is additive, so it carries the sum to a sum.
  have h := congr(((ObjectProperty.ι _).map $hab).hom (e.symm x))
  simp only [Functor.map_sum, Functor.map_comp, ModuleCat.hom_sum] at h
  simpa using congr(e $h)

end Artin

section Hom

variable {A : Type v} [Ring A] {M : Type v} [AddCommGroup M] [Module A M]

/-- For a module `M` that is finitely generated, projective and injective over its endomorphism
ring `Γ`, the `Γ`-module `Hom_A(Aⁿ, M) ≅ Mⁿ` is too, as an object of `ModuleCat Γ`. -/
private theorem finite_projective_injective_linearMap (n : ℕ)
    [Module.Finite (Module.End A M) M] [Module.Projective (Module.End A M) M]
    [Module.Injective (Module.End A M) M] :
    Module.Finite (Module.End A M) ((Fin n → A) →ₗ[A] M) ∧
      Projective (ModuleCat.of (Module.End A M) ((Fin n → A) →ₗ[A] M)) ∧
        Injective (ModuleCat.of (Module.End A M) ((Fin n → A) →ₗ[A] M)) := by
  let e := LinearEquiv.piRing A M (Fin n) (Module.End A M)
  have : Module.Projective (Module.End A M) ((Fin n → A) →ₗ[A] M) := .of_equiv e.symm
  have : Module.Injective (Module.End A M) ((Fin n → A) →ₗ[A] M) :=
    ((Module.Baer.of_injective inferInstance).of_equiv e.symm).injective
  exact ⟨.equiv e.symm, (IsProjective.iff_projective _).1 inferInstance,
    Module.injective_object_of_injective_module _ _⟩

/-- Precomposition with `q : F → M`, as a map `Γ → Hom_A(F, M)` of `Γ`-modules, where `Γ` acts on
`Hom_A(F, M)` by postcomposition. -/
private def precomp {F : Type*} [AddCommGroup F] [Module A F] (q : F →ₗ[A] M) :
    Module.End A M →ₗ[Module.End A M] (F →ₗ[A] M) where
  toFun g := g ∘ₗ q
  map_add' _ _ := LinearMap.add_comp _ _ _
  map_smul' _ _ := rfl

end Hom

/-- **Müller's criterion, forward direction, for a generator.** Let `A` be a left Noetherian ring
and `M` a finitely generated generator of the category of `A`-modules that is injective over its
endomorphism ring `Γ`. Then `Γ` has dominant dimension at least two: a presentation
`Aᵐ → Aⁿ → M → 0` gives the exact sequence `0 → Γ → Hom_A(Aⁿ, M) → Hom_A(Aᵐ, M)`, whose last two
terms are isomorphic to `Mⁿ` and `Mᵐ`. -/
theorem two_le_dominantDimension_end_of_isGenerator {A : Type v} [Ring A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.IsGenerator A M]
    [Module.Injective (Module.End A M) M] : 2 ≤ dominantDimension (Module.End A M) := by
  -- A presentation `Aᵐ → Aⁿ → M → 0`; the kernel of `q` is finitely generated as `A` is Noetherian.
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' A M
  obtain ⟨m, r', hr'⟩ := Module.Finite.exists_fin' A (LinearMap.ker q)
  let r := (LinearMap.ker q).subtype ∘ₗ r'
  have hqr : Function.Exact r q := fun x ↦ ⟨fun h ↦ (hr' ⟨x, h⟩).imp fun _ hy ↦
    congr_arg Subtype.val hy, fun ⟨y, hy⟩ ↦ hy ▸ (r' y).property⟩
  -- Applying `Hom_A(-, M)` gives `0 → Γ → Hom_A(Aⁿ, M) → Hom_A(Aᵐ, M)`.
  have hex := hqr.lcomp_of_surjective (T := Module.End A M) M hq
  refine (two_le_dominantDimension_iff _).2 ⟨_, _, ModuleCat.ofHom (precomp q),
    ModuleCat.ofHom (LinearMap.lcomp _ M r), ?_, ?_, ?_,
    finite_projective_injective_linearMap n, finite_projective_injective_linearMap m⟩
  · refine ModuleCat.hom_ext (LinearMap.ext fun g ↦ LinearMap.ext fun x ↦ ?_)
    simp [precomp, hqr.apply_apply_eq_zero]
  · exact (ModuleCat.mono_iff_injective _).2 hq.injective_linearMapComp_right
  · exact (ShortComplex.moduleCat_exact_iff _).2 fun g hg ↦ (hex g).1 hg

/-- **The Morita-Tachikawa correspondence, forward direction.** The endomorphism ring of a
generator-cogenerator `M` of `mod A`, for an Artin algebra `A`, has dominant dimension at least two.
The base ring `R` may live in any universe. -/
theorem two_le_dominantDimension_end (R : Type u) [CommRing R] [IsArtinianRing R]
    {A : Type v} [Ring A] [Algebra R A] [Module.Finite R A] (M : FGModuleCat.{v} A)
    (hM : IsGeneratorCogenerator M) : 2 ≤ dominantDimension (Module.End A M.obj) := by
  obtain ⟨hs, hc⟩ := isGeneratorCogenerator_iff.1 hM
  have := IsArtinianRing.of_finite R A
  have : Module.IsGenerator A M.obj := FGModuleCat.isGenerator_of_isSeparator hs
  -- Replace `R` by the centre `C` of `A`, which lives in the universe of `A`, and take an injective
  -- hull of `C ⧸ J(C)` there.
  let C := Subalgebra.center R A
  have : Module.Finite C A := Subalgebra.finite_centerAlgebra_of_finite
  obtain ⟨E, _, _, i, hi⟩ := exists_isInjectiveEnvelope C (C ⧸ Ring.jacobson C)
  have := hi.injective_end_of_isCoseparator hc
  exact two_le_dominantDimension_end_of_isGenerator M.obj

end TauCeti
