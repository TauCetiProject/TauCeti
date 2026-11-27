/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Morita.Auslander
import TauCeti.Algebra.Category.FGModuleCat.End
import TauCeti.Algebra.Module.Projective.Complement
import TauCeti.CategoryTheory.Preadditive.Projectivization.SelfInjective

/-!
# The dimensions of nonsemisimple Auslander algebras

If a ring has finite global dimension and its dominant dimension exceeds that bound, then
the regular module is injective. For an endomorphism ring of an additive generator of `mod A`,
left self-injectivity would force the cyclic quotients of `A` to split, making `A` semisimple.
Consequently, for a nonsemisimple Artin algebra with an additive generator, its Auslander algebra
has global and dominant dimension exactly two.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), §VI.5, Proposition VI.5.4(a).
-/

public section

open CategoryTheory

namespace TauCeti

universe u v w

/-- If an Auslander algebra is not left self-injective, its global and dominant dimensions are
both two. -/
theorem IsAuslanderAlgebra.globalDimension_eq_two_and_dominantDimension_eq_two
    {Γ : Type w} [Ring Γ] (hΓ : IsAuslanderAlgebra Γ) (hinj : ¬ Module.Injective Γ Γ) :
    globalDimension.{w} Γ = 2 ∧ dominantDimension Γ = 2 := by
  obtain ⟨hgl, hdom⟩ := isAuslanderAlgebra_iff.mp hΓ
  have hdom_le : dominantDimension Γ ≤ 2 :=
    dominantDimension_le_of_globalDimension_le (n := 2) (by simpa using hgl) hinj
  refine ⟨le_antisymm hgl (le_of_not_gt fun hlt ↦ ?_), le_antisymm hdom_le hdom⟩
  have hgl_one : globalDimension.{w} Γ ≤ 1 :=
    ENat.WithBot.lt_add_one_iff.mp (by simpa [one_add_one_eq_two] using hlt)
  have hdom_one : dominantDimension Γ ≤ 1 :=
    dominantDimension_le_of_globalDimension_le (n := 1) (by simpa using hgl_one) hinj
  exact (by decide : ¬ (2 : ℕ∞) ≤ 1) (hdom.trans hdom_one)

/-- If the endomorphism ring of an additive generator of finitely generated left `A`-modules is
left self-injective, then `A` is semisimple. -/
theorem IsAdditiveGenerator.isSemisimpleRing_of_injective_end {A : Type v} [Ring A]
    [Small.{w} A] {M : FGModuleCat.{w} A} (hM : IsAdditiveGenerator M)
    (hinj : Module.Injective (Module.End A M.obj) (Module.End A M.obj)) : IsSemisimpleRing A := by
  let e := (FGModuleCat.endRingEquiv M).symm
  have hEnd : Module.Injective (End M) (End M) :=
    Module.Injective.of_ringEquiv e e.toSemilinearEquiv
  refine (isSemisimpleModule_iff A A).mpr ⟨fun I ↦ ?_⟩
  -- Bring the quotient map into the module universe of `M` before applying projectivization.
  let eA := Shrink.linearEquiv.{w} A A
  let eQ := Shrink.linearEquiv.{w} A (A ⧸ I)
  let q := eQ.symm.toLinearMap ∘ₗ I.mkQ ∘ₗ eA.toLinearMap
  let f := FGModuleCat.ofHom q
  have hf : Function.Surjective q := eQ.symm.surjective.comp (I.mkQ_surjective.comp eA.surjective)
  have : Epi f := (ModuleCat.isFG A).ι.epi_of_epi_map ((ModuleCat.epi_iff_surjective _).2 hf)
  have := isSplitEpi_of_injective_end (hM.additiveClosure _) (hM.additiveClosure _) hEnd f
  let s := (section_ f).hom.hom
  have hs (x : Shrink.{w} (A ⧸ I)) : q (s x) = x := by
    simpa only [s, f, FGModuleCat.hom_hom_comp, FGModuleCat.hom_hom_ofHom, FGModuleCat.hom_hom_id,
      LinearMap.comp_apply, LinearMap.id_apply] using
      LinearMap.congr_fun (congrArg (fun g ↦ g.hom.hom) (IsSplitEpi.id f)) x
  let t := eA.toLinearMap ∘ₗ s ∘ₗ eQ.symm.toLinearMap
  have ht : I.mkQ ∘ₗ t = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact eQ.symm.injective (by simpa only [q, t, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.id_apply] using hs (eQ.symm x))
  have : Module.Projective A (A ⧸ I) := Module.Projective.of_split t I.mkQ ht
  exact I.isComplemented_of_projective_quotient

/-- **Auslander, Reiten and Smalø, Proposition VI.5.4(a).** The endomorphism ring of an additive
generator of a nonsemisimple Artin algebra has global dimension two and dominant dimension two. -/
theorem IsAdditiveGenerator.globalDimension_end_eq_two_and_dominantDimension_end_eq_two
    (R : Type u) [CommRing R] [IsArtinianRing R] {A : Type v} [Ring A] [Algebra R A]
    [Module.Finite R A] [Small.{w} A] {M : FGModuleCat.{w} A} (hM : IsAdditiveGenerator M)
    (hA : ¬ IsSemisimpleRing A) :
    globalDimension.{w} (Module.End A M.obj) = 2 ∧ dominantDimension (Module.End A M.obj) = 2 :=
  (isAuslanderAlgebra_end R M hM).globalDimension_eq_two_and_dominantDimension_eq_two
    fun hinj ↦ hA (hM.isSemisimpleRing_of_injective_end hinj)

end TauCeti
