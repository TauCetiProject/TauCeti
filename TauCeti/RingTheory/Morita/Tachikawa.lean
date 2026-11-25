/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Generator.Basic
public import TauCeti.RingTheory.DominantDimension

import Mathlib.RingTheory.HopkinsLevitzki
import TauCeti.Algebra.Category.FGModuleCat.Generator.Endomorphism
import TauCeti.Algebra.Module.Injective.Copresentation.DoubleCentralizer
import TauCeti.RingTheory.Noetherian.LinearMap

/-!
# The Morita-Tachikawa correspondence

Let `A` be an Artin algebra and `M` a generator-cogenerator of `mod A`, with endomorphism ring
`Γ = Module.End A M` acting on `M` by evaluation. The Morita-Tachikawa correspondence says that
`Γ` has dominant dimension at least two, and that every Artin algebra of dominant dimension at least
two arises in this way. This file proves both directions.

The forward direction (`TauCeti.two_le_dominantDimension_end`) combines Müller's criterion
(`TauCeti.two_le_dominantDimension_end_of_projective_of_injective`), for a finitely presented module
that is projective and injective over its endomorphism ring, with the projectivity of a generator
(`TauCeti.Module.IsGenerator.projective_end`) and the injectivity of a coseparator
(`CategoryTheory.IsCoseparator.injective_end`) over their endomorphism rings.

For the converse (`TauCeti.exists_algEquiv_end_of_two_le_dominantDimension`), let `Γ` be an Artin
algebra with an exact sequence `0 → Γ → I₀ → I₁` by finitely generated projective-injective
modules (`TauCeti.two_le_dominantDimension_iff`). Put `Q = I₀ × I₁` and `B = Module.End Γ Q`.
Then `Q` is a generator over `B`, being finitely generated and projective over `Γ`
(`TauCeti.Module.isGenerator_end_of_projective`), and a cogenerator, being finitely generated and
injective (`TauCeti.isCoseparator_end_of_injective`). The copresentation `0 → Γ → Q → Q²`
gives the double centralizer property `Γ ≅ Module.End B Q`
(`TauCeti.toModuleEnd_moduleEnd_bijective_of_exact`). The algebra `B` is again an Artin algebra,
finite over the base ring as a ring of linear maps between finitely generated modules.

## Main results

* `TauCeti.two_le_dominantDimension_end`: **the Morita-Tachikawa correspondence, forward
  direction**: the endomorphism ring of a generator-cogenerator of `mod A`, for an Artin algebra
  `A`, has dominant dimension at least two.
* `TauCeti.exists_algEquiv_end_of_two_le_dominantDimension`: **the Morita-Tachikawa
  correspondence, converse**: an Artin algebra of dominant dimension at least two is the
  endomorphism algebra of a generator-cogenerator of `mod B` for some Artin algebra `B`.

## References

* B. J. Müller, *The classification of algebras by dominant dimension*, Canad. J. Math. 20 (1968),
  398–409, Theorem 2.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  Studies in Advanced Mathematics 36, CUP (1995), Proposition VI.5.4(a) and Theorem VI.5.5.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w

/-- **The Morita-Tachikawa correspondence, forward direction.** The endomorphism ring of a
generator-cogenerator `M` of `mod A`, for an Artin algebra `A`, has dominant dimension at least two.
The base ring `R` may live in any universe, and the modules in any universe in which `A` is
small. -/
theorem two_le_dominantDimension_end (R : Type u) [CommRing R] [IsArtinianRing R]
    {A : Type v} [Ring A] [Algebra R A] [Module.Finite R A] [Small.{w} A]
    (M : FGModuleCat.{w} A) (hM : IsGeneratorCogenerator M) :
    2 ≤ dominantDimension (Module.End A M.obj) := by
  obtain ⟨hs, hc⟩ := isGeneratorCogenerator_iff.1 hM
  have := IsArtinianRing.of_finite R A
  have : Module.IsGenerator A M.obj := FGModuleCat.isGenerator_of_isSeparator hs
  have := Module.finitePresentation_of_finite A M.obj
  have := hc.injective_end R
  -- `Module.IsGenerator.projective_end` makes `M` projective over its endomorphism ring.
  exact two_le_dominantDimension_end_of_projective_of_injective M.obj

open scoped ModuleCat.Algebra in
/-- **The Morita-Tachikawa correspondence, converse.** An Artin algebra `Γ` of dominant dimension
at least two is isomorphic, as an `R`-algebra, to the endomorphism algebra of a
generator-cogenerator `M` of `mod B`, for some Artin `R`-algebra `B`. The base ring `R` may live in
any universe. The `R`-algebra structure on `Module.End B M.obj` comes from the action of `R` on `M`
through `B`. -/
theorem exists_algEquiv_end_of_two_le_dominantDimension (R : Type*) [CommRing R]
    [IsArtinianRing R] (Γ : Type u) [Ring Γ] [Algebra R Γ] [Module.Finite R Γ]
    (hΓ : 2 ≤ dominantDimension Γ) :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra R B) (_ : Module.Finite R B)
      (M : FGModuleCat.{u} B),
      IsGeneratorCogenerator M ∧ Nonempty (Γ ≃ₐ[R] Module.End B M.obj) := by
  obtain ⟨I₀, I₁, f, g, w, hf, hfg, ⟨_, hP₀, hI₀⟩, _, hP₁, hI₁⟩ :=
    (two_le_dominantDimension_iff Γ).1 hΓ
  -- `Q = I₀ × I₁` is finitely generated, projective and injective, with `R` acting through `Γ`.
  have : Module.Projective Γ I₀ := (IsProjective.iff_projective _).2 hP₀
  have : Module.Projective Γ I₁ := (IsProjective.iff_projective _).2 hP₁
  have : Module.Injective Γ (I₀ × I₁) := Module.injective_module_of_injective_object Γ _
    (inj := Injective.of_iso (ModuleCat.biprodIsoProd I₀ I₁) inferInstance)
  let B := Module.End Γ (I₀ × I₁)
  have : Module.Finite R (I₀ × I₁) := .trans Γ _
  have : Module.Finite R B := Module.IsNoetherian.finite R B
  have : Module.Finite B (I₀ × I₁) := .of_restrictScalars_finite R B _
  -- The copresentation `0 → Γ → Q → Q²`, with second map `(a, b) ↦ ((0, g a), (0, b))`.
  let f' := LinearMap.inl Γ I₀ I₁ ∘ₗ f.hom
  let g' : (I₀ × I₁) →ₗ[Γ] Fin 2 → I₀ × I₁ :=
    LinearMap.pi ![LinearMap.inr Γ I₀ I₁ ∘ₗ g.hom ∘ₗ LinearMap.fst Γ I₀ I₁,
      LinearMap.inr Γ I₀ I₁ ∘ₗ LinearMap.snd Γ I₀ I₁]
  have hf' : Function.Injective f' :=
    LinearMap.inl_injective.comp ((ModuleCat.mono_iff_injective f).1 hf)
  have hfg' : Function.Exact f' g' := by
    have hfg := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hfg
    rintro ⟨a, b⟩
    simpa [f', g', funext_iff, Fin.forall_fin_two] using and_congr (hfg a) eq_comm
  let φ : Γ →ₐ[R] Module.End B (FGModuleCat.of B (I₀ × I₁)).obj :=
    Algebra.lsmul R B (FGModuleCat.of B (I₀ × I₁)).obj
  refine ⟨B, inferInstance, inferInstance, inferInstance, FGModuleCat.of B (I₀ × I₁),
    isGeneratorCogenerator_iff.2
      ⟨FGModuleCat.isSeparator_of_isGenerator _, isCoseparator_end_of_injective R⟩,
    ⟨AlgEquiv.ofBijective φ (toModuleEnd_moduleEnd_bijective_of_exact hf' hfg')⟩⟩

end TauCeti
