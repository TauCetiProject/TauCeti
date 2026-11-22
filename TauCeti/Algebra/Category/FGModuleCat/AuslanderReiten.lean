/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Translate
public import TauCeti.CategoryTheory.AlmostSplit.Sequence
import Mathlib.RingTheory.HopkinsLevitzki
import TauCeti.Algebra.Category.FGModuleCat.Injective
import TauCeti.Algebra.Category.FGModuleCat.Projective
import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Sequence
import TauCeti.CategoryTheory.AlmostSplit.Equivalence
import TauCeti.RingTheory.MatlisDuality.ArtinAlgebra

/-!
# Almost-split sequences in `FGModuleCat` over an Artin algebra

Let `A` be an Artin algebra over a commutative Artinian ring `R`. In the category `mod A` of
finitely generated modules, every indecomposable non-projective module ends an almost-split
sequence and every indecomposable non-injective module starts one. With `E` an injective
`R`-module such that each `Hom_R(R ⧸ 𝔪, E)` has length one, the other end is identified: the
sequence ending at `M` starts at `τ M = ModuleCat.arTranslate R E M`, and the sequence starting at
`N` ends at `τ⁻ N = ModuleCat.arInverseTranslate R E N`. A finite-dimensional algebra over a field
`k` is the case `R = E = k` (`TauCeti.length_quotient_linearMap_self_eq_one`).

The sequence ending at `M` is the almost-split sequence of all `A`-modules of
`ModuleCat.exists_isAlmostSplit_arTranslate`, whose terms are finitely generated.
The inclusion of `mod A` into all modules is fully faithful and exact, so it reflects almost-split
sequences (`CategoryTheory.ShortComplex.isAlmostSplit_of_map`). The sequence starting at `N` is the
one ending at `τ⁻ N`, using `τ τ⁻ N ≅ N`
(`ModuleCat.nonempty_iso_arTranslate_arInverseTranslate`). Projectivity and injectivity in
`mod A` agree with those in all modules (`FGModuleCat.projective_obj_iff`,
`FGModuleCat.injective_obj_iff`).

## Main results

* `FGModuleCat.exists_isAlmostSplit_arTranslate` and
  `FGModuleCat.exists_isAlmostSplit_arInverseTranslate`: almost-split sequences with the
  translates as their other ends.
* `FGModuleCat.exists_isAlmostSplit` and `FGModuleCat.exists_isAlmostSplit_of_not_injective`: the
  existence of almost-split sequences, taking for `E` an injective hull of `R ⧸ J(R)`.

## Implementation notes

The modules live in any universe `max u v w` containing those of `R` and `A`, while `E` lives in
the universe of `R`, as for `ModuleCat.arTranslate`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Section V.1, in particular Theorem V.1.15.
-/

public section

namespace FGModuleCat

open CategoryTheory TauCeti

universe u v w

variable (R : Type u) {A : Type v} [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A]
  [Module.Finite R A]

section Translate

variable (E : Type u) [AddCommGroup E] [Module R E] [Module.Injective R E]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
include hE

/-- **The Auslander–Reiten theorem in `FGModuleCat`, existence.** Over an Artin algebra, a
finitely generated indecomposable module `M` that is not projective in `FGModuleCat A` ends an
almost-split sequence of `FGModuleCat A` whose left-hand end is the translate `τ M`. -/
theorem exists_isAlmostSplit_arTranslate (M : FGModuleCat.{max u v w} A)
    (hM : Indecomposable M.obj) (hP : ¬ Projective M) :
    ∃ S : ShortComplex (FGModuleCat.{max u v w} A), S.IsAlmostSplit ∧
      Nonempty (S.X₁.obj ≅ ModuleCat.arTranslate R E M.obj) ∧ Nonempty (S.X₃ ≅ M) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  obtain ⟨Y, i, p, h, hY, hS⟩ := ModuleCat.exists_isAlmostSplit_arTranslate
    R E hE M.obj hM ((projective_obj_iff M).not.mpr hP)
  have : Module.Finite A (ModuleCat.arTranslate R E M.obj) :=
    Module.Finite.of_injective i.hom ((ModuleCat.mono_iff_injective i).mp hS.shortExact.mono_f)
  let T : FGModuleCat.{max u v w} A := ⟨_, (ModuleCat.isFG_iff _).mpr this⟩
  let Y' : FGModuleCat.{max u v w} A := ⟨Y, (ModuleCat.isFG_iff _).mpr hY⟩
  let S : ShortComplex (FGModuleCat.{max u v w} A) :=
    ShortComplex.mk (X₁ := T) (X₂ := Y') (X₃ := M) (ObjectProperty.homMk i)
      (ObjectProperty.homMk p) ((ObjectProperty.ι _).map_injective h)
  exact ⟨S, ShortComplex.isAlmostSplit_of_map (ObjectProperty.ι _) hS, ⟨Iso.refl _⟩,
    ⟨Iso.refl _⟩⟩

/-- **The Auslander–Reiten theorem in `FGModuleCat`, existence on the left.** Over an Artin
algebra, a finitely generated indecomposable module `N` that is not injective in `FGModuleCat A`
starts an almost-split sequence of `FGModuleCat A` whose right-hand end is the inverse translate
`τ⁻ N`. The finiteness of `E` follows from `hE`; it is assumed so that `τ⁻ N` is defined. -/
theorem exists_isAlmostSplit_arInverseTranslate [Module.Finite R E]
    (N : FGModuleCat.{max u v w} A)
    (hN : Indecomposable N.obj) (hI : ¬ Injective N) :
    ∃ S : ShortComplex (FGModuleCat.{max u v w} A), S.IsAlmostSplit ∧
      Nonempty (S.X₁ ≅ N) ∧ Nonempty (S.X₃.obj ≅ ModuleCat.arInverseTranslate R E N.obj) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  have hI' : ¬ Injective N.obj := (injective_obj_iff N).not.mpr hI
  let M : FGModuleCat.{max u v w} A := ⟨ModuleCat.arInverseTranslate R E N.obj,
    (ModuleCat.isFG_iff _).mpr inferInstance⟩
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₃⟩⟩ := exists_isAlmostSplit_arTranslate R E hE M
    ((ModuleCat.indecomposable_arInverseTranslate_iff hE N.obj hN).mpr hI')
    ((projective_obj_iff M).not.mp
      ((ModuleCat.projective_arInverseTranslate_iff hE N.obj).not.mpr hI'))
  obtain ⟨f⟩ := ModuleCat.nonempty_iso_arTranslate_arInverseTranslate hE N.obj hN hI'
  exact ⟨S, hS, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso (e₁ ≪≫ f)⟩,
    ⟨(ObjectProperty.ι _).mapIso e₃⟩⟩

end Translate

include R

/-- **Almost-split sequences ending at a module.** Over an Artin algebra, every finitely
generated indecomposable module that is not projective in `FGModuleCat A` ends an almost-split
sequence of `FGModuleCat A`. -/
theorem exists_isAlmostSplit (M : FGModuleCat.{max u v w} A) (hM : Indecomposable M.obj)
    (hP : ¬ Projective M) :
    ∃ S : ShortComplex (FGModuleCat.{max u v w} A), S.IsAlmostSplit ∧ Nonempty (S.X₃ ≅ M) := by
  obtain ⟨E, _, _, f, hf, -⟩ := exists_isInjectiveEnvelope_quotient_jacobson R
  have := hf.moduleInjective
  obtain ⟨S, hS, -, h₃⟩ := exists_isAlmostSplit_arTranslate R E
    hf.length_quotient_linearMap_eq_one M hM hP
  exact ⟨S, hS, h₃⟩

/-- **Almost-split sequences starting at a module.** Over an Artin algebra, every finitely
generated indecomposable module that is not injective in `FGModuleCat A` starts an almost-split
sequence of `FGModuleCat A`. -/
theorem exists_isAlmostSplit_of_not_injective (M : FGModuleCat.{max u v w} A)
    (hM : Indecomposable M.obj) (hI : ¬ Injective M) :
    ∃ S : ShortComplex (FGModuleCat.{max u v w} A), S.IsAlmostSplit ∧ Nonempty (S.X₁ ≅ M) := by
  obtain ⟨E, _, _, f, hf, hfl⟩ := exists_isInjectiveEnvelope_quotient_jacobson R
  have := hf.moduleInjective
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).1
  obtain ⟨S, hS, h₁, -⟩ := exists_isAlmostSplit_arInverseTranslate R E
    hf.length_quotient_linearMap_eq_one M hM hI
  exact ⟨S, hS, h₁⟩

end FGModuleCat
