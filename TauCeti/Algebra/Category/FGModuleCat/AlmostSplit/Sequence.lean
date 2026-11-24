/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Translate
public import TauCeti.CategoryTheory.AlmostSplit.Sequence
import TauCeti.Algebra.Category.FGModuleCat.Injective
import TauCeti.Algebra.Category.FGModuleCat.KrullSchmidt
import TauCeti.Algebra.Category.FGModuleCat.Projective
import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Sequence
import TauCeti.CategoryTheory.AlmostSplit.Equivalence

/-!
# Almost-split sequences in `FGModuleCat` over an Artin algebra

Let `A` be an Artin algebra over a commutative Artinian ring `R`. In the category `mod A` of
finitely generated modules, every indecomposable non-projective module ends an almost-split sequence
and every indecomposable non-injective module starts one. With `E` an injective `R`-module such that
each `Hom_R(R ⧸ 𝔪, E)` has length one, the other end is identified: the sequence ending at `M`
starts at `τ M = FGModuleCat.arTranslate R E M`, and the sequence starting at `N` ends at
`τ⁻ N = FGModuleCat.arInverseTranslate R E N`. These are the translates `ModuleCat.arTranslate`
and `ModuleCat.arInverseTranslate`, bundled as objects of `mod A` (`FGModuleCat.arTranslate_obj`,
`FGModuleCat.arInverseTranslate_obj`). A finite-dimensional algebra over a field `k` is the case
`R = E = k` (`TauCeti.length_quotient_linearMap_self_eq_one`).

The sequence ending at `M` is the almost-split sequence of all `A`-modules of
`ModuleCat.exists_isAlmostSplit_arTranslate`, whose terms are finitely generated. The inclusion of
`mod A` into all modules is fully faithful and exact, so it reflects almost-split sequences
(`CategoryTheory.Functor.isAlmostSplit_of_map`). The sequence starting at `N` is the one ending at
`τ⁻ N`, using `τ τ⁻ N ≅ N` (`ModuleCat.nonempty_iso_arTranslate_arInverseTranslate`). Projectivity
and injectivity in `mod A` agree with those in all modules (`FGModuleCat.projective_obj_iff`,
`FGModuleCat.injective_obj_iff`), and so does indecomposability
(`FGModuleCat.indecomposable_obj_iff`).

## Main definitions

* `FGModuleCat.arTranslate` and `FGModuleCat.arInverseTranslate`: the translates `τ` and `τ⁻` as
  objects of `mod A`. They respect isomorphisms (`FGModuleCat.nonempty_iso_arTranslate_of_iso`,
  `FGModuleCat.nonempty_iso_arInverseTranslate_of_iso`); `τ M` is injective exactly when `M` is
  projective, `τ⁻ N` is projective exactly when `N` is injective, and for indecomposable `M`, `N`
  the translates are indecomposable exactly when `M` is not projective, respectively `N` is not
  injective (`FGModuleCat.injective_arTranslate_iff`,
  `FGModuleCat.projective_arInverseTranslate_iff`, `FGModuleCat.indecomposable_arTranslate_iff`,
  `FGModuleCat.indecomposable_arInverseTranslate_iff`).

## Main results

* `FGModuleCat.exists_isAlmostSplit_arTranslate` and
  `FGModuleCat.exists_isAlmostSplit_arInverseTranslate`: almost-split sequences with the
  translates as their other ends.
* `FGModuleCat.exists_isAlmostSplit` and `FGModuleCat.exists_isAlmostSplit_of_not_injective`: the
  existence of almost-split sequences, from `ModuleCat.exists_isAlmostSplit_of_not_projective` and
  `ModuleCat.exists_isAlmostSplit_of_not_injective`.

## Implementation notes

In the theorems naming a translate, the modules live in any universe `max u v w` containing those
of `R` and `A`, while `E` lives in the universe of `R`, as for `ModuleCat.arTranslate`. The
existence theorems that do not name `E` hold in any universe in which `A` is small.

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

variable (E : Type u) [AddCommGroup E] [Module R E] [Module.Finite R E]

/-- The Auslander–Reiten translate `τ M = ModuleCat.arTranslate R E M` of a finitely generated
module, as an object of `FGModuleCat A`. -/
noncomputable def arTranslate (M : FGModuleCat.{max u v w} A) : FGModuleCat.{max u v w} A :=
  ⟨ModuleCat.arTranslate R E M.obj, (ModuleCat.isFG_iff _).mpr inferInstance⟩

@[simp]
theorem arTranslate_obj (M : FGModuleCat.{max u v w} A) :
    (arTranslate R E M).obj = ModuleCat.arTranslate R E M.obj :=
  (rfl)

/-- The inverse Auslander–Reiten translate `τ⁻ N = ModuleCat.arInverseTranslate R E N` of a finitely
generated module, as an object of `FGModuleCat A`. -/
noncomputable def arInverseTranslate (N : FGModuleCat.{max u v w} A) : FGModuleCat.{max u v w} A :=
  ⟨ModuleCat.arInverseTranslate R E N.obj, (ModuleCat.isFG_iff _).mpr inferInstance⟩

@[simp]
theorem arInverseTranslate_obj (N : FGModuleCat.{max u v w} A) :
    (arInverseTranslate R E N).obj = ModuleCat.arInverseTranslate R E N.obj :=
  (rfl)

/-- Isomorphic modules have isomorphic Auslander–Reiten translates in `FGModuleCat A`. -/
theorem nonempty_iso_arTranslate_of_iso {M M' : FGModuleCat.{max u v w} A} (e : M ≅ M') :
    Nonempty (arTranslate R E M ≅ arTranslate R E M') := by
  obtain ⟨f⟩ := ModuleCat.nonempty_iso_arTranslate_of_iso R E (M := M.obj) (N := M'.obj)
    ((ObjectProperty.ι _).mapIso e)
  exact ⟨(ObjectProperty.fullyFaithfulι _).preimageIso (X := arTranslate R E M)
    (Y := arTranslate R E M') f⟩

/-- Isomorphic modules have isomorphic inverse Auslander–Reiten translates in `FGModuleCat A`. -/
theorem nonempty_iso_arInverseTranslate_of_iso {N N' : FGModuleCat.{max u v w} A} (e : N ≅ N') :
    Nonempty (arInverseTranslate R E N ≅ arInverseTranslate R E N') := by
  obtain ⟨f⟩ := ModuleCat.nonempty_iso_arInverseTranslate_of_iso R E (N := N.obj) (N' := N'.obj)
    ((ObjectProperty.ι _).mapIso e)
  exact ⟨(ObjectProperty.fullyFaithfulι _).preimageIso (X := arInverseTranslate R E N)
    (Y := arInverseTranslate R E N') f⟩

variable [Module.Injective R E]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
include hE

/-- The translate of an indecomposable module is indecomposable exactly when the module is not
projective, in `FGModuleCat A`. -/
@[simp]
theorem indecomposable_arTranslate_iff (M : FGModuleCat.{max u v w} A) (hiM : Indecomposable M) :
    Indecomposable (arTranslate R E M) ↔ ¬ Projective M :=
  (indecomposable_obj_iff _).symm.trans ((ModuleCat.indecomposable_arTranslate_iff hE M.obj
    ((indecomposable_obj_iff M).mpr hiM)).trans (projective_obj_iff M).not)

/-- The translate is injective exactly when the module is projective, in `FGModuleCat A`. -/
@[simp]
theorem injective_arTranslate_iff (M : FGModuleCat.{max u v w} A) :
    Injective (arTranslate R E M) ↔ Projective M := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  exact (injective_obj_iff _).symm.trans
    ((ModuleCat.injective_arTranslate_iff hE M.obj).trans (projective_obj_iff M))

/-- The inverse translate of an indecomposable module is indecomposable exactly when the module is
not injective, in `FGModuleCat A`. -/
@[simp]
theorem indecomposable_arInverseTranslate_iff (N : FGModuleCat.{max u v w} A)
    (hiN : Indecomposable N) : Indecomposable (arInverseTranslate R E N) ↔ ¬ Injective N := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  exact (indecomposable_obj_iff _).symm.trans ((ModuleCat.indecomposable_arInverseTranslate_iff
    hE N.obj ((indecomposable_obj_iff N).mpr hiN)).trans (injective_obj_iff N).not)

/-- The inverse translate is projective exactly when the module is injective, in
`FGModuleCat A`. -/
@[simp]
theorem projective_arInverseTranslate_iff (N : FGModuleCat.{max u v w} A) :
    Projective (arInverseTranslate R E N) ↔ Injective N := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  exact (projective_obj_iff _).symm.trans
    ((ModuleCat.projective_arInverseTranslate_iff hE N.obj).trans (injective_obj_iff N))

/-- **The Auslander–Reiten theorem in `FGModuleCat`, existence.** Over an Artin algebra, a
finitely generated indecomposable module `M` that is not projective in `FGModuleCat A` ends an
almost-split sequence of `FGModuleCat A` whose left-hand end is the translate `τ M`. The finiteness
of `E` follows from `hE`; it is assumed so that `τ M` is an object of `FGModuleCat A`. -/
theorem exists_isAlmostSplit_arTranslate (M : FGModuleCat.{max u v w} A)
    (hM : Indecomposable M) (hP : ¬ Projective M) :
    ∃ S : ShortComplex (FGModuleCat.{max u v w} A), S.IsAlmostSplit ∧
      Nonempty (S.X₁ ≅ arTranslate R E M) ∧ Nonempty (S.X₃ ≅ M) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  obtain ⟨Y, i, p, h, hY, hS⟩ := ModuleCat.exists_isAlmostSplit_arTranslate R E hE M.obj
    ((indecomposable_obj_iff M).mpr hM) ((projective_obj_iff M).not.mpr hP)
  obtain ⟨i', p', h', hS', -⟩ := (ObjectProperty.ι _).exists_isAlmostSplit_of_obj_iso hS
    (X₁ := arTranslate R E M) (X₂ := ⟨Y, (ModuleCat.isFG_iff _).mpr hY⟩) (X₃ := M)
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  exact ⟨ShortComplex.mk i' p' h', hS', ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩

/-- **The Auslander–Reiten theorem in `FGModuleCat`, existence on the left.** Over an Artin
algebra, a finitely generated indecomposable module `N` that is not injective in `FGModuleCat A`
starts an almost-split sequence of `FGModuleCat A` whose right-hand end is the inverse translate
`τ⁻ N`. The finiteness of `E` follows from `hE`; it is assumed so that `τ⁻ N` is defined. -/
theorem exists_isAlmostSplit_arInverseTranslate (N : FGModuleCat.{max u v w} A)
    (hN : Indecomposable N) (hI : ¬ Injective N) :
    ∃ S : ShortComplex (FGModuleCat.{max u v w} A), S.IsAlmostSplit ∧
      Nonempty (S.X₁ ≅ N) ∧ Nonempty (S.X₃ ≅ arInverseTranslate R E N) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  have hN' : Indecomposable N.obj := (indecomposable_obj_iff N).mpr hN
  have hI' : ¬ Injective N.obj := (injective_obj_iff N).not.mpr hI
  let M := arInverseTranslate R E N
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₃⟩⟩ := exists_isAlmostSplit_arTranslate R E hE M
    ((indecomposable_obj_iff M).mp
      ((ModuleCat.indecomposable_arInverseTranslate_iff hE N.obj hN').mpr hI'))
    ((projective_obj_iff M).not.mp
      ((ModuleCat.projective_arInverseTranslate_iff hE N.obj).not.mpr hI'))
  obtain ⟨f⟩ := ModuleCat.nonempty_iso_arTranslate_arInverseTranslate hE N.obj hN' hI'
  exact ⟨S, hS, ⟨e₁ ≪≫ (ObjectProperty.fullyFaithfulι _).preimageIso f⟩, ⟨e₃⟩⟩

end Translate

include R

/-- **Almost-split sequences ending at a module.** Over an Artin algebra, every finitely
generated indecomposable module that is not projective in `FGModuleCat A` ends an almost-split
sequence of `FGModuleCat A`. The modules live in any universe in which `A` is small. -/
theorem exists_isAlmostSplit [Small.{w} A] (M : FGModuleCat.{w} A) (hM : Indecomposable M)
    (hP : ¬ Projective M) :
    ∃ S : ShortComplex (FGModuleCat.{w} A), S.IsAlmostSplit ∧ Nonempty (S.X₃ ≅ M) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  obtain ⟨X, Y, i, p, h, hX, hY, hS⟩ := ModuleCat.exists_isAlmostSplit_of_not_projective R M.obj
    ((indecomposable_obj_iff M).mpr hM) ((projective_obj_iff M).not.mpr hP)
  obtain ⟨i', p', h', hS', -⟩ := (ObjectProperty.ι _).exists_isAlmostSplit_of_obj_iso hS
    (X₁ := ⟨X, (ModuleCat.isFG_iff _).mpr hX⟩) (X₂ := ⟨Y, (ModuleCat.isFG_iff _).mpr hY⟩)
    (X₃ := M) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  exact ⟨ShortComplex.mk i' p' h', hS', ⟨Iso.refl _⟩⟩

/-- **Almost-split sequences starting at a module.** Over an Artin algebra, every finitely
generated indecomposable module that is not injective in `FGModuleCat A` starts an almost-split
sequence of `FGModuleCat A`. The modules live in any universe in which `A` is small. -/
theorem exists_isAlmostSplit_of_not_injective [Small.{w} A] (M : FGModuleCat.{w} A)
    (hM : Indecomposable M) (hI : ¬ Injective M) :
    ∃ S : ShortComplex (FGModuleCat.{w} A), S.IsAlmostSplit ∧ Nonempty (S.X₁ ≅ M) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  obtain ⟨Y, Z, i, p, h, hY, hZ, hS⟩ := ModuleCat.exists_isAlmostSplit_of_not_injective R M.obj
    ((indecomposable_obj_iff M).mpr hM) ((injective_obj_iff M).not.mpr hI)
  obtain ⟨i', p', h', hS', -⟩ := (ObjectProperty.ι _).exists_isAlmostSplit_of_obj_iso hS
    (X₁ := M) (X₂ := ⟨Y, (ModuleCat.isFG_iff _).mpr hY⟩)
    (X₃ := ⟨Z, (ModuleCat.isFG_iff _).mpr hZ⟩) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  exact ⟨ShortComplex.mk i' p' h', hS', ⟨Iso.refl _⟩⟩

end FGModuleCat
