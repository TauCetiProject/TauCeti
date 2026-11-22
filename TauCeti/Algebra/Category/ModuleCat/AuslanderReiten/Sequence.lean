/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Formula
public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Translate
public import TauCeti.CategoryTheory.AlmostSplit.Sequence
import TauCeti.Algebra.Category.ModuleCat.Ext.FiniteLength
import TauCeti.Algebra.Category.ModuleCat.ULift
import TauCeti.CategoryTheory.AlmostSplit.Equivalence
import TauCeti.CategoryTheory.AlmostSplit.Minimal

/-!
# Existence of almost-split sequences over an Artin algebra

Let `A` be an Artin algebra over a commutative Artinian ring `R`, and `E` an injective `R`-module
such that each `Hom_R(R ⧸ 𝔪, E)` has length one, for instance an injective hull of `R ⧸ J(R)`. A
finite-dimensional algebra over a field `k` is the case `R = E = k`
(`TauCeti.length_quotient_linearMap_self_eq_one`). This file proves the existence half of the
Auslander–Reiten theorem: every finitely generated indecomposable non-projective `A`-module `M`
ends an almost-split sequence

`0 → τ M → Y → M → 0`

of `A`-modules, whose left-hand end is the translate `τ M = ModuleCat.arTranslate R E M` and whose
middle term is finitely generated (`ModuleCat.exists_isAlmostSplit_arTranslate`). Dually, every
finitely generated indecomposable non-injective module starts an almost-split sequence with
finitely generated middle term and right-hand end
(`ModuleCat.exists_isAlmostSplit_of_not_injective`), obtained from the sequence ending at its
inverse translate.

Both lifting properties hold in the category of *all* `A`-modules, not only the finitely
generated ones. A finitely generated module therefore ends an almost-split sequence exactly when
it is indecomposable and non-projective, and starts one exactly when it is indecomposable and
non-injective.

By `CategoryTheory.ShortComplex.IsAlmostSplit.nonempty_iso`, the sequence ending at `M` is unique
up to isomorphism among the almost-split sequences ending at `M` whose left-hand end has a local
endomorphism ring, for instance a finitely generated one.

The sequence comes from the Auslander–Reiten formula. For any finite projective presentation `P`
of `M`, minimal or not, the translate `τ_P M = D Tr_P M` represents `D Ext¹(M, -)` on the
injectively stable category, with universal element the Auslander–Reiten form
(`ModuleCat.bijective_costablePairing_auslanderReitenForm`); this needs no indecomposability of
`M`. When `τ_P M` has a local endomorphism ring and is not injective, the one-sided local duality
theorem (`TauCeti.ExactStructure.exists_isLeftAlmostSplit_of_bijective_costablePairing`) turns this
representation into a conflation `τ_P M ⟶ Y ⟶ M` whose inflation is left almost split
(`TauCeti.FiniteProjectivePresentation.exists_isLeftAlmostSplit_matlisDualTranspose`). Its
finiteness hypothesis is that `Ext¹(M, τ_P M)` has finite length over `R`, which holds for all
finitely generated modules (`ModuleCat.isFiniteLength_ext1`). For a minimal presentation `τ_P M`
is the translate `τ M` (`ModuleCat.exists_isLeftAlmostSplit_arTranslate`). If moreover `M` is
indecomposable, both ends have local endomorphism rings and the sequence is almost split.

## Main results

* `TauCeti.FiniteProjectivePresentation.exists_isLeftAlmostSplit_matlisDualTranspose`: a short
  exact sequence starting at the translate `τ_P M` of any finite projective presentation `P` of
  `M`, with left almost-split first map, when `τ_P M` is non-injective with local endomorphism
  ring.
* `ModuleCat.exists_isLeftAlmostSplit_arTranslate`: the same for the chosen translate `τ M`.
* `ModuleCat.exists_isAlmostSplit_arTranslate`: the existence of almost-split sequences ending at
  finitely generated indecomposable non-projective modules.
* `ModuleCat.exists_isAlmostSplit_of_not_projective`: the same, without naming the translate, for
  modules in any universe in which `A` is small.
* `ModuleCat.exists_isAlmostSplit_of_not_injective`: the existence of almost-split sequences
  starting at finitely generated indecomposable non-injective modules.
* `ModuleCat.exists_isAlmostSplit_X₃_eq_iff` and `ModuleCat.exists_isAlmostSplit_X₁_eq_iff`: a
  finitely generated module ends, respectively starts, an almost-split sequence exactly when it is
  indecomposable and non-projective, respectively non-injective.

## Implementation notes

The theorems that do not name `E` are stated for modules in any universe `w` with `A` small in it.
They lift a module to the universe of the translate with `ModuleCat.uliftFunctor`, and bring the
finitely generated terms of the sequence back with `Shrink`; the lifting functor is fully faithful,
so it reflects almost-split sequences (`CategoryTheory.Functor.isAlmostSplit_of_map`).

`Ext¹` is the Yoneda `Ext¹` of the abelian exact structure on `ModuleCat A`, with the `R`-linear
structure of the scoped instances of `ModuleCat.Algebra`. The translate `ModuleCat.arTranslate`
takes `E` in the universe of `R`, while the Auslander–Reiten formula takes the module universe to
contain that of its coefficient module. The proof therefore applies the formula to the universe
lift `ULift E`, whose Matlis duals agree with those of `E` by `TauCeti.MatlisDual.congrCoeffOp`.

## References

* M. Auslander, I. Reiten, *Representation theory of Artin algebras III: almost split
  sequences*, Comm. Algebra 3 (1975), 239–294.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Chapter IV and Section V.1, in particular Theorem V.1.15.
* H. Krause, *A short proof for Auslander's defect formula*, Linear Algebra Appl. **365** (2003),
  267–270.
-/

public section

namespace ModuleCat

open CategoryTheory TauCeti TauCeti.ExactStructure
open scoped ModuleCat.Algebra

universe u v w

section Artin

variable (R : Type u) {A : Type v} [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A]
  [Module.Finite R A]

section Presentation

variable {R} {E : Type w} [AddCommGroup E] [Module R E] [Module.Injective R E] [Small.{w} R]

/-- **Left almost-split maps out of the translate of a presentation.** Over an Artin algebra, let
`P` be a finite projective presentation of a module `M`, not necessarily minimal, whose translate
`τ_P M = D Tr_P M` has a local endomorphism ring and is not injective. Then there is a short exact
sequence `0 → τ_P M → Y → M → 0` of `A`-modules with `Y` finitely generated whose first map is
left almost split. The module `M` need not be indecomposable. -/
theorem _root_.TauCeti.FiniteProjectivePresentation.exists_isLeftAlmostSplit_matlisDualTranspose
    {M : ModuleCat.{max u v w} A} (P : FiniteProjectivePresentation M)
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    [IsLocalRing (End (matlisDualTranspose R E P))] (hT : ¬ Injective (matlisDualTranspose R E P)) :
    ∃ (Y : ModuleCat.{max u v w} A) (i : matlisDualTranspose R E P ⟶ Y) (p : Y ⟶ M)
      (h : i ≫ p = 0),
      Module.Finite A Y ∧ (ShortComplex.mk i p h).ShortExact ∧ IsLeftAlmostSplit i := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  have := finite_of_forall_isMaximal hE
  have : Module.Finite A M := Module.Finite.of_surjective P.π P.surjective
  have : Module.Finite A (matlisDualTranspose R E P) :=
    inferInstanceAs (Module.Finite A (AuslanderReitenTranslate R E P.p))
  obtain ⟨x, hx⟩ := exists_isLeftAlmostSplit_of_bijective_costablePairing hE
    (fun h ↦ hT ((abelian_isInjective_iff _).mp h)) (isFiniteLength_ext1 R M _)
    (bijective_costablePairing_auslanderReitenForm R E P)
  have hS := x.shortExact
  have : Module.Finite A x.obj := Module.Finite.of_exact
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact)
    hS.moduleCat_surjective_g
  exact ⟨x.obj, x.f, x.g, x.zero, this, hS, hx⟩

end Presentation

section Translate

variable (E : Type u) [AddCommGroup E] [Module R E] [Module.Injective R E]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
include hE

/-- **Left almost-split maps out of the translate.** Over an Artin algebra, let `M` be a finitely
generated module whose translate `τ M` has a local endomorphism ring and is not injective. Then
there is a short exact sequence `0 → τ M → Y → M → 0` of `A`-modules with `Y` finitely generated
whose first map is left almost split. The module `M` need not be indecomposable. This is
`TauCeti.FiniteProjectivePresentation.exists_isLeftAlmostSplit_matlisDualTranspose` for a minimal
presentation. -/
theorem exists_isLeftAlmostSplit_arTranslate (M : ModuleCat.{max u v w} A) [Module.Finite A M]
    [IsLocalRing (End (arTranslate R E M))] (hT : ¬ Injective (arTranslate R E M)) :
    ∃ (Y : ModuleCat.{max u v w} A) (i : arTranslate R E M ⟶ Y) (p : Y ⟶ M) (h : i ≫ p = 0),
      Module.Finite A Y ∧ (ShortComplex.mk i p h).ShortExact ∧ IsLeftAlmostSplit i := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  have := finite_of_forall_isMaximal hE
  -- The translate of a minimal presentation, with `E` lifted to the module universe.
  let E' := ULift.{w} E
  have : Module.Injective R E' := Module.ulift_injective_of_injective R inferInstance
  have hE' : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E') = 1 := fun 𝔪 h𝔪 ↦
    (LinearEquiv.congrRight ULift.moduleEquiv).length_eq.trans (hE 𝔪 h𝔪)
  obtain ⟨P, hP⟩ := FiniteProjectivePresentation.exists_isMinimal (M := M)
  obtain ⟨e⟩ := nonempty_iso_arTranslate R E M P hP
  let T := matlisDualTranspose R E' P
  let e : arTranslate R E M ≅ T := e ≪≫ (MatlisDual.congrCoeffOp ULift.moduleEquiv.symm).toModuleIso
  have : Module.Finite A T := Module.Finite.equiv e.toLinearEquiv
  have : IsLocalRing (End T) := (indecomposable_iff_isLocalRing_end T
    (isFiniteLength_of_finite A T)).mp (((indecomposable_iff_isLocalRing_end _
      (isFiniteLength_of_finite A _)).mpr ‹_›).of_iso e)
  obtain ⟨Y, i, p, h, hY, hS, hi⟩ := P.exists_isLeftAlmostSplit_matlisDualTranspose hE'
    fun h ↦ hT (Injective.of_iso e.symm h)
  exact ⟨Y, e.hom ≫ i, p, by simp [h], hY, ShortComplex.shortExact_of_iso
    (S₁ := ShortComplex.mk i p h) (ShortComplex.isoMk e.symm (Iso.refl _) (Iso.refl _)) hS,
    hi.iso_comp e.hom⟩

/-- **The Auslander–Reiten theorem, existence.** Over an Artin algebra, a finitely generated
indecomposable non-projective module `M` ends an almost-split sequence `0 → τ M → Y → M → 0` of
`A`-modules whose left-hand end is the translate `τ M` and whose middle term is finitely
generated. -/
theorem exists_isAlmostSplit_arTranslate (M : ModuleCat.{max u v w} A) [Module.Finite A M]
    (hiM : Indecomposable M) (hpM : ¬ Projective M) :
    ∃ (Y : ModuleCat.{max u v w} A) (i : arTranslate R E M ⟶ Y) (p : Y ⟶ M) (h : i ≫ p = 0),
      Module.Finite A Y ∧ (ShortComplex.mk i p h).IsAlmostSplit := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  have := finite_of_forall_isMaximal hE
  have : IsLocalRing (End M) :=
    (indecomposable_iff_isLocalRing_end M (isFiniteLength_of_finite A M)).mp hiM
  have : IsLocalRing (End (arTranslate R E M)) := (indecomposable_iff_isLocalRing_end _
    (isFiniteLength_of_finite A _)).mp ((indecomposable_arTranslate_iff hE M hiM).mpr hpM)
  obtain ⟨Y, i, p, h, hY, hS, hi⟩ := exists_isLeftAlmostSplit_arTranslate R E hE M
    fun h ↦ hpM ((injective_arTranslate_iff hE M).mp h)
  exact ⟨Y, i, p, h, hY, hS.isAlmostSplit_iff_isLeftAlmostSplit.mpr hi⟩

end Translate

section Lift

/-! ### Descending to modules in a smaller universe -/

include R

/-- **The Auslander–Reiten theorem, existence on the right.** Over an Artin algebra, a finitely
generated indecomposable non-projective module `M` ends an almost-split sequence
`0 → X → Y → M → 0` of `A`-modules with `X` and `Y` finitely generated. The modules live in any
universe in which `A` is small. -/
theorem exists_isAlmostSplit_of_not_projective [Small.{w} A] (M : ModuleCat.{w} A)
    [Module.Finite A M]
    (hiM : Indecomposable M) (hpM : ¬ Projective M) :
    ∃ (X Y : ModuleCat.{w} A) (i : X ⟶ Y) (p : Y ⟶ M) (h : i ≫ p = 0),
      Module.Finite A X ∧ Module.Finite A Y ∧ (ShortComplex.mk i p h).IsAlmostSplit := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  let F := uliftFunctor.{max u v, w} A
  have : Module.Finite A (F.obj M) := Module.Finite.equiv ULift.moduleEquiv.symm
  obtain ⟨E, _, _, _, -, hE⟩ := exists_injective_finite_length_quotient_linearMap_eq_one R
  obtain ⟨Y, i, p, h, hY, hS⟩ := exists_isAlmostSplit_arTranslate.{u, v, w} R E hE (F.obj M)
    (F.indecomposable_obj_of_map_bijective hiM ((fullyFaithfulUliftFunctor A).map_bijective M M))
    fun hp ↦ hpM ((projective_of_ulift_iff.{v, w, max u v} M).mp hp)
  have : Module.Finite A (arTranslate R E (F.obj M)) := Module.Finite.of_injective i.hom
    ((ModuleCat.mono_iff_injective i).mp hS.shortExact.mono_f)
  obtain ⟨X₀, _, ⟨e₁⟩⟩ := exists_uliftFunctor_obj_iso.{v, w, max u v} (arTranslate R E (F.obj M))
  obtain ⟨Y₀, _, ⟨e₂⟩⟩ := exists_uliftFunctor_obj_iso.{v, w, max u v} Y
  obtain ⟨i', p', h', hS', -⟩ := F.exists_isAlmostSplit_of_obj_iso hS e₁ e₂ (Iso.refl (F.obj M))
  exact ⟨X₀, Y₀, i', p', h', inferInstance, inferInstance, hS'⟩

/-- Over an Artin algebra, a finitely generated module ends an almost-split sequence of `A`-modules
exactly when it is indecomposable and non-projective. -/
theorem exists_isAlmostSplit_X₃_eq_iff [Small.{w} A] (M : ModuleCat.{w} A) [Module.Finite A M] :
    (∃ S : ShortComplex (ModuleCat.{w} A), S.X₃ = M ∧ S.IsAlmostSplit) ↔
      Indecomposable M ∧ ¬ Projective M := by
  refine ⟨?_, fun ⟨hiM, hpM⟩ ↦ ?_⟩
  · rintro ⟨S, rfl, hS⟩
    exact ⟨hS.isRightAlmostSplit_g.indecomposable, hS.not_projective_X₃⟩
  · obtain ⟨X, Y, i, p, h, -, -, hS⟩ := exists_isAlmostSplit_of_not_projective R M hiM hpM
    exact ⟨_, rfl, hS⟩

/-- **The Auslander–Reiten theorem, existence on the left.** Over an Artin algebra, a finitely
generated indecomposable non-injective module `N` starts an almost-split sequence
`0 → N → Y → M → 0` of `A`-modules with `Y` and `M` finitely generated. The modules live in any
universe in which `A` is small. -/
theorem exists_isAlmostSplit_of_not_injective [Small.{w} A] (N : ModuleCat.{w} A)
    [Module.Finite A N]
    (hiN : Indecomposable N) (hinj : ¬ Injective N) :
    ∃ (Y M : ModuleCat.{w} A) (i : N ⟶ Y) (p : Y ⟶ M) (h : i ≫ p = 0),
      Module.Finite A Y ∧ Module.Finite A M ∧ (ShortComplex.mk i p h).IsAlmostSplit := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  let F := uliftFunctor.{max u v, w} A
  have : Module.Finite A (F.obj N) := Module.Finite.equiv ULift.moduleEquiv.symm
  obtain ⟨E, _, _, _, -, hE⟩ := exists_injective_finite_length_quotient_linearMap_eq_one R
  obtain ⟨M, _, hiM, hpM, ⟨e⟩⟩ := exists_nonempty_iso_arTranslate.{u, v, w} hE (F.obj N)
    (F.indecomposable_obj_of_map_bijective hiN ((fullyFaithfulUliftFunctor A).map_bijective N N))
    fun h ↦ hinj ((injective_of_ulift_iff.{v, w, max u v} N).mp h)
  obtain ⟨Y, i, p, h, hY, hS⟩ := exists_isAlmostSplit_arTranslate R E hE M hiM hpM
  obtain ⟨Y₀, _, ⟨e₂⟩⟩ := exists_uliftFunctor_obj_iso.{v, w, max u v} Y
  obtain ⟨M₀, _, ⟨e₃⟩⟩ := exists_uliftFunctor_obj_iso.{v, w, max u v} M
  obtain ⟨i', p', h', hS', -⟩ := F.exists_isAlmostSplit_of_obj_iso hS e.symm e₂ e₃
  exact ⟨Y₀, M₀, i', p', h', inferInstance, inferInstance, hS'⟩

/-- Over an Artin algebra, a finitely generated module starts an almost-split sequence of
`A`-modules exactly when it is indecomposable and non-injective. -/
theorem exists_isAlmostSplit_X₁_eq_iff [Small.{w} A] (N : ModuleCat.{w} A) [Module.Finite A N] :
    (∃ S : ShortComplex (ModuleCat.{w} A), S.X₁ = N ∧ S.IsAlmostSplit) ↔
      Indecomposable N ∧ ¬ Injective N := by
  refine ⟨?_, fun ⟨hiN, hinj⟩ ↦ ?_⟩
  · rintro ⟨S, rfl, hS⟩
    exact ⟨hS.isLeftAlmostSplit_f.indecomposable, hS.not_injective_X₁⟩
  · obtain ⟨Y, M, i, p, h, -, -, hS⟩ := exists_isAlmostSplit_of_not_injective R N hiN hinj
    exact ⟨_, rfl, hS⟩

end Lift

end Artin

end ModuleCat
