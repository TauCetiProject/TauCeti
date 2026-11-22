/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Formula
public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Translate
public import TauCeti.CategoryTheory.AlmostSplit.Sequence
import Mathlib.RingTheory.HopkinsLevitzki
import TauCeti.Algebra.Category.ModuleCat.Algebra
import TauCeti.Algebra.Category.ModuleCat.Injective.FiniteDimensional
import TauCeti.CategoryTheory.Preadditive.Indecomposable
import TauCeti.RingTheory.Artinian.FiniteLength
import TauCeti.RingTheory.MatlisDuality.Semilocal

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

The sequence comes from the Auslander–Reiten formula. For a finite minimal projective presentation
`P` of `M`, the translate `τ M = D Tr M` represents `D Ext¹(M, -)` on the injectively stable
category, with universal element the Auslander–Reiten form
(`ModuleCat.bijective_costablePairing_auslanderReitenForm`). Since `M` and `τ M` have local
endomorphism rings and `τ M` is not injective, the local duality theorem
(`TauCeti.ExactStructure.exists_isAlmostSplit_of_bijective_costablePairing`) turns this
representation into an almost-split conflation `τ M ⟶ Y ⟶ M`. Its finiteness hypothesis is that
`Ext¹(M, τ M)` has finite length over `R`, which holds for all finitely generated modules
(`ModuleCat.isFiniteLength_ext1`).

## Main results

* `ModuleCat.isFiniteLength_ext1`: `Ext¹` between finitely generated modules over an Artin
  algebra has finite length over the base ring.
* `ModuleCat.exists_isAlmostSplit_arTranslate`: the existence of almost-split sequences ending at
  finitely generated indecomposable non-projective modules.
* `ModuleCat.exists_isAlmostSplit_of_not_injective`: the existence of almost-split sequences
  starting at finitely generated indecomposable non-injective modules.
* `ModuleCat.exists_isAlmostSplit_X₃_eq_iff` and `ModuleCat.exists_isAlmostSplit_X₁_eq_iff`: a
  finitely generated module ends, respectively starts, an almost-split sequence exactly when it is
  indecomposable and non-projective, respectively non-injective.

## Implementation notes

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

open CategoryTheory CategoryTheory.Limits TauCeti TauCeti.ExactStructure
open scoped ModuleCat.Algebra

universe u v w

section Artin

variable (R : Type u) {A : Type v} [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A]
  [Module.Finite R A]

/-- **`Ext¹` between finitely generated modules over an Artin algebra has finite length** over the
base ring. Embedding `N` into a finitely generated injective module `I` presents `Ext¹(M, N)` as a
quotient of `Hom(M, I ⧸ N)`, a finitely generated module over the Artinian base ring. -/
theorem isFiniteLength_ext1 [Small.{w} A] (M N : ModuleCat.{w} A) [Module.Finite A M]
    [Module.Finite A N] :
    IsFiniteLength R ((ExactStructure.abelian (ModuleCat.{w} A)).Ext1 M N) := by
  obtain ⟨I, _⟩ := exists_injectivePresentation_finite_of_isArtinianRing R N
  let K : ModuleCat.{w} A := cokernel I.f
  let e : (ExactStructure.abelian _).Extension K N :=
    ⟨I.J, I.f, cokernel.π I.f, cokernel.condition _, abelian_conflation_of_mono _⟩
  have : Module.Finite A K := Module.Finite.of_surjective (cokernel.π I.f).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  have := Module.Finite.equiv
    (e.homQuotientEquivExt1 ((abelian_isInjective_iff _).mpr I.injective) R M)
  exact isFiniteLength_of_finite R _

section Translate

variable (E : Type u) [AddCommGroup E] [Module R E] [Module.Injective R E]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)

include hE in
/-- **The Auslander–Reiten theorem, existence.** Over an Artin algebra, a finitely generated
indecomposable non-projective module `M` ends an almost-split sequence `0 → τ M → Y → M → 0` of
`A`-modules whose left-hand end is the translate `τ M` and whose middle term is finitely
generated. -/
theorem exists_isAlmostSplit_arTranslate (M : ModuleCat.{max u v w} A) [Module.Finite A M]
    (hiM : Indecomposable M) (hpM : ¬ Projective M) :
    ∃ (Y : ModuleCat.{max u v w} A) (i : arTranslate R E M ⟶ Y) (p : Y ⟶ M) (h : i ≫ p = 0),
      Module.Finite A Y ∧ (ShortComplex.mk i p h).IsAlmostSplit := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  have : Module.Finite R E := by
    have := (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (isFiniteLength_of_forall_isMaximal hE)).1
    infer_instance
  -- The Auslander–Reiten formula is applied to the lift `E'` of `E` to the module universe.
  let E' := ULift.{w} E
  have : Module.Injective R E' := Module.ulift_injective_of_injective R inferInstance
  have hE' : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E') = 1 := fun 𝔪 h𝔪 ↦
    (LinearEquiv.congrRight ULift.moduleEquiv).length_eq.trans (hE 𝔪 h𝔪)
  obtain ⟨P, hP⟩ := FiniteProjectivePresentation.exists_isMinimal (M := M)
  obtain ⟨e⟩ := nonempty_iso_arTranslate R E M P hP
  let T := matlisDualTranspose R E' P
  let e : arTranslate R E M ≅ T := e ≪≫ (MatlisDual.congrCoeffOp ULift.moduleEquiv.symm).toModuleIso
  have : Module.Finite A T := Module.Finite.equiv e.toLinearEquiv
  have : IsLocalRing (End M) :=
    (indecomposable_iff_isLocalRing_end M (isFiniteLength_of_finite A M)).mp hiM
  have : IsLocalRing (End T) := (indecomposable_iff_isLocalRing_end T
    (isFiniteLength_of_finite A T)).mp
      (((indecomposable_arTranslate_iff hE M hiM).mpr hpM).of_iso e)
  have hT : ¬ (ExactStructure.abelian _).isInjective T := fun h ↦ hpM
    ((injective_arTranslate_iff hE M).mp (Injective.of_iso e.symm
      ((abelian_isInjective_iff T).mp h)))
  obtain ⟨x, hx⟩ := exists_isAlmostSplit_of_bijective_costablePairing hE' hT
    (isFiniteLength_ext1 R M T) (bijective_costablePairing_auslanderReitenForm R E' P)
  have hS := hx.shortExact
  have : Module.Finite A x.obj := Module.Finite.of_exact
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact)
    hS.moduleCat_surjective_g
  exact ⟨x.obj, e.hom ≫ x.f, x.g, by simp, this, ShortComplex.isAlmostSplit_of_iso
    (S₁ := x.shortComplex) (ShortComplex.isoMk e.symm (Iso.refl _) (Iso.refl _)) hx⟩

end Translate

/-- An Artinian ring has an injective module `E` with each `Hom_R(R ⧸ 𝔪, E)` of length one: an
injective hull of `R ⧸ J(R)`. -/
private theorem exists_injective_length_quotient_linearMap_eq_one :
    ∃ (E : Type u) (_ : AddCommGroup E) (_ : Module R E), Module.Injective R E ∧
      ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1 := by
  obtain ⟨E, _, _, f, hf, -⟩ := exists_isInjectiveEnvelope_quotient_jacobson R
  exact ⟨E, _, _, hf.moduleInjective, hf.length_quotient_linearMap_eq_one⟩

include R

/-- Over an Artin algebra, a finitely generated module ends an almost-split sequence of `A`-modules
exactly when it is indecomposable and non-projective. -/
theorem exists_isAlmostSplit_X₃_eq_iff (M : ModuleCat.{max u v w} A) [Module.Finite A M] :
    (∃ S : ShortComplex (ModuleCat.{max u v w} A), S.X₃ = M ∧ S.IsAlmostSplit) ↔
      Indecomposable M ∧ ¬ Projective M := by
  refine ⟨?_, fun ⟨hiM, hpM⟩ ↦ ?_⟩
  · rintro ⟨S, rfl, hS⟩
    exact ⟨hS.isRightAlmostSplit_g.indecomposable, hS.not_projective_X₃⟩
  · obtain ⟨E, _, _, _, hE⟩ := exists_injective_length_quotient_linearMap_eq_one R
    obtain ⟨Y, i, p, h, -, hS⟩ := exists_isAlmostSplit_arTranslate R E hE M hiM hpM
    exact ⟨_, rfl, hS⟩

/-- **The Auslander–Reiten theorem, existence on the left.** Over an Artin algebra, a finitely
generated indecomposable non-injective module `N` starts an almost-split sequence
`0 → N → Y → M → 0` of `A`-modules with `Y` and `M` finitely generated. -/
theorem exists_isAlmostSplit_of_not_injective (N : ModuleCat.{max u v w} A) [Module.Finite A N]
    (hiN : Indecomposable N) (hinj : ¬ Injective N) :
    ∃ (Y M : ModuleCat.{max u v w} A) (i : N ⟶ Y) (p : Y ⟶ M) (h : i ≫ p = 0),
      Module.Finite A Y ∧ Module.Finite A M ∧ (ShortComplex.mk i p h).IsAlmostSplit := by
  obtain ⟨E, _, _, _, hE⟩ := exists_injective_length_quotient_linearMap_eq_one R
  obtain ⟨M, _, hiM, hpM, ⟨e⟩⟩ := exists_nonempty_iso_arTranslate hE N hiN hinj
  obtain ⟨Y, i, p, h, hY, hS⟩ := exists_isAlmostSplit_arTranslate R E hE M hiM hpM
  exact ⟨Y, M, e.inv ≫ i, p, by simp [h], hY, inferInstance,
    ShortComplex.isAlmostSplit_of_iso (S₁ := ShortComplex.mk i p h)
      (ShortComplex.isoMk e (Iso.refl _) (Iso.refl _)) hS⟩

/-- Over an Artin algebra, a finitely generated module starts an almost-split sequence of
`A`-modules exactly when it is indecomposable and non-injective. -/
theorem exists_isAlmostSplit_X₁_eq_iff (N : ModuleCat.{max u v w} A) [Module.Finite A N] :
    (∃ S : ShortComplex (ModuleCat.{max u v w} A), S.X₁ = N ∧ S.IsAlmostSplit) ↔
      Indecomposable N ∧ ¬ Injective N := by
  refine ⟨?_, fun ⟨hiN, hinj⟩ ↦ ?_⟩
  · rintro ⟨S, rfl, hS⟩
    exact ⟨hS.isLeftAlmostSplit_f.indecomposable, hS.not_injective_X₁⟩
  · obtain ⟨Y, M, i, p, h, -, -, hS⟩ := exists_isAlmostSplit_of_not_injective R N hiN hinj
    exact ⟨_, rfl, hS⟩

end Artin

end ModuleCat
