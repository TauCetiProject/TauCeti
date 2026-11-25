/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.KFlat.BaseChange
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.DerivabilityStructure
public import TauCeti.Algebra.Homology.Monoidal.KFlat.LeftDerivedTensor
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import TauCeti.RingTheory.Flat.CompletelyFlat
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
import TauCeti.Algebra.Homology.Bifunctor.Single
import TauCeti.Algebra.Homology.ModuleCat.KFlat.Basic

/-!
# Complete flatness in the derived category

Let `A` be a commutative ring and `I` an ideal of `A`. For an object `M` of the derived category
`D(A)` of `A`-modules, the *derived reduction* `M ⊗^L_A A/I` is the derived extension of scalars
along `A → A/I`, an object of `D(A/I)`. The object `M` is `I`-*completely flat* when its derived
reduction is a flat `A/I`-module placed in degree zero, and `I`-*completely faithfully flat* when
that module is faithfully flat. Neither predicate asks `M` to be derived `I`-complete. The object
`M` has `I`-*complete Tor-amplitude* in `[a, b]` when, for every `A/I`-module `N`, the derived
tensor product `(M ⊗^L_A A/I) ⊗^L_{A/I} N` has cohomology only in degrees `a ≤ n ≤ b`.

A flat module `M` placed in degree zero is `I`-completely flat for every ideal `I`: it is K-flat, so
its derived reduction is the ordinary scalar extension `A/I ⊗_A M` in degree zero, which is flat
over `A/I`. Likewise a faithfully flat module is `I`-completely faithfully flat. A completely flat
object has complete Tor-amplitude `[0, 0]`, since its derived reduction is a K-flat complex in
degree zero.

## Main definitions

* `TauCeti.DerivedDeRham.derivedReduction I`: the derived reduction `M ↦ M ⊗^L_A A/I`.
* `TauCeti.DerivedDeRham.IsCompletelyFlat I M`: `M` is `I`-completely flat.
* `TauCeti.DerivedDeRham.IsCompletelyFaithfullyFlat I M`: `M` is `I`-completely faithfully flat.
* `TauCeti.DerivedDeRham.HasCompleteTorAmplitude I a b M`: `M` has `I`-complete Tor-amplitude in
  `[a, b]`.

## Main results

* `TauCeti.DerivedDeRham.isCompletelyFlat_iff`,
  `TauCeti.DerivedDeRham.isCompletelyFaithfullyFlat_iff` and
  `TauCeti.DerivedDeRham.hasCompleteTorAmplitude_iff`: the defining conditions.
* `TauCeti.DerivedDeRham.IsCompletelyFlat.hasCompleteTorAmplitude`: completely flat objects have
  complete Tor-amplitude `[0, 0]`.
* `ModuleCat.isCompletelyFlat_single`: flat modules are `I`-completely flat.
* `ModuleCat.isCompletelyFaithfullyFlat_single`: faithfully flat modules are `I`-completely
  faithfully flat.
* `ModuleCat.isCompletelyFaithfullyFlat_single_iff`: a flat module in degree zero is `I`-completely
  faithfully flat exactly when it is so as a module
  (`TauCeti.DerivedDeRham.IsCompletelyFaithfullyFlatModule`).

The derived reduction of a flat module in degree zero is computed by
`TauCeti.derivedExtendScalarsSingleIso`, and its flatness over `A/I` by
`ModuleCat.flat_extendScalars` and `ModuleCat.faithfullyFlat_extendScalars`.

## References

* B. Bhatt, M. Morrow and P. Scholze, *Topological Hochschild homology and integral `p`-adic
  Hodge theory*, Publ. Math. IHÉS 129 (2019), Definition 4.1.
* B. Bhatt and P. Scholze, *Prisms and prismatic cohomology*, arXiv:1905.08229v4, §1.2.
-/

public section

noncomputable section

open CategoryTheory Limits DerivedCategory

universe w w' u

namespace TauCeti.DerivedDeRham

variable {A : Type u} [CommRing A] (I : Ideal A)
  [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w'} (ModuleCat.{u} (A ⧸ I))]

/-- **The derived reduction** `M ↦ M ⊗^L_A A/I` from `D(A)` to `D(A/I)`: the derived extension
of scalars along the quotient map `A → A/I`. -/
abbrev derivedReduction :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} (A ⧸ I)) :=
  derivedExtendScalars.{u, w, w'} (Ideal.Quotient.mk I)

/-- **Complete flatness.** An object `M` of `D(A)` is `I`-completely flat when its derived
reduction `M ⊗^L_A A/I` is isomorphic to a flat `A/I`-module placed in degree zero. The predicate
does not ask `M` to be derived `I`-complete (Bhatt, Morrow and Scholze, *Topological Hochschild
homology and integral `p`-adic Hodge theory*, Definition 4.1, for `I = (p)`). -/
def IsCompletelyFlat (M : DerivedCategory (ModuleCat.{u} A)) : Prop :=
  ∃ F : ModuleCat.{u} (A ⧸ I), Module.Flat (A ⧸ I) F ∧
    Nonempty ((derivedReduction I).obj M ≅ (singleFunctor _ 0).obj F)

/-- **Complete faithful flatness.** An object `M` of `D(A)` is `I`-completely faithfully flat when
its derived reduction `M ⊗^L_A A/I` is isomorphic to a faithfully flat `A/I`-module placed in
degree zero. -/
def IsCompletelyFaithfullyFlat (M : DerivedCategory (ModuleCat.{u} A)) : Prop :=
  ∃ F : ModuleCat.{u} (A ⧸ I), Module.FaithfullyFlat (A ⧸ I) F ∧
    Nonempty ((derivedReduction I).obj M ≅ (singleFunctor _ 0).obj F)

/-- **Complete Tor-amplitude.** An object `M` of `D(A)` has `I`-complete Tor-amplitude in
`[a, b]` when for every `A/I`-module `N` the derived tensor product
`(M ⊗^L_A A/I) ⊗^L_{A/I} N[0]` has vanishing cohomology outside the degrees `a ≤ n ≤ b`. -/
def HasCompleteTorAmplitude (a b : ℤ) (M : DerivedCategory (ModuleCat.{u} A)) : Prop :=
  ∀ (N : ModuleCat.{u} (A ⧸ I)) (n : ℤ), n < a ∨ b < n →
    IsZero ((homologyFunctor (ModuleCat.{u} (A ⧸ I)) n).obj
      (((derivedTensor (ModuleCat.{u} (A ⧸ I))).obj ((derivedReduction I).obj M)).obj
        ((singleFunctor _ 0).obj N)))

variable {I}

/-- The defining condition of `I`-complete flatness. -/
theorem isCompletelyFlat_iff {M : DerivedCategory (ModuleCat.{u} A)} :
    IsCompletelyFlat I M ↔ ∃ F : ModuleCat.{u} (A ⧸ I), Module.Flat (A ⧸ I) F ∧
      Nonempty ((derivedReduction I).obj M ≅ (singleFunctor _ 0).obj F) :=
  Iff.rfl

/-- The defining condition of `I`-complete faithful flatness. -/
theorem isCompletelyFaithfullyFlat_iff {M : DerivedCategory (ModuleCat.{u} A)} :
    IsCompletelyFaithfullyFlat I M ↔ ∃ F : ModuleCat.{u} (A ⧸ I), Module.FaithfullyFlat (A ⧸ I) F ∧
      Nonempty ((derivedReduction I).obj M ≅ (singleFunctor _ 0).obj F) :=
  Iff.rfl

/-- The defining condition of `I`-complete Tor-amplitude in `[a, b]`. -/
theorem hasCompleteTorAmplitude_iff {a b : ℤ} {M : DerivedCategory (ModuleCat.{u} A)} :
    HasCompleteTorAmplitude I a b M ↔ ∀ (N : ModuleCat.{u} (A ⧸ I)) (n : ℤ), n < a ∨ b < n →
      IsZero ((homologyFunctor (ModuleCat.{u} (A ⧸ I)) n).obj
        (((derivedTensor (ModuleCat.{u} (A ⧸ I))).obj ((derivedReduction I).obj M)).obj
          ((singleFunctor _ 0).obj N))) :=
  Iff.rfl

/-- A completely faithfully flat object is completely flat. -/
theorem IsCompletelyFaithfullyFlat.isCompletelyFlat {M : DerivedCategory (ModuleCat.{u} A)}
    (h : IsCompletelyFaithfullyFlat I M) : IsCompletelyFlat I M := by
  obtain ⟨F, _, e⟩ := h
  exact ⟨F, inferInstance, e⟩

/-- Complete flatness is invariant under isomorphism in `D(A)`. -/
theorem IsCompletelyFlat.of_iso {M M' : DerivedCategory (ModuleCat.{u} A)}
    (h : IsCompletelyFlat I M) (e : M ≅ M') : IsCompletelyFlat I M' := by
  obtain ⟨F, hF, ⟨e'⟩⟩ := h
  exact ⟨F, hF, ⟨(derivedReduction I).mapIso e.symm ≪≫ e'⟩⟩

/-- Complete faithful flatness is invariant under isomorphism in `D(A)`. -/
theorem IsCompletelyFaithfullyFlat.of_iso {M M' : DerivedCategory (ModuleCat.{u} A)}
    (h : IsCompletelyFaithfullyFlat I M) (e : M ≅ M') :
    IsCompletelyFaithfullyFlat I M' := by
  obtain ⟨F, hF, ⟨e'⟩⟩ := h
  exact ⟨F, hF, ⟨(derivedReduction I).mapIso e.symm ≪≫ e'⟩⟩

/-- Complete Tor-amplitude is invariant under isomorphism in `D(A)`. -/
theorem HasCompleteTorAmplitude.of_iso {a b : ℤ} {M M' : DerivedCategory (ModuleCat.{u} A)}
    (h : HasCompleteTorAmplitude I a b M) (e : M ≅ M') :
    HasCompleteTorAmplitude I a b M' := fun N n hn ↦
  (h N n hn).of_iso ((homologyFunctor _ n).mapIso
    (((derivedTensor _).mapIso ((derivedReduction I).mapIso e.symm)).app _))

/-- Complete Tor-amplitude in `[a, b]` implies complete Tor-amplitude in every larger interval. -/
theorem HasCompleteTorAmplitude.mono {a b a' b' : ℤ} {M : DerivedCategory (ModuleCat.{u} A)}
    (h : HasCompleteTorAmplitude I a b M) (ha : a' ≤ a) (hb : b ≤ b') :
    HasCompleteTorAmplitude I a' b' M := fun N n hn ↦
  h N n (hn.imp (fun h' ↦ h'.trans_le ha) (fun h' ↦ hb.trans_lt h'))

/-- **Completely flat objects have complete Tor-amplitude `[0, 0]`.** If the derived reduction
of `M` is a flat `A/I`-module `F` in degree zero, then for every `A/I`-module `N` the derived
tensor product `F ⊗^L_{A/I} N` is computed by the K-flat complex `F[0]`, and is concentrated in
degree zero. -/
theorem IsCompletelyFlat.hasCompleteTorAmplitude {M : DerivedCategory (ModuleCat.{u} A)}
    (h : IsCompletelyFlat I M) : HasCompleteTorAmplitude I 0 0 M := by
  obtain ⟨F, hF, ⟨e⟩⟩ := h
  intro N n hn
  have hn' : n ≠ 0 := by omega
  let S := HomologicalComplex.single (ModuleCat.{u} (A ⧸ I)) (.up ℤ) 0
  have e' := (homologyFunctor _ n).mapIso
    (((derivedTensor _).mapIso (e ≪≫ (singleFunctorIsoCompQ _ 0).app F)).app
        ((singleFunctor _ 0).obj N) ≪≫
      ((derivedTensor _).obj (Q.obj (S.obj F))).mapIso ((singleFunctorIsoCompQ _ 0).app N) ≪≫
      CochainComplex.derivedTensorKFlatLeftIso (S.obj F) (S.obj N)) ≪≫
    (homologyFunctorFactors _ n).app _
  refine IsZero.of_iso ?_ e'
  exact ShortComplex.isZero_homology_of_isZero_X₂ _
    (HomologicalComplex.isZero_mapBifunctor_single_single_X _ _ 0 0 F N (by simpa using hn'.symm))

end TauCeti.DerivedDeRham

/-! ### Flat modules -/

namespace ModuleCat

open TauCeti TauCeti.DerivedDeRham

variable {A : Type u} [CommRing A] {I : Ideal A}
  [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w'} (ModuleCat.{u} (A ⧸ I))]

/-- **Flat modules are completely flat.** A flat `A`-module placed in degree zero is
`I`-completely flat for every ideal `I`. -/
theorem isCompletelyFlat_single (M : ModuleCat.{u} A) [Module.Flat A M] :
    IsCompletelyFlat I ((singleFunctor _ 0).obj M) :=
  ⟨_, inferInstance, ⟨derivedExtendScalarsSingleIso _ M⟩⟩

/-- **Faithfully flat modules are completely faithfully flat.** A faithfully flat `A`-module
placed in degree zero is `I`-completely faithfully flat for every ideal `I`. -/
theorem isCompletelyFaithfullyFlat_single (M : ModuleCat.{u} A) [Module.FaithfullyFlat A M] :
    IsCompletelyFaithfullyFlat I ((singleFunctor _ 0).obj M) :=
  ⟨_, inferInstance, ⟨derivedExtendScalarsSingleIso _ M⟩⟩

/-- **Comparison with the module form, for flat modules.** A flat `A`-module `M` placed in degree
zero is `I`-completely faithfully flat in `D(A)` exactly when it is so as a module, that is, when
`A/I ⊗_A M` is faithfully flat over `A/I`: its derived reduction is `A/I ⊗_A M` in degree zero. -/
theorem isCompletelyFaithfullyFlat_single_iff (M : ModuleCat.{u} A) [Module.Flat A M] :
    IsCompletelyFaithfullyFlat I ((singleFunctor _ 0).obj M) ↔
      IsCompletelyFaithfullyFlatModule A I M := by
  rw [isCompletelyFaithfullyFlatModule_iff]
  refine ⟨fun ⟨F, hF, ⟨e⟩⟩ ↦ ⟨isCompletelyFlatModule_of_flat M, ?_⟩, fun ⟨_, h⟩ ↦
    ⟨(ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj M, h, ⟨derivedExtendScalarsSingleIso _ M⟩⟩⟩
  let e' := (singleFunctor (ModuleCat.{u} (A ⧸ I)) 0).preimageIso
    (e.symm ≪≫ derivedExtendScalarsSingleIso _ M)
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e'.toLinearEquiv.symm

end ModuleCat
