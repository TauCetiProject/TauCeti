/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.LocalizerMorphism
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Equivalence
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Lifting
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.QuasiIso
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Resolution

/-!
# The derived tensor product of DG modules

Let `A` be a differential graded algebra over a commutative ring `R`. For a row-finite twisting
cocycle `m` on a graded set of generators `P`, with free DG left module `K_m = P →₀ A`, the
twisted complexes `M ⊗_A K_m` with coefficients in DG right modules `M` form a functor
`RowFiniteTwistingCocycle.coefficientFunctor` from DG right modules to cochain complexes of
`R`-modules. When `m` is **semi-free**, that is the row relation `y ∈ (m.m x).support` is
well-founded, this functor sends quasi-isomorphisms to quasi-isomorphisms
(`TauCeti.RowFiniteTwistingCocycle.quasiIso_coefficientFunctor_map`): semi-free modules are
K-flat. It is therefore a morphism of localizers
(`TauCeti.RowFiniteTwistingCocycle.coefficientLocalizerMorphism`), and induces, through Mathlib's
`LocalizerMorphism.localizedFunctor`, a functor from any localization of the DG right modules at
the quasi-isomorphisms, such as their derived category, to any localization of the cochain
complexes at the quasi-isomorphisms, such as the derived category of `R`-modules.

Continuation cocycles act naturally in the coefficients
(`TauCeti.RowFiniteContinuationCocycle.continuationNatTrans`), so homologous semi-free cocycles
induce isomorphic functors on the localizations
(`TauCeti.RowFiniteHomologous.localizedFunctorIso`).

For a DG left module `N`, tensoring with its semi-free resolution
(`TauCeti.semifreeResolution`) is the **derived tensor product** `- ⊗^L_A N`
(`TauCeti.derivedTensorLocalizerMorphism`). Any two semi-free resolutions of `N` are homologous
(`TauCeti.exists_rowFiniteHomologous_homotopy`); in particular any other semi-free resolution of
`N`, whose generators live in the same universe, is homologous to the canonical one
(`TauCeti.nonempty_rowFiniteHomologous_semifreeResolution`), so tensoring with it computes the
same functor up to isomorphism (`TauCeti.nonempty_localizedFunctor_iso_derivedTensor`).

## Main definitions

* `TauCeti.RowFiniteTwistingCocycle.coefficientFunctor`: `M ↦ M ⊗_A K_m`.
* `TauCeti.RowFiniteTwistingCocycle.coefficientLocalizerMorphism`: the same functor, for a
  semi-free cocycle, as a morphism of localizers for the quasi-isomorphisms.
* `TauCeti.RowFiniteContinuationCocycle.continuationNatTrans`: the natural transformation
  induced by a continuation cocycle.
* `TauCeti.RowFiniteHomologous.localizedFunctorIso`: the isomorphism of localized functors
  induced by homologous semi-free cocycles.
* `TauCeti.derivedTensorLocalizerMorphism`: the derived tensor product with a DG left module.

## Main results

* `TauCeti.RowFiniteTwistingCocycle.quasiIso_coefficientFunctor_map`: semi-free modules are
  K-flat.
* `TauCeti.nonempty_rowFiniteHomologous_semifreeResolution`: a semi-free resolution is
  homologous to the canonical one.
* `TauCeti.nonempty_localizedFunctor_iso_derivedTensor`: the derived tensor product does not
  depend on the semi-free resolution.

## References

* B. Keller, *Deriving DG categories*, Ann. Sci. École Norm. Sup. (4) 27 (1994), Sections 3 and
  6.
* Y. Félix, S. Halperin, J.-C. Thomas, *Rational Homotopy Theory*, GTM 205, Springer, 2001,
  Chapter 6.
-/

public noncomputable section

open CategoryTheory

namespace TauCeti

universe uR uA uM uP uN

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} (hA : IsDGAlgebra 𝒜 d)

/-! ### Tensoring with a row-finite twisted module -/

namespace RowFiniteTwistingCocycle

variable {P : Type uP} {ind : P → ℤ} (m : RowFiniteTwistingCocycle 𝒜 d P ind)

/-- **Tensoring with a row-finite twisted module**: the functor `M ↦ M ⊗_A K_m` from DG right
modules to cochain complexes, sending a DG right module to the twisted complex with coefficients
in it and a morphism to the map applying it to every coefficient. -/
-- Exposed so that the objects and maps reduce to the twisted complexes and coefficient maps,
-- which the natural transformations of continuation maps below are built from.
@[expose]
def coefficientFunctor :
    DGRightModuleCat.{uR, uA, uM} hA ⥤ CochainComplex (ModuleCat.{max uP uM} R) ℤ where
  obj M := m.coefficientCochainComplex M.isDGRightModule
  map {M N} f := m.coefficientCochainComplexMap M.isDGRightModule N.isDGRightModule f
  map_id M := m.coefficientCochainComplexMap_id M.isDGRightModule
  map_comp {M N Q} f g :=
    m.coefficientCochainComplexMap_comp M.isDGRightModule N.isDGRightModule Q.isDGRightModule f g

@[simp]
theorem coefficientFunctor_obj (M : DGRightModuleCat.{uR, uA, uM} hA) :
    (m.coefficientFunctor hA).obj M = m.coefficientCochainComplex M.isDGRightModule :=
  (rfl)

@[simp]
theorem coefficientFunctor_map {M N : DGRightModuleCat.{uR, uA, uM} hA} (f : M ⟶ N) :
    (m.coefficientFunctor hA).map f =
      m.coefficientCochainComplexMap M.isDGRightModule N.isDGRightModule f :=
  (rfl)

variable (hm : WellFounded fun y x ↦ y ∈ (m.m x).support)

include hm in
/-- **Semi-free modules are K-flat**: for a semi-free cocycle `m`, tensoring with `K_m` sends
quasi-isomorphisms of DG right modules to quasi-isomorphisms. -/
theorem quasiIso_coefficientFunctor_map {M N : DGRightModuleCat.{uR, uA, uM} hA} {f : M ⟶ N}
    (hf : DGRightModuleCat.IsQuasiIso f) : QuasiIso ((m.coefficientFunctor hA).map f) :=
  m.quasiIso_coefficientCochainComplexMap M.isDGRightModule N.isDGRightModule hm hf

/-- For a semi-free cocycle `m`, tensoring with `K_m` as a morphism of localizers from the
quasi-isomorphisms of DG right modules to the quasi-isomorphisms of cochain complexes. Its
`LocalizerMorphism.localizedFunctor` is the induced functor on the localizations, such as the
derived categories. -/
-- Exposed so that its functor reduces to `coefficientFunctor`.
@[expose]
def coefficientLocalizerMorphism :
    LocalizerMorphism (DGRightModuleCat.quasiIsos.{uR, uA, uM} hA)
      (HomologicalComplex.quasiIso (ModuleCat.{max uP uM} R) (ComplexShape.up ℤ)) where
  functor := m.coefficientFunctor hA
  map _ _ f hf := (HomologicalComplex.mem_quasiIso_iff _).2
    (m.quasiIso_coefficientFunctor_map hA hm ((DGRightModuleCat.quasiIsos_iff f).1 hf))

@[simp]
theorem coefficientLocalizerMorphism_functor :
    (m.coefficientLocalizerMorphism hA hm).functor = m.coefficientFunctor hA :=
  (rfl)

end RowFiniteTwistingCocycle

/-! ### Naturality of continuation maps -/

open RowFiniteTwistingCocycle

namespace RowFiniteContinuationCocycle

variable {hA} {P Q : Type uP} {indP : P → ℤ} {indQ : Q → ℤ}
  {mP : RowFiniteTwistingCocycle 𝒜 d P indP} {mQ : RowFiniteTwistingCocycle 𝒜 d Q indQ}
  (ν : RowFiniteContinuationCocycle mP mQ)

variable (hA) in
/-- The continuation maps of a row-finite continuation cocycle from `mP` to `mQ`, as a natural
transformation `M ⊗_A K_{mP} ⟶ M ⊗_A K_{mQ}` of functors of the DG right module `M`. -/
def continuationNatTrans :
    mP.coefficientFunctor.{uR, uA, uM} hA ⟶ mQ.coefficientFunctor hA where
  app M := ν.continuationHom M.isDGRightModule
  naturality {M N} f :=
    ν.coefficientCochainComplexMap_comp_continuationHom M.isDGRightModule N.isDGRightModule f

@[simp]
theorem continuationNatTrans_app (M : DGRightModuleCat.{uR, uA, uM} hA) :
    (ν.continuationNatTrans hA).app M = ν.continuationHom M.isDGRightModule :=
  (rfl)

end RowFiniteContinuationCocycle

/-! ### Homologous cocycles induce isomorphic functors -/

namespace RowFiniteHomologous

variable {hA} {P Q : Type uP} {indP : P → ℤ} {indQ : Q → ℤ}
  {mP : RowFiniteTwistingCocycle 𝒜 d P indP} {mQ : RowFiniteTwistingCocycle 𝒜 d Q indQ}
  (H : RowFiniteHomologous hA mP mQ)
  {D₁ D₂ : Type*} [Category* D₁] [Category* D₂]
  (L₁ : DGRightModuleCat.{uR, uA, uM} hA ⥤ D₁) [L₁.IsLocalization (DGRightModuleCat.quasiIsos hA)]
  (L₂ : CochainComplex (ModuleCat.{max uP uM} R) ℤ ⥤ D₂)
  [L₂.IsLocalization (HomologicalComplex.quasiIso (ModuleCat.{max uP uM} R) (ComplexShape.up ℤ))]

/-- The image of a continuation map of homologous cocycles in a localization of the cochain
complexes at the quasi-isomorphisms is an isomorphism, since it is a homotopy equivalence. -/
theorem isIso_map_continuationHom {M : Type uM} [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M]
    [IsScalarTower R Aᵐᵒᵖ M] {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
    {dM : M →ₗ[R] M} (hM : IsDGRightModule hA ℳ dM) :
    IsIso (L₂.map (H.ν.continuationHom hM)) :=
  Localization.inverts L₂ (HomologicalComplex.quasiIso _ _) _
    ((HomologicalComplex.mem_quasiIso_iff _).2 (by
      simpa only [homotopyEquiv_hom] using (H.homotopyEquiv hM).quasiIso_hom))

/-- Homologous cocycles `mP` and `mQ` give isomorphic functors `M ↦ M ⊗_A K_{mP}` and
`M ↦ M ⊗_A K_{mQ}` after localizing the cochain complexes at the quasi-isomorphisms, through the
continuation maps. -/
def coefficientFunctorCompIso :
    mP.coefficientFunctor.{uR, uA, uM} hA ⋙ L₂ ≅ mQ.coefficientFunctor hA ⋙ L₂ :=
  haveI : ∀ M, IsIso ((Functor.whiskerRight (H.ν.continuationNatTrans hA) L₂).app M) :=
    fun M ↦ H.isIso_map_continuationHom L₂ M.isDGRightModule
  haveI := NatIso.isIso_of_isIso_app (Functor.whiskerRight (H.ν.continuationNatTrans hA) L₂)
  asIso (Functor.whiskerRight (H.ν.continuationNatTrans hA) L₂)

@[simp]
theorem coefficientFunctorCompIso_hom_app (M : DGRightModuleCat.{uR, uA, uM} hA) :
    (H.coefficientFunctorCompIso L₂).hom.app M =
      L₂.map (H.ν.continuationHom M.isDGRightModule) :=
  (rfl)

variable (hmP : WellFounded fun y x ↦ y ∈ (mP.m x).support)
  (hmQ : WellFounded fun y x ↦ y ∈ (mQ.m x).support)

/-- **Homologous semi-free cocycles induce isomorphic derived functors**: the functors induced by
`M ↦ M ⊗_A K_{mP}` and `M ↦ M ⊗_A K_{mQ}` on the localizations at the quasi-isomorphisms are
isomorphic, through the continuation maps. -/
def localizedFunctorIso :
    (mP.coefficientLocalizerMorphism hA hmP).localizedFunctor L₁ L₂ ≅
      (mQ.coefficientLocalizerMorphism hA hmQ).localizedFunctor L₁ L₂ :=
  Localization.liftNatIso L₁ (DGRightModuleCat.quasiIsos hA)
    ((mP.coefficientLocalizerMorphism hA hmP).functor ⋙ L₂)
    ((mQ.coefficientLocalizerMorphism hA hmQ).functor ⋙ L₂) _ _
    (H.coefficientFunctorCompIso L₂)

/-- On the image of a DG right module, `localizedFunctorIso` is the image of the continuation map,
read through the identifications of the localized functors on such images. -/
theorem localizedFunctorIso_hom_app (M : DGRightModuleCat.{uR, uA, uM} hA) :
    (H.localizedFunctorIso L₁ L₂ hmP hmQ).hom.app (L₁.obj M) =
      (Localization.Lifting.iso L₁ (DGRightModuleCat.quasiIsos hA)
          ((mP.coefficientLocalizerMorphism hA hmP).functor ⋙ L₂)
          ((mP.coefficientLocalizerMorphism hA hmP).localizedFunctor L₁ L₂)).hom.app M ≫
        L₂.map (H.ν.continuationHom M.isDGRightModule) ≫
        (Localization.Lifting.iso L₁ (DGRightModuleCat.quasiIsos hA)
          ((mQ.coefficientLocalizerMorphism hA hmQ).functor ⋙ L₂)
          ((mQ.coefficientLocalizerMorphism hA hmQ).localizedFunctor L₁ L₂)).inv.app M :=
  Localization.liftNatTrans_app _ _ _ _ _ _ _ M

end RowFiniteHomologous

/-! ### The derived tensor product with a DG left module -/

section DerivedTensor

variable {N : Type uN} [AddCommGroup N] [Module R N] [Module A N]
  (𝒩 : ℤ → Submodule R N) (dN : N →ₗ[R] N)

/-- **The derived tensor product** `- ⊗^L_A N` with a DG left module `N`: tensoring DG right
modules with the semi-free resolution of `N`, as a morphism of localizers for the
quasi-isomorphisms. Its `LocalizerMorphism.localizedFunctor` is the derived functor on the
localizations, such as the derived categories. -/
def derivedTensorLocalizerMorphism :
    LocalizerMorphism (DGRightModuleCat.quasiIsos.{uR, uA, uM} hA)
      (HomologicalComplex.quasiIso (ModuleCat.{max (max uA uN) uM} R) (ComplexShape.up ℤ)) :=
  (semifreeResolution 𝒜 d 𝒩 dN).coefficientLocalizerMorphism hA
    wellFounded_mem_support_semifreeResolution

/-- The derived tensor product is the morphism of localizers of the semi-free resolution, through
which homologous cocycles give isomorphic localized functors
(`TauCeti.RowFiniteHomologous.localizedFunctorIso`). -/
theorem derivedTensorLocalizerMorphism_def :
    derivedTensorLocalizerMorphism.{uR, uA, uM} hA 𝒩 dN =
      (semifreeResolution 𝒜 d 𝒩 dN).coefficientLocalizerMorphism hA
        wellFounded_mem_support_semifreeResolution :=
  (rfl)

@[simp]
theorem derivedTensorLocalizerMorphism_functor :
    (derivedTensorLocalizerMorphism.{uR, uA, uM} hA 𝒩 dN).functor =
      (semifreeResolution 𝒜 d 𝒩 dN).coefficientFunctor hA :=
  (rfl)

variable [IsScalarTower R A N] [SetLike.GradedSMul 𝒜 𝒩] [DirectSum.Decomposition 𝒩]
  {hA 𝒩 dN} {D₁ D₂ : Type*} [Category* D₁] [Category* D₂]
  (L₁ : DGRightModuleCat.{uR, uA, uM} hA ⥤ D₁) [L₁.IsLocalization (DGRightModuleCat.quasiIsos hA)]
  (L₂ : CochainComplex (ModuleCat.{max (max uA uN) uM} R) ℤ ⥤ D₂)
  [L₂.IsLocalization (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))]

/-- **A semi-free resolution is homologous to the canonical one.** Let `mP` be a semi-free
cocycle, with generators in the universe of those of the canonical resolution, and
`ε : K_{mP} → N`, given on generators, a quasi-isomorphism of DG left modules: a degree-preserving
chain map whose relative cycles are relative boundaries. Then `mP` and the canonical semi-free
resolution of `N` (`TauCeti.semifreeResolution`) are homologous. -/
theorem nonempty_rowFiniteHomologous_semifreeResolution (hN : IsDGLeftModule hA 𝒩 dN)
    {P : Type (max uA uN)} {ind : P → ℤ} {mP : RowFiniteTwistingCocycle 𝒜 d P ind}
    (hmP : WellFounded fun y x ↦ y ∈ (mP.m x).support) {ε : P → N}
    (hε : ∀ x, ε x ∈ 𝒩 (-ind x))
    (hεd : ∀ x, Finsupp.linearCombination A ε (mP.m x) = dN (ε x))
    (hεrel : ∀ c w, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m c = 0 →
      Finsupp.linearCombination A ε c = dN w →
        ∃ u v, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m u = c ∧
          Finsupp.linearCombination A ε u + dN v = w) :
    Nonempty (RowFiniteHomologous hA mP (semifreeResolution 𝒜 d 𝒩 dN)) := by
  obtain ⟨H, -⟩ := exists_rowFiniteHomologous_homotopy hmP
    wellFounded_mem_support_semifreeResolution hN hε semifreeResolutionAugmentation_mem hεd
    linearCombination_semifreeResolutionAugmentation_m hεrel
    (exists_rowFiniteTwistedDifferential_semifreeResolution_eq hN)
  exact ⟨H⟩

/-- **The derived tensor product does not depend on the resolution.** Let `mP` be a semi-free
cocycle, with generators in the universe of those of the canonical resolution, and
`ε : K_{mP} → N`, given on generators, a quasi-isomorphism of DG left modules: a degree-preserving
chain map whose relative cycles are relative boundaries. Then tensoring with `K_{mP}` induces a
functor on the localizations isomorphic to the derived tensor product `- ⊗^L_A N`. -/
theorem nonempty_localizedFunctor_iso_derivedTensor (hN : IsDGLeftModule hA 𝒩 dN)
    {P : Type (max uA uN)} {ind : P → ℤ} {mP : RowFiniteTwistingCocycle 𝒜 d P ind}
    (hmP : WellFounded fun y x ↦ y ∈ (mP.m x).support) {ε : P → N}
    (hε : ∀ x, ε x ∈ 𝒩 (-ind x))
    (hεd : ∀ x, Finsupp.linearCombination A ε (mP.m x) = dN (ε x))
    (hεrel : ∀ c w, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m c = 0 →
      Finsupp.linearCombination A ε c = dN w →
        ∃ u v, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m u = c ∧
          Finsupp.linearCombination A ε u + dN v = w) :
    Nonempty ((mP.coefficientLocalizerMorphism hA hmP).localizedFunctor L₁ L₂ ≅
      (derivedTensorLocalizerMorphism hA 𝒩 dN).localizedFunctor L₁ L₂) :=
  (nonempty_rowFiniteHomologous_semifreeResolution hN hmP hε hεd hεrel).map fun H ↦
    H.localizedFunctorIso L₁ L₂ hmP wellFounded_mem_support_semifreeResolution

end DerivedTensor

end TauCeti
