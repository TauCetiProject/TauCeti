/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AB
public import TauCeti.AlgebraicTopology.DGLocalSystem.Components
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.DerivedTensor
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.SemifreeModel

/-!
# Brown models over a space that is not path connected

Let `R` be a commutative ring and `B` a space with a basepoint `b_c` chosen in each path component
`c` (`TauCeti.PathComponentBasepoints`). A DG local system on `B` is a family `(𝓕_c)` of right DG
modules over the chain algebras `C_*(Ω_{b_c} B; R)` of the Moore loops at the chosen basepoints
(`TauCeti.DGLocalSystemFamily`), and a family of twisting cocycles `m_c` over these algebras has the
twisted complex `⨁_c 𝓕_c ⊗ K_{m_c}` (`TauCeti.DGLocalSystemFamily.twistedComplex`). The Moore paths
from `b_c` never leave the path component `c`, so Brown's resolution of the ground ring is built
component by component: a family of Brown models `M_c` of the chains `C_*(P_{b_c} B; R)` on the
Moore paths starting at the chosen basepoints (`TauCeti.BrownModel`). For a CW complex these are
the models `TauCeti.pathComponentBrownModel` on the cells of each path component, whose generators
are together the cells of the complex, each once
(`Topology.CWComplex.sigmaPathComponentCellEquiv`).

This file shows that the twisted complex of such a family computes the derived tensor products
with the ground ring over all the path components at once.

* The **derived tensor product with the ground ring over the path components**
  (`TauCeti.DGLocalSystemFamily.derivedTensorLocalizerMorphism`) is the twisted complex of the
  family of canonical semi-free resolutions of `R`, on which the loop chains act through their
  augmentation. Its value on a family is the direct sum `⨁_c 𝓕_c ⊗^L R` of the derived tensor
  products of the components
  (`TauCeti.DGLocalSystemFamily.derivedTensorLocalizerMorphism_functor_obj`).
* A Brown model is homologous to the semi-free resolution of `R`
  (`TauCeti.BrownModel.nonempty_rowFiniteHomologous_semifreeResolution`), so on the localizations at
  the componentwise quasi-isomorphisms of families (`TauCeti.DGLocalSystemFamily.quasiIsos`) and at
  the quasi-isomorphisms of cochain complexes, the twisted complex of a family of Brown models
  induces a functor isomorphic to this derived tensor product
  (`TauCeti.BrownModel.nonempty_twistedComplexLocalizedFunctor_iso_derivedTensor`). Two families of
  Brown models therefore induce isomorphic functors
  (`TauCeti.BrownModel.nonempty_twistedComplexLocalizedFunctor_iso`).
* On homology, the twisted complex of a family of Brown models has in each degree the direct sum
  over the path components of the homologies of the derived tensor products, the groups
  `Tor^{C_*(Ω_{b_c} B; R)}(𝓕_c, R)` (`TauCeti.BrownModel.nonempty_homology_twistedComplex_iso`).
* For a CW complex containing every path component, Brown's models of the path components compute
  the derived tensor product over the path components
  (`TauCeti.nonempty_pathComponentBrownModel_twistedComplexLocalizedFunctor_iso_derivedTensor`).

## Implementation notes

The generators of all the cocycles of a family live in the universe of the coefficient modules
(`TauCeti.DGLocalSystemFamily.twistedComplex`), and those of the canonical semi-free resolution in
the universe of the loop chains. The coefficient families of the derived statements therefore have
carriers in the universe of the loop chains, which contains those of `B` and of `R`. For a CW
complex, `B` and `R` lie in `Type`, as in `TauCeti.pathComponentBrownModel`.

## Main definitions

* `TauCeti.DGLocalSystemFamily.derivedTensorLocalizerMorphism β R`: the derived tensor product
  `⨁_c 𝓕_c ⊗^L R` over the path components, as a morphism of localizers.

## Main results

* `TauCeti.BrownModel.nonempty_twistedComplexLocalizedFunctor_iso_derivedTensor`: the twisted
  complex of a family of Brown models computes the derived tensor product over the path
  components.
* `TauCeti.BrownModel.nonempty_twistedComplexLocalizedFunctor_iso`: two families of Brown models
  induce isomorphic functors on the localizations.
* `TauCeti.BrownModel.nonempty_homology_twistedComplex_iso`: the homology of the twisted complex of
  a family of Brown models is the direct sum of the groups `Tor^{C_*(Ω_{b_c} B; R)}(𝓕_c, R)`.
* `TauCeti.nonempty_pathComponentBrownModel_twistedComplexLocalizedFunctor_iso_derivedTensor`: the
  case of the models of the path components of a CW complex.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3, 4 and 13.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uB uH uR uM

namespace TauCeti

variable {B : Type uB} [TopologicalSpace B] {β : PathComponentBasepoints B} {R : Type uR}
  [CommRing R]

namespace DGLocalSystemFamily

variable (β R)

/-- **The derived tensor product with the ground ring over the path components**: the twisted
complex `⨁_c 𝓕_c ⊗ K_c` of the family of canonical semi-free resolutions `K_c` of `R` over the
chains `C_*(Ω_{b_c} B; R)` on the Moore loops at the chosen basepoints, on which the loop chains act
through their augmentation, as a morphism of localizers. Its value on a family is the direct sum of
the derived tensor products `𝓕_c ⊗^L R` of the components
(`TauCeti.DGLocalSystemFamily.derivedTensorLocalizerMorphism_functor_obj`). -/
def derivedTensorLocalizerMorphism :
    LocalizerMorphism (quasiIsos β R : MorphismProperty (DGLocalSystemFamily.{max uB uR} β R))
      (HomologicalComplex.quasiIso (ModuleCat.{max uB uR} R) (ComplexShape.up ℤ)) :=
  twistedComplexLocalizerMorphism
    (fun c ↦ semifreeResolution (R := R) (A := loopChainAlgebra B (β.point c) R)
      (cubicalChainGrading (MooreLoopSpace B (β.point c)) R)
      (cubicalChainDifferential (MooreLoopSpace B (β.point c)) R)
      (loopChainAugmentation B (β.point c) R).bimoduleGrading
      (loopChainAugmentation B (β.point c) R).bimoduleDifferential)
    fun _ ↦ wellFounded_mem_support_semifreeResolution

/-- The derived tensor product over the path components is the morphism of localizers of the
family of semi-free resolutions, through which families of homologous cocycles give isomorphic
localized functors (`TauCeti.DGLocalSystemFamily.twistedComplexLocalizedFunctorIso`). -/
theorem derivedTensorLocalizerMorphism_def :
    DGLocalSystemFamily.derivedTensorLocalizerMorphism β R =
      twistedComplexLocalizerMorphism
        (fun c ↦ semifreeResolution (R := R) (A := loopChainAlgebra B (β.point c) R)
          (cubicalChainGrading (MooreLoopSpace B (β.point c)) R)
          (cubicalChainDifferential (MooreLoopSpace B (β.point c)) R)
          (loopChainAugmentation B (β.point c) R).bimoduleGrading
          (loopChainAugmentation B (β.point c) R).bimoduleDifferential)
        fun _ ↦ wellFounded_mem_support_semifreeResolution :=
  (rfl)

@[simp]
theorem derivedTensorLocalizerMorphism_functor :
    (DGLocalSystemFamily.derivedTensorLocalizerMorphism β R).functor =
      twistedComplexFunctor
        (fun c ↦ semifreeResolution (R := R) (A := loopChainAlgebra B (β.point c) R)
          (cubicalChainGrading (MooreLoopSpace B (β.point c)) R)
          (cubicalChainDifferential (MooreLoopSpace B (β.point c)) R)
          (loopChainAugmentation B (β.point c) R).bimoduleGrading
          (loopChainAugmentation B (β.point c) R).bimoduleDifferential) :=
  (rfl)

/-- The derived tensor product over the path components sends a family `(𝓕_c)` to the direct sum
of the derived tensor products `𝓕_c ⊗^L R` (`TauCeti.derivedTensorLocalizerMorphism`) of its
components. -/
theorem derivedTensorLocalizerMorphism_functor_obj (𝓕 : DGLocalSystemFamily.{max uB uR} β R) :
    (DGLocalSystemFamily.derivedTensorLocalizerMorphism β R).functor.obj 𝓕 =
      ∐ fun c ↦ (TauCeti.derivedTensorLocalizerMorphism (loopChain_isDGAlgebra B (β.point c) R)
        (loopChainAugmentation B (β.point c) R).bimoduleGrading
        (loopChainAugmentation B (β.point c) R).bimoduleDifferential).functor.obj (𝓕 c) := by
  simp only [derivedTensorLocalizerMorphism_functor, twistedComplexFunctor_obj,
    TauCeti.derivedTensorLocalizerMorphism_functor, RowFiniteTwistingCocycle.coefficientFunctor_obj]

end DGLocalSystemFamily

namespace BrownModel

open DGLocalSystemFamily

variable {H : Type uH}

/-- **Families of Brown models induce isomorphic derived functors.** For two families of Brown
models `M_c` and `M'_c` at the chosen basepoints, such as those of two CW structures, with
generators in the universe of the coefficients, the twisted complexes `⨁_c 𝓕_c ⊗ K_{M_c}` and
`⨁_c 𝓕_c ⊗ K_{M'_c}` induce isomorphic functors on any localizations at the componentwise
quasi-isomorphisms and at the quasi-isomorphisms. -/
theorem nonempty_twistedComplexLocalizedFunctor_iso
    [HasColimitsOfShape (Discrete (ZerothHomotopy B)) (ModuleCat.{uM} R)]
    [HasExactColimitsOfShape (Discrete (ZerothHomotopy B)) (ModuleCat.{uM} R)]
    {P Q : ZerothHomotopy B → Type uM} {indP : ∀ c, P c → ℤ} {indQ : ∀ c, Q c → ℤ}
    (M : ∀ c, BrownModel B (β.point c) H R (P c) (indP c))
    (M' : ∀ c, BrownModel B (β.point c) H R (Q c) (indQ c))
    {D₁ D₂ : Type*} [Category* D₁] [Category* D₂]
    (L₁ : DGLocalSystemFamily.{uM} β R ⥤ D₁) [L₁.IsLocalization (quasiIsos β R)]
    (L₂ : CochainComplex (ModuleCat.{uM} R) ℤ ⥤ D₂)
    [L₂.IsLocalization (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))] :
    Nonempty ((twistedComplexLocalizerMorphism (fun c ↦ (M c).cocycle)
        fun c ↦ (M c).wellFounded).localizedFunctor L₁ L₂ ≅
      (twistedComplexLocalizerMorphism (fun c ↦ (M' c).cocycle)
        fun c ↦ (M' c).wellFounded).localizedFunctor L₁ L₂) :=
  ⟨twistedComplexLocalizedFunctorIso _ (fun c ↦
    ((M c).exists_rowFiniteHomologous_homotopy (M' c)).choose) L₁ L₂ _⟩

section DerivedTensor

variable {P : ZerothHomotopy B → Type (max uB uR)} {indP : ∀ c, P c → ℤ}
  (M : ∀ c, BrownModel B (β.point c) H R (P c) (indP c))
  {D₁ D₂ : Type*} [Category* D₁] [Category* D₂]
  (L₁ : DGLocalSystemFamily.{max uB uR} β R ⥤ D₁) [L₁.IsLocalization (quasiIsos β R)]
  (L₂ : CochainComplex (ModuleCat.{max uB uR} R) ℤ ⥤ D₂)
  [L₂.IsLocalization (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))]

/-- **Brown models over the path components compute the derived tensor product with the ground
ring.** For a family of Brown models `M_c` of the chains on the Moore paths starting at the chosen
basepoints, with generators in the universe of the loop chains, the twisted complex
`⨁_c 𝓕_c ⊗ K_{M_c}` induces, on any localizations at the componentwise quasi-isomorphisms and at
the quasi-isomorphisms, a functor isomorphic to the derived tensor product `⨁_c 𝓕_c ⊗^L R` over
the path components. -/
theorem nonempty_twistedComplexLocalizedFunctor_iso_derivedTensor :
    Nonempty ((twistedComplexLocalizerMorphism (fun c ↦ (M c).cocycle)
        fun c ↦ (M c).wellFounded).localizedFunctor L₁ L₂ ≅
      (DGLocalSystemFamily.derivedTensorLocalizerMorphism β R).localizedFunctor L₁ L₂) :=
  ⟨twistedComplexLocalizedFunctorIso _ (fun c ↦
    (M c).nonempty_rowFiniteHomologous_semifreeResolution.some) L₁ L₂ _⟩

/-- **The homology of the twisted complex of a family of Brown models** is, in each degree `n`,
the direct sum over the path components `c` of the homologies of the derived tensor products
`𝓕_c ⊗^L R`, the groups `Tor^{C_*(Ω_{b_c} B; R)}(𝓕_c, R)`. -/
theorem nonempty_homology_twistedComplex_iso (𝓕 : DGLocalSystemFamily.{max uB uR} β R) (n : ℤ) :
    Nonempty ((twistedComplex (fun c ↦ (M c).cocycle) 𝓕).homology n ≅
      ∐ fun c ↦ ((TauCeti.derivedTensorLocalizerMorphism (loopChain_isDGAlgebra B (β.point c) R)
        (loopChainAugmentation B (β.point c) R).bimoduleGrading
        (loopChainAugmentation B (β.point c) R).bimoduleDifferential).functor.obj
          (𝓕 c)).homology n) := by
  let E c := (M c).nonempty_rowFiniteHomologous_semifreeResolution.some
  have := quasiIso_twistedComplexContinuation E 𝓕
  refine ⟨asIso (HomologicalComplex.homologyMap
    (twistedComplexContinuation (fun c ↦ (E c).ν) 𝓕) n) ≪≫
      twistedComplexHomologyIso _ 𝓕 n ≪≫ eqToIso ?_⟩
  simp only [TauCeti.derivedTensorLocalizerMorphism_functor,
    RowFiniteTwistingCocycle.coefficientFunctor_obj]

end DerivedTensor

end BrownModel

section CWComplex

open Topology Topology.RelCWComplex DGLocalSystemFamily

/-- **Brown's resolution of a CW complex that is not path connected.** Let `C` be a CW complex in
`B` containing the path component of each chosen basepoint, for instance all of `B`. Brown's models
of the path components (`TauCeti.pathComponentBrownModel`), one generator for each cell of the
component, give the twisted complex `⨁_c 𝓕_c ⊗ K_c`, which has one free generator for each cell of
`C` when `C` is all of `B` (`Topology.CWComplex.sigmaPathComponentCellEquiv`). On any localizations
at the componentwise quasi-isomorphisms and at the quasi-isomorphisms, it induces a functor
isomorphic to the derived tensor product `⨁_c 𝓕_c ⊗^L R` over the path components. -/
theorem nonempty_pathComponentBrownModel_twistedComplexLocalizedFunctor_iso_derivedTensor
    {B : Type} [TopologicalSpace B] [T2Space B] {C : Set B} [CWComplex C]
    {β : PathComponentBasepoints B} (H : Type*) {R : Type} [CommRing R]
    (hC : ∀ c, pathComponent (β.point c) ⊆ C) {D₁ D₂ : Type*} [Category* D₁] [Category* D₂]
    (L₁ : DGLocalSystemFamily.{0} β R ⥤ D₁) [L₁.IsLocalization (quasiIsos β R)]
    (L₂ : CochainComplex (ModuleCat.{0} R) ℤ ⥤ D₂)
    [L₂.IsLocalization (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))] :
    Nonempty ((twistedComplexLocalizerMorphism
        (fun c ↦ (pathComponentBrownModel H R (hC c)).cocycle)
        fun c ↦ (pathComponentBrownModel H R (hC c)).wellFounded).localizedFunctor L₁ L₂ ≅
      (DGLocalSystemFamily.derivedTensorLocalizerMorphism β R).localizedFunctor L₁ L₂) :=
  BrownModel.nonempty_twistedComplexLocalizedFunctor_iso_derivedTensor
    (fun c ↦ pathComponentBrownModel H R (hC c)) L₁ L₂

end CWComplex

end TauCeti
