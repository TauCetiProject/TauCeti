/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.OfHom
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.DerivedTensor
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Circle

/-!
# Brown's models compute the derived tensor product with the ground ring

Let `R` be a commutative ring, `B` a space with a point `b`, and `C_*(Ω_b B; R)` the chains on the
Moore loops at `b`, augmented to `R` by `TauCeti.loopChainAugmentation`. Through the augmentation,
`R` is a differential graded left module over `C_*(Ω_b B; R)`, concentrated in degree zero with
zero differential: the bimodule `{}_ε R` of the augmentation (`TauCeti.DGAlgHom.toBimodule`), on
which a chain `a` acts by multiplication by `ε(a)`. For a DG local system `𝓕`, a DG right module
over `C_*(Ω_b B; R)`, the cohomology of the derived tensor product `𝓕 ⊗^L R` with this module
(`TauCeti.derivedTensorLocalizerMorphism`) is `Tor^{C_*(Ω_b B; R)}(𝓕, R)`.

Brown's twisted tensor products are semi-free left modules `K_m` over `C_*(Ω_b B; R)`, one free
generator for each cell of a CW structure on `B`, compared with the chains `C_*(P_b B; R)` on the
Moore paths from `b` by a quasi-isomorphism that is linear over the loop chains: Brown models
(`TauCeti.BrownModel`). This file shows that every Brown model computes the derived tensor product
with `R` (`TauCeti.BrownModel.nonempty_localizedFunctor_iso_derivedTensor`): tensoring DG right
modules with `K_m` induces, on any localizations at the quasi-isomorphisms, a functor isomorphic to
`- ⊗^L R`. So the twisted complex `𝓕 ⊗ K_m` has cohomology `Tor^{C_*(Ω_b B; R)}(𝓕, R)`. This
applies to the model of every CW complex, `TauCeti.brownModel`.

The reason is that the based path space is contractible: its augmentation
(`TauCeti.pathFromChainAugmentationHom`), read as a map of left modules to `{}_ε R`, is a
quasi-isomorphism (`TauCeti.exists_differential_eq_and_pathFromChainAugmentationHom_add_eq`), so
the composite of the comparison with it is a quasi-isomorphism from `K_m` onto `R`
(`TauCeti.BrownModel.exists_differential_eq_and_augmentation_add_eq`): a Brown model is a
semi-free resolution of `R`. So it is homologous to the canonical semi-free resolution of `R`
(`TauCeti.BrownModel.nonempty_rowFiniteHomologous_semifreeResolution`), and homologous semi-free
cocycles induce isomorphic functors on the localizations
(`TauCeti.RowFiniteHomologous.localizedFunctorIso`), so a Brown model computes the derived tensor
product with `R`.

For the circle, Brown's resolution `TauCeti.loopCellCocycle` with its comparison
`TauCeti.cycleCellPathComparison` is a Brown model (`TauCeti.loopCellBrownModel`), so
(`TauCeti.nonempty_loopCellCocycle_localizedFunctor_iso_derivedTensor_loopChainAugmentation`) the
two-generator twisted complex `𝓕 e₀ ⊕ 𝓕 e₁` with `D e₁ = ([γ] - [1]) e₀` computes
`𝓕 ⊗^L_{C_*(Ω S¹; R)} R`.

## Implementation notes

The derived tensor product is built from the canonical semi-free resolution, whose generators lie
in the universe of the loop chains, and a model is compared with it through generators in that
same universe. The generators `Unit ⊕ Unit` of `TauCeti.loopCellCocycle` lie in `Type`, so the
circle is treated with coefficients `R : Type`, as in
`TauCeti.exists_loopCellCocycle_expLoop_differential_eq_and_cycleCellPathComparison_add_eq`.

## Main definitions

* `TauCeti.pathFromChainAugmentationHom`: the augmentation `C_*(P_b B; R) → R`, linear over the
  loop chains acting on `R` through their augmentation.

## Main results

* `TauCeti.exists_differential_eq_and_pathFromChainAugmentationHom_add_eq`: the augmentation of the
  chains on the based path space is a quasi-isomorphism onto `R`.
* `TauCeti.BrownModel.exists_differential_eq_and_augmentation_add_eq`: a Brown model is a
  semi-free resolution of the ground ring.
* `TauCeti.BrownModel.nonempty_rowFiniteHomologous_semifreeResolution`: a Brown model is
  homologous to the canonical semi-free resolution of the ground ring.
* `TauCeti.BrownModel.nonempty_localizedFunctor_iso_derivedTensor`: a Brown model computes the
  derived tensor product with the ground ring.
* `TauCeti.nonempty_loopCellCocycle_localizedFunctor_iso_derivedTensor_loopChainAugmentation`:
  Brown's resolution of the circle computes the derived tensor product with the ground ring.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
* B. Keller, *Deriving DG categories*, Ann. Sci. École Norm. Sup. (4) 27 (1994), Section 6.
-/

public noncomputable section

open CategoryTheory

universe uB uR uM

namespace TauCeti

section Augmentation

variable (B : Type uB) [TopologicalSpace B] (b : B) (H : Type*) (R : Type uR) [CommRing R]

/-- **The augmentation of the chains on the based path space, over the loop chains.** The
augmentation `C_*(P_b B; R) → R`, as a map of left modules over `C_*(Ω_b B; R)` to the ground ring
`R` on which the loop chains act through their augmentation, the bimodule `{}_ε R` of
`TauCeti.loopChainAugmentation`. -/
def pathFromChainAugmentationHom :
    cubicalChainModule (MoorePathFrom B b) H R →ₗ[loopChainAlgebra B b R]
      Bimodule (loopChainAugmentation B b R).toGradedAlgHom.toAlgHom where
  toFun m := Bimodule.of _ (cubicalChainModuleAugmentation (MoorePathFrom B b) H R m)
  map_add' m m' := by rw [map_add, map_add]
  map_smul' a m := by
    simp [pathFromChainAugmentation_smul, Algebra.TensorProduct.smul_moduleLeft, Bimodule.smul_of]

variable {B b H R}

/-- The augmentation of the based path chains, read in `R`. -/
@[simp]
theorem bimoduleOf_symm_pathFromChainAugmentationHom
    (m : cubicalChainModule (MoorePathFrom B b) H R) :
    (Bimodule.of _).symm (pathFromChainAugmentationHom B b H R m) =
      cubicalChainModuleAugmentation (MoorePathFrom B b) H R m :=
  (Bimodule.of _).symm_apply_apply _

/-- The augmentation of the based path chains preserves degrees. -/
theorem pathFromChainAugmentationHom_mem {i : ℤ}
    {m : cubicalChainModule (MoorePathFrom B b) H R}
    (hm : m ∈ cubicalChainModuleGrading (MoorePathFrom B b) H R i) :
    pathFromChainAugmentationHom B b H R m ∈ (loopChainAugmentation B b R).bimoduleGrading i := by
  rw [DGAlgHom.mem_bimoduleGrading_iff, bimoduleOf_symm_pathFromChainAugmentationHom]
  exact cubicalChainModuleAugmentation_mem hm

/-- The augmentation of the based path chains vanishes on boundaries, so it commutes with the
differentials. -/
theorem pathFromChainAugmentationHom_differential
    (m : cubicalChainModule (MoorePathFrom B b) H R) :
    pathFromChainAugmentationHom B b H R (cubicalChainModuleDifferential _ H R m) =
      (loopChainAugmentation B b R).bimoduleDifferential
        (pathFromChainAugmentationHom B b H R m) := by
  rw [(loopChainAugmentation B b R).bimoduleDifferential_eq_zero rfl, LinearMap.zero_apply]
  exact (Bimodule.of _).symm.injective (by simp)

/-- **The augmentation of the based path chains is a quasi-isomorphism onto the ground ring**:
every relative cycle `(u, w)` of `TauCeti.pathFromChainAugmentationHom`, with `d u = 0` and
`ε(u) = 0`, is a relative boundary `(d u', ε(u'))`. The based path space is contractible, so `u`
is a boundary `d v`, and the cycle `[b]` of augmentation `1` corrects the augmentation of `v`. -/
theorem exists_differential_eq_and_pathFromChainAugmentationHom_add_eq
    (u : cubicalChainModule (MoorePathFrom B b) H R)
    (w : Bimodule (loopChainAugmentation B b R).toGradedAlgHom.toAlgHom)
    (hu : cubicalChainModuleDifferential _ H R u = 0)
    (hw : pathFromChainAugmentationHom B b H R u =
      (loopChainAugmentation B b R).bimoduleDifferential w) :
    ∃ u' w', cubicalChainModuleDifferential _ H R u' = u ∧
      pathFromChainAugmentationHom B b H R u' +
        (loopChainAugmentation B b R).bimoduleDifferential w' = w :=
  have hd := (loopChainAugmentation B b R).bimoduleDifferential_eq_zero rfl
  exists_differential_eq_and_add_eq_of_augmentation
    (f := (pathFromChainAugmentationHom B b H R).restrictScalars R)
    (εN := (Bimodule.of (loopChainAugmentation B b R).toGradedAlgHom.toAlgHom).symm.toLinearMap)
    pathFromChainAugmentationHom_differential bimoduleOf_symm_pathFromChainAugmentationHom
    (by simp [hd]) (cubicalChainModuleDifferential_cubicalChainModulePoint (MoorePathFrom.refl B b))
    (cubicalChainModuleAugmentation_cubicalChainModulePoint _)
    exists_pathFromChainDifferential_eq_of_augmentation_eq_zero
    (fun _ hw ↦ ⟨0, by rw [hd, LinearMap.zero_apply, eq_comm]; simpa using hw⟩) hu hw

end Augmentation

section DerivedTensor

variable {B : Type uB} [TopologicalSpace B] {b : B} {H : Type*} {R : Type uR} [CommRing R]

namespace BrownModel

/-- **A Brown model resolves the ground ring.** For a Brown model `M`, the composite of its
comparison with the augmentation `TauCeti.pathFromChainAugmentationHom` of the based path chains is
a quasi-isomorphism from the free module `K_m` onto `R`, on which the loop chains act through their
augmentation: every relative cycle `(u, w)` is a relative boundary `(D u', ε(g(u')))`. Both maps
are quasi-isomorphisms, the second because the based path space is contractible. -/
theorem exists_differential_eq_and_augmentation_add_eq {P : Type*} {ind : P → ℤ}
    (M : BrownModel B b H R P ind) (u : P →₀ loopChainAlgebra B b R)
    (w : Bimodule (loopChainAugmentation B b R).toGradedAlgHom.toAlgHom)
    (hu : rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
      (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
      (d := cubicalChainDifferential (MooreLoopSpace B b) R) M.cocycle.m u = 0)
    (hw : Finsupp.linearCombination (loopChainAlgebra B b R)
        (pathFromChainAugmentationHom B b H R ∘ M.comparison) u =
      (loopChainAugmentation B b R).bimoduleDifferential w) :
    ∃ u' w', rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R) M.cocycle.m u' = u ∧
      Finsupp.linearCombination (loopChainAlgebra B b R)
          (pathFromChainAugmentationHom B b H R ∘ M.comparison) u' +
        (loopChainAugmentation B b R).bimoduleDifferential w' = w := by
  -- The images of the generators in `R` are the augmentations of their images in the path chains.
  have hlc := Finsupp.apply_linearCombination _ (pathFromChainAugmentationHom B b H R) M.comparison
  obtain ⟨u', w', hu', hw'⟩ := exists_differential_eq_and_comp_add_eq
    (g := (Finsupp.linearCombination (loopChainAlgebra B b R) M.comparison).restrictScalars R)
    (f := (pathFromChainAugmentationHom B b H R).restrictScalars R) M.linearCombination_differential
    pathFromChainAugmentationHom_differential M.exists_differential_eq_and_linearCombination_add_eq
    exists_differential_eq_and_pathFromChainAugmentationHom_add_eq u w hu ((hlc u).trans hw)
  exact ⟨u', w', hu', (congrArg (· + _) (hlc u')).symm.trans hw'⟩

/-- **A Brown model is homologous to the semi-free resolution of the ground ring.** For a Brown
model `M` with generators in the universe of the loop chains, the cocycle of `M` and the canonical
semi-free resolution (`TauCeti.semifreeResolution`) of `R`, on which the loop chains act through
their augmentation, are homologous. So the twisted complex `𝓕 ⊗ K_m` is homotopy equivalent to
`𝓕 ⊗ K`, for the free module `K` of that resolution, with coefficients in every DG right module
`𝓕` (`TauCeti.RowFiniteHomologous.homotopyEquiv`). -/
theorem nonempty_rowFiniteHomologous_semifreeResolution {P : Type (max uB uR)} {ind : P → ℤ}
    (M : BrownModel B b H R P ind) :
    Nonempty (RowFiniteHomologous (loopChain_isDGAlgebra B b R) M.cocycle
      (semifreeResolution (R := R) (A := loopChainAlgebra B b R)
        (cubicalChainGrading (MooreLoopSpace B b) R)
        (cubicalChainDifferential (MooreLoopSpace B b) R)
        (loopChainAugmentation B b R).bimoduleGrading
        (loopChainAugmentation B b R).bimoduleDifferential)) := by
  -- The left action of the loop chains on `{}_ε R` respects degrees; the instance has to be
  -- supplied, since the grading of the loop chains is stated with the direct-sum module structure.
  have := DGAlgHom.bimoduleGradedSMulLeft (loopChainAugmentation B b R)
  refine TauCeti.nonempty_rowFiniteHomologous_semifreeResolution
    (loopChainAugmentation B b R).isDGBimodule.toIsDGLeftModule M.wellFounded
    (ε := pathFromChainAugmentationHom B b H R ∘ M.comparison)
    (fun x ↦ pathFromChainAugmentationHom_mem (M.comparison_mem x)) (fun x ↦ ?_)
    M.exists_differential_eq_and_augmentation_add_eq
  rw [← Finsupp.apply_linearCombination, M.linearCombination_comparison_m,
    pathFromChainAugmentationHom_differential, Function.comp_apply]

variable {D₁ D₂ : Type*} [Category* D₁] [Category* D₂]
  (L₁ : DGRightModuleCat.{uR, max uB uR, uM} (loopChain_isDGAlgebra B b R) ⥤ D₁)
  [L₁.IsLocalization (DGRightModuleCat.quasiIsos (loopChain_isDGAlgebra B b R))]
  (L₂ : CochainComplex (ModuleCat.{max uB uR uM} R) ℤ ⥤ D₂)
  [L₂.IsLocalization (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))]

/-- **Brown models compute the derived tensor product with the ground ring.** For a Brown model
`M` of the chains on the based path space, with generators in the universe of the loop chains,
tensoring DG right modules with the free module `K_m` of its cocycle induces, on any localizations
at the quasi-isomorphisms, a functor isomorphic to the derived tensor product `- ⊗^L R` with the
ground ring, on which the loop chains act through their augmentation. So the twisted complex
`𝓕 ⊗ K_m` has cohomology `Tor^{C_*(Ω_b B; R)}(𝓕, R)`. -/
theorem nonempty_localizedFunctor_iso_derivedTensor {P : Type (max uB uR)} {ind : P → ℤ}
    (M : BrownModel B b H R P ind) :
    Nonempty ((M.cocycle.coefficientLocalizerMorphism (loopChain_isDGAlgebra B b R)
        M.wellFounded).localizedFunctor L₁ L₂ ≅
      (derivedTensorLocalizerMorphism (loopChain_isDGAlgebra B b R)
        (loopChainAugmentation B b R).bimoduleGrading
        (loopChainAugmentation B b R).bimoduleDifferential).localizedFunctor L₁ L₂) := by
  rw [derivedTensorLocalizerMorphism_def]
  exact M.nonempty_rowFiniteHomologous_semifreeResolution.map fun E ↦
    E.localizedFunctorIso L₁ L₂ M.wellFounded wellFounded_mem_support_semifreeResolution

end BrownModel

/-- **Brown's resolution of the circle computes the derived tensor product with the ground ring.**
For the complex unit circle, based at `1`, with its `1`-cell attached along the counterclockwise
loop, tensoring DG right modules `𝓕` over `C_*(Ω S¹; R)` with the free module of
`TauCeti.loopCellCocycle`, which gives the twisted complex `𝓕 e₀ ⊕ 𝓕 e₁` with
`D e₁ = ([γ] - [1]) e₀`, induces on any localizations at the quasi-isomorphisms a functor
isomorphic to the derived tensor product `- ⊗^L R` with the ground ring. -/
theorem nonempty_loopCellCocycle_localizedFunctor_iso_derivedTensor_loopChainAugmentation
    {R : Type} [CommRing R] {D₁ D₂ : Type*} [Category* D₁] [Category* D₂]
    (L₁ : DGRightModuleCat.{0, 0, uM} (loopChain_isDGAlgebra Circle 1 R) ⥤ D₁)
    [L₁.IsLocalization (DGRightModuleCat.quasiIsos (loopChain_isDGAlgebra Circle 1 R))]
    (L₂ : CochainComplex (ModuleCat.{uM} R) ℤ ⥤ D₂)
    [L₂.IsLocalization (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))] :
    Nonempty (((loopCellCocycle R Circle.expLoop.toMooreLoop).coefficientLocalizerMorphism
        (loopChain_isDGAlgebra Circle 1 R)
        (wellFounded_mem_support_loopCellCocycle _)).localizedFunctor L₁ L₂ ≅
      (derivedTensorLocalizerMorphism (loopChain_isDGAlgebra Circle 1 R)
        (loopChainAugmentation Circle 1 R).bimoduleGrading
        (loopChainAugmentation Circle 1 R).bimoduleDifferential).localizedFunctor L₁ L₂) := by
  -- The chains on the based paths may be taken over any monoid, since the localized functors do
  -- not involve them.
  have h := (loopCellBrownModel PUnit.{1} Circle.expLoop.toMooreLoop
    exists_loopCellCocycle_expLoop_differential_eq_of_loopCellAugmentation_eq_zero
    ).nonempty_localizedFunctor_iso_derivedTensor L₁ L₂
  simpa only [loopCellBrownModel_cocycle] using h

end DerivedTensor

end TauCeti
