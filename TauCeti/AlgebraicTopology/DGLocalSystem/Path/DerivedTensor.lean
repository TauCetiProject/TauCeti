/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.OfHom
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.DerivedTensor
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Circle
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.SemifreeModel

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
Moore paths from `b` by a map that is linear over the loop chains. This file shows that every such
model computes the derived tensor product with `R`
(`TauCeti.nonempty_localizedFunctor_iso_derivedTensor_loopChainAugmentation`): if `K_m` is
semi-free and its comparison with `C_*(P_b B; R)` is a quasi-isomorphism, then tensoring DG right
modules with `K_m` induces, on any localizations at the quasi-isomorphisms, a functor isomorphic to
`- ⊗^L R`. So the twisted complex `𝓕 ⊗ K_m` has cohomology `Tor^{C_*(Ω_b B; R)}(𝓕, R)`.

The reason is that the based path space is contractible: its augmentation
(`TauCeti.pathFromChainAugmentationHom`), read as a map of left modules to `{}_ε R`, is a
quasi-isomorphism (`TauCeti.exists_differential_eq_and_pathFromChainAugmentationHom_add_eq`), so
the composite of the comparison with it is a quasi-isomorphism from `K_m` onto `R`
(`TauCeti.exists_differential_eq_and_comp_add_eq`). A semi-free resolution of `R` computes the
derived tensor product with `R` (`TauCeti.nonempty_localizedFunctor_iso_derivedTensor`).

For the circle, Brown's resolution `TauCeti.loopCellCocycle` with its comparison
`TauCeti.loopCellPathComparison` is such a model
(`TauCeti.nonempty_loopCellCocycle_localizedFunctor_iso_derivedTensor_loopChainAugmentation`): the
two-generator twisted complex `𝓕 e₀ ⊕ 𝓕 e₁` with `D e₁ = ([γ] - [1]) e₀` computes
`𝓕 ⊗^L_{C_*(Ω S¹; R)} R`.

Over an arbitrary CW complex, Brown's semi-free model of `C_*(P_b B; R)`
(`TauCeti.exists_semifreeModel_pathFromChain`), with one generator in degree `-n` for each `n`-cell,
attached along a cycle on the cells of lower dimension and sent to the cube of paths over the cell,
is such a model too
(`TauCeti.exists_semifreeModel_localizedFunctor_iso_derivedTensor_loopChainAugmentation`). So for
every DG right module `𝓕` over `C_*(Ω_b B; R)`, the twisted complex of `𝓕` over the cells of `B`
computes `𝓕 ⊗^L_{C_*(Ω_b B; R)} R`, and its cohomology is `Tor^{C_*(Ω_b B; R)}(𝓕, R)`.

## Implementation notes

The derived tensor product is built from the canonical semi-free resolution, whose generators lie
in the universe of the loop chains, and a model is compared with it through generators in that
same universe. The generators `Unit ⊕ Unit` of `TauCeti.loopCellCocycle` lie in `Type`, so the
circle is treated with coefficients `R : Type`, as in
`TauCeti.exists_loopCellCocycle_expLoop_differential_eq_and_loopCellPathComparison_add_eq`. For the
same reason a CW complex `B` and the coefficients `R` lie in `Type`, as in
`TauCeti.exists_semifreeModel_pathFromChain`, so that the cells of `B` index generators in `Type`.

## Main definitions

* `TauCeti.pathFromChainAugmentationHom`: the augmentation `C_*(P_b B; R) → R`, linear over the
  loop chains acting on `R` through their augmentation.

## Main results

* `TauCeti.exists_differential_eq_and_pathFromChainAugmentationHom_add_eq`: the augmentation of the
  chains on the based path space is a quasi-isomorphism onto `R`.
* `TauCeti.nonempty_localizedFunctor_iso_derivedTensor_loopChainAugmentation`: a semi-free model
  quasi-isomorphic to the chains on the based path space computes the derived tensor product with
  the ground ring.
* `TauCeti.exists_rowFiniteTwistedDifferential_eq_of_augmentation_eq_zero`: a cycle of such a
  model whose image in the based path chains has augmentation zero is a boundary.
* `TauCeti.nonempty_loopCellCocycle_localizedFunctor_iso_derivedTensor_loopChainAugmentation`:
  Brown's resolution of the circle computes the derived tensor product with the ground ring.
* `TauCeti.exists_semifreeModel_localizedFunctor_iso_derivedTensor_loopChainAugmentation`:
  Brown's model of an arbitrary CW complex computes the derived tensor product with the ground
  ring.

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
  {D₁ D₂ : Type*} [Category* D₁] [Category* D₂]
  (L₁ : DGRightModuleCat.{uR, max uB uR, uM} (loopChain_isDGAlgebra B b R) ⥤ D₁)
  [L₁.IsLocalization (DGRightModuleCat.quasiIsos (loopChain_isDGAlgebra B b R))]
  (L₂ : CochainComplex (ModuleCat.{max uB uR uM} R) ℤ ⥤ D₂)
  [L₂.IsLocalization (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))]

/-- **Brown's models compute the derived tensor product with the ground ring.** Let `m` be a
semi-free twisting cocycle over the loop chains `C_*(Ω_b B; R)`, with a comparison `g` of its free
module `K_m` with the chains `C_*(P_b B; R)` on the based path space: `g` sends each generator `x`
to a chain of degree `-ind x` whose boundary is the image of the row of `x`, and every relative
cycle of `g` is a relative boundary, so that `g` is a quasi-isomorphism. Then tensoring DG right
modules with `K_m` induces, on any localizations at the quasi-isomorphisms, a functor isomorphic to
the derived tensor product `- ⊗^L R` with the ground ring, on which the loop chains act through
their augmentation. -/
theorem nonempty_localizedFunctor_iso_derivedTensor_loopChainAugmentation
    {P : Type (max uB uR)} {ind : P → ℤ}
    {m : RowFiniteTwistingCocycle (R := R) (A := loopChainAlgebra B b R)
      (cubicalChainGrading (MooreLoopSpace B b) R) (cubicalChainDifferential (MooreLoopSpace B b) R)
      P ind}
    (hm : WellFounded fun y x ↦ y ∈ (m.m x).support)
    {g : P → cubicalChainModule (MoorePathFrom B b) H R}
    (hg : ∀ x, g x ∈ cubicalChainModuleGrading (MoorePathFrom B b) H R (-ind x))
    (hgd : ∀ x, Finsupp.linearCombination (loopChainAlgebra B b R) g (m.m x) =
      cubicalChainModuleDifferential (MoorePathFrom B b) H R (g x))
    (hgrel : ∀ u w, rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R) m.m u = 0 →
      Finsupp.linearCombination (loopChainAlgebra B b R) g u =
        cubicalChainModuleDifferential (MoorePathFrom B b) H R w →
      ∃ u' w', rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
          (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
          (d := cubicalChainDifferential (MooreLoopSpace B b) R) m.m u' = u ∧
        Finsupp.linearCombination (loopChainAlgebra B b R) g u' +
          cubicalChainModuleDifferential (MoorePathFrom B b) H R w' = w) :
    Nonempty ((m.coefficientLocalizerMorphism (loopChain_isDGAlgebra B b R) hm).localizedFunctor
        L₁ L₂ ≅
      (derivedTensorLocalizerMorphism (loopChain_isDGAlgebra B b R)
        (loopChainAugmentation B b R).bimoduleGrading
        (loopChainAugmentation B b R).bimoduleDifferential).localizedFunctor L₁ L₂) := by
  -- The left action of the loop chains on `{}_ε R` respects degrees; the instance has to be
  -- supplied, since the grading of the loop chains is stated with the direct-sum module structure.
  have := DGAlgHom.bimoduleGradedSMulLeft (loopChainAugmentation B b R)
  have hcomm := linearCombination_rowFiniteTwistedDifferential
    (pathFromChain_isDGLeftModule B b H R) m.m hgd
  -- The images of the generators in `R` are the augmentations of their images in the path chains.
  have hlc (f : P →₀ loopChainAlgebra B b R) :
      Finsupp.linearCombination _ (fun x ↦ pathFromChainAugmentationHom B b H R (g x)) f =
        pathFromChainAugmentationHom B b H R (Finsupp.linearCombination _ g f) :=
    (Finsupp.apply_linearCombination _ _ g f).symm
  refine nonempty_localizedFunctor_iso_derivedTensor L₁ L₂
    (loopChainAugmentation B b R).isDGBimodule.toIsDGLeftModule hm
    (ε := fun x ↦ pathFromChainAugmentationHom B b H R (g x))
    (fun x ↦ pathFromChainAugmentationHom_mem (hg x)) (fun x ↦ ?_) fun u w hu hw ↦ ?_
  · rw [hlc, hgd, pathFromChainAugmentationHom_differential]
  · -- The composite of the comparison with the augmentation of the path chains.
    obtain ⟨u', w', hu', hw'⟩ := exists_differential_eq_and_comp_add_eq
      (g := (Finsupp.linearCombination (loopChainAlgebra B b R) g).restrictScalars R)
      (f := (pathFromChainAugmentationHom B b H R).restrictScalars R) hcomm
      pathFromChainAugmentationHom_differential hgrel
      exists_differential_eq_and_pathFromChainAugmentationHom_add_eq u w hu
      ((hlc u).symm.trans hw)
    exact ⟨u', w', hu', (congrArg (· + _) (hlc u')).trans hw'⟩

/-- **A cycle of a Brown model whose image has augmentation zero is a boundary.** Let `m` be a
twisting cocycle over the loop chains `C_*(Ω_b B; R)`, with a comparison `g` of its free module
`K_m` with the chains `C_*(P_b B; R)` on the based path space that commutes with the differentials
and is a quasi-isomorphism: every relative cycle of `g` is a relative boundary. Then the composite
of `g` with the augmentation `C_*(P_b B; R) → R` kills no nonzero class: every cycle `u` of `K_m`
whose image under `g` has augmentation zero is a boundary. -/
theorem exists_rowFiniteTwistedDifferential_eq_of_augmentation_eq_zero
    {P : Type*} {ind : P → ℤ}
    {m : RowFiniteTwistingCocycle (R := R) (A := loopChainAlgebra B b R)
      (cubicalChainGrading (MooreLoopSpace B b) R) (cubicalChainDifferential (MooreLoopSpace B b) R)
      P ind}
    {g : P → cubicalChainModule (MoorePathFrom B b) H R}
    (hgd : ∀ x, Finsupp.linearCombination (loopChainAlgebra B b R) g (m.m x) =
      cubicalChainModuleDifferential (MoorePathFrom B b) H R (g x))
    (hgrel : ∀ u w, rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R) m.m u = 0 →
      Finsupp.linearCombination (loopChainAlgebra B b R) g u =
        cubicalChainModuleDifferential (MoorePathFrom B b) H R w →
      ∃ u' w', rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
          (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
          (d := cubicalChainDifferential (MooreLoopSpace B b) R) m.m u' = u ∧
        Finsupp.linearCombination (loopChainAlgebra B b R) g u' +
          cubicalChainModuleDifferential (MoorePathFrom B b) H R w' = w)
    {u : P →₀ loopChainAlgebra B b R}
    (hu : rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
      (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
      (d := cubicalChainDifferential (MooreLoopSpace B b) R) m.m u = 0)
    (hε : cubicalChainModuleAugmentation (MoorePathFrom B b) H R
      (Finsupp.linearCombination (loopChainAlgebra B b R) g u) = 0) :
    ∃ u', rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
      (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
      (d := cubicalChainDifferential (MooreLoopSpace B b) R) m.m u' = u := by
  -- The comparison with the path chains and their augmentation are quasi-isomorphisms, so their
  -- composite `K_m → R` is one.
  obtain ⟨u', -, hu', -⟩ := exists_differential_eq_and_comp_add_eq
    (g := (Finsupp.linearCombination (loopChainAlgebra B b R) g).restrictScalars R)
    (f := (pathFromChainAugmentationHom B b H R).restrictScalars R)
    (linearCombination_rowFiniteTwistedDifferential (pathFromChain_isDGLeftModule B b H R) m.m hgd)
    pathFromChainAugmentationHom_differential hgrel
    exists_differential_eq_and_pathFromChainAugmentationHom_add_eq u 0 hu
    ((Bimodule.of _).symm.injective (by simpa using hε))
  exact ⟨u', hu'⟩

/-- **Brown's resolution of the circle computes the derived tensor product with the ground ring.**
For the complex unit circle, based at `1`, with its `1`-cell attached along the counterclockwise
loop, tensoring DG right modules `𝓕` over `C_*(Ω S¹; R)` with the free module of
`TauCeti.loopCellCocycle`, which gives the twisted complex `𝓕 e₀ ⊕ 𝓕 e₁` with
`D e₁ = ([γ] - [1]) e₀`, induces on any localizations at the quasi-isomorphisms a functor
isomorphic to the derived tensor product `- ⊗^L R` with the ground ring. -/
theorem nonempty_loopCellCocycle_localizedFunctor_iso_derivedTensor_loopChainAugmentation
    {H : Type*} {R : Type} [CommRing R] {D₁ D₂ : Type*} [Category* D₁] [Category* D₂]
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
  set γ := Circle.expLoop.toMooreLoop
  set g : Unit ⊕ Unit → cubicalChainModule (MoorePathFrom Circle 1) H R :=
    Sum.elim (fun _ ↦ cubicalChainModulePoint _ H R (MoorePathFrom.refl Circle 1))
      (fun _ ↦ loopCellPathChain H R γ)
  -- The linear combination of the images of the generators is Brown's comparison map.
  have hg : Finsupp.linearCombination (loopChainAlgebra Circle 1 R) g =
      loopCellPathComparison H R γ := by
    refine Finsupp.lhom_ext fun x a ↦ ?_
    rcases x with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp [g]
  have hgmem : ∀ x, g x ∈ cubicalChainModuleGrading (MoorePathFrom Circle 1) H R
      (-Sum.elim (fun _ ↦ (0 : ℤ)) (fun _ ↦ 1) x) := by
    rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
    · simpa [g] using cubicalChainModulePoint_mem (G := H) (R := R) (MoorePathFrom.refl Circle 1)
    · simpa [g] using loopCellPathChain_mem (H := H) (R := R) γ
  have hgd : ∀ f, Finsupp.linearCombination (loopChainAlgebra Circle 1 R) g
      (rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra Circle 1 R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace Circle 1) R)
        (d := cubicalChainDifferential (MooreLoopSpace Circle 1) R) (loopCellCocycle R γ).m f) =
      cubicalChainModuleDifferential _ H R (Finsupp.linearCombination _ g f) := by
    intro f
    rw [hg]
    exact loopCellPathComparison_differential γ f
  refine nonempty_localizedFunctor_iso_derivedTensor_loopChainAugmentation L₁ L₂ _ hgmem
    ((forall_linearCombination_rowFiniteTwistedDifferential_iff
      (pathFromChain_isDGLeftModule Circle 1 H R) _ g).1 hgd) fun u w hu hw ↦ ?_
  rw [hg] at hw ⊢
  exact exists_loopCellCocycle_expLoop_differential_eq_and_loopCellPathComparison_add_eq hu hw

end DerivedTensor

section CWComplex

open Topology Topology.RelCWComplex

variable {B : Type} [TopologicalSpace B] [T2Space B] {b : B} {C : Set B} [CWComplex C]
  (H : Type*) (R : Type) [CommRing R]

/-- **Brown's model of a CW complex computes the derived tensor product with the ground ring.**
Let `B` be a CW complex with a point `b`, and choose a Moore path `τ n j` from `b` to the centre of
every `n`-cell `j`. There is a row-finite twisting cocycle `m` over the loop chains
`C_*(Ω_b B; R)` on the cells of `B`, the generator of an `n`-cell in degree `-n`, whose free module
`K_m` maps to the chains `C_*(P_b B; R)` on the based path space by a map `g` such that:

* `g` sends the generator of an `n`-cell into degree `-n` of the chains over the `n`-skeleton,
  to the chain of the cell `TauCeti.cellPathChain H R τ` modulo the chains over the lower skeleta,
  and commutes with the differentials;
* the row of an `n`-cell only involves cells of dimension `< n`, so `K_m` is semi-free;
* `g` is a quasi-isomorphism relative to the skeleta: for every `k`, a cycle of `K_m` on the cells
  of dimension `< k` whose image bounds a chain over the `(k - 1)`-skeleton is, together with that
  chain, the image of a pair of the same kind; and `g` is a quasi-isomorphism onto
  `C_*(P_b B; R)`, in the same form without the restrictions on dimension;
* the composite of `g` with the augmentation `C_*(P_b B; R) → R` kills no nonzero class: every
  cycle of `K_m` whose image has augmentation zero is a boundary;
* for every DG right module `𝓕` over `C_*(Ω_b B; R)`, the twisted complex `𝓕 ⊗ K_m` computes the
  derived tensor product `𝓕 ⊗^L R` with the ground ring, on which the loop chains act through
  their augmentation: on any localizations at the quasi-isomorphisms, the functor induced by
  `𝓕 ↦ 𝓕 ⊗ K_m` is isomorphic to `- ⊗^L R`.

So the cohomology of `𝓕 ⊗ K_m` is `Tor^{C_*(Ω_b B; R)}(𝓕, R)`. -/
theorem exists_semifreeModel_localizedFunctor_iso_derivedTensor_loopChainAugmentation
    (hC : ∀ x, x ∈ C) (τ : ∀ (n : ℕ) (j : cell C n), MoorePathBetween B b (map n j 0)) :
    ∃ (m : RowFiniteTwistingCocycle (R := R) (A := loopChainAlgebra B b R)
        (cubicalChainGrading (MooreLoopSpace B b) R)
        (cubicalChainDifferential (MooreLoopSpace B b) R) (Σ n, cell C n) fun x ↦ (x.1 : ℤ))
      (g : (Σ n, cell C n) → cubicalChainModule (MoorePathFrom B b) H R)
      (hm : WellFounded fun y x ↦ y ∈ (m.m x).support),
      (∀ x, g x ∈ cubicalChainModuleGrading (MoorePathFrom B b) H R (-(x.1 : ℤ))) ∧
      (∀ x, g x ∈ pathFromChainSkeleton b C H R x.1) ∧
      (∀ x, g x - cellPathChain H R τ x.1 x.2 ∈ pathFromChainSkeleton b C H R ((x.1 : ℤ) - 1)) ∧
      (∀ x, Finsupp.linearCombination (loopChainAlgebra B b R) g (m.m x) =
        cubicalChainModuleDifferential (MoorePathFrom B b) H R (g x)) ∧
      (∀ x, m.m x ∈ Finsupp.supported (loopChainAlgebra B b R) (loopChainAlgebra B b R)
        {y | y.1 < x.1}) ∧
      (∀ (k : ℕ) (u : (Σ n, cell C n) →₀ loopChainAlgebra B b R)
          (w : cubicalChainModule (MoorePathFrom B b) H R),
        u ∈ Finsupp.supported (loopChainAlgebra B b R) (loopChainAlgebra B b R) {y | y.1 < k} →
        rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
          (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
          (d := cubicalChainDifferential (MooreLoopSpace B b) R) m.m u = 0 →
        Finsupp.linearCombination (loopChainAlgebra B b R) g u =
          cubicalChainModuleDifferential (MoorePathFrom B b) H R w →
        w ∈ pathFromChainSkeleton b C H R ((k : ℤ) - 1) →
        ∃ (u' : (Σ n, cell C n) →₀ loopChainAlgebra B b R)
          (w' : cubicalChainModule (MoorePathFrom B b) H R),
          u' ∈ Finsupp.supported (loopChainAlgebra B b R) (loopChainAlgebra B b R) {y | y.1 < k} ∧
            w' ∈ pathFromChainSkeleton b C H R ((k : ℤ) - 1) ∧
            rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
              (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
              (d := cubicalChainDifferential (MooreLoopSpace B b) R) m.m u' = u ∧
            Finsupp.linearCombination (loopChainAlgebra B b R) g u' +
              cubicalChainModuleDifferential (MoorePathFrom B b) H R w' = w) ∧
      (∀ (u : (Σ n, cell C n) →₀ loopChainAlgebra B b R)
        (w : cubicalChainModule (MoorePathFrom B b) H R),
        rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
          (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
          (d := cubicalChainDifferential (MooreLoopSpace B b) R) m.m u = 0 →
        Finsupp.linearCombination (loopChainAlgebra B b R) g u =
          cubicalChainModuleDifferential (MoorePathFrom B b) H R w →
        ∃ (u' : (Σ n, cell C n) →₀ loopChainAlgebra B b R)
          (w' : cubicalChainModule (MoorePathFrom B b) H R),
          rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
            (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
            (d := cubicalChainDifferential (MooreLoopSpace B b) R) m.m u' = u ∧
          Finsupp.linearCombination (loopChainAlgebra B b R) g u' +
            cubicalChainModuleDifferential (MoorePathFrom B b) H R w' = w) ∧
      (∀ u, rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
          (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
          (d := cubicalChainDifferential (MooreLoopSpace B b) R) m.m u = 0 →
        cubicalChainModuleAugmentation (MoorePathFrom B b) H R
          (Finsupp.linearCombination (loopChainAlgebra B b R) g u) = 0 →
        ∃ u', rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
          (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
          (d := cubicalChainDifferential (MooreLoopSpace B b) R) m.m u' = u) ∧
      ∀ {D₁ D₂ : Type*} [Category* D₁] [Category* D₂]
        (L₁ : DGRightModuleCat.{0, 0, uM} (loopChain_isDGAlgebra B b R) ⥤ D₁)
        [L₁.IsLocalization (DGRightModuleCat.quasiIsos (loopChain_isDGAlgebra B b R))]
        (L₂ : CochainComplex (ModuleCat.{uM} R) ℤ ⥤ D₂)
        [L₂.IsLocalization (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))],
        Nonempty ((m.coefficientLocalizerMorphism (loopChain_isDGAlgebra B b R) hm).localizedFunctor
            L₁ L₂ ≅
          (derivedTensorLocalizerMorphism (loopChain_isDGAlgebra B b R)
            (loopChainAugmentation B b R).bimoduleGrading
            (loopChainAugmentation B b R).bimoduleDifferential).localizedFunctor L₁ L₂) := by
  obtain ⟨m, g, hgdeg, hgF, hgc, hgd, hms, hwf, hK, hgrel⟩ :=
    exists_semifreeModel_pathFromChain (H := H) (R := R) τ hC
  exact ⟨m, g, hwf, hgdeg, hgF, hgc, hgd, hms, hK, hgrel,
    fun _ hu hε ↦ exists_rowFiniteTwistedDifferential_eq_of_augmentation_eq_zero hgd hgrel hu hε,
    fun L₁ _ L₂ _ ↦
      nonempty_localizedFunctor_iso_derivedTensor_loopChainAugmentation L₁ L₂ hwf hgdeg hgd hgrel⟩

end CWComplex

end TauCeti
