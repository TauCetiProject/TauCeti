/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.DerivedTensor
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.SemifreeModel

/-!
# Brown's twisting cocycle of a CW complex

Let `B` be a CW complex with a point `b`, and choose a Moore path `τ n j` from `b` to the centre of
every `n`-cell `j`. Brown's semi-free model of the chains `C_*(P_b B; R)` on the based Moore path
space, over the chains `C_*(Ω_b B; R)` on the Moore loops, exists by
`TauCeti.exists_semifreeModel_pathFromChain`. This file names it: the **Brown cocycle**
`TauCeti.brownCocycle H R τ hC`, a row-finite twisting cocycle over `C_*(Ω_b B; R)` on the cells
of `B`, the cell `⟨n, j⟩` having index `n`, together with its comparison
`TauCeti.brownComparison H R τ hC`, the images in `C_*(P_b B; R)` of its free generators. Their
characteristic properties are the lemmas below: the comparison sends the generator of an `n`-cell
to a chain over the `n`-skeleton agreeing with the chain of the cell
(`TauCeti.cellPathChain`) modulo the `(n - 1)`-skeleton, it commutes with the differentials, the
row of an `n`-cell only involves cells of lower dimension, and the comparison is a
quasi-isomorphism, over each skeleton and globally.

Two consequences are proved.

* **Brown's cocycle computes the derived tensor product with the ground ring.** For every DG right
  module `𝓕` over `C_*(Ω_b B; R)`, the twisted complex `𝓕 ⊗ K_m` of the Brown cocycle represents
  `𝓕 ⊗^L R`, the loop chains acting on `R` through their augmentation: tensoring with the free
  module of the Brown cocycle induces, on any localizations at the quasi-isomorphisms, a functor
  isomorphic to the derived tensor product
  (`TauCeti.nonempty_brownCocycle_localizedFunctor_iso_derivedTensor`). So the cohomology of
  `𝓕 ⊗ K_m` is `Tor^{C_*(Ω_b B; R)}(𝓕, R)`.
* **Brown's cocycle does not depend on the choices.** The Brown cocycle is homologous to every
  semi-free model of `C_*(P_b B; R)` quasi-isomorphic to it, compatibly with the comparisons
  (`TauCeti.exists_rowFiniteHomologous_brownCocycle`). In particular the Brown cocycles of two CW
  structures on `B`, built with any two choices of paths to the centres of the cells, are
  homologous (`TauCeti.exists_rowFiniteHomologous_brownCocycle_brownCocycle`), so their twisted
  complexes with coefficients in any DG right module are homotopy equivalent
  (`TauCeti.RowFiniteHomologous.homotopyEquiv`), through specified continuation maps.

## Main definitions

* `TauCeti.brownCocycle`: Brown's twisting cocycle of a CW complex.
* `TauCeti.brownComparison`: its comparison with the chains on the based path space.

## Main results

* `TauCeti.exists_rowFiniteTwistedDifferential_brownCocycle_eq`: the comparison is a
  quasi-isomorphism.
* `TauCeti.nonempty_brownCocycle_localizedFunctor_iso_derivedTensor`: the Brown cocycle computes
  the derived tensor product with the ground ring.
* `TauCeti.exists_rowFiniteHomologous_brownCocycle`,
  `TauCeti.exists_rowFiniteHomologous_brownCocycle_brownCocycle`: the Brown cocycle is unique up
  to homology, independently of the paths and of the CW structure.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
-/

public section

noncomputable section

open CategoryTheory Set Topology Topology.RelCWComplex Finsupp

universe uM

namespace TauCeti

variable {B : Type} [TopologicalSpace B] [T2Space B] {b : B} {C : Set B} [CWComplex C]
  {H : Type*} {R : Type} [CommRing R]
  (τ : ∀ (n : ℕ) (j : cell C n), MoorePathBetween B b (map n j 0)) (hC : ∀ x, x ∈ C)

variable (H R) in
/-- **Brown's twisting cocycle of a CW complex** `B`, for a choice of Moore paths `τ n j` from `b`
to the centre of every cell `j` of every dimension `n`: a row-finite twisting cocycle over the loop
chains `C_*(Ω_b B; R)` on the cells of `B`, the cell `⟨n, j⟩` having index `n`, whose free module
`K_m` is Brown's semi-free model of the chains `C_*(P_b B; R)` on the based path space through the
comparison `TauCeti.brownComparison` (`TauCeti.exists_semifreeModel_pathFromChain`). -/
def brownCocycle :
    RowFiniteTwistingCocycle (R := R) (A := loopChainAlgebra B b R)
      (cubicalChainGrading (MooreLoopSpace B b) R)
      (cubicalChainDifferential (MooreLoopSpace B b) R) (Σ n, cell C n) fun x ↦ (x.1 : ℤ) :=
  (exists_semifreeModel_pathFromChain (H := H) (R := R) τ hC).choose

variable (H R) in
/-- **The comparison of Brown's cocycle with the chains on the based path space**: the image in
`C_*(P_b B; R)` of the free generator of each cell, which extends linearly over the loop chains
to the quasi-isomorphism `K_m → C_*(P_b B; R)` from the free module of `TauCeti.brownCocycle`. -/
def brownComparison : (Σ n, cell C n) → cubicalChainModule (MoorePathFrom B b) H R :=
  (exists_semifreeModel_pathFromChain (H := H) (R := R) τ hC).choose_spec.choose

/-- The comparison sends the generator of an `n`-cell to a chain of dimension `n`. -/
theorem brownComparison_mem_cubicalChainModuleGrading (x : Σ n, cell C n) :
    brownComparison H R τ hC x ∈
      cubicalChainModuleGrading (MoorePathFrom B b) H R (-(x.1 : ℤ)) :=
  (exists_semifreeModel_pathFromChain (H := H) (R := R) τ hC).choose_spec.choose_spec.1 x

/-- The comparison sends the generator of an `n`-cell to a chain over the `n`-skeleton. -/
theorem brownComparison_mem_pathFromChainSkeleton (x : Σ n, cell C n) :
    brownComparison H R τ hC x ∈ pathFromChainSkeleton b C H R x.1 :=
  (exists_semifreeModel_pathFromChain (H := H) (R := R) τ hC).choose_spec.choose_spec.2.1 x

/-- The comparison sends the generator of an `n`-cell to the chain of the cell
(`TauCeti.cellPathChain`) modulo the chains over the `(n - 1)`-skeleton. -/
theorem brownComparison_sub_cellPathChain_mem_pathFromChainSkeleton (x : Σ n, cell C n) :
    brownComparison H R τ hC x - cellPathChain H R τ x.1 x.2 ∈
      pathFromChainSkeleton b C H R ((x.1 : ℤ) - 1) :=
  (exists_semifreeModel_pathFromChain (H := H) (R := R) τ hC).choose_spec.choose_spec.2.2.1 x

/-- The comparison commutes with the differentials: the row of a generator goes to the boundary
of its image. -/
theorem linearCombination_brownComparison_brownCocycle_m (x : Σ n, cell C n) :
    linearCombination (loopChainAlgebra B b R) (brownComparison H R τ hC)
        ((brownCocycle H R τ hC).m x) =
      cubicalChainModuleDifferential (MoorePathFrom B b) H R (brownComparison H R τ hC x) :=
  (exists_semifreeModel_pathFromChain (H := H) (R := R) τ hC).choose_spec.choose_spec.2.2.2.1 x

/-- The row of an `n`-cell only involves cells of dimension `< n`. -/
theorem brownCocycle_m_mem_supported (x : Σ n, cell C n) :
    (brownCocycle H R τ hC).m x ∈
      supported (loopChainAlgebra B b R) (loopChainAlgebra B b R) {y | y.1 < x.1} :=
  (exists_semifreeModel_pathFromChain (H := H) (R := R) τ hC).choose_spec.choose_spec.2.2.2.2.1 x

/-- **Brown's cocycle is semi-free**: its row relation is well-founded. -/
theorem wellFounded_mem_support_brownCocycle :
    WellFounded fun y x ↦ y ∈ ((brownCocycle H R τ hC).m x).support :=
  (exists_semifreeModel_pathFromChain (H := H) (R := R) τ hC).choose_spec.choose_spec.2.2.2.2.2.1

/-- **The comparison is a quasi-isomorphism over each skeleton.** For every `k`, the restriction
of the comparison to the cells of dimension `< k` is a quasi-isomorphism onto the chains over the
`(k - 1)`-skeleton: relative cycles `(u, w)`, with `u` on these cells and `w` over this skeleton,
are relative boundaries `(D u', g(u') + d w')` with `u'` on the same cells and `w'` over the same
skeleton. -/
theorem exists_rowFiniteTwistedDifferential_brownCocycle_eq_of_mem_supported (k : ℕ)
    (u : (Σ n, cell C n) →₀ loopChainAlgebra B b R)
    (w : cubicalChainModule (MoorePathFrom B b) H R)
    (hu : u ∈ supported (loopChainAlgebra B b R) (loopChainAlgebra B b R) {y | y.1 < k})
    (hDu : rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
      (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
      (d := cubicalChainDifferential (MooreLoopSpace B b) R) (brownCocycle H R τ hC).m u = 0)
    (huw : linearCombination (loopChainAlgebra B b R) (brownComparison H R τ hC) u =
      cubicalChainModuleDifferential (MoorePathFrom B b) H R w)
    (hw : w ∈ pathFromChainSkeleton b C H R ((k : ℤ) - 1)) :
    ∃ (u' : (Σ n, cell C n) →₀ loopChainAlgebra B b R)
      (w' : cubicalChainModule (MoorePathFrom B b) H R),
      u' ∈ supported (loopChainAlgebra B b R) (loopChainAlgebra B b R) {y | y.1 < k} ∧
        w' ∈ pathFromChainSkeleton b C H R ((k : ℤ) - 1) ∧
        rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
          (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
          (d := cubicalChainDifferential (MooreLoopSpace B b) R) (brownCocycle H R τ hC).m u' =
            u ∧
        linearCombination (loopChainAlgebra B b R) (brownComparison H R τ hC) u' +
          cubicalChainModuleDifferential (MoorePathFrom B b) H R w' = w :=
  (exists_semifreeModel_pathFromChain (H := H) (R := R) τ hC).choose_spec.choose_spec.2.2.2.2.2.2.1
    k u w hu hDu huw hw

/-- **The comparison is a quasi-isomorphism.** Every relative cycle `(u, w)` of the comparison
`g : K_m → C_*(P_b B; R)`, with `D u = 0` and `g(u) = d w`, is a relative boundary
`(D u', g(u') + d w')`. -/
theorem exists_rowFiniteTwistedDifferential_brownCocycle_eq
    (u : (Σ n, cell C n) →₀ loopChainAlgebra B b R)
    (w : cubicalChainModule (MoorePathFrom B b) H R)
    (hDu : rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
      (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
      (d := cubicalChainDifferential (MooreLoopSpace B b) R) (brownCocycle H R τ hC).m u = 0)
    (huw : linearCombination (loopChainAlgebra B b R) (brownComparison H R τ hC) u =
      cubicalChainModuleDifferential (MoorePathFrom B b) H R w) :
    ∃ (u' : (Σ n, cell C n) →₀ loopChainAlgebra B b R)
      (w' : cubicalChainModule (MoorePathFrom B b) H R),
      rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
          (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
          (d := cubicalChainDifferential (MooreLoopSpace B b) R) (brownCocycle H R τ hC).m u' =
          u ∧
        linearCombination (loopChainAlgebra B b R) (brownComparison H R τ hC) u' +
          cubicalChainModuleDifferential (MoorePathFrom B b) H R w' = w :=
  (exists_semifreeModel_pathFromChain (H := H) (R := R) τ hC).choose_spec.choose_spec.2.2.2.2.2.2.2
    u w hDu huw

/-! ### The derived tensor product with the ground ring -/

section DerivedTensor

variable {D₁ D₂ : Type*} [Category* D₁] [Category* D₂]
  (L₁ : DGRightModuleCat.{0, 0, uM} (loopChain_isDGAlgebra B b R) ⥤ D₁)
  [L₁.IsLocalization (DGRightModuleCat.quasiIsos (loopChain_isDGAlgebra B b R))]
  (L₂ : CochainComplex (ModuleCat.{uM} R) ℤ ⥤ D₂)
  [L₂.IsLocalization (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))]

/-- **Brown's cocycle computes the derived tensor product with the ground ring.** For a CW complex
`B`, tensoring DG right modules `𝓕` over `C_*(Ω_b B; R)` with the free module `K_m` of Brown's
cocycle induces, on any localizations at the quasi-isomorphisms, a functor isomorphic to the
derived tensor product `- ⊗^L R` with the ground ring, on which the loop chains act through their
augmentation. So the twisted complex `𝓕 ⊗ K_m` has cohomology `Tor^{C_*(Ω_b B; R)}(𝓕, R)`. -/
theorem nonempty_brownCocycle_localizedFunctor_iso_derivedTensor :
    Nonempty (((brownCocycle H R τ hC).coefficientLocalizerMorphism
        (loopChain_isDGAlgebra B b R) (wellFounded_mem_support_brownCocycle τ hC)).localizedFunctor
        L₁ L₂ ≅
      (derivedTensorLocalizerMorphism (loopChain_isDGAlgebra B b R)
        (loopChainAugmentation B b R).bimoduleGrading
        (loopChainAugmentation B b R).bimoduleDifferential).localizedFunctor L₁ L₂) :=
  nonempty_localizedFunctor_iso_derivedTensor_loopChainAugmentation L₁ L₂
    (wellFounded_mem_support_brownCocycle τ hC)
    (brownComparison_mem_cubicalChainModuleGrading τ hC)
    (linearCombination_brownComparison_brownCocycle_m τ hC)
    (exists_rowFiniteTwistedDifferential_brownCocycle_eq τ hC)

end DerivedTensor

/-! ### Independence of the choices -/

/-- **Brown's cocycle is unique up to homology.** Let `m` be any semi-free row-finite twisting
cocycle over `C_*(Ω_b B; R)`, on generators `Q` with indices `ind`, and `g` the images of its
generators in `C_*(P_b B; R)`, of degrees `-ind`, such that `g : K_m → C_*(P_b B; R)` commutes with
the differentials and is a quasi-isomorphism. Then Brown's cocycle is homologous to `m`, so their
twisted complexes with coefficients in any DG right module are homotopy equivalent
(`TauCeti.RowFiniteHomologous.homotopyEquiv`), and the equivalence is compatible with the
comparisons: a homotopy `k`, of degree `-1` and given on the cells, joins `g ∘ ν` to the comparison
of Brown's cocycle, where `ν` is the continuation cocycle from Brown's cocycle to `m`. -/
theorem exists_rowFiniteHomologous_brownCocycle {Q : Type} {ind : Q → ℤ}
    {m : RowFiniteTwistingCocycle (R := R) (A := loopChainAlgebra B b R)
      (cubicalChainGrading (MooreLoopSpace B b) R) (cubicalChainDifferential (MooreLoopSpace B b) R)
      Q ind}
    (hm : WellFounded fun y x ↦ y ∈ (m.m x).support)
    {g : Q → cubicalChainModule (MoorePathFrom B b) H R}
    (hg : ∀ y, g y ∈ cubicalChainModuleGrading (MoorePathFrom B b) H R (-ind y))
    (hgd : ∀ y, linearCombination (loopChainAlgebra B b R) g (m.m y) =
      cubicalChainModuleDifferential (MoorePathFrom B b) H R (g y))
    (hgrel : ∀ u w, rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R) m.m u = 0 →
      linearCombination (loopChainAlgebra B b R) g u =
        cubicalChainModuleDifferential (MoorePathFrom B b) H R w →
      ∃ u' w', rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
          (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
          (d := cubicalChainDifferential (MooreLoopSpace B b) R) m.m u' = u ∧
        linearCombination (loopChainAlgebra B b R) g u' +
          cubicalChainModuleDifferential (MoorePathFrom B b) H R w' = w) :
    ∃ (E : RowFiniteHomologous (loopChain_isDGAlgebra B b R) (brownCocycle H R τ hC) m)
      (k : (Σ n, cell C n) → cubicalChainModule (MoorePathFrom B b) H R),
      (∀ x, k x ∈ cubicalChainModuleGrading (MoorePathFrom B b) H R (-(x.1 : ℤ) - 1)) ∧
      ∀ x, cubicalChainModuleDifferential (MoorePathFrom B b) H R (k x) +
          rowFiniteSignedMap (R := R) (A := loopChainAlgebra B b R)
            (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R) k
            ((brownCocycle H R τ hC).m x) =
        brownComparison H R τ hC x - linearCombination (loopChainAlgebra B b R) g (E.ν.ν x) :=
  exists_rowFiniteHomologous_homotopy (wellFounded_mem_support_brownCocycle τ hC) hm
    (pathFromChain_isDGLeftModule B b H R) (brownComparison_mem_cubicalChainModuleGrading τ hC) hg
    (linearCombination_brownComparison_brownCocycle_m τ hC) hgd
    (exists_rowFiniteTwistedDifferential_brownCocycle_eq τ hC) hgrel

/-- **Brown's cocycle does not depend on the paths or on the CW structure.** For two CW
structures `C` and `C'` on `B` and any choices of Moore paths `τ` and `τ'` from `b` to the centres
of their cells, the two Brown cocycles are homologous, so their twisted complexes with
coefficients in any DG right module are homotopy equivalent
(`TauCeti.RowFiniteHomologous.homotopyEquiv`), through specified continuation maps. -/
theorem exists_rowFiniteHomologous_brownCocycle_brownCocycle {C' : Set B} [CWComplex C']
    (τ' : ∀ (n : ℕ) (j : cell C' n), MoorePathBetween B b (map n j 0)) (hC' : ∀ x, x ∈ C') :
    Nonempty (RowFiniteHomologous (loopChain_isDGAlgebra B b R) (brownCocycle H R τ hC)
      (brownCocycle H R τ' hC')) :=
  let ⟨E, _⟩ := exists_rowFiniteHomologous_brownCocycle τ hC
    (wellFounded_mem_support_brownCocycle τ' hC')
    (brownComparison_mem_cubicalChainModuleGrading τ' hC')
    (linearCombination_brownComparison_brownCocycle_m τ' hC')
    (exists_rowFiniteTwistedDifferential_brownCocycle_eq τ' hC')
  ⟨E⟩

end TauCeti
