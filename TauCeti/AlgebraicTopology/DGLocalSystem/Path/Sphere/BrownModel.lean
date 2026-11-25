/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.DerivedTensor
public import TauCeti.AlgebraicTopology.DGLocalSystem.SphereResolution

/-!
# Brown's model of a sphere

For the sphere `Sⁿ`, `n = m + 2`, with one `0`-cell at the pole and one `n`-cell attached along the
attaching cycle `x` of its top cell, Brown's twisted tensor product is the free module of
`TauCeti.sphereCellCocycle`, one cell attached along a cycle (`TauCeti.cycleCellCocycle`). Its
comparison with the chains `C_*(P_b Sⁿ; k)` on the Moore paths from the pole
(`TauCeti.cycleCellPathComparison`) sends the generator of the top cell to the path cube
`TauCeti.spherePathCube` of Moore paths from the pole along the top cell
(`TauCeti.spherePathChain`), whose boundary is the image of the attaching cycle `x`
(`TauCeti.cubicalChainModuleDifferential_spherePathChain`). The module of
`TauCeti.sphereCellCocycle` resolves the ground ring
(`TauCeti.exists_sphereCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero`), so it is a
Brown model of `C_*(P_b Sⁿ; k)` (`TauCeti.sphereBrownModel`), and it computes the derived tensor
product with the ground ring
(`TauCeti.nonempty_sphereCellCocycle_localizedFunctor_iso_derivedTensor_loopChainAugmentation`):
for every DG local system `𝓕` on `Sⁿ`, the twisted complex `𝓕 e₀ ⊕ 𝓕 e₁` with `D e₁ = x e₀` has
cohomology `Tor^{C_*(Ω_b Sⁿ; k)}(𝓕, k)`. For `S²` the attaching cycle has dimension `1`.

## Main definitions

* `TauCeti.spherePathChain`: the path cube of the top cell of a sphere, in `C_*(P_b Sⁿ; k)`.
* `TauCeti.sphereBrownModel`: Brown's model of the chains on the based paths of a sphere.

## Main results

* `TauCeti.cubicalChainModuleDifferential_spherePathChain`: the boundary of the path cube of a
  sphere is the attaching cycle acting on the point chain of the pole.
* `TauCeti.nonempty_sphereCellCocycle_localizedFunctor_iso_derivedTensor_loopChainAugmentation`:
  Brown's resolution of a sphere computes the derived tensor product with the ground ring.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
-/

public noncomputable section

open AlgebraicTopology CategoryTheory Metric

universe uM

namespace TauCeti

open NormalizedCubicalChain

/-! ### The sphere -/

section Sphere

variable {ι : Type} [Fintype ι] {m : ℕ} (h : Fintype.card ι = m + 3) (H : Type*) (k : Type)
  [CommRing k]

local notation "Sph" => sphere (0 : EuclideanSpace ℝ ι) 1

/-- **The path cube of the top cell of a sphere**, as a chain on the based path space: the singular
`(m + 2)`-cube `TauCeti.spherePathCube` of Moore paths from the pole along the top cell of `Sⁿ`,
`n = m + 2`, in `C_*(P_b Sⁿ; k)`. It is the image of the generator of the top cell in Brown's model
of the sphere. -/
def spherePathChain : cubicalChainModule (MoorePathFrom Sph (spherePolePoint h)) H k :=
  cubicalChainModuleLof _ H k (m + 1 + 1)
    (ofCube (MoorePathFrom Sph (spherePolePoint h)) k (spherePathCube h))

/-- Unfold `TauCeti.spherePathChain`. -/
theorem spherePathChain_def :
    spherePathChain h H k = cubicalChainModuleLof _ H k (m + 1 + 1)
      (ofCube (MoorePathFrom Sph (spherePolePoint h)) k (spherePathCube h)) :=
  (rfl)

/-- The path cube of a sphere `Sⁿ`, `n = m + 2`, has dimension `n`. -/
theorem spherePathChain_mem :
    spherePathChain h H k ∈ cubicalChainModuleGrading (MoorePathFrom Sph (spherePolePoint h)) H k
      (-(((m + 1 : ℕ) : ℤ) + 1)) :=
  mem_cubicalChainModuleGrading_iff.2 (Or.inr ⟨m + 1 + 1, _, by push_cast; ring, rfl⟩)

/-- **The boundary of the path cube of a sphere** is the attaching cycle `x` of the top cell acting
on the point chain `[b]` of the constant path at the pole: `d σ = x · [b]`. -/
theorem cubicalChainModuleDifferential_spherePathChain :
    cubicalChainModuleDifferential (MoorePathFrom Sph (spherePolePoint h)) H k
        (spherePathChain h H k) =
      sphereAttachingChain h k • cubicalChainModulePoint (MoorePathFrom Sph (spherePolePoint h)) H k
        (MoorePathFrom.refl Sph (spherePolePoint h)) := by
  -- A chain `z` of loops acts on `[b]` as its push-forward to the based paths.
  have key (z : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k (m + 1)) :
      cubicalChainLof _ k (m + 1) z • cubicalChainModulePoint
          (MoorePathFrom Sph (spherePolePoint h)) H k (MoorePathFrom.refl Sph (spherePolePoint h)) =
        cubicalChainModuleLof _ H k (m + 1) (map k MooreLoopSpace.toMoorePathFrom (m + 1) z) := by
    -- The action lands in degree `m + 1 + 0`, which is `m + 1` by definition, so the closing
    -- `rfl` of `rw` finishes the proof.
    rw [cubicalChainModulePoint_def, lof_smul_cubicalChainModuleLof,
      leftAct_ofCube_point_right _ _ _ MooreLoopSpace.toMoorePathFrom_eq_smul_refl]
  rw [spherePathChain_def, cubicalChainModuleDifferential_lof_succ, boundary_ofCube_spherePathCube,
    sphereAttachingChain_def]
  -- Both sides now carry the underlying chain of the attaching cycle, a cycle on the loops
  -- `(loopPair Sph b).snd` of the pair. This space is `TopCat.of (MooreLoopSpace Sph b)` by
  -- definition, so that chain is a chain of Moore loops and `key` applies to it.
  exact (key ((((normalizedCubicalChainComplex k).obj _).iCycles (m + 1)).hom
    (sphereAttachingCycle h k))).symm

/-- **Brown's model of a sphere.** For the sphere `Sⁿ`, `n = m + 2`, with one `0`-cell at the
pole and one `n`-cell attached along the attaching cycle `x` of its top cell, the semi-free
resolution `C_*(Ω_b Sⁿ; k) e₀ ⊕ C_*(Ω_b Sⁿ; k) e₁` with `D e₁ = x e₀` of
`TauCeti.sphereCellCocycle h k`, with the comparison sending `e₀` to the point chain `[b]` of the
pole and `e₁` to the path cube `TauCeti.spherePathChain` of the top cell, is a Brown model of the
chains `C_*(P_b Sⁿ; k)` on the based paths. -/
def sphereBrownModel :
    BrownModel Sph (spherePolePoint h) H k (Unit ⊕ Unit)
      (Sum.elim (fun _ ↦ 0) (fun _ ↦ ((m + 1 : ℕ) : ℤ) + 1)) :=
  cycleCellBrownModel H (sphereAttachingChain_mem h k)
    (cubicalChainDifferential_sphereAttachingChain h k) (spherePathChain h H k)
    (spherePathChain_mem h H k) (cubicalChainModuleDifferential_spherePathChain h H k)
    (exists_sphereCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero h k)

/-- The cocycle of Brown's model of a sphere is `TauCeti.sphereCellCocycle`. -/
@[simp]
theorem sphereBrownModel_cocycle : (sphereBrownModel h H k).cocycle = sphereCellCocycle h k :=
  cycleCellBrownModel_cocycle _ _ _

/-- Brown's model of a sphere sends the generator `e₀` of the `0`-cell to the point chain `[b]` of
the constant path at the pole. -/
@[simp]
theorem sphereBrownModel_comparison_inl (y : Unit) :
    (sphereBrownModel h H k).comparison (Sum.inl y) =
      cubicalChainModulePoint (MoorePathFrom Sph (spherePolePoint h)) H k
        (MoorePathFrom.refl Sph (spherePolePoint h)) :=
  cycleCellBrownModel_comparison_inl _ _ _ y

/-- Brown's model of a sphere sends the generator `e₁` of the top cell to its path cube. -/
@[simp]
theorem sphereBrownModel_comparison_inr (y : Unit) :
    (sphereBrownModel h H k).comparison (Sum.inr y) = spherePathChain h H k :=
  cycleCellBrownModel_comparison_inr _ _ _ y

/-- The comparison of Brown's model of a sphere sends `e₀` to the point chain of the pole and `e₁`
to the path cube of the top cell. -/
@[simp]
theorem linearCombination_sphereBrownModel_comparison :
    Finsupp.linearCombination (loopChainAlgebra Sph (spherePolePoint h) k)
        (sphereBrownModel h H k).comparison =
      cycleCellPathComparison H k (spherePathChain h H k) :=
  linearCombination_cycleCellBrownModel_comparison _ _ _

/-- **Brown's resolution of a sphere computes the derived tensor product with the ground ring.**
For the sphere `Sⁿ`, `n = m + 2`, based at the pole, tensoring DG right modules `𝓕` over
`C_*(Ω_b Sⁿ; k)` with the free module of `TauCeti.sphereCellCocycle`, which gives the twisted
complex `𝓕 e₀ ⊕ 𝓕 e₁` with `D e₁ = x e₀` for the attaching cycle `x` of the top cell, induces on
any localizations at the quasi-isomorphisms a functor isomorphic to the derived tensor product
`- ⊗^L k` with the ground ring. -/
theorem nonempty_sphereCellCocycle_localizedFunctor_iso_derivedTensor_loopChainAugmentation
    {D₁ D₂ : Type*} [Category* D₁] [Category* D₂]
    (L₁ : DGRightModuleCat.{0, 0, uM} (loopChain_isDGAlgebra Sph (spherePolePoint h) k) ⥤ D₁)
    [L₁.IsLocalization
      (DGRightModuleCat.quasiIsos (loopChain_isDGAlgebra Sph (spherePolePoint h) k))]
    (L₂ : CochainComplex (ModuleCat.{uM} k) ℤ ⥤ D₂)
    [L₂.IsLocalization (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))] :
    Nonempty (((sphereCellCocycle h k).coefficientLocalizerMorphism
        (loopChain_isDGAlgebra Sph (spherePolePoint h) k)
        (wellFounded_mem_support_cycleCellCocycle _ _)).localizedFunctor L₁ L₂ ≅
      (derivedTensorLocalizerMorphism (loopChain_isDGAlgebra Sph (spherePolePoint h) k)
        (loopChainAugmentation Sph (spherePolePoint h) k).bimoduleGrading
        (loopChainAugmentation Sph (spherePolePoint h) k).bimoduleDifferential).localizedFunctor
          L₁ L₂) := by
  -- The chains on the based paths may be taken over any monoid, since the localized functors do
  -- not involve them.
  have hB := (sphereBrownModel h PUnit.{1} k).nonempty_localizedFunctor_iso_derivedTensor L₁ L₂
  simpa only [sphereBrownModel_cocycle] using hB

end Sphere

end TauCeti
