/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.CircleResolution
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.CycleCell

/-!
# Brown's resolution of a circle maps quasi-isomorphically to the chains on its based paths

For a Moore loop `γ` at `b`, the free module `K = C_*(Ω_b B; R) e₀ ⊕ C_*(Ω_b B; R) e₁` of
`TauCeti.loopCellCocycle R γ`, with `D e₁ = ([γ] - [1]) e₀`, is Brown's semi-free resolution of
`R` over `C_*(Ω_b B; R)` for a circle with one `0`-cell at `b` and one `1`-cell attached along
`γ` (`TauCeti.exists_loopCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero`). It is the
module of one cell attached along the `0`-cycle `[γ] - [1]` (`TauCeti.cycleCellCocycle`), which
Brown's construction compares with the chains `C_*(P_b B; R)` on the Moore paths from `b` by the
map `TauCeti.cycleCellPathComparison`, linear over the loop algebra: the generator `e₀` of the
`0`-cell goes to the point chain `[b]` of the constant path, and the generator `e₁` of the `1`-cell
to a chain of paths whose boundary is the image of its attaching row. This file supplies that
chain for the circle.

* The generator `e₁` of the `1`-cell goes to the `1`-chain `c_γ` of the initial segments of `γ`
  (`TauCeti.loopCellPathChain`): minus the cone on the point chain `[γ]` along the contraction
  `TauCeti.MoorePathFrom.truncateHomotopy` of the based path space. Its boundary is `[γ] - [b]`
  (`TauCeti.cubicalChainModuleDifferential_loopCellPathChain`, from
  `TauCeti.cubicalChainModuleDifferential_cone_cubicalChainModulePoint`), and since loops act on
  point chains by concatenation in front
  (`TauCeti.cubicalChainPoint_smul_cubicalChainModulePoint`) this is `([γ] - [1]) · [b]`, the image
  of the row of `e₁` (`TauCeti.cubicalChainModuleDifferential_loopCellPathChain_eq_smul`).

So the map `α e₀ + β e₁ ↦ α · [b] + β · c_γ` commutes with the differentials and the augmentations,
for every Moore loop `γ` of every space. Whenever `K` resolves `R`, as when `B` is aspherical at `b`
and the class of `γ` generates an infinite cyclic fundamental group, the comparison is a
quasi-isomorphism, since the based path space is contractible, and `K` with the comparison is a
Brown model of `C_*(P_b B; R)` (`TauCeti.loopCellBrownModel`). The case of the complex unit circle
and its counterclockwise loop is
`TauCeti.exists_loopCellCocycle_expLoop_differential_eq_and_cycleCellPathComparison_add_eq`.

This is the circle instance of the comparison between Brown's semi-free model and the chains on
the based path space, whose general cell-by-cell construction runs along the skeletal filtration
`TauCeti.pathFromChainSkeleton`.

## Main definitions

* `TauCeti.loopCellPathChain`: the `1`-chain `c_γ` of initial segments of a Moore loop, in
  `C_*(P_b B; R)`.
* `TauCeti.loopCellBrownModel`: `K` with the comparison, as a Brown model, when `K` resolves `R`.

## Main results

* `TauCeti.cubicalChainModuleDifferential_loopCellPathChain`: `d c_γ = [γ] - [b]`.
* `TauCeti.exists_loopCellCocycle_expLoop_differential_eq_and_cycleCellPathComparison_add_eq`: the
  comparison is a quasi-isomorphism for the circle.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
-/

public noncomputable section

open AlgebraicTopology

namespace TauCeti

open NormalizedCubicalChain

section Comparison

variable {B : Type*} [TopologicalSpace B] {b : B}

variable (H : Type*) (R : Type*) [CommRing R]

/-- The `1`-chain `c_γ` of the **initial segments of a Moore loop** `γ`, in `C_*(P_b B; R)`: minus
the cone, along the contraction `TauCeti.MoorePathFrom.truncateHomotopy` of the based path space, on
the point chain of `γ` read as a path from `b`. -/
def loopCellPathChain (γ : MooreLoopSpace B b) : cubicalChainModule (MoorePathFrom B b) H R :=
  -cubicalChainModuleCone R MoorePathFrom.truncateHomotopy
    (cubicalChainModulePoint _ H R (γ • MoorePathFrom.refl B b))

variable {H R}

/-- Unfold `TauCeti.loopCellPathChain`. -/
theorem loopCellPathChain_def (γ : MooreLoopSpace B b) :
    loopCellPathChain H R γ = -cubicalChainModuleCone R MoorePathFrom.truncateHomotopy
      (cubicalChainModulePoint _ H R (γ • MoorePathFrom.refl B b)) :=
  (rfl)

/-- The chain `c_γ` lies in degree `-1`. -/
theorem loopCellPathChain_mem (γ : MooreLoopSpace B b) :
    loopCellPathChain H R γ ∈ cubicalChainModuleGrading (MoorePathFrom B b) H R (-1) := by
  rw [loopCellPathChain_def, cubicalChainModulePoint_def, cubicalChainModuleCone_lof]
  exact neg_mem (by simpa using cubicalChainModuleLof_mem (G := H) (n := 0 + 1) _)

/-- The augmentation of `c_γ` vanishes, since it is a `1`-chain. -/
@[simp]
theorem cubicalChainModuleAugmentation_loopCellPathChain (γ : MooreLoopSpace B b) :
    cubicalChainModuleAugmentation (MoorePathFrom B b) H R (loopCellPathChain H R γ) = 0 := by
  rw [loopCellPathChain_def, cubicalChainModulePoint_def, cubicalChainModuleCone_lof, map_neg,
    cubicalChainModuleAugmentation_lof_succ, neg_zero]

/-- **The boundary of the initial segments of a loop**: `d c_γ = [γ] - [b]`, the difference of the
point chains of `γ`, read as a path from `b`, and of the constant path. -/
@[simp]
theorem cubicalChainModuleDifferential_loopCellPathChain (γ : MooreLoopSpace B b) :
    cubicalChainModuleDifferential (MoorePathFrom B b) H R (loopCellPathChain H R γ) =
      cubicalChainModulePoint (MoorePathFrom B b) H R (γ • MoorePathFrom.refl B b) -
        cubicalChainModulePoint (MoorePathFrom B b) H R (MoorePathFrom.refl B b) := by
  rw [loopCellPathChain_def, map_neg, cubicalChainModuleDifferential_cone_cubicalChainModulePoint,
    neg_sub]

/-- **The boundary of the initial segments of a loop is the image of the attaching row**:
`d c_γ = ([γ] - [1]) · [b]`, since the point chain of a loop acts on `[b]` by concatenation in
front. -/
theorem cubicalChainModuleDifferential_loopCellPathChain_eq_smul (γ : MooreLoopSpace B b) :
    cubicalChainModuleDifferential (MoorePathFrom B b) H R (loopCellPathChain H R γ) =
      (cubicalChainPoint (MooreLoopSpace B b) R γ - 1) •
        cubicalChainModulePoint (MoorePathFrom B b) H R (MoorePathFrom.refl B b) := by
  rw [cubicalChainModuleDifferential_loopCellPathChain, sub_smul, one_smul,
    cubicalChainPoint_smul_cubicalChainModulePoint]

end Comparison

section Model

variable {B : Type*} [TopologicalSpace B] {b : B} (H : Type*) {R : Type*} [CommRing R]

/-- **Brown's resolution of a circle as a Brown model.** Let the free module `K` of
`TauCeti.loopCellCocycle R γ` resolve `R`: every cycle of `K` whose augmentation vanishes is a
boundary, as for the counterclockwise loop of the complex unit circle
(`TauCeti.exists_loopCellCocycle_expLoop_differential_eq_of_loopCellAugmentation_eq_zero`). Then
`K`, with the comparison `TauCeti.cycleCellPathComparison` sending `e₀` to the point chain `[b]`
and `e₁` to the chain `c_γ` of initial segments of `γ`, is a Brown model of `C_*(P_b B; R)`: the
Brown model `TauCeti.cycleCellBrownModel` of a cell attached along `[γ] - [1]`. -/
def loopCellBrownModel (γ : MooreLoopSpace B b)
    (hK : ∀ {u : Unit ⊕ Unit →₀ loopChainAlgebra B b R},
      rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R) (loopCellCocycle R γ).m u = 0 →
      loopCellAugmentation B b R u = 0 →
      ∃ v, rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R) (loopCellCocycle R γ).m v = u) :
    BrownModel B b H R (Unit ⊕ Unit) (Sum.elim (fun _ ↦ 0) (fun _ ↦ 1)) :=
  cycleCellBrownModel H (by simpa using cubicalChainPoint_sub_one_mem γ)
    (cubicalChainDifferential_cubicalChainPoint_sub_one γ) (loopCellPathChain H R γ)
    (by simpa using loopCellPathChain_mem γ)
    (cubicalChainModuleDifferential_loopCellPathChain_eq_smul γ)
    (by rw [← loopCellCocycle_eq_cycleCellCocycle]; exact hK)

variable {H} {γ : MooreLoopSpace B b}

/-- The cocycle of the Brown model of a circle is `TauCeti.loopCellCocycle`. -/
@[simp]
theorem loopCellBrownModel_cocycle (hK) :
    (loopCellBrownModel H γ hK).cocycle = loopCellCocycle R γ :=
  (cycleCellBrownModel_cocycle _ _ _).trans (loopCellCocycle_eq_cycleCellCocycle γ).symm

/-- The Brown model of a circle sends the generator `e₀` of the `0`-cell to the point chain `[b]`
of the constant path. -/
@[simp]
theorem loopCellBrownModel_comparison_inl (hK) (x : Unit) :
    (loopCellBrownModel H γ hK).comparison (Sum.inl x) =
      cubicalChainModulePoint (MoorePathFrom B b) H R (MoorePathFrom.refl B b) :=
  cycleCellBrownModel_comparison_inl _ _ _ x

/-- The Brown model of a circle sends the generator `e₁` of the `1`-cell to the chain `c_γ` of
initial segments of `γ`. -/
@[simp]
theorem loopCellBrownModel_comparison_inr (hK) (x : Unit) :
    (loopCellBrownModel H γ hK).comparison (Sum.inr x) = loopCellPathChain H R γ :=
  cycleCellBrownModel_comparison_inr _ _ _ x

/-- The comparison of the Brown model of a circle is `TauCeti.cycleCellPathComparison`, sending
`e₁` to the chain `c_γ` of initial segments of `γ`. -/
@[simp]
theorem linearCombination_loopCellBrownModel_comparison (hK) :
    Finsupp.linearCombination (loopChainAlgebra B b R) (loopCellBrownModel H γ hK).comparison =
      cycleCellPathComparison H R (loopCellPathChain H R γ) :=
  linearCombination_cycleCellBrownModel_comparison _ _ _

end Model

section QuasiIso

/-- **Brown's resolution of the circle is quasi-isomorphic to the chains on its based paths.** For
the complex unit circle, based at `1`, with its `1`-cell attached along the counterclockwise loop
`t ↦ exp(2πit)`, the comparison `TauCeti.cycleCellPathComparison` with `C_*(P_1 S¹; R)` sending
`e₁` to the chain `c_γ` of initial segments of the loop is a quasi-isomorphism: every relative
cycle is a relative boundary. -/
theorem exists_loopCellCocycle_expLoop_differential_eq_and_cycleCellPathComparison_add_eq
    {H : Type*} {R : Type} [CommRing R] {u : Unit ⊕ Unit →₀ loopChainAlgebra Circle 1 R}
    {w : cubicalChainModule (MoorePathFrom Circle 1) H R}
    (hu : rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra Circle 1 R)
      (𝒜 := cubicalChainGrading (MooreLoopSpace Circle 1) R)
      (d := cubicalChainDifferential (MooreLoopSpace Circle 1) R)
      (loopCellCocycle R Circle.expLoop.toMooreLoop).m u = 0)
    (hw : cycleCellPathComparison H R (loopCellPathChain H R Circle.expLoop.toMooreLoop) u =
      cubicalChainModuleDifferential _ H R w) :
    ∃ u' w', rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra Circle 1 R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace Circle 1) R)
        (d := cubicalChainDifferential (MooreLoopSpace Circle 1) R)
        (loopCellCocycle R Circle.expLoop.toMooreLoop).m u' = u ∧
      cycleCellPathComparison H R (loopCellPathChain H R Circle.expLoop.toMooreLoop) u' +
        cubicalChainModuleDifferential _ H R w' = w := by
  -- This is the quasi-isomorphism of the Brown model of the circle.
  have hM := (loopCellBrownModel H Circle.expLoop.toMooreLoop
    exists_loopCellCocycle_expLoop_differential_eq_of_loopCellAugmentation_eq_zero
    ).exists_differential_eq_and_linearCombination_add_eq u w
  rw [loopCellBrownModel_cocycle, linearCombination_loopCellBrownModel_comparison] at hM
  exact hM hu hw

end QuasiIso

end TauCeti
