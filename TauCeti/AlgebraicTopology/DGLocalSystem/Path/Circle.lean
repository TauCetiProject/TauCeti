/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Augmentation
public import TauCeti.AlgebraicTopology.DGLocalSystem.CircleResolution
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.BrownModel

/-!
# Brown's resolution of a circle maps quasi-isomorphically to the chains on its based paths

For a Moore loop `γ` at `b`, the free module `K = C_*(Ω_b B; R) e₀ ⊕ C_*(Ω_b B; R) e₁` of
`TauCeti.loopCellCocycle R γ`, with `D e₁ = ([γ] - [1]) e₀`, is Brown's semi-free resolution of
`R` over `C_*(Ω_b B; R)` for a circle with one `0`-cell at `b` and one `1`-cell attached along
`γ` (`TauCeti.exists_loopCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero`). Brown's
construction compares such a module with the chains `C_*(P_b B; R)` on the Moore paths from `b`, a
differential graded left module over `C_*(Ω_b B; R)` through concatenation in front
(`TauCeti.pathFromChain_isDGLeftModule`), by a map that is linear over the loop algebra: the
generator of each cell goes to a chain of paths whose boundary is the image of its attaching row.
This file constructs that comparison for the circle and proves that it is a quasi-isomorphism.

* The generator `e₀` of the `0`-cell goes to the point chain `[b]` of the constant path of length
  zero at `b` (`TauCeti.cubicalChainModulePoint`).
* The generator `e₁` of the `1`-cell goes to the `1`-chain `c_γ` of the initial segments of `γ`
  (`TauCeti.loopCellPathChain`): minus the cone on the point chain `[γ]` along the contraction
  `TauCeti.MoorePathFrom.truncateHomotopy` of the based path space. Its boundary is `[γ] - [b]`
  (`TauCeti.cubicalChainModuleDifferential_loopCellPathChain`, from
  `TauCeti.cubicalChainModuleDifferential_cone_cubicalChainModulePoint`), and since
  loops act on point chains by concatenation in front (`TauCeti.point_smul_cubicalChainModulePoint`)
  this is `([γ] - [1]) · [b]`, the image of the row of `e₁`.

So the map `α e₀ + β e₁ ↦ α · [b] + β · c_γ` (`TauCeti.loopCellPathComparison`) commutes with the
differentials (`TauCeti.loopCellPathComparison_differential`), for every Moore loop `γ` of every
space, and it commutes with the augmentations
(`TauCeti.cubicalChainModuleAugmentation_loopCellPathComparison`).

The augmentation of `C_*(P_b B; R)` is always a quasi-isomorphism onto `R`, since the based path
space is contractible (`TauCeti.exists_pathFromChainDifferential_eq_of_augmentation_eq_zero`).
Whenever that of `K` is too, as when `B` is aspherical at `b` and the class of `γ` generates an
infinite cyclic fundamental group, so that `K` is Brown's resolution, the comparison is a
quasi-isomorphism
(`TauCeti.exists_loopCellCocycle_differential_eq_and_loopCellPathComparison_add_eq`, through
`TauCeti.exists_differential_eq_and_add_eq_of_augmentation`), in the form used for the attachment
of cells (`TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists`): every relative cycle
`(u, w)`, with `D u = 0` and `c(u) = d w`, is a relative boundary `(D u', c(u') + d w')`. The
case of the complex unit circle and its counterclockwise loop is
`TauCeti.exists_loopCellCocycle_expLoop_differential_eq_and_loopCellPathComparison_add_eq`. With
the comparison, `K` is then a Brown model of `C_*(P_b B; R)` (`TauCeti.loopCellBrownModel`).

This is the circle instance of the comparison between Brown's semi-free model and the chains on
the based path space, whose general cell-by-cell construction runs along the skeletal filtration
`TauCeti.pathFromChainSkeleton`.

## Main definitions

* `TauCeti.loopCellPathChain`: the `1`-chain `c_γ` of initial segments of a Moore loop, in
  `C_*(P_b B; R)`.
* `TauCeti.loopCellPathComparison`: the map `K → C_*(P_b B; R)`, linear over `C_*(Ω_b B; R)`.
* `TauCeti.loopCellBrownModel`: `K` with this comparison, as a Brown model, when `K` resolves `R`.

## Main results

* `TauCeti.cubicalChainModuleDifferential_loopCellPathChain`: `d c_γ = [γ] - [b]`.
* `TauCeti.loopCellPathComparison_differential`: the comparison commutes with the differentials.
* `TauCeti.cubicalChainModuleAugmentation_loopCellPathComparison`: it commutes with the
  augmentations.
* `TauCeti.exists_loopCellCocycle_differential_eq_and_loopCellPathComparison_add_eq`: when `K`
  resolves `R`, the comparison is a quasi-isomorphism.
* `TauCeti.exists_loopCellCocycle_expLoop_differential_eq_and_loopCellPathComparison_add_eq`: the
  case of the circle.

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

variable (H R) in
/-- **The comparison of Brown's resolution of a circle with the chains on its based paths**: the
map from the free module of `TauCeti.loopCellCocycle R γ` to `C_*(P_b B; R)`, linear over the loop
algebra `C_*(Ω_b B; R)`, sending the generator `e₀` of the `0`-cell to the point chain `[b]` of the
constant path and the generator `e₁` of the `1`-cell to the chain `c_γ` of the initial segments of
`γ`. -/
def loopCellPathComparison (γ : MooreLoopSpace B b) :
    (Unit ⊕ Unit →₀ loopChainAlgebra B b R) →ₗ[loopChainAlgebra B b R]
      cubicalChainModule (MoorePathFrom B b) H R :=
  Finsupp.linearCombination _
    (Sum.elim (fun _ ↦ cubicalChainModulePoint (MoorePathFrom B b) H R (MoorePathFrom.refl B b))
      (fun _ ↦ loopCellPathChain H R γ))

@[simp]
theorem loopCellPathComparison_single_inl (γ : MooreLoopSpace B b) (α : loopChainAlgebra B b R) :
    loopCellPathComparison H R γ (Finsupp.single (Sum.inl ()) α) =
      α • cubicalChainModulePoint (MoorePathFrom B b) H R (MoorePathFrom.refl B b) := by
  simp [loopCellPathComparison]

@[simp]
theorem loopCellPathComparison_single_inr (γ : MooreLoopSpace B b) (β : loopChainAlgebra B b R) :
    loopCellPathComparison H R γ (Finsupp.single (Sum.inr ()) β) =
      β • loopCellPathChain H R γ := by
  simp [loopCellPathComparison]

/-- The comparison on `α e₀ + β e₁` is `α · [b] + β · c_γ`. -/
theorem loopCellPathComparison_apply (γ : MooreLoopSpace B b)
    (u : Unit ⊕ Unit →₀ loopChainAlgebra B b R) :
    loopCellPathComparison H R γ u =
      u (Sum.inl ()) •
          cubicalChainModulePoint (MoorePathFrom B b) H R (MoorePathFrom.refl B b) +
        u (Sum.inr ()) • loopCellPathChain H R γ := by
  have hu : u = Finsupp.single (Sum.inl ()) (u (Sum.inl ())) +
      Finsupp.single (Sum.inr ()) (u (Sum.inr ())) := by
    ext i
    rcases i with ⟨⟩ | ⟨⟩ <;> simp
  conv_lhs => rw [hu]
  rw [map_add, loopCellPathComparison_single_inl, loopCellPathComparison_single_inr]

/-- **The comparison commutes with the differentials**, for every Moore loop `γ` of every space:
the image `c_γ` of `e₁` bounds the image `([γ] - [1]) · [b]` of its attaching row. -/
theorem loopCellPathComparison_differential (γ : MooreLoopSpace B b)
    (u : Unit ⊕ Unit →₀ loopChainAlgebra B b R) :
    loopCellPathComparison H R γ
        (rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
          (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
          (d := cubicalChainDifferential (MooreLoopSpace B b) R) (loopCellCocycle R γ).m u) =
      cubicalChainModuleDifferential (MoorePathFrom B b) H R (loopCellPathComparison H R γ u) := by
  refine ((forall_linearCombination_rowFiniteTwistedDifferential_iff
    (pathFromChain_isDGLeftModule B b H R) _ _).2 ?_) u
  rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
  · simp
  · simp

/-- **The comparison commutes with the augmentations**: the augmentation of the image of `u` in
`C_*(P_b B; R)` is the augmentation of the coefficient of `e₀`. -/
@[simp]
theorem cubicalChainModuleAugmentation_loopCellPathComparison (γ : MooreLoopSpace B b)
    (u : Unit ⊕ Unit →₀ loopChainAlgebra B b R) :
    cubicalChainModuleAugmentation (MoorePathFrom B b) H R (loopCellPathComparison H R γ u) =
      loopCellAugmentation B b R u := by
  simp [loopCellPathComparison_apply, pathFromChainAugmentation_smul, loopCellAugmentation_apply]

end Comparison

section QuasiIso

variable {B : Type*} [TopologicalSpace B] {b : B} {H : Type*} {R : Type*} [CommRing R]

/-- **Brown's resolution of a circle is quasi-isomorphic to the chains on its based paths.** Let
the free module `K` of `TauCeti.loopCellCocycle R γ` resolve `R`: every cycle of `K` whose
augmentation vanishes is a boundary, as over an aspherical space whose fundamental group is
infinite cyclic, generated by the class of `γ`
(`TauCeti.exists_loopCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero`). Then the
comparison `TauCeti.loopCellPathComparison` from `K` to `C_*(P_b B; R)` is a quasi-isomorphism:
every relative cycle `(u, w)`, with `D u = 0` and `c(u) = d w`, is a relative boundary
`(D u', c(u') + d w')`.

Both augmentations are quasi-isomorphisms onto `R`, the comparison commutes with them, and `e₀`
is a cycle of augmentation `1` (`TauCeti.exists_differential_eq_and_add_eq_of_augmentation`). -/
theorem exists_loopCellCocycle_differential_eq_and_loopCellPathComparison_add_eq
    {γ : MooreLoopSpace B b}
    (hK : ∀ {u : Unit ⊕ Unit →₀ loopChainAlgebra B b R},
      rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R) (loopCellCocycle R γ).m u = 0 →
      loopCellAugmentation B b R u = 0 →
      ∃ v, rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R) (loopCellCocycle R γ).m v = u)
    {u : Unit ⊕ Unit →₀ loopChainAlgebra B b R} {w : cubicalChainModule (MoorePathFrom B b) H R}
    (hu : rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
      (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
      (d := cubicalChainDifferential (MooreLoopSpace B b) R) (loopCellCocycle R γ).m u = 0)
    (hw : loopCellPathComparison H R γ u = cubicalChainModuleDifferential _ H R w) :
    ∃ u' w', rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R) (loopCellCocycle R γ).m u' = u ∧
      loopCellPathComparison H R γ u' + cubicalChainModuleDifferential _ H R w' = w :=
  exists_differential_eq_and_add_eq_of_augmentation
    (f := (loopCellPathComparison H R γ).restrictScalars R)
    (loopCellPathComparison_differential γ)
    (cubicalChainModuleAugmentation_loopCellPathComparison γ)
    (cubicalChainModuleAugmentation_differential (G := H))
    (loopCellCocycle_differential_single_inl_one γ) (by simp) hK
    exists_pathFromChainDifferential_eq_of_augmentation_eq_zero hu hw

/-- **Brown's resolution of the circle is quasi-isomorphic to the chains on its based paths.** For
the complex unit circle, based at `1`, with its `1`-cell attached along the counterclockwise loop
`t ↦ exp(2πit)`, the comparison `TauCeti.loopCellPathComparison` with `C_*(P_1 S¹; R)` is a
quasi-isomorphism: every relative cycle is a relative boundary. -/
theorem exists_loopCellCocycle_expLoop_differential_eq_and_loopCellPathComparison_add_eq
    {H : Type*} {R : Type} [CommRing R] {u : Unit ⊕ Unit →₀ loopChainAlgebra Circle 1 R}
    {w : cubicalChainModule (MoorePathFrom Circle 1) H R}
    (hu : rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra Circle 1 R)
      (𝒜 := cubicalChainGrading (MooreLoopSpace Circle 1) R)
      (d := cubicalChainDifferential (MooreLoopSpace Circle 1) R)
      (loopCellCocycle R Circle.expLoop.toMooreLoop).m u = 0)
    (hw : loopCellPathComparison H R Circle.expLoop.toMooreLoop u =
      cubicalChainModuleDifferential _ H R w) :
    ∃ u' w', rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra Circle 1 R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace Circle 1) R)
        (d := cubicalChainDifferential (MooreLoopSpace Circle 1) R)
        (loopCellCocycle R Circle.expLoop.toMooreLoop).m u' = u ∧
      loopCellPathComparison H R Circle.expLoop.toMooreLoop u' +
        cubicalChainModuleDifferential _ H R w' = w :=
  exists_loopCellCocycle_differential_eq_and_loopCellPathComparison_add_eq
    exists_loopCellCocycle_expLoop_differential_eq_of_loopCellAugmentation_eq_zero hu hw

end QuasiIso

section Model

variable {B : Type*} [TopologicalSpace B] {b : B} (H : Type*) {R : Type*} [CommRing R]

/-- **Brown's resolution of a circle as a Brown model.** Let the free module `K` of
`TauCeti.loopCellCocycle R γ` resolve `R`: every cycle of `K` whose augmentation vanishes is a
boundary, as for the counterclockwise loop of the complex unit circle
(`TauCeti.exists_loopCellCocycle_expLoop_differential_eq_of_loopCellAugmentation_eq_zero`). Then
`K`, with the comparison `TauCeti.loopCellPathComparison` sending `e₀` to the point chain `[b]` and
`e₁` to the chain `c_γ` of initial segments of `γ`, is a Brown model of `C_*(P_b B; R)`. -/
def loopCellBrownModel (γ : MooreLoopSpace B b)
    (hK : ∀ {u : Unit ⊕ Unit →₀ loopChainAlgebra B b R},
      rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R) (loopCellCocycle R γ).m u = 0 →
      loopCellAugmentation B b R u = 0 →
      ∃ v, rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R) (loopCellCocycle R γ).m v = u) :
    BrownModel B b H R (Unit ⊕ Unit) (Sum.elim (fun _ ↦ 0) (fun _ ↦ 1)) where
  cocycle := loopCellCocycle R γ
  wellFounded := wellFounded_mem_support_loopCellCocycle γ
  comparison := Sum.elim
    (fun _ ↦ cubicalChainModulePoint (MoorePathFrom B b) H R (MoorePathFrom.refl B b))
    (fun _ ↦ loopCellPathChain H R γ)
  comparison_mem := by
    rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
    · simpa using cubicalChainModulePoint_mem (G := H) (R := R) (MoorePathFrom.refl B b)
    · simpa using loopCellPathChain_mem (H := H) (R := R) γ
  -- `loopCellPathComparison` is by definition the linear combination of these images.
  linearCombination_comparison_m := (forall_linearCombination_rowFiniteTwistedDifferential_iff
    (pathFromChain_isDGLeftModule B b H R) _ _).1 (loopCellPathComparison_differential γ)
  exists_differential_eq_and_linearCombination_add_eq _ _ hu hw :=
    exists_loopCellCocycle_differential_eq_and_loopCellPathComparison_add_eq hK hu hw

variable {H} {γ : MooreLoopSpace B b}

/-- The cocycle of the Brown model of a circle is `TauCeti.loopCellCocycle`. -/
@[simp]
theorem loopCellBrownModel_cocycle (hK) :
    (loopCellBrownModel H γ hK).cocycle = loopCellCocycle R γ := (rfl)

/-- The Brown model of a circle sends the generator `e₀` of the `0`-cell to the point chain `[b]`
of the constant path. -/
@[simp]
theorem loopCellBrownModel_comparison_inl (hK) (x : Unit) :
    (loopCellBrownModel H γ hK).comparison (Sum.inl x) =
      cubicalChainModulePoint (MoorePathFrom B b) H R (MoorePathFrom.refl B b) := (rfl)

/-- The Brown model of a circle sends the generator `e₁` of the `1`-cell to the chain `c_γ` of
initial segments of `γ`. -/
@[simp]
theorem loopCellBrownModel_comparison_inr (hK) (x : Unit) :
    (loopCellBrownModel H γ hK).comparison (Sum.inr x) = loopCellPathChain H R γ := (rfl)

/-- The comparison of the Brown model of a circle is `TauCeti.loopCellPathComparison`. -/
@[simp]
theorem linearCombination_loopCellBrownModel_comparison (hK) :
    Finsupp.linearCombination (loopChainAlgebra B b R) (loopCellBrownModel H γ hK).comparison =
      loopCellPathComparison H R γ := (rfl)

end Model

end TauCeti
