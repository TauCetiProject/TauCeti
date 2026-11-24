/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Interior.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# The inclusion of the interior of a manifold with corners

Let `M` be a charted space modelled with corners, through `I : H → E`, on a finite-dimensional
space `E`. Its interior `I.interior M` is a charted space modelled on `E`
(`ModelWithCorners.instChartedSpaceInterior`), whose chart at `x` is the extended chart of `M` at
`x`, restricted to the interior. This file studies the inclusion `Subtype.val : I.interior M → M`.

In the extended charts the inclusion is the identity: the extended chart of the interior at `x` is
the extended chart of `M` at `x`, restricted to the interior
(`ModelWithCorners.extChartAt_interior_apply` and its companions). Hence a map into the interior
is `C^n` exactly when its composite with the inclusion is
(`ModelWithCorners.contMDiff_subtypeVal_comp_interior_iff`, with versions within a set, at a point
and on a set), with no smoothness assumption on `M`. The inclusion is a `C^n` local diffeomorphism
at every regularity (`ModelWithCorners.isLocalDiffeomorph_subtypeVal_interior`) and its manifold
derivative is the identity of `E` (`ModelWithCorners.mfderiv_subtypeVal_interior`). When `M` has
no boundary, the inclusion is a diffeomorphism onto `M` (`ModelWithCorners.interiorDiffeomorph`).

## Main definitions

* `ModelWithCorners.interiorOpens`: the interior of `M`, as an open subset.
* `ModelWithCorners.interiorDiffeomorphOpens`: the identity diffeomorphism from the interior,
  charted by `E`, to the open subset `I.interiorOpens M`, charted by `H`.
* `ModelWithCorners.interiorDiffeomorph`: for `M` without boundary, the inclusion of the interior
  as a diffeomorphism onto `M`.

## Main results

* `ModelWithCorners.extChartAt_interior_apply`, `ModelWithCorners.extChartAt_interior_source`,
  `ModelWithCorners.extChartAt_interior_target`,
  `ModelWithCorners.coe_extChartAt_interior_symm_apply`: the extended charts of the interior are
  those of `M`, restricted to the interior.
* `ModelWithCorners.contMDiffWithinAt_subtypeVal_comp_interior_iff`,
  `ModelWithCorners.contMDiff_subtypeVal_comp_interior_iff`: maps into the interior are `C^n`
  exactly when they are as maps into `M`.
* `ModelWithCorners.isLocalDiffeomorph_subtypeVal_interior`: the inclusion is a `C^n` local
  diffeomorphism.
* `ModelWithCorners.mfderiv_subtypeVal_interior`: its manifold derivative is the identity of `E`.

The interior of a locally compact `M` is locally compact.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 1, manifolds with boundary: the interior of a manifold with boundary is an open
  submanifold without boundary.
-/

public section

noncomputable section

open Function Set TopologicalSpace Topology

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E H M : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  [TopologicalSpace M] [ChartedSpace H M]

namespace ModelWithCorners

/-! ### The extended charts of the interior -/

/-- The extended chart of the interior at `x` is the extended chart of `M` at `x`. -/
theorem extChartAt_interior_apply (x y : I.interior M) :
    extChartAt 𝓘(𝕜, E) x y = extChartAt I (x : M) y := by
  simp only [extChartAt_coe, comp_apply, modelWithCornersSelf_coe, id_eq, chartAt_interior_apply]

/-- The source of the extended chart of the interior at `x` consists of the interior points in the
source of the extended chart of `M` at `x`. -/
theorem extChartAt_interior_source (x : I.interior M) :
    (extChartAt 𝓘(𝕜, E) x).source = Subtype.val ⁻¹' (extChartAt I (x : M)).source := by
  rw [extChartAt_source, extChartAt_source, chartAt_interior_source]

/-- The target of the extended chart of the interior at `x` consists of the points of the target
of the extended chart of `M` at `x` lying in the interior of the range of `I`. -/
theorem extChartAt_interior_target (x : I.interior M) :
    (extChartAt 𝓘(𝕜, E) x).target = (extChartAt I (x : M)).target ∩ interior (range I) := by
  rw [extChartAt_target, extChartAt_target, chartAt_interior_target, modelWithCornersSelf_coe_symm,
    preimage_id, modelWithCornersSelf_coe, range_id, inter_univ, inter_assoc,
    inter_eq_right.2 interior_subset]

/-- The inverse of the extended chart of the interior at `x` is the inverse of the extended chart
of `M` at `x`, on the target of the former. -/
theorem coe_extChartAt_interior_symm_apply (x : I.interior M) {v : E}
    (hv : v ∈ (extChartAt 𝓘(𝕜, E) x).target) :
    ((extChartAt 𝓘(𝕜, E) x).symm v : M) = (extChartAt I (x : M)).symm v := by
  have hv' : v ∈ (chartAt E x).target := by
    simpa only [extChartAt_target, modelWithCornersSelf_coe_symm, preimage_id,
      modelWithCornersSelf_coe, range_id, inter_univ] using hv
  rw [extChartAt_coe_symm, comp_apply, modelWithCornersSelf_coe_symm, id_eq,
    coe_chartAt_interior_symm_apply I x hv', extChartAt_coe_symm, comp_apply]

/-! ### Maps into the interior -/

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N] {n : WithTop ℕ∞}

variable {I}

/-- **Maps into the interior.** A map into the interior is `C^n` within a set at a point exactly
when it is as a map into `M`: in the extended charts, the two maps have the same expression. -/
@[simp]
theorem contMDiffWithinAt_subtypeVal_comp_interior_iff {f : N → I.interior M} {s : Set N} {x : N} :
    ContMDiffWithinAt J I n (Subtype.val ∘ f) s x ↔ ContMDiffWithinAt J 𝓘(𝕜, E) n f s x := by
  rw [contMDiffWithinAt_iff, contMDiffWithinAt_iff,
    ← IsInducing.subtypeVal.continuousWithinAt_iff]
  refine and_congr_right fun _ ↦ ?_
  have h : extChartAt I ((Subtype.val ∘ f) x) ∘ (Subtype.val ∘ f) ∘ (extChartAt J x).symm =
      extChartAt 𝓘(𝕜, E) (f x) ∘ f ∘ (extChartAt J x).symm :=
    funext fun y ↦ (extChartAt_interior_apply I (f x) (f ((extChartAt J x).symm y))).symm
  rw [h]

/-- A map into the interior is `C^n` at a point exactly when it is as a map into `M`. -/
@[simp]
theorem contMDiffAt_subtypeVal_comp_interior_iff {f : N → I.interior M} {x : N} :
    ContMDiffAt J I n (Subtype.val ∘ f) x ↔ ContMDiffAt J 𝓘(𝕜, E) n f x :=
  contMDiffWithinAt_subtypeVal_comp_interior_iff

/-- A map into the interior is `C^n` on a set exactly when it is as a map into `M`. -/
@[simp]
theorem contMDiffOn_subtypeVal_comp_interior_iff {f : N → I.interior M} {s : Set N} :
    ContMDiffOn J I n (Subtype.val ∘ f) s ↔ ContMDiffOn J 𝓘(𝕜, E) n f s :=
  forall₂_congr fun _ _ ↦ contMDiffWithinAt_subtypeVal_comp_interior_iff

/-- A map into the interior is `C^n` exactly when it is as a map into `M`. -/
@[simp]
theorem contMDiff_subtypeVal_comp_interior_iff {f : N → I.interior M} :
    ContMDiff J I n (Subtype.val ∘ f) ↔ ContMDiff J 𝓘(𝕜, E) n f :=
  forall_congr' fun _ ↦ contMDiffAt_subtypeVal_comp_interior_iff

/-! ### The inclusion as a local diffeomorphism -/

variable (I M)

/-- The interior `I.interior M` of a manifold with corners modelled on a finite-dimensional space,
as an open subset. -/
def interiorOpens : Opens M :=
  ⟨I.interior M, I.isOpen_interior_of_finiteDimensional M⟩

/-- The underlying set of `I.interiorOpens M` is the interior `I.interior M`. -/
@[simp]
theorem coe_interiorOpens : (I.interiorOpens M : Set M) = I.interior M :=
  (rfl)

variable {I M} in
/-- A point lies in `I.interiorOpens M` exactly when it is an interior point. -/
@[simp]
theorem mem_interiorOpens {x : M} : x ∈ I.interiorOpens M ↔ x ∈ I.interior M :=
  Iff.rfl

/-- The interior of a locally compact manifold is locally compact. -/
instance [LocallyCompactSpace M] : LocallyCompactSpace (I.interior M) :=
  (I.isOpen_interior_of_finiteDimensional M).isOpenEmbedding_subtypeVal.locallyCompactSpace

/-- The identity diffeomorphism from the interior, charted by `E`, to the open subset
`I.interiorOpens M` of `M`, charted by the charts of `M` restricted to it. -/
def interiorDiffeomorphOpens (n : WithTop ℕ∞) :
    I.interior M ≃ₘ^n⟮𝓘(𝕜, E), I⟯ I.interiorOpens M where
  toEquiv := Equiv.subtypeEquivRight fun _ ↦ Iff.rfl
  contMDiff_toFun :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff (I.interiorOpens M) _).1
      (contMDiff_subtypeVal_interior I)
  contMDiff_invFun := contMDiff_subtypeVal_comp_interior_iff.1 contMDiff_subtypeVal

variable {I M}

/-- The diffeomorphism to `I.interiorOpens M` does not move points of `M`. -/
@[simp]
theorem coe_interiorDiffeomorphOpens_apply (n : WithTop ℕ∞) (x : I.interior M) :
    (I.interiorDiffeomorphOpens M n x : M) = x :=
  (rfl)

/-- The inverse of the diffeomorphism to `I.interiorOpens M` does not move points of `M`. -/
@[simp]
theorem coe_interiorDiffeomorphOpens_symm_apply (n : WithTop ℕ∞) (x : I.interiorOpens M) :
    ((I.interiorDiffeomorphOpens M n).symm x : M) = x :=
  (rfl)

variable (I M) in
/-- **The inclusion of the interior is a local diffeomorphism**, for every model with corners and
every regularity. -/
theorem isLocalDiffeomorph_subtypeVal_interior (n : WithTop ℕ∞) :
    IsLocalDiffeomorph 𝓘(𝕜, E) I n (Subtype.val : I.interior M → M) := fun x ↦
  IsLocalDiffeomorphAt.comp I M ((I.interiorDiffeomorphOpens M n).isLocalDiffeomorph x)
    (TauCeti.isLocalDiffeomorph_subtype_val (U := I.interiorOpens M) _)

/-- The inclusion of the interior has the identity of `E` as its manifold derivative. -/
theorem hasMFDerivAt_subtypeVal_interior (x : I.interior M) :
    HasMFDerivAt 𝓘(𝕜, E) I Subtype.val x (ContinuousLinearMap.id 𝕜 E) :=
  continuous_subtypeVal.continuousAt.hasMFDerivAt_of_writtenInExtChartAt_eventuallyEq _
    (nhdsWithin_le_nhds (writtenInExtChartAt_subtypeVal_interior_eventuallyEq x))

/-- **The derivative of the inclusion of the interior** is the identity of `E`. -/
@[simp]
theorem mfderiv_subtypeVal_interior (x : I.interior M) :
    mfderiv 𝓘(𝕜, E) I Subtype.val x = ContinuousLinearMap.id 𝕜 E :=
  (hasMFDerivAt_subtypeVal_interior x).mfderiv

/-! ### Manifolds without boundary -/

variable (I M) in
/-- For a manifold `M` without boundary, the inclusion of the interior is a `C^n` diffeomorphism
onto `M`. -/
def interiorDiffeomorph [BoundarylessManifold I M] (n : WithTop ℕ∞) :
    I.interior M ≃ₘ^n⟮𝓘(𝕜, E), I⟯ M :=
  (I.interiorDiffeomorphOpens M n).trans
    (Diffeomorph.ofTop _ (SetLike.coe_injective I.interior_eq_univ))

/-- The diffeomorphism onto a manifold without boundary is the inclusion of the interior. -/
@[simp]
theorem coe_interiorDiffeomorph [BoundarylessManifold I M] (n : WithTop ℕ∞) :
    ⇑(I.interiorDiffeomorph M n) = Subtype.val := by
  rw [ModelWithCorners.interiorDiffeomorph, Diffeomorph.coe_trans, Diffeomorph.coe_ofTop]
  funext x
  exact coe_interiorDiffeomorphOpens_apply n x

/-- The inverse of the diffeomorphism onto a manifold without boundary sends a point to the
interior point over it. -/
@[simp]
theorem coe_interiorDiffeomorph_symm_apply [BoundarylessManifold I M] (n : WithTop ℕ∞) (x : M) :
    ((I.interiorDiffeomorph M n).symm x : M) = x :=
  (congrFun (coe_interiorDiffeomorph (I := I) (M := M) n) _).symm.trans
    ((I.interiorDiffeomorph M n).apply_symm_apply x)

/-- The inverse of the diffeomorphism onto a manifold without boundary sends a point of the
interior, viewed in `M`, back to itself. -/
@[simp]
theorem interiorDiffeomorph_symm_apply_coe [BoundarylessManifold I M] (n : WithTop ℕ∞)
    (x : I.interior M) : (I.interiorDiffeomorph M n).symm (x : M) = x :=
  Subtype.ext (coe_interiorDiffeomorph_symm_apply n (x : M))

end ModelWithCorners
