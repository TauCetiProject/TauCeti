/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Atlas
public import TauCeti.Geometry.Manifold.Orientation.Prod
public import TauCeti.Geometry.Manifold.Orientation.Pullback
public import TauCeti.Geometry.Manifold.Orientation.Sign
public import TauCeti.Geometry.Manifold.Orientation.TopForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Opens
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Restricting an orientation to an open subset

An open subset `U` of a manifold `M`, charted by the restrictions of the charts of `M`, includes
into `M` by a local diffeomorphism (`TauCeti.isLocalDiffeomorph_subtype_val`). So every orientation
of `M` pulls back to an orientation of `U` (`TauCeti.Manifold.Orientation.restrict`), the unique
one for which the inclusion preserves orientation. Its tangent orientation at a point is that of
`M`, read through the canonical identification `TauCeti.Manifold.tangentSpaceOpenEquiv` of the
tangent spaces (`TauCeti.Manifold.Orientation.map_orientationAt_restrict`).

Restriction is compatible with the usual sources of orientations and with maps.

* **Successive restrictions.** For open subsets `U ≤ W`, the inclusion of `U` into `W` preserves
  the orientations restricted from `M`.
* **Restricted maps.** Let `f : U → V` be the restriction of a map `A : M → M'` to open subsets,
  that is `Subtype.val ∘ f = A ∘ Subtype.val`. Then `f` preserves (reverses) the restricted
  orientations at `x` exactly when `A` preserves (reverses) orientation at `x`
  (`TauCeti.Manifold.Orientation.isOrientationPreservingAt_restrict_iff_of_comp_eq`), so it has
  the orientation sign of `A` (`TauCeti.Manifold.Orientation.orientationSign_restrict_of_comp_eq`).
  No open subset needs to be a product or a preimage: any `U` with `A(U) ⊆ V` gives such an `f`.
* **Products.** The inclusion of `U × V` into an open subset of `M × M'` preserves orientation
  from the product of the restricted orientations to the restriction of the product orientation
  (`TauCeti.Manifold.Orientation.isOrientationPreservingAt_prod_restrict_of_comp_eq`).
* **Top forms.** The restriction of the orientation of a nowhere-vanishing top form is the
  orientation of its restriction (`TauCeti.Manifold.Orientation.restrict_ofTopForm`).
* **Oriented atlases.** When the coordinate changes of `M` preserve orientation, so do those of
  the open submanifold `U`, whose charts are the restrictions of the charts of `M`; the
  restriction of the orientation of the atlas of `M` is the orientation of the atlas of `U`
  (`TauCeti.Manifold.Orientation.restrict_isOrientedAtlas_orientation`).

## Main definitions

* `TauCeti.Manifold.Orientation.restrict`: the restriction of an orientation to an open subset.

## Main results

* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_restrict`: the inclusion of the open
  subset preserves orientation from the restriction.
* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_restrict_inclusion`: for open subsets
  `U ≤ W`, the inclusion of `U` into `W` preserves the restricted orientations.
* `TauCeti.Manifold.Orientation.eq_restrict_iff`: this property characterizes the restriction.
* `TauCeti.Manifold.Orientation.restrict_neg`: restriction commutes with taking the opposite
  orientation.
* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_restrict_comp_subtype_val_iff`,
  `TauCeti.Manifold.Orientation.isOrientationPreservingAt_restrict_iff_subtype_val_comp`: a map
  preserves orientation on an open source, or into an open target, exactly as it does on the
  ambient manifolds.
* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_restrict_iff_of_comp_eq`,
  `TauCeti.Manifold.Orientation.isOrientationReversingAt_restrict_iff_of_comp_eq`,
  `TauCeti.Manifold.Orientation.orientationSign_restrict_of_comp_eq`: restricted maps.
* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_prod_restrict_of_comp_eq`: restriction
  commutes with products.
* `TauCeti.Manifold.Orientation.restrict_ofTopForm`: restriction of the orientation of a top form.
* `TauCeti.Manifold.Orientation.restrict_isOrientedAtlas_orientation`: restriction of the
  orientation of an oriented atlas.
* `TauCeti.Manifold.Orientation.map_orientationAt_restrict`: the tangent orientations of the
  restriction.
-/

public section

noncomputable section

open TopologicalSpace TauCeti.Manifold
open scoped Manifold ContDiff

namespace TauCeti.Manifold.Orientation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {ι : Type*} [Fintype ι]
  {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M']
  [ChartedSpace H' M'] [IsManifold I' 1 M']

/-- The restriction of an orientation of `M` to the open subset `U`: its pullback along the
inclusion `U → M`. -/
def restrict (o : Orientation I M ι) (U : Opens M) : Orientation I U ι :=
  o.pullback contMDiff_subtypeVal
    (fun x ↦ (isLocalDiffeomorph_subtype_val (n := 1) x).isInvertible_mfderiv one_ne_zero)
    o.card_eq

/-- The inclusion of an open subset preserves orientation from the restricted orientation. -/
@[simp]
theorem isOrientationPreservingAt_restrict (o : Orientation I M ι) (U : Opens M) (x : U) :
    IsOrientationPreservingAt (o.restrict U) o Subtype.val x :=
  isOrientationPreservingAt_pullback _ _ _ _ x

/-- The tangent orientation of the restriction of `o` to `U` at `x` is the tangent orientation of
`o` at `x`, through the canonical identification of the tangent spaces of `U` and `M`. -/
theorem map_orientationAt_restrict (o : Orientation I M ι) (U : Opens M) (x : U) :
    _root_.Orientation.map ι (tangentSpaceOpenEquiv (I := I) x).toLinearEquiv
      ((o.restrict U).orientationAt x) = o.orientationAt x :=
  map_orientationAt_pullback _ _ _ _ x _ (mfderiv_subtype_val x).symm

/-- For open subsets `U ≤ W`, the inclusion of `U` into `W` preserves the orientations restricted
from `M`. -/
@[simp]
theorem isOrientationPreservingAt_restrict_inclusion (o : Orientation I M ι) {U W : Opens M}
    (h : U ≤ W) (x : U) :
    IsOrientationPreservingAt (o.restrict U) (o.restrict W) (Opens.inclusion h) x :=
  -- The inclusion of `W` into `M` after the inclusion of `U` into `W` is the inclusion of `U`.
  .of_comp (o.isOrientationPreservingAt_restrict W _) (o.isOrientationPreservingAt_restrict U x)
    ((contMDiff_inclusion h).mdifferentiableAt one_ne_zero)

/-- Restricting the opposite orientation gives the opposite of the restriction. -/
@[simp]
theorem restrict_neg (o : Orientation I M ι) (U : Opens M) : (-o).restrict U = -o.restrict U :=
  pullback_neg ..

/-- The restriction is the only orientation of `U` from which the inclusion into `M` preserves
orientation at every point. -/
theorem eq_restrict_iff {o : Orientation I M ι} {U : Opens M} {o' : Orientation I U ι} :
    o' = o.restrict U ↔ ∀ x, IsOrientationPreservingAt o' o Subtype.val x :=
  eq_pullback_iff _ _ _ _

/-! ### Maps on open subsets -/

/-- A map preserves orientation at a point of an open subset `U` of its source, from the
restricted orientation, exactly when it preserves orientation there on all of its source. -/
theorem isOrientationPreservingAt_restrict_comp_subtype_val_iff (o : Orientation I M ι)
    {U : Opens M} (o' : Orientation I' M' ι) (f : M → M') (x : U) :
    IsOrientationPreservingAt (o.restrict U) o' (f ∘ Subtype.val) x ↔
      IsOrientationPreservingAt o o' f x := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp (o.isOrientationPreservingAt_restrict U x)⟩
  obtain ⟨e, he, hmap⟩ := (isOrientationPreservingAt_iff _ _ _ _).mp h
  -- Precompose the derivative of `f ∘ Subtype.val` with the identification of tangent spaces.
  refine (isOrientationPreservingAt_iff _ _ _ _).mpr
    ⟨(tangentSpaceOpenEquiv (I := I) x).symm.trans e, ?_, ?_⟩
  · ext v
    rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply,
      tangentSpaceOpenEquiv_symm_apply]
    exact (congrArg (· v) he).trans (mfderiv_comp_subtype_val_apply (x := x) v)
  · rw [ContinuousLinearEquiv.trans_toLinearEquiv, _root_.Orientation.map_trans,
      ContinuousLinearEquiv.toLinearEquiv_symm, ← _root_.Orientation.map_symm,
      ← map_orientationAt_restrict o U x, Equiv.symm_apply_apply]
    exact hmap

/-- A map into an open subset `V` of a manifold preserves orientation at a point, for the
restricted orientation of `V`, exactly when its composition with the inclusion of `V` does. -/
theorem isOrientationPreservingAt_restrict_iff_subtype_val_comp (o : Orientation I M ι)
    {V : Opens M'} (o' : Orientation I' M' ι) (f : M → V) (x : M) :
    IsOrientationPreservingAt o (o'.restrict V) f x ↔
      IsOrientationPreservingAt o o' (Subtype.val ∘ f) x :=
  ⟨fun h ↦ (o'.isOrientationPreservingAt_restrict V (f x)).comp h, fun h ↦
    (o'.isOrientationPreservingAt_restrict V (f x)).of_comp h
      (mdifferentiableAt_subtype_val_comp_iff.mp
        (mdifferentiableAt_of_isInvertible_mfderiv h.isInvertible_mfderiv))⟩

/-- **Restricted maps preserve the restricted orientations.** Let `f : U → V` be the restriction
of a map `A : M → M'` to open subsets `U` and `V`, that is `Subtype.val ∘ f = A ∘ Subtype.val`.
Then `f` preserves the restricted orientations at `x` exactly when `A` preserves orientation at
`x`. -/
theorem isOrientationPreservingAt_restrict_iff_of_comp_eq {U : Opens M} {V : Opens M'}
    {f : U → V} {A : M → M'} (hcomp : Subtype.val ∘ f = A ∘ Subtype.val)
    (o : Orientation I M ι) (o' : Orientation I' M' ι) (x : U) :
    IsOrientationPreservingAt (o.restrict U) (o'.restrict V) f x ↔
      IsOrientationPreservingAt o o' A x := by
  rw [isOrientationPreservingAt_restrict_iff_subtype_val_comp, hcomp,
    isOrientationPreservingAt_restrict_comp_subtype_val_iff]

/-- **Restricted maps reverse the restricted orientations.** Let `f : U → V` be the restriction
of a map `A : M → M'` to open subsets `U` and `V`. Then `f` reverses the restricted orientations at
`x` exactly when `A` reverses orientation at `x`. -/
theorem isOrientationReversingAt_restrict_iff_of_comp_eq {U : Opens M} {V : Opens M'}
    {f : U → V} {A : M → M'} (hcomp : Subtype.val ∘ f = A ∘ Subtype.val)
    (o : Orientation I M ι) (o' : Orientation I' M' ι) (x : U) :
    IsOrientationReversingAt (o.restrict U) (o'.restrict V) f x ↔
      IsOrientationReversingAt o o' A x := by
  rw [← isOrientationPreservingAt_neg_right, ← restrict_neg,
    isOrientationPreservingAt_restrict_iff_of_comp_eq hcomp, isOrientationPreservingAt_neg_right]

/-- A restriction `f : U → V` of a map `A : M → M'` to open subsets has, for the restricted
orientations, the orientation sign of `A` at every point. -/
theorem orientationSign_restrict_of_comp_eq {U : Opens M} {V : Opens M'} {f : U → V}
    {A : M → M'} (hcomp : Subtype.val ∘ f = A ∘ Subtype.val) (o : Orientation I M ι)
    (o' : Orientation I' M' ι) (x : U) :
    orientationSign (o.restrict U) (o'.restrict V) f x = orientationSign o o' A x := by
  have hp := isOrientationPreservingAt_restrict_iff_of_comp_eq hcomp o o' x
  have hr := isOrientationReversingAt_restrict_iff_of_comp_eq hcomp o o' x
  -- Both signs lie in `{-1, 0, 1}`, and the values `1` and `-1` are attained simultaneously.
  have h₁ := abs_le.mp (abs_orientationSign_le_one (o := o.restrict U) (o' := o'.restrict V)
    (f := f) (x := x))
  have h₂ := abs_le.mp (abs_orientationSign_le_one (o := o) (o' := o') (f := A) (x := (x : M)))
  have e₁ : orientationSign (o.restrict U) (o'.restrict V) f x = 1 ↔
      orientationSign o o' A x = 1 := by
    rw [orientationSign_eq_one_iff, orientationSign_eq_one_iff, hp]
  have e₂ : orientationSign (o.restrict U) (o'.restrict V) f x = -1 ↔
      orientationSign o o' A x = -1 := by
    rw [orientationSign_eq_neg_one_iff, orientationSign_eq_neg_one_iff, hr]
  omega

/-- **Restriction commutes with products.** Let `U` and `V` be open subsets of `M` and `M'`, and let
`g : U × V → W` be the inclusion of `U × V` into an open subset `W` of `M × M'`, that is
`Subtype.val ∘ g = Prod.map Subtype.val Subtype.val`. Then `g` preserves orientation from the
product of the restricted orientations to the restriction of the product orientation. -/
theorem isOrientationPreservingAt_prod_restrict_of_comp_eq {m n : ℕ} {U : Opens M}
    {V : Opens M'} {W : Opens (M × M')} {g : U × V → W}
    (hg : Subtype.val ∘ g = Prod.map Subtype.val Subtype.val) (o : Orientation I M (Fin m))
    (o' : Orientation I' M' (Fin n)) (z : U × V) :
    IsOrientationPreservingAt ((o.restrict U).prod (o'.restrict V)) ((o.prod o').restrict W) g
      z := by
  rw [isOrientationPreservingAt_restrict_iff_subtype_val_comp, hg]
  exact (o.isOrientationPreservingAt_restrict U z.1).prodMap
    (o'.isOrientationPreservingAt_restrict V z.2)

/-! ### Orientations of top forms and of oriented atlases -/

/-- The restriction to an open subset `U` of the orientation of a nowhere-vanishing top form `φ`
is the orientation of the restriction of `φ` to `U`. -/
theorem restrict_ofTopForm {k : ℕ} (hk : Module.finrank ℝ E = k) (φ : RoughForm I M ℝ k)
    (hφ : IsSmoothForm I 0 φ) (h0 : ∀ x, φ x ≠ 0) (U : Opens M) :
    (ofTopForm hk φ hφ h0).restrict U =
      ofTopForm hk (mpullback I I (Subtype.val : U → M) φ) (hφ.mpullback contMDiff_subtypeVal)
        (fun x ↦ by rw [mpullback_subtype_val_apply]; exact h0 x) :=
  (eq_restrict_iff.mpr fun _ ↦
    isOrientationPreservingAt_ofTopForm_of_mpullback_eq_smul hk hk _ _ _ _ one_pos
      (one_smul ℝ _).symm).symm

/-- **Oriented atlases of open subsets.** If the coordinate changes of `M` preserve orientation,
so do those of an open subset `U`, whose charts are the restrictions of the charts of `M`. For
every model orientation, the restriction to `U` of the orientation of the atlas of `M` is then the
orientation of the atlas of `U`. -/
theorem restrict_isOrientedAtlas_orientation {n : ℕ∞ω} [NeZero n] [IsManifold I n M]
    [HasGroupoid M (orientationPreservingGroupoid I)] (U : Opens M)
    (model : _root_.Orientation ℝ E ι) (hι : Fintype.card ι = Module.finrank ℝ E) :
    ((isOrientedAtlas_atlas I n M).orientation model hι).restrict U =
      (isOrientedAtlas_atlas I n U).orientation model hι := by
  refine (eq_restrict_iff.mpr fun x ↦ (isOrientationPreservingAt_iff _ _ _ _).mpr ?_).symm
  refine ⟨tangentSpaceOpenEquiv (I := I) x, (mfderiv_subtype_val x).symm, ?_⟩
  -- In the preferred charts both orientations read as the model orientation, and the tangent
  -- spaces of `U` and `M` are identified by the identity of `E`.
  rw [IsOrientedAtlas.orientationAt_orientation _ _ _ (chart_mem_atlas H x),
    IsOrientedAtlas.orientationAt_orientation _ _ _ (chart_mem_atlas H (x : M))]
  have hrefl : (tangentSpaceOpenEquiv (I := I) x).toLinearEquiv = LinearEquiv.refl ℝ E :=
    LinearEquiv.ext (tangentSpaceOpenEquiv_apply x)
  rw [hrefl]
  exact Equiv.ext_iff.mp (_root_.Orientation.map_refl (R := ℝ) (M := E) ι) model

end TauCeti.Manifold.Orientation
