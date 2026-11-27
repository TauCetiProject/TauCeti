/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.CircleFamily.Torus
public import TauCeti.Geometry.Manifold.Orientation.OpenSubset
public import TauCeti.Geometry.Manifold.Orientation.Torus

/-!
# Time forms and orientations on open subsets of circles, tori and circle families

An open subset `U` of the circle `AddCircle p`, of a torus `∀ i, AddCircle (p i)` or of a family of
tori `TauCeti.TorusFamily p` is a manifold with the charts restricted from the ambient manifold.
The time forms restrict to `U` by pullback along the inclusion, and the orientations by
`TauCeti.Manifold.Orientation.restrict`. This file shows that these restrictions keep the laws of
the ambient constructions, for every open subset, including those that are not products of open
subsets of the factors.

* **The oriented atlas.** The coordinate changes of the circle are translations, so the atlas of
  `U`, made of the restricted local real lifts, is oriented, and its orientation is the restriction
  of the positive orientation of the circle
  (`AddCircle.restrict_orientation_eq_isOrientedAtlas_orientation`).
* **Restricted maps.** Let `A` be one of the maps between these manifolds and `f : U → V` its
  restriction to open subsets, `Subtype.val ∘ f = A ∘ Subtype.val`, which exists for every open
  `U ⊆ A⁻¹(V)`. Then `f` pulls the restricted forms back as `A` pulls back the forms
  (`TauCeti.mpullback_mpullback_subtype_val_of_comp_eq`), and preserves or reverses the restricted
  orientations as `A` does
  (`TauCeti.Manifold.Orientation.isOrientationPreservingAt_restrict_iff_of_comp_eq`). This is
  recorded for the rescalings of circles and tori, the reindexings of tori with their permutation
  sign, the coordinate-fibre embeddings of tori, restricted to the open preimage of an open subset
  of the torus, and the base changes and fibrewise rescalings of families of tori.

Successive restrictions to open subsets `U ≤ W` are compatible
(`TauCeti.mpullback_inclusion_mpullback_subtype_val`,
`TauCeti.Manifold.Orientation.isOrientationPreservingAt_restrict_inclusion`), and restriction
commutes with products of orientations
(`TauCeti.Manifold.Orientation.isOrientationPreservingAt_prod_restrict_of_comp_eq`).

## Main results

* `AddCircle.restrict_orientation_eq_isOrientedAtlas_orientation`: the restricted orientation of
  the circle is the orientation of the oriented atlas of the open subset.
* `AddCircle.mpullback_mpullback_subtype_val_timeForm_of_comp_eq`,
  `AddCircle.isOrientationPreservingAt_restrict_of_comp_eq`: restricted rescalings of circles.
* `TauCeti.mpullback_mpullback_subtype_val_torusTimeForm_of_comp_eq_reindex`,
  `TauCeti.orientationSign_restrict_torusOrientation_of_comp_eq_reindex`: restricted reindexings
  of tori.
* `TauCeti.mpullback_mpullback_subtype_val_torusTimeForm_of_comp_eq_piMap`,
  `TauCeti.isOrientationPreservingAt_restrict_torusOrientation_of_comp_eq_piMap`: restricted
  rescalings of tori.
* `TauCeti.mpullback_mpullback_subtype_val_torusTimeForm_self_of_comp_eq_update`,
  `TauCeti.mpullback_mpullback_subtype_val_torusTimeForm_of_ne_of_comp_eq_update`: restricted
  coordinate-fibre embeddings.
* `TauCeti.TorusFamily.mpullback_mpullback_subtype_val_timeForm_of_comp_eq_comap`,
  `TauCeti.TorusFamily.mpullback_mpullback_subtype_val_timeForm_of_comp_eq_rescale`: restricted
  base changes and fibrewise rescalings of families of tori.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapters 14 and 15 (restriction of forms and orientations to
  open submanifolds).
-/

public section

noncomputable section

open Set TopologicalSpace TauCeti TauCeti.Manifold.Orientation
open scoped Manifold ContDiff

namespace AddCircle

variable {p q : ℝ} [Fact (0 < p)] [Fact (0 < q)]

variable (p) in
/-- **The oriented atlas of an open subset of a circle.** The charts of an open subset `U` of
`AddCircle p` are the restricted local real lifts, whose coordinate changes are translations. The
orientation of this oriented atlas, in which `1` is positive, is the restriction to `U` of the
positive orientation of the circle. -/
theorem restrict_orientation_eq_isOrientedAtlas_orientation {n : ℕ∞ω} [NeZero n]
    (U : Opens (AddCircle p)) :
    (AddCircle.orientation p).restrict U =
      (isOrientedAtlas_atlas 𝓘(ℝ) n U).orientation
        (Module.Basis.singleton (Fin 1) ℝ).orientation (by simp) := by
  rw [orientation_eq_isOrientedAtlas_orientation p (n := n), restrict_isOrientedAtlas_orientation]

/-- A restriction `f : U → V` of the rescaling `AddCircle p ≃ AddCircle q` to open subsets pulls
the restriction of the time form `dt_q` back to `p⁻¹ * q` times the restriction of `dt_p`. -/
theorem mpullback_mpullback_subtype_val_timeForm_of_comp_eq {n : ℕ∞ω} {U : Opens (AddCircle p)}
    {V : Opens (AddCircle q)} {f : U → V}
    (hf : Subtype.val ∘ f = diffeomorphAddCircle p q n ∘ Subtype.val) :
    mpullback 𝓘(ℝ) 𝓘(ℝ) f (mpullback 𝓘(ℝ) 𝓘(ℝ) Subtype.val (timeForm q).val) =
      (p⁻¹ * q) • mpullback 𝓘(ℝ) 𝓘(ℝ) Subtype.val (timeForm p).val := by
  rw [mpullback_mpullback_subtype_val_of_comp_eq hf, mpullback_diffeomorphAddCircle_timeForm,
    mpullback_smul]

/-- A restriction `f : U → V` of the rescaling `AddCircle p ≃ AddCircle q` to open subsets
preserves the restricted positive orientations. -/
theorem isOrientationPreservingAt_restrict_of_comp_eq {n : ℕ∞ω} {U : Opens (AddCircle p)}
    {V : Opens (AddCircle q)} {f : U → V}
    (hf : Subtype.val ∘ f = diffeomorphAddCircle p q n ∘ Subtype.val) (x : U) :
    IsOrientationPreservingAt ((AddCircle.orientation p).restrict U)
      ((AddCircle.orientation q).restrict V) f x :=
  (isOrientationPreservingAt_restrict_iff_of_comp_eq hf _ _ x).mpr
    (isOrientationPreservingAt_diffeomorphAddCircle p q n x)

end AddCircle

namespace TauCeti

/-! ### Tori -/

section Torus

variable {ι : Type*} [Fintype ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)]

/-- A restriction `f : U → V` of the reindexing `x ↦ (j ↦ x (e j))` of tori to open subsets pulls
the restriction of the `j`-th coordinate time form back to the restriction of the `e j`-th one. -/
theorem mpullback_mpullback_subtype_val_torusTimeForm_of_comp_eq_reindex {ι' : Type*} [Fintype ι']
    (e : ι' → ι) {U : Opens (∀ i, AddCircle (p i))} {V : Opens (∀ l, AddCircle (p (e l)))}
    {f : U → V}
    (hf : Subtype.val ∘ f = (fun (x : ∀ i, AddCircle (p i)) (l : ι') ↦ x (e l)) ∘ Subtype.val)
    (j : ι') :
    mpullback (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ModelWithCorners.pi fun _ : ι' ↦ 𝓘(ℝ)) f
        (mpullback _ _ Subtype.val (torusTimeForm (fun l ↦ p (e l)) j).val) =
      mpullback _ _ Subtype.val (torusTimeForm p (e j)).val := by
  rw [mpullback_mpullback_subtype_val_of_comp_eq hf]
  exact congrArg _ ((SmoothForm.coe_mpullback _ _ _).symm.trans
    (congrArg Subtype.val (mpullback_reindex_torusTimeForm p e j)))

/-- **The permutation sign law on open subsets.** A restriction `f : U → V` of the reordering
`x ↦ (j ↦ x (σ j))` of the factors of a torus to open subsets has orientation sign `sign σ`, for
the restricted torus orientations, at every point. -/
theorem orientationSign_restrict_torusOrientation_of_comp_eq_reindex {n : ℕ} (p : Fin n → ℝ)
    [∀ i, Fact (0 < p i)] (σ : Equiv.Perm (Fin n)) {U : Opens (∀ i, AddCircle (p i))}
    {V : Opens (∀ j, AddCircle (p (σ j)))} {f : U → V}
    (hf : Subtype.val ∘ f = (fun (x : ∀ i, AddCircle (p i)) (j : Fin n) ↦ x (σ j)) ∘ Subtype.val)
    (x : U) :
    orientationSign ((torusOrientation p).restrict U)
      ((torusOrientation fun j ↦ p (σ j)).restrict V) f x = Equiv.Perm.sign σ := by
  rw [orientationSign_restrict_of_comp_eq hf, orientationSign_torusOrientation_reindex]

/-- A restriction `f : U → V` of the diagonal rescaling of the periods of a torus, by the
rescalings `AddCircle (p j) ≃ AddCircle (q j)`, pulls the restriction of the coordinate time form
`dt_i` of the periods `q` back to `(p i)⁻¹ * q i` times the restriction of that of the periods
`p`. -/
theorem mpullback_mpullback_subtype_val_torusTimeForm_of_comp_eq_piMap (q : ι → ℝ)
    [∀ i, Fact (0 < q i)]
    {U : Opens (∀ i, AddCircle (p i))} {V : Opens (∀ i, AddCircle (q i))} {f : U → V}
    (hf : Subtype.val ∘ f =
      (Pi.map fun j ↦ AddCircle.diffeomorphAddCircle (p j) (q j) ∞) ∘ Subtype.val) (i : ι) :
    mpullback (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) f
        (mpullback _ _ Subtype.val (torusTimeForm q i).val) =
      ((p i)⁻¹ * q i) • mpullback _ _ Subtype.val (torusTimeForm p i).val := by
  rw [mpullback_mpullback_subtype_val_of_comp_eq hf, ← mpullback_smul, ← SetLike.val_smul]
  exact congrArg _ ((SmoothForm.coe_mpullback _ _ _).symm.trans
    (congrArg Subtype.val (mpullback_piMap_diffeomorphAddCircle_torusTimeForm p q i)))

/-- A restriction `f : U → V` of the diagonal rescaling of the periods of a torus to open subsets
preserves the restricted torus orientations. -/
theorem isOrientationPreservingAt_restrict_torusOrientation_of_comp_eq_piMap {n : ℕ}
    (p q : Fin n → ℝ) [∀ i, Fact (0 < p i)] [∀ i, Fact (0 < q i)]
    {U : Opens (∀ i, AddCircle (p i))} {V : Opens (∀ i, AddCircle (q i))} {f : U → V}
    (hf : Subtype.val ∘ f =
      (Pi.map fun j ↦ AddCircle.diffeomorphAddCircle (p j) (q j) ∞) ∘ Subtype.val) (x : U) :
    IsOrientationPreservingAt ((torusOrientation p).restrict U) ((torusOrientation q).restrict V)
      f x :=
  (isOrientationPreservingAt_restrict_iff_of_comp_eq hf _ _ x).mpr
    (isOrientationPreservingAt_piMap_diffeomorphAddCircle p q x)

/-- A restriction `f : U → V` of the coordinate-fibre embedding `update x i` of the `i`-th circle
into the torus to open subsets, for instance to the open preimage `U` of `V`, pulls the
restriction of the coordinate time form `dt_i` back to the restriction of the time form of the
`i`-th circle. -/
theorem mpullback_mpullback_subtype_val_torusTimeForm_self_of_comp_eq_update [DecidableEq ι]
    (x : ∀ i, AddCircle (p i)) (i : ι) {U : Opens (AddCircle (p i))}
    {V : Opens (∀ i, AddCircle (p i))} {f : U → V}
    (hf : Subtype.val ∘ f = Function.update x i ∘ Subtype.val) :
    mpullback 𝓘(ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) f
        (mpullback _ _ Subtype.val (torusTimeForm p i).val) =
      mpullback _ _ Subtype.val (AddCircle.timeForm (p i)).val := by
  rw [mpullback_mpullback_subtype_val_of_comp_eq hf]
  exact congrArg _ ((SmoothForm.coe_mpullback _ _ _).symm.trans
    (congrArg Subtype.val (mpullback_update_torusTimeForm_self p x i)))

/-- A restriction `f : U → V` of the coordinate-fibre embedding `update x i` of the `i`-th circle
into the torus to open subsets pulls the restriction of every other coordinate time form `dt_j`
back to zero. -/
theorem mpullback_mpullback_subtype_val_torusTimeForm_of_ne_of_comp_eq_update [DecidableEq ι]
    (x : ∀ i, AddCircle (p i)) {i j : ι} (h : j ≠ i) {U : Opens (AddCircle (p i))}
    {V : Opens (∀ i, AddCircle (p i))} {f : U → V}
    (hf : Subtype.val ∘ f = Function.update x i ∘ Subtype.val) :
    mpullback 𝓘(ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) f
        (mpullback _ _ Subtype.val (torusTimeForm p j).val) = 0 := by
  rw [mpullback_mpullback_subtype_val_of_comp_eq hf]
  refine (congrArg _ ((SmoothForm.coe_mpullback _ _ _).symm.trans
    (congrArg Subtype.val (mpullback_update_torusTimeForm_of_ne p x h)))).trans ?_
  funext y
  rw [mpullback_subtype_val_apply]
  rfl

end Torus

/-! ### Families of tori -/

namespace TorusFamily

variable {B ι : Type*} [Fintype ι] (p : ι → B → PositivePeriod) {EB HB : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB] (IB : ModelWithCorners ℝ EB HB)
  [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]

/-- A restriction `F : U → V` of the base change of a family of tori along a smooth map `f` to open
subsets pulls the restriction of the time form `η_i` of the family of `p` back to the restriction
of the time form `η_i` of the family of the periods `p i ∘ f`. -/
theorem mpullback_mpullback_subtype_val_timeForm_of_comp_eq_comap {B' : Type*} (f : B' → B)
    {EB' HB' : Type*} [NormedAddCommGroup EB'] [NormedSpace ℝ EB'] [TopologicalSpace HB']
    {IB' : ModelWithCorners ℝ EB' HB'} [TopologicalSpace B'] [ChartedSpace HB' B']
    [IsManifold IB' ∞ B'] (hf : ContMDiff IB' IB ∞ f) (i : ι) (hp : ContMDiff IB 𝓘(ℝ) ∞ (p i))
    {U : Opens (TorusFamily fun i ↦ p i ∘ f)} {V : Opens (TorusFamily p)} {F : U → V}
    (hF : Subtype.val ∘ F = comap p f ∘ Subtype.val) :
    mpullback (IB'.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)))
        (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) F
        (mpullback _ _ Subtype.val (timeForm p IB i hp).val) =
      mpullback _ _ Subtype.val (timeForm (fun i ↦ p i ∘ f) IB' i (hp.comp hf)).val := by
  rw [mpullback_mpullback_subtype_val_of_comp_eq hF]
  exact congrArg _ ((SmoothForm.coe_mpullback _ _ _).symm.trans
    (congrArg Subtype.val (mpullback_comap_timeForm p IB f i hp hf)))

/-- A restriction `F : U → V` of the fibrewise rescaling of a family of tori from the periods `p`
to the periods `q` to open subsets pulls the restriction of the time form `η_i` of `q` back to
`q i / p i` times the restriction of the time form `η_i` of `p`. -/
theorem mpullback_mpullback_subtype_val_timeForm_of_comp_eq_rescale (q : ι → B → PositivePeriod)
    (i : ι)
    (hp : ContMDiff IB 𝓘(ℝ) ∞ (p i)) (hq : ContMDiff IB 𝓘(ℝ) ∞ (q i))
    {U : Opens (TorusFamily p)} {V : Opens (TorusFamily q)} {F : U → V}
    (hF : Subtype.val ∘ F = rescale p IB q ∞ ∘ Subtype.val) :
    mpullback (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)))
        (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) F
        (mpullback _ _ Subtype.val (timeForm q IB i hq).val) =
      fun z : U ↦ ((q i (z : TorusFamily p).base : ℝ) / p i (z : TorusFamily p).base) •
        mpullback _ _ Subtype.val (timeForm p IB i hp).val z := by
  rw [mpullback_mpullback_subtype_val_of_comp_eq hF]
  refine (congrArg _ ((SmoothForm.coe_mpullback _ _ _).symm.trans
    (mpullback_rescale_timeForm p IB q i hp hq))).trans ?_
  funext z
  rw [mpullback_subtype_val_apply, mpullback_subtype_val_apply]
  -- The tangent spaces of `U` and of the family at `z` are the same model space.
  rfl

end TorusFamily

end TauCeti
