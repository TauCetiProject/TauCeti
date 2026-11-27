/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Opens
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Torus

/-!
# Time forms on open subsets of circles and tori

An open subset `U` of the circle `AddCircle p` or of a torus `∀ i, AddCircle (p i)` is a manifold
with the charts restricted from the ambient manifold, and the time forms restrict to `U` by
pullback along the inclusion. Let `A` be one of the maps between these manifolds and `f : U → V`
its restriction to open subsets, `Subtype.val ∘ f = A ∘ Subtype.val`, which exists for every open
`U ⊆ A⁻¹(V)`. Then `f` pulls the restricted time forms back as `A` pulls back the time forms
(`TauCeti.mpullback_mpullback_subtype_val_of_comp_eq`,
`TauCeti.SmoothForm.mpullback_mpullback_subtype_val_of_comp_eq`). This is recorded for the
rescalings of circles and tori, the reindexings of tori, and the coordinate-fibre embeddings of
tori, for every open subset, including those that are not products of open subsets of the factors.
The corresponding orientation laws are in `TauCeti.Geometry.Manifold.Orientation.Torus.Opens`, and
the families of tori are treated in `TauCeti.Geometry.Manifold.DifferentialForm.CircleFamily.Opens`.

Successive restrictions to open subsets `U ≤ W` are compatible
(`TauCeti.mpullback_inclusion_mpullback_subtype_val`).

## Main results

* `AddCircle.mpullback_mpullback_subtype_val_timeForm_of_comp_eq_diffeomorphAddCircle`:
  restricted rescalings of circles.
* `TauCeti.mpullback_mpullback_subtype_val_torusTimeForm_of_comp_eq_reindex`: restricted
  reindexings of tori.
* `TauCeti.mpullback_mpullback_subtype_val_torusTimeForm_of_comp_eq_piMap`: restricted rescalings
  of tori.
* `TauCeti.mpullback_mpullback_subtype_val_torusTimeForm_self_of_comp_eq_update`,
  `TauCeti.mpullback_mpullback_subtype_val_torusTimeForm_of_ne_of_comp_eq_update`: restricted
  coordinate-fibre embeddings.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 14 (restriction of forms to open submanifolds).
-/

public section

noncomputable section

open TopologicalSpace TauCeti
open scoped Manifold ContDiff

namespace AddCircle

variable {p q : ℝ} [Fact (0 < p)] [Fact (0 < q)]

/-- A restriction `f : U → V` of the rescaling `AddCircle p ≃ AddCircle q` to open subsets pulls
the restriction of the time form `dt_q` back to `p⁻¹ * q` times the restriction of `dt_p`. -/
theorem mpullback_mpullback_subtype_val_timeForm_of_comp_eq_diffeomorphAddCircle {n : ℕ∞ω}
    {U : Opens (AddCircle p)} {V : Opens (AddCircle q)} {f : U → V}
    (hf : Subtype.val ∘ f = diffeomorphAddCircle p q n ∘ Subtype.val) :
    mpullback 𝓘(ℝ) 𝓘(ℝ) f (mpullback 𝓘(ℝ) 𝓘(ℝ) Subtype.val (timeForm q).val) =
      (p⁻¹ * q) • mpullback 𝓘(ℝ) 𝓘(ℝ) Subtype.val (timeForm p).val := by
  rw [mpullback_mpullback_subtype_val_of_comp_eq hf, mpullback_diffeomorphAddCircle_timeForm,
    mpullback_smul]

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
      mpullback _ _ Subtype.val (torusTimeForm p (e j)).val :=
  SmoothForm.mpullback_mpullback_subtype_val_of_comp_eq hf (mpullback_reindex_torusTimeForm p e j)

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
  rw [SmoothForm.mpullback_mpullback_subtype_val_of_comp_eq hf
    (mpullback_piMap_diffeomorphAddCircle_torusTimeForm p q i), SetLike.val_smul, mpullback_smul]

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
      mpullback _ _ Subtype.val (AddCircle.timeForm (p i)).val :=
  SmoothForm.mpullback_mpullback_subtype_val_of_comp_eq hf
    (mpullback_update_torusTimeForm_self p x i)

/-- A restriction `f : U → V` of the coordinate-fibre embedding `update x i` of the `i`-th circle
into the torus to open subsets pulls the restriction of every other coordinate time form `dt_j`
back to zero. -/
theorem mpullback_mpullback_subtype_val_torusTimeForm_of_ne_of_comp_eq_update [DecidableEq ι]
    (x : ∀ i, AddCircle (p i)) {i j : ι} (h : j ≠ i) {U : Opens (AddCircle (p i))}
    {V : Opens (∀ i, AddCircle (p i))} {f : U → V}
    (hf : Subtype.val ∘ f = Function.update x i ∘ Subtype.val) :
    mpullback 𝓘(ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) f
        (mpullback _ _ Subtype.val (torusTimeForm p j).val) = 0 := by
  rw [SmoothForm.mpullback_mpullback_subtype_val_of_comp_eq hf
    (mpullback_update_torusTimeForm_of_ne p x h), ZeroMemClass.coe_zero, mpullback_zero]

end Torus

end TauCeti
