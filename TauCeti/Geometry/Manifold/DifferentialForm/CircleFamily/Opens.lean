/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.CircleFamily.Torus
public import TauCeti.Geometry.Manifold.DifferentialForm.Opens
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Time forms on open subsets of families of tori

An open subset `U` of a family of tori `TauCeti.TorusFamily p` is a manifold with the charts
restricted from the family, and the time forms `η_i` restrict to `U` by pullback along the
inclusion. Let `A` be a base change `TauCeti.TorusFamily.comap p f` or a fibrewise rescaling
`TauCeti.TorusFamily.rescale p IB q ∞`, and `F : U → V` its restriction to open subsets, that is
`Subtype.val ∘ F = A ∘ Subtype.val`, which exists for every open `U ⊆ A⁻¹(V)`. Then `F` pulls the
restricted time forms back as `A` pulls back the time forms
(`TauCeti.mpullback_mpullback_subtype_val_of_comp_eq`,
`TauCeti.SmoothForm.mpullback_mpullback_subtype_val_of_comp_eq`). No open subset needs to be a
product of an open subset of the base and an open subset of the fibre. The corresponding results
for circles and tori are in `TauCeti.Geometry.Manifold.DifferentialForm.Torus.Opens`.

## Main results

* `TauCeti.TorusFamily.mpullback_mpullback_subtype_val_timeForm_of_comp_eq_comap`,
  `TauCeti.TorusFamily.mpullback_mpullback_subtype_val_timeForm_of_comp_eq_rescale`: restricted
  base changes and fibrewise rescalings of families of tori.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 14 (restriction of forms to open submanifolds).
-/

public section

noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

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
      mpullback _ _ Subtype.val (timeForm (fun i ↦ p i ∘ f) IB' i (hp.comp hf)).val :=
  SmoothForm.mpullback_mpullback_subtype_val_of_comp_eq hF
    (mpullback_comap_timeForm p IB f i hp hf)

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
  rw [mpullback_mpullback_subtype_val_of_comp_eq hF,
    ← SmoothForm.coe_mpullback _ (rescale p IB q ∞).contMDiff,
    mpullback_rescale_timeForm p IB q i hp hq]
  funext z
  rw [mpullback_subtype_val_apply, mpullback_subtype_val_apply]
  -- The tangent spaces of `U` and of the family at `z` are the same model space.
  rfl

end TorusFamily

end TauCeti
