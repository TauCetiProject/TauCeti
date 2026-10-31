/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Retraction
public import TauCeti.Topology.Homotopy.Extension.NDRPair

/-!
# Full subcomplexes are NDR pairs

Let `s` be a set of vertices of an abstract simplicial complex `K`. The polyhedron of the full
subcomplex spanned by `s` is the set of points of the weak realization whose barycentric support
lies in `s`. This file shows that it is an NDR pair in the realization, and hence has the
homotopy extension property.

The control function is `openStarControl K s`, one minus the barycentric mass `∑ᶠ v ∈ s, x v`
on `s`. It vanishes exactly on the polyhedron of the full subcomplex, and it is less than one
exactly on the open star of `s`. Feeding it, together with the straight-line deformation
`AbstractSimplicialComplex.openStarDeformation` of the open star, to
`TauCeti.NDRPair.ofHomotopyRel` gives the NDR data. No finiteness or local finiteness of `K` is
assumed.

## Main definitions

* `AbstractSimplicialComplex.openStarControl`: one minus the barycentric mass on `s`.
* `AbstractSimplicialComplex.fullSubcomplexNDRPair`: NDR data for the polyhedron of the full
  subcomplex spanned by `s`.

## Main results

* `AbstractSimplicialComplex.hasHomotopyExtensionProperty_setOf_support_subset`: the polyhedron
  of a full subcomplex has the homotopy extension property in the realization.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 3 (full subcomplexes and simplicial neighbourhoods).
* N. E. Steenrod, *A convenient category of topological spaces*, Michigan Math. J. 14 (1967),
  133–152 (NDR pairs).
-/

public section

noncomputable section

open Set unitInterval

namespace AbstractSimplicialComplex

variable {ι : Type*} (K : AbstractSimplicialComplex ι) (s : Set ι)

/-- The mass on `s` of finitely supported coordinates is the sum over the vertices in `s` of any
finite set containing their support. -/
private theorem mass_eq_sum_filter_of_support_subset [DecidablePred (· ∈ s)] {x : ι →₀ ℝ}
    {t : Finset ι} (ht : x.support ⊆ t) : ∑ᶠ v ∈ s, x v = ∑ v ∈ t with v ∈ s, x v := by
  refine finsum_mem_eq_sum_of_inter_support_eq _ (Set.ext fun v => ?_)
  simp only [mem_inter_iff, Function.mem_support, Finset.coe_filter, mem_ofPred_eq]
  exact ⟨fun h => ⟨⟨ht (Finsupp.mem_support_iff.2 h.2), h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩

private theorem mass_eq_sum_filter [DecidablePred (· ∈ s)] (x : Realization K) :
    ∑ᶠ v ∈ s, x.1 v = ∑ v ∈ x.1.support with v ∈ s, x.1 v :=
  mass_eq_sum_filter_of_support_subset s subset_rfl

/-- The barycentric mass on `s` and the mass off `s` add up to one. -/
private theorem mass_add_sum_filter_not [DecidablePred (· ∈ s)] (x : Realization K) :
    ∑ᶠ v ∈ s, x.1 v + ∑ v ∈ x.1.support with v ∉ s, x.1 v = 1 := by
  rw [mass_eq_sum_filter, Finset.sum_filter_add_sum_filter_not, ← Realization.sum_eq_one K x,
    Finsupp.sum]

private theorem mass_nonneg (x : Realization K) : 0 ≤ ∑ᶠ v ∈ s, x.1 v := by
  classical
  rw [mass_eq_sum_filter]
  exact Finset.sum_nonneg fun v _ => Realization.nonneg K x v

private theorem mass_le_one (x : Realization K) : ∑ᶠ v ∈ s, x.1 v ≤ 1 := by
  classical
  have := mass_add_sum_filter_not K s x
  linarith [Finset.sum_nonneg fun v (_ : v ∈ x.1.support.filter (· ∉ s)) =>
    Realization.nonneg K x v]

private theorem one_sub_mass_mem (x : Realization K) : 1 - ∑ᶠ v ∈ s, x.1 v ∈ unitInterval :=
  ⟨sub_nonneg.2 (mass_le_one K s x), sub_le_self _ (mass_nonneg K s x)⟩

/-- The barycentric mass on `s` is continuous for the weak topology: on each closed simplex it
is a finite sum of coordinates. -/
private theorem continuous_mass : Continuous fun x : Realization K => ∑ᶠ v ∈ s, x.1 v := by
  classical
  refine continuous_iff_faceInclusion.2 fun τ => ?_
  have hcoord : Continuous fun y : StandardSimplex τ.1 => (y.1 : ι → ℝ) := continuous_induced_dom
  refine (continuous_finsetSum (τ.1.filter (· ∈ s)) fun v _ =>
    (continuous_apply v).comp hcoord).congr fun y => ?_
  simp only [Function.comp_apply, faceInclusion_val]
  exact (mass_eq_sum_filter_of_support_subset s (StandardSimplex.support_subset y)).symm

/-- The control function of the open star of `s`: one minus the barycentric mass on `s`. It
vanishes exactly on the polyhedron of the full subcomplex spanned by `s`, and is less than one
exactly on the open star of `s`. -/
def openStarControl : C(Realization K, I) where
  toFun x := ⟨1 - ∑ᶠ v ∈ s, x.1 v, one_sub_mass_mem K s x⟩
  continuous_toFun := (continuous_const.sub (continuous_mass K s)).subtype_mk _

@[simp]
theorem coe_openStarControl_apply (x : Realization K) :
    (K.openStarControl s x : ℝ) = 1 - ∑ᶠ v ∈ s, x.1 v :=
  (rfl)

/-- The control function of the open star of `s` vanishes exactly on the polyhedron of the full
subcomplex spanned by `s`. -/
theorem openStarControl_eq_zero_iff {x : Realization K} :
    K.openStarControl s x = 0 ↔ (x.1.support : Set ι) ⊆ s := by
  classical
  have h : 1 - ∑ᶠ v ∈ s, x.1 v = ∑ v ∈ x.1.support with v ∉ s, x.1 v := by
    linarith [mass_add_sum_filter_not K s x]
  rw [← Subtype.coe_inj, coe_openStarControl_apply, Icc.coe_zero, h,
    Finset.sum_eq_zero_iff_of_nonneg fun v _ => Realization.nonneg K x v]
  simp only [Finset.mem_filter, Finsupp.mem_support_iff, and_imp]
  exact ⟨fun h v hv => by_contra fun hs =>
      Finsupp.mem_support_iff.1 hv (h v (Finsupp.mem_support_iff.1 hv) hs),
    fun h v hv hs => absurd (h (Finsupp.mem_support_iff.2 hv)) hs⟩

/-- The control function of the open star of `s` is less than one exactly on the open star. -/
theorem openStarControl_lt_one_iff {x : Realization K} :
    K.openStarControl s x < 1 ↔ x ∈ K.openStarRealizationSet s := by
  classical
  rw [← Subtype.coe_lt_coe, coe_openStarControl_apply, Icc.coe_one, sub_lt_self_iff,
    mass_eq_sum_filter, Finset.sum_pos_iff_of_nonneg fun v _ => Realization.nonneg K x v]
  simp only [Finset.mem_filter, Finsupp.mem_support_iff, mem_openStarRealizationSet]
  exact ⟨fun ⟨v, ⟨_, hv⟩, hpos⟩ => ⟨v, hv, hpos⟩, fun ⟨v, hv, hpos⟩ => ⟨v, ⟨hpos.ne', hv⟩, hpos⟩⟩

/-- **The polyhedron of a full subcomplex is an NDR pair.** The NDR data is obtained from the
straight-line deformation of the open star of `s` onto the full subcomplex spanned by `s`, cut
off by the control function `openStarControl K s`. -/
def fullSubcomplexNDRPair : TauCeti.NDRPair {x : Realization K | (x.1.support : Set ι) ⊆ s} :=
  .ofHomotopyRel (K.setOf_support_subset_subset_openStarRealizationSet s)
    (K.openStarDeformation s) (K.openStarControl s)
    (fun _ => K.openStarControl_eq_zero_iff s) fun _ => (K.openStarControl_lt_one_iff s).1

theorem fullSubcomplexNDRPair_def :
    K.fullSubcomplexNDRPair s =
      .ofHomotopyRel (K.setOf_support_subset_subset_openStarRealizationSet s)
        (K.openStarDeformation s) (K.openStarControl s)
        (fun _ => K.openStarControl_eq_zero_iff s) fun _ => (K.openStarControl_lt_one_iff s).1 :=
  (rfl)

/-- **The polyhedron of a full subcomplex has the homotopy extension property** in the weak
realization. -/
theorem hasHomotopyExtensionProperty_setOf_support_subset :
    TauCeti.HasHomotopyExtensionProperty {x : Realization K | (x.1.support : Set ι) ⊆ s} :=
  (K.fullSubcomplexNDRPair s).hasHomotopyExtensionProperty

end AbstractSimplicialComplex
