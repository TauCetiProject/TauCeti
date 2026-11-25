/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Basic
import TauCeti.Geometry.Manifold.RegularValue.Covering

/-!
# Local constancy of the degree on the regular values

Let `f : M → N` be a proper `C¹` map from a Hausdorff boundaryless manifold to a manifold of the
same dimension, with orientations `o` of `M` and `o'` of `N`, and let `y` be a regular value of `f`.
If `y` is attained, `f` is trivialized over a neighbourhood of `y` consisting of regular values
(`TauCeti.IsRegularValue.exists_trivialization_contMDiffOn_symm`): its inverse branches, labelled by
the finite fibre over `y`, enumerate the fibre over every nearby value, and the branch through a
point `x` of the fibre keeps the orientation sign of `f` at `x`. If `y` is not attained, neither are
the nearby values, since the range of a proper map is closed. Either way the signed count of
preimages `deg_y(f) = TauCeti.degreeAtRegularValue o o' f y` is locally constant on the regular
values (`TauCeti.eventually_isRegularValue_and_degreeAtRegularValue_eq`). In particular, when every
value is regular, as for a local diffeomorphism, and `N` is preconnected, the degree does not
depend on the value (`TauCeti.degreeAtRegularValue_eq_of_forall_isRegularValue`), and it is the
mapping degree `TauCeti.degree o o' f`
(`TauCeti.degree_eq_degreeAtRegularValue_of_forall_isRegularValue`). No Sard theorem is used.

The two manifolds may be modelled on different spaces of the same dimension.

## Main results

* `TauCeti.eventually_isRegularValue_and_degreeAtRegularValue_eq`: values near a regular value are
  regular, with the same degree.
* `TauCeti.degreeAtRegularValue_eq_of_forall_isRegularValue`: if every value is regular and `N`
  is preconnected, the degree is constant.
* `TauCeti.degree_eq_degreeAtRegularValue_of_forall_isRegularValue`: if every value is regular
  and `N` is preconnected, the mapping degree is the signed count of preimages at any value.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 17, section Degree Theory.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §1 (the stack of records) and §5.
-/

public section

noncomputable section

open Set Filter
open scoped Manifold Topology

namespace TauCeti

variable {E E' H H' M N ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 1 N] [Fintype ι]

open Manifold.Orientation

/-- **The degree is locally constant on the regular values.** Let `f : M → N` be a proper `C¹` map
from a Hausdorff boundaryless manifold to a manifold of the same dimension, with orientations `o`
and `o'`. Every value near a regular value `y` of `f` is a regular value, with the same signed
count of preimages: the inverse branches of `f` through the points of the fibre over `y` meet the
fibre over a nearby value once each, with the orientation signs of `f` at their points over `y`. -/
theorem eventually_isRegularValue_and_degreeAtRegularValue_eq [T2Space M]
    [BoundarylessManifold I M] (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation J N ι)
    {f : M → N} (hf : ContMDiff I J 1 f) (hfp : IsProperMap f) {y : N}
    (hy : IsRegularValue I J f y) :
    ∀ᶠ y' in 𝓝 y, IsRegularValue I J f y' ∧
      degreeAtRegularValue o o' f y' = degreeAtRegularValue o o' f y := by
  have hdim := o.card_eq.symm.trans o'.card_eq
  by_cases hyf : y ∉ range f
  · -- The values near `y` lie off the closed range of `f`, so their fibres are empty.
    filter_upwards [hfp.isClosedMap.isClosed_range.isOpen_compl.mem_nhds hyf] with y' hy'
    exact ⟨isRegularValue_iff.2 fun x hx ↦ (hy' ⟨x, hx⟩).elim, by
      rw [degreeAtRegularValue_of_notMem_range hy', degreeAtRegularValue_of_notMem_range hyf]⟩
  obtain ⟨t, hyt, hreg, hlabel, hsmooth⟩ :=
    hy.exists_trivialization_contMDiffOn_symm hdim hf le_rfl hfp (not_not.1 hyf)
  have : Finite (f ⁻¹' {y}) := (hy.finite_preimage_of_isProperMap hdim hfp).to_subtype
  -- Near `y`, the branch through each point `x` of the fibre keeps the orientation sign at `x`.
  have hsgn : ∀ᶠ y' in 𝓝 y, ∀ x : f ⁻¹' {y},
      orientationSign o o' f (t.toOpenPartialHomeomorph.symm (y', x)) =
        orientationSign o o' f x := by
    refine eventually_all.2 fun x ↦ Tendsto.eventually
      (p := fun z ↦ orientationSign o o' f z = orientationSign o o' f x)
      ((hsmooth x).continuousOn.continuousAt (t.open_baseSet.mem_nhds hyt)) ?_
    simp only [hlabel x]
    exact eventually_orientationSign_eq hf.contMDiffAt
      ((isRegularPoint_iff_isInvertible_mfderiv hdim).mp (hy.isRegularPoint x.property))
  filter_upwards [t.open_baseSet.mem_nhds hyt, hsgn] with y' hy' hsgn'
  refine ⟨hreg hy', ?_⟩
  -- Over `y'`, the branches through the points of the fibre over `y` enumerate the fibre.
  have hbij : Function.Bijective fun x : f ⁻¹' {y} ↦
      (⟨t.toOpenPartialHomeomorph.symm (y', x), t.proj_symm_apply' hy'⟩ : f ⁻¹' {y'}) := by
    refine ⟨fun x x' hxx' ↦ ?_, fun w ↦ ⟨(t w).2, Subtype.ext ?_⟩⟩
    · simpa only [t.apply_symm_apply' hy', Prod.mk.injEq, true_and] using
        congrArg (fun w : f ⁻¹' {y'} ↦ t w) hxx'
    · have hw : f w = y' := w.property
      have := t.symm_apply_mk_proj (t.mem_source.2 (hw ▸ hy'))
      rwa [hw] at this
  rw [degreeAtRegularValue_def, degreeAtRegularValue_def, ← finsum_set_coe_eq_finsum_mem,
    ← finsum_set_coe_eq_finsum_mem, ← finsum_eq_of_bijective _ hbij fun _ ↦ rfl]
  exact finsum_congr hsgn'

/-- **The degree of a map without critical values is constant.** If every value of a proper `C¹`
map `f` from a Hausdorff boundaryless manifold to a preconnected manifold of the same dimension is
regular, as for a local diffeomorphism, then the signed count of preimages is the
same at every value. -/
theorem degreeAtRegularValue_eq_of_forall_isRegularValue [T2Space M] [PreconnectedSpace N]
    [BoundarylessManifold I M] (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation J N ι)
    {f : M → N} (hf : ContMDiff I J 1 f) (hfp : IsProperMap f)
    (hreg : ∀ y, IsRegularValue I J f y) (y y' : N) :
    degreeAtRegularValue o o' f y = degreeAtRegularValue o o' f y' :=
  ((IsLocallyConstant.iff_eventually_eq _).2 fun y ↦
    (eventually_isRegularValue_and_degreeAtRegularValue_eq o o' hf hfp (hreg y)).mono
      fun _ h ↦ h.2).apply_eq_of_preconnectedSpace y y'

/-- **The mapping degree of a map without critical values.** If every value of a proper `C¹` map
`f` from a Hausdorff boundaryless manifold to a preconnected manifold of the same dimension is
regular, then the mapping degree of `f` is its signed count of preimages at any
value. -/
theorem degree_eq_degreeAtRegularValue_of_forall_isRegularValue [T2Space M] [PreconnectedSpace N]
    [BoundarylessManifold I M] (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation J N ι)
    {f : M → N} (hf : ContMDiff I J 1 f) (hfp : IsProperMap f)
    (hreg : ∀ y, IsRegularValue I J f y) (y : N) :
    degree o o' f = degreeAtRegularValue o o' f y := by
  rw [degree_eq_degreeAtRegularValue_choose ⟨y, hreg y⟩]
  exact degreeAtRegularValue_eq_of_forall_isRegularValue o o' hf hfp hreg _ y

end TauCeti
