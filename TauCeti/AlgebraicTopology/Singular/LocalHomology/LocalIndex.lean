/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Degree
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.OpenEmbedding
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Topology.Homotopy.Affine
import TauCeti.Data.Set.Restrict
import TauCeti.Topology.ContinuousOn.PuncturedNhds
import TauCeti.Topology.MetricSpace.Pseudo.Defs
import TauCeti.Topology.OpenPartialHomeomorph.Continuity

/-!
# The local index of a map at an isolated point of its fibre

Let `M` and `N` be topological manifolds of the same dimension `n`, oriented by `o` and `o'`
(`TauCeti.HomologicalOrientation`), and let `f : M → N` be continuous. A point `x` is *isolated in
its fibre* when some open neighbourhood `U` of `x` meets `f⁻¹(f x)` only in `x`. Then `f`
restricts to a map of pairs `(U, U ∖ {x}) → (N, N ∖ {f x})`. By excision the local homology
`Hₙ(U, U ∖ {x}; ℤ)` is that of `M` at `x`, so the local orientation `o x` is a class there, and
its image is an integer multiple of the local orientation `o' (f x)`. That integer is the
**local index** `o.localIndex o' f x` of `f` at `x`. It does not depend on the choice of `U`
(`TauCeti.HomologicalOrientation.localIndex_eq_iff`), only on the germ of `f` at `x`
(`TauCeti.HomologicalOrientation.localIndex_congr`), and it is `0` by convention when `x` is not
isolated in its fibre. It is natural under open embeddings
(`TauCeti.HomologicalOrientation.localIndex_comap`): the local index of a map between open
subsets, oriented by restriction, is that of any map of the ambient manifolds extending it near
the point.

The local degree of `f` at a point `y` with finite fibre is the sum of the local indices at the
points of the fibre (`TauCeti.HomologicalOrientation.localDegree_eq_sum_localIndex`): the
fundamental class of `M` along the fibre decomposes as the sum of the local orientations at its
points, each pushed forward from a small neighbourhood of that point. For a proper map onto a
connected manifold the degree is therefore the sum of the local indices over any finite fibre
(`TauCeti.HomologicalOrientation.degree_eq_sum_localIndex`). This is how a degree is computed by
counting the preimages of a regular value with signs, once the local index at a regular point is
identified with the sign of the Jacobian. At a point where `f` is a local homeomorphism the local
index is `±1`
(`TauCeti.HomologicalOrientation.localIndex_eq_one_or_eq_neg_one_of_isLocalHomeomorphOn`), so a
proper map whose fibre over a point of a connected target is a single such point has degree `±1`.

Local indices multiply under composition: if `f x` is isolated in its fibre under `g`, then the
local index of `g ∘ f` at `x` is the local index of `g` at `f x` times that of `f` at `x`
(`TauCeti.HomologicalOrientation.localIndex_comp`). The same holds without any condition on the
fibres when `f` is an open embedding
(`TauCeti.HomologicalOrientation.localIndex_comp_of_isOpenEmbedding`). This is how the local index
behaves under changes of coordinates on the source or the target.

For maps into a finite-dimensional real normed space `F` of dimension `n` (while the source
dimension `finrank ℝ E` need not equal `n`), the local index is stable under perturbations that are
small compared with the displacement from the value at the point (Rouché's principle): if
`‖g z - f z‖ < ‖f z - f x‖` on a punctured neighbourhood of `x`, then `f` and `g` have the same
local index at `x` (`TauCeti.HomologicalOrientation.localIndex_eq_of_norm_sub_lt`), since in
positive source dimension continuity gives `f x = g x` and the straight-line homotopy from `f` to
`g` takes the value `f x` only at `x` near `x` (while in dimension zero either `n = 0` and `F` is
subsingleton or the local homology of `M` vanishes). If instead `‖g z - f z‖ ≤ c ‖f z - f x‖` near
`x` for a constant `c < 1`, the two local indices agree whether or not `x` is isolated in its fibre
(`TauCeti.HomologicalOrientation.localIndex_eq_of_norm_sub_le`).

## Main definitions

* `TauCeti.HomologicalOrientation.localIndex o o' f x`: the local index of `f` at `x`.

## Main results

* `TauCeti.HomologicalOrientation.localIndex_eq_iff`: the defining property of the local index,
  in any open neighbourhood isolating `x` in its fibre.
* `TauCeti.HomologicalOrientation.localIndex_congr`: maps agreeing near `x` have the same local
  index at `x`.
* `TauCeti.HomologicalOrientation.localIndex_comap`: the local index is natural under open
  embeddings of the source and target, with the pulled-back orientations.
* `TauCeti.HomologicalOrientation.localDegree_eq_sum_localIndex`: the local degree at a point with
  finite fibre is the sum of the local indices over the fibre.
* `TauCeti.HomologicalOrientation.degree_eq_sum_localIndex`: the degree of a proper map onto a
  preconnected manifold is the sum of the local indices over any finite fibre.
* `TauCeti.HomologicalOrientation.localIndex_eq_one_or_eq_neg_one_of_isLocalHomeomorphOn`: a
  local homeomorphism has local index `±1`.
* `TauCeti.HomologicalOrientation.degree_eq_one_or_eq_neg_one_of_isLocalHomeomorphOn`: a proper
  map with a one-point fibre, at whose point it is a local homeomorphism, has degree `±1`.
* `TauCeti.HomologicalOrientation.degree_addRight`: translations of a finite-dimensional real
  normed space have degree one, being properly homotopic to the identity, and so local index one
  (`TauCeti.HomologicalOrientation.localIndex_addRight`).
* `TauCeti.HomologicalOrientation.exists_eventuallyEq_and_localIndex_comap_eq`: the local index
  of a map read in open coordinates `j : M → E`, `k : N → F` of finite-dimensional real normed
  spaces is that of a map `E → F` agreeing with the coordinate expression near the point.
* `TauCeti.HomologicalOrientation.localIndex_comp`: the chain rule for local indices.
* `TauCeti.HomologicalOrientation.localIndex_comp_of_isOpenEmbedding`: the chain rule for local
  indices along an open embedding.
* `TauCeti.HomologicalOrientation.localIndex_eq_of_norm_sub_lt`,
  `TauCeti.HomologicalOrientation.localIndex_eq_of_norm_sub_le`: Rouché's principle for the local
  index.

## References

* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VIII, §4 (the degree as a
  sum of local indices).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Proposition 2.30 (the degree of a map of spheres as a sum of local degrees).
-/

public section

noncomputable section

open CategoryTheory Filter Module Set Topology

namespace TauCeti

namespace HomologicalOrientation

/-! ### Definition and basic properties -/

section Isolating

variable {M N E : Type} [TopologicalSpace M] [T2Space M] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n)

/-- The image of the local orientation `o x` under the restriction of `f` to an open neighbourhood
`U` of `x` meeting the fibre of `f` through `y` only in `x`, computed through the excision
isomorphism of the local homology of `U` at `x` with that of `M`. -/
private def localIndexClass (f : C(M, N)) {x : M} {y : N} {U : Set M} (hUo : IsOpen U)
    (hx : x ∈ U) (hU : ∀ z ∈ U, f z = y → z = x) :
    localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({y} : Set N) n :=
  localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (f.restrict U)
    ((Set.preimage_domRestrict_singleton_subset_iff hx).2 hU : f.restrict U ⁻¹' {y} ⊆ {⟨x, hx⟩}) n
    ((hUo.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨x, hx⟩ n).symm (o x)).val

/-- Shrinking the isolating neighbourhood does not change the image of the local orientation. -/
private theorem localIndexClass_of_subset (f : C(M, N)) {x : M} {y : N} {U V : Set M}
    (hUo : IsOpen U) (hVo : IsOpen V) (hVU : V ⊆ U) (hx : x ∈ V)
    (hU : ∀ z ∈ U, f z = y → z = x) :
    o.localIndexClass f hVo hx (fun z hz ↦ hU z (hVU hz)) =
      o.localIndexClass f hUo (hVU hx) hU := by
  have hincl : ContinuousMap.inclusion hVU ⁻¹' {⟨x, hVU hx⟩} ⊆ {⟨x, hx⟩} :=
    fun z hz ↦ Subtype.ext (by simpa [Subtype.ext_iff] using hz)
  -- The inclusion `V → U` carries the local orientation of `V` at `x` to that of `U` at `x`.
  have hmap := hUo.localHomologyMap_inclusion_localOrientationEquiv_symm hVo hVU hx (o x) hincl
  have hcomp : (f.restrict U).comp (ContinuousMap.inclusion hVU) = f.restrict V :=
    ContinuousMap.ext fun _ ↦ rfl
  have hsubU : f.restrict U ⁻¹' {y} ⊆ {⟨x, hVU hx⟩} :=
    (Set.preimage_domRestrict_singleton_subset_iff (hVU hx)).2 hU
  rw [localIndexClass, localIndexClass, ← hmap, ← ConcreteCategory.comp_apply]
  exact ConcreteCategory.congr_hom
    ((localHomologyMap_congr _ hcomp.symm _ n).trans
      (localHomologyMap_comp _ (ContinuousMap.inclusion hVU) (f.restrict U) hincl hsubU n).symm) _

/-- The image of the local orientation does not depend on the isolating neighbourhood. -/
private theorem localIndexClass_eq (f : C(M, N)) {x : M} {y : N} {U V : Set M} (hUo : IsOpen U)
    (hVo : IsOpen V) (hxU : x ∈ U) (hxV : x ∈ V) (hU : ∀ z ∈ U, f z = y → z = x)
    (hV : ∀ z ∈ V, f z = y → z = x) :
    o.localIndexClass f hUo hxU hU = o.localIndexClass f hVo hxV hV :=
  (o.localIndexClass_of_subset f hUo (hUo.inter hVo) inter_subset_left ⟨hxU, hxV⟩ hU).symm.trans
    (o.localIndexClass_of_subset f hVo (hUo.inter hVo) inter_subset_right ⟨hxU, hxV⟩ hV)

end Isolating

section Basic

variable {M N E F : Type} [TopologicalSpace M] [T2Space M] [TopologicalSpace N] [T2Space N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ChartedSpace F N]
  {n : ℕ} (o : HomologicalOrientation M E n) (o' : HomologicalOrientation N F n)

open scoped Classical in
/-- The **local index** of `f : M → N` at `x ∈ M`: when `x` is isolated in its fibre `f⁻¹(f x)`,
the integer `d` such that the restriction of `f` to an open neighbourhood `U` of `x` meeting the
fibre only in `x` carries the local orientation `o x` to `d • o' (f x)` in `Hₙ(N, N ∖ {f x}; ℤ)`
(`TauCeti.HomologicalOrientation.localIndex_eq_iff`), and `0` when `x` is not isolated in its
fibre. -/
def localIndex (f : C(M, N)) (x : M) : ℤ :=
  if h : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x then
    have hU := eventually_nhdsNE_ne_iff_exists_isOpen.1 h
    ((isLocalOrientation_iff _ _ _).1 (o' (f x)).property
      (o.localIndexClass f hU.choose_spec.1 hU.choose_spec.2.1 hU.choose_spec.2.2)).choose
  else 0

/-- In an open neighbourhood `U` of `x` meeting the fibre of `f` through `y = f x` only in `x`, the
restriction of `f` carries the local orientation `o x` to the local index times `o' y`. -/
theorem localHomologyMap_restrict_localOrientationEquiv_symm (f : C(M, N)) {x : M} {y : N}
    (hxy : f x = y) {U : Set M} (hUo : IsOpen U) (hx : x ∈ U) (hU : ∀ z ∈ U, f z = y → z = x) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (f.restrict U) (S := {⟨x, hx⟩}) (T := {y})
        (fun z hz ↦ Subtype.ext (hU z z.property (by simpa using hz))) n
        ((hUo.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨x, hx⟩ n).symm (o x)).val =
      o.localIndex o' f x • (o' y).val := by
  subst hxy
  have h : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x := eventually_nhdsNE_ne_iff_exists_isOpen.2 ⟨U, hUo, hx, hU⟩
  rw [localIndex, dite_eq_left h]
  have hV := eventually_nhdsNE_ne_iff_exists_isOpen.1 h
  refine Eq.trans ?_ ((isLocalOrientation_iff _ _ _).1 (o' (f x)).property _).choose_spec.symm
  exact o.localIndexClass_eq f hUo hV.choose_spec.1 hx hV.choose_spec.2.1 hU hV.choose_spec.2.2

/-- **The defining property of the local index**: in an open neighbourhood `U` of `x` meeting the
fibre of `f` through `y = f x` only in `x`, the local index is the integer `c` such that the
restriction of `f` to `U` carries the local orientation `o x`, read in `U` through excision, to
`c • o' y`. -/
theorem localIndex_eq_iff (hF : finrank ℝ F = n) (f : C(M, N)) {x : M} {y : N} (hxy : f x = y)
    {U : Set M} (hUo : IsOpen U) (hx : x ∈ U) (hU : ∀ z ∈ U, f z = y → z = x) {c : ℤ} :
    o.localIndex o' f x = c ↔
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (f.restrict U) (S := {⟨x, hx⟩}) (T := {y})
          (fun z hz ↦ Subtype.ext (hU z z.property (by simpa using hz))) n
          ((hUo.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨x, hx⟩ n).symm (o x)).val =
        c • (o' y).val := by
  rw [o.localHomologyMap_restrict_localOrientationEquiv_symm o' f hxy hUo hx hU]
  exact ⟨fun h ↦ h ▸ rfl, fun h ↦ o'.zsmul_left_injective hF y h⟩

/-- The local index vanishes at a point which is not isolated in its fibre. -/
theorem localIndex_of_frequently_eq (f : C(M, N)) {x : M} (h : ∃ᶠ z in 𝓝[≠] x, f z = f x) :
    o.localIndex o' f x = 0 := by
  rw [localIndex, dite_eq_right (not_eventually.2 (by simpa using h))]

/-- If the source manifold's dimension differs from `n` while the target manifold has dimension
`n`, every continuous map has local index `0` at `x`. -/
theorem localIndex_eq_zero_of_finrank_ne (hE : finrank ℝ E ≠ n) (hF : finrank ℝ F = n)
    (f : C(M, N)) (x : M) : o.localIndex o' f x = 0 := by
  have hz := isZero_singularHomology_complSingleton_of_ne (A := ModuleCat.{0} ℤ)
    (ModuleCat.of ℤ (ULift.{0} ℤ)) (chartAt E x) (mem_chart_source E x) rfl hE.symm
  have ho0 : (o x).val = 0 := by
    simpa using ConcreteCategory.congr_hom (hz.eq_of_src (𝟙 _) 0) (o x).val
  by_cases hf : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x
  · obtain ⟨U, hUo, hxU, hU⟩ := eventually_nhdsNE_ne_iff_exists_isOpen.1 hf
    rw [o.localIndex_eq_iff o' hF f rfl hUo hxU hU, zero_zsmul,
      IsOpenEmbedding.coe_localOrientationEquiv_symm, ho0, map_zero, map_zero]
  · exact o.localIndex_of_frequently_eq o' f (by simpa using not_eventually.1 hf)

/-- **The local index only depends on the germ of the map**: maps agreeing on a neighbourhood of
`x` have the same local index at `x`. -/
theorem localIndex_congr (hF : finrank ℝ F = n) {f g : C(M, N)} {x : M} (hfg : f =ᶠ[𝓝 x] g) :
    o.localIndex o' f x = o.localIndex o' g x := by
  have hfgx : f x = g x := hfg.eq_of_nhds
  have hfg' : ∀ᶠ z in 𝓝[≠] x, f z = g z := eventually_nhdsWithin_of_eventually_nhds hfg
  by_cases hf : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x
  · -- An open neighbourhood isolating `x` for `f`, shrunk into a neighbourhood `W` on which the
    -- two maps agree, isolates `x` for `g`, and the two restrictions coincide there.
    obtain ⟨U, hUo, hxU, hU⟩ := eventually_nhdsNE_ne_iff_exists_isOpen.1 hf
    obtain ⟨W, hWfg, hWo, hxW⟩ := eventually_nhds_iff.1 hfg
    have hfU : ∀ z ∈ U ∩ W, f z = f x → z = x := fun z hz ↦ hU z hz.1
    have hgU : ∀ z ∈ U ∩ W, g z = f x → z = x := fun z hz hgz ↦
      hU z hz.1 ((hWfg z hz.2).trans hgz)
    have hrestrict : g.restrict (U ∩ W) = f.restrict (U ∩ W) :=
      ContinuousMap.ext fun z ↦ (hWfg z z.property.2).symm
    rw [eq_comm, o.localIndex_eq_iff o' hF g hfgx.symm (hUo.inter hWo) (mem_inter hxU hxW) hgU,
      ← o.localHomologyMap_restrict_localOrientationEquiv_symm o' f rfl (hUo.inter hWo)
        (mem_inter hxU hxW) hfU]
    simp only [hrestrict]
  · have hg : ∃ᶠ z in 𝓝[≠] x, g z = g x :=
      ((not_eventually.1 hf).and_eventually hfg').mono fun z h ↦ by
        rw [← h.2, ← hfgx]
        exact not_not.1 h.1
    rw [o.localIndex_of_frequently_eq o' f (by simpa using not_eventually.1 hf),
      o.localIndex_of_frequently_eq o' g hg]

/-- Reversing the orientation of the source negates the local index. -/
@[simp]
theorem localIndex_neg_left (hF : finrank ℝ F = n) (f : C(M, N)) (x : M) :
    (-o).localIndex o' f x = -o.localIndex o' f x := by
  by_cases h : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x
  · obtain ⟨U, hUo, hx, hU⟩ := eventually_nhdsNE_ne_iff_exists_isOpen.1 h
    have hneg : (hUo.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨x, hx⟩ n).symm (-o x) =
        -(hUo.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨x, hx⟩ n).symm (o x) :=
      (Equiv.symm_apply_eq _).2 (by
        rw [IsOpenEmbedding.localOrientationEquiv_neg, Equiv.apply_symm_apply])
    rw [(-o).localIndex_eq_iff o' hF f rfl hUo hx hU, neg_apply, hneg, LocalOrientation.coe_neg,
      map_neg, o.localHomologyMap_restrict_localOrientationEquiv_symm o' f rfl hUo hx hU,
      neg_zsmul]
  · have h' : ∃ᶠ z in 𝓝[≠] x, f z = f x := by simpa using not_eventually.1 h
    rw [(-o).localIndex_of_frequently_eq o' f h', o.localIndex_of_frequently_eq o' f h', neg_zero]

/-- Reversing the orientation of the target negates the local index. -/
@[simp]
theorem localIndex_neg_right (hF : finrank ℝ F = n) (f : C(M, N)) (x : M) :
    o.localIndex (-o') f x = -o.localIndex o' f x := by
  by_cases h : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x
  · obtain ⟨U, hUo, hx, hU⟩ := eventually_nhdsNE_ne_iff_exists_isOpen.1 h
    rw [o.localIndex_eq_iff (-o') hF f rfl hUo hx hU,
      o.localHomologyMap_restrict_localOrientationEquiv_symm o' f rfl hUo hx hU, neg_apply,
      LocalOrientation.coe_neg, neg_zsmul, zsmul_neg, neg_neg]
  · have h' : ∃ᶠ z in 𝓝[≠] x, f z = f x := by simpa using not_eventually.1 h
    rw [o.localIndex_of_frequently_eq (-o') f h', o.localIndex_of_frequently_eq o' f h', neg_zero]

/-- **The local index in the whole source.** If `x` is the only point of `M` sent to `y = f x`,
the local index of `f` at `x` is the integer `c` such that `f` carries the local orientation `o x`
to `c • o' y`, with no isolating neighbourhood to choose. -/
theorem localIndex_eq_iff_of_preimage_subset (hF : finrank ℝ F = n) (f : C(M, N)) {x : M} {y : N}
    (hxy : f x = y) (h : f ⁻¹' {y} ⊆ {x}) {c : ℤ} :
    o.localIndex o' f x = c ↔
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) f h n (o x).val = c • (o' y).val := by
  have hincl : (⟨Subtype.val, continuous_subtypeVal⟩ : C((univ : Set M), M)) ⁻¹' {x} ⊆
      {⟨x, mem_univ x⟩} := fun z hz ↦ Subtype.ext hz
  rw [o.localIndex_eq_iff o' hF f hxy isOpen_univ (mem_univ x) fun z _ hz ↦ h hz,
    ← isOpen_univ.isOpenEmbedding_subtypeVal.localHomologyMap_localOrientationEquiv_symm
      ⟨x, mem_univ x⟩ (o x) hincl, ← ConcreteCategory.comp_apply, localHomologyMap_comp]
  -- `f.comp ⟨Subtype.val, _⟩` is `f.restrict univ` by definition.
  rfl

/-- **The local index only depends on the orientations at the point and its image**: if `o` and
`p` agree at `x`, and `o'` and `p'` agree at `f x`, the two local indices of `f` at `x` agree. The
orientations `p` and `p'` may be read in other model spaces. -/
theorem localIndex_eq_localIndex_of_apply_eq {E' F' : Type} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [ChartedSpace E' M] [NormedAddCommGroup F']
    [NormedSpace ℝ F'] [FiniteDimensional ℝ F'] [ChartedSpace F' N]
    {p : HomologicalOrientation M E' n} {p' : HomologicalOrientation N F' n} (f : C(M, N))
    {x : M} (hx : o x = p x) (hy : o' (f x) = p' (f x)) :
    o.localIndex o' f x = p.localIndex p' f x := by
  simp only [localIndex, localIndexClass, hx, hy]

/-- **A nonzero local index detects the local orientation of the source.** If `f` has the same
nonzero local index at `x` for the source orientations `o` and `p`, then `o` and `p` agree at `x`:
otherwise `p x = -o x`, and the two local indices would be negatives of each other. -/
theorem apply_eq_of_localIndex_eq_left (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) {E' : Type}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [ChartedSpace E' M]
    {p : HomologicalOrientation M E' n} (f : C(M, N)) {x : M}
    (h : o.localIndex o' f x = p.localIndex o' f x) (h0 : o.localIndex o' f x ≠ 0) :
    o x = p x := by
  subst hE
  rcases IsLocalOrientation.eq_or_eq_neg
      (singularHomologyComplSingletonFinrankIso _ (chartAt E x) (mem_chart_source E x))
      (o x).property (p x).property with h' | h'
  · exact Subtype.ext h'.symm
  · have hneg : p.localIndex o' f x = -o.localIndex o' f x := by
      rw [← (-o).localIndex_eq_localIndex_of_apply_eq o' f
        (Subtype.ext (h'.trans (LocalOrientation.coe_neg _).symm)).symm rfl,
        localIndex_neg_left o o' hF]
    omega

/-- **A nonzero local index detects the local orientation of the target.** If `f` has the same
nonzero local index at `x` for the target orientations `o'` and `p'`, then `o'` and `p'` agree at
`f x`: otherwise `p' (f x) = -o' (f x)`, and the two local indices would be negatives of each
other. -/
theorem apply_eq_of_localIndex_eq_right (hF : finrank ℝ F = n) {F' : Type} [NormedAddCommGroup F']
    [NormedSpace ℝ F'] [FiniteDimensional ℝ F'] [ChartedSpace F' N]
    {p' : HomologicalOrientation N F' n} (f : C(M, N)) {x : M}
    (h : o.localIndex o' f x = o.localIndex p' f x) (h0 : o.localIndex o' f x ≠ 0) :
    o' (f x) = p' (f x) := by
  subst hF
  rcases IsLocalOrientation.eq_or_eq_neg
      (singularHomologyComplSingletonFinrankIso _ (chartAt F (f x)) (mem_chart_source F (f x)))
      (o' (f x)).property (p' (f x)).property with h' | h'
  · exact Subtype.ext h'.symm
  · have hneg : o.localIndex p' f x = -o.localIndex o' f x := by
      rw [← o.localIndex_eq_localIndex_of_apply_eq (-o') f rfl
        (Subtype.ext (h'.trans (LocalOrientation.coe_neg _).symm)).symm,
        localIndex_neg_right o o' rfl]
    omega

end Basic

/-! ### Naturality and composition -/

section Functoriality

variable {M N E F : Type} [TopologicalSpace M] [T2Space M] [TopologicalSpace N] [T2Space N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ChartedSpace F N]
  {n : ℕ} (o : HomologicalOrientation M E n) (o' : HomologicalOrientation N F n)

/-- If `W` is an open neighbourhood of `x` meeting the fibre of `f` through `f x` only in `x` on
which `g ∘ j = k ∘ f`, then the restriction of `g` to `j '' W` carries the local orientation
`o (j x)` (read in `j '' W` through excision) to `(o.comap hj).localIndex (o'.comap hk) f x` times
`o' (k (f x))`. -/
private theorem localHomologyMap_restrict_comap_eq {U V : Type} [TopologicalSpace U]
    [T2Space U] [ChartedSpace E U] [TopologicalSpace V] [T2Space V] [ChartedSpace F V]
    {j : U → M} (hj : IsOpenEmbedding j) {k : V → N} (hk : IsOpenEmbedding k)
    {f : C(U, V)} {g : C(M, N)} {x : U} {W : Set U} (hWo : IsOpen W) (hxW : x ∈ W)
    (hWf : ∀ z ∈ W, f z = f x → z = x) (hWg : ∀ z ∈ W, g (j z) = k (f z)) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (g.restrict (j '' W))
        (S := {⟨j x, mem_image_of_mem j hxW⟩}) (T := {k (f x)})
        ((Set.preimage_domRestrict_singleton_subset_iff (mem_image_of_mem j hxW)).2 <| by
          rintro _ ⟨u, hu, rfl⟩ hgu
          exact congrArg j (hWf u hu (hk.injective ((hWg u hu).symm.trans hgu)))) n
        (((hj.isOpenMap W hWo).isOpenEmbedding_subtypeVal.localOrientationEquiv
          ⟨j x, mem_image_of_mem j hxW⟩ n).symm (o (j x))).val =
      (o.comap hj).localIndex (o'.comap hk) f x • (o' (k (f x))).val := by
  have hW'o : IsOpen (j '' W) := hj.isOpenMap W hWo
  have hxW' : j x ∈ j '' W := mem_image_of_mem j hxW
  have hW' : ∀ z ∈ j '' W, g z = k (f x) → z = j x := by
    rintro _ ⟨z, hz, rfl⟩ hgz
    rw [hWf z hz (hk.injective ((hWg z hz).symm.trans hgz))]
  let ψ : C(W, ↥(j '' W)) :=
    ⟨fun z ↦ ⟨j z, mem_image_of_mem j z.property⟩,
      (hj.continuous.comp continuous_subtypeVal).subtype_mk _⟩
  have hψ_comp : Subtype.val ∘ (ψ : W → ↥(j '' W)) = j ∘ Subtype.val := rfl
  have hψ : IsOpenEmbedding ψ :=
    (IsOpenEmbedding.of_comp_iff ψ hW'o.isOpenEmbedding_subtypeVal).1
      (hψ_comp.symm ▸ hj.comp hWo.isOpenEmbedding_subtypeVal)
  -- `j` identifies `W` with `j '' W`, compatibly with the local orientations at `x` and `j x`.
  have hclass : (hWo.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨x, hxW⟩ n).symm
      (o.comap hj x) = (hψ.localOrientationEquiv ⟨x, hxW⟩ n).symm
        ((hW'o.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨j x, hxW'⟩ n).symm (o (j x))) := by
    rw [comap_apply, ← Equiv.symm_trans_apply, IsOpenEmbedding.localOrientationEquiv_trans,
      ← Equiv.symm_trans_apply]
    refine congrArg (fun e ↦ e.symm (o (j x))) ((Equiv.ext fun z ↦ Subtype.ext ?_).trans
      (IsOpenEmbedding.localOrientationEquiv_trans hψ hW'o.isOpenEmbedding_subtypeVal
        ⟨x, hxW⟩ n).symm)
    simp only [IsOpenEmbedding.coe_localOrientationEquiv, localHomologyIsoOfIsOpenEmbedding_hom]
    exact ConcreteCategory.congr_hom
      (localHomologyMap_congr _ (ContinuousMap.ext (congrFun hψ_comp.symm)) _ n) z.val
  have hψx : ψ ⁻¹' {⟨j x, hxW'⟩} ⊆ {⟨x, hxW⟩} := fun z hz ↦ hψ.injective hz
  have hkx : (⟨k, hk.continuous⟩ : C(V, N)) ⁻¹' {k (f x)} ⊆ {f x} := fun z hz ↦ hk.injective hz
  have hpush := congrArg (ConcreteCategory.hom (localHomologyMap (A := ModuleCat.{0} ℤ)
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟨k, hk.continuous⟩ hkx n))
    ((o.comap hj).localHomologyMap_restrict_localOrientationEquiv_symm (o'.comap hk) f rfl hWo hxW
      hWf)
  rw [map_zsmul, comap_apply o' hk, hk.localHomologyMap_localOrientationEquiv_symm _ _ hkx] at hpush
  have hpull := hψ.localHomologyMap_localOrientationEquiv_symm ⟨x, hxW⟩
    ((hW'o.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨j x, hxW'⟩ n).symm (o (j x))) hψx
  have hgW' : g.restrict (j '' W) ⁻¹' {k (f x)} ⊆ {⟨j x, hxW'⟩} :=
    (Set.preimage_domRestrict_singleton_subset_iff hxW').2 hW'
  have hfW' : f.restrict W ⁻¹' {f x} ⊆ {⟨x, hxW⟩} :=
    (Set.preimage_domRestrict_singleton_subset_iff hxW).2 hWf
  have hmaps : localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟨ψ, hψ.continuous⟩ hψx n ≫
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (g.restrict (j '' W)) hgW' n =
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (f.restrict W) hfW' n ≫
        localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟨k, hk.continuous⟩ hkx n := by
    rw [localHomologyMap_comp, localHomologyMap_comp]
    exact localHomologyMap_congr _ (ContinuousMap.ext fun z : W ↦ hWg z z.property) _ n
  rw [← hpush, hclass, ← hpull]
  exact (ConcreteCategory.comp_apply _ _ _).symm.trans
    ((ConcreteCategory.congr_hom hmaps _).trans (ConcreteCategory.comp_apply _ _ _))

/-- **The local index is natural under open embeddings.** Let `j : U → M` and `k : V → N` be
open embeddings, and let `f : U → V` and `g : M → N` satisfy `g ∘ j = k ∘ f` near `x`. Then the
local index of `f` at `x`, for the orientations pulled back along `j` and `k`, is the local index
of `g` at `j x`. In particular the local index of a map between open subsets is computed in the
ambient manifolds. -/
theorem localIndex_comap (hF : finrank ℝ F = n) {U V : Type} [TopologicalSpace U] [T2Space U]
    [ChartedSpace E U] [TopologicalSpace V] [T2Space V] [ChartedSpace F V] {j : U → M}
    (hj : IsOpenEmbedding j) {k : V → N} (hk : IsOpenEmbedding k) {f : C(U, V)} {g : C(M, N)}
    {x : U} (h : ∀ᶠ z in 𝓝 x, g (j z) = k (f z)) :
    (o.comap hj).localIndex (o'.comap hk) f x = o.localIndex o' g (j x) := by
  by_cases hfx : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x
  · obtain ⟨W, hWo, hxW, hW⟩ := eventually_nhdsNE_ne_iff_exists_isOpen.1 hfx
    obtain ⟨W₁, hW₁, hW₁o, hxW₁⟩ := eventually_nhds_iff.1 h
    have hWf : ∀ z ∈ W ∩ W₁, f z = f x → z = x := fun z hz ↦ hW z hz.1
    have hWg : ∀ z ∈ W ∩ W₁, g (j z) = k (f z) := fun z hz ↦ hW₁ z hz.2
    rw [eq_comm, o.localIndex_eq_iff o' hF g (hWg x ⟨hxW, hxW₁⟩) (hj.isOpenMap _ (hWo.inter hW₁o))
      (mem_image_of_mem j ⟨hxW, hxW₁⟩) (by
        rintro _ ⟨z, hz, rfl⟩ hgz
        rw [hWf z hz (hk.injective ((hWg z hz).symm.trans hgz))])]
    exact o.localHomologyMap_restrict_comap_eq o' hj hk (hWo.inter hW₁o) ⟨hxW, hxW₁⟩ hWf hWg
  · -- If `x` is not isolated in its fibre, neither is `j x`, and both local indices vanish.
    have hf : ∃ᶠ z in 𝓝[≠] x, f z = f x := by simpa using not_eventually.1 hfx
    have hg : ∃ᶠ z in 𝓝[≠] (j x), g z = g (j x) := by
      rw [← hj.map_nhdsNE_eq x, frequently_map]
      exact (hf.and_eventually (eventually_nhdsWithin_of_eventually_nhds h)).mono
        fun z hz ↦ hz.2.trans ((congrArg k hz.1).trans h.self_of_nhds.symm)
    rw [(o.comap hj).localIndex_of_frequently_eq (o'.comap hk) f hf,
      o.localIndex_of_frequently_eq o' g hg]

/-- **The chain rule for local indices.** If `f x` is isolated in its fibre under `g`, the local
index of `g ∘ f` at `x` is the product of the local index of `g` at `f x` and that of `f` at `x`.
When `x` is not isolated in its fibre under `f`, neither is it under `g ∘ f`, and both sides
vanish. -/
theorem localIndex_comp {P G : Type} [TopologicalSpace P] [T2Space P] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [ChartedSpace G P]
    (o'' : HomologicalOrientation P G n) (hG : finrank ℝ G = n) {f : C(M, N)} {g : C(N, P)}
    {x : M} (hg : ∀ᶠ z in 𝓝[≠] f x, g z ≠ g (f x)) :
    o.localIndex o'' (g.comp f) x = o'.localIndex o'' g (f x) * o.localIndex o' f x := by
  by_cases hf : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x
  swap
  · have hf' : ∃ᶠ z in 𝓝[≠] x, f z = f x := by simpa using not_eventually.1 hf
    rw [o.localIndex_of_frequently_eq o' f hf', mul_zero]
    exact o.localIndex_of_frequently_eq o'' _ (hf'.mono fun z hz ↦ by simp [hz])
  obtain ⟨V, hVo, hxV, hV⟩ := eventually_nhdsNE_ne_iff_exists_isOpen.1 hg
  obtain ⟨U₀, hU₀o, hxU₀, hU₀⟩ := eventually_nhdsNE_ne_iff_exists_isOpen.1 hf
  set U := U₀ ∩ f ⁻¹' V
  have hUo : IsOpen U := hU₀o.inter (hVo.preimage f.continuous)
  have hxU : x ∈ U := ⟨hxU₀, hxV⟩
  have hfU : ∀ z ∈ U, f z = f x → z = x := fun z hz ↦ hU₀ z hz.1
  have hgfU : ∀ z ∈ U, g (f z) = g (f x) → z = x := fun z hz hgz ↦ hfU z hz (hV _ hz.2 hgz)
  -- `f` restricts to a map `φ : U → V`, through which both restrictions to `U` factor.
  let φ : C(U, V) :=
    ⟨fun z ↦ ⟨f z, z.property.2⟩, (f.continuous.comp continuous_subtypeVal).subtype_mk _⟩
  have hφ : φ ⁻¹' {⟨f x, hxV⟩} ⊆ {⟨x, hxU⟩} := fun z hz ↦
    Subtype.ext (hfU z z.property (congrArg Subtype.val hz))
  have hval : (ContinuousMap.mk (Subtype.val : V → N)) ⁻¹' {f x} ⊆ {⟨f x, hxV⟩} :=
    fun z hz ↦ Subtype.ext hz
  have hgV : g.restrict V ⁻¹' {g (f x)} ⊆ {⟨f x, hxV⟩} := fun z hz ↦
    Subtype.ext (hV z z.property hz)
  have hfφ : (ContinuousMap.mk (Subtype.val : V → N)).comp φ = f.restrict U :=
    ContinuousMap.ext fun _ ↦ rfl
  have hgφ : (g.comp f).restrict U = (g.restrict V).comp φ := ContinuousMap.ext fun _ ↦ rfl
  set c := (hUo.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨x, hxU⟩ n).symm (o x)
  set c' := (hVo.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨f x, hxV⟩ n).symm (o' (f x))
  -- `φ` carries the local orientation of `U` at `x` to the local index of `f` times that of `V`
  -- at `f x`, as the excision isomorphism of `V` shows.
  have hc : localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) φ hφ n c.val =
      o.localIndex o' f x • c'.val := by
    refine (ConcreteCategory.bijective_of_isIso (localHomologyIsoOfIsOpenEmbedding
      (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) hVo.isOpenEmbedding_subtypeVal
      ⟨f x, hxV⟩ n).hom).1 ?_
    rw [localHomologyIsoOfIsOpenEmbedding_hom, map_zsmul, ← ConcreteCategory.comp_apply,
      localHomologyMap_comp,
      hVo.isOpenEmbedding_subtypeVal.localHomologyMap_localOrientationEquiv_symm ⟨f x, hxV⟩ _ hval]
    exact (ConcreteCategory.congr_hom (localHomologyMap_congr _ hfφ _ n) _).trans
      (o.localHomologyMap_restrict_localOrientationEquiv_symm o' f rfl hUo hxU hfU)
  rw [o.localIndex_eq_iff o'' hG (g.comp f) (y := g (f x)) rfl hUo hxU hgfU]
  refine (ConcreteCategory.congr_hom (localHomologyMap_congr _ hgφ _ n) _).trans ?_
  rw [← localHomologyMap_comp _ φ (g.restrict V) hφ hgV, ConcreteCategory.comp_apply, hc,
    map_zsmul, o'.localHomologyMap_restrict_localOrientationEquiv_symm o'' g rfl hVo hxV hV,
    smul_smul, mul_comm]

/-- **The chain rule for local indices along an open embedding.** If `f` is an open embedding, the
local index of `g ∘ f` at `x` is the product of the local index of `g` at `f x` and that of `f`
at `x`, with no condition on the fibres: when `f x` is not isolated in its fibre under `g`,
neither is `x` under `g ∘ f`, since `f` identifies the punctured neighbourhoods of `x` and of
`f x`. -/
theorem localIndex_comp_of_isOpenEmbedding {P G : Type} [TopologicalSpace P] [T2Space P]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [ChartedSpace G P]
    (o'' : HomologicalOrientation P G n) (hG : finrank ℝ G = n) {f : C(M, N)} {g : C(N, P)}
    (hf : IsOpenEmbedding f) (x : M) :
    o.localIndex o'' (g.comp f) x = o'.localIndex o'' g (f x) * o.localIndex o' f x := by
  by_cases hg : ∀ᶠ z in 𝓝[≠] f x, g z ≠ g (f x)
  · exact o.localIndex_comp o' o'' hG hg
  have hg' : ∃ᶠ z in 𝓝[≠] f x, g z = g (f x) := by simpa using not_eventually.1 hg
  rw [o'.localIndex_of_frequently_eq o'' g hg', zero_mul]
  rw [← hf.map_nhdsNE_eq x] at hg'
  exact o.localIndex_of_frequently_eq o'' _ (frequently_map.1 hg')

end Functoriality

/-! ### Relation to local degree and degree -/

section Degree

variable {M N E F : Type} [TopologicalSpace M] [T2Space M] [TopologicalSpace N] [T2Space N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ChartedSpace F N]
  {n : ℕ} (o : HomologicalOrientation M E n) (o' : HomologicalOrientation N F n)

/-- The local orientation at a point `x` of a finite set `S`, pushed forward from the complement of
`S ∖ {x}` to a class of `Hₙ(M, M ∖ S)`. -/
private def compClass {S : Set M} (hS : S.Finite) (x : M) :
    localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) S n :=
  localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟨Subtype.val, continuous_subtypeVal⟩
    (Set.preimage_val_compl_diff_singleton_subset S x) n
    (((hS.sdiff.isClosed.isOpen_compl).isOpenEmbedding_subtypeVal.localOrientationEquiv
      ⟨x, fun h ↦ h.2 rfl⟩ n).symm (o x)).val

/-- The class of `x` restricts to the local orientation `o x` at `x`. -/
private theorem localHomologyRestriction_compClass_self {S : Set M} (hS : S.Finite) {x : M}
    (hx : x ∈ S) :
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) (singleton_subset_iff.2 hx) n
      (o.compClass hS x) = (o x).val := by
  rw [compClass, ← ConcreteCategory.comp_apply, localHomologyMap_comp_localHomologyRestriction]
  exact IsOpenEmbedding.localHomologyMap_localOrientationEquiv_symm
    (hS.sdiff.isClosed.isOpen_compl).isOpenEmbedding_subtypeVal ⟨x, fun h ↦ h.2 rfl⟩ (o x) _

/-- The class of `x` restricts to `0` at every other point `x'` of `S`: the complement of
`S ∖ {x}` misses `x'`, so the restriction factors through `Hₙ(U, U) = 0`. -/
private theorem localHomologyRestriction_compClass_of_ne {S : Set M} (hS : S.Finite) {x x' : M}
    (hx' : x' ∈ S) (hxx' : x ≠ x') :
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) (singleton_subset_iff.2 hx') n
      (o.compClass hS x) = 0 := by
  rw [compClass, ← ConcreteCategory.comp_apply,
    localHomologyMap_comp_localHomologyRestriction_eq_zero_of_notMem_range _ _ _ hx' ?_]
  · simp
  rintro ⟨z, hz : (z : M) = x'⟩
  exact z.property ⟨hz ▸ hx', fun h ↦ hxx' (hz ▸ h).symm⟩

/-- The classes of the points of a finite set `S` sum to the fundamental class along `S`. -/
private theorem sum_compClass (hE : finrank ℝ E = n) {S : Set M} (hS : S.Finite) :
    ∑ x ∈ hS.toFinset, o.compClass hS x = o.fundamentalClassOn hE hS.isCompact := by
  refine o.eq_fundamentalClassOn hE hS.isCompact fun x' hx' ↦ ?_
  rw [map_sum, Finset.sum_eq_single_of_mem x' (hS.mem_toFinset.2 hx')
    fun x _ hxx' ↦ o.localHomologyRestriction_compClass_of_ne hS hx' hxx',
    o.localHomologyRestriction_compClass_self hS hx']

/-- **The local degree is the sum of the local indices over the fibre**: if the fibre of `f` over
`y` is finite, the local degree of `f` at `y` is the sum of the local indices of `f` at the points
of the fibre. -/
theorem localDegree_eq_sum_localIndex (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (f : C(M, N))
    {y : N} (hy : (f ⁻¹' {y}).Finite) :
    o.localDegree o' hE f y = ∑ x ∈ hy.toFinset, o.localIndex o' f x := by
  rw [localDegree_eq_iff o o' hE hF f hy.isCompact, ← o.sum_compClass hE hy, map_sum]
  -- The class of each point `x` of the fibre is carried by `f` to the local index at `x` times
  -- `o' y`, the complement of the rest of the fibre being a neighbourhood isolating `x`.
  -- The scalar action on the homology group is `zsmul`, so `Finset.sum_smul` is used with the
  -- `ℤ`-module structure `AddCommGroup.toIntModule` rather than the one of `ModuleCat`.
  refine (Finset.sum_congr rfl fun x hx ↦ ?_).trans
    (@Finset.sum_smul _ _ _ _ _ (AddCommGroup.toIntModule _) _ _ _).symm
  rw [compClass, ← ConcreteCategory.comp_apply, localHomologyMap_comp]
  exact o.localHomologyMap_restrict_localOrientationEquiv_symm o' f (hy.mem_toFinset.1 hx)
    hy.sdiff.isClosed.isOpen_compl (fun h ↦ h.2 rfl) fun z hz hfz ↦ by_contra fun h ↦ hz ⟨hfz, h⟩

/-- If `x` is the only point of `M` sent to `y`, the local degree of `f` at `y` is the local index
of `f` at `x`. -/
theorem localDegree_eq_localIndex (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (f : C(M, N))
    {x : M} {y : N} (h : f ⁻¹' {y} = {x}) :
    o.localDegree o' hE f y = o.localIndex o' f x := by
  have hfin : (f ⁻¹' {y}).Finite := h ▸ finite_singleton x
  have hs : hfin.toFinset = {x} := by ext; simp [h]
  rw [o.localDegree_eq_sum_localIndex o' hE hF f hfin, hs, Finset.sum_singleton]

/-- The identity has local index `1` at every point. -/
@[simp]
theorem localIndex_id (hE : finrank ℝ E = n) (x : M) :
    o.localIndex o (ContinuousMap.id M) x = 1 := by
  rw [← o.localDegree_eq_localIndex o hE hE _ (preimage_id (s := {x})), localDegree_id]

/-- **The degree is the sum of the local indices over any finite fibre**: for a proper map `f`
onto a preconnected manifold and a point `y` whose fibre is finite, the degree of `f` is the sum
of the local indices of `f` at the points of the fibre over `y`. -/
theorem degree_eq_sum_localIndex (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)
    [PreconnectedSpace N] {f : C(M, N)} (hf : IsProperMap f) {y : N} (hy : (f ⁻¹' {y}).Finite) :
    o.degree o' hE f = ∑ x ∈ hy.toFinset, o.localIndex o' f x := by
  rw [← o.localDegree_eq_degree o' hE hF hf y, o.localDegree_eq_sum_localIndex o' hE hF f hy]

/-- **A local homeomorphism has local index `±1`.** If `f` is a local homeomorphism at `x`, it
identifies the local homology of `M` at `x` with that of `N` at `f x`. So it carries the local
orientation `o x` to a generator of `Hₙ(N, N ∖ {f x}; ℤ)`, which is `o' (f x)` or its
negative. -/
theorem localIndex_eq_one_or_eq_neg_one_of_isLocalHomeomorphOn (hF : finrank ℝ F = n)
    {f : C(M, N)} {s : Set M} (hf : IsLocalHomeomorphOn f s) {x : M} (hx : x ∈ s) :
    o.localIndex o' f x = 1 ∨ o.localIndex o' f x = -1 := by
  obtain ⟨e, hxe, hfe⟩ := hf x hx
  have hU : IsOpenEmbedding (f.restrict e.source) := by
    rw [ContinuousMap.coe_restrict, hfe]
    exact e.isOpenEmbedding_restrict
  have hfib : ∀ z ∈ e.source, f z = f x → z = x := fun z hz hfz ↦
    congrArg Subtype.val (hU.injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨x, hxe⟩) hfz)
  -- The restriction of `f` to `e.source` carries the local orientation `o x`, read in
  -- `e.source`, to the local orientation of `N` at `f x` corresponding to it, which is
  -- `± o' (f x)`.
  let w := hU.localOrientationEquiv ⟨x, hxe⟩ n
    ((e.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨x, hxe⟩ n).symm (o x))
  have hw := hU.localHomologyMap_localOrientationEquiv_symm ⟨x, hxe⟩ w
    (fun z hz ↦ Subtype.ext (hfib z z.property hz))
  rw [Equiv.symm_apply_apply] at hw
  have key (c : ℤ) (hc : w.val = c • (o' (f x)).val) : o.localIndex o' f x = c :=
    (o.localIndex_eq_iff o' hF f rfl e.open_source hxe hfib).2 (hw.trans hc)
  subst hF
  rcases IsLocalOrientation.eq_or_eq_neg
      (singularHomologyComplSingletonFinrankIso _ (chartAt F (f x)) (mem_chart_source F (f x)))
      (o' (f x)).property w.property with h | h
  · exact Or.inl (key 1 (by rw [h, one_zsmul]))
  · exact Or.inr (key (-1) (by rw [h, neg_one_zsmul]))

/-- **A map with a one-point fibre at which it is a local homeomorphism has degree `±1`.** For a
proper map `f` onto a preconnected manifold, if `x` is the only point sent to `f x` and `f` is a
local homeomorphism at `x`, then the degree of `f` is `1` or `-1`. -/
theorem degree_eq_one_or_eq_neg_one_of_isLocalHomeomorphOn (hE : finrank ℝ E = n)
    (hF : finrank ℝ F = n) [PreconnectedSpace N] {f : C(M, N)} (hf : IsProperMap f) {x : M}
    (hfib : f ⁻¹' {f x} = {x}) {s : Set M} (hs : IsLocalHomeomorphOn f s) (hx : x ∈ s) :
    o.degree o' hE f = 1 ∨ o.degree o' hE f = -1 := by
  rw [← o.localDegree_eq_degree o' hE hF hf (f x), o.localDegree_eq_localIndex o' hE hF f hfib]
  exact o.localIndex_eq_one_or_eq_neg_one_of_isLocalHomeomorphOn o' hF hs hx

end Degree

/-! ### Translations and coordinate charts in normed spaces -/

section Normed

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
  (o : HomologicalOrientation E E n)

/-- **Translations have degree one.** The translation by `v` of a finite-dimensional real normed
space is properly homotopic to the identity, so its degree is that of the identity. -/
@[simp]
theorem degree_addRight (hE : finrank ℝ E = n) (v : E) :
    o.degree o hE (ContinuousMap.addRight v) = 1 := by
  -- The straight-line homotopy from the identity to the translation is proper: it is the
  -- projection `[0, 1] × E → E` composed with the homeomorphism `(t, y) ↦ (t, y + t v)`.
  have hH : IsProperMap (ContinuousMap.Homotopy.affine (ContinuousMap.id E)
      (ContinuousMap.addRight v)) := by
    let Φ : unitInterval × E ≃ₜ unitInterval × E :=
      { toFun := fun p ↦ (p.1, p.2 + (p.1 : ℝ) • v)
        invFun := fun p ↦ (p.1, p.2 - (p.1 : ℝ) • v)
        left_inv := fun p ↦ by simp
        right_inv := fun p ↦ by simp
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    have h : ⇑(ContinuousMap.Homotopy.affine (ContinuousMap.id E) (ContinuousMap.addRight v)) =
        Prod.snd ∘ Φ := by
      ext p
      simp [Φ, AffineMap.lineMap_apply_module', add_comm]
    rw [h]
    exact isProperMap_snd_of_compactSpace.comp Φ.isProperMap
  rw [← o.degree_eq_of_homotopy o hE hE (ContinuousMap.Homotopy.affine _ _) hH, degree_id]

/-- Translations preserve every orientation of a finite-dimensional real normed space: the
translation by `v` has local index `1` at every point, since it has degree one. -/
@[simp]
theorem localIndex_addRight (hE : finrank ℝ E = n) (v x : E) :
    o.localIndex o (ContinuousMap.addRight v) x = 1 := by
  have hfib : ContinuousMap.addRight v ⁻¹' {x + v} = {x} := by ext; simp
  rw [← o.localDegree_eq_localIndex o hE hE _ hfib,
    o.localDegree_eq_degree o hE hE (Homeomorph.addRight v).isProperMap, o.degree_addRight hE]

/-- **The translated identity chart preserves every orientation.** The identity chart of `E`,
followed by the translation taking `z` to the origin, carries the local orientation `o z` to
`o 0`: translations have local index `1`. -/
theorem localHomologyMap_refl_sub_localOrientationEquiv_symm (hE : finrank ℝ E = n) (z : E) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : (OpenPartialHomeomorph.refl E).source ↦ OpenPartialHomeomorph.refl E x -
            OpenPartialHomeomorph.refl E z,
          (OpenPartialHomeomorph.refl E).continuousOn.domRestrict.sub continuous_const⟩ :
          C((OpenPartialHomeomorph.refl E).source, E)) (S := {⟨z, mem_univ z⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext ((OpenPartialHomeomorph.refl E).injOn x.property (mem_univ z)
            (sub_eq_zero.1 hx))) n
        (((OpenPartialHomeomorph.refl E).open_source.isOpenEmbedding_subtypeVal
          |>.localOrientationEquiv ⟨z, mem_univ z⟩ n).symm (o z)).val =
      (o 0).val := by
  have h := o.localIndex_addRight hE (-z) z
  rw [o.localIndex_eq_iff o hE (ContinuousMap.addRight (-z)) (y := 0) (add_neg_cancel z)
    (OpenPartialHomeomorph.refl E).open_source (mem_univ z)
    (fun x _ hx ↦ neg_add_eq_zero.1 ((add_comm _ _).trans hx) |>.symm), one_smul] at h
  refine Eq.trans ?_ h
  -- The translated chart is the restriction of the translation by `-z` to the chart source.
  have e : (⟨fun x : (OpenPartialHomeomorph.refl E).source ↦ OpenPartialHomeomorph.refl E x -
      OpenPartialHomeomorph.refl E z,
      (OpenPartialHomeomorph.refl E).continuousOn.domRestrict.sub continuous_const⟩ :
        C((OpenPartialHomeomorph.refl E).source, E)) =
      (ContinuousMap.addRight (-z)).restrict (OpenPartialHomeomorph.refl E).source :=
    ContinuousMap.ext fun x ↦ sub_eq_add_neg _ _
  exact ConcreteCategory.congr_hom (localHomologyMap_congr _ e _ n) _

/-- **Comparing a chart orientation with a restricted orientation.** Let `φ` be a chart of `M`
with values in `E`, and `V` an open neighbourhood of `z` inside its source. If `φ`, followed by the
translation taking `φ z` to the origin, carries the local orientation `oM z` to `o 0`, then the
orientation of `V` pulled back from `o` along `φ` agrees at `z` with the orientation of `V`
restricted from `oM`: the translated chart has local index `1` at `z` for both. -/
theorem comap_apply_eq_of_localHomologyMap_chart_sub (hE : finrank ℝ E = n) {M : Type}
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] (oM : HomologicalOrientation M E n)
    (φ : OpenPartialHomeomorph M E) {z : M} (V : TopologicalSpace.Opens M) (hz : z ∈ V)
    (hVφ : (V : Set M) ⊆ φ.source)
    (hφ : localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : φ.source ↦ φ x - φ z, φ.continuousOn.domRestrict.sub continuous_const⟩ :
          C(φ.source, E)) (S := {⟨z, hVφ hz⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext (φ.injOn x.property (hVφ hz) (sub_eq_zero.1 hx))) n
        ((φ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hVφ hz⟩
          n).symm (oM z)).val =
      (o 0).val)
    (hj : IsOpenEmbedding (fun x : V ↦ φ x)) :
    (o.comap hj) ⟨z, hz⟩ = (oM.comap V.isOpenEmbedding') ⟨z, hz⟩ := by
  let W : TopologicalSpace.Opens M := ⟨φ.source, φ.open_source⟩
  let incl : V → W := fun x ↦ ⟨x.val, hVφ x.property⟩
  have hincl : IsOpenEmbedding incl :=
    (IsOpenEmbedding.of_comp_iff _ W.isOpenEmbedding').1 V.isOpenEmbedding'
  -- The translated chart `τ` on the source of `φ` has local index `1` at `z` for `oM`, by `hφ`, ...
  let τ : C(W, E) := ⟨fun x ↦ φ x - φ z, φ.continuousOn.domRestrict.sub continuous_const⟩
  have hτ : (oM.comap W.isOpenEmbedding').localIndex o τ ⟨z, hVφ hz⟩ = 1 := by
    rw [localIndex_eq_iff_of_preimage_subset _ o hE τ (x := ⟨z, hVφ hz⟩) (sub_self _)
      (fun x hx ↦ Subtype.ext (φ.injOn x.property (hVφ hz) (sub_eq_zero.1 (hx : φ x - φ z = 0)))),
      one_smul, comap_apply]
    exact hφ
  -- ... so does its restriction to `V`, for the orientation of `V` restricted from `oM` ...
  let τV : C(V, E) := τ.comp ⟨incl, hincl.continuous⟩
  have hτV : (oM.comap V.isOpenEmbedding').localIndex o τV ⟨z, hz⟩ = 1 := by
    have h := (oM.comap W.isOpenEmbedding').localIndex_comap o hE hincl IsOpenEmbedding.id
      (f := τV) (g := τ) (x := ⟨z, hz⟩) (.of_forall fun _ ↦ rfl)
    rw [comap_comap, comap_id, comap_congr _ _ V.isOpenEmbedding' rfl] at h
    exact h.trans hτ
  -- ... and for the orientation pulled back along `φ`, since translations preserve orientation.
  have hτj : (o.comap hj).localIndex o τV ⟨z, hz⟩ = 1 := by
    have h := o.localIndex_comap o hE hj IsOpenEmbedding.id (f := τV)
      (g := ContinuousMap.addRight (-φ z)) (x := ⟨z, hz⟩)
      (.of_forall fun _ ↦ (sub_eq_add_neg _ _).symm)
    rwa [comap_id, localIndex_addRight o hE] at h
  exact apply_eq_of_localIndex_eq_left _ o hE hE τV (hτj.trans hτV.symm)
    (by rw [hτj]; exact one_ne_zero)

/-- **The local index in open coordinates is that of a map of the ambient spaces.** Let
`j : M → E` and `k : N → F` be open embeddings into finite-dimensional real normed spaces, oriented
by `o` and `o'`, and let `f : M → N` be given near `x` in these coordinates by `φ : E → F`, so that
`φ (j z) = k (f z)` near `x`. Then there is a continuous map `G : E → F` agreeing with `φ` near
`j x` whose local index at `j x` is the local index of `f` at `x`, for the orientations pulled back
along `j` and `k`. -/
theorem exists_eventuallyEq_and_localIndex_comap_eq {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (o' : HomologicalOrientation F F n)
    (hF : finrank ℝ F = n) {M N : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [TopologicalSpace N] [T2Space N] [ChartedSpace F N] {j : M → E} (hj : IsOpenEmbedding j)
    {k : N → F} (hk : IsOpenEmbedding k) {f : C(M, N)} {φ : E → F} {x : M}
    (hφ : ∀ᶠ z in 𝓝 x, φ (j z) = k (f z)) :
    ∃ G : C(E, F), G =ᶠ[𝓝 (j x)] φ ∧
      (o.comap hj).localIndex (o'.comap hk) f x = o.localIndex o' G (j x) := by
  -- On an open neighbourhood `W` of `x` where `φ ∘ j = k ∘ f`, `φ` is continuous on `j '' W`.
  obtain ⟨W, hW, hWo, hxW⟩ := eventually_nhds_iff.1 hφ
  have hφc : ContinuousOn φ (j '' W) := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hj.continuousAt_iff.1 ((hk.continuous.comp f.continuous).continuousAt.congr
      (eventually_of_mem (hWo.mem_nhds hz) fun y hy ↦ (hW y hy).symm))).continuousWithinAt
  -- Extend `φ` from a closed ball about `j x` inside `j '' W` to a continuous map `G : E → F`, by
  -- Tietze's theorem; `G` agrees with `φ` near `j x`, and so `G ∘ j` agrees with `k ∘ f` near `x`.
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 (hj.isOpenMap W hWo) (j x) (mem_image_of_mem j hxW)
  have hB : Metric.closedBall (j x) (ε / 2) ⊆ j '' W :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεW
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq Metric.isClosed_closedBall
    ⟨_, (hφc.mono hB).domRestrict⟩
  have hGφ : G =ᶠ[𝓝 (j x)] φ :=
    eventually_of_mem (Metric.closedBall_mem_nhds _ (half_pos hε)) fun z hz ↦
      congrArg (· ⟨z, hz⟩) hG
  exact ⟨G, hGφ, o.localIndex_comap o' hF hj hk
    ((((hj.continuous.tendsto x).eventually hGφ).and hφ).mono fun z hz ↦ hz.1.trans hz.2)⟩

end Normed

/-! ### Rouché's principle -/

section Rouche

variable {M E F : Type} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {n : ℕ} (o : HomologicalOrientation M E n)
  (o' : HomologicalOrientation F F n)

/-- **Rouché's principle for the local index.** If, on a punctured neighbourhood of `x`, `g` is
closer to `f` than `f` is to its value `f x`, then `f` and `g` have the same local index at `x`.
Only the target dimension must equal `n`; the source dimension may differ. -/
theorem localIndex_eq_of_norm_sub_lt (hF : finrank ℝ F = n) {f g : C(M, F)} {x : M}
    (h : ∀ᶠ z in 𝓝[≠] x, ‖g z - f z‖ < ‖f z - f x‖) :
    o.localIndex o' f x = o.localIndex o' g x := by
  by_cases hE0 : finrank ℝ E = 0 ∧ n ≠ 0
  · rw [o.localIndex_eq_zero_of_finrank_ne o' (by omega) hF,
      o.localIndex_eq_zero_of_finrank_ne o' (by omega) hF]
  have hfg : f x = g x := by
    by_cases h0 : finrank ℝ E = 0
    · have : Subsingleton F := Module.finrank_zero_iff (R := ℝ).1 (hF.trans (by tauto))
      exact Subsingleton.elim _ _
    · have : Nontrivial E := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero h0)
      have : (𝓝[≠] x).NeBot := (chartAt E x).nhdsNE_neBot (mem_chart_source E x)
      exact (f.continuous.continuousAt.mono_left nhdsWithin_le_nhds).eq_of_eventually_dist_le
        (g.continuous.continuousAt.mono_left nhdsWithin_le_nhds)
        (h.mono fun _ hz ↦ by simpa only [dist_eq_norm] using hz.le)
  obtain ⟨W, hW, hWo, hxW⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h)
  -- Along the straight-line homotopy on `W` from `f` to `g`, the value `f x` is only taken at `x`.
  let H := ContinuousMap.Homotopy.affine (f.restrict W) (g.restrict W)
  have hH : ∀ (t : unitInterval) (z : W),
      z ∉ ({⟨x, hxW⟩} : Set W) → H (t, z) ∉ ({f x} : Set F) := by
    intro t z hz htz
    refine (hW z z.property fun hzx ↦ hz (Subtype.ext hzx)).not_ge ?_
    have hseg : ‖H (t, z) - f z‖ ≤ ‖g z - f z‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm, dist_comm (g z) (f z)]
      simpa only [H, ContinuousMap.Homotopy.affine_apply, ContinuousMap.restrict_apply,
        dist_lineMap_left] using mul_le_of_le_one_left dist_nonneg
          (by rw [Real.norm_of_nonneg t.property.1]; exact t.property.2)
    rw [mem_singleton_iff.1 htz, norm_sub_rev] at hseg
    exact hseg
  have hfW : ∀ z ∈ W, f z = f x → z = x := fun z hz hfz ↦
    by_contra fun hzx ↦ hH 0 ⟨z, hz⟩ (fun h ↦ hzx (congrArg Subtype.val h))
      ((H.apply_zero ⟨z, hz⟩).trans ((f.restrict_apply W ⟨z, hz⟩).trans hfz))
  have hgW : ∀ z ∈ W, g z = f x → z = x := fun z hz hgz ↦
    by_contra fun hzx ↦ hH 1 ⟨z, hz⟩ (fun h ↦ hzx (congrArg Subtype.val h))
      ((H.apply_one ⟨z, hz⟩).trans ((g.restrict_apply W ⟨z, hz⟩).trans hgz))
  rw [eq_comm, o.localIndex_eq_iff o' hF g hfg.symm hWo hxW hgW,
    ← o.localHomologyMap_restrict_localOrientationEquiv_symm o' f rfl hWo hxW hfW]
  exact ConcreteCategory.congr_hom (localHomologyMap_eq_of_homotopy _ H hH _ _ n).symm _

/-- **Rouché's principle for the local index, with a uniform ratio.** If
`‖g z - f z‖ ≤ c ‖f z - f x‖` near `x` for some `c < 1`, then `f` and `g` have the same local
index at `x`. Only the target dimension must equal `n`; the source dimension may differ. When `x`
is not isolated in its fibre under `f`, the estimate makes `g` take the value `g x` wherever `f`
takes `f x`, so both local indices vanish. -/
theorem localIndex_eq_of_norm_sub_le (hF : finrank ℝ F = n) {f g : C(M, F)} {x : M} {c : ℝ}
    (hc : c < 1) (h : ∀ᶠ z in 𝓝 x, ‖g z - f z‖ ≤ c * ‖f z - f x‖) :
    o.localIndex o' f x = o.localIndex o' g x := by
  by_cases hiso : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x
  · refine o.localIndex_eq_of_norm_sub_lt o' hF ?_
    filter_upwards [hiso, eventually_nhdsWithin_of_eventually_nhds h] with z hz hz'
    exact hz'.trans_lt (mul_lt_of_lt_one_left (norm_pos_iff.2 (sub_ne_zero.2 hz)) hc)
  have hfg : f x = g x :=
    (sub_eq_zero.1 (norm_le_zero_iff.1 (by simpa using h.self_of_nhds))).symm
  have hfr : ∃ᶠ z in 𝓝[≠] x, f z = f x := by simpa using not_eventually.1 hiso
  have hfr' := hfr.and_eventually (eventually_nhdsWithin_of_eventually_nhds h)
  rw [o.localIndex_of_frequently_eq o' f hfr, o.localIndex_of_frequently_eq o' g
    (hfr'.mono fun z hz ↦ ?_)]
  have hgz : ‖g z - f z‖ ≤ 0 := by simpa [hz.1] using hz.2
  rw [← hfg, ← hz.1, ← sub_eq_zero, ← norm_le_zero_iff]
  exact hgz

end Rouche

end HomologicalOrientation

end TauCeti
