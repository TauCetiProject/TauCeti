/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain
public import TauCeti.Topology.WedgeSum

/-!
# Points with no Euclidean neighbourhood

A topological manifold without boundary is a space in which every point has an open
neighbourhood homeomorphic to a Euclidean space. This file shows that two basic compact spaces
built from manifolds fail this at particular points, whatever the dimension of the Euclidean space:

* a point on the boundary sphere of a closed ball `closedBall c r`, `r ≠ 0`, in a
  finite-dimensional real normed space has no open neighbourhood in the ball homeomorphic to a
  finite-dimensional real normed space (`TauCeti.isEmpty_homeomorph_of_mem_sphere`);
* the wedge point of a wedge sum (`TauCeti.WedgeSum`) of at least two manifolds, all modelled on a
  real normed space of positive finite dimension, has no open neighbourhood homeomorphic to a
  finite-dimensional real normed space (`TauCeti.WedgeSum.isEmpty_homeomorph_of_base_mem`).

Hence neither space is the union of two open sets homeomorphic to `ℝᵐ`
(`TauCeti.not_exists_two_euclidean_opens_closedBall`,
`TauCeti.WedgeSum.not_exists_two_euclidean_opens`). A compact Hausdorff space with such a cover,
`m > 0`, is homeomorphic to the sphere `Sᵐ`
(`TauCeti.nonempty_homeomorph_sphere_of_two_euclidean_opens`). The closed ball `Dᵐ` and the wedge
`Sᵐ ∨ Sᵐ` of two spheres (`TauCeti.WedgeSum.not_exists_two_euclidean_opens_sphere`), for `m > 0`,
are compact Hausdorff spaces which are not spheres, and what they lack is exactly such a cover.

Both proofs rest on invariance of domain.

* If a boundary point `x` of the closed ball had a neighbourhood `U` homeomorphic to `ℝᵐ`, then
  `U`, as the image of `ℝᵐ` in `E`, would be open in `E` by the global form of invariance of domain
  (`Continuous.isOpenEmbedding_of_injective`), so `x` would lie in the interior of the ball, which
  is the open ball.
* The wedge argument uses a form for maps into a space which is only known to be Euclidean near
  the image (`IsOpen.image_of_continuousOn_of_injOn_of_mapsTo`): if an open subset `U` of a space
  `X` is homeomorphic to a manifold of dimension `m`, then a continuous injection of an open subset
  of another manifold of dimension `m` into `U` has open image in `X`. If the wedge point had a
  neighbourhood `U` homeomorphic to `ℝᵐ`, then the charts of two distinct summands at their base
  points would carry open subsets of `ℝᵐ` onto two neighbourhoods of the wedge point. These meet
  only in the wedge point, which would be isolated, while no point of `ℝᵐ` is isolated for `m > 0`.

When the dimension of the neighbourhood might differ from that of the ball or of the summands,
invariance of dimension (`Topology.IsOpenEmbedding.finrank_eq`), applied to an open set away
from the special point, shows that the two dimensions agree.

## Main results

* `TauCeti.isEmpty_homeomorph_of_mem_sphere`: a boundary point of a closed ball has no open
  neighbourhood in the ball homeomorphic to a finite-dimensional real normed space.
* `TauCeti.not_exists_two_euclidean_opens_closedBall`: a closed ball of positive radius in a space
  of positive dimension is not the union of two open sets homeomorphic to a finite-dimensional real
  normed space.
* `TauCeti.WedgeSum.isEmpty_homeomorph_of_base_mem`: the wedge point of a wedge of at least two
  manifolds of positive dimension has no open neighbourhood homeomorphic to a finite-dimensional
  real normed space.
* `TauCeti.WedgeSum.not_exists_two_euclidean_opens`,
  `TauCeti.WedgeSum.not_exists_two_euclidean_opens_sphere`: such a wedge, for instance `Sᵐ ∨ Sᵐ`
  with `m > 0`, is not the union of two open sets homeomorphic to a finite-dimensional real normed
  space.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 2B.3 (invariance
  of domain).
* J. Milnor, *Sommes de variétés différentiables et structures différentiables des sphères*,
  Bull. Soc. Math. France 87 (1959), 439–444, Theorem 1 and Corollary 1, for the recognition of
  spheres by covers with two Euclidean open sets.
-/

public section

open Function Metric Module Set Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

namespace TauCeti

/-- A space has no cover by two open sets homeomorphic to `F` when some point `p` has no open
neighbourhood homeomorphic to `F`: `p` lies in one of the two sets. -/
private theorem not_exists_two_opens_of_isEmpty_homeomorph {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] (p : X) (h : ∀ U : Set X, IsOpen U → p ∈ U → IsEmpty (U ≃ₜ G)) :
    ¬∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ U ∪ V = univ ∧ Nonempty (U ≃ₜ G) ∧
      Nonempty (V ≃ₜ G) := by
  rintro ⟨U, V, hU, hV, hUV, ⟨eU⟩, ⟨eV⟩⟩
  rcases (hUV ▸ mem_univ p : p ∈ U ∪ V) with hp | hp
  · exact (h U hU hp).false eU
  · exact (h V hV hp).false eV

/-! ### The closed ball -/

/-- **A boundary point of a closed ball has no Euclidean neighbourhood.** Let `x` be a point at
distance `r ≠ 0` from `c` in a finite-dimensional real normed space `E`. Then no open
neighbourhood of `x` in the closed ball `closedBall c r` is homeomorphic to a finite-dimensional
real normed space `F`, of any dimension. -/
theorem isEmpty_homeomorph_of_mem_sphere {c : E} {r : ℝ} (hr : r ≠ 0) {U : Set (closedBall c r)}
    (hU : IsOpen U) {x : closedBall c r} (hxU : x ∈ U) (hx : (x : E) ∈ sphere c r) :
    IsEmpty (U ≃ₜ F) := by
  refine ⟨fun e ↦ ?_⟩
  obtain ⟨G, hG, hGU⟩ := isOpen_induced_iff.1 hU
  -- Near `x`, the set `U` meets the open ball, where it is open in `E`; so `F` and `E` have the
  -- same dimension.
  have hEF : finrank ℝ E = finrank ℝ F := by
    have hxG : (x : E) ∈ G := by
      rw [← hGU] at hxU
      exact hxU
    have hcl : (x : E) ∈ closure (ball c r) := by
      rw [closure_ball c hr]
      exact x.property
    obtain ⟨y, hyG, hyB⟩ := mem_closure_iff.1 hcl G hG hxG
    let V : Set U := {u | ((u : closedBall c r) : E) ∈ ball c r}
    have hV : IsOpen V :=
      isOpen_ball.preimage (continuous_subtypeVal.comp continuous_subtypeVal)
    have : Nonempty V := ⟨⟨⟨⟨y, ball_subset_closedBall hyB⟩, hGU ▸ hyG⟩, hyB⟩⟩
    refine IsOpenEmbedding.finrank_eq (f := fun v : V ↦ (((v : U) : closedBall c r) : E))
      ⟨IsEmbedding.subtypeVal.comp (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal), ?_⟩
      (e.isOpenEmbedding.comp hV.isOpenEmbedding_subtypeVal)
    have hrange : range (fun v : V ↦ (((v : U) : closedBall c r) : E)) = G ∩ ball c r := by
      ext z
      constructor
      · rintro ⟨⟨⟨⟨z, hz⟩, hzU⟩, hzB⟩, rfl⟩
        rw [← hGU] at hzU
        exact ⟨hzU, hzB⟩
      · rintro ⟨hzG, hzB⟩
        exact ⟨⟨⟨⟨z, ball_subset_closedBall hzB⟩, hGU ▸ hzG⟩, hzB⟩, rfl⟩
    rw [hrange]
    exact hG.inter isOpen_ball
  -- The copy of `F` in `E` is open, so it lies in the interior of the closed ball, the open ball.
  have hopen : IsOpen (range fun v : F ↦ ((e.symm v : closedBall c r) : E)) :=
    (Continuous.isOpenEmbedding_of_injective (by fun_prop)
      (fun v w h ↦ e.symm.injective (Subtype.ext (Subtype.ext h))) hEF.symm).isOpen_range
  have hsub : (range fun v : F ↦ ((e.symm v : closedBall c r) : E)) ⊆ ball c r := by
    rw [← interior_closedBall c hr]
    exact interior_maximal (range_subset_iff.2 fun v ↦ (e.symm v : closedBall c r).property) hopen
  have hxB : (x : E) ∈ ball c r := hsub ⟨e ⟨x, hxU⟩, by simp⟩
  exact (mem_ball.1 hxB).ne (mem_sphere.1 hx)

omit [FiniteDimensional ℝ E] in
/-- **A closed ball is not covered by two Euclidean open sets.** A closed ball of positive radius
in a real normed space `E` of positive finite dimension is not the union of two open sets
homeomorphic to a finite-dimensional real normed space `F`: a point of its boundary sphere lies in
one of them. -/
theorem not_exists_two_euclidean_opens_closedBall (hE : 0 < finrank ℝ E) (c : E) {r : ℝ}
    (hr : 0 < r) :
    ¬∃ U V : Set (closedBall c r), IsOpen U ∧ IsOpen V ∧ U ∪ V = univ ∧ Nonempty (U ≃ₜ F) ∧
      Nonempty (V ≃ₜ F) := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos hE
  have : Nontrivial E := Module.nontrivial_of_finrank_pos hE
  obtain ⟨y, hy⟩ := (NormedSpace.sphere_nonempty (x := c)).2 hr.le
  exact not_exists_two_opens_of_isEmpty_homeomorph ⟨y, sphere_subset_closedBall hy⟩
    fun _ hU hz ↦ isEmpty_homeomorph_of_mem_sphere hr.ne' hU hz hy

/-! ### The wedge of manifolds -/

namespace WedgeSum

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace E (X i)]
  {x : ∀ i, X i} {U : Set (WedgeSum x)}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The chart of the summand `k` at its base point, read in the wedge sum. On the open set of
points of its target which it carries into an open neighbourhood `U` of the wedge point, the map
`y ↦ incl x k (chart⁻¹ y)` is continuous and injective with values in `U`, and the centre of the
chart lies in this set. -/
private theorem exists_chart (k : ι) (hU : IsOpen U) (hb : base x ∈ U) :
    ∃ W : Set E, IsOpen W ∧ W ⊆ (chartAt E (x k)).target ∧ chartAt E (x k) (x k) ∈ W ∧
      ContinuousOn (fun y ↦ incl x k ((chartAt E (x k)).symm y)) W ∧
      InjOn (fun y ↦ incl x k ((chartAt E (x k)).symm y)) W ∧
      MapsTo (fun y ↦ incl x k ((chartAt E (x k)).symm y)) W U := by
  refine ⟨(chartAt E (x k)).target ∩ (chartAt E (x k)).symm ⁻¹' (incl x k ⁻¹' U),
    (chartAt E (x k)).isOpen_inter_preimage_symm (hU.preimage (incl x k).continuous),
    inter_subset_left, ⟨(chartAt E (x k)).map_source (mem_chart_source E (x k)), ?_⟩,
    (incl x k).continuous.comp_continuousOn
      ((chartAt E (x k)).continuousOn_symm.mono inter_subset_left),
    fun y hy z hz h ↦ (chartAt E (x k)).symm.injOn hy.1 hz.1 (incl_injective k h),
    fun _ hy ↦ hy.2⟩
  rw [mem_preimage, mem_preimage, (chartAt E (x k)).left_inv (mem_chart_source E (x k)),
    incl_apply_self]
  exact hb

/-- Away from its base point, a summand is an open part of the wedge sum which is a manifold
modelled on `E`. So if an open neighbourhood `U` of the wedge point is homeomorphic to a
finite-dimensional real normed space `F`, then `F` has the dimension of a nontrivial `E`, by
invariance of dimension. -/
private theorem finrank_eq_of_base_mem [Nontrivial E] (i : ι) (hU : IsOpen U)
    (hb : base x ∈ U) (e : U ≃ₜ F) : finrank ℝ E = finrank ℝ F := by
  obtain ⟨W, hW, hWt, hpW, hφc, hφinj, hmaps⟩ := exists_chart (E := E) i hU hb
  set φ := fun y ↦ incl x i ((chartAt E (x i)).symm y)
  set p := chartAt E (x i) (x i)
  let V : Set E := W ∩ {p}ᶜ
  have hV : IsOpen V := hW.inter isOpen_compl_singleton
  obtain ⟨y, hy⟩ : V.Nonempty :=
    (Filter.nonempty_of_mem (inter_mem_nhdsWithin {p}ᶜ (hW.mem_nhds hpW))).mono
      fun z (hz : z ∈ ({p}ᶜ : Set E) ∩ W) ↦ ⟨hz.2, hz.1⟩
  have : Nonempty V := ⟨⟨y, hy⟩⟩
  -- The images of open subsets of `V` avoid the base point of the summand, so they are open.
  have hopen {O : Set E} (hO : IsOpen O) (hOV : O ⊆ V) : IsOpen (φ '' O) := by
    rw [← image_image]
    refine isOpen_image_incl ((chartAt E (x i)).isOpen_image_symm_of_subset_target hO
      fun z (hz : z ∈ O) ↦ hWt (hOV hz).1) ?_
    rintro ⟨z, hz, hzx⟩
    refine (hOV hz).2 ?_
    rw [mem_singleton_iff, ← (chartAt E (x i)).right_inv (hWt (hOV hz).1), hzx]
  -- So the chart identifies `V` with an open subset of `U`.
  let g : V → U := fun v ↦ ⟨φ v, hmaps v.property.1⟩
  have hg : IsOpenEmbedding g := by
    refine .of_continuous_injective_isOpenMap
      ((hφc.mono inter_subset_left).domRestrict.subtype_mk _)
      (fun v w h ↦ Subtype.ext (hφinj v.property.1 w.property.1 (congrArg Subtype.val h)))
      fun O hO ↦ ?_
    obtain ⟨O', hO', rfl⟩ := isOpen_induced_iff.1 hO
    have himage : g '' (Subtype.val ⁻¹' O') = Subtype.val ⁻¹' (φ '' (O' ∩ V)) := by
      ext u
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v, ⟨hv, v.property⟩, rfl⟩
      · rintro ⟨z, ⟨hzO, hzV⟩, hz⟩
        exact ⟨⟨z, hzV⟩, hzO, Subtype.ext hz⟩
    rw [himage]
    exact (hopen (hO'.inter hV) inter_subset_right).preimage continuous_subtypeVal
  exact IsOpenEmbedding.finrank_eq hV.isOpenEmbedding_subtypeVal (e.isOpenEmbedding.comp hg)

omit [FiniteDimensional ℝ E] in
/-- **The wedge point of manifolds has no Euclidean neighbourhood.** Let `X i` be topological
manifolds without boundary, all charted on a real normed space `E` of positive finite dimension,
with base points `x i`, and let `i ≠ j` be two of the indices. Then no open neighbourhood of the
wedge point in the wedge sum of the `X i` is homeomorphic to a finite-dimensional real normed
space `F`, of any dimension. -/
theorem isEmpty_homeomorph_of_base_mem (hE : 0 < finrank ℝ E) {i j : ι} (hij : i ≠ j)
    (hU : IsOpen U) (hb : base x ∈ U) : IsEmpty (U ≃ₜ F) := by
  refine ⟨fun e ↦ ?_⟩
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos hE
  have : Nontrivial E := Module.nontrivial_of_finrank_pos hE
  have hEF := finrank_eq_of_base_mem (E := E) i hU hb e
  -- By invariance of domain, the charts of a summand at its base point carry an open set of `E`
  -- onto a neighbourhood of the wedge point inside that summand.
  have hnhds (k : ι) : ∃ S ∈ 𝓝 (base x), S ⊆ range (incl x k) := by
    obtain ⟨W, hW, -, hpW, hφc, hφinj, hmaps⟩ := exists_chart (E := E) k hU hb
    refine ⟨_, (hW.image_of_continuousOn_of_injOn_of_mapsTo hU e hφc hφinj hmaps hEF).mem_nhds
      ⟨_, hpW, ?_⟩, image_subset_range _ _ |>.trans (range_comp_subset_range _ _)⟩
    simp [(chartAt E (x k)).left_inv (mem_chart_source E (x k))]
  -- The neighbourhoods of the summands `i` and `j` meet only in the wedge point, which is
  -- therefore isolated.
  obtain ⟨S, hS, hSi⟩ := hnhds i
  obtain ⟨T, hT, hTj⟩ := hnhds j
  have hsingle : {base x} ∈ 𝓝 (base x) := by
    refine Filter.mem_of_superset (Filter.inter_mem hS hT) fun z ⟨hzS, hzT⟩ ↦ ?_
    obtain ⟨a, rfl⟩ := hSi hzS
    obtain ⟨b, hab⟩ := hTj hzT
    obtain ⟨-, rfl⟩ | h := incl_eq_incl_iff.1 hab
    · exact incl_apply_self i
    · exact absurd (congrArg Sigma.fst h).symm hij
  have hbase : IsOpen ({base x} : Set (WedgeSum x)) := isOpen_iff_mem_nhds.2 fun z hz ↦ by
    rw [mem_singleton_iff.1 hz]
    exact hsingle
  -- But `F`, of the positive dimension of `E`, has no isolated point.
  have : Nontrivial F := Module.nontrivial_of_finrank_pos (hEF ▸ hE)
  have hpre : (Subtype.val ⁻¹' {base x} : Set U) = {⟨base x, hb⟩} := by
    ext u
    simp [Subtype.ext_iff]
  refine not_isOpen_singleton (e ⟨base x, hb⟩) ?_
  rw [← image_singleton, ← hpre]
  exact e.isOpenMap _ (hbase.preimage continuous_subtypeVal)

omit [FiniteDimensional ℝ E] in
/-- **A wedge of manifolds is not covered by two Euclidean open sets.** Let `X i` be topological
manifolds without boundary, all charted on a real normed space `E` of positive finite dimension,
with base points `x i`, and let `i ≠ j` be two of the indices. Then the wedge sum of the `X i` is
not the union of two open sets homeomorphic to a finite-dimensional real normed space `F`: the
wedge point lies in one of them. -/
theorem not_exists_two_euclidean_opens (hE : 0 < finrank ℝ E) {i j : ι} (hij : i ≠ j) :
    ¬∃ U V : Set (WedgeSum x), IsOpen U ∧ IsOpen V ∧ U ∪ V = univ ∧ Nonempty (U ≃ₜ F) ∧
      Nonempty (V ≃ₜ F) :=
  not_exists_two_opens_of_isEmpty_homeomorph (base x) fun _ hU hb ↦
    isEmpty_homeomorph_of_base_mem hE hij hU hb

omit [FiniteDimensional ℝ E] in
/-- **The wedge `Sᵐ ∨ Sᵐ` of two spheres is not covered by two Euclidean open sets**, for `m > 0`.
Here the spheres are the unit sphere of an inner product space `G` of dimension `m + 1`, with base
points `v 0` and `v 1`, and `F` is any finite-dimensional real normed space. -/
theorem not_exists_two_euclidean_opens_sphere {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] {m : ℕ} [Fact (finrank ℝ G = m + 1)] (hm : 0 < m)
    (v : Fin 2 → sphere (0 : G) 1) :
    ¬∃ U V : Set (WedgeSum v), IsOpen U ∧ IsOpen V ∧ U ∪ V = univ ∧ Nonempty (U ≃ₜ F) ∧
      Nonempty (V ≃ₜ F) :=
  not_exists_two_euclidean_opens (E := EuclideanSpace ℝ (Fin m)) (by simpa using hm)
    (i := 0) (j := 1) (by decide)

end WedgeSum

end TauCeti
