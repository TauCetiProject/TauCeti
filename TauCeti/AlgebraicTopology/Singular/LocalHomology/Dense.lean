/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Section

/-!
# Top-dimensional classes are determined on a dense set

Let `M` be a Hausdorff space modelled on a finite-dimensional real normed space, a topological
manifold without boundary. Every point `x` of `M` has a compact neighbourhood `B` such that the
restriction `Hₖ(M, M ∖ B) ⟶ Hₖ(M, M ∖ {y})` is an isomorphism for every `y ∈ B`
(`TauCeti.exists_isCompact_mem_nhds_isIso_localHomologyRestriction`). So the local classes of a
class `μ ∈ Hₖ(M)` at the points of `B` are all read off from a single class of `Hₖ(M, M ∖ B)`:
if `μ` vanishes in the local homology at the points of a set `D`, it vanishes there at every point
of the closure of `D` (`TauCeti.singularHomologyToLocalHomology_eq_zero_of_mem_closure`), and if
its local classes generate at the points of `D`, they generate at every point of the closure of
`D` (`TauCeti.span_singularHomologyToLocalHomology_eq_top_of_mem_closure`). The same holds for a
class `θ ∈ Hₖ(M, M ∖ U)` along an open set `U`, whose local classes are defined at the points of
`U`: choosing `B` inside `U`, the set of points of `U` where they vanish is open and closed in `U`,
so they vanish on a preconnected subset of `U` as soon as they vanish at one of its points
(`TauCeti.localHomologyRestriction_eq_zero_of_isPreconnected`).

On a compact manifold of dimension `n`, a class of `Hₙ(M)` is determined by its local classes
(`TauCeti.existsUnique_singularHomology_localHomologyRestriction_eq_of_invariant`). Hence it is
already determined by its local classes at the points of a dense set
(`TauCeti.singularHomology_ext_of_dense`), or by its images in the local homology groups
`Hₙ(M, M ∖ Uᵢ)` along a family of sets whose union is dense
(`TauCeti.singularHomology_ext_of_dense_iUnion`), and it is a fundamental class as soon as its
local classes generate at the points of a dense set (`TauCeti.isFundamentalClass_of_dense`).

These are the statements through which fundamental classes are assembled from the faces of a
decomposition. The boundary of a manifold with corners is the union of its faces, and the
interiors of the faces are dense in it. A cycle of the boundary which, near each point of the
interior of a face, agrees with a fundamental chain of that face, therefore represents the class
determined by these local classes, and no computation is needed at the corners, where several
faces meet.

## Main results

* `TauCeti.singularHomologyToLocalHomology_eq_zero_of_mem_closure`: the local classes of a class
  vanish on the closure of the set where they vanish.
* `TauCeti.localHomologyRestriction_eq_zero_of_isPreconnected`: the local classes of a class
  along an open set `U` vanish on a preconnected subset of `U` as soon as they vanish at one of its
  points.
* `TauCeti.singularHomology_ext_of_dense`: on a compact `n`-manifold, two classes of `Hₙ(M)` with
  the same local classes at the points of a dense set are equal.
* `TauCeti.singularHomology_ext_of_dense_iUnion`: the same for the images in `Hₙ(M, M ∖ Uᵢ)`,
  for a family of sets `Uᵢ` with dense union.
* `TauCeti.isFundamentalClass_of_dense`: a class whose local classes generate at the points of a
  dense set is a fundamental class.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.3, Lemma 3.27 and the topology of the orientation
  covering `M_R` by the groups `Hₙ(M | B)` for balls `B`.
* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Annals of
  Mathematics 166 (2007), Appendix A, where fundamental chains of compactified trajectory spaces
  are glued from the fundamental chains of their boundary faces.
-/

public section

noncomputable section

open CategoryTheory Module Set Topology

universe w

namespace TauCeti

variable {M E : Type w} [TopologicalSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]

section Closure

variable {Λ : Type*} [Ring Λ] (N : ModuleCat.{w} Λ)

/-- **The local classes of a class vanish on the closure of the set where they vanish.** If the
image of `μ ∈ Hₖ(M; N)` in the local homology `Hₖ(M, M ∖ {y}; N)` vanishes at every point `y` of
`D`, it vanishes at every point of the closure of `D`: near each point, the local classes are the
restrictions of a single class along a compact neighbourhood, to which every restriction is
isomorphic. -/
theorem singularHomologyToLocalHomology_eq_zero_of_mem_closure [T2Space M] [ChartedSpace E M]
    [FiniteDimensional ℝ E] {D : Set M} {x : M}
    (hx : x ∈ closure D) {k : ℕ}
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N k : ModuleCat.{w} Λ)}
    (hμ : ∀ y ∈ D, singularHomologyToLocalHomology N y k μ = 0) :
    singularHomologyToLocalHomology N x k μ = 0 := by
  obtain ⟨B, hB, -, hiso⟩ := exists_isCompact_mem_nhds_isIso_localHomologyRestriction (E := E) N x k
  obtain ⟨y, hyB, hyD⟩ := mem_closure_iff_nhds.1 hx B hB
  have hxB := mem_of_mem_nhds hB
  -- The image of `μ` along `B` restricts to zero at `y ∈ D`, so it is zero.
  have hβ : ((TopPair.ofSubset (Bᶜ : Set (TopCat.of M))).singularHomologyπ
      (C := ModuleCat.{w} Λ) N k).hom μ = 0 := by
    have := hiso y hyB
    apply (ModuleCat.mono_iff_injective
      (localHomologyRestriction N (singleton_subset_iff.2 hyB) k)).1 inferInstance
    rw [map_zero, ← singularHomologyToLocalHomology_eq_localHomologyRestriction N hyB, hμ y hyD]
  rw [singularHomologyToLocalHomology_eq_localHomologyRestriction N hxB, hβ, map_zero]

/-- **Generation of local classes passes to the closure.** If the image of `μ ∈ Hₖ(M; N)` in the
local homology `Hₖ(M, M ∖ {y}; N)` generates it at every point `y` of `D`, it generates it at
every point of the closure of `D`. -/
theorem span_singularHomologyToLocalHomology_eq_top_of_mem_closure [T2Space M]
    [ChartedSpace E M] [FiniteDimensional ℝ E] {D : Set M} {x : M}
    (hx : x ∈ closure D) {k : ℕ}
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N k : ModuleCat.{w} Λ)}
    (hμ : ∀ y ∈ D, Submodule.span Λ {singularHomologyToLocalHomology N y k μ} = ⊤) :
    Submodule.span Λ {singularHomologyToLocalHomology N x k μ} = ⊤ := by
  obtain ⟨B, hB, -, hiso⟩ := exists_isCompact_mem_nhds_isIso_localHomologyRestriction (E := E) N x k
  obtain ⟨y, hyB, hyD⟩ := mem_closure_iff_nhds.1 hx B hB
  have hxB := mem_of_mem_nhds hB
  set β := ((TopPair.ofSubset (Bᶜ : Set (TopCat.of M))).singularHomologyπ
    (C := ModuleCat.{w} Λ) N k).hom μ
  -- The class `β` along `B` generates, since an isomorphism carries it to a generator at `y`.
  have hβ : Submodule.span Λ {β} = ⊤ := by
    have := hiso y hyB
    refine (asIso (localHomologyRestriction N (singleton_subset_iff.2 hyB) k)).toLinearEquiv
      |>.span_singleton_apply_eq_top_iff.1 ?_
    rw [Iso.toLinearEquiv_apply, asIso_hom,
      ← singularHomologyToLocalHomology_eq_localHomologyRestriction N hyB]
    exact hμ y hyD
  have := hiso x hxB
  rw [singularHomologyToLocalHomology_eq_localHomologyRestriction N hxB]
  exact (asIso (localHomologyRestriction N (singleton_subset_iff.2 hxB) k)).toLinearEquiv
    |>.span_singleton_apply_eq_top_iff.2 hβ

/-- **The local classes of a class along an open set vanish on whole preconnected sets.** Let `U`
be an open subset of `M`, let `θ ∈ Hₖ(M, M ∖ U; N)`, and let `S ⊆ U` be preconnected. If the image
of `θ` in the local homology `Hₖ(M, M ∖ {x}; N)` vanishes at one point `x` of `S`, it vanishes at
every point of `S`: near each point of `U`, the local classes of `θ` are the restrictions of its
image along a compact neighbourhood inside `U`, to which every restriction is isomorphic, so the
set of points of `U` where they vanish is open and closed in `U`. -/
theorem localHomologyRestriction_eq_zero_of_isPreconnected [T2Space M] [ChartedSpace E M]
    [FiniteDimensional ℝ E] {U S : Set M} (hU : IsOpen U) (hS : IsPreconnected S) (hSU : S ⊆ U)
    {k : ℕ} {θ : (localHomology N U k : ModuleCat.{w} Λ)} {x y : M} (hx : x ∈ S) (hy : y ∈ S)
    (hθ : localHomologyRestriction N (singleton_subset_iff.2 (hSU hx)) k θ = 0) :
    localHomologyRestriction N (singleton_subset_iff.2 (hSU hy)) k θ = 0 := by
  -- Near a point `z` of `U`, the local class at `w` vanishes exactly when the local class at `z`
  -- does.
  have hloc (z : M) (hz : z ∈ U) : ∀ᶠ w in 𝓝 z, ∀ hw : w ∈ U,
      (localHomologyRestriction N (singleton_subset_iff.2 hw) k θ = 0 ↔
        localHomologyRestriction N (singleton_subset_iff.2 hz) k θ = 0) := by
    obtain ⟨B, hB, -, hBU, hiso⟩ :=
      exists_isCompact_subset_mem_nhds_isIso_localHomologyRestriction (E := E) N (hU.mem_nhds hz) k
    have hzero (w : M) (hwB : w ∈ B) (hw : w ∈ U) :
        localHomologyRestriction N (singleton_subset_iff.2 hw) k θ = 0 ↔
          localHomologyRestriction N hBU k θ = 0 := by
      have := hiso w hwB
      have hinj := (ModuleCat.mono_iff_injective
        (localHomologyRestriction N (singleton_subset_iff.2 hwB) k)).1 inferInstance
      rw [← localHomologyRestriction_comp_apply N (singleton_subset_iff.2 hwB) hBU]
      exact ⟨fun h ↦ hinj (h.trans (map_zero _).symm), fun h ↦ by rw [h, map_zero]⟩
    filter_upwards [hB] with w hwB hw
    rw [hzero w hwB hw, hzero z (mem_of_mem_nhds hB) hz]
  -- So vanishing of the local class is a locally constant condition on `S`.
  have := isPreconnected_iff_preconnectedSpace.1 hS
  let f : S → Prop := fun z ↦
    localHomologyRestriction N (singleton_subset_iff.2 (hSU z.property)) k θ = 0
  have hf : IsLocallyConstant f := by
    refine (IsLocallyConstant.iff_eventually_eq f).2 fun z ↦ ?_
    filter_upwards [(continuous_subtypeVal.tendsto z).eventually (hloc z (hSU z.property))]
      with w hw
    exact propext (hw (hSU w.property))
  exact Eq.mp (hf.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩) hθ

/-- **A class whose local classes generate on a dense set is a fundamental class.** If the image
of `μ ∈ Hₙ(M; N)` in the local homology `Hₙ(M, M ∖ {y}; N)` generates it at every point `y` of a
dense set, then `μ` is a fundamental class. -/
theorem isFundamentalClass_of_dense [T2Space M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    {D : Set M} (hD : Dense D) {n : ℕ}
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} Λ)}
    (hμ : ∀ y ∈ D, Submodule.span Λ {singularHomologyToLocalHomology N y n μ} = ⊤) :
    IsFundamentalClass μ :=
  (isFundamentalClass_iff μ).2 fun x ↦
    span_singularHomologyToLocalHomology_eq_top_of_mem_closure (E := E) N (hD x) hμ

end Closure

section Compact

variable {Λ : Type w} [Ring Λ] (N : ModuleCat.{w} Λ)

/-- **Top-dimensional classes of a compact manifold are determined on a dense set.** On a compact
manifold of dimension `n`, two classes of `Hₙ(M; N)` whose images in the local homology
`Hₙ(M, M ∖ {y}; N)` agree at every point `y` of a dense set are equal. -/
theorem singularHomology_ext_of_dense [T2Space M] [CompactSpace M] [ChartedSpace E M]
    [FiniteDimensional ℝ E] {n : ℕ} (hn : finrank ℝ E = n)
    {D : Set M} (hD : Dense D)
    {μ ν : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} Λ)}
    (h : ∀ y ∈ D, singularHomologyToLocalHomology N y n μ =
      singularHomologyToLocalHomology N y n ν) :
    μ = ν := by
  -- The difference has vanishing local classes everywhere, like `0`, so it is `0`.
  have hzero : ∀ x : M, singularHomologyToLocalHomology N x n (μ - ν) = 0 := fun x ↦
    singularHomologyToLocalHomology_eq_zero_of_mem_closure (E := E) N (hD x) fun y hy ↦ by
      rw [map_sub, h y hy, sub_self]
  obtain ⟨γ, -, huniq⟩ := existsUnique_singularHomology_localHomologyRestriction_eq_of_invariant
    (M := M) (E := E) N hn (fun _ ↦ 0) fun _ ↦ map_zero _
  exact sub_eq_zero.1 ((huniq _ hzero).trans (huniq 0 fun x ↦ map_zero _).symm)

/-- **Top-dimensional classes of a compact manifold are determined along a dense union.** On a
compact manifold of dimension `n`, let `(Uᵢ)` be a family of sets whose union is dense. Two classes
of `Hₙ(M; N)` with the same image in the local homology `Hₙ(M, M ∖ Uᵢ; N)` along each `Uᵢ` are
equal. For the interiors of the faces of a decomposition of `M`, this says that a class of `M` is
determined face by face. -/
theorem singularHomology_ext_of_dense_iUnion [T2Space M] [CompactSpace M] [ChartedSpace E M]
    [FiniteDimensional ℝ E] {n : ℕ} (hn : finrank ℝ E = n)
    {ι : Type*} {U : ι → Set M} (hU : Dense (⋃ i, U i))
    {μ ν : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} Λ)}
    (h : ∀ i, ((TopPair.ofSubset ((U i)ᶜ : Set (TopCat.of M))).singularHomologyπ
        (C := ModuleCat.{w} Λ) N n).hom μ =
      ((TopPair.ofSubset ((U i)ᶜ : Set (TopCat.of M))).singularHomologyπ
        (C := ModuleCat.{w} Λ) N n).hom ν) :
    μ = ν := by
  refine singularHomology_ext_of_dense (E := E) N hn hU fun y hy ↦ ?_
  -- The local class at `y ∈ Uᵢ` is the restriction of the image along `Uᵢ`.
  obtain ⟨i, hi⟩ := mem_iUnion.1 hy
  rw [singularHomologyToLocalHomology_eq_localHomologyRestriction N hi,
    singularHomologyToLocalHomology_eq_localHomologyRestriction N hi, h i]

end Compact

end TauCeti
