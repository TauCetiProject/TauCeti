/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import TauCeti.Analysis.Complex.RiemannSurface.Degree
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.Analysis.Complex.RiemannSurface.LocalNormalForm
import TauCeti.Analysis.Polynomial.RootSum

/-!
# Fibres counted with multiplicity, and symmetric functions of fibre values

Let `f : X → Y` be a map between Riemann surfaces. Its **fibre multiset** over `y`
(`TauCeti.RiemannSurface.fiberMultiset f y`) is the multiset of points of `f ⁻¹' {y}`, each repeated
according to the local multiplicity of `f` there. For a finite holomorphic map from a compact
connected Riemann surface to a connected one, it has as many elements as the degree of `f`,
whatever `y` is.

The main result of this file is that symmetric functions of the values of a holomorphic function
along the fibres vary holomorphically, also across the branch values of `f`. Precisely, let `g` be
holomorphic near the fibre of `f` over `y₀`. Then `y ↦ ∑ g(x)`, the sum running over the fibre
multiset of `y`, is holomorphic at `y₀` when read in a chart
(`TauCeti.RiemannSurface.analyticAt_sum_map_fiberMultiset`). By Newton's identities the same then
holds for the elementary symmetric functions of the values of `g` on the fibre multiset
(`TauCeti.RiemannSurface.analyticAt_esymm_map_fiberMultiset`), that is, for the coefficients of
`∏ (T - g(x))`.

At a point `x` of the fibre of local multiplicity `m`, the local normal form gives a chart at `x` in
which `f` becomes `w ↦ w ^ m` in the coordinate `z` of a chart at `y₀` centred at `y₀`. So the
points of the fibre of `y` near `x` are the images of the `m`-th roots of `z(y)`. Away from `y₀`
these are `m` distinct points of local multiplicity `1`, while at `y₀` they collide at `x`, which
has multiplicity `m`: in both cases the fibre multiset near `x` is the image of the multiset of
`m`-th roots of `z(y)`. Since `f` is a closed map, for `y` near `y₀` the whole fibre lies in these
charts. The sum of `g` over the `m`-th roots of `s` is analytic in `s` at `0` even though no single
root is (`TauCeti.analyticAt_sum_map_nthRoots`), which gives the result.

This is the analytic input of the classical proof that a meromorphic function on a compact Riemann
surface `X` satisfies a polynomial equation of degree `deg β` over the rational functions, for any
nonconstant holomorphic `β : X → OnePoint ℂ`: its coefficients are the elementary symmetric
functions of the values of the meromorphic function along the fibres of `β`.

## Main definitions

* `TauCeti.RiemannSurface.fiberMultiset f y`: the fibre of `f` over `y`, counted with local
  multiplicities.

## Main results

* `TauCeti.RiemannSurface.count_fiberMultiset` and `TauCeti.RiemannSurface.mem_fiberMultiset`: the
  multiplicity of a point in a finite fibre multiset is its local multiplicity.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.card_fiberMultiset`: every fibre multiset of a
  finite holomorphic map from a compact connected Riemann surface to a connected one has the
  degree as cardinality.
* `TauCeti.RiemannSurface.analyticAt_sum_map_fiberMultiset`: sums of a holomorphic function over
  the fibre multisets are holomorphic on the target, across branch values included.
* `TauCeti.RiemannSurface.analyticAt_esymm_map_fiberMultiset`: the same for the elementary
  symmetric functions of the values.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §8, Theorem 8.2 (the elementary symmetric functions of the values of a function along the fibres
  of a branched covering are holomorphic, with the fibres counted with multiplicity).
* Ernesto Girondo and Gabino González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  proof of Proposition 1.89.
-/

public noncomputable section

open Filter Function IsManifold Polynomial Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
  [ChartedSpace ℂ Y] {f : X → Y} {y : Y}

/-! ### The fibre multiset -/

/-- The **fibre multiset** of `f` over `y`: the points of the fibre `f ⁻¹' {y}`, each repeated
according to the local multiplicity of `f` at it. It is the fibre counted with multiplicities, so
for a finite fibre its cardinality is `TauCeti.RiemannSurface.fiberMultiplicitySum f y`
(`TauCeti.RiemannSurface.card_fiberMultiset`). By the convention for `finsum`, it is `0` when
infinitely many points of the fibre have nonzero local multiplicity. -/
def fiberMultiset (f : X → Y) (y : Y) : Multiset X :=
  ∑ᶠ x ∈ f ⁻¹' {y}, Multiset.replicate (localMultiplicity f x) x

theorem fiberMultiset_def (f : X → Y) (y : Y) :
    fiberMultiset f y = ∑ᶠ x ∈ f ⁻¹' {y}, Multiset.replicate (localMultiplicity f x) x :=
  (rfl)

/-- Over a finite fibre, the fibre multiset is a finite sum. -/
theorem fiberMultiset_eq_sum (hy : (f ⁻¹' {y}).Finite) :
    fiberMultiset f y = ∑ x ∈ hy.toFinset, Multiset.replicate (localMultiplicity f x) x :=
  finsum_mem_eq_finite_toFinset_sum _ hy

/-- In a finite fibre multiset, each point of the fibre occurs as often as its local multiplicity,
and no other point occurs. -/
theorem count_fiberMultiset [DecidableEq X] [DecidableEq Y] (hy : (f ⁻¹' {y}).Finite) (x : X) :
    (fiberMultiset f y).count x = if f x = y then localMultiplicity f x else 0 := by
  rw [fiberMultiset_eq_sum hy, Multiset.count_sum']
  simp only [Multiset.count_replicate, Finset.sum_ite_eq', Set.Finite.mem_toFinset, mem_preimage,
    mem_singleton_iff]

/-- The points of a finite fibre multiset are the points of the fibre of positive local
multiplicity. -/
theorem mem_fiberMultiset (hy : (f ⁻¹' {y}).Finite) {x : X} :
    x ∈ fiberMultiset f y ↔ f x = y ∧ 0 < localMultiplicity f x := by
  classical
  rw [← Multiset.count_pos, count_fiberMultiset hy]
  split_ifs with h <;> simp [h]

/-- A finite fibre multiset has the fibre sum of local multiplicities as its cardinality. -/
theorem card_fiberMultiset (hy : (f ⁻¹' {y}).Finite) :
    Multiset.card (fiberMultiset f y) = fiberMultiplicitySum f y := by
  rw [fiberMultiset_eq_sum hy, fiberMultiplicitySum_eq_sum hy, Multiset.card_sum]
  simp only [Multiset.card_replicate]

variable [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]

/-- **The fibre multisets of a finite holomorphic map have the degree as cardinality.** -/
theorem FiniteHolomorphicMap.card_fiberMultiset [CompactSpace X] [T2Space X] [T2Space Y]
    [PreconnectedSpace X] [PreconnectedSpace Y] (f : FiniteHolomorphicMap X Y) (y : Y) :
    Multiset.card (fiberMultiset f y) = degree f := by
  rw [RiemannSurface.card_fiberMultiset (f.finite_fiber y),
    fiberMultiplicitySum_eq_sum (f.finite_fiber y), degree_eq_fiber_sum f y]

/-! ### The fibre multiset in local normal form -/

/-- **The fibre multiset in a normal-form chart.** Let `f` be holomorphic and nonconstant near a
point `x` of local multiplicity `m`, and let `e'` be a chart at `f x`. There is a chart `e` at `x`,
inside any prescribed neighbourhood of `x`, such that for `z` near the coordinate of `f x` the
points of the fibre of `e'.symm z` in the domain of `e`, counted with local multiplicity, are the
images under `e.symm` of the `m`-th roots of `z - e' (f x)`. -/
private theorem exists_chart_sum_replicate_inter_source_eq {x : X}
    (hf : ∀ᶠ x' in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x') (hne : ¬ EventuallyConst f (𝓝 x))
    {e' : OpenPartialHomeomorph Y ℂ} (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 Y) (hfx : f x ∈ e'.source)
    {W : Set X} (hW : W ∈ 𝓝 x) :
    ∃ e : OpenPartialHomeomorph X ℂ, e ∈ maximalAtlas 𝓘(ℂ) 1 X ∧ x ∈ e.source ∧ e x = 0 ∧
      e.source ⊆ W ∧ ∀ᶠ z in 𝓝 (e' (f x)),
        ∑ᶠ x' ∈ f ⁻¹' {e'.symm z} ∩ e.source,
            Multiset.replicate (localMultiplicity f x') x' =
          (nthRoots (localMultiplicity f x) (z - e' (f x))).map e.symm := by
  set m := localMultiplicity f x
  have hm : 0 < m := (localMultiplicity_pos_iff hf).2 hne
  -- Shrink `W` so that every point of it other than `x` has local multiplicity `1`.
  have hW' : W ∩ {x' | x' = x ∨ localMultiplicity f x' = 1} ∈ 𝓝 x := by
    refine inter_mem hW ?_
    filter_upwards [eventually_nhdsWithin_iff.1 (eventually_localMultiplicity_eq_one hf hne)]
      with x' hx'
    by_cases h : x' = x
    · exact Or.inl h
    · exact Or.inr (hx' h)
  obtain ⟨e, he, hxe, hex, hsrc, hpow⟩ :=
    exists_chart_eq_pow_localMultiplicity hf hne he' hfx hW'
  refine ⟨e, he, hxe, hex, hsrc.trans inter_subset_left, ?_⟩
  set c := e' (f x)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 e.open_target 0 (hex ▸ e.map_source hxe)
  filter_upwards [e'.open_target.mem_nhds (e'.map_source hfx),
    Metric.ball_mem_nhds c (pow_pos hr m)] with z hz hzr
  set s := z - c
  -- The `m`-th roots of `s` lie in the target of `e`.
  have hroot (w : ℂ) (hw : w ^ m = s) : w ∈ e.target := by
    refine hball ?_
    rw [Metric.mem_ball, dist_zero_right]
    refine lt_of_pow_lt_pow_left₀ m hr.le ?_
    rw [← norm_pow, hw]
    simpa [s, dist_eq_norm] using hzr
  -- The points of the fibre in the domain of `e` are those whose coordinate is an `m`-th root.
  have hmem (x' : X) : x' ∈ f ⁻¹' {e'.symm z} ∩ e.source ↔ x' ∈ e.source ∧ e x' ^ m = s := by
    refine ⟨fun ⟨h1, h2⟩ ↦ ⟨h2, ?_⟩, fun ⟨h2, h1⟩ ↦ ⟨?_, h2⟩⟩
    · have h := (hpow x' h2).2
      rw [mem_preimage, mem_singleton_iff] at h1
      rw [h1, e'.right_inv hz] at h
      exact h.symm
    · have h := hpow x' h2
      rw [mem_preimage, mem_singleton_iff, ← e'.left_inv h.1]
      congr 1
      linear_combination h.2 + h1
  have hpiece (x' : X) (hx' : x' ∈ f ⁻¹' {e'.symm z} ∩ e.source) :
      x' = e.symm (e x') := (e.left_inv ((hmem x').1 hx').1).symm
  rcases eq_or_ne s 0 with hs | hs
  · -- Over `f x` itself the piece of the fibre is `{x}`, of multiplicity `m`, and the `m`-th
    -- roots of `0` all vanish.
    have hx : f ⁻¹' {e'.symm z} ∩ e.source = {x} := by
      ext x'
      rw [hmem, mem_singleton_iff]
      refine ⟨fun ⟨h2, h⟩ ↦ e.injOn h2 hxe ?_, fun h ↦ ⟨h ▸ hxe, by rw [h, hex, hs,
        zero_pow hm.ne']⟩⟩
      rw [hex]
      exact pow_eq_zero_iff hm.ne' |>.1 (h.trans hs)
    rw [hx, finsum_mem_singleton, hs, nthRoots_zero_right, Multiset.map_replicate, ← hex,
      e.left_inv hxe]
  · -- Away from `f x` the piece consists of points of multiplicity `1`, one for each of the `m`
    -- distinct `m`-th roots of `s`.
    have hmult (x' : X) (hx' : x' ∈ f ⁻¹' {e'.symm z} ∩ e.source) :
        localMultiplicity f x' = 1 := by
      obtain ⟨h2, h⟩ := (hmem x').1 hx'
      refine (hsrc h2).2.resolve_left fun h' ↦ hs ?_
      rw [← h, h', hex, zero_pow hm.ne']
    have hfin : (f ⁻¹' {e'.symm z} ∩ e.source).Finite := by
      refine ((nthRootsFinset m s).finite_toSet.image e.symm).subset fun x' hx' ↦ ?_
      exact ⟨e x', by simpa [mem_nthRootsFinset hm] using ((hmem x').1 hx').2,
        (hpiece x' hx').symm⟩
    rw [finsum_mem_congr rfl fun x' hx' ↦ by rw [hmult x' hx', Multiset.replicate_one],
      finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_eq_multiset_sum,
      Multiset.sum_map_singleton]
    have hnodup : (nthRoots m s).Nodup :=
      (Complex.isPrimitiveRoot_exp m hm.ne').nthRoots_nodup hs
    refine (Multiset.Nodup.ext hfin.toFinset.nodup (hnodup.map_on fun w hw w' hw' h ↦ ?_)).2
      fun x' ↦ ?_
    · rw [mem_nthRoots hm] at hw hw'
      exact e.symm.injOn (hroot w hw) (hroot w' hw') h
    · rw [Finset.mem_val, hfin.mem_toFinset, Multiset.mem_map]
      refine ⟨fun hx' ↦ ⟨e x', (mem_nthRoots hm).2 ((hmem x').1 hx').2, (hpiece x' hx').symm⟩,
        ?_⟩
      rintro ⟨w, hw, rfl⟩
      rw [mem_nthRoots hm] at hw
      rw [hmem, e.right_inv (hroot w hw)]
      exact ⟨e.map_target (hroot w hw), hw⟩

/-- **The fibre multisets near `y₀` in normal-form charts.** For a holomorphic map from a compact
Riemann surface which is constant near no point, and a chart `e'` at `y₀`, there are charts
`e x` centred at the points `x` of the fibre of `y₀` such that for `z` near `e' y₀` the fibre
multiset of `e'.symm z` is the sum over `x` of the images under `(e x).symm` of the `m`-th roots of
`z - e' y₀`, where `m` is the local multiplicity of `f` at `x`. -/
private theorem exists_charts_eventually_fiberMultiset_eq [CompactSpace X] [T2Space X]
    [T2Space Y] (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hne : ∀ x, ¬ EventuallyConst f (𝓝 x))
    {e' : OpenPartialHomeomorph Y ℂ} (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 Y) {y₀ : Y}
    (hy₀ : y₀ ∈ e'.source) :
    ∃ e : X → OpenPartialHomeomorph X ℂ,
      (∀ x ∈ f ⁻¹' {y₀}, e x ∈ maximalAtlas 𝓘(ℂ) 1 X ∧ x ∈ (e x).source ∧ e x x = 0) ∧
      ∀ᶠ z in 𝓝 (e' y₀), fiberMultiset f (e'.symm z) =
        ∑ᶠ x ∈ f ⁻¹' {y₀}, (nthRoots (localMultiplicity f x) (z - e' y₀)).map (e x).symm := by
  classical
  have hS : (f ⁻¹' {y₀}).Finite := finite_preimage_singleton hf hne y₀
  -- Pairwise disjoint open neighbourhoods of the finitely many points of the fibre of `y₀`, and
  -- normal-form charts inside them.
  obtain ⟨O, hO, hOdisj⟩ := hS.t2_separation
  have hloc : ∀ x ∈ f ⁻¹' {y₀}, ∃ e : OpenPartialHomeomorph X ℂ,
      (e ∈ maximalAtlas 𝓘(ℂ) 1 X ∧ x ∈ e.source ∧ e x = 0) ∧ e.source ⊆ O x ∧
      ∀ᶠ z in 𝓝 (e' y₀), ∑ᶠ x' ∈ f ⁻¹' {e'.symm z} ∩ e.source,
          Multiset.replicate (localMultiplicity f x') x' =
        (nthRoots (localMultiplicity f x) (z - e' y₀)).map e.symm := by
    intro x hx
    have hfx : f x = y₀ := hx
    obtain ⟨e, he, hxe, hex, hsub, hev⟩ := exists_chart_sum_replicate_inter_source_eq
      (.of_forall fun z ↦ hf z) (hne x) he' (hfx ▸ hy₀) ((hO x).2.mem_nhds (hO x).1)
    exact ⟨e, ⟨he, hxe, hex⟩, hsub, hfx ▸ hev⟩
  choose e₀ he₀ hsub₀ hev₀ using hloc
  -- Off the fibre of `y₀` the choice of chart is irrelevant.
  set e : X → OpenPartialHomeomorph X ℂ := fun x ↦
    if hx : x ∈ f ⁻¹' {y₀} then e₀ x hx else chartAt ℂ x
  have he_eq (x : X) (hx : x ∈ f ⁻¹' {y₀}) : e x = e₀ x hx := by
    have hfx : f x = y₀ := hx
    simp [e, hfx]
  have he (x : X) (hx : x ∈ f ⁻¹' {y₀}) :
      e x ∈ maximalAtlas 𝓘(ℂ) 1 X ∧ x ∈ (e x).source ∧ e x x = 0 := he_eq x hx ▸ he₀ x hx
  have hsub (x : X) (hx : x ∈ f ⁻¹' {y₀}) : (e x).source ⊆ O x := he_eq x hx ▸ hsub₀ x hx
  have hev (x : X) (hx : x ∈ f ⁻¹' {y₀}) : ∀ᶠ z in 𝓝 (e' y₀),
      ∑ᶠ x' ∈ f ⁻¹' {e'.symm z} ∩ (e x).source,
          Multiset.replicate (localMultiplicity f x') x' =
        (nthRoots (localMultiplicity f x) (z - e' y₀)).map (e x).symm :=
    he_eq x hx ▸ hev₀ x hx
  refine ⟨e, he, ?_⟩
  -- Outside the chart domains the map misses `y₀`, hence a whole neighbourhood of `y₀`.
  have hK : IsCompact (⋃ x ∈ f ⁻¹' {y₀}, (e x).source)ᶜ :=
    (isOpen_biUnion fun x _ ↦ (e x).open_source).isClosed_compl.isCompact
  have hyK : y₀ ∉ f '' (⋃ x ∈ f ⁻¹' {y₀}, (e x).source)ᶜ := by
    rintro ⟨x, hxK, hfx⟩
    exact hxK (mem_iUnion₂.2 ⟨x, hfx, (he x hfx).2.1⟩)
  have hV₀ : (f '' (⋃ x ∈ f ⁻¹' {y₀}, (e x).source)ᶜ)ᶜ ∈ 𝓝 y₀ :=
    (hK.image hf.continuous).isClosed.isOpen_compl.mem_nhds hyK
  have hsymm : Tendsto e'.symm (𝓝 (e' y₀)) (𝓝 y₀) := by
    have h := (e'.continuousAt_symm (e'.map_source hy₀)).tendsto
    rwa [e'.left_inv hy₀] at h
  filter_upwards [hsymm.eventually hV₀, hS.eventually_all.2 hev] with z hz hzev
  -- The fibre of `e'.symm z` is the disjoint union of its pieces inside the chart domains.
  have hfib : f ⁻¹' {e'.symm z} = ⋃ x ∈ f ⁻¹' {y₀}, (f ⁻¹' {e'.symm z} ∩ (e x).source) := by
    ext x'
    refine ⟨fun hx' ↦ ?_, fun hx' ↦ ?_⟩
    · have hx'U : x' ∈ ⋃ x ∈ f ⁻¹' {y₀}, (e x).source := by
        by_contra h
        exact hz ⟨x', h, hx'⟩
      obtain ⟨x, hx, hx'U⟩ := mem_iUnion₂.1 hx'U
      exact mem_iUnion₂.2 ⟨x, hx, hx', hx'U⟩
    · obtain ⟨x, -, hx'⟩ := mem_iUnion₂.1 hx'
      exact hx'.1
  have hdisj : (f ⁻¹' {y₀}).PairwiseDisjoint fun x ↦ f ⁻¹' {e'.symm z} ∩ (e x).source :=
    hOdisj.mono_on fun x hx ↦ inter_subset_right.trans (hsub x hx)
  have hfin := finite_preimage_singleton hf hne (e'.symm z)
  rw [fiberMultiset_def, hfib,
    finsum_mem_biUnion hdisj hS fun x _ ↦ hfin.subset inter_subset_left]
  exact finsum_mem_congr rfl hzev

/-! ### Holomorphy of symmetric functions of fibre values -/

section Holomorphy

variable [CompactSpace X] [T2Space X] [T2Space Y] (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
  (hne : ∀ x, ¬ EventuallyConst f (𝓝 x)) {e' : OpenPartialHomeomorph Y ℂ}
  (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 Y) {y₀ : Y} (hy₀ : y₀ ∈ e'.source) {g : X → ℂ}
  (hg : ∀ x ∈ f ⁻¹' {y₀}, ∀ᶠ x' in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g x')
include hf hne he' hy₀ hg

/-- **Sums along the fibres are holomorphic, across branch values.** Let `f` be a holomorphic map
from a compact Riemann surface which is constant near no point, and let `g` be holomorphic near the
fibre of `f` over `y₀`. Then the sum of the values of `g` over the fibre multiset of `y`, read in a
chart `e'` at `y₀`, is analytic at the coordinate of `y₀`. No hypothesis is made on the
ramification of `f` over `y₀`. -/
theorem analyticAt_sum_map_fiberMultiset :
    AnalyticAt ℂ (fun z ↦ ((fiberMultiset f (e'.symm z)).map g).sum) (e' y₀) := by
  obtain ⟨e, he, hev⟩ := exists_charts_eventually_fiberMultiset_eq hf hne he' hy₀
  have hS : (f ⁻¹' {y₀}).Finite := finite_preimage_singleton hf hne y₀
  refine AnalyticAt.congr (f := fun z ↦ ∑ x ∈ hS.toFinset,
      ((nthRoots (localMultiplicity f x) (z - e' y₀)).map (g ∘ (e x).symm)).sum)
    (Finset.analyticAt_fun_sum _ fun x hx ↦ ?_) ?_
  · rw [hS.mem_toFinset] at hx
    obtain ⟨hex, hxe, hx0⟩ := he x hx
    have hG : AnalyticAt ℂ (g ∘ (e x).symm) 0 := by
      simpa [hx0, chartAt_self_eq, Function.comp_def] using
        analyticAt_chart_comp_comp_symm hex (chart_mem_maximalAtlas (g x)) hxe
          (mem_chart_source ℂ (g x)) (hg x hx)
    exact (analyticAt_sum_map_nthRoots hG _).comp_of_eq (analyticAt_id.sub analyticAt_const)
      (sub_self _)
  · filter_upwards [hev] with z hz
    rw [hz, finsum_mem_eq_finite_toFinset_sum _ hS, ← Multiset.coe_mapAddMonoidHom, map_sum,
      ← Multiset.coe_sumAddMonoidHom, map_sum]
    simp only [Multiset.coe_mapAddMonoidHom, Multiset.coe_sumAddMonoidHom, Multiset.map_map]

/-- **Elementary symmetric functions of fibre values are holomorphic, across branch values.**
Under the hypotheses of `TauCeti.RiemannSurface.analyticAt_sum_map_fiberMultiset`, each elementary
symmetric function of the values of `g` on the fibre multiset of `y`, read in a chart at `y₀`, is
analytic at the coordinate of `y₀`. -/
theorem analyticAt_esymm_map_fiberMultiset (k : ℕ) :
    AnalyticAt ℂ (fun z ↦ ((fiberMultiset f (e'.symm z)).map g).esymm k) (e' y₀) :=
  analyticAt_esymm_of_forall_analyticAt_sum_map_pow k fun j _ _ ↦ by
    simpa only [Multiset.map_map, Function.comp_def] using
      analyticAt_sum_map_fiberMultiset hf hne he' hy₀ (g := fun x ↦ g x ^ j)
        fun x hx ↦ (hg x hx).mono fun _ h ↦ h.pow j

end Holomorphy

end TauCeti.RiemannSurface
