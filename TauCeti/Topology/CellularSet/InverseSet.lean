/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.Topology.CellularSet.Basic
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Separation.Connected
import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain
import TauCeti.AlgebraicTopology.Singular.JordanBrouwer
import TauCeti.Analysis.Normed.Module.Connected
import TauCeti.Topology.Separation.InvFunOn
import TauCeti.Topology.Sphere.Shrink

/-!
# Inverse sets of maps into a sphere are cellular

Let `Q` be the closed unit ball of a real normed space `E` of dimension `n ≥ 2`, and let `f` map
`Q` continuously into the unit sphere `Sⁿ` of a real inner product space of dimension `n + 1`.
Suppose that the fibre `X = Q ∩ f⁻¹(y)` over some point `y` is nonempty and lies in the open
ball, and that `f` is injective on `Q \ X`: in M. Brown's terminology, `X` is the only *inverse
set* of `f`. Then `X` is cellular in `E` (`TauCeti.isCellularSet_closedBall_inter_preimage`).
This is Theorem 3 of Brown's proof of the generalized Schoenflies theorem. The hypothesis `n ≥ 2`
is used only through the connectedness of punctured balls.

Brown deduces from it his Theorem 4: if a continuous surjection `g` of `Sⁿ` onto itself is
injective off the fibres over two points `p` and `q`, then both fibres are cellular in `Sⁿ`
(`TauCeti.isCellularSet_preimage_singleton`). With the collapse of cellular sets
(`TauCeti.IsCellularSet.exists_collapse`) this identifies the closures of the complementary domains
of a bicollared sphere with cells (his Theorem 5,
`TauCeti.IsBicollar.exists_homeomorph_closure_connectedComponentIn_compl_range`).

The proof has three steps.

* The sphere `f(∂Q)` separates `Sⁿ` by the Jordan–Brouwer theorem
  (`TauCeti.not_isPreconnected_compl_range_sphere`), while the open ball is mapped onto a connected
  set disjoint from it, so `f(Q) ≠ Sⁿ`.
* `f(Q)` is a neighbourhood of `y`. By invariance of domain `f(int Q \ X)` is open, since `f` is
  injective on the open set `int Q \ X`; on a neighbourhood `V` of `y` missing the closed set
  `f(∂Q)` it agrees with `f(Q) \ {y}`, so `f(Q) \ {y}` is both open and closed in `V \ {y}`. This
  punctured neighbourhood is connected when `n ≥ 2`, and it meets `f(Q)` because `X` has frontier
  points in `int Q`; so it lies in `f(Q)`.
* Given an open `U ⊇ X`, choose `p ∉ f(Q)` and read `Sⁿ \ {p}` in the stereographic chart. A
  radial squeeze about `y` which is the identity near `y`
  (`TauCeti.exists_continuousOn_injOn_mapsTo_sphere`) gives a map `k`, continuous and injective on
  `Sⁿ \ {p}`, carrying `f(Q)` into the neighbourhood `f(Q ∩ U)` of `y`. Then `g = f⁻¹ ∘ k ∘ f`
  on `Q \ X`, extended by the identity on `X`, is a continuous injection of `Q` into `U`: near
  `X` it is the identity, and elsewhere the inverse of `f` is continuous because `Q` is compact
  (`ContinuousOn.continuousOn_invFunOn_image_of_isCompact`). Its image is a cell containing `X` in
  its interior, and iterating with `U` shrinking to `X` exhibits `X` as cellular.

For Theorem 4, choose a point `z` whose image is neither `p` nor `q`. The inverse stereographic
projection from `z` gives a closed cell `ψ(Q)` of `Sⁿ` containing both fibres in its interior.
Choose a map `k` of the sphere which is the identity near `p`, continuous and injective off `g z`,
and moves `g(ψ(Q))` off `q`. Then the map `G` which is the identity on the fibre over `p` and
`g⁻¹ ∘ k ∘ g` elsewhere is continuous on `ψ(Q)`. On `ψ(Q)` its only inverse set is the fibre over
`q`, so Theorem 3 applied to `G ∘ ψ` shows that this fibre is cellular.

## Main results

* `TauCeti.isCellularSet_closedBall_inter_preimage`: **Brown's theorem on inverse sets**: the only
  inverse set of a map of an `n`-cell into `Sⁿ`, `n ≥ 2`, is cellular.
* `TauCeti.isCellularSet_preimage_singleton`: **Brown's theorem on two inverse sets**: the inverse
  sets of a map of `Sⁿ` onto itself, `n ≥ 2`, with at most two inverse sets are cellular.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorems 0, 3 and 4.
-/

public section

open Function Metric Module Set Filter Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → sphere (0 : F) 1} {y : sphere (0 : F) 1}

omit [InnerProductSpace ℝ F] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Two points of the closed ball with the same image under `f`, not in the fibre over `y`, are
equal, when `f` is injective off that fibre. -/
private theorem eq_of_apply_eq (hinj : InjOn f (closedBall 0 1 \ f ⁻¹' {y})) {x x' : E}
    (hx : x ∈ closedBall 0 1) (hx' : x' ∈ closedBall 0 1) (h : f x = f x') (hy : f x ≠ y) :
    x = x' :=
  hinj ⟨hx, hy⟩ ⟨hx', fun h' ↦ hy (h.trans h')⟩ h

/-- **The image of the closed ball is not the whole sphere.** By the Jordan–Brouwer separation
theorem the embedded sphere `f(∂Q)` separates `Sⁿ`, while `f` maps the open ball onto a connected
set disjoint from `f(∂Q)`. -/
private theorem exists_notMem_image_closedBall (hEF : finrank ℝ F = finrank ℝ E + 1)
    (hf : ContinuousOn f (closedBall 0 1)) (hinj : InjOn f (closedBall 0 1 \ f ⁻¹' {y}))
    (hy : y ∉ f '' sphere 0 1) : ∃ p, p ∉ f '' closedBall 0 1 := by
  by_contra! h
  have hne {x : E} (hx : x ∈ sphere (0 : E) 1) : f x ≠ y := fun h ↦ hy ⟨x, hx, h⟩
  have hc : Continuous fun x : sphere (0 : E) 1 ↦ f x :=
    hf.comp_continuous continuous_subtype_val fun x ↦ sphere_subset_closedBall x.2
  have hi : Injective fun x : sphere (0 : E) 1 ↦ f x := fun x x' h ↦ Subtype.ext <|
    eq_of_apply_eq hinj (sphere_subset_closedBall x.2) (sphere_subset_closedBall x'.2) h (hne x.2)
  -- The complement of `f(∂Q)` is the image of the open ball, which is connected.
  have hrange : (range fun x : sphere (0 : E) 1 ↦ f x)ᶜ = f '' ball 0 1 := by
    ext z
    refine ⟨fun hz ↦ ?_, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := h z
      refine ⟨x, ?_, rfl⟩
      rw [← closedBall_sdiff_sphere]
      exact ⟨hx, fun hxs ↦ hz ⟨⟨x, hxs⟩, rfl⟩⟩
    · rintro ⟨x, hx, rfl⟩ ⟨s, hs⟩
      exact sphere_disjoint_ball.ne_of_mem s.2 hx <| eq_of_apply_eq hinj
        (sphere_subset_closedBall s.2) (ball_subset_closedBall hx) hs (hne s.2)
  exact not_isPreconnected_compl_range_sphere hEF hc hi
    (hrange ▸ isPreconnected_ball.image f (hf.mono ball_subset_closedBall))

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ E] in
/-- Under the hypotheses of `TauCeti.isCellularSet_closedBall_inter_preimage`, the fibre over `y`
has a frontier point, and every neighbourhood of `y` contains the image of a point of the open ball
outside the fibre. -/
private theorem exists_mem_ball_apply_mem (hn : 2 ≤ finrank ℝ E)
    (hf : ContinuousOn f (closedBall 0 1)) (hy : y ∉ f '' sphere 0 1)
    (hy' : y ∈ f '' closedBall 0 1) {V : Set (sphere (0 : F) 1)} (hV : V ∈ 𝓝 y) :
    ∃ x ∈ ball (0 : E) 1, f x ≠ y ∧ f x ∈ V := by
  set X := closedBall (0 : E) 1 ∩ f ⁻¹' {y}
  have hX : IsClosed X := hf.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨v, hv⟩ := exists_norm_eq E zero_le_two
  have hXu : X ≠ univ := fun h ↦ by
    have := (h.symm ▸ mem_univ v : v ∈ X).1
    rw [mem_closedBall_zero_iff, hv] at this
    norm_num at this
  obtain ⟨m, hm⟩ := nonempty_frontier_iff.2 ⟨by obtain ⟨x, hx, rfl⟩ := hy'; exact ⟨x, hx, rfl⟩, hXu⟩
  have hmX : m ∈ X := hX.frontier_subset hm
  have hmb : m ∈ ball (0 : E) 1 := by
    rw [← closedBall_sdiff_sphere]
    exact ⟨hmX.1, fun h ↦ hy ⟨m, h, hmX.2⟩⟩
  -- The open set of points of the open ball mapped into the interior of `V` contains `m`, so it
  -- meets the complement of `X`.
  have hW : IsOpen (ball (0 : E) 1 ∩ f ⁻¹' interior V) :=
    (hf.mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball isOpen_interior
  have hmW : m ∈ ball (0 : E) 1 ∩ f ⁻¹' interior V :=
    ⟨hmb, by rw [mem_preimage, hmX.2]; exact mem_interior_iff_mem_nhds.2 hV⟩
  obtain ⟨x, ⟨hxb, hxV⟩, hxX⟩ :=
    mem_closure_iff.1 (frontier_eq_closure_inter_closure.subset hm).2 _ hW hmW
  exact ⟨x, hxb, fun h ↦ hxX ⟨ball_subset_closedBall hxb, h⟩, interior_subset hxV⟩

/-- **The image of the closed ball is a neighbourhood of `y`.** Off `y` the image of the open ball
minus the fibre is open by invariance of domain, so a connected punctured neighbourhood of `y`
missing `f(∂Q)` lies in `f(Q)` as soon as it meets it. -/
private theorem image_closedBall_mem_nhds (hn : 2 ≤ finrank ℝ E)
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hf : ContinuousOn f (closedBall 0 1))
    (hinj : InjOn f (closedBall 0 1 \ f ⁻¹' {y})) (hy : y ∉ f '' sphere 0 1)
    (hy' : y ∈ f '' closedBall 0 1) : f '' closedBall 0 1 ∈ 𝓝 y := by
  have : Fact (finrank ℝ F = finrank ℝ E + 1) := ⟨hEF⟩
  set n := finrank ℝ E
  have hS : IsClosed (f '' sphere 0 1) :=
    ((isCompact_sphere 0 1).image_of_continuousOn (hf.mono sphere_subset_closedBall)).isClosed
  have hQ : IsClosed (f '' closedBall 0 1) :=
    ((isCompact_closedBall 0 1).image_of_continuousOn hf).isClosed
  -- A neighbourhood `V` of `y` missing `f(∂Q)`, with `V \ {y}` connected.
  obtain ⟨V, hV, hVS, hVc⟩ := exists_mem_nhds_subset_isConnected_sdiff_singleton_of_mem_source
    (E := EuclideanSpace ℝ (Fin n))
    (by rw [← finrank_eq_rank, finrank_euclideanSpace_fin]; exact_mod_cast hn)
    (chartAt (EuclideanSpace ℝ (Fin n)) y) (mem_chart_source _ y) (hS.isOpen_compl.mem_nhds hy)
  -- The image of the open ball minus the fibre is open.
  set O := ball (0 : E) 1 ∩ f ⁻¹' {y}ᶜ
  have hOQ : O ⊆ closedBall 0 1 \ f ⁻¹' {y} := fun x hx ↦ ⟨ball_subset_closedBall hx.1, hx.2⟩
  have hO : IsOpen O :=
    (hf.mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have hfO : IsOpen (f '' O) :=
    hO.image_of_continuousOn_of_injOn (F := EuclideanSpace ℝ (Fin n))
      (hf.mono fun x hx ↦ (hOQ hx).1) (hinj.mono hOQ) finrank_euclideanSpace_fin.symm
  -- Every point of `V \ {y}` in `f(Q)` is the image of a point of `O`.
  have hcover : V \ {y} ⊆ f '' O ∪ (f '' closedBall 0 1)ᶜ := by
    rintro z ⟨hzV, hzy⟩
    by_cases hz : z ∈ f '' closedBall 0 1
    · obtain ⟨x, hx, rfl⟩ := hz
      refine .inl ⟨x, ⟨?_, hzy⟩, rfl⟩
      rw [← closedBall_sdiff_sphere]
      exact ⟨hx, fun h ↦ hVS hzV ⟨x, h, rfl⟩⟩
    · exact .inr hz
  obtain ⟨x, hxb, hxy, hxV⟩ := exists_mem_ball_apply_mem hn hf hy hy' hV
  have hsub : V \ {y} ⊆ f '' O := hVc.isPreconnected.subset_left_of_subset_union hfO
    hQ.isOpen_compl (disjoint_compl_right_iff_subset.2 (image_mono fun x hx ↦ (hOQ hx).1))
    hcover ⟨f x, ⟨hxV, hxy⟩, x, ⟨hxb, hxy⟩, rfl⟩
  refine mem_of_superset hV fun z hz ↦ ?_
  rcases eq_or_ne z y with rfl | hzy
  · exact hy'
  · exact image_mono (fun x hx ↦ (hOQ hx).1) (hsub ⟨hz, hzy⟩)

omit [InnerProductSpace ℝ F] in
/-- Off the fibre `X` over `y`, the map `f⁻¹ ∘ k ∘ f` is continuous on the closed ball `Q`, for a
map `k` continuous off a point `p ∉ f(Q)` which preserves `f(Q \ X)`: the inverse of `f` on
`Q \ X` is continuous since `Q` is compact. -/
private theorem continuousWithinAt_invFunOn_comp (hf : ContinuousOn f (closedBall 0 1))
    (hinj : InjOn f (closedBall 0 1 \ f ⁻¹' {y})) {p : sphere (0 : F) 1}
    (hp : p ∉ f '' closedBall 0 1) {k : sphere (0 : F) 1 → sphere (0 : F) 1}
    (hkc : ContinuousOn k {p}ᶜ)
    (hkP : ∀ x ∈ closedBall 0 1 \ f ⁻¹' {y}, k (f x) ∈ f '' (closedBall 0 1 \ f ⁻¹' {y}))
    {x : E} (hx : x ∈ closedBall 0 1 \ f ⁻¹' {y}) :
    ContinuousWithinAt (fun x ↦ invFunOn f (closedBall 0 1 \ f ⁻¹' {y}) (k (f x)))
      (closedBall 0 1 \ f ⁻¹' {y}) x := by
  have hinv : ContinuousOn (invFunOn f (closedBall 0 1 \ f ⁻¹' {y}))
      (f '' (closedBall 0 1 \ f ⁻¹' {y})) :=
    hf.continuousOn_invFunOn_image_of_isCompact (isCompact_closedBall 0 1) sdiff_subset hinj
      (disjoint_left.2 fun _ ⟨x', hx', hx'z⟩ ⟨x'', hx'', hx''z⟩ ↦
        hx''.2 (hx''z.trans (hx'z.symm.trans (not_not.1 fun h ↦ hx'.2 ⟨hx'.1, h⟩))))
  have hkf : ContinuousWithinAt (fun x ↦ k (f x)) (closedBall 0 1 \ f ⁻¹' {y}) x :=
    (hkc.continuousAt (isOpen_compl_singleton.mem_nhds fun h ↦ hp ⟨x, hx.1, h⟩))
      |>.comp_continuousWithinAt ((hf x hx.1).mono sdiff_subset)
  exact (hinv _ (hkP x hx)).comp (f := fun x' ↦ k (f x')) hkf hkP

omit [InnerProductSpace ℝ F] in
/-- **One shrinking step, given a push of `f(Q)`.** Let `k` be a map of the sphere, continuous
and injective off a point `p ∉ f(Q)`, which is the identity near `y` and maps `f(Q)` into
`f(Q ∩ U)`. Then `f⁻¹ ∘ k ∘ f` off the fibre `X` over `y`, extended by the identity on `X`, is
continuous and injective on `Q`, fixes `X` pointwise and maps `Q` into `U`. -/
private theorem exists_mapsTo_of_mapsTo_image (hf : ContinuousOn f (closedBall 0 1))
    (hinj : InjOn f (closedBall 0 1 \ f ⁻¹' {y})) {p : sphere (0 : F) 1}
    (hp : p ∉ f '' closedBall 0 1) (hyp : y ≠ p) {U : Set E}
    (hXU : closedBall 0 1 ∩ f ⁻¹' {y} ⊆ U) {k : sphere (0 : F) 1 → sphere (0 : F) 1}
    (hkc : ContinuousOn k {p}ᶜ) (hki : InjOn k {p}ᶜ) (hkid : k =ᶠ[𝓝 y] id)
    (hkN : MapsTo k (f '' closedBall 0 1) (f '' (closedBall 0 1 ∩ U))) :
    ∃ g : E → E, ContinuousOn g (closedBall 0 1) ∧ InjOn g (closedBall 0 1) ∧
      MapsTo g (closedBall 0 1) U ∧ ∀ x ∈ closedBall 0 1 ∩ f ⁻¹' {y}, g x = x := by
  classical
  set Q := closedBall (0 : E) 1
  set P := Q \ f ⁻¹' {y}
  have hfp {x : E} (hx : x ∈ Q) : f x ∈ ({p}ᶜ : Set (sphere (0 : F) 1)) := fun h ↦ hp ⟨x, hx, h⟩
  have hky : k y = y := hkid.eq_of_nhds
  have hkP {x : E} (hx : x ∈ P) : k (f x) ∈ f '' P := by
    obtain ⟨x', hx', hx'k⟩ := hkN (mem_image_of_mem f hx.1)
    refine ⟨x', ⟨hx'.1, fun h ↦ hx.2 ?_⟩, hx'k⟩
    exact hki (hfp hx.1) hyp (hx'k.symm.trans h ▸ hky.symm)
  set g : E → E := fun x ↦ if f x = y then x else invFunOn f P (k (f x))
  have hgX {x : E} (hx : f x = y) : g x = x := by simp [g, hx]
  have hg {x : E} (hx : f x ≠ y) : g x = invFunOn f P (k (f x)) := by simp [g, hx]
  have hgP {x : E} (hx : x ∈ P) : g x ∈ P ∧ f (g x) = k (f x) := by
    rw [hg hx.2]
    exact ⟨invFunOn_mem (hkP hx), invFunOn_eq (hkP hx)⟩
  -- `g` maps `Q` into `U`.
  have hgU : MapsTo g Q U := fun x hx ↦ by
    by_cases hxy : f x = y
    · simpa [g, hxy] using hXU ⟨hx, hxy⟩
    obtain ⟨hgx, hfgx⟩ := hgP ⟨hx, hxy⟩
    obtain ⟨x', hx', hx'k⟩ := hkN (mem_image_of_mem f hx)
    rw [eq_of_apply_eq hinj hgx.1 hx'.1 (hfgx.trans hx'k.symm) hgx.2]
    exact hx'.2
  have hfg {x : E} (hx : x ∈ Q) : f (g x) = k (f x) := by
    by_cases hxy : f x = y
    · simp [g, hxy, hky]
    · exact (hgP ⟨hx, hxy⟩).2
  refine ⟨g, fun x hx ↦ ?_, fun x hx x' hx' h ↦ ?_, hgU, fun x hx ↦ hgX hx.2⟩
  · -- Near a point mapped close to `y`, `g` is the identity; elsewhere it is `f⁻¹ ∘ k ∘ f`.
    obtain ⟨W, hWk, hW, hyW⟩ := _root_.eventually_nhds_iff.1 hkid
    by_cases hxW : f x ∈ W
    · have hid : g =ᶠ[𝓝[Q] x] id := by
        filter_upwards [self_mem_nhdsWithin,
          (hf x hx).preimage_mem_nhdsWithin (hW.mem_nhds hxW)] with x' hx' hx'W
        by_cases hx'y : f x' = y
        · simp [g, hx'y]
        have hfgx' : f (g x') = f x' := (hfg hx').trans (hWk _ hx'W)
        exact eq_of_apply_eq hinj (hgP ⟨hx', hx'y⟩).1.1 hx' hfgx' (by rwa [hfgx'])
      exact continuousWithinAt_id.congr_of_eventuallyEq hid (hid.eq_of_nhdsWithin hx)
    · have hxP : x ∈ P := ⟨hx, fun h ↦ hxW (h ▸ hyW)⟩
      have hgx : ContinuousWithinAt g P x :=
        (continuousWithinAt_invFunOn_comp hf hinj hp hkc (fun x' hx' ↦ hkP hx') hxP).congr
          (fun x' hx' ↦ hg hx'.2) (hg hxP.2)
      exact hgx.mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin
        ((hf x hx).preimage_mem_nhdsWithin (isOpen_compl_singleton.mem_nhds hxP.2)))
  · have hfx : f x = f x' := hki (hfp hx) (hfp hx') (by rw [← hfg hx, ← hfg hx', h])
    by_cases hxy : f x = y
    · simpa [g, hxy, ← hfx] using h
    · exact eq_of_apply_eq hinj hx hx' hfx hxy

/-- **One shrinking step.** For every open `U` containing the fibre `X` over `y`, there is a map
of `E`, continuous and injective on the closed ball, which fixes `X` pointwise and maps the closed
ball into `U`. -/
private theorem exists_mapsTo_of_isOpen (hn : 2 ≤ finrank ℝ E)
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hf : ContinuousOn f (closedBall 0 1))
    (hinj : InjOn f (closedBall 0 1 \ f ⁻¹' {y})) (hy : y ∉ f '' sphere 0 1)
    (hy' : y ∈ f '' closedBall 0 1) {U : Set E} (hU : IsOpen U)
    (hXU : closedBall 0 1 ∩ f ⁻¹' {y} ⊆ U) :
    ∃ g : E → E, ContinuousOn g (closedBall 0 1) ∧ InjOn g (closedBall 0 1) ∧
      MapsTo g (closedBall 0 1) U ∧ ∀ x ∈ closedBall 0 1 ∩ f ⁻¹' {y}, g x = x := by
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  obtain ⟨p, hp⟩ := exists_notMem_image_closedBall hEF hf hinj hy
  have hyp : y ≠ p := fun h ↦ hp (h ▸ hy')
  -- `f(Q ∩ U)` is a neighbourhood of `y`, since `f(Q \ U)` is compact and misses `y`.
  have hN : f '' (closedBall 0 1 ∩ U) ∈ 𝓝 y := by
    have hC : IsClosed (f '' (closedBall 0 1 \ U)) :=
      (((isCompact_closedBall 0 1).diff hU).image_of_continuousOn (hf.mono sdiff_subset)).isClosed
    refine mem_of_superset (inter_mem (image_closedBall_mem_nhds hn hEF hf hinj hy hy')
      (hC.isOpen_compl.mem_nhds fun ⟨x, hx, hxy⟩ ↦ hx.2 (hXU ⟨hx.1, hxy⟩))) ?_
    rintro _ ⟨⟨x, hx, rfl⟩, hxU⟩
    exact ⟨x, ⟨hx, not_not.1 fun h ↦ hxU ⟨x, ⟨hx, h⟩, rfl⟩⟩, rfl⟩
  obtain ⟨k, hkc, hki, hkid, hkN⟩ := exists_continuousOn_injOn_mapsTo_sphere hyp
    ((isCompact_closedBall 0 1).image_of_continuousOn hf) hp hN
  exact exists_mapsTo_of_mapsTo_image hf hinj hp hyp hXU hkc hki hkid hkN

/-- **Brown's theorem on inverse sets.** Let `E` be a real normed space of dimension `n ≥ 2`, and
let `f` map the closed unit ball `Q` of `E` continuously into the unit sphere `Sⁿ` of a real inner
product space of dimension `n + 1`. Suppose that the fibre `Q ∩ f⁻¹(y)` of a point `y` of `f(Q)`
lies in the open ball and that `f` is injective off it, so that it is the only inverse set of `f`.
Then this fibre is cellular. -/
theorem isCellularSet_closedBall_inter_preimage (hn : 2 ≤ finrank ℝ E)
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hf : ContinuousOn f (closedBall 0 1))
    (hinj : InjOn f (closedBall 0 1 \ f ⁻¹' {y})) (hy : y ∉ f '' sphere 0 1)
    (hy' : y ∈ f '' closedBall 0 1) :
    IsCellularSet E (closedBall (0 : E) 1 ∩ f ⁻¹' {y}) := by
  set X := closedBall (0 : E) 1 ∩ f ⁻¹' {y}
  have hX : IsClosed X := hf.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
  have hXb : X ⊆ ball 0 1 := fun x hx ↦ by
    rw [← closedBall_sdiff_sphere]
    exact ⟨hx.1, fun h ↦ hy ⟨x, h, hx.2⟩⟩
  have hδ (i : ℕ) : (0 : ℝ) < 1 / ((i : ℝ) + 1) := Nat.one_div_pos_of_nat
  -- A choice of shrinking step for every open set containing `X`.
  have step (U : Set E) : ∃ g : E → E, IsOpen U → X ⊆ U → ContinuousOn g (closedBall 0 1) ∧
      InjOn g (closedBall 0 1) ∧ MapsTo g (closedBall 0 1) U ∧ ∀ x ∈ X, g x = x := by
    by_cases h : IsOpen U ∧ X ⊆ U
    · obtain ⟨g, hg⟩ := exists_mapsTo_of_isOpen hn hEF hf hinj hy hy' h.1 h.2
      exact ⟨g, fun _ _ ↦ hg⟩
    · exact ⟨id, fun hU hXU ↦ absurd ⟨hU, hXU⟩ h⟩
  choose G hG using step
  -- The cells: `e 0` is the identity, and `e (i + 1)` maps the closed ball into the open cell
  -- `e i '' ball 0 1` and into the `1 / (i + 1)`-neighbourhood of `X`.
  obtain ⟨e, he0, hesucc⟩ : ∃ e : ℕ → E → E, e 0 = id ∧
      ∀ i, e (i + 1) = G (e i '' ball 0 1 ∩ thickening (1 / ((i : ℝ) + 1)) X) :=
    ⟨fun n ↦ Nat.rec (motive := fun _ ↦ E → E) id
      (fun i ei ↦ G (ei '' ball 0 1 ∩ thickening (1 / ((i : ℝ) + 1)) X)) n, rfl, fun _ ↦ rfl⟩
  have hU (i : ℕ) (hc : ContinuousOn (e i) (closedBall 0 1)) (hi : InjOn (e i) (closedBall 0 1))
      (hfix : ∀ x ∈ X, e i x = x) :
      IsOpen (e i '' ball 0 1 ∩ thickening (1 / ((i : ℝ) + 1)) X) ∧
        X ⊆ e i '' ball 0 1 ∩ thickening (1 / ((i : ℝ) + 1)) X :=
    ⟨(isOpen_ball.image_of_continuousOn_of_injOn (E := E) (F := E) (hc.mono ball_subset_closedBall)
      (hi.mono ball_subset_closedBall) rfl).inter isOpen_thickening,
      fun x hx ↦ ⟨⟨x, hXb hx, hfix x hx⟩, self_subset_thickening (hδ i) X hx⟩⟩
  have he (i : ℕ) : ContinuousOn (e i) (closedBall 0 1) ∧ InjOn (e i) (closedBall 0 1) ∧
      ∀ x ∈ X, e i x = x := by
    induction i with
    | zero => exact ⟨he0 ▸ continuousOn_id, he0 ▸ injOn_id _, fun x _ ↦ by rw [he0, id]⟩
    | succ i ih =>
      obtain ⟨hc, hi, -, hfix⟩ := hesucc i ▸ hG _ (hU i ih.1 ih.2.1 ih.2.2).1
        (hU i ih.1 ih.2.1 ih.2.2).2
      exact ⟨hc, hi, hfix⟩
  have hmaps (i : ℕ) : MapsTo (e (i + 1)) (closedBall 0 1)
      (e i '' ball 0 1 ∩ thickening (1 / ((i : ℝ) + 1)) X) :=
    hesucc i ▸ (hG _ (hU i (he i).1 (he i).2.1 (he i).2.2).1 (hU i (he i).1 (he i).2.1
      (he i).2.2).2).2.2.1
  refine (isCellularSet_iff E).2 ⟨e, fun i ↦ (he i).1, fun i ↦ (he i).2.1,
    fun i ↦ (hmaps i).image_subset.trans inter_subset_left, ?_⟩
  refine Subset.antisymm (fun x hx ↦ hX.closure_subset_iff.2 subset_rfl ?_)
    fun x hx ↦ mem_iInter.2 fun i ↦ ⟨x, hXb hx |> ball_subset_closedBall, (he i).2.2 x hx⟩
  -- A point of every cell is within `1 / (i + 1)` of `X` for every `i`.
  refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
  obtain ⟨i, hi⟩ := exists_nat_one_div_lt hε
  obtain ⟨z, hz, hxz⟩ := mem_thickening_iff.1 ((hmaps i).image_subset (mem_iInter.1 hx (i + 1))).2
  exact ⟨z, hz, hxz.trans hi⟩

/-! ### Maps of the sphere onto itself with two inverse sets -/

section TwoInverseSets

/-- A compact subset `K` of the unit sphere `Sⁿ` missing a point `z` lies in the open cell of an
injection of `E`, `dim E = n`, whose image misses `z`: the inverse stereographic projection from
`z`, precomposed with a linear isomorphism and a dilation of `E`. -/
private theorem exists_injective_subset_image_ball
    (hEF : finrank ℝ F = finrank ℝ E + 1) {K : Set (sphere (0 : F) 1)} (hK : IsCompact K)
    {z : sphere (0 : F) 1} (hz : z ∉ K) :
    ∃ ψ : E → sphere (0 : F) 1, Continuous ψ ∧ Injective ψ ∧ z ∉ range ψ ∧
      K ⊆ ψ '' ball 0 1 := by
  have : Fact (finrank ℝ F = finrank ℝ E + 1) := ⟨hEF⟩
  set φ := stereographic' (finrank ℝ E) z
  have htgt : φ.target = univ := stereographic'_target z
  have hKs : K ⊆ φ.source := fun w hw ↦ by
    rw [stereographic'_source]
    exact fun h : w = z ↦ hz (h ▸ hw)
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  -- The image of `K` in `E` lies in a ball of radius `R`.
  obtain ⟨R, hR, hKR⟩ := ((hK.image_of_continuousOn (φ.continuousOn.mono hKs)).image
    L.symm.continuous).isBounded.subset_ball_lt 0 0
  refine ⟨fun x ↦ φ.symm (L (R • x)),
    φ.continuousOn_symm.comp_continuous (by fun_prop) fun x ↦ htgt ▸ mem_univ _,
    fun x x' h ↦ smul_right_injective E hR.ne' <| L.injective <|
      φ.symm.injOn (by simp [htgt]) (by simp [htgt]) h, ?_, fun w hw ↦ ?_⟩
  · rintro ⟨x, hx⟩
    have := φ.map_target (htgt ▸ mem_univ (L (R • x)))
    rw [stereographic'_source] at this
    exact this hx
  · refine ⟨R⁻¹ • L.symm (φ w), ?_, ?_⟩
    · have := hKR ⟨φ w, ⟨w, hw, rfl⟩, rfl⟩
      rw [mem_ball_zero_iff] at this ⊢
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hR.le, inv_mul_lt_one₀ hR]
      exact this
    · simp [smul_smul, hR.ne', φ.left_inv (hKs hw)]

/-- **One inverse set inside a cell of the sphere.** Let `ψ : E → Sⁿ` be a continuous injection,
`dim E = n ≥ 2`, and let `G` be a map of the sphere, continuous on the closed cell `ψ(Q)`, which is
injective on `ψ(Q)` off a nonempty set `X` lying in the open cell and collapsed by `G` to a point
`c` taken nowhere else on `ψ(Q)`. Then `X` is cellular. This is
`TauCeti.isCellularSet_closedBall_inter_preimage` for `G ∘ ψ`, read through `ψ`. -/
private theorem isCellularSet_of_injOn_image_closedBall (hn : 2 ≤ finrank ℝ E)
    (hEF : finrank ℝ F = finrank ℝ E + 1) {ψ : E → sphere (0 : F) 1} (hψ : Continuous ψ)
    (hψi : Injective ψ) {G : sphere (0 : F) 1 → sphere (0 : F) 1}
    (hG : ContinuousOn G (ψ '' closedBall 0 1)) {X : Set (sphere (0 : F) 1)}
    {c : sphere (0 : F) 1} (hX : X ⊆ ψ '' ball 0 1) (hXne : X.Nonempty)
    (hGc : ∀ w ∈ ψ '' closedBall 0 1, G w = c ↔ w ∈ X)
    (hGi : InjOn G (ψ '' closedBall 0 1 \ X)) : IsCellularSet E X := by
  have hc {x : E} (hx : x ∈ closedBall 0 1) : G (ψ x) = c ↔ ψ x ∈ X :=
    hGc _ (mem_image_of_mem ψ hx)
  have hfib : closedBall 0 1 ∩ (G ∘ ψ) ⁻¹' {c} = closedBall 0 1 ∩ ψ ⁻¹' X := by
    ext x
    exact and_congr_right hc
  have hball : closedBall 0 1 ∩ ψ ⁻¹' X ⊆ ball 0 1 := fun x hx ↦ by
    obtain ⟨x', hx', h⟩ := hX hx.2
    exact hψi h ▸ hx'
  have hcell := isCellularSet_closedBall_inter_preimage (f := G ∘ ψ) (y := c) hn hEF
    (hG.comp hψ.continuousOn (mapsTo_image _ _))
    (fun x hx x' hx' h ↦ hψi <| hGi ⟨mem_image_of_mem ψ hx.1, fun h' ↦ hx.2 ((hc hx.1).2 h')⟩
      ⟨mem_image_of_mem ψ hx'.1, fun h' ↦ hx.2 (h.trans ((hc hx'.1).2 h'))⟩ h)
    (fun ⟨x, hx, hxc⟩ ↦ sphere_disjoint_ball.ne_of_mem hx
      (hball ⟨sphere_subset_closedBall hx, (hc (sphere_subset_closedBall hx)).1 hxc⟩) rfl)
    (by
      obtain ⟨w, hw⟩ := hXne
      obtain ⟨x, hx, rfl⟩ := hX hw
      exact ⟨x, ball_subset_closedBall hx, (hc (ball_subset_closedBall hx)).2 hw⟩)
  rw [hfib] at hcell
  have := hcell.image isOpen_ball hball hψ.continuousOn hψi.injOn
  rwa [image_inter_preimage, inter_eq_right.2 (hX.trans (image_mono ball_subset_closedBall))]
    at this

/-- **Pushing one inverse set off its value.** Let `g` be a continuous surjection of `Sⁿ` onto
itself, injective off the fibres over two distinct points `p` and `q`, and let `D` be a compact set
meeting the fibre over `q` whose image misses some point `g z ≠ p`. Then some map `G` of the
sphere, continuous on `D`, collapses the fibre over `q` to a point `c` taken nowhere else on `D`,
and is injective on `D` off that fibre. Following Brown, `G` is the identity on the fibre over `p`
and `g⁻¹ ∘ k ∘ g` elsewhere, for a map `k` which is the identity near `p` and moves `g(D)` off
`q`. -/
private theorem exists_continuousOn_injOn_sdiff_preimage [FiniteDimensional ℝ F]
    {g : sphere (0 : F) 1 → sphere (0 : F) 1} (hg : Continuous g) (hgs : Surjective g)
    {p q : sphere (0 : F) 1} (hpq : p ≠ q) (hinj : InjOn g (g ⁻¹' {p, q})ᶜ)
    {D : Set (sphere (0 : F) 1)} (hD : IsCompact D) (hqD : q ∈ g '' D) {z : sphere (0 : F) 1}
    (hzp : g z ≠ p) (hzD : g z ∉ g '' D) :
    ∃ (G : sphere (0 : F) 1 → sphere (0 : F) 1) (c : sphere (0 : F) 1), ContinuousOn G D ∧
      (∀ w ∈ D, G w = c ↔ w ∈ g ⁻¹' {q}) ∧ InjOn G (D \ g ⁻¹' {q}) := by
  classical
  have : Nonempty (sphere (0 : F) 1) := ⟨p⟩
  obtain ⟨k, hkc, hki, hkid, hkN⟩ := exists_continuousOn_injOn_mapsTo_sphere hzp.symm
    (hD.image hg) hzD (isOpen_compl_singleton.mem_nhds hpq)
  set P := (g ⁻¹' {p, q})ᶜ
  have hgP : g '' P = {p, q}ᶜ := by
    ext v
    refine ⟨fun ⟨w, hw, hwv⟩ ↦ hwv ▸ hw, fun hv ↦ ?_⟩
    obtain ⟨w, rfl⟩ := hgs v
    exact ⟨w, hv, rfl⟩
  have hinv : ContinuousOn (invFunOn g P) {p, q}ᶜ := hgP ▸
    hg.continuousOn.continuousOn_invFunOn_image_of_isCompact isCompact_univ (subset_univ P) hinj
      (disjoint_left.2 fun _ ⟨_, hw, hwv⟩ hv ↦ hgP.subset hv (hwv ▸ not_not.1 hw.2))
  have hkp : k p = p := hkid.eq_of_nhds
  have hgz {w : sphere (0 : F) 1} (hw : w ∈ D) : g w ≠ g z := fun h ↦ hzD ⟨w, hw, h⟩
  -- Off the fibre over `p`, `k ∘ g` avoids both `p` and `q` on `D`.
  have hk {w : sphere (0 : F) 1} (hw : w ∈ D) (hwp : g w ≠ p) : k (g w) ∈ g '' P := by
    rw [hgP]
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun h ↦ hwp (hki (hgz hw) hzp.symm (h.trans hkp.symm)), hkN ⟨w, hw, rfl⟩⟩
  set G : sphere (0 : F) 1 → sphere (0 : F) 1 :=
    fun w ↦ if g w = p then w else invFunOn g P (k (g w))
  have hGp {w : sphere (0 : F) 1} (hwp : g w = p) : G w = w := by simp [G, hwp]
  have hGP {w : sphere (0 : F) 1} (hw : w ∈ D) (hwp : g w ≠ p) : G w ∈ P ∧ g (G w) = k (g w) := by
    simp only [G, hwp, ite_false]
    exact ⟨invFunOn_mem (hk hw hwp), invFunOn_eq (hk hw hwp)⟩
  have hPp {w : sphere (0 : F) 1} (hw : w ∈ P) : g w ≠ p := fun h ↦ hw (.inl h)
  obtain ⟨w₀, hw₀, hw₀q⟩ := hqD
  refine ⟨G, G w₀, fun w hw ↦ ?_, fun w hw ↦ ⟨fun h ↦ ?_, fun hwq ↦ ?_⟩, ?_⟩
  · -- Near a point sent close to `p`, `G` is the identity; elsewhere it is `g⁻¹ ∘ k ∘ g`.
    obtain ⟨W, hWk, hW, hpW⟩ := _root_.eventually_nhds_iff.1 hkid
    by_cases hwW : g w ∈ W ∩ {q}ᶜ
    · have hid : G =ᶠ[𝓝[D] w] id := by
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
          (hg.continuousAt.preimage_mem_nhds ((hW.inter isOpen_compl_singleton).mem_nhds hwW))]
          with w' hw' hw'W
        by_cases hw'p : g w' = p
        · exact hGp hw'p
        obtain ⟨hGw', hgG⟩ := hGP hw' hw'p
        rw [hWk _ hw'W.1, id] at hgG
        exact hinj hGw' (by simpa [P, hw'p] using hw'W.2) hgG
      exact continuousWithinAt_id.congr_of_eventuallyEq hid (hid.eq_of_nhdsWithin hw)
    · have hwp : g w ≠ p := fun h ↦ hwW ⟨h ▸ hpW, h ▸ hpq⟩
      have hcomp : ContinuousWithinAt (fun w' ↦ invFunOn g P (k (g w'))) (D ∩ {w' | g w' ≠ p}) w :=
        (hinv _ (hgP ▸ hk hw hwp)).comp
          ((hkc.continuousAt (isOpen_compl_singleton.mem_nhds (hgz hw))).comp_continuousWithinAt
            hg.continuousWithinAt) fun w' hw' ↦ hgP ▸ hk hw'.1 hw'.2
      refine (hcomp.congr (fun w' hw' ↦ by simp [G, show g w' ≠ p from hw'.2])
        (by simp [G, hwp])).mono_of_mem_nhdsWithin
        (inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds
          (hg.continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hwp))))
  · -- Only the fibre over `q` is sent to `G w₀`.
    have hc := hGP hw₀ (hw₀q ▸ hpq.symm)
    by_cases hwp : g w = p
    · rw [hGp hwp] at h
      exact absurd hwp (hPp (h ▸ hc.1))
    · have h' := (hGP hw hwp).2
      rw [h, hc.2, hw₀q] at h'
      exact hki (hgz hw) (hw₀q ▸ hgz hw₀) h'.symm
  · simp only [mem_preimage, mem_singleton_iff] at hwq
    simp [G, hwq, hw₀q, hpq.symm]
  · rintro w ⟨hw, hwq⟩ w' ⟨hw', hw'q⟩ h
    by_cases hwp : g w = p <;> by_cases hw'p : g w' = p
    · rwa [hGp hwp, hGp hw'p] at h
    · exact absurd hwp (hPp (hGp hwp ▸ h ▸ (hGP hw' hw'p).1))
    · exact absurd hw'p (hPp (hGp hw'p ▸ h.symm ▸ (hGP hw hwp).1))
    · have hgg := hki (hgz hw) (hgz hw') ((hGP hw hwp).2.symm.trans (h ▸ (hGP hw' hw'p).2))
      exact hinj (by simp [P, hwp, show g w ≠ q from hwq])
        (by simp [P, hw'p, show g w' ≠ q from hw'q]) hgg

/-- **Brown's theorem on two inverse sets.** Let `F` be a real inner product space of dimension
`n + 1`, `n ≥ 2`, and let `g` be a continuous surjection of the unit sphere `Sⁿ` of `F` onto
itself which is injective off the fibres over two points `p` and `q`, so that these fibres are its
only inverse sets. Then the fibre over `q` is cellular, modelled on any real normed space of
dimension `n`. By symmetry so is the fibre over `p`. -/
theorem isCellularSet_preimage_singleton (hn : 2 ≤ finrank ℝ E)
    (hEF : finrank ℝ F = finrank ℝ E + 1) {g : sphere (0 : F) 1 → sphere (0 : F) 1}
    (hg : Continuous g) (hgs : Surjective g) {p q : sphere (0 : F) 1}
    (hinj : InjOn g (g ⁻¹' {p, q})ᶜ) : IsCellularSet E (g ⁻¹' {q}) := by
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  -- A point `z` whose image is neither `p` nor `q`: the sphere is connected, so infinite.
  obtain ⟨z, hzp, hzq⟩ : ∃ z, g z ≠ p ∧ g z ≠ q := by
    have : PreconnectedSpace (sphere (0 : F) 1) := Subtype.preconnectedSpace
      (isConnected_sphere (by rw [← finrank_eq_rank]; exact_mod_cast (by omega : 1 < finrank ℝ F))
        0 zero_le_one).2
    have : Nontrivial (sphere (0 : F) 1) := ⟨⟨p, -p, ne_neg_of_mem_unit_sphere ℝ p⟩⟩
    have := PreconnectedSpace.infinite (X := sphere (0 : F) 1)
    classical
    obtain ⟨r, hr⟩ := Infinite.exists_notMem_finset ({p, q} : Finset (sphere (0 : F) 1))
    obtain ⟨z, rfl⟩ := hgs r
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
    exact ⟨z, hr⟩
  -- A closed cell `ψ(Q)` containing both fibres in its interior and missing `z`.
  obtain ⟨ψ, hψ, hψi, hzψ, hKψ⟩ := exists_injective_subset_image_ball hEF
    ((((toFinite {p, q}).isClosed).preimage hg).isCompact) (z := z) fun h ↦ by
      rcases h with h | h
      exacts [hzp h, hzq h]
  have hB : g ⁻¹' {q} ⊆ ψ '' ball 0 1 := fun w hw ↦ hKψ (by simp_all)
  obtain ⟨w₀, hw₀⟩ := hgs q
  have hBne : (g ⁻¹' {q}).Nonempty := ⟨w₀, hw₀⟩
  rcases eq_or_ne p q with rfl | hpq
  · -- One inverse set: `g` itself collapses only the fibre over `p` on `ψ(Q)`.
    refine isCellularSet_of_injOn_image_closedBall hn hEF hψ hψi hg.continuousOn hB hBne
      (fun w _ ↦ Iff.rfl) fun w hw w' hw' ↦ hinj (by simpa using hw.2) (by simpa using hw'.2)
  · -- Two inverse sets: push the value `q` off while fixing a neighbourhood of `p`.
    have hzD : g z ∉ g '' (ψ '' closedBall 0 1) := by
      rintro ⟨_, ⟨x, -, rfl⟩, h⟩
      refine hzψ ⟨x, hinj ?_ (by simp [hzp, hzq]) h⟩
      simp [h, hzp, hzq]
    obtain ⟨G, c, hG, hGc, hGi⟩ := exists_continuousOn_injOn_sdiff_preimage hg hgs hpq hinj
      ((isCompact_closedBall 0 1).image hψ) ⟨w₀, image_mono ball_subset_closedBall (hB hw₀), hw₀⟩
      hzp hzD
    exact isCellularSet_of_injOn_image_closedBall hn hEF hψ hψi hG hB hBne hGc hGi

end TwoInverseSets

end TauCeti
