/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.Topology.CellularSet.Basic
import Mathlib.Geometry.Manifold.Instances.Sphere
import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain
import TauCeti.AlgebraicTopology.Singular.JordanBrouwer
import TauCeti.Analysis.Normed.Module.Connected
import TauCeti.Topology.Separation.InvFunOn
import TauCeti.Topology.Sphere.Shrink

/-!
# The only inverse set of a map of a cell into a sphere is cellular

Let `Q` be the closed unit ball of a real normed space `E` of dimension `n ≥ 2`, and let `f` map
`Q` continuously into the unit sphere `Sⁿ` of a real inner product space of dimension `n + 1`.
Suppose that the fibre `X = Q ∩ f⁻¹(y)` over some point `y` is nonempty and lies in the open
ball, and that `f` is injective on `Q \ X`: in M. Brown's terminology, `X` is the only *inverse
set* of `f`. Then `X` is cellular in `E` (`TauCeti.isCellularSet_closedBall_inter_preimage`).
This is Theorem 3 of Brown's proof of the generalized Schoenflies theorem. Brown deduces from it
that both inverse sets of a map of `Sⁿ` onto itself with exactly two inverse sets are cellular (his
Theorem 4); with the collapse of cellular sets (`TauCeti.IsCellularSet.exists_collapse`) this
identifies the closures of the complementary domains of a bicollared sphere with cells (his
Theorem 5). The hypothesis `n ≥ 2` is used only through the connectedness of punctured balls.

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

## Main results

* `TauCeti.isCellularSet_closedBall_inter_preimage`: **Brown's theorem on inverse sets**: the only
  inverse set of a map of an `n`-cell into `Sⁿ`, `n ≥ 2`, is cellular.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorems 0 and 3.
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

end TauCeti
