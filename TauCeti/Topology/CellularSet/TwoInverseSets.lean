/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CellularSet.InverseSet
import Mathlib.Analysis.Normed.Module.Connected
import TauCeti.Topology.Sphere.Shrink

/-!
# Both inverse sets of a map of a sphere onto itself with two inverse sets are cellular

Let `f` map the unit sphere `Sⁿ` of a real inner product space of dimension `n + 1 ≥ 3` onto
itself, and suppose that `f` is injective off the two fibres `A = f⁻¹(a)` and `B = f⁻¹(b)`,
`a ≠ b`: in M. Brown's terminology, `A` and `B` are the only *inverse sets* of `f`. Then `A` and
`B` are cellular in `Sⁿ` (`TauCeti.isCellularSet_preimage_singleton`). This is Theorem 4 of
Brown's proof of the generalized Schoenflies theorem. Brown's collapse of the outside of a bicollar
(`TauCeti.IsBicollar.exists_collapse`) is such a map, so the two outer pieces of a bicollared
sphere are cellular; collapsing them (`TauCeti.IsCellularSet.exists_collapse`) identifies the
closures of the complementary domains of the sphere with closed hemispheres (his Theorem 5).

The proof reduces to Brown's theorem on a single inverse set
(`TauCeti.isCellularSet_closedBall_inter_preimage`). Choose a point `z` outside `A ∪ B`, and a
closed cell `Q` missing `z` whose interior contains `A ∪ B`: the preimage of a large closed ball
under the stereographic projection from `z`
(`TauCeti.exists_continuous_injective_isOpen_image_ball_superset_notMem_range`). Since `f` is onto
and the complement of the interior of `Q` is compact and misses `A`, the image `f(Q)` is a
neighbourhood of `a`. The point `f z` is not in `f(Q)`, so a radial squeeze about `a` in the
stereographic chart from `f z` (`TauCeti.exists_continuousOn_injOn_mapsTo_sphere`) gives a map
`k`, continuous and injective off `f z`, which is the identity near `a` and pushes `f(Q)` into
`f(Q) \ {b}`. The map `g = f⁻¹ ∘ k ∘ f` on `Q \ A`, extended by the identity on `A`, then maps `Q`
continuously into itself (`TauCeti.exists_continuousOn_lift_comp`), and `B` is its only inverse
set. Hence `B` is cellular, and so, exchanging `a` and `b`, is `A`.

## Main results

* `TauCeti.isCellularSet_preimage_singleton`: **Brown's theorem on two inverse sets**: both inverse
  sets of a map of `Sⁿ`, `n ≥ 2`, onto itself with exactly two inverse sets are cellular.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorem 4.
-/

public section

open Function Metric Module Set Filter Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ F] in
/-- **Unfolding one of two inverse sets.** Let `f` be continuous on a compact set `Q` of `Sⁿ`, and
injective on `Q` off the fibres over two points `a ≠ b`. Let `k` be a map of the sphere, continuous
and injective off a point `p ∉ f(Q)`, which is the identity near `a` and maps `f(Q)` into
`f(Q) \ {b}`. Then `f⁻¹ ∘ k ∘ f` off the fibre over `a`, extended by the identity on that fibre,
maps `Q` continuously into itself, is injective off the fibre over `b`, and collapses that fibre to
one point. -/
private theorem exists_continuousOn_mapsTo_injOn {Q : Set (sphere (0 : F) 1)} (hQ : IsCompact Q)
    {f : sphere (0 : F) 1 → sphere (0 : F) 1} (hf : ContinuousOn f Q) {a b : sphere (0 : F) 1}
    (hab : a ≠ b) (hinj : InjOn f (Q \ f ⁻¹' {a, b})) {p : sphere (0 : F) 1} (hp : p ∉ f '' Q)
    (hap : a ≠ p) {k : sphere (0 : F) 1 → sphere (0 : F) 1} (hkc : ContinuousOn k {p}ᶜ)
    (hki : InjOn k {p}ᶜ) (hkid : k =ᶠ[𝓝 a] id) (hkN : MapsTo k (f '' Q) (f '' Q ∩ {b}ᶜ)) :
    ∃ g : sphere (0 : F) 1 → sphere (0 : F) 1, ContinuousOn g Q ∧ MapsTo g Q Q ∧
      InjOn g (Q \ f ⁻¹' {b}) ∧ ∀ x ∈ Q, ∀ x' ∈ Q, f x' = b → (g x = g x' ↔ f x = b) := by
  set P := Q \ f ⁻¹' {a, b}
  have hfp {x} (hx : x ∈ Q) : f x ∈ ({p}ᶜ : Set (sphere (0 : F) 1)) := fun h ↦ hp ⟨x, hx, h⟩
  have hka : k a = a := hkid.eq_of_nhds
  -- Off the fibre over `a`, `k ∘ f` takes values in `f(P)`.
  have hkP {x} (hx : x ∈ Q) (hxa : f x ≠ a) : k (f x) ∈ f '' P := by
    obtain ⟨⟨x', hx', hx'k⟩, hb⟩ := hkN (mem_image_of_mem f hx)
    refine ⟨x', ⟨hx', ?_⟩, hx'k⟩
    rintro (h | h)
    · exact hxa (hki (hfp hx) hap ((hx'k.symm.trans h).trans hka.symm))
    · exact hb (hx'k.symm.trans h)
  obtain ⟨g, hgc, hfg, hgP, hga⟩ := exists_continuousOn_lift_comp hQ hf hinj
    (Filter.mem_of_superset (isOpen_compl_singleton.mem_nhds hab) fun _ hb h ↦ h.resolve_right hb)
    (hkc.mono fun _ ⟨x, hx, hxq⟩ ↦ hxq ▸ hfp hx) hkid fun x hx hxa ↦ hkP hx hxa
  refine ⟨g, hgc, fun x hx ↦ ?_, fun x hx x' hx' h ↦ ?_, fun x hx x' hx' hx'b ↦ ?_⟩
  · by_cases hxa : f x = a
    · rwa [hga x hx hxa]
    · exact (hgP x hx hxa).1
  · have hfx : f x = f x' := hki (hfp hx.1) (hfp hx'.1) (by rw [← hfg x hx.1, ← hfg x' hx'.1, h])
    by_cases hxa : f x = a
    · rwa [hga x hx.1 hxa, hga x' hx'.1 (hfx ▸ hxa)] at h
    · exact hinj ⟨hx.1, by rintro (h | h); exacts [hxa h, hx.2 h]⟩
        ⟨hx'.1, by rintro (h | h); exacts [hxa (hfx.trans h), hx'.2 h]⟩ hfx
  · have hx'a : f x' ≠ a := fun h ↦ hab (h.symm.trans hx'b)
    refine ⟨fun h ↦ (hki (hfp hx) (hfp hx') ?_).trans hx'b, fun h ↦ ?_⟩
    · rw [← hfg x hx, ← hfg x' hx', h]
    · have hxa : f x ≠ a := fun h' ↦ hx'a (hx'b.trans (h.symm.trans h'))
      exact hinj (hgP x hx hxa) (hgP x' hx' hx'a) (by rw [hfg x hx, hfg x' hx', h, hx'b])

/-- A continuous map from a preconnected space onto a `T₁` space takes a value other than two
given distinct points `a` and `b`: otherwise the fibre over `a` would be clopen. -/
private theorem exists_notMem_preimage_pair {X Y : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] [TopologicalSpace Y] [T1Space Y] {f : X → Y} (hf : Continuous f)
    (hfs : Surjective f) {a b : Y} (hab : a ≠ b) : ∃ z, z ∉ f ⁻¹' {a, b} := by
  by_contra! h
  have hcompl : f ⁻¹' {a} = (f ⁻¹' {b})ᶜ := by
    ext x
    have hx := h x
    simp only [mem_preimage, mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with hx | hx <;> simp [hx, hab, hab.symm]
  rcases isClopen_iff.1 ⟨isClosed_singleton.preimage hf,
    by rw [hcompl]; exact (isClosed_singleton.preimage hf).isOpen_compl⟩ with h' | h'
  · obtain ⟨x, hx⟩ := hfs a
    have hx' : x ∈ f ⁻¹' {a} := hx
    rw [h'] at hx'
    exact hx'
  · obtain ⟨x, hx⟩ := hfs b
    have hx' : x ∈ f ⁻¹' {a} := by rw [h']; exact mem_univ x
    exact hab ((show f x = a from hx').symm.trans hx)

/-- **Brown's theorem on two inverse sets.** Let `E` be a real normed space of dimension `n ≥ 2`,
and let `f` map the unit sphere `Sⁿ` of a real inner product space of dimension `n + 1`
continuously onto itself. Suppose that `f` is injective off the fibres over two points `a ≠ b`, so
that these fibres are the only inverse sets of `f`. Then the fibre over `b` is cellular; exchanging
`a` and `b`, so is the fibre over `a`. -/
theorem isCellularSet_preimage_singleton (hn : 2 ≤ finrank ℝ E)
    (hEF : finrank ℝ F = finrank ℝ E + 1) {f : sphere (0 : F) 1 → sphere (0 : F) 1}
    (hf : Continuous f) (hfs : Surjective f) {a b : sphere (0 : F) 1} (hab : a ≠ b)
    (hinj : InjOn f (f ⁻¹' {a, b})ᶜ) : IsCellularSet E (f ⁻¹' {b}) := by
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  have : PreconnectedSpace (sphere (0 : F) 1) := Subtype.preconnectedSpace
    (isPreconnected_sphere (by rw [← finrank_eq_rank]; exact_mod_cast (by omega : 1 < finrank ℝ F))
      0 1)
  have hAB : IsClosed (f ⁻¹' {a, b}) := (Set.toFinite _).isClosed.preimage hf
  -- A point `z` outside both inverse sets.
  obtain ⟨z, hz⟩ := exists_notMem_preimage_pair hf hfs hab
  obtain ⟨θ, hθc, hθi, hθo, hABθ, hzθ⟩ :=
    exists_continuous_injective_isOpen_image_ball_superset_notMem_range (E := E) hEF
      hAB.isCompact hz
  set Q := θ '' closedBall 0 1
  have hQ : IsCompact Q := (isCompact_closedBall 0 1).image hθc
  have hBθ : f ⁻¹' {b} ⊆ θ '' ball 0 1 := fun x hx ↦ hABθ (Or.inr hx)
  -- `f z` is not in `f(Q)`, since `z` is alone in its fibre and lies outside `Q`.
  have hpQ : f z ∉ f '' Q := by
    rintro ⟨q, ⟨x, -, rfl⟩, hq⟩
    exact hzθ ⟨x, hinj (fun h ↦ hz (by rw [mem_preimage, ← hq]; exact h)) hz hq⟩
  -- `f(Q)` is a neighbourhood of `a`: the complement of the open cell is compact and misses the
  -- fibre over `a`, and `f` is onto.
  have hN : f '' Q ∩ {b}ᶜ ∈ 𝓝 a := by
    have hC : (f '' (θ '' ball 0 1)ᶜ)ᶜ ∈ 𝓝 a :=
      (hθo.isClosed_compl.isCompact.image hf).isClosed.isOpen_compl.mem_nhds
        fun ⟨x, hx, hxa⟩ ↦ hx (hABθ (Or.inl hxa))
    filter_upwards [hC, isOpen_compl_singleton.mem_nhds hab] with y hy hyb
    obtain ⟨u, rfl⟩ := hfs y
    exact ⟨⟨u, image_mono ball_subset_closedBall (not_not.1 fun h ↦ hy ⟨u, h, rfl⟩), rfl⟩, hyb⟩
  have hap : a ≠ f z := fun h ↦ hz (Or.inl h.symm)
  obtain ⟨k, hkc, hki, hkid, hkN⟩ :=
    exists_continuousOn_injOn_mapsTo_sphere hap (hQ.image hf) hpQ hN
  obtain ⟨g, hgc, hgQ, hgi, hgb⟩ := exists_continuousOn_mapsTo_injOn hQ hf.continuousOn hab
    (hinj.mono fun x hx ↦ hx.2) hpQ hap hkc hki hkid hkN
  -- Apply Brown's theorem on a single inverse set to `g ∘ θ`.
  obtain ⟨u, hu⟩ := hfs b
  obtain ⟨x₀, hx₀, rfl⟩ := hBθ hu
  have hx₀Q : θ x₀ ∈ Q := mem_image_of_mem θ (ball_subset_closedBall hx₀)
  have hθQ {x : E} (hx : x ∈ closedBall 0 1) : θ x ∈ Q := mem_image_of_mem θ hx
  have hgb' {x : E} (hx : x ∈ closedBall 0 1) : g (θ x) = g (θ x₀) ↔ f (θ x) = b :=
    hgb _ (hθQ hx) _ hx₀Q hu
  have hball {x : E} (hx : f (θ x) = b) : x ∈ ball 0 1 := by
    obtain ⟨x', hx', hxx'⟩ := hBθ hx
    exact hθi hxx' ▸ hx'
  have hfib : closedBall (0 : E) 1 ∩ (g ∘ θ) ⁻¹' {g (θ x₀)} = θ ⁻¹' (f ⁻¹' {b}) := by
    ext x
    refine ⟨fun ⟨hx, hgx⟩ ↦ (hgb' hx).1 hgx, fun hx ↦ ?_⟩
    have hx' := ball_subset_closedBall (hball hx)
    exact ⟨hx', (hgb' hx').2 hx⟩
  have h3 := isCellularSet_closedBall_inter_preimage hn hEF (f := g ∘ θ) (y := g (θ x₀))
    (hgc.comp hθc.continuousOn fun x hx ↦ hθQ hx)
    (fun x hx x' hx' h ↦ hθi (hgi ⟨hθQ hx.1, fun hb ↦ hx.2 ((hgb' hx.1).2 hb)⟩
      ⟨hθQ hx'.1, fun hb ↦ hx'.2 ((hgb' hx'.1).2 hb)⟩ h))
    (fun ⟨x, hx, hgx⟩ ↦ sphere_disjoint_ball.ne_of_mem hx
      (hball ((hgb' (sphere_subset_closedBall hx)).1 hgx)) rfl)
    ⟨x₀, ball_subset_closedBall hx₀, rfl⟩
  rw [hfib] at h3
  have h4 := h3.image hθc hθi
  rwa [image_preimage_eq_of_subset (hBθ.trans (image_subset_range _ _))] at h4

end TauCeti
