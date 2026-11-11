/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.Topology.CellularSet.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.Instances.Sphere
import TauCeti.Topology.CellularSet.InverseSet
import TauCeti.Topology.Separation.InvFunOn
import TauCeti.Topology.Sphere.Shrink

/-!
# Both inverse sets of a map of a sphere with two inverse sets are cellular

Let `g` be a continuous surjection of the unit sphere `Sⁿ` of a real inner product space of
dimension `n + 1 ≥ 3` onto itself, and let `a ≠ b` be two points of `Sⁿ` such that `g` is
injective off `g⁻¹{a, b}`: in M. Brown's terminology, `A = g⁻¹(a)` and `B = g⁻¹(b)` are the only
*inverse sets* of `g`. Then `A` is cellular, and by symmetry so is `B`
(`TauCeti.isCellularSet_preimage_singleton_of_injOn`). This is Theorem 4 of Brown's proof of the
generalized Schoenflies theorem. Brown applies it to the map collapsing the two pieces of `Sⁿ`
outside the open collar of a bicollared sphere to the poles
(`TauCeti.IsBicollar.exists_collapse`); the collapse of the cellular inverse sets
(`TauCeti.IsCellularSet.exists_homeomorph_preimage_hemisphere`) then identifies the closures of
the two complementary domains with closed balls.

The proof reduces to Brown's theorem on a single inverse set
(`TauCeti.isCellularSet_closedBall_inter_preimage`), applied to `g⁻¹ ∘ k ∘ g` on a closed cell
`Q ⊆ Sⁿ` containing `A ∪ B` in its interior.

* Since `Sⁿ` is connected, `A ∪ B ≠ Sⁿ`. Read `Sⁿ` in the stereographic chart from a point
  `z ∉ A ∪ B`; the compact set `A ∪ B` lies in the open cell of a large coordinate ball `Q`
  (`TauCeti.exists_continuous_injective_subset_image_ball_sphere`), and `p = g z` is not in
  `g(Q)`.
* A map `k` of `Sⁿ`, continuous and injective off `p`, which is the identity near `b` and pushes
  `g(Q)` off `a` (`TauCeti.exists_continuousOn_injOn_mapsTo_sphere`), makes `g⁻¹ ∘ k ∘ g`
  single-valued off `B`. Extended by the identity on `B`, this map is continuous on `Q`, and
  injective there except that it collapses `A` to one point.
* Hence `A` is the only inverse set of the restriction of `g⁻¹ ∘ k ∘ g` to the cell `Q`, so it is
  cellular.

## Main results

* `TauCeti.isCellularSet_preimage_singleton_of_injOn`: **Brown's theorem on two inverse sets**: if
  a map of `Sⁿ` onto itself, `n ≥ 2`, is injective off the fibres over two points, then these
  fibres are cellular.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorem 4.
-/

public section

open Function Metric Module Set Filter Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {g : sphere (0 : F) 1 → sphere (0 : F) 1} {a b : sphere (0 : F) 1}

/-- **Undoing the collapse of `g⁻¹(b)`.** Let `g` be a continuous surjection of the sphere which is
injective off `g⁻¹{a, b}`, and let `Q` be a compact set whose image misses a point `p ≠ b`. Then
there is a map `h`, continuous on `Q`, whose only identifications on `Q` are those of `g⁻¹(a)`:
it is `g⁻¹ ∘ k ∘ g` off `g⁻¹(b)` and the identity on `g⁻¹(b)`, for a map `k` of the sphere which is
the identity near `b` and pushes `g(Q)` off `a`. -/
private theorem exists_continuousOn_eq_iff (hg : Continuous g) (hgs : Surjective g)
    (hab : a ≠ b) (hinj : InjOn g (g ⁻¹' {a, b})ᶜ) {Q : Set (sphere (0 : F) 1)}
    (hQ : IsCompact Q) {p : sphere (0 : F) 1} (hp : p ∉ g '' Q) (hbp : b ≠ p) :
    ∃ h : sphere (0 : F) 1 → sphere (0 : F) 1, ContinuousOn h Q ∧
      ∀ x ∈ Q, ∀ x' ∈ Q, (h x = h x' ↔ x = x' ∨ g x = a ∧ g x' = a) := by
  classical
  have : Nonempty (sphere (0 : F) 1) := ⟨a⟩
  set U := (g ⁻¹' {a, b})ᶜ
  obtain ⟨k, hkc, hki, hkid, hka⟩ := exists_continuousOn_injOn_mapsTo_sphere hbp
    (hQ.image hg) hp (isOpen_compl_singleton.mem_nhds hab.symm)
  have hkb : k b = b := hkid.eq_of_nhds
  have hfp {x} (hx : x ∈ Q) : g x ≠ p := fun h ↦ hp ⟨x, hx, h⟩
  have hgU : g '' U = {a, b}ᶜ := by
    refine Subset.antisymm (image_subset_iff.2 fun x hx ↦ hx) fun y hy ↦ ?_
    obtain ⟨x, rfl⟩ := hgs y
    exact ⟨x, hy, rfl⟩
  -- The inverse of `g` is continuous on `g '' U`, since the sphere is compact.
  have hinv : ContinuousOn (invFunOn g U) (g '' U) := by
    refine hg.continuousOn.continuousOn_invFunOn_image_of_isCompact isCompact_univ
      (subset_univ _) hinj (disjoint_left.2 ?_)
    rintro _ ⟨x, hx, rfl⟩ ⟨x', hx', hx'x⟩
    exact hx' (by rw [mem_preimage, hx'x]; exact not_not.1 hx.2)
  -- Off `g⁻¹(b)`, the point `k (g x)` is neither `a` nor `b`.
  have hkU {x} (hx : x ∈ Q) (hxb : g x ≠ b) : k (g x) ∈ g '' U := by
    rw [hgU, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hka (mem_image_of_mem g hx), fun h ↦ hxb (hki (hfp hx) hbp (h.trans hkb.symm))⟩
  set h : sphere (0 : F) 1 → sphere (0 : F) 1 :=
    fun x ↦ if g x = b then x else invFunOn g U (k (g x))
  have hh {x} (hxb : g x ≠ b) : h x = invFunOn g U (k (g x)) := by simp [h, hxb]
  have hhU {x} (hx : x ∈ Q) (hxb : g x ≠ b) : h x ∈ U ∧ g (h x) = k (g x) := by
    rw [hh hxb]
    exact ⟨invFunOn_mem (hkU hx hxb), invFunOn_eq (hkU hx hxb)⟩
  have hgh {x} (hx : x ∈ Q) : g (h x) = k (g x) := by
    by_cases hxb : g x = b
    · simp [h, hxb, hkb]
    · exact (hhU hx hxb).2
  refine ⟨h, fun x hx ↦ ?_, fun x hx x' hx' ↦ ⟨fun hxx' ↦ ?_, ?_⟩⟩
  · -- Near a point mapped close to `b`, `h` is the identity; elsewhere it is `g⁻¹ ∘ k ∘ g`.
    obtain ⟨W, hWk, hW, hbW⟩ := _root_.eventually_nhds_iff.1 hkid
    by_cases hxW : g x ∈ W
    · have hid : h =ᶠ[𝓝[Q] x] id := by
        filter_upwards [self_mem_nhdsWithin,
          hg.continuousWithinAt.preimage_mem_nhdsWithin (hW.mem_nhds hxW)] with x' hx' hx'W
        by_cases hx'b : g x' = b
        · simp [h, hx'b]
        have hkx' : k (g x') = g x' := hWk _ hx'W
        have hx'U : x' ∈ U := by
          simp only [U, mem_compl_iff, mem_preimage, mem_insert_iff, mem_singleton_iff, not_or]
          exact ⟨fun h ↦ hka (mem_image_of_mem g hx') (hkx'.trans h), hx'b⟩
        exact hinj (hhU hx' hx'b).1 hx'U ((hhU hx' hx'b).2.trans hkx')
      exact continuousWithinAt_id.congr_of_eventuallyEq hid (hid.eq_of_nhdsWithin hx)
    · have hxb : g x ≠ b := fun h ↦ hxW (h ▸ hbW)
      have hkg : ContinuousWithinAt (fun x ↦ k (g x)) (Q ∩ g ⁻¹' {b}ᶜ) x :=
        ((hkc.continuousAt (isOpen_compl_singleton.mem_nhds (hfp hx))).comp
          hg.continuousAt).continuousWithinAt
      have hcont : ContinuousWithinAt h (Q ∩ g ⁻¹' {b}ᶜ) x :=
        ((hinv _ (hkU hx hxb)).comp (f := fun x' ↦ k (g x')) hkg
          fun x' hx' ↦ hkU hx'.1 hx'.2).congr
          (fun x' hx' ↦ hh hx'.2) (hh hxb)
      exact hcont.mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin
        (hg.continuousWithinAt.preimage_mem_nhdsWithin (isOpen_compl_singleton.mem_nhds hxb)))
  · have hgx : g x = g x' := hki (hfp hx) (hfp hx') (by rw [← hgh hx, ← hgh hx', hxx'])
    by_cases hxb : g x = b
    · left
      simpa [h, hxb, ← hgx] using hxx'
    by_cases hxa : g x = a
    · exact .inr ⟨hxa, hgx ▸ hxa⟩
    have hxU : x ∈ U := by
      simp only [U, mem_compl_iff, mem_preimage, mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨hxa, hxb⟩
    have hx'U : x' ∈ U := fun h ↦ hxU (by rw [mem_preimage, hgx]; exact h)
    exact .inl (hinj hxU hx'U hgx)
  · rintro (rfl | ⟨hxa, hx'a⟩)
    · rfl
    · rw [hh (hxa ▸ hab), hh (hx'a ▸ hab), hxa, hx'a]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Brown's theorem on two inverse sets.** Let `g` be a continuous surjection of the unit sphere
`Sⁿ` of a real inner product space of dimension `n + 1`, `n ≥ 2`, onto itself, which is injective
off the fibres over two distinct points `a` and `b`. Then the fibre `g⁻¹(a)` is cellular, with
cells modelled on any real normed space `E` of dimension `n`. -/
theorem isCellularSet_preimage_singleton_of_injOn (hn : 2 ≤ finrank ℝ E)
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hg : Continuous g) (hgs : Surjective g) (hab : a ≠ b)
    (hinj : InjOn g (g ⁻¹' {a, b})ᶜ) : IsCellularSet E (g ⁻¹' {a}) := by
  have : PreconnectedSpace (sphere (0 : F) 1) := Subtype.preconnectedSpace
    (isConnected_sphere (by rw [← finrank_eq_rank]; exact_mod_cast (by omega : 1 < finrank ℝ F))
      0 zero_le_one).2
  -- A point `z` outside both fibres; its fibre is a single point.
  obtain ⟨z, hz⟩ : ∃ z, z ∉ g ⁻¹' {a, b} := by
    by_contra! hz
    have hAB : g ⁻¹' {a} = (g ⁻¹' {b})ᶜ := by
      ext x
      have := hz x
      simp only [mem_preimage, mem_insert_iff, mem_singleton_iff, mem_compl_iff] at this ⊢
      exact ⟨fun h h' ↦ hab (h.symm.trans h'), this.resolve_right⟩
    have hA : IsClopen (g ⁻¹' {a}) :=
      ⟨isClosed_singleton.preimage hg, hAB ▸ (isClosed_singleton.preimage hg).isOpen_compl⟩
    rcases isClopen_iff.1 hA with h | h
    · obtain ⟨x, hx⟩ := hgs a
      exact (eq_empty_iff_forall_notMem.1 h) x hx
    · obtain ⟨x, hx⟩ := hgs b
      exact hab ((eq_univ_iff_forall.1 h x : g x = a).symm.trans hx)
  -- The cell `Q = φ(closedBall 0 1)` contains both fibres in its open cell and misses `z`.
  obtain ⟨φ, hφc, hφi, hzφ, hKφ⟩ := exists_continuous_injective_subset_image_ball_sphere hEF
    (((finite_singleton b).insert a).isClosed.preimage hg).isCompact hz
  set Q := φ '' closedBall 0 1
  have hp : g z ∉ g '' Q := by
    rintro ⟨_, ⟨v, -, rfl⟩, hv⟩
    have hφv : φ v ∉ g ⁻¹' {a, b} := by
      simp only [mem_preimage, hv]
      exact hz
    exact hzφ ⟨v, hinj hφv hz hv⟩
  have hbp : b ≠ g z := fun h ↦ hz (by simp [← h])
  obtain ⟨h, hhc, hh⟩ := exists_continuousOn_eq_iff hg hgs hab hinj
    ((isCompact_closedBall 0 1).image hφc) hp hbp
  -- `f = h ∘ φ` has the single inverse set `φ⁻¹(g⁻¹(a))` on the closed ball.
  set f := h ∘ φ
  obtain ⟨x₀, hx₀⟩ := hgs a
  obtain ⟨v₀, hv₀, hφv₀⟩ := hKφ (Or.inl hx₀ : x₀ ∈ g ⁻¹' {a, b})
  have hQ {v : E} (hv : v ∈ closedBall 0 1) : φ v ∈ Q := mem_image_of_mem φ hv
  have hfib {v : E} (hv : v ∈ closedBall 0 1) : f v = f v₀ ↔ g (φ v) = a := by
    simp only [f, comp_apply]
    rw [hh _ (hQ hv) _ (hQ (ball_subset_closedBall hv₀)), hφv₀, hx₀]
    exact ⟨fun h ↦ h.elim (fun h ↦ h ▸ hx₀) And.left, fun h ↦ .inr ⟨h, rfl⟩⟩
  have hball {v : E} (hv : v ∈ closedBall 0 1) (hva : g (φ v) = a) : v ∈ ball 0 1 := by
    obtain ⟨w, hw, hwv⟩ := hKφ (Or.inl hva : φ v ∈ g ⁻¹' {a, b})
    exact hφi hwv ▸ hw
  have hcell := isCellularSet_closedBall_inter_preimage (f := f) (y := f v₀) hn hEF
    (hhc.comp hφc.continuousOn fun v hv ↦ hQ hv)
    (fun v hv v' hv' hvv' ↦ hφi <| ((hh _ (hQ hv.1) _ (hQ hv'.1)).1 hvv').resolve_right
      fun h ↦ hv.2 ((hfib hv.1).2 h.1))
    (fun ⟨v, hv, hfv⟩ ↦ sphere_disjoint_ball.ne_of_mem hv
      (hball (sphere_subset_closedBall hv) ((hfib (sphere_subset_closedBall hv)).1 hfv)) rfl)
    ⟨v₀, ball_subset_closedBall hv₀, rfl⟩
  convert hcell.image hφc hφi using 1
  ext x
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨w, hw, rfl⟩ := hKφ (Or.inl hx : x ∈ g ⁻¹' {a, b})
    exact ⟨w, ⟨ball_subset_closedBall hw, (hfib (ball_subset_closedBall hw)).2 hx⟩, rfl⟩
  · rintro ⟨v, ⟨hv, hfv⟩, rfl⟩
    exact (hfib hv).1 hfv

end TauCeti
