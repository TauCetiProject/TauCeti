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
import Mathlib.Topology.Separation.Connected
import TauCeti.Topology.CellularSet.InverseSet
import TauCeti.Topology.Separation.Collapse
import TauCeti.Topology.Sphere.OpenCell
import TauCeti.Topology.Sphere.Shrink

/-!
# Both inverse sets of a map of a sphere onto itself with two inverse sets are cellular

Let `g` be a continuous surjection of the unit sphere `Sⁿ` of a real inner product space of
dimension `n + 1 ≥ 3` onto itself, and suppose that `g` is injective off the two fibres `g⁻¹(a)`
and `g⁻¹(b)`: in M. Brown's terminology, `g` has at most two *inverse sets*. Then each of the two
fibres is cellular (`TauCeti.isCellularSet_preimage_singleton_of_injOn`, applied with `a` and `b`
in either order). This is Theorem 4 of Brown's proof
of the generalized Schoenflies theorem. It applies to Brown's collapse of the outside of a
bicollared sphere onto the two poles (`TauCeti.IsBicollar.exists_collapse`), whose inverse sets are
then cellular; collapsing them identifies the closures of the two complementary domains with
closed hemispheres (`TauCeti.IsCellularSet.exists_homeomorph_preimage_hemisphere`).

The proof reduces to the case of one inverse set, Brown's Theorem 3
(`TauCeti.isCellularSet_closedBall_inter_preimage`). Choose a point `z` off both fibres, and the
closed cell `Q` of `Sⁿ` read through the stereographic chart from `z` as a large closed ball,
whose interior contains both fibres (`TauCeti.exists_subset_image_ball_sphere`). Since `g` is
surjective and `g⁻¹(b)` lies in the interior of `Q`, the image `g(Q)` is a neighbourhood of `b`,
and `g z ∉ g(Q)`. A radial squeeze `k` about `b`, read in the stereographic chart from `g z`
(`TauCeti.exists_continuousOn_injOn_mapsTo_sphere`), is the identity near `b`, injective off `g z`,
and pushes `g(Q)` into `g(Q) \ {a}`. The map
`G = g⁻¹ ∘ k ∘ g` on `Q` off `g⁻¹(b)`, extended by the identity on `g⁻¹(b)`, is then a continuous
map of `Q` into itself whose only inverse set is `g⁻¹(a)`
(`TauCeti.exists_continuousOn_mapsTo_collapse`), so `g⁻¹(a)` is cellular by Theorem 3.

## Main results

* `TauCeti.isCellularSet_preimage_singleton_of_injOn`: **Brown's theorem on two inverse sets**:
  if a continuous surjection of `Sⁿ`, `n ≥ 2`, onto itself is injective off the fibres over `a`
  and `b`, then the fibre over `a` is cellular.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorem 4.
-/

public section

open Function Metric Module Set Filter Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The fibre over `a` is cellular, assuming moreover `a ≠ b`. -/
private theorem isCellularSet_preimage_singleton_of_injOn_of_ne [FiniteDimensional ℝ E]
    (hn : 2 ≤ finrank ℝ E)
    (hEF : finrank ℝ F = finrank ℝ E + 1) {g : sphere (0 : F) 1 → sphere (0 : F) 1}
    (hg : Continuous g) (hgs : Surjective g) {a b : sphere (0 : F) 1}
    (hinj : InjOn g (g ⁻¹' {a, b})ᶜ) (hab : a ≠ b) : IsCellularSet E (g ⁻¹' {a}) := by
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  have hmem {x : sphere (0 : F) 1} : x ∈ g ⁻¹' {a, b} ↔ g x = a ∨ g x = b := by simp
  -- A point `z` off both fibres: the sphere is connected, hence infinite.
  have : PreconnectedSpace (sphere (0 : F) 1) := Subtype.preconnectedSpace <|
    isPreconnected_sphere (by rw [← finrank_eq_rank]; exact_mod_cast (by omega : 1 < finrank ℝ F))
      0 1
  have : Nontrivial (sphere (0 : F) 1) := ⟨⟨a, b, hab⟩⟩
  have := PreconnectedSpace.infinite (X := sphere (0 : F) 1)
  obtain ⟨y, hy⟩ := (toFinite {a, b}).infinite_compl.nonempty
  obtain ⟨z, rfl⟩ := hgs y
  have hzb : g z ≠ b := fun h ↦ hy (.inr h)
  have hzAB : z ∉ g ⁻¹' {a, b} := hy
  -- A closed cell `K = e(closedBall 0 1)` missing `z`, whose interior contains both fibres.
  obtain ⟨e, hec, hei, hez, heO, hABe⟩ := exists_subset_image_ball_sphere (E := E) hEF
    ((toFinite {a, b}).isClosed.preimage hg).isCompact hzAB
  set K := e '' closedBall 0 1
  have hK : IsCompact K := (isCompact_closedBall 0 1).image hec
  -- `g z ∉ g(K)`, since `g` is injective at `z`.
  have hpK : g z ∉ g '' K := by
    rintro ⟨_, ⟨v, -, rfl⟩, hv⟩
    exact hez v (hinj (fun h ↦ hzAB (by rw [hmem, ← hv]; exact hmem.1 h)) hzAB hv)
  -- `g(K)` contains the neighbourhood `N` of `b` of the points whose fibres meet the open cell.
  set N := (g '' (e '' ball 0 1)ᶜ)ᶜ
  have hN : N ∈ 𝓝 b := by
    refine ((heO.isClosed_compl.isCompact.image hg).isClosed.isOpen_compl).mem_nhds ?_
    rintro ⟨x, hx, hxb⟩
    exact hx (hABe (hmem.2 (.inr hxb)))
  have hNK : N ⊆ g '' K := fun y hy ↦ by
    obtain ⟨x, rfl⟩ := hgs y
    by_cases hx : x ∈ e '' ball 0 1
    · exact mem_image_of_mem g (image_mono ball_subset_closedBall hx)
    · exact absurd (mem_image_of_mem g hx) hy
  -- The squeeze `k` about `b`, pushing `g(K)` into `N \ {a}`.
  obtain ⟨k, hkc, hki, hkid, hkN⟩ := exists_continuousOn_injOn_mapsTo_sphere (Ne.symm hzb)
    (hK.image hg) hpK
    (inter_mem hN (isOpen_compl_singleton.mem_nhds (mem_compl_singleton_iff.2 hab.symm)))
  have : Nonempty (sphere (0 : F) 1) := ⟨a⟩
  obtain ⟨G, hGc, hGK, hGf⟩ := exists_continuousOn_mapsTo_collapse hg.continuousOn hK hab
    (Ne.symm hzb) hpK (hinj.mono fun x hx ↦ hx.2) hkc hki hkid
    (hkN.mono_right fun y hy ↦ ⟨hNK hy.1, hy.2⟩)
  -- Brown's Theorem 3 applies to `G ∘ e`, whose only inverse set is `e⁻¹(g⁻¹(a))`.
  obtain ⟨x₀, hv₀a⟩ := hgs a
  obtain ⟨v₀, hv₀, rfl⟩ := hABe (hmem.2 (.inl hv₀a))
  set y := G (e v₀)
  have hfib (v : E) (hv : v ∈ closedBall (0 : E) 1) : G (e v) = y ↔ g (e v) = a := by
    rw [hGf _ ⟨v, hv, rfl⟩ _ ⟨v₀, ball_subset_closedBall hv₀, rfl⟩, hv₀a]
    exact ⟨fun h ↦ h.elim (· ▸ hv₀a) And.left, fun h ↦ .inr ⟨h, rfl⟩⟩
  have hball (v : E) (hv : v ∈ closedBall (0 : E) 1) (hva : g (e v) = a) : v ∈ ball (0 : E) 1 := by
    obtain ⟨w, hw, hwv⟩ := hABe (hmem.2 (.inl hva))
    exact hei hwv ▸ hw
  have hcell := isCellularSet_closedBall_inter_preimage (f := G ∘ e) (y := y) hn hEF
    (hGc.comp hec.continuousOn fun v hv ↦ ⟨v, hv, rfl⟩)
    (fun v hv w hw h ↦ by
      rcases (hGf _ ⟨v, hv.1, rfl⟩ _ ⟨w, hw.1, rfl⟩).1 h with h | ⟨hva, -⟩
      · exact hei h
      · exact absurd ((hfib v hv.1).2 hva) hv.2)
    (by
      rintro ⟨v, hv, hvy⟩
      exact sphere_disjoint_ball.ne_of_mem hv (hball v (sphere_subset_closedBall hv)
        ((hfib v (sphere_subset_closedBall hv)).1 hvy)) rfl)
    ⟨v₀, ball_subset_closedBall hv₀, rfl⟩
  convert hcell.image hec hei using 1
  ext x
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨v, hv, rfl⟩ := hABe (hmem.2 (.inl hx))
    exact ⟨v, ⟨ball_subset_closedBall hv, (hfib v (ball_subset_closedBall hv)).2 hx⟩, rfl⟩
  · rintro ⟨v, ⟨hv, hvy⟩, rfl⟩
    exact (hfib v hv).1 hvy

/-- **Brown's theorem on two inverse sets.** Let `E` be a real normed space of dimension `n ≥ 2`
and `g` a continuous surjection of the unit sphere `Sⁿ` of a real inner product space of dimension
`n + 1` onto itself. If `g` is injective off the two fibres over `a` and `b`, so that these are its
only inverse sets, then the fibre over `a` is cellular, with cells modelled on `E`. -/
theorem isCellularSet_preimage_singleton_of_injOn (hn : 2 ≤ finrank ℝ E)
    (hEF : finrank ℝ F = finrank ℝ E + 1) {g : sphere (0 : F) 1 → sphere (0 : F) 1}
    (hg : Continuous g) (hgs : Surjective g) {a b : sphere (0 : F) 1}
    (hinj : InjOn g (g ⁻¹' {a, b})ᶜ) : IsCellularSet E (g ⁻¹' {a}) := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  rcases ne_or_eq a b with hab | rfl
  · exact isCellularSet_preimage_singleton_of_injOn_of_ne hn hEF hg hgs hinj hab
  · -- With a single inverse set, replace the second fibre by the fibre over `-a`.
    refine isCellularSet_preimage_singleton_of_injOn_of_ne hn hEF hg hgs (b := -a)
      (hinj.mono (compl_subset_compl.2 (preimage_mono (by simp)))) ?_
    exact ne_neg_of_mem_unit_sphere ℝ a

end TauCeti
