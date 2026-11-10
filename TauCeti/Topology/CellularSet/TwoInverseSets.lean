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
import TauCeti.Topology.Separation.InvFunOn
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
whose interior contains both fibres. Since `g` is surjective and `g⁻¹(b)` lies in the interior of
`Q`, the image `g(Q)` is a neighbourhood of `b`, and `g z ∉ g(Q)`. A radial squeeze `k`
about `b`, read in the stereographic chart from `g z`
(`TauCeti.exists_continuousOn_injOn_mapsTo_sphere`), is the identity near `b`, injective off `g z`,
and pushes `g(Q)` into `g(Q) \ {a}`. The map
`G = g⁻¹ ∘ k ∘ g` on `Q` off `g⁻¹(b)`, extended by the identity on `g⁻¹(b)`, is then a continuous
map of `Q` into itself whose only inverse set is `g⁻¹(a)`, so `g⁻¹(a)` is cellular by Theorem 3.

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

/-- **Collapsing one of two inverse sets.** Let `g` be continuous on a compact set `K` and
injective on `K` off the fibres over `a` and `b`, let `p ∉ g(K)`, and let `k` be a map, continuous
and injective off `p`, which is the identity near `b` and maps `g(K)` into `g(K) \ {a}`. Then
`g⁻¹ ∘ k ∘ g` off the fibre over `b`, extended by the identity on that fibre, is a continuous map
of `K` into itself which collapses the fibre over `a` and is injective elsewhere on `K`. -/
private theorem exists_continuousOn_mapsTo_collapse {α β : Type*} [TopologicalSpace α]
    [Nonempty α] [TopologicalSpace β] [T2Space β] {g : α → β} {K : Set α} (hg : ContinuousOn g K)
    (hK : IsCompact K) {a b p : β} (hab : a ≠ b) (hbp : b ≠ p) (hp : p ∉ g '' K)
    (hinj : InjOn g (K \ g ⁻¹' {a, b})) {k : β → β} (hkc : ContinuousOn k {p}ᶜ)
    (hki : InjOn k {p}ᶜ) (hkid : k =ᶠ[𝓝 b] id) (hkK : MapsTo k (g '' K) (g '' K \ {a})) :
    ∃ G : α → α, ContinuousOn G K ∧ MapsTo G K K ∧
      ∀ x ∈ K, ∀ y ∈ K, G x = G y ↔ x = y ∨ g x = a ∧ g y = a := by
  classical
  set P := K \ g ⁻¹' {a, b}
  have hkb : k b = b := hkid.eq_of_nhds
  have hgp {x : α} (hx : x ∈ K) : g x ∈ ({p}ᶜ : Set β) := fun h ↦ hp ⟨x, hx, h⟩
  have hmemP {x : α} : x ∈ P ↔ x ∈ K ∧ g x ≠ a ∧ g x ≠ b := by
    simp only [P, Set.mem_sdiff, mem_preimage, mem_insert_iff, mem_singleton_iff, not_or]
  -- Off the fibre over `b`, the map `k ∘ g` takes values in `g(P)`.
  have hkP {x : α} (hx : x ∈ K) (hxb : g x ≠ b) : k (g x) ∈ g '' P := by
    obtain ⟨⟨x', hx', hx'k⟩, ha⟩ := hkK (mem_image_of_mem g hx)
    refine ⟨x', hmemP.2 ⟨hx', fun h ↦ ha (hx'k ▸ h), fun h ↦ hxb ?_⟩, hx'k⟩
    exact hki (hgp hx) hbp (hx'k.symm.trans h ▸ hkb.symm)
  set G : α → α := fun x ↦ if g x = b then x else invFunOn g P (k (g x))
  have hGb {x : α} (hx : g x = b) : G x = x := by simp [G, hx]
  have hG {x : α} (hx : g x ≠ b) : G x = invFunOn g P (k (g x)) := by simp [G, hx]
  have hGP {x : α} (hx : x ∈ K) (hxb : g x ≠ b) : G x ∈ P ∧ g (G x) = k (g x) := by
    rw [hG hxb]
    exact ⟨invFunOn_mem (hkP hx hxb), invFunOn_eq (hkP hx hxb)⟩
  refine ⟨G, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx y hy ↦ ⟨fun h ↦ ?_, ?_⟩⟩
  · -- Near a point mapped close to `b`, `G` is the identity; elsewhere it is `g⁻¹ ∘ k ∘ g`.
    obtain ⟨W, hWk, hW, hbW⟩ := _root_.eventually_nhds_iff.1 hkid
    by_cases hxW : g x ∈ W \ {a}
    · have hid : G =ᶠ[𝓝[K] x] id := by
        filter_upwards [self_mem_nhdsWithin, (hg x hx).preimage_mem_nhdsWithin
          ((hW.sdiff isClosed_singleton).mem_nhds hxW)] with x' hx' hx'W
        by_cases hx'b : g x' = b
        · exact hGb hx'b
        have hgG : g (G x') = g x' := (hGP hx' hx'b).2.trans (hWk _ hx'W.1)
        exact hinj (hGP hx' hx'b).1 (hmemP.2 ⟨hx', hx'W.2, hx'b⟩) hgG
      exact continuousWithinAt_id.congr_of_eventuallyEq hid (hid.eq_of_nhdsWithin hx)
    · have hxb : g x ≠ b := fun h ↦ hxW ⟨h ▸ hbW, h ▸ hab.symm⟩
      have hinv : ContinuousOn (invFunOn g P) (g '' P) :=
        hg.continuousOn_invFunOn_image_of_isCompact hK sdiff_subset hinj <|
          disjoint_left.2 fun _ ⟨x₁, hx₁, hx₁y⟩ ⟨x₂, hx₂, hx₂y⟩ ↦ by
            obtain ⟨-, hx₂a, hx₂b⟩ := hmemP.1 hx₂
            have : g x₁ = a ∨ g x₁ = b := by
              by_contra! h
              exact hx₁.2 (hmemP.2 ⟨hx₁.1, h⟩)
            rcases this with h | h
            exacts [hx₂a (hx₂y.trans (hx₁y.symm.trans h)), hx₂b (hx₂y.trans (hx₁y.symm.trans h))]
      have hkg : ContinuousWithinAt (fun x ↦ k (g x)) (K \ g ⁻¹' {b}) x :=
        (hkc.continuousAt (isOpen_compl_singleton.mem_nhds (hgp hx))).comp_continuousWithinAt
          ((hg x hx).mono sdiff_subset)
      have hGx : ContinuousWithinAt G (K \ g ⁻¹' {b}) x :=
        ((hinv _ (hkP hx hxb)).comp (f := fun x ↦ k (g x)) hkg fun x' hx' ↦ hkP hx'.1 hx'.2).congr
          (fun x' hx' ↦ hG hx'.2) (hG hxb)
      exact hGx.mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin
        ((hg x hx).preimage_mem_nhdsWithin (isOpen_compl_singleton.mem_nhds hxb)))
  · by_cases hxb : g x = b
    · rwa [hGb hxb]
    · exact (hmemP.1 (hGP hx hxb).1).1
  · by_cases hxb : g x = b <;> by_cases hyb : g y = b
    · exact .inl (by rwa [hGb hxb, hGb hyb] at h)
    · exact absurd (hGb hxb ▸ h ▸ (hGP hy hyb).1) fun h' ↦ (hmemP.1 h').2.2 hxb
    · exact absurd (hGb hyb ▸ h.symm ▸ (hGP hx hxb).1) fun h' ↦ (hmemP.1 h').2.2 hyb
    · have hgxy : g x = g y :=
        hki (hgp hx) (hgp hy) (by rw [← (hGP hx hxb).2, ← (hGP hy hyb).2, h])
      by_cases hxa : g x = a
      · exact .inr ⟨hxa, hgxy ▸ hxa⟩
      · exact .inl (hinj (hmemP.2 ⟨hx, hxa, hxb⟩) (hmemP.2 ⟨hy, hgxy ▸ hxa, hyb⟩) hgxy)
  · rintro (rfl | ⟨hxa, hya⟩)
    · rfl
    · rw [hG (hxa ▸ hab), hG (hya ▸ hab), hxa, hya]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A compact subset of a sphere missing a point lies in an open cell.** If `C` is a compact
subset of the unit sphere `Sⁿ` of a real inner product space of dimension `n + 1` and `z ∉ C`, then
there is a continuous injection `e` of a real normed space `E` of dimension `n` into `Sⁿ \ {z}`
such that the image of the open unit ball is open and contains `C`. It is the stereographic chart
from `z`, rescaled so that its closed unit ball contains `C` in its interior. -/
private theorem exists_subset_image_ball [FiniteDimensional ℝ E]
    (hEF : finrank ℝ F = finrank ℝ E + 1) {C : Set (sphere (0 : F) 1)} (hC : IsCompact C)
    {z : sphere (0 : F) 1} (hz : z ∉ C) :
    ∃ e : E → sphere (0 : F) 1, Continuous e ∧ Injective e ∧ (∀ v, e v ≠ z) ∧
      IsOpen (e '' ball 0 1) ∧ C ⊆ e '' ball 0 1 := by
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  have : Fact (finrank ℝ F = finrank ℝ E + 1) := ⟨hEF⟩
  set φ := stereographic' (finrank ℝ E) z
  have hφs : φ.source = {z}ᶜ := stereographic'_source z
  have hφt : φ.target = univ := stereographic'_target z
  set L := ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := E)
    (F := EuclideanSpace ℝ (Fin (finrank ℝ E))) (finrank_euclideanSpace_fin.symm)
  have hCφ : C ⊆ φ.source := by
    rw [hφs]
    rintro x hx (rfl : x = z)
    exact hz hx
  -- `C` lies in the image of the open ball of radius `R` under `φ⁻¹ ∘ L`.
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn
    (L.symm.continuous.comp_continuousOn (φ.continuousOn.mono hCφ))
  set R := max B 0 + 1
  have hR : 0 < R := by positivity
  have hsymm : Continuous φ.symm := continuousOn_univ.1 (hφt ▸ φ.continuousOn_symm)
  refine ⟨fun v ↦ φ.symm (L (R • v)), hsymm.comp (by fun_prop), fun v w h ↦
    smul_right_injective E hR.ne' (L.injective (φ.symm.injOn (by simp [hφt]) (by simp [hφt]) h)),
    fun v ↦ ?_, ?_, fun x hx ↦ ⟨R⁻¹ • L.symm (φ x), ?_, ?_⟩⟩
  · have h := φ.map_target (x := L (R • v)) (by simp [hφt])
    rwa [hφs, mem_compl_singleton_iff] at h
  · rw [show (fun v ↦ φ.symm (L (R • v))) = φ.symm ∘ (L ∘ (R • ·)) from rfl, image_comp]
    exact φ.symm.isOpen_image_of_subset_source
      ((L.toHomeomorph.isOpenMap.comp (isOpenMap_smul₀ hR.ne')) _ isOpen_ball) (by simp [hφt])
  · rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR,
      inv_mul_lt_iff₀ hR, mul_one]
    exact (hB x hx).trans_lt (by simp [R]; linarith [le_max_left B 0])
  · simp [smul_smul, hR.ne', φ.left_inv (hCφ hx)]

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
  obtain ⟨e, hec, hei, hez, heO, hABe⟩ := exists_subset_image_ball (E := E) hEF
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
