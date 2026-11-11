/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Separation.Hausdorff
import TauCeti.Topology.Separation.InvFunOn

/-!
# Collapsing one of two fibres of a map out of a compact set

Let `g` be continuous on a compact set `K`, with values in a Hausdorff space, and injective on `K`
off the two fibres over `a` and `b`. Given a point `p ∉ g(K)` and a map `k`, continuous and
injective off `p`, which is the identity near `b` and pushes `g(K)` into `g(K) \ {a}`, the map
`g⁻¹ ∘ k ∘ g` off the fibre over `b`, extended by the identity on that fibre, is a continuous
self-map of `K` which collapses the fibre over `a` and is injective elsewhere on `K`
(`TauCeti.exists_continuousOn_mapsTo_collapse`). Continuity off the fibre over `b` is the
continuity of inverses of maps out of compact sets
(`ContinuousOn.continuousOn_invFunOn_image_of_isCompact`).

This is the map `g⁻¹ k g` in the proof of Theorem 4 of M. Brown's proof of the generalized
Schoenflies theorem, which reduces a map with two inverse sets to one with a single inverse set.

## Main results

* `TauCeti.exists_continuousOn_mapsTo_collapse`: a continuous self-map of `K` whose only inverse
  set is the fibre of `g` over `a`.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorem 4.
-/

public section

open Function Set Filter Topology

namespace TauCeti

/-- **Collapsing one of two inverse sets.** Let `g` be continuous on a compact set `K` and
injective on `K` off the fibres over `a` and `b`, let `p ∉ g(K)`, and let `k` be a map, continuous
and injective off `p`, which is the identity near `b` and maps `g(K)` into `g(K) \ {a}`. Then
`g⁻¹ ∘ k ∘ g` off the fibre over `b`, extended by the identity on that fibre, is a continuous map
of `K` into itself which collapses the fibre over `a` and is injective elsewhere on `K`. -/
theorem exists_continuousOn_mapsTo_collapse {α β : Type*} [TopologicalSpace α]
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

end TauCeti
