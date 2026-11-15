/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Isomorphism.Basic
public import TauCeti.Combinatorics.Network.Connectivity.Basic

/-!
# Directed connectivity under network isomorphisms

A network isomorphism relabels vertices and individual arrows. Reachability after deleting
vertices or arrows is preserved when the deleted set is transported by the corresponding
equivalence. Consequently local arc reachability, arc strength, vertex strength, and both
numerical connectivity invariants are independent of these labels.

These results let connectivity certificates be transferred between isomorphic networks,
including networks on different vertex types. They require no finiteness and retain the
identities of loops and parallel arrows. Capacities play no role in connectivity.
-/

public section

namespace TauCeti.Network.Iso

open Finset

universe u u' v v' w

variable {K : Type w} [LE K] {V : Type u} {W : Type u'}
variable {N : Network.{u, v} K V} {N' : Network.{u', v'} K W}
variable (e : N ≃ₙ N') {s t : V} {k : ℕ}

include e

/-- Relabelling a network preserves reachability after deleting the corresponding arrows. -/
@[simp]
theorem reachableWithout_preimage_iff (F : Set (Σ x y, N'.Hom x y)) :
    ReachableWithout (e.totalHomEquiv ⁻¹' F) s t ↔
      ReachableWithout F (e.vertexEquiv s) (e.vertexEquiv t) := by
  constructor
  · intro h
    exact h.mem_of_mem
      (C := {v | ReachableWithout F (e.vertexEquiv s) (e.vertexEquiv v)})
      (.refl _ _) fun x y a hx ha ↦ hx.tail (e.homEquiv x y a) (by
        simpa only [Set.mem_preimage, totalHomEquiv_apply] using ha)
  · intro h
    have hmap : ∀ {x y : W}, ReachableWithout F x y →
        ReachableWithout (e.totalHomEquiv ⁻¹' F)
          (e.symm.vertexEquiv x) (e.symm.vertexEquiv y) := by
      intro x y hxy
      exact hxy.mem_of_mem
        (C := {v | ReachableWithout (e.totalHomEquiv ⁻¹' F)
          (e.symm.vertexEquiv x) (e.symm.vertexEquiv v)})
        (.refl _ _) fun a b f ha hf ↦ ha.tail (e.symm.homEquiv a b f) (by
          rw [Set.mem_preimage, ← e.symm.totalHomEquiv_apply ⟨a, b, f⟩, totalHomEquiv_symm,
            Equiv.apply_symm_apply]
          exact hf)
    simpa only [symm_vertexEquiv_apply_vertexEquiv] using hmap h

/-- Relabelling a network preserves reachability after deleting the corresponding vertices. -/
@[simp]
theorem reachableAvoiding_preimage_iff (X : Set W) :
    ReachableAvoiding N.Hom (e.vertexEquiv ⁻¹' X) s t ↔
      ReachableAvoiding N'.Hom X (e.vertexEquiv s) (e.vertexEquiv t) := by
  constructor
  · intro h
    exact h.mem_of_mem
      (C := {v | ReachableAvoiding N'.Hom X (e.vertexEquiv s) (e.vertexEquiv v)})
      (.refl h.source_notMem) fun x y a hx _ hy ↦ hx.tail (e.homEquiv x y a) hy
  · intro h
    have hmap : ∀ {x y : W}, ReachableAvoiding N'.Hom X x y →
        ReachableAvoiding N.Hom (e.vertexEquiv ⁻¹' X)
          (e.symm.vertexEquiv x) (e.symm.vertexEquiv y) := by
      intro x y hxy
      exact hxy.mem_of_mem
        (C := {v | ReachableAvoiding N.Hom (e.vertexEquiv ⁻¹' X)
          (e.symm.vertexEquiv x) (e.symm.vertexEquiv v)})
        (.refl (by simpa using hxy.source_notMem)) fun a b f ha _ hb ↦
          ha.tail (e.symm.homEquiv a b f) (by simpa using hb)
    simpa only [symm_vertexEquiv_apply_vertexEquiv] using hmap h

/-- Local arc reachability is unchanged by a network isomorphism, including when the two
terminals coincide. -/
theorem isArcReachable_iff :
    IsArcReachable N.Hom k s t ↔
      IsArcReachable N'.Hom k (e.vertexEquiv s) (e.vertexEquiv t) := by
  classical
  rw [isArcReachable_def, isArcReachable_def]
  constructor
  · intro h F hF
    have hr := h (F.map e.totalHomEquiv.symm.toEmbedding) (by simpa using hF)
    apply (e.reachableWithout_preimage_iff (F : Set _)).1
    convert hr using 1
    ext a
    simp only [Set.mem_preimage, mem_coe, mem_map_equiv, Equiv.symm_symm]
  · intro h F hF
    have hr := h (F.map e.totalHomEquiv.toEmbedding) (by simpa using hF)
    have := (e.symm.reachableWithout_preimage_iff (F : Set _)).1 (by
      convert hr using 1
      ext a
      simp only [Set.mem_preimage, mem_coe, mem_map_equiv, totalHomEquiv_symm])
    simpa using this

/-- Global arc-strength thresholds are preserved and reflected by network isomorphisms. -/
theorem isArcStrong_iff : IsArcStrong N.Hom k ↔ IsArcStrong N'.Hom k := by
  rw [isArcStrong_def, isArcStrong_def]
  constructor
  · intro h x y
    obtain ⟨x, rfl⟩ := e.vertexEquiv.surjective x
    obtain ⟨y, rfl⟩ := e.vertexEquiv.surjective y
    exact e.isArcReachable_iff.1 (h x y)
  · intro h x y
    exact e.isArcReachable_iff.2 (h _ _)

/-- Vertex-strength thresholds are preserved and reflected by network isomorphisms, including
on empty vertex types. -/
theorem isVertexStrong_iff : IsVertexStrong N.Hom k ↔ IsVertexStrong N'.Hom k := by
  classical
  rw [isVertexStrong_def, isVertexStrong_def, ← ENat.card_congr e.vertexEquiv]
  refine and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · intro h X hX s hs t ht
    obtain ⟨s, rfl⟩ := e.vertexEquiv.surjective s
    obtain ⟨t, rfl⟩ := e.vertexEquiv.surjective t
    apply (e.reachableAvoiding_preimage_iff (X : Set W)).1
    have hr := h (X.map e.vertexEquiv.symm.toEmbedding) (by simpa using hX)
      (by simpa using hs) (by simpa using ht)
    convert hr using 1
    ext v
    simp
  · intro h X hX s hs t ht
    have hr := h (X.map e.vertexEquiv.toEmbedding) (by simpa using hX)
      (s := e.vertexEquiv s) (by simpa using hs)
      (t := e.vertexEquiv t) (by simpa using ht)
    apply (e.reachableAvoiding_preimage_iff
      ((X.map e.vertexEquiv.toEmbedding : Finset W) : Set W)).2 at hr
    simpa using hr

/-- Arc connectivity is invariant under network isomorphism. -/
theorem arcConnectivity_eq : arcConnectivity N.Hom = arcConnectivity N'.Hom :=
  ENat.eq_of_forall_natCast_le_iff fun k ↦ by
    rw [← isArcStrong_iff_le_arcConnectivity, ← isArcStrong_iff_le_arcConnectivity,
      e.isArcStrong_iff]

/-- Vertex strong connectivity is invariant under network isomorphism. The supremum definition
also handles the empty vertex type, where the invariant is zero. -/
theorem vertexStrongConnectivity_eq :
    vertexStrongConnectivity N.Hom = vertexStrongConnectivity N'.Hom := by
  cases isEmpty_or_nonempty V with
  | inl hV =>
    let : IsEmpty W := ⟨fun w ↦ hV.false (e.vertexEquiv.symm w)⟩
    simp
  | inr hV =>
    let : Nonempty W := hV.map e.vertexEquiv
    exact ENat.eq_of_forall_natCast_le_iff fun k ↦ by
      rw [← isVertexStrong_iff_le_vertexStrongConnectivity,
        ← isVertexStrong_iff_le_vertexStrongConnectivity, e.isVertexStrong_iff]

end TauCeti.Network.Iso
