/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Colimit.Ring
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.DirectLimit

/-!
# Checks for the adic spectrum of a directed colimit

1. **Mathlib's direct limit of rings**: the colimit hypotheses of
   `TauCeti.ValuationSpectrum.directLimitHomeomorph` hold for `Ring.DirectLimit` with its
   canonical maps, so `Spv` of any directed colimit of commutative rings is the inverse limit of
   the valuation spectra of the stages.
2. **Constant system**: for a Huber ring `L` with plus ring `L⁺` and the constant system with
   identity transition maps over a nonempty directed index set, every hypothesis of
   `TauCeti.ValuationSpectrum.spaDirectLimitHomeomorph` holds, the ideal of definition consisting
   of topologically nilpotent elements, and every coordinate of the image of `v ∈ Spa(L, L⁺)` is
   `v` itself: the system recovers its own spectrum with identity projections.
-/

open TauCeti TauCeti.Huber TauCeti.ValuationSpectrum

namespace SpaDirectLimitChecks

/-- **Mathlib's direct limit of rings** satisfies the colimit hypotheses, so its valuation
spectrum is the inverse limit of the valuation spectra of the stages. -/
noncomputable example {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (G : ι → Type*) [∀ i, CommRing (G i)] (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h ↦ f i j h] :
    Spv (Ring.DirectLimit G fun i j h ↦ f i j h) ≃ₜ
      {w : ∀ i, Spv (G i) | ∀ i j (h : i ≤ j), comap (f i j h) (w j) = w i} :=
  directLimitHomeomorph (φ := fun i ↦ Ring.DirectLimit.of G (fun i j h ↦ f i j h) i)
    (fun i j h a ↦ Ring.DirectLimit.of_f h a) Ring.DirectLimit.exists_of
    fun i a b hab ↦ by
      obtain ⟨j, hij, hj⟩ := Ring.DirectLimit.of.zero_exact (G := G) (f' := f) (i := i)
        (x := a - b) (by rw [map_sub, hab, sub_self])
      exact ⟨j, hij, sub_eq_zero.mp (by rwa [map_sub] at hj)⟩

/-- **Constant system**: the constant directed system on a Huber pair `(L, L⁺)` recovers
`Spa(L, L⁺)`, each coordinate of the comparison map being the identity. -/
example {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] {L : Type*} [CommRing L]
    [TopologicalSpace L] [IsTopologicalRing L] (P : PairOfDefinition L) (Lplus : Subring L)
    (v : spa Lplus) (i : ι) :
    letI : DirectedSystem (fun _ : ι ↦ L) fun _ _ _ ↦ RingHom.id L :=
      ⟨fun _ _ ↦ rfl, fun _ _ _ _ _ _ ↦ rfl⟩
    (spaDirectLimitHomeomorph (t := fun _ _ _ ↦ RingHom.id L) (φ := fun _ ↦ RingHom.id L)
      (fun _ ↦ Lplus) Lplus (fun _ ↦ continuous_id) (fun _ _ ha ↦ ha) (fun _ _ _ _ ↦ rfl)
      (fun x ↦ ⟨Classical.arbitrary ι, x, rfl⟩) (fun _ _ _ ↦ continuous_id) (fun _ _ _ _ ha ↦ ha)
      (fun i _ _ hab ↦ ⟨i, le_rfl, hab⟩) P
      (fun a ha ↦ ⟨Classical.arbitrary ι, a, P.isTopologicallyNilpotent_of_mem_idealOfDefinition ha,
        rfl⟩)
      (fun x hx ↦ ⟨Classical.arbitrary ι, x, hx, rfl⟩) v : ∀ _ : ι, spa Lplus) i = v := by
  rw [spaDirectLimitHomeomorph_apply_coe]
  exact congr_fun (spaComap_id Lplus) v

end SpaDirectLimitChecks
