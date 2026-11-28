/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Coordinate box volumes, pushforward kernels, and `Sum.elim` volume preservation

Three elementary measure-theoretic utilities used in disintegrating volume along quadric blocks:

* `TauCeti.volume_pi_const`: the product volume of a uniform box `{x : κ → A | ∀ i, x i ∈ S}` is
  `volume S ^ Fintype.card κ`.
* `TauCeti.exists_kernel_eq_map`: the pushforward of an s-finite measure `ζ` along a jointly
  measurable family `K : X × Z → Y` defines an s-finite Markov/measure kernel
  `l : ProbabilityTheory.Kernel X Y` with `l x = ζ.map (fun z ↦ K (x, z))`.
* `TauCeti.measurePreserving_sumElim_comp_symm`: joining two coordinate blocks `(η → A) × (B → A)`
  along an equivalence `e : η ⊕ B ≃ κ` preserves product volume.

## Provenance

Adapted from `New.Floors.volume_coordinateBox`, `New.Floors.exists_kernel_eq_map`, and
`New.Floors.measurePreserving_sumElim_comp_symm` in `grh-lean`
(https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
file `src/Lib/DiscreteSeries/Bruhat/QuadricBlocks.lean`).
-/

public section

namespace TauCeti

open MeasureTheory Measure ProbabilityTheory

/-- The volume of the uniform coordinate box `{x : κ → A | ∀ i, x i ∈ S}` equals
`volume S ^ Fintype.card κ`. -/
theorem volume_pi_const {A κ : Type*} [Fintype κ] [MeasureSpace A]
    [SigmaFinite (volume : Measure A)] (S : Set A) :
    volume {x : κ → A | ∀ i : κ, x i ∈ S} = (volume S) ^ Fintype.card κ := by
  have hbox : {x : κ → A | ∀ i : κ, x i ∈ S} = Set.univ.pi fun _ : κ ↦ S :=
    Set.ext fun _ ↦ by simp
  rw [hbox, volume_pi_pi, Finset.prod_const, Finset.card_univ]

/-- Pushing forward an s-finite measure `ζ` along a jointly measurable family `K : X × Z → Y`
produces an s-finite kernel `l : Kernel X Y` with `l x = ζ.map (fun z ↦ K (x, z))`. -/
theorem exists_kernel_eq_map {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (ζ : Measure Z) [SFinite ζ] {K : X × Z → Y} (hK : Measurable K) :
    ∃ l : Kernel X Y, IsSFiniteKernel l ∧ ∀ x : X, l x = ζ.map fun z : Z ↦ K (x, z) := by
  refine ⟨(Kernel.id ×ₖ Kernel.const X ζ).map K, inferInstance, fun x ↦ ?_⟩
  rw [Kernel.map_apply _ hK, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, dirac_prod,
    Measure.map_map hK measurable_prodMk_left]
  rfl

/-- Joining two coordinate blocks `(η → A) × (B → A)` along an equivalence `e : η ⊕ B ≃ κ`
preserves product volume. -/
theorem measurePreserving_sumElim_comp_symm {A η B κ : Type*} [Fintype η] [Fintype B] [Fintype κ]
    [MeasureSpace A] [SigmaFinite (volume : Measure A)] (e : η ⊕ B ≃ κ) :
    MeasurePreserving (fun p : (η → A) × (B → A) ↦ Sum.elim p.fst p.snd ∘ e.symm)
      (volume.prod volume) volume := by
  classical
  have hsum : MeasurePreserving (fun p : (η → A) × (B → A) ↦ Sum.elim p.fst p.snd)
      (volume.prod volume) volume :=
    volume_measurePreserving_sumPiEquivProdPi_symm fun _ ↦ A
  exact (volume_measurePreserving_piCongrLeft (fun _ : η ⊕ B ↦ A) e.symm).symm.comp hsum

end TauCeti
