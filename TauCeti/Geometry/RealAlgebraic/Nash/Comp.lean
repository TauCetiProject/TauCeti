/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Nash.Graph
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Image
import TauCeti.Geometry.RealAlgebraic.CAD.Existence

/-!
# Composition of Nash germs

A map `g : (σ → ℝ) → (τ → ℝ)` between finite-dimensional coordinate spaces is regarded as a Nash
map germ at `x` when each of its coordinates `fun y ↦ g y i` is a Nash germ at `x`
(`TauCeti.IsNashAt`). This file proves the map form of the local Nash graph criterion and deduces
that Nash germs compose.

The proof of composition goes through semialgebraic graphs rather than through polynomial
relations. Nash coordinates of `g` have semialgebraic graphs on one open semialgebraic
neighbourhood `U` of `x`, and a Nash germ `f` at `g x` has semialgebraic graph on an open
semialgebraic neighbourhood `V` of `g x`. By the Tarski–Seidenberg theorem the part of `U` mapped
into `V` is semialgebraic and `f ∘ g` has semialgebraic graph there; it is a neighbourhood of `x`
because `g` is continuous at `x`. Since `f ∘ g` is analytic at `x`, the graph criterion makes it a
Nash germ.

## Main results

* `TauCeti.forall_isNashAt_apply_iff_exists_isSemialgebraicOn`: the coordinates of a map are Nash
  germs at `x` exactly when the map is analytic at `x` and has semialgebraic graph on some open
  semialgebraic neighbourhood of `x`.
* `TauCeti.IsNashAt.comp`: if `f` is a Nash germ at `g x` and the coordinates of `g` are Nash germs
  at `x`, then `f ∘ g` is a Nash germ at `x`.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 36, Springer, 1998, Section 8.1 (Nash functions).
-/

public section

open Filter Set Topology

namespace TauCeti

variable {σ τ : Type*} [Fintype σ] [Fintype τ] {g : (σ → ℝ) → (τ → ℝ)} {x : σ → ℝ}

/-- **The local Nash graph criterion for maps.** The coordinates of a map between
finite-dimensional coordinate spaces are Nash germs at `x` exactly when the map is analytic at `x`
and its graph is semialgebraic on some open semialgebraic neighbourhood of `x`. -/
theorem forall_isNashAt_apply_iff_exists_isSemialgebraicOn :
    (∀ i, IsNashAt (fun y ↦ g y i) x) ↔
      AnalyticAt ℝ g x ∧ ∃ U, IsOpen U ∧ x ∈ U ∧ IsSemialgebraicOn g U := by
  constructor
  · intro hg
    obtain ⟨U, hUo, hxU, hU, hgU⟩ := exists_isSemialgebraicOn_of_forall_isNashAt hg
    exact ⟨AnalyticAt.pi fun i ↦ (hg i).analyticAt, U, hUo, hxU, .pi hU hgU⟩
  · rintro ⟨hga, U, hUo, hxU, hgU⟩ i
    obtain ⟨hU, hgU⟩ := isSemialgebraicOn_pi_iff.mp hgU
    exact isNashAt_iff_exists_isSemialgebraicOn.mpr
      ⟨analyticAt_pi_iff.mp hga i, U, hUo, hxU, hU, hgU i⟩

/-- **Composition of Nash germs.** If `f` is a Nash germ at `g x` and every coordinate of `g` is a
Nash germ at `x`, then `f ∘ g` is a Nash germ at `x`. -/
theorem IsNashAt.comp {f : (τ → ℝ) → ℝ} (hf : IsNashAt f (g x))
    (hg : ∀ i, IsNashAt (fun y ↦ g y i) x) : IsNashAt (f ∘ g) x := by
  obtain ⟨hga, U, hUo, hxU, hgU⟩ := forall_isNashAt_apply_iff_exists_isSemialgebraicOn.mp hg
  obtain ⟨hfa, V, hVo, hgxV, hV, hfV⟩ := isNashAt_iff_exists_isSemialgebraicOn.mp hf
  have hW : IsSemialgebraic (U ∩ g ⁻¹' V) := hgU.isSemialgebraic_inter_preimage hV
  refine (hfV.comp (hgU.mono hW inter_subset_left) fun y hy ↦ hy.2).isNashAt
    (hfa.comp hga) ?_
  exact inter_mem (hUo.mem_nhds hxU) (hga.continuousAt.preimage_mem_nhds (hVo.mem_nhds hgxV))

end TauCeti
