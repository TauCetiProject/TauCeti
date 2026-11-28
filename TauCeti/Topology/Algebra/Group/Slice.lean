/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Tactic.Group

/-!
# Slices for a conjugation action

Let a group `Γ` act on a group `G` by conjugation through a homomorphism `j : Γ →* G`, both groups
carrying topologies, and let `H ⊆ Γ` be a subgroup. A pair `X ⊆ C ⊆ G` is a *slice*
(`TauCeti.IsSlice j H X C`) if `C` is closed, `C` is the set of conjugates `j γ * y * (j γ)⁻¹` of
points `y ∈ X`, such a conjugate lies in `X` exactly when `γ ∈ H`, and near `X` every point of `C`
is conjugated into `X` by an element of `Γ` close to `1`. The map `(γ, y) ↦ j γ * y * (j γ)⁻¹`
from `Γ × X` onto `C` then has the `H`-orbits `(γ * h, (j h)⁻¹ * y * j h)` as fibres
(`TauCeti.IsSlice.conj_eq_conj_iff`).

Slices are the setting of Harish-Chandra's descent of invariant distributions. Integration along
the fibres is `TauCeti.fiberIntegral`, in `TauCeti.MeasureTheory.Group.SliceIntegral`, and the
descent itself is `TauCeti.IsSlice.map_eq_zero_of_integral_eq_zero_of_eq_fiberIntegral`, in
`TauCeti.RepresentationTheory.Smooth.SliceDescent`.

## Main definitions

* `TauCeti.IsSlice j H X C`: `X ⊆ C` is a slice for the conjugation action of `Γ` through `j`, with
  stabiliser `H`.

## Main results

* `TauCeti.IsSlice.conj_mem_of_mem`, `TauCeti.IsSlice.inv_conj_mem`: `C` is stable under
  conjugation by `j Γ`, and `X` under conjugation by `j H`.
* `TauCeti.IsSlice.conj_eq_conj_iff`: the fibres of `(γ, y) ↦ j γ * y * (j γ)⁻¹` on `Γ × X` are
  the `H`-orbits.
* `TauCeti.IsSlice.of_conj_mem`: a closed set stable under conjugation by `j Γ` is a slice for the
  whole group `Γ`.

## References

* Harish-Chandra, *Harmonic analysis on reductive p-adic groups*, notes by G. van Dijk, Lecture
  Notes in Mathematics 162, Springer, 1970 (descent of invariant distributions to a slice).
* The definition adapts the declaration `New.IsSlice` of the formal proof `[ShortProof]`, grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC), file
  `src/Lib/Adelic/TraceFormula/FibreIntegral.lean`; the proofs are written independently.
-/

public section

open Filter Set Topology

namespace TauCeti

variable {Γ G : Type*} [Group Γ] [Group G] {j : Γ →* G} {H : Subgroup Γ} {X C : Set G}

variable [TopologicalSpace Γ] [TopologicalSpace G]

variable (j H X C) in
/-- `X ⊆ C ⊆ G` is a **slice** for the conjugation action of `Γ` on `G` through `j`, with stabiliser
`H`: `C` is closed and is the set of conjugates `j γ * y * (j γ)⁻¹` of points `y ∈ X`; such a
conjugate lies in `X` exactly when `γ ∈ H`; and near each point of `X`, every point of `C` is
conjugated into `X` by an element of `Γ` close to `1`. -/
structure IsSlice : Prop where
  /-- The set `C` of conjugates of `X` is closed. -/
  isClosed : IsClosed C
  /-- `C` is the set of conjugates of the points of `X`. -/
  mem_iff : ∀ c, c ∈ C ↔ ∃ γ, ∃ y ∈ X, j γ * y * (j γ)⁻¹ = c
  /-- A conjugate of a point of `X` lies in `X` exactly when the conjugating element lies in
  `H`. -/
  conj_mem_iff : ∀ γ, ∀ y ∈ X, j γ * y * (j γ)⁻¹ ∈ X ↔ γ ∈ H
  /-- Near each point `y` of `X`, the points of `C` are conjugates of points of `X` by elements of
  any given neighbourhood of `1` in `Γ`. -/
  eventually_exists_conj : ∀ y ∈ X, ∀ U ∈ 𝓝 (1 : Γ), ∀ᶠ c in 𝓝[C] y,
    ∃ u ∈ U, ∃ x ∈ X, j u * x * (j u)⁻¹ = c

namespace IsSlice

/-- A conjugate of a point of `X` lies in `C`. -/
theorem conj_mem (hs : IsSlice j H X C) (γ : Γ) {y : G} (hy : y ∈ X) :
    j γ * y * (j γ)⁻¹ ∈ C :=
  (hs.mem_iff _).2 ⟨γ, y, hy, rfl⟩

/-- The slice `X` is contained in `C`. -/
theorem subset (hs : IsSlice j H X C) : X ⊆ C := fun y hy => by
  simpa using hs.conj_mem 1 hy

/-- `C` is stable under conjugation by `j Γ`. -/
theorem conj_mem_of_mem (hs : IsSlice j H X C) (δ : Γ) {c : G} (hc : c ∈ C) :
    j δ * c * (j δ)⁻¹ ∈ C := by
  obtain ⟨γ, y, hy, rfl⟩ := (hs.mem_iff c).1 hc
  convert hs.conj_mem (δ * γ) hy using 1
  simp only [map_mul, mul_inv_rev, mul_assoc]

/-- Conjugation by `(j h)⁻¹` for `h ∈ H` preserves `X`. -/
theorem inv_conj_mem (hs : IsSlice j H X C) {h : Γ} (hh : h ∈ H) {y : G} (hy : y ∈ X) :
    (j h)⁻¹ * y * j h ∈ X := by
  simpa using (hs.conj_mem_iff h⁻¹ y hy).2 (inv_mem hh)

/-- **The fibres over `C` are the `H`-orbits.** Two points `(γ, y)` and `(γ', y')` of `Γ × X` have
the same conjugate `j γ * y * (j γ)⁻¹ = j γ' * y' * (j γ')⁻¹` exactly when
`(γ', y') = (γ * h, (j h)⁻¹ * y * j h)` for some `h ∈ H`. -/
theorem conj_eq_conj_iff (hs : IsSlice j H X C) {γ γ' : Γ} {y y' : G} (hy : y ∈ X)
    (hy' : y' ∈ X) :
    j γ * y * (j γ)⁻¹ = j γ' * y' * (j γ')⁻¹ ↔ ∃ h ∈ H, γ' = γ * h ∧ y' = (j h)⁻¹ * y * j h := by
  refine ⟨fun hc => ?_, ?_⟩
  · -- The element `h = γ⁻¹ * γ'` conjugates `y'` to `y`, hence lies in `H`.
    have hk : y' = (j (γ⁻¹ * γ'))⁻¹ * y * j (γ⁻¹ * γ') :=
      calc y' = (j γ')⁻¹ * (j γ' * y' * (j γ')⁻¹) * j γ' := by group
        _ = (j (γ⁻¹ * γ'))⁻¹ * y * j (γ⁻¹ * γ') := by
          rw [← hc]
          simp only [map_mul, map_inv]
          group
    have hkH : γ⁻¹ * γ' ∈ H := by
      have hk' : j (γ⁻¹ * γ')⁻¹ * y * (j (γ⁻¹ * γ')⁻¹)⁻¹ = y' := by rw [hk, map_inv, inv_inv]
      rw [← inv_mem_iff, ← hs.conj_mem_iff _ y hy, hk']
      exact hy'
    exact ⟨_, hkH, (mul_inv_cancel_left γ γ').symm, hk⟩
  · rintro ⟨h, -, rfl, rfl⟩
    simp only [map_mul]
    group

/-- A closed set `X` stable under conjugation by `j Γ` is a slice for the whole group `Γ`, with
`C = X`. -/
theorem of_conj_mem (hX : IsClosed X) (h : ∀ γ, ∀ y ∈ X, j γ * y * (j γ)⁻¹ ∈ X) :
    IsSlice j ⊤ X X where
  isClosed := hX
  mem_iff c := ⟨fun hc => ⟨1, c, hc, by simp⟩, fun ⟨γ, y, hy, hc⟩ => hc ▸ h γ y hy⟩
  conj_mem_iff γ y hy := by simpa using h γ y hy
  eventually_exists_conj y _ U hU := eventually_mem_nhdsWithin.mono fun c hc =>
    ⟨1, mem_of_mem_nhds hU, c, hc, by simp⟩

end IsSlice

end TauCeti
