/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.FiberBundle.Trivialization

/-!
# Local trivializations of orbit maps

Let a topological group `G` act on a space `X`, and fix a point `x₀ : X` whose orbit map
`g ↦ g • x₀` is continuous. A continuous local section `s` of the orbit map over an open set `U`,
that is, `s z • x₀ = z` for `z ∈ U`, determines a local trivialization of the orbit map over `U`
whose fibre is the stabilizer `H` of `x₀`. On the source, the preimage of `U`, the fibre coordinate
of `g` is `s(g • x₀)⁻¹ * g`, which fixes `x₀`; on the target `U ×ˢ univ`, the inverse chart
reconstructs `g` as `s(z) * h`. The chart intertwines right multiplication by `H` on `G` with right
multiplication on the fibre, so the orbit map is a principal `H`-bundle wherever such sections
exist.

This is the orbit-map counterpart of `Subgroup.localSectionTrivialization`, which trivializes the
quotient map `G → G ⧸ H` by a section; here the base is the space `X` itself rather than the
quotient, which matters when no homeomorphism `G ⧸ H ≃ₜ X` is available in advance.

## Main definitions and results

* `TauCeti.orbitMapTrivialization`: the trivialization of the orbit map of `x₀` over `U`
  determined by a continuous local section.
* `TauCeti.orbitMapTrivialization_fiberCoordinate` and
  `TauCeti.orbitMapTrivialization_symm_apply`: the chart and its inverse.
* `TauCeti.orbitMapTrivialization_apply_mul`: the chart is equivariant for right multiplication
  by the stabilizer.

## References

* D. Husemoller, *Fibre Bundles*, third edition, Chapter 4, §3.
* N. Steenrod, *The Topology of Fibre Bundles*, Part I, §7.
-/

open Set Topology

public section

namespace TauCeti

variable {G X : Type*} [Group G] [MulAction G X] {x₀ : X}

/-- If `s z • x₀ = z`, then `s(z)⁻¹ * g` fixes `x₀` whenever `g • x₀ = z`. -/
private theorem inv_mul_mem_stabilizer {s : X → G} {z : X} (hs : s z • x₀ = z) {g : G}
    (hg : g • x₀ = z) : (s z)⁻¹ * g ∈ MulAction.stabilizer G x₀ := by
  rw [MulAction.mem_stabilizer_iff, mul_smul, hg, inv_smul_eq_iff, hs]

/-- If `s z • x₀ = z` and `h` fixes `x₀`, then `s(z) * h` carries `x₀` to `z`. -/
private theorem mul_smul_eq_of_mem_stabilizer {s : X → G} {z : X} (hs : s z • x₀ = z)
    (h : MulAction.stabilizer G x₀) : (s z * h) • x₀ = z := by
  rw [mul_smul, MulAction.mem_stabilizer_iff.1 h.2, hs]

variable [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G] [TopologicalSpace X]

/-- **The local trivialization of an orbit map defined by a continuous local section.** Let
`s : X → G` be continuous on an open set `U` with `s z • x₀ = z` for `z ∈ U`. Over `U`, the orbit
map `g ↦ g • x₀` is trivialized with fibre the stabilizer of `x₀`: the chart sends `g` to
`(g • x₀, s(g • x₀)⁻¹ * g)`, and its inverse sends `(z, h)` to `s(z) * h`. Off the source and the
target the chart and its inverse take the junk values `1`. -/
noncomputable def orbitMapTrivialization (hx₀ : Continuous fun g : G ↦ g • x₀) (U : Set X)
    (hU : IsOpen U) (s : X → G) (hs : ContinuousOn s U) (hsec : ∀ z ∈ U, s z • x₀ = z) :
    Bundle.Trivialization (MulAction.stabilizer G x₀) (fun g : G ↦ g • x₀) := by
  classical
  refine
    { toFun := fun g ↦ (g • x₀, if hg : g • x₀ ∈ U then
        ⟨(s (g • x₀))⁻¹ * g, inv_mul_mem_stabilizer (hsec _ hg) rfl⟩ else 1)
      invFun := fun zh ↦ if zh.1 ∈ U then s zh.1 * zh.2 else 1
      source := (fun g : G ↦ g • x₀) ⁻¹' U
      target := U ×ˢ univ
      map_source' := by
        intro g hg
        exact ⟨hg, mem_univ _⟩
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_
      open_source := hU.preimage hx₀
      open_target := hU.prod isOpen_univ
      continuousOn_toFun := ?_
      continuousOn_invFun := ?_
      baseSet := U
      open_baseSet := hU
      source_eq := rfl
      target_eq := rfl
      proj_toFun := by
        intro g hg
        rfl }
  · rintro ⟨z, h⟩ ⟨hz, -⟩
    simp only [mem_preimage, hz, ↓reduceIte, mul_smul_eq_of_mem_stabilizer (hsec z hz) h]
  · intro g hg
    simp [show g • x₀ ∈ U from hg]
  · rintro ⟨z, h⟩ ⟨hz, -⟩
    have hgz := mul_smul_eq_of_mem_stabilizer (hsec z hz) h
    simp only [hz, ↓reduceIte, hgz, ↓reduceDIte]
    exact Prod.ext rfl (Subtype.ext (by simp))
  · refine hx₀.continuousOn.prodMk ?_
    -- On the source the fibre coordinate is `s(g • x₀)⁻¹ * g`.
    have hcarrier : ContinuousOn (fun g : G ↦ ((if hg : g • x₀ ∈ U then
        ⟨(s (g • x₀))⁻¹ * g, inv_mul_mem_stabilizer (hsec _ hg) rfl⟩ else 1 :
          MulAction.stabilizer G x₀) : G)) ((fun g : G ↦ g • x₀) ⁻¹' U) := by
      refine (((hs.comp hx₀.continuousOn fun _ hg ↦ hg).inv).mul continuousOn_id).congr
        fun g hg ↦ ?_
      simp [show g • x₀ ∈ U from hg]
    rw [continuousOn_iff_continuous_domRestrict] at hcarrier ⊢
    exact hcarrier.subtype_mk _
  · refine (((hs.comp continuousOn_fst fun zh (hz : zh ∈ U ×ˢ univ) ↦ hz.1).mul
      (continuous_subtype_val.comp_continuousOn continuousOn_snd))).congr
        fun zh (hzh : zh ∈ U ×ˢ univ) ↦ ?_
    simp [show zh.1 ∈ U from hzh.1]

variable {hx₀ : Continuous fun g : G ↦ g • x₀} {U : Set X} {hU : IsOpen U} {s : X → G}
  {hs : ContinuousOn s U} {hsec : ∀ z ∈ U, s z • x₀ = z}

/-- The base of the orbit-map trivialization is the domain of the local section. -/
@[simp]
theorem orbitMapTrivialization_baseSet :
    (orbitMapTrivialization hx₀ U hU s hs hsec).baseSet = U := (rfl)

open Classical in
/-- The orbit-map trivialization, unfolded: the base coordinate is the orbit map and the fibre
coordinate is `s(g • x₀)⁻¹ * g` on the source. -/
private theorem orbitMapTrivialization_apply (g : G) :
    orbitMapTrivialization hx₀ U hU s hs hsec g = (g • x₀, if hg : g • x₀ ∈ U then
      ⟨(s (g • x₀))⁻¹ * g, inv_mul_mem_stabilizer (hsec _ hg) rfl⟩ else 1) := (rfl)

open Classical in
/-- The inverse of the orbit-map trivialization, unfolded. -/
private theorem orbitMapTrivialization_symm_apply' (zh : X × MulAction.stabilizer G x₀) :
    (orbitMapTrivialization hx₀ U hU s hs hsec).toOpenPartialHomeomorph.symm zh =
      if zh.1 ∈ U then s zh.1 * zh.2 else 1 := (rfl)

/-- On the source, the fibre coordinate of the orbit-map trivialization is `s(g • x₀)⁻¹ * g`. -/
@[simp]
theorem orbitMapTrivialization_fiberCoordinate {g : G} (hg : g • x₀ ∈ U) :
    (((orbitMapTrivialization hx₀ U hU s hs hsec g).2 : MulAction.stabilizer G x₀) : G) =
      (s (g • x₀))⁻¹ * g := by
  simp [orbitMapTrivialization_apply, hg]

/-- The inverse of the orbit-map trivialization multiplies the section by the fibre coordinate. -/
@[simp]
theorem orbitMapTrivialization_symm_apply {z : X} (hz : z ∈ U) (h : MulAction.stabilizer G x₀) :
    (orbitMapTrivialization hx₀ U hU s hs hsec).toOpenPartialHomeomorph.symm (z, h) =
      s z * h := by
  simp [orbitMapTrivialization_symm_apply', hz]

/-- The orbit-map trivialization intertwines right multiplication by the stabilizer on `G` with
right multiplication on the fibre. -/
theorem orbitMapTrivialization_apply_mul {g : G} (hg : g • x₀ ∈ U)
    (h : MulAction.stabilizer G x₀) :
    orbitMapTrivialization hx₀ U hU s hs hsec (g * h) =
      (g • x₀, (orbitMapTrivialization hx₀ U hU s hs hsec g).2 * h) := by
  have hgh : (g * h) • x₀ = g • x₀ := by rw [mul_smul, MulAction.mem_stabilizer_iff.1 h.2]
  refine Prod.ext hgh (Subtype.ext ?_)
  rw [orbitMapTrivialization_fiberCoordinate (hgh ▸ hg), Subgroup.coe_mul,
    orbitMapTrivialization_fiberCoordinate hg, hgh, mul_assoc]

end TauCeti
