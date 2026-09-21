/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.FiberBundle.Trivialization

/-!
# Local trivializations of quotient maps

A continuous local section of the quotient by a subgroup determines a local trivialization of
the quotient map.  The fiber coordinate of an element `g` is `s([g])⁻¹ * g`; its membership in
the subgroup follows from the section property.

This is the standard local product chart for a homogeneous space; see, for example, Husemoller's
*Fibre Bundles*, Chapter 4.
-/

open Set Topology

public section

namespace Subgroup

variable {G : Type*} [Group G]

noncomputable section

@[to_additive]
private theorem mk_mul_eq_of_localSection (H : Subgroup G) (U : Set (G ⧸ H))
    (s : G ⧸ H → G) (hsec : ∀ q ∈ U, (s q : G ⧸ H) = q)
    (q : G ⧸ H) (hq : q ∈ U) (h : H) :
    ((s q * (h : G) : G) : G ⧸ H) = q := by
  have hh : (s q)⁻¹ * (s q * (h : G)) ∈ H := by
    rw [inv_mul_cancel_left]
    exact h.property
  exact (QuotientGroup.eq.mpr hh).symm.trans (hsec q hq)

/-- A continuous local section of a subgroup quotient defines the standard local product chart.

On the target `U ×ˢ univ`, the chart sends `g` to `([g], s([g])⁻¹ * g)` and its inverse sends
`(q, h)` to `s(q) * h`; outside that target the inverse uses the canonical value `1`.
-/
@[to_additive
  /-- A continuous local section of an additive-subgroup quotient defines the standard local
  product chart. On the target `U ×ˢ univ`, the chart sends `g` to `([g], -s([g]) + g)` and its
  inverse sends `(q, h)` to `s(q) + h`; outside that target the inverse uses `0`. -/,
  expose]
def localSectionTrivialization [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G]
    (H : Subgroup G) (U : Set (G ⧸ H)) (hU : IsOpen U)
    (s : G ⧸ H → G) (hs : ContinuousOn s U)
    (hsec : ∀ q ∈ U, (s q : G ⧸ H) = q) :
    Bundle.Trivialization H (QuotientGroup.mk : G → G ⧸ H) := by
  classical
  refine
    { toFun := fun g ↦ ((g : G ⧸ H), if hg : (g : G ⧸ H) ∈ U then
        ⟨(s (g : G ⧸ H))⁻¹ * g, QuotientGroup.eq.mp (hsec (g : G ⧸ H) hg)⟩ else 1)
      invFun := fun qh ↦ if hq : qh.1 ∈ U then s qh.1 * qh.2 else 1
      source := (QuotientGroup.mk : G → G ⧸ H) ⁻¹' U
      target := U ×ˢ Set.univ
      map_source' := by
        intro g hg
        exact ⟨hg, Set.mem_univ _⟩
      map_target' := by
        rintro ⟨q, h⟩ ⟨hq, -⟩
        have hq' : (q, h).1 ∈ U := hq
        simp only [dite_eq_left hq', Set.mem_preimage]
        rw [mk_mul_eq_of_localSection H U s hsec q hq h]
        exact hq
      left_inv' := by
        intro g hg
        have hg' : (g : G ⧸ H) ∈ U := hg
        simp [hg']
      right_inv' := by
        rintro ⟨q, h⟩ ⟨hq, -⟩
        have hq' : (q, h).1 ∈ U := hq
        have hmk := mk_mul_eq_of_localSection H U s hsec q hq h
        simp only [dite_eq_left hq']
        apply Prod.ext
        · exact hmk
        · apply Subtype.ext
          simp [hmk, hq]
      open_source := hU.preimage QuotientGroup.continuous_mk
      open_target := hU.prod isOpen_univ
      continuousOn_toFun := by
        apply ContinuousOn.prodMk QuotientGroup.continuous_mk.continuousOn
        have hcarrier :
            ContinuousOn (fun g : G ↦ ((if hg : (g : G ⧸ H) ∈ U then
                ⟨(s (g : G ⧸ H))⁻¹ * g, QuotientGroup.eq.mp (hsec (g : G ⧸ H) hg)⟩
              else 1 : H) : G))
              ((QuotientGroup.mk : G → G ⧸ H) ⁻¹' U) := by
          intro g hg
          have hs' : ContinuousWithinAt (fun x : G ↦ s (x : G ⧸ H))
              ((QuotientGroup.mk : G → G ⧸ H) ⁻¹' U) g :=
            (hs (g : G ⧸ H) hg).comp QuotientGroup.continuous_mk.continuousAt.continuousWithinAt
              (fun _ hx ↦ hx)
          apply (hs'.inv.mul continuousWithinAt_id).congr_of_mem _ hg
          intro x hx
          have hx' : (x : G ⧸ H) ∈ U := hx
          simp [hx']
        rw [continuousOn_iff_continuous_domRestrict]
        exact (continuousOn_iff_continuous_domRestrict.mp hcarrier).subtype_mk _
      continuousOn_invFun := by
        have hcont : ContinuousOn (fun qh : (G ⧸ H) × H ↦ s qh.1 * qh.2)
            (U ×ˢ Set.univ) := by
          apply ContinuousOn.mul
          · exact hs.comp continuousOn_fst (fun _ hx ↦ hx.1)
          · exact continuous_subtype_val.comp_continuousOn continuousOn_snd
        apply hcont.congr
        intro qh hq
        simp [hq.1]
      baseSet := U
      open_baseSet := hU
      source_eq := rfl
      target_eq := rfl
      proj_toFun := by simp }

/-- The base of the quotient trivialization is the domain of the local section. -/
@[to_additive, simp]
theorem localSectionTrivialization_baseSet [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G]
    (H : Subgroup G) (U : Set (G ⧸ H))
    (hU : IsOpen U) (s : G ⧸ H → G) (hs : ContinuousOn s U)
    (hsec : ∀ q ∈ U, (s q : G ⧸ H) = q) :
    (localSectionTrivialization H U hU s hs hsec).baseSet = U := rfl

/-- On the chart source, the fiber coordinate is `s([g])⁻¹ * g`. -/
@[to_additive, simp]
theorem localSectionTrivialization_fiberCoordinate [TopologicalSpace G] [ContinuousMul G]
    [ContinuousInv G]
    (H : Subgroup G) (U : Set (G ⧸ H))
    (hU : IsOpen U) (s : G ⧸ H → G) (hs : ContinuousOn s U)
    (hsec : ∀ q ∈ U, (s q : G ⧸ H) = q) (g : G)
    (hg : (g : G ⧸ H) ∈ U) :
    (((localSectionTrivialization H U hU s hs hsec g).2 : H) : G) =
      (s (g : G ⧸ H))⁻¹ * g := by
  simp [localSectionTrivialization, hg]

/-- The inverse chart reconstructs a group element by multiplying the section by the fiber. -/
@[to_additive, simp]
theorem localSectionTrivialization_symm_apply [TopologicalSpace G] [ContinuousMul G]
    [ContinuousInv G]
    (H : Subgroup G) (U : Set (G ⧸ H))
    (hU : IsOpen U) (s : G ⧸ H → G) (hs : ContinuousOn s U)
    (hsec : ∀ q ∈ U, (s q : G ⧸ H) = q) (q : G ⧸ H) (hq : q ∈ U) (h : H) :
    (localSectionTrivialization H U hU s hs hsec).toOpenPartialHomeomorph.symm (q, h) =
      s q * h := by
  simp [localSectionTrivialization, hq]

end

end Subgroup
