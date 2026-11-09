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
the quotient map.  On the source `mk ⁻¹' U`, the fiber coordinate of an element `g` is
`s([g])⁻¹ * g`; its membership in the subgroup follows from the section property.  On the target
`U ×ˢ univ`, the inverse chart reconstructs `g` as `s(q) * h`.

This is the standard local product chart for a homogeneous space; see, for example, Husemoller's
*Fibre Bundles*, Chapter 4.
-/

open Set Topology

public section

namespace Subgroup

variable {G : Type*} [Group G]

noncomputable section

section LocalSection

variable (H : Subgroup G)

@[to_additive]
private theorem mk_mul_eq_of_localSection {U : Set (G ⧸ H)} {s : G ⧸ H → G}
    (hsec : ∀ q ∈ U, (s q : G ⧸ H) = q) {q : G ⧸ H}
    (hq : q ∈ U) (h : H) : ((s q * h : G) : G ⧸ H) = q :=
  (QuotientGroup.eq.mpr (by simp)).symm.trans (hsec q hq)

/-- The fiber coordinate of `localSectionTrivialization`: `s([g])⁻¹ * g` over `U`, and `1`
elsewhere. -/
@[to_additive /-- The fiber coordinate of `localSectionTrivialization`: `-s([g]) + g` over `U`,
and `0` elsewhere. -/]
private def localSectionFiber (U : Set (G ⧸ H)) (s : G ⧸ H → G)
    (hsec : ∀ q ∈ U, (s q : G ⧸ H) = q) (g : G) : H :=
  letI := Classical.dec ((g : G ⧸ H) ∈ U)
  if hg : (g : G ⧸ H) ∈ U then ⟨(s g)⁻¹ * g, QuotientGroup.eq.mp (hsec _ hg)⟩ else 1

@[to_additive]
private theorem coe_localSectionFiber {U : Set (G ⧸ H)} {s : G ⧸ H → G}
    {hsec : ∀ q ∈ U, (s q : G ⧸ H) = q} {g : G}
    (hg : (g : G ⧸ H) ∈ U) : (localSectionFiber H U s hsec g : G) = (s g)⁻¹ * g := by
  simp [localSectionFiber, hg]

variable [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G]

/-- A continuous local section of a subgroup quotient defines the standard local product chart.

On the source `mk ⁻¹' U`, the chart sends `g` to `([g], s([g])⁻¹ * g)`. Its inverse sends
`(q, h)` to `s(q) * h`.
-/
@[to_additive
  /-- A continuous local section of an additive-subgroup quotient defines the standard local
  product chart. On the source `mk ⁻¹' U`, the chart sends `g` to `([g], -s([g]) + g)`. Its
  inverse sends `(q, h)` to `s(q) + h`. -/]
def localSectionTrivialization (U : Set (G ⧸ H)) (hU : IsOpen U) (s : G ⧸ H → G)
    (hs : ContinuousOn s U) (hsec : ∀ q ∈ U, (s q : G ⧸ H) = q) :
    Bundle.Trivialization H (QuotientGroup.mk : G → G ⧸ H) where
  toFun g := (g, localSectionFiber H U s hsec g)
  invFun p := s p.1 * p.2
  source := QuotientGroup.mk ⁻¹' U
  target := U ×ˢ univ
  map_source' _ hg := ⟨hg, mem_univ _⟩
  map_target' p hp := by
    rw [mem_preimage, mk_mul_eq_of_localSection H hsec hp.1]
    exact hp.1
  left_inv' g hg := by simp [coe_localSectionFiber H hg]
  right_inv' p hp := by
    have hp' := mk_mul_eq_of_localSection H hsec hp.1 p.2
    refine Prod.ext hp' (Subtype.ext ?_)
    dsimp only
    rw [coe_localSectionFiber H (hp'.symm ▸ hp.1), hp', inv_mul_cancel_left]
  open_source := hU.preimage QuotientGroup.continuous_mk
  open_target := hU.prod isOpen_univ
  continuousOn_toFun := by
    refine QuotientGroup.continuous_mk.continuousOn.prodMk ?_
    rw [IsInducing.subtypeVal.continuousOn_iff]
    exact ((hs.comp QuotientGroup.continuous_mk.continuousOn fun _ hg ↦ hg).inv.mul
      continuousOn_id).congr fun g hg ↦ coe_localSectionFiber H hg
  continuousOn_invFun :=
    (hs.comp (continuousOn_fst (s := U ×ˢ univ)) fun _ hp ↦ hp.1).mul
      (continuous_subtype_val.comp_continuousOn continuousOn_snd)
  baseSet := U
  open_baseSet := hU
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

variable {H} {U : Set (G ⧸ H)} {s : G ⧸ H → G} {hU : IsOpen U} {hs : ContinuousOn s U}
  {hsec : ∀ q ∈ U, (s q : G ⧸ H) = q}

/-- The base of the quotient trivialization is the domain of the local section. -/
@[to_additive (attr := simp)]
theorem localSectionTrivialization_baseSet :
    (localSectionTrivialization H U hU s hs hsec).baseSet = U := (rfl)

/-- On the chart source, the fiber coordinate is `s([g])⁻¹ * g`. -/
@[to_additive (attr := simp)
  /-- On the chart source, the fiber coordinate is `-s([g]) + g`. -/]
theorem localSectionTrivialization_fiberCoordinate {g : G} (hg : (g : G ⧸ H) ∈ U) :
    ((localSectionTrivialization H U hU s hs hsec g).2 : G) = (s g)⁻¹ * g :=
  coe_localSectionFiber H (hsec := hsec) hg

/-- The inverse chart reconstructs a group element by multiplying the section by the fiber. -/
@[to_additive (attr := simp)
  /-- The inverse chart reconstructs a group element by adding the fiber to the section. -/]
theorem localSectionTrivialization_symm_apply (p : (G ⧸ H) × H) :
    (localSectionTrivialization H U hU s hs hsec).toOpenPartialHomeomorph.symm p =
      s p.1 * p.2 := (rfl)

end LocalSection

end

end Subgroup
