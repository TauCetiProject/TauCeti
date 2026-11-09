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

Let `π : G → X` be a continuous map from a topological group whose fibres are the left cosets of
a subgroup `K`, such as the quotient map `G → G ⧸ K` or the orbit map `g ↦ g • x₀` of an action,
with `K` the stabilizer of `x₀`. A section `s` of `π`, continuous on an open set `U`, determines a
local trivialization of `π` over `U` with fibre `K`. On the source `π ⁻¹' U`, the fiber coordinate
of an element `g` is `s (π g)⁻¹ * g`; its membership in `K` follows from the section property.
On the target `U ×ˢ univ`, the inverse chart reconstructs `g` as `s q * h`. The chart intertwines
right multiplication by `K` on `G` with right multiplication on the fibre.

This is the standard local product chart for a homogeneous space; see, for example, Husemoller's
*Fibre Bundles*, Chapter 4, and Steenrod, *The Topology of Fibre Bundles*, §7.

## Main definitions and results

* `Subgroup.trivializationOfLocalSection`: the local trivialization of a map whose fibres are the
  left cosets of `K`, determined by a continuous local section.
* `Subgroup.trivializationOfLocalSection_apply_mul`: the chart intertwines right multiplication by
  `K` on `G` with right multiplication on the fibre.
* `Subgroup.localSectionTrivialization`: the case of the quotient map `G → G ⧸ H`.
-/

open Set Topology

public section

namespace Subgroup

variable {G : Type*} [Group G]

noncomputable section

section Projection

variable {X : Type*} {K : Subgroup G} {π : G → X} {U : Set X} {s : X → G}

@[to_additive]
private theorem map_mul_eq_of_localSection (hK : ∀ a b, π a = π b ↔ a⁻¹ * b ∈ K)
    (hsec : ∀ q ∈ U, π (s q) = q) {q : X} (hq : q ∈ U) (h : K) : π (s q * h) = q :=
  ((hK _ _).2 (by rw [inv_mul_cancel_left]; exact h.2)).symm.trans (hsec q hq)

/-- The fiber coordinate of `trivializationOfLocalSection`: over `U` it is `s (π g)⁻¹ * g`, and
elsewhere it is `1`. -/
@[to_additive /-- The fiber coordinate of `trivializationOfLocalSection`: over `U` it is
`-s (π g) + g`, and elsewhere it is `0`. -/]
private def localSectionFiber (hK : ∀ a b, π a = π b ↔ a⁻¹ * b ∈ K) (U : Set X) (s : X → G)
    (hsec : ∀ q ∈ U, π (s q) = q) (g : G) : K :=
  letI := Classical.dec (π g ∈ U)
  if hg : π g ∈ U then ⟨(s (π g))⁻¹ * g, (hK _ _).1 (hsec _ hg)⟩ else 1

@[to_additive]
private theorem coe_localSectionFiber {hK : ∀ a b, π a = π b ↔ a⁻¹ * b ∈ K}
    {hsec : ∀ q ∈ U, π (s q) = q} {g : G} (hg : π g ∈ U) :
    (localSectionFiber hK U s hsec g : G) = (s (π g))⁻¹ * g := by
  simp only [localSectionFiber, hg, ↓reduceDIte]

variable [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G] [TopologicalSpace X]

/-- Let `π : G → X` be a continuous map whose fibres are the left cosets of a subgroup `K`. A
section `s` of `π`, continuous on an open set `U`, defines the local product chart of `π` over `U`
with fibre `K`: it sends `g` over `U` to `(π g, s (π g)⁻¹ * g)`, and its inverse sends `(q, h)` to
`s q * h`. -/
@[to_additive /-- Let `π : G → X` be a continuous map whose fibres are the cosets of an additive
subgroup `K`. A section `s` of `π`, continuous on an open set `U`, defines the local product chart
of `π` over `U` with fibre `K`: it sends `g` over `U` to `(π g, -s (π g) + g)`, and its inverse
sends `(q, h)` to `s q + h`. -/]
def trivializationOfLocalSection (K : Subgroup G) (hπ : Continuous π)
    (hK : ∀ a b, π a = π b ↔ a⁻¹ * b ∈ K) (U : Set X) (hU : IsOpen U) (s : X → G)
    (hs : ContinuousOn s U) (hsec : ∀ q ∈ U, π (s q) = q) : Bundle.Trivialization K π where
  toFun g := (π g, localSectionFiber hK U s hsec g)
  invFun p := s p.1 * p.2
  source := π ⁻¹' U
  target := U ×ˢ univ
  map_source' _ hg := ⟨hg, mem_univ _⟩
  map_target' p hp := by
    rw [mem_preimage, map_mul_eq_of_localSection hK hsec hp.1]
    exact hp.1
  left_inv' g hg := by
    simp only [coe_localSectionFiber hg, mul_inv_cancel_left]
  right_inv' p hp := by
    have hp' := map_mul_eq_of_localSection hK hsec hp.1 p.2
    refine Prod.ext hp' (Subtype.ext ?_)
    rw [coe_localSectionFiber (hp'.symm ▸ hp.1 : π (s p.1 * p.2) ∈ U), hp', inv_mul_cancel_left]
  open_source := hU.preimage hπ
  open_target := hU.prod isOpen_univ
  continuousOn_toFun := by
    refine hπ.continuousOn.prodMk ?_
    rw [IsInducing.subtypeVal.continuousOn_iff]
    exact ((hs.comp hπ.continuousOn fun _ hg ↦ hg).inv.mul continuousOn_id).congr
      fun g hg ↦ coe_localSectionFiber hg
  continuousOn_invFun :=
    (hs.comp (continuousOn_fst (s := U ×ˢ univ)) fun _ hp ↦ hp.1).mul
      (continuous_subtype_val.comp_continuousOn continuousOn_snd)
  baseSet := U
  open_baseSet := hU
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

variable {hπ : Continuous π} {hK : ∀ a b, π a = π b ↔ a⁻¹ * b ∈ K} {hU : IsOpen U}
  {hs : ContinuousOn s U} {hsec : ∀ q ∈ U, π (s q) = q}

/-- The base of `trivializationOfLocalSection` is the domain of the local section. -/
@[to_additive (attr := simp)]
theorem trivializationOfLocalSection_baseSet :
    (trivializationOfLocalSection K hπ hK U hU s hs hsec).baseSet = U := (rfl)

/-- On the chart source, the fiber coordinate of `trivializationOfLocalSection` is
`s (π g)⁻¹ * g`. -/
@[to_additive (attr := simp) /-- On the chart source, the fiber coordinate of
`trivializationOfLocalSection` is `-s (π g) + g`. -/]
theorem trivializationOfLocalSection_fiberCoordinate {g : G} (hg : π g ∈ U) :
    ((trivializationOfLocalSection K hπ hK U hU s hs hsec g).2 : G) = (s (π g))⁻¹ * g :=
  coe_localSectionFiber (hK := hK) (hsec := hsec) hg

/-- The inverse of `trivializationOfLocalSection` reconstructs a group element by multiplying the
section by the fiber. -/
@[to_additive (attr := simp) /-- The inverse of `trivializationOfLocalSection` reconstructs a
group element by adding the fiber to the section. -/]
theorem trivializationOfLocalSection_symm_apply (p : X × K) :
    (trivializationOfLocalSection K hπ hK U hU s hs hsec).toOpenPartialHomeomorph.symm p =
      s p.1 * p.2 := (rfl)

/-- `trivializationOfLocalSection` intertwines right multiplication by `K` on `G` with right
multiplication on the fibre. -/
@[to_additive /-- `trivializationOfLocalSection` intertwines addition of elements of `K` on `G`
with addition on the fibre. -/]
theorem trivializationOfLocalSection_apply_mul {g : G} (hg : π g ∈ U) (h : K) :
    trivializationOfLocalSection K hπ hK U hU s hs hsec (g * h) =
      ((trivializationOfLocalSection K hπ hK U hU s hs hsec g).1,
        (trivializationOfLocalSection K hπ hK U hU s hs hsec g).2 * h) := by
  have hgh : π (g * h) = π g :=
    ((hK _ _).2 (by rw [inv_mul_cancel_left]; exact h.2)).symm
  refine Prod.ext hgh (Subtype.ext ?_)
  rw [Subgroup.coe_mul, trivializationOfLocalSection_fiberCoordinate (hgh.symm ▸ hg),
    trivializationOfLocalSection_fiberCoordinate hg, hgh, mul_assoc]

end Projection

section LocalSection

variable [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G] (H : Subgroup G)

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
    Bundle.Trivialization H (QuotientGroup.mk : G → G ⧸ H) :=
  H.trivializationOfLocalSection QuotientGroup.continuous_mk (fun _ _ ↦ QuotientGroup.eq) U hU s
    hs hsec

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
  trivializationOfLocalSection_fiberCoordinate hg

/-- The inverse chart reconstructs a group element by multiplying the section by the fiber. -/
@[to_additive (attr := simp)
  /-- The inverse chart reconstructs a group element by adding the fiber to the section. -/]
theorem localSectionTrivialization_symm_apply (p : (G ⧸ H) × H) :
    (localSectionTrivialization H U hU s hs hsec).toOpenPartialHomeomorph.symm p =
      s p.1 * p.2 := (rfl)

end LocalSection

end

end Subgroup
