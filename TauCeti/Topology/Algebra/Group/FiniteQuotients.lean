/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Generation

/-!
# Continuous finite quotients of a topological group

A finite group `Q` **occurs as a continuous finite quotient** of a topological group `G`, written
`IsFiniteContinuousQuotient G Q`, when `Q` is finite and some surjective homomorphism `G →* Q` has
open kernel. The predicate is phrased through the kernel and not through a topology on `Q`: when
`G` is a topological group (`IsTopologicalGroup G`), a homomorphism into a finite discrete group is
continuous exactly when its kernel is open (`MonoidHom.continuous_iff_isOpen_ker`), so nothing is
lost, and the predicate is manifestly invariant under isomorphism of `Q`. The continuous finite
quotients of `G` are, up to isomorphism, the quotients `G ⧸ U` by its open normal subgroups of
finite index; when `G` is compact with separately continuous multiplication (in particular a
compact topological group) every open subgroup has finite index, so they are the quotients by all
open normal subgroups.

The finite-quotient determinacy of topologically finitely generated profinite groups, the main
consumer of this predicate, is in `TauCeti.Topology.Algebra.Group.Profinite.FiniteQuotients`.

## Main definitions

* `TauCeti.IsFiniteContinuousQuotient`: `Q` occurs as a continuous finite quotient of `G`.

## Main results

* `TauCeti.isFiniteContinuousQuotient_iff_exists_openNormalSubgroup`: the continuous finite
  quotients of `G` are the quotients by its open normal subgroups of finite index, up to
  isomorphism.
* `TauCeti.isFiniteContinuousQuotient_iff_exists_continuous`: for a finite discrete `Q` and a
  topological group `G`, the predicate is the existence of a continuous surjection `G →* Q`.
* `TauCeti.isFiniteContinuousQuotient_congr_left`,
  `TauCeti.isFiniteContinuousQuotient_congr_right`: the predicate depends only on the topological
  isomorphism class of `G` and on the isomorphism class of `Q`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 3.2.
-/

public section

namespace TauCeti

universe u v

section Defs

variable (G : Type u) [Group G] [TopologicalSpace G] (Q : Type v) [Group Q]

/-- `Q` **occurs as a continuous finite quotient** of the topological group `G`: `Q` is finite and
some surjective homomorphism `G →* Q` has open kernel. The group `Q` carries no topology; when `G`
is a topological group (`IsTopologicalGroup G`) and `Q` carries the discrete topology, an open
kernel is the same as continuity (`isFiniteContinuousQuotient_iff_exists_continuous`). Finiteness
is part of the predicate because an open kernel alone does not force it: a discrete group is a
quotient of itself with open kernel. When `G` is compact with separately continuous multiplication
(in particular a compact topological group) every open subgroup has finite index, so there
finiteness is automatic (`OpenNormalSubgroup.isFiniteContinuousQuotient`). -/
def IsFiniteContinuousQuotient : Prop :=
  Finite Q ∧ ∃ f : G →* Q, Function.Surjective f ∧ IsOpen (f.ker : Set G)

end Defs

section Basic

variable {G : Type u} [Group G] [TopologicalSpace G] {Q : Type v} [Group Q]

/-- A group `Q` is a continuous finite quotient of `G` exactly when it is finite and there is a
surjective homomorphism `G →* Q` with open kernel. -/
theorem isFiniteContinuousQuotient_iff :
    IsFiniteContinuousQuotient G Q ↔
      Finite Q ∧ ∃ f : G →* Q, Function.Surjective f ∧ IsOpen (f.ker : Set G) :=
  -- The definition is not `@[expose]`d, so importing modules cannot unfold it and rewrite with
  -- this lemma instead.
  Iff.rfl

/-- The quotient of `G` by an open normal subgroup of finite index is a continuous finite quotient
of `G`. When `G` is compact with separately continuous multiplication (in particular a compact
topological group) every open subgroup has finite index (`OpenSubgroup.finiteIndex_toSubgroup`),
so the finite-index instance is then found automatically. -/
theorem _root_.OpenNormalSubgroup.isFiniteContinuousQuotient (U : OpenNormalSubgroup G)
    [U.toSubgroup.FiniteIndex] : IsFiniteContinuousQuotient G (G ⧸ U.toSubgroup) :=
  ⟨inferInstance, QuotientGroup.mk' U.toSubgroup, QuotientGroup.mk'_surjective _, by
    rw [QuotientGroup.ker_mk']
    exact U.isOpen⟩

/-- A continuous finite quotient is finite. -/
theorem IsFiniteContinuousQuotient.finite (h : IsFiniteContinuousQuotient G Q) : Finite Q :=
  h.1

/-- For a topological group `G` and a finite group `Q` carrying the discrete topology, occurring as
a continuous finite quotient is the existence of a continuous surjective homomorphism onto `Q`. -/
theorem isFiniteContinuousQuotient_iff_exists_continuous [IsTopologicalGroup G] [Finite Q]
    [TopologicalSpace Q] [DiscreteTopology Q] :
    IsFiniteContinuousQuotient G Q ↔ ∃ f : G →* Q, Function.Surjective f ∧ Continuous f := by
  rw [isFiniteContinuousQuotient_iff, and_iff_right ‹Finite Q›]
  simp only [MonoidHom.continuous_iff_isOpen_ker]

/-- If `G` is a continuous surjective image of `G'`, then every continuous finite quotient of `G`
is also a continuous finite quotient of `G'`. -/
theorem IsFiniteContinuousQuotient.comp {G' : Type*} [Group G'] [TopologicalSpace G']
    (h : IsFiniteContinuousQuotient G Q) {φ : G' →* G} (hφ : Continuous φ)
    (hsurj : Function.Surjective φ) : IsFiniteContinuousQuotient G' Q := by
  obtain ⟨hfin, f, hf, hopen⟩ := h
  refine ⟨hfin, f.comp φ, hf.comp hsurj, ?_⟩
  rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
  exact hopen.preimage hφ

/-- Occurring as a continuous finite quotient is transported along an isomorphism of the
quotient. -/
theorem IsFiniteContinuousQuotient.of_mulEquiv {Q' : Type*} [Group Q']
    (h : IsFiniteContinuousQuotient G Q) (e : Q ≃* Q') : IsFiniteContinuousQuotient G Q' := by
  obtain ⟨_, f, hf, hopen⟩ := h
  exact ⟨Finite.of_equiv Q e, (e : Q →* Q').comp f, e.surjective.comp hf, by
    rwa [MonoidHom.ker_mulEquiv_comp]⟩

/-- Occurring as a continuous finite quotient depends only on the topological isomorphism class
of the group. -/
theorem isFiniteContinuousQuotient_congr_left {G' : Type*} [Group G'] [TopologicalSpace G']
    (e : G ≃ₜ* G') : IsFiniteContinuousQuotient G Q ↔ IsFiniteContinuousQuotient G' Q :=
  ⟨fun h ↦ h.comp (φ := (e.symm : G' →* G)) e.symm.continuous e.symm.surjective,
    fun h ↦ h.comp (φ := (e : G →* G')) e.continuous e.surjective⟩

/-- Occurring as a continuous finite quotient depends only on the isomorphism class of the
quotient. -/
theorem isFiniteContinuousQuotient_congr_right {Q' : Type*} [Group Q'] (e : Q ≃* Q') :
    IsFiniteContinuousQuotient G Q ↔ IsFiniteContinuousQuotient G Q' :=
  ⟨fun h ↦ h.of_mulEquiv e, fun h ↦ h.of_mulEquiv e.symm⟩

/-- The continuous finite quotients of `G` are, up to isomorphism, exactly the quotients of `G` by
its open normal subgroups of finite index. -/
theorem isFiniteContinuousQuotient_iff_exists_openNormalSubgroup :
    IsFiniteContinuousQuotient G Q ↔
      ∃ U : OpenNormalSubgroup G, U.toSubgroup.FiniteIndex ∧ Nonempty (G ⧸ U.toSubgroup ≃* Q) := by
  refine ⟨fun h ↦ ?_, fun ⟨U, hU, ⟨e⟩⟩ ↦ U.isFiniteContinuousQuotient.of_mulEquiv e⟩
  obtain ⟨_, f, hf, hopen⟩ := h
  have e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have : Finite (G ⧸ f.ker) := Finite.of_equiv Q e.symm
  exact ⟨⟨⟨f.ker, hopen⟩, inferInstance⟩, Subgroup.finiteIndex_of_finite_quotient, ⟨e⟩⟩

end Basic

end TauCeti
