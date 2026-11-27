/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.DerivedSeries
public import TauCeti.Topology.Algebra.Group.Profinite.Basic

/-!
# Iterated solvable quotients

Write `G^n` for the quotient of a topological group by its `n`-th closed derived subgroup.
Taking the `m`-step solvable quotient of `G^n` recovers `G^m` whenever `m ≤ n`. The isomorphism
`SolvableQuotient.iteratedEquiv` sends the class of an element of `G^n` to its image under
the transition homomorphism `G^n → G^m`.

The image of every closed derived subgroup of `G` in `G^n` is the corresponding closed derived
subgroup of `G^n`. Compactness is unnecessary here. At levels `m ≤ n` the image is the kernel
of the transition to `G^m`, and beyond level `n` the series is trivial. When `G` is profinite,
its solvable quotients carry the usual profinite structure of quotients by closed normal subgroups.
-/

public section

namespace TauCeti

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace SolvableQuotient

/-- The canonical projection from the `n`-step to the `m`-step solvable quotient for `m ≤ n`. -/
def transition {m n : ℕ} (h : m ≤ n) : SolvableQuotient G n →ₜ* SolvableQuotient G m :=
  QuotientGroup.mapOfLEContinuousMonoidHom (closedDerivedSeries_antitone G h)

/-- A transition map preserves representatives in the original group. -/
@[simp]
theorem transition_mk {m n : ℕ} (h : m ≤ n) (x : G) :
    transition G h (x : SolvableQuotient G n) = (x : SolvableQuotient G m) :=
  QuotientGroup.mapOfLEContinuousMonoidHom_mk _ _

/-- The underlying homomorphism of a transition is the quotient map for the inclusion
of the two closed derived subgroups. -/
theorem coe_transition {m n : ℕ} (h : m ≤ n) :
    (transition G h : SolvableQuotient G n →* SolvableQuotient G m) =
      QuotientGroup.mapOfLE (closedDerivedSeries_antitone G h) :=
  QuotientGroup.monoidHom_ext _ <| MonoidHom.ext fun g ↦
    (transition_mk G h g).trans (QuotientGroup.mapOfLE_mk _ g).symm

/-- Transition maps are surjective. -/
theorem transition_surjective {m n : ℕ} (h : m ≤ n) : Function.Surjective (transition G h) := by
  simpa [← coe_transition G h] using
    QuotientGroup.mapOfLE_surjective (closedDerivedSeries_antitone G h)

/-- The transition at a single level is the identity. -/
@[simp]
theorem transition_refl (n : ℕ) :
    transition G (le_refl n) = ContinuousMonoidHom.id (SolvableQuotient G n) :=
  ContinuousMonoidHom.toMonoidHom_injective <|
    (coe_transition G _).trans QuotientGroup.mapOfLE_refl

/-- Projecting through an intermediate solvable quotient gives the same transition map. -/
@[simp]
theorem transition_comp {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) :
    (transition G hkm).comp (transition G hmn) = transition G (hkm.trans hmn) :=
  ContinuousMonoidHom.ext fun x ↦ QuotientGroup.induction_on x fun g ↦ by simp

variable {G} in
/-- The transition to a lower level commutes with the map induced by a continuous homomorphism. -/
@[simp]
theorem transition_map {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {m n : ℕ} (h : m ≤ n) (f : G →* H) (hf : Continuous f) (x : SolvableQuotient G n) :
    transition H h (map f hf n x) = map f hf m (transition G h x) :=
  QuotientGroup.induction_on x fun g ↦ by simp

end SolvableQuotient

/-- Projection to any solvable quotient carries each closed derived subgroup onto the closed
derived subgroup of the same index. -/
@[simp]
theorem map_closedDerivedSeries_solvableQuotient (m n : ℕ) :
    (closedDerivedSeries G m).map (QuotientGroup.mk' (closedDerivedSeries G n)) =
      closedDerivedSeries (SolvableQuotient G n) m := by
  refine le_antisymm ((QuotientGroup.mk' _).map_closedDerivedSeries_le
    QuotientGroup.continuous_mk m) ?_
  rcases le_total m n with h | h
  · -- The projection to level m kills the m-th closed derived subgroup of level n.
    rw [← QuotientGroup.ker_mapOfLE (closedDerivedSeries_antitone G h), ← Subgroup.map_eq_bot_iff]
    apply eq_bot_iff.mpr
    exact ((QuotientGroup.mapOfLE _).map_closedDerivedSeries_le
      (QuotientGroup.continuous_mapOfLE _) m).trans
      (closedDerivedSeries_solvableQuotient_eq_bot G m).le
  · exact (closedDerivedSeries_antitone _ h).trans
      ((closedDerivedSeries_solvableQuotient_eq_bot G n).le.trans bot_le)

namespace SolvableQuotient

/-- The kernel of the transition to level `m` is the `m`-th closed derived subgroup of `G^n`. -/
@[simp]
theorem ker_transition {m n : ℕ} (h : m ≤ n) :
    (transition G h : SolvableQuotient G n →* SolvableQuotient G m).ker =
      closedDerivedSeries (SolvableQuotient G n) m := by
  rw [coe_transition, QuotientGroup.ker_mapOfLE, map_closedDerivedSeries_solvableQuotient]

/-- The canonical topological group isomorphism `(G^n)^m ≃ G^m` for `m ≤ n`. -/
noncomputable def iteratedEquiv {m n : ℕ} (h : m ≤ n) :
    SolvableQuotient (SolvableQuotient G n) m ≃ₜ* SolvableQuotient G m :=
  (Subgroup.quotientContinuousMulEquivOfEq
    (map_closedDerivedSeries_solvableQuotient G m n).symm).trans
    (Subgroup.quotientQuotientContinuousMulEquiv _ _ (closedDerivedSeries_antitone G h))

/-- The isomorphism from the iterated quotient sends the class of `x : G^n` to its projection
in `G^m`. -/
@[simp]
theorem iteratedEquiv_mk {m n : ℕ} (h : m ≤ n) (x : SolvableQuotient G n) :
    iteratedEquiv G h (x : SolvableQuotient (SolvableQuotient G n) m) = transition G h x :=
  QuotientGroup.induction_on x fun g ↦ by simp [iteratedEquiv]

/-- The inverse sends the class of `g` to its class in the iterated quotient. -/
@[simp]
theorem iteratedEquiv_symm_mk {m n : ℕ} (h : m ≤ n) (g : G) :
    (iteratedEquiv G h).symm (g : SolvableQuotient G m) =
      ((g : SolvableQuotient G n) : SolvableQuotient (SolvableQuotient G n) m) :=
  (iteratedEquiv G h).symm_apply_eq.mpr (by simp)

end SolvableQuotient

end TauCeti
