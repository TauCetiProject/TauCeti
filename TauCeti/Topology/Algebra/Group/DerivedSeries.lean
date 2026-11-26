/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
public import TauCeti.Topology.Algebra.Group.ClosedSubgroup
public import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# The closed derived series and the solvable quotients of a topological group

The **closed derived series** of a topological group `G` is the sequence of closed normal
subgroups `G^[n]`, the topological closures of the terms of the derived series
`Subgroup.derivedSeries G n` of the underlying group. It satisfies the recursion

```text
G^[0] = G,   G^[n+1] = closure ⁅G^[n], G^[n]⁆,
```

because closing up the factors of a commutator does not change its closure
(`Subgroup.topologicalClosure_commutator_topologicalClosure`). The quotient `G^n = G ⧸ G^[n]` is
the **maximal `n`-step solvable quotient** of `G`: it is a Hausdorff topological group whose
derived series vanishes at step `n`, and a closed normal subgroup `N` contains `G^[n]` exactly when
the derived series of `G ⧸ N` vanishes at step `n`. For `n = 1`, `G^1` is Mathlib's topological
abelianization `TopologicalAbelianization G` by definition.

For anabelian geometry of local fields, the groups `G^n` for `G` an absolute Galois group are the
objects of the `m`-step solvable Grothendieck conjecture [Hyeon 2025, §2]. The series is defined as
a closure, not by iterating closed commutators, so that it is visibly functorial: a continuous
homomorphism carries `G^[n]` into `H^[n]`, a continuous closed surjection (for instance a continuous
surjection from a compact group onto a Hausdorff group) carries it onto `H^[n]`, and so the
solvable quotients are functorial and an isomorphism of topological groups induces isomorphisms of
all of them.

Without a separation axiom the closed and abstract derived series differ even for commutative
groups: an indiscrete group has `G^[n] = G` for every `n`
(`TauCeti.closedDerivedSeries_eq_top_of_indiscreteTopology`), whereas a discrete group has
`G^[n] = Subgroup.derivedSeries G n`. For `G` a `T1` group, `G` is commutative exactly when
`G^[1]` is trivial.

## Main definitions

* `TauCeti.closedDerivedSeries`: the closed derived series `G^[n]`.
* `TauCeti.SolvableQuotient`: the maximal `n`-step solvable quotient `G^n = G ⧸ G^[n]`.
* `TauCeti.SolvableQuotient.map`: the homomorphism `G^n →* H^n` induced by a continuous
  homomorphism `G →* H`.
* `ContinuousMulEquiv.solvableQuotientCongr`: the isomorphism `G^n ≃ₜ* H^n` induced by an
  isomorphism of topological groups `G ≃ₜ* H`.

## Main results

* `TauCeti.closedDerivedSeries_succ`: the recursion `G^[n+1] = closure ⁅G^[n], G^[n]⁆`.
* `TauCeti.closedDerivedSeries_antitone`: the series is decreasing.
* `TauCeti.closedDerivedSeries_one`, `TauCeti.solvableQuotient_one`: `G^[1]` is the closed
  commutator subgroup, and `G^1` is `TopologicalAbelianization G`.
* `TauCeti.closedDerivedSeries_one_eq_bot_iff`: a `T1` group is commutative exactly when `G^[1]`
  is trivial.
* `TauCeti.closedDerivedSeries_le_iff_derivedSeries_quotient_eq_bot`: `G^n` is the maximal
  `n`-step solvable quotient by a closed normal subgroup.
* `MonoidHom.map_closedDerivedSeries_le`, `MonoidHom.map_closedDerivedSeries_eq_of_surjective`,
  `ContinuousMulEquiv.map_closedDerivedSeries_eq`: functoriality of the closed derived series.

## References

* S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local fields*,
  J. London Math. Soc. (2) **112** (2025), e70402, §2.
-/

public section

namespace TauCeti

open Subgroup

section Basic

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The **closed derived series** `G^[n]` of a topological group: the topological closure of the
`n`-th term of the derived series of the underlying group. The recursion through closed
commutators is `TauCeti.closedDerivedSeries_succ`.

The body is exposed so that `SolvableQuotient G 1` is `TopologicalAbelianization G` by definition
(`TauCeti.solvableQuotient_one`), and not merely up to isomorphism. -/
@[expose] def closedDerivedSeries (n : ℕ) : Subgroup G :=
  (Subgroup.derivedSeries G n).topologicalClosure

/-- `G^[n]` is the topological closure of `Subgroup.derivedSeries G n`. -/
theorem closedDerivedSeries_def (n : ℕ) :
    closedDerivedSeries G n = (Subgroup.derivedSeries G n).topologicalClosure :=
  (rfl)

/-- The carrier of `G^[n]` is the closure of the carrier of `Subgroup.derivedSeries G n`. -/
theorem coe_closedDerivedSeries (n : ℕ) :
    (closedDerivedSeries G n : Set G) = _root_.closure (Subgroup.derivedSeries G n : Set G) :=
  (rfl)

/-- Every term of the closed derived series is a normal subgroup. -/
instance closedDerivedSeries_normal (n : ℕ) : (closedDerivedSeries G n).Normal :=
  Subgroup.is_normal_topologicalClosure _

/-- Every term of the closed derived series is closed. This is an instance, so that instance search
finds the solvable quotients `G ⧸ closedDerivedSeries G n` to be Hausdorff. -/
instance isClosed_closedDerivedSeries (n : ℕ) : IsClosed (closedDerivedSeries G n : Set G) :=
  isClosed_topologicalClosure _

/-- The derived series of the underlying group lies in the closed derived series. -/
theorem derivedSeries_le_closedDerivedSeries (n : ℕ) :
    Subgroup.derivedSeries G n ≤ closedDerivedSeries G n :=
  le_topologicalClosure _

variable {G} in
/-- A closed subgroup contains `G^[n]` exactly when it contains the `n`-th term of the derived
series of the underlying group. -/
theorem closedDerivedSeries_le_iff {n : ℕ} {H : Subgroup G} (hH : IsClosed (H : Set G)) :
    closedDerivedSeries G n ≤ H ↔ Subgroup.derivedSeries G n ≤ H :=
  ⟨(derivedSeries_le_closedDerivedSeries G n).trans, fun h ↦ topologicalClosure_minimal _ h hH⟩

/-- The zeroth term of the closed derived series is the whole group. -/
@[simp]
theorem closedDerivedSeries_zero : closedDerivedSeries G 0 = ⊤ := by
  simpa using derivedSeries_le_closedDerivedSeries G 0

/-- `G^[1]` is the closure of the commutator subgroup, the subgroup by which Mathlib's
`TopologicalAbelianization` is the quotient. -/
theorem closedDerivedSeries_one :
    closedDerivedSeries G 1 = (commutator G).topologicalClosure := by
  rw [closedDerivedSeries_def, Subgroup.derivedSeries_one]

/-- **The recursion of the closed derived series**: `G^[n+1] = closure ⁅G^[n], G^[n]⁆`. -/
theorem closedDerivedSeries_succ (n : ℕ) :
    closedDerivedSeries G (n + 1) =
      ⁅closedDerivedSeries G n, closedDerivedSeries G n⁆.topologicalClosure := by
  rw [closedDerivedSeries_def, closedDerivedSeries_def, Subgroup.derivedSeries_succ,
    topologicalClosure_commutator_topologicalClosure]

/-- The commutator subgroup of `G^[n]` lies in `G^[n+1]`. -/
theorem commutator_closedDerivedSeries_le (n : ℕ) :
    ⁅closedDerivedSeries G n, closedDerivedSeries G n⁆ ≤ closedDerivedSeries G (n + 1) := by
  rw [closedDerivedSeries_succ]
  exact le_topologicalClosure _

/-- The closed derived series is decreasing. -/
theorem closedDerivedSeries_antitone : Antitone (closedDerivedSeries G) :=
  fun _ _ h ↦ topologicalClosure_mono (Subgroup.derivedSeries_antitone G h)

/-- On a discrete group the closed derived series is the derived series. -/
theorem closedDerivedSeries_eq_derivedSeries [DiscreteTopology G] (n : ℕ) :
    closedDerivedSeries G n = Subgroup.derivedSeries G n :=
  (isClosed_discrete _).subgroup_topologicalClosure_eq

/-- On an indiscrete group every term of the closed derived series is the whole group, whatever
the derived series of the underlying group is. -/
theorem closedDerivedSeries_eq_top_of_indiscreteTopology [IndiscreteTopology G] (n : ℕ) :
    closedDerivedSeries G n = ⊤ := by
  rw [← SetLike.coe_set_eq, coe_closedDerivedSeries, coe_top]
  exact closure_indiscrete ⟨1, one_mem _⟩

/-- For a commutative group, `G^[1]` is the closure of the trivial subgroup. Without a separation
axiom this need not be trivial. -/
theorem closedDerivedSeries_one_eq_topologicalClosure_bot [IsMulCommutative G] :
    closedDerivedSeries G 1 = (⊥ : Subgroup G).topologicalClosure := by
  rw [closedDerivedSeries_one, (commutator_eq_bot_iff G).mpr ‹_›]

/-- A `T1` topological group is commutative exactly when `G^[1]` is trivial. -/
theorem closedDerivedSeries_one_eq_bot_iff [T1Space G] :
    closedDerivedSeries G 1 = ⊥ ↔ IsMulCommutative G := by
  rw [closedDerivedSeries_one, ← commutator_eq_bot_iff]
  refine ⟨fun h ↦ eq_bot_iff.mpr (h ▸ le_topologicalClosure _), fun h ↦ ?_⟩
  rw [h]
  exact IsClosed.subgroup_topologicalClosure_eq (by simp)

/-- The **maximal `n`-step solvable quotient** `G^n = G ⧸ G^[n]` of a topological group. For
`n = 1` it is `TopologicalAbelianization G` (`TauCeti.solvableQuotient_one`). -/
abbrev SolvableQuotient (n : ℕ) : Type _ :=
  G ⧸ closedDerivedSeries G n

/-- The first solvable quotient is Mathlib's topological abelianization, by definition. -/
theorem solvableQuotient_one : SolvableQuotient G 1 = TopologicalAbelianization G :=
  rfl

variable {G} in
/-- **The universal property of the solvable quotient.** A closed normal subgroup `N` contains
`G^[n]` exactly when the derived series of `G ⧸ N` vanishes at step `n`, so `G^n` is the maximal
`n`-step solvable quotient of `G` by a closed normal subgroup. -/
theorem closedDerivedSeries_le_iff_derivedSeries_quotient_eq_bot {N : Subgroup G} [N.Normal]
    (hN : IsClosed (N : Set G)) (n : ℕ) :
    closedDerivedSeries G n ≤ N ↔ Subgroup.derivedSeries (G ⧸ N) n = ⊥ := by
  rw [closedDerivedSeries_le_iff hN,
    ← Subgroup.map_derivedSeries_eq (QuotientGroup.mk'_surjective N), Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk']

/-- The derived series of `G^n` vanishes at step `n`. -/
@[simp]
theorem derivedSeries_solvableQuotient_eq_bot (n : ℕ) :
    Subgroup.derivedSeries (SolvableQuotient G n) n = ⊥ :=
  (closedDerivedSeries_le_iff_derivedSeries_quotient_eq_bot
    (isClosed_closedDerivedSeries G n) n).mp le_rfl

/-- The solvable quotients are solvable. -/
instance isSolvable_solvableQuotient (n : ℕ) : Group.IsSolvable (SolvableQuotient G n) :=
  ⟨⟨n, derivedSeries_solvableQuotient_eq_bot G n⟩⟩

/-- The closed derived series of `G^n` vanishes at step `n`. -/
@[simp]
theorem closedDerivedSeries_solvableQuotient_eq_bot (n : ℕ) :
    closedDerivedSeries (SolvableQuotient G n) n = ⊥ := by
  rw [closedDerivedSeries_def (SolvableQuotient G n), derivedSeries_solvableQuotient_eq_bot]
  exact IsClosed.subgroup_topologicalClosure_eq (by simp)

end Basic

/-! ### Functoriality -/

section Map

variable {G H K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- A continuous homomorphism carries `G^[n]` into `H^[n]`. -/
theorem _root_.MonoidHom.map_closedDerivedSeries_le (f : G →* H) (hf : Continuous f) (n : ℕ) :
    (closedDerivedSeries G n).map f ≤ closedDerivedSeries H n :=
  (f.map_topologicalClosure_le hf _).trans
    (topologicalClosure_mono (Subgroup.map_derivedSeries_le_derivedSeries f n))

/-- A continuous closed surjection carries `G^[n]` onto `H^[n]`. This applies to a continuous
surjection from a compact group onto a Hausdorff group, by `Continuous.isClosedMap`. -/
theorem _root_.MonoidHom.map_closedDerivedSeries_eq_of_surjective (f : G →* H)
    (hf : Continuous f) (hfc : IsClosedMap f) (hsurj : Function.Surjective f) (n : ℕ) :
    (closedDerivedSeries G n).map f = closedDerivedSeries H n := by
  refine le_antisymm (f.map_closedDerivedSeries_le hf n) ?_
  have hclosed : IsClosed ((closedDerivedSeries G n).map f : Set H) := by
    rw [coe_map]
    exact hfc _ (isClosed_closedDerivedSeries G n)
  rw [closedDerivedSeries_le_iff hclosed, ← Subgroup.map_derivedSeries_eq hsurj n]
  exact map_mono (derivedSeries_le_closedDerivedSeries G n)

/-- An isomorphism of topological groups carries `G^[n]` onto `H^[n]`. -/
theorem _root_.ContinuousMulEquiv.map_closedDerivedSeries_eq (e : G ≃ₜ* H) (n : ℕ) :
    (closedDerivedSeries G n).map e.toMulEquiv.toMonoidHom = closedDerivedSeries H n :=
  e.toMulEquiv.toMonoidHom.map_closedDerivedSeries_eq_of_surjective e.continuous
    e.toHomeomorph.isClosedMap e.surjective n

namespace SolvableQuotient

/-- The homomorphism `G^n →* H^n` of solvable quotients induced by a continuous homomorphism
`f : G →* H`. -/
def map (f : G →* H) (hf : Continuous f) (n : ℕ) : SolvableQuotient G n →* SolvableQuotient H n :=
  QuotientGroup.map _ _ f (map_le_iff_le_comap.mp (f.map_closedDerivedSeries_le hf n))

/-- `map f hf n` sends the class of `x : G` to the class of `f x`. -/
@[simp]
theorem map_mk (f : G →* H) (hf : Continuous f) (n : ℕ) (x : G) :
    map f hf n (x : SolvableQuotient G n) = (f x : SolvableQuotient H n) :=
  QuotientGroup.map_mk _ _ _ _ x

/-- The homomorphism of solvable quotients induced by a continuous homomorphism is continuous. -/
theorem continuous_map (f : G →* H) (hf : Continuous f) (n : ℕ) : Continuous (map f hf n) := by
  refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr ?_
  have h : map f hf n ∘ (QuotientGroup.mk : G → SolvableQuotient G n) =
      QuotientGroup.mk ∘ f := funext (map_mk f hf n)
  rw [h]
  exact QuotientGroup.continuous_mk.comp hf

/-- The identity of `G` induces the identity of `G^n`. -/
@[simp]
theorem map_id (n : ℕ) :
    map (MonoidHom.id G) continuous_id n = MonoidHom.id (SolvableQuotient G n) :=
  QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun x ↦ map_mk (MonoidHom.id G) continuous_id n x)

/-- The solvable quotients are functorial: the map induced by a composite is the composite of the
induced maps. -/
theorem map_comp (g : H →* K) (hg : Continuous g) (f : G →* H) (hf : Continuous f) (n : ℕ) :
    (map g hg n).comp (map f hf n) = map (g.comp f) (hg.comp hf) n :=
  QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun x ↦ by simp)

/-- The homomorphism of solvable quotients induced by a continuous surjection is surjective. -/
theorem map_surjective (f : G →* H) (hf : Continuous f) (hsurj : Function.Surjective f) (n : ℕ) :
    Function.Surjective (map f hf n) :=
  QuotientGroup.map_surjective_of_surjective _ _ f
    ((QuotientGroup.mk'_surjective (closedDerivedSeries H n)).comp hsurj) _

end SolvableQuotient

/-- An isomorphism of topological groups `G ≃ₜ* H` induces an isomorphism `G^n ≃ₜ* H^n` of the
solvable quotients. For `n = 1` this is `ContinuousMulEquiv.topologicalAbelianizationCongr`. -/
def _root_.ContinuousMulEquiv.solvableQuotientCongr (e : G ≃ₜ* H) (n : ℕ) :
    SolvableQuotient G n ≃ₜ* SolvableQuotient H n :=
  e.quotientCongr _ _ (e.map_closedDerivedSeries_eq n)

/-- `e.solvableQuotientCongr n` sends the class of `x : G` to the class of `e x`. -/
@[simp]
theorem _root_.ContinuousMulEquiv.solvableQuotientCongr_mk (e : G ≃ₜ* H) (n : ℕ) (x : G) :
    e.solvableQuotientCongr n (x : SolvableQuotient G n) = (e x : SolvableQuotient H n) :=
  e.quotientCongr_mk _ _ _ x

/-- The inverse of `e.solvableQuotientCongr n` is `e.symm.solvableQuotientCongr n`. -/
@[simp]
theorem _root_.ContinuousMulEquiv.solvableQuotientCongr_symm (e : G ≃ₜ* H) (n : ℕ) :
    (e.solvableQuotientCongr n).symm = e.symm.solvableQuotientCongr n :=
  ContinuousMulEquiv.ext fun x ↦ QuotientGroup.induction_on x fun h ↦
    (e.solvableQuotientCongr n).symm_apply_eq.mpr (by simp)

/-- The isomorphism of solvable quotients induced by `e` is the homomorphism induced by `e`. -/
theorem _root_.ContinuousMulEquiv.coe_solvableQuotientCongr (e : G ≃ₜ* H) (n : ℕ) :
    ((e.solvableQuotientCongr n : SolvableQuotient G n ≃* SolvableQuotient H n) :
        SolvableQuotient G n →* SolvableQuotient H n) =
      SolvableQuotient.map e.toMulEquiv.toMonoidHom e.continuous n :=
  QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun x ↦ by simp)

end Map

end TauCeti
