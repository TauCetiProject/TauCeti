/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Generating tuples in quotients by open normal subgroups

A tuple in a group generates a quotient when its image generates that quotient. For a group
with separately continuous multiplication, the set of tuples generating the quotient by an
open normal subgroup is closed, and generation descends along quotient maps.

For compact groups these quotients are finite. These facts let compactness produce a tuple
that works in every finite quotient when each quotient has a generating tuple of that length.
In particular, they apply to absolute Galois groups, with tuple length specialized to the
arithmetic bound `[K : ℚ_[p]] + 2` for finite extensions of `ℚ_[p]`.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- Generation by a family modulo a normal subgroup descends to any larger normal subgroup. -/
theorem closure_range_quotient_mk_eq_top_of_le {ι : Type*} {N N' : Subgroup G}
    [N.Normal] [N'.Normal] (h : N' ≤ N) {x : ι → G}
    (hx : Subgroup.closure (Set.range fun i ↦ (QuotientGroup.mk (x i) : G ⧸ N')) = ⊤) :
    Subgroup.closure (Set.range fun i ↦ (QuotientGroup.mk (x i) : G ⧸ N)) = ⊤ := by
  have hN : N' ≤ N.comap (MonoidHom.id G) := h
  let f : G ⧸ N' →* G ⧸ N := QuotientGroup.map N' N (MonoidHom.id G) hN
  have hf : Function.Surjective f :=
    QuotientGroup.map_surjective_of_surjective N' N (MonoidHom.id G)
      QuotientGroup.mk_surjective hN
  have hcomp : (fun i ↦ (QuotientGroup.mk (x i) : G ⧸ N)) =
      f ∘ (fun i ↦ (QuotientGroup.mk (x i) : G ⧸ N')) :=
    funext fun i ↦ (QuotientGroup.map_mk N' N (MonoidHom.id G) hN (x i)).symm
  rw [hcomp, Set.range_comp, ← MonoidHom.map_closure, hx, Subgroup.map_top_of_surjective f hf]

variable [TopologicalSpace G]

/-- The tuples of length `n` whose images generate the quotient by an open normal subgroup.
Repetitions are allowed, so a tuple may have greater length than a minimal generating set. -/
def generatingTuples (n : ℕ) (U : OpenNormalSubgroup G) : Set (Fin n → G) :=
  {x | Subgroup.closure (Set.range fun i ↦ (QuotientGroup.mk (x i) : G ⧸ U.toSubgroup)) = ⊤}

/-- Membership in `generatingTuples` means that the images of the tuple generate the quotient. -/
@[simp]
theorem mem_generatingTuples (n : ℕ) (U : OpenNormalSubgroup G) (x : Fin n → G) :
    x ∈ generatingTuples n U ↔
      Subgroup.closure (Set.range fun i ↦ (QuotientGroup.mk (x i) : G ⧸ U.toSubgroup)) = ⊤ :=
  Iff.rfl

/-- The tuples generating a quotient by an open normal subgroup form a closed set: the
condition depends only on their image in a discrete quotient. -/
theorem isClosed_generatingTuples [SeparatelyContinuousMul G] (n : ℕ)
    (U : OpenNormalSubgroup G) : IsClosed (generatingTuples n U) := by
  let q : (Fin n → G) → (Fin n → G ⧸ U.toSubgroup) := fun x i ↦ QuotientGroup.mk (x i)
  have hq : Continuous q := by
    apply continuous_pi
    intro i
    exact continuous_quotient_mk'.comp (continuous_apply i)
  let S : Set (Fin n → G ⧸ U.toSubgroup) := {y | Subgroup.closure (Set.range y) = ⊤}
  have : DiscreteTopology (G ⧸ U.toSubgroup) := QuotientGroup.discreteTopology U.isOpen
  have hS : IsClosed S := isClosed_discrete S
  have hEq : generatingTuples n U = q ⁻¹' S := by
    ext x
    rfl
  rw [hEq]
  exact hS.preimage hq

/-- If `U' ≤ U`, every tuple generating the finer quotient by `U'` also generates the quotient
by `U`. -/
theorem generatingTuples_mono (n : ℕ) {U U' : OpenNormalSubgroup G}
    (h : U' ≤ U) : generatingTuples n U' ⊆ generatingTuples n U :=
  fun _ hx ↦ (mem_generatingTuples n U _).mpr
    (closure_range_quotient_mk_eq_top_of_le h ((mem_generatingTuples n U' _).mp hx))

end TauCeti
