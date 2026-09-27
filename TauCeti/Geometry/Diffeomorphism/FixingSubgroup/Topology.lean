/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.FixingSubgroup.Basic
public import TauCeti.Geometry.Diffeomorphism.Topology
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# Closed pointwise fixing subgroups of diffeomorphisms

For a compact source manifold, the weak Whitney topology makes evaluation at each point
continuous. Consequently, the diffeomorphisms fixing any subset pointwise form a closed
subgroup: its carrier is the intersection of the equalizer sets `f x = x`. Taking the subset
to be the boundary gives the relative diffeomorphism group used in homotopy questions about
manifolds with boundary.

The topology here is the weak Whitney topology on `C^n` diffeomorphisms. It is available for
any smoothness exponent `n`, including `∞`, and for manifolds with boundary. Only Hausdorffness
of the target is needed for each equalizer to be closed.
-/

public section

open scoped Manifold ContDiff TauCeti.DiffeomorphWeakWhitney

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [CompactSpace M] [T2Space M] {n : ℕ∞ω} [IsManifold I n M]

/-- The pointwise fixing subgroup of any subset is closed in the weak Whitney topology.
In particular, this applies to the boundary set of a compact manifold with boundary. -/
theorem isClosed_fixingSubgroup (s : Set M) :
    IsClosed ((fixingSubgroup (I := I) (n := n) s : Subgroup (M ≃ₘ^n⟮I, I⟯ M)) :
      Set (M ≃ₘ^n⟮I, I⟯ M)) := by
  have hset : ((fixingSubgroup (I := I) (n := n) s : Subgroup (M ≃ₘ^n⟮I, I⟯ M)) :
      Set (M ≃ₘ^n⟮I, I⟯ M)) = ⋂ x ∈ s, {f | f x = x} := by
    ext f
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe, mem_fixingSubgroup_iff]
  rw [hset]
  exact isClosed_biInter fun x _ => isClosed_eq (continuous_eval_const x) continuous_const

/-- The diffeomorphisms fixing `s` pointwise, as a closed subgroup of the weak Whitney
space of diffeomorphisms. For `s = I.boundary M` this is `Diff(M, ∂M)`. -/
def closedFixingSubgroup (s : Set M) : ClosedSubgroup (M ≃ₘ^n⟮I, I⟯ M) :=
  ⟨fixingSubgroup (I := I) (n := n) s, isClosed_fixingSubgroup (I := I) (n := n) s⟩

/-- The carrier of the closed fixing subgroup is the existing pointwise fixing subgroup. -/
@[simp]
theorem coe_closedFixingSubgroup (s : Set M) :
    (closedFixingSubgroup (I := I) (n := n) s : Subgroup (M ≃ₘ^n⟮I, I⟯ M)) =
      fixingSubgroup (I := I) (n := n) s := (rfl)

/-- Membership in the closed fixing subgroup is pointwise fixedness on `s`. -/
@[simp]
theorem mem_closedFixingSubgroup_iff {s : Set M} {f : M ≃ₘ^n⟮I, I⟯ M} :
    f ∈ closedFixingSubgroup (I := I) (n := n) s ↔ ∀ x ∈ s, f x = x := by
  calc
    -- A closed subgroup's `SetLike` carrier is its underlying subgroup's carrier.
    f ∈ closedFixingSubgroup (I := I) (n := n) s ↔
        f ∈ (closedFixingSubgroup (I := I) (n := n) s : Subgroup _) := Iff.rfl
    _ ↔ f ∈ fixingSubgroup (I := I) (n := n) s := by rw [coe_closedFixingSubgroup]
    _ ↔ ∀ x ∈ s, f x = x := mem_fixingSubgroup_iff

end Diffeomorph
