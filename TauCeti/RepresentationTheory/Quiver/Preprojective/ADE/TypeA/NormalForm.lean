/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.Basic
public import TauCeti.RingTheory.Idempotents.Corner

/-!
# Corner normal forms for the type-`A` preprojective algebra

In the signless preprojective algebra of the path `0 — ⋯ — (n - 1)`, every path from `a` to
`b` reduces to a valley word: descend to `m`, then climb to `b`. Reading heights from both
ends shows that only

```
max 0 (a + b + 1 - n) ≤ m ≤ min a b
```

can survive. The corresponding valley classes span the corner `e_b Π e_a`, over every
commutative ring, with no division and no restriction on characteristic. The reduction preserves
path length. These finite corner spanning families are the spanning half of the normal-form
basis needed to compute the socles of type-`A` projectives and a Frobenius functional.
Linear independence and nonvanishing of the listed words are not asserted here.

Products use later-factor-first order: the rightmost arrow is traversed first. The signless
presentation is isomorphic to the additive preprojective presentation for every orientation
of this bipartite graph, by the existing sign-rescaling comparison.

## References

* W. Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson
  problem*, Section 1, for the preprojective relations.
* C. M. Ringel, *The preprojective algebra of a quiver*, for the finite-Dynkin Frobenius property.

The reduction uses `TauCeti.ladderValley` and the endpoint-height bounds of
`TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.Basic`.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

variable (k : Type*) [CommRing k] {n : ℕ}

attribute [local instance] finiteNeighborSetFintype

local notation "AG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.A n))
local notation "Π" => signlessPreprojectiveAlgebra k (DoubledQuiver AG)
local notation "π" => signlessPreprojectiveMk k (DoubledQuiver AG)
local notation "e" => fun a : Fin (DynkinType.A n).rank => π (vertexIdempotent k (vertex AG a))

/-- The valley class from `a` to `b` with bottom `m`, projected to the corner `e_b Π e_a`.
For `m ≤ min a b`, its word descends `a - m` steps and climbs `b - m` steps. -/
noncomputable def signlessPreprojectiveAValley (a b : Fin (DynkinType.A n).rank) (m : ℕ) : Π :=
  e b * ladderValley (fun w => signlessArrow k AG w (w + 1))
    (fun w => signlessArrow k AG (w + 1) w) m (a.val - m) (b.val - m) * e a

/-- The valley class, written as its projected ladder word. -/
theorem signlessPreprojectiveAValley_def (a b : Fin (DynkinType.A n).rank) (m : ℕ) :
    signlessPreprojectiveAValley k a b m =
      e b * ladderValley (fun w => signlessArrow k AG w (w + 1))
        (fun w => signlessArrow k AG (w + 1) w) m (a.val - m) (b.val - m) * e a := by
  rw [signlessPreprojectiveAValley]

/-- Each valley class lies in the indicated source/target corner. -/
@[simp]
theorem signlessPreprojectiveAValley_mem_cornerSubmodule
    (a b : Fin (DynkinType.A n).rank) (m : ℕ) :
    signlessPreprojectiveAValley k a b m ∈ cornerSubmodule k (e b) (e a) := by
  have hid (i : Fin (DynkinType.A n).rank) : IsIdempotentElem (e i) :=
    IsIdempotentElem.map (vertexIdempotent_mul_self (k := k) (vertex AG i)) π
  rw [mem_cornerSubmodule_iff k (hid b) (hid a), signlessPreprojectiveAValley_def]
  simp only [← mul_assoc, (hid b).eq]
  simp only [mul_assoc, (hid a).eq]

/-- The valley of length zero at `a` is its vertex idempotent. -/
@[simp]
theorem signlessPreprojectiveAValley_self (a : Fin (DynkinType.A n).rank) :
    signlessPreprojectiveAValley k a a a.val = e a := by
  rw [signlessPreprojectiveAValley_def]
  simp only [Nat.sub_self, ladderValley_zero_zero, mul_one, ← map_mul,
    vertexIdempotent_mul_self]

/-- Every path reduces to zero or to an integer multiple of a bounded valley class.
The number of descents plus climbs equals the original path length. -/
theorem signlessPreprojectiveMk_A_ofPath_eq_zero_or_valley {a b : Fin (DynkinType.A n).rank}
    (p : Path (vertex AG a) (vertex AG b)) :
    π (ofPath ⟨_, _, p⟩) = 0 ∨
      ∃ m ∈ Finset.Icc (a.val + b.val + 1 - n) (min a.val b.val), ∃ ε : ℤ,
        (a.val - m) + (b.val - m) = p.length ∧
          π (ofPath ⟨_, _, p⟩) = ε • signlessPreprojectiveAValley k a b m := by
  by_cases hp : min (a.val + b.val)
      (2 * ((DynkinType.A n).rank - 1) - a.val - b.val) < p.length
  · exact .inl (signlessPreprojectiveMk_A_ofPath_eq_zero_of_endpoint_bound k p hp)
  rcases signlessPreprojectiveMk_A_ofPath_eq_zero_or_ladderValley k p with
    h | ⟨m, s, r, ε, hlen, hs, hr, h⟩
  · exact .inl h
  have ha := a.isLt
  have hb := b.isLt
  have hn := DynkinType.rank_A n
  have hs' : a.val - m = s := by omega
  have hr' : b.val - m = r := by omega
  refine .inr ⟨m, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ε, by omega, ?_⟩
  have hcorner : e b * π (ofPath ⟨_, _, p⟩) = π (ofPath ⟨_, _, p⟩) := by
    rw [← map_mul, vertexIdempotent_mul_ofPath]
  rw [← hcorner, h, mul_smul_comm, signlessPreprojectiveAValley_def, hs', hr', mul_assoc]

/-- Cutting a path class to `e_b Π e_a` gives a linear combination of the bounded valleys. -/
private theorem corner_ofPath_mem_span (a b : Fin (DynkinType.A n).rank)
    (x : Quiver.TotalPath (DoubledQuiver AG)) :
    e b * π (ofPath x) * e a ∈ Submodule.span k
      (signlessPreprojectiveAValley k a b ''
        (Finset.Icc (a.val + b.val + 1 - n) (min a.val b.val) : Set ℕ)) := by
  obtain ⟨c, d, p⟩ := x
  obtain ⟨c, rfl⟩ := exists_eq_vertex AG c
  obtain ⟨d, rfl⟩ := exists_eq_vertex AG d
  by_cases hc : c = a
  swap
  · rw [mul_assoc, ← map_mul, ofPath_mul_vertexIdempotent_of_ne _
      (fun h => hc (vertex_injective AG h.symm)), map_zero, mul_zero]
    exact Submodule.zero_mem _
  subst c
  by_cases hd : d = b
  swap
  · rw [← map_mul, vertexIdempotent_mul_ofPath_of_ne _
      (fun h => hd (vertex_injective AG h.symm)), map_zero, zero_mul]
    exact Submodule.zero_mem _
  subst d
  rw [← map_mul, vertexIdempotent_mul_ofPath, ← map_mul, ofPath_mul_vertexIdempotent]
  rcases signlessPreprojectiveMk_A_ofPath_eq_zero_or_valley k p with h | ⟨m, hm, ε, -, h⟩
  · rw [h]
    exact Submodule.zero_mem _
  · rw [h]
    rw [← Int.cast_smul_eq_zsmul k]
    exact Submodule.smul_mem _ (ε : k) (Submodule.subset_span ⟨m, hm, rfl⟩)

/-- The bounded valley classes span the entire corner `e_b Π e_a` of the signless type-`A`
preprojective algebra. This is a spanning statement, not a claim of linear independence. -/
theorem cornerSubmodule_signlessPreprojective_A_eq_span_valley
    (a b : Fin (DynkinType.A n).rank) :
    cornerSubmodule k (e b) (e a) = Submodule.span k
      (signlessPreprojectiveAValley k a b ''
        (Finset.Icc (a.val + b.val + 1 - n) (min a.val b.val) : Set ℕ)) := by
  apply le_antisymm
  · intro x hx
    have hid (i : Fin (DynkinType.A n).rank) : IsIdempotentElem (e i) :=
      IsIdempotentElem.map (vertexIdempotent_mul_self (k := k) (vertex AG i)) π
    rw [mem_cornerSubmodule_iff k (hid b) (hid a)] at hx
    rw [← hx]
    obtain ⟨f, rfl⟩ := signlessPreprojectiveMk_surjective k (DoubledQuiver AG) x
    clear hx
    induction f using PathAlgebra.induction_linear with
    | zero =>
      simp only [map_zero, mul_zero, zero_mul]
      exact Submodule.zero_mem _
    | add f g hf hg =>
      simpa only [map_add, mul_add, add_mul] using Submodule.add_mem _ hf hg
    | single x c =>
      simpa only [single_eq_smul_ofPath, map_smul, mul_smul_comm, smul_mul_assoc] using
        Submodule.smul_mem _ c (corner_ofPath_mem_span k a b x)
  · apply Submodule.span_le.mpr
    rintro _ ⟨m, -, rfl⟩
    exact signlessPreprojectiveAValley_mem_cornerSubmodule k a b m

end TauCeti
