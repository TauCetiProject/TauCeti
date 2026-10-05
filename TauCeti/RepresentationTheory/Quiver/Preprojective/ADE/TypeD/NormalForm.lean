/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.Basic

/-!
# Finite corner spanning families for type-`D` preprojective algebras

The explicit arm and fork words of `TauCeti.signlessPreprojectiveDNormalForms` span every
source/target corner of the signless preprojective algebra of `Dₙ`, for `n ≥ 3`, over any
commutative ring. The fork words alternate between the two leaf backtracks; no choice of
arbitrary paths remains in the spanning families. These words provide the finite families
needed for the projective-socle and Frobenius-pairing calculations. Linear independence,
nonvanishing, and a dimension formula are not claimed.

The path reduction is `TauCeti.signlessPreprojectiveMk_D_ofPath_mem_span_normalForms`.
The passage from path classes to corners follows the corresponding type-`A` construction in
`TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.NormalForm`.

## References

* W. Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson
  problem*, Section 1, for the local relations.
* C. M. Ringel, *The preprojective algebra of a quiver*, for the finite-Dynkin Frobenius property.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

variable (k : Type*) [CommRing k] {n : ℕ}

attribute [local instance] forkNeighborSetFintype

local notation "DG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.D n))
local notation "π" => signlessPreprojectiveMk k (DoubledQuiver DG)
local notation "e" => fun a : Fin (DynkinType.D n).rank => π (vertexIdempotent k (vertex DG a))

/-- Cutting a path class to a fixed corner gives a linear combination of its normal words. -/
private theorem corner_ofPath_mem_span (hn : 3 ≤ n) (a b : Fin (DynkinType.D n).rank)
    (x : Quiver.TotalPath (DoubledQuiver DG)) :
    e b * π (ofPath x) * e a ∈ Submodule.span k (signlessPreprojectiveDNormalForms k a b) := by
  obtain ⟨u, v, p⟩ := x
  obtain ⟨u, rfl⟩ := exists_eq_vertex DG u
  obtain ⟨v, rfl⟩ := exists_eq_vertex DG v
  by_cases hu : u = a
  swap
  · rw [mul_assoc, ← map_mul, ofPath_mul_vertexIdempotent_of_ne _
      (fun h => hu (vertex_injective DG h.symm)), map_zero, mul_zero]
    exact Submodule.zero_mem _
  subst u
  by_cases hv : v = b
  swap
  · rw [← map_mul, vertexIdempotent_mul_ofPath_of_ne _
      (fun h => hv (vertex_injective DG h.symm)), map_zero, zero_mul]
    exact Submodule.zero_mem _
  subst v
  rw [← map_mul, vertexIdempotent_mul_ofPath, ← map_mul, ofPath_mul_vertexIdempotent]
  exact signlessPreprojectiveMk_D_ofPath_mem_span_normalForms k hn p

/-- The finite family of arm valleys, alternating fork words, and leaf idempotents spans the
entire corner `e_b Π e_a` of the type-`D` signless preprojective algebra. -/
theorem cornerSubmodule_signlessPreprojective_D_eq_span_normalForms (hn : 3 ≤ n)
    (a b : Fin (DynkinType.D n).rank) :
    cornerSubmodule k (e b) (e a) = Submodule.span k (signlessPreprojectiveDNormalForms k a b) := by
  apply le_antisymm
  · intro z hz
    have hid (i : Fin (DynkinType.D n).rank) : IsIdempotentElem (e i) :=
      IsIdempotentElem.map (vertexIdempotent_mul_self (k := k) (vertex DG i)) π
    rw [mem_cornerSubmodule_iff k (hid b) (hid a)] at hz
    rw [← hz]
    obtain ⟨f, rfl⟩ := signlessPreprojectiveMk_surjective k (DoubledQuiver DG) z
    clear hz
    induction f using PathAlgebra.induction_linear with
    | zero =>
      simp only [map_zero, mul_zero, zero_mul]
      exact Submodule.zero_mem _
    | add f g hf hg =>
      simpa only [map_add, mul_add, add_mul] using Submodule.add_mem _ hf hg
    | single x r =>
      simpa only [single_eq_smul_ofPath, map_smul, mul_smul_comm, smul_mul_assoc] using
        Submodule.smul_mem _ r (corner_ofPath_mem_span k hn a b x)
  · exact Submodule.span_le.mpr (signlessPreprojectiveDNormalForms_subset_cornerSubmodule k a b)

end TauCeti
