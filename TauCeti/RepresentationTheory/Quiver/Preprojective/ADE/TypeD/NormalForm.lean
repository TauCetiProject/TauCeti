/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.Words
-- Reuse the internal path reduction without exposing its auxiliary definitions.
import all TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Corner

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

section ForkGraph

variable (G : SimpleGraph (Fin n)) (c : ℕ)

/-- The direct path out of the branch node towards `j`. -/
private noncomputable def forkExit (j : ℕ) :=
  if j ≤ c then ladderValley (forkUp k G c) (forkDown k G c) 0 0 (c - j)
  else signlessArrow k G c j

end ForkGraph

section NormalWords

local notation "DG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.D n))
local notation "Π" => signlessPreprojectiveAlgebra k (DoubledQuiver DG)
local notation "π" => signlessPreprojectiveMk k (DoubledQuiver DG)
local notation "dc" => n - 3
local notation "e" => fun a : Fin (DynkinType.D n).rank => π (vertexIdempotent k (vertex DG a))
local notation "entry" => forkEntry k (n := DynkinType.rank (DynkinType.D n)) DG dc
local notation "exit" => forkExit k (n := DynkinType.rank (DynkinType.D n)) DG dc
local notation "turn" => forkTurn k (n := DynkinType.rank (DynkinType.D n)) DG dc
local notation "S" => forkSpan k (n := DynkinType.rank (DynkinType.D n)) DG dc

/-- Alternating fork backtracks, placed between the direct entry and exit paths, lie in the
span of the finite normal-word family. -/
private theorem forkBranch_mem_span_normalForms (hn : 3 ≤ n)
    (a b : Fin (DynkinType.D n).rank) (t : ℕ) (w : Π) (hw : w ∈ S ^ t) :
    e b * exit b.val * w * entry a.val (e a) ∈
      Submodule.span k (signlessPreprojectiveDNormalForms k a b) := by
  let M := Submodule.span k (signlessPreprojectiveDNormalForms k a b)
  have hword (l : Bool) (s : ℕ) (hs : s < dc + 2) :
      e b * exit b.val *
        (if s = 0 then 1 else
          (if l then turn (dc + 1) else turn (dc + 2)) *
            (turn (dc + 1) + turn (dc + 2)) ^ (s - 1)) * entry a.val (e a) ∈ M := by
    have hmem : signlessPreprojectiveDBranchWord k a b l s ∈ M := by
      apply Submodule.subset_span
      rw [signlessPreprojectiveDNormalForms_def]
      exact .inl (.inr ⟨(l, ⟨s, hs⟩), Set.mem_univ _, rfl⟩)
    rw [signlessPreprojectiveDBranchWord_def] at hmem
    dsimp only [forkExit, forkEntry, forkTurn] at hmem ⊢
    unfold forkUp forkDown
    simpa only [ite_mul, mul_assoc] using hmem
  have hn' : (DynkinType.D n).rank = dc + 3 := by rw [DynkinType.rank_D]; omega
  have hG := diagramGraph_D_adj hn
  by_cases ht : dc + 2 ≤ t
  · have hzero := forkSpan_pow_eq_bot k (G := DG) hn' hG ht
    have hw0 : w = 0 := (Submodule.mem_bot ℤ).mp (hzero ▸ hw)
    simp only [hw0, mul_zero, zero_mul, Submodule.zero_mem]
  cases t with
  | zero =>
    rw [pow_zero, Submodule.one_eq_span] at hw
    obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp hw
    simpa only [← Int.cast_smul_eq_zsmul k, mul_smul_comm, smul_mul_assoc, ite_true] using
      M.smul_of_tower_mem α (hword false 0 (by omega))
  | succ t =>
    have hx := forkTurn_mul_self k (G := DG) hn' hG (l := dc + 1) (by omega) (by omega)
    have hy := forkTurn_mul_self k (G := DG) hn' hG (l := dc + 2) (by omega) (by omega)
    have hw' := span_pair_pow_succ_le (R := ℤ) hx hy t hw
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hw'
    have hleft := hword true (t + 1) (by omega)
    have hright := hword false (t + 1) (by omega)
    simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, ite_false, Bool.false_eq_true,
      ite_true] at hleft hright
    simpa only [mul_add, add_mul, ← Int.cast_smul_eq_zsmul k, mul_smul_comm, smul_mul_assoc] using
      M.add_mem (M.smul_of_tower_mem α hleft) (M.smul_of_tower_mem β hright)

/-- Every path class from `a` to `b` belongs to the span of the explicit type-`D` corner words.
This is a uniform spanning theorem, with no independence or characteristic assumption. -/
theorem signlessPreprojectiveMk_D_ofPath_mem_span_normalForms (hn : 3 ≤ n)
    {a b : Fin (DynkinType.D n).rank} (p : Path (vertex DG a) (vertex DG b)) :
    π (ofPath ⟨_, _, p⟩) ∈ Submodule.span k (signlessPreprojectiveDNormalForms k a b) := by
  let M := Submodule.span k (signlessPreprojectiveDNormalForms k a b)
  have hcorner : e b * π (ofPath ⟨_, _, p⟩) = π (ofPath ⟨_, _, p⟩) := by
    rw [← map_mul, vertexIdempotent_mul_ofPath]
  have hnf := forkNormalForm_ofPath k (G := DG) (c := dc)
    (by rw [DynkinType.rank_D]; omega) (diagramGraph_D_adj hn) p
  rw [ForkNormalForm] at hnf
  simp only [vertexEquiv_symm_vertex, ← vertexIdempotent_eq_ofPath] at hnf
  rcases hnf with ⟨m, s, r, ε, hm, -, hs, hr, hz⟩ |
    ⟨t, s₀, w, D, hw, -, hb, -, hz, ε, hD⟩ |
    ⟨t, s₀, w, D, hw, -, hb, -, hz, ε, hD⟩ | ⟨-, hb, hab, hz⟩
  · have ha : a.val ≤ dc := by omega
    have hb : b.val ≤ dc := by omega
    have hval : signlessPreprojectiveDValley k a b m ∈ M := by
      apply Submodule.subset_span
      rw [signlessPreprojectiveDNormalForms_def, ite_eq_left ⟨ha, hb⟩]
      exact .inl (.inl ⟨m, Finset.mem_Icc.mpr ⟨hm, by omega⟩, rfl⟩)
    rw [← hcorner, hz, mul_smul_comm]
    have hs' : dc - a.val - m = s := by omega
    have hr' : dc - b.val - m = r := by omega
    unfold forkUp forkDown
    simpa only [signlessPreprojectiveDValley_def, hs', hr', mul_assoc] using
      M.smul_of_tower_mem ε hval
  · rw [← hcorner, hz, hD]
    have h := forkBranch_mem_span_normalForms k hn a b t w hw
    rw [forkExit, ite_eq_left hb] at h
    simpa only [mul_assoc, mul_smul_comm] using M.smul_of_tower_mem ε h
  · rw [← hcorner, hz, hD]
    have h := forkBranch_mem_span_normalForms k hn a b t w hw
    rw [forkExit, ite_eq_right (by omega)] at h
    simpa only [mul_assoc, mul_smul_comm] using M.smul_of_tower_mem ε h
  · have hab' : a = b := Fin.ext hab.symm
    rw [hz]
    apply Submodule.subset_span
    rw [signlessPreprojectiveDNormalForms_def]
    apply Or.inr
    rw [ite_eq_left ⟨hab', by omega⟩]
    exact Set.mem_singleton _

end NormalWords

local notation "DG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.D n))
local notation "π" => signlessPreprojectiveMk k (DoubledQuiver DG)
local notation "e" => fun a : Fin (DynkinType.D n).rank => π (vertexIdempotent k (vertex DG a))

/-- The finite family of arm valleys, alternating fork words, and leaf idempotents spans the
entire corner `e_b Π e_a` of the type-`D` signless preprojective algebra. -/
theorem cornerSubmodule_signlessPreprojective_D_eq_span_normalForms (hn : 3 ≤ n)
    (a b : Fin (DynkinType.D n).rank) :
    cornerSubmodule k (e b) (e a) = Submodule.span k (signlessPreprojectiveDNormalForms k a b) := by
  apply le_antisymm
  · exact PathAlgebra.cornerSubmodule_le_of_ofPath_mem (π).toNonUnitalAlgHom
      (signlessPreprojectiveMk_surjective k (DoubledQuiver DG)) (vertex DG a) (vertex DG b)
      (Submodule.span k (signlessPreprojectiveDNormalForms k a b))
      (signlessPreprojectiveMk_D_ofPath_mem_span_normalForms k hn)
  · exact Submodule.span_le.mpr (signlessPreprojectiveDNormalForms_subset_cornerSubmodule k a b)

end TauCeti
