/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite spans and singleton spans

A generator with a unit coefficient in a linear combination can be replaced by that combination
without changing the span. Over a division semiring, a nonzero vector in a singleton span can be
used to recover the generator's membership in any submodule. Acting on a line gives the line
through the image of its generator, so a group element stabilizes the line through a vector
exactly when it sends that vector to a multiple of itself. Finally, a submodule over a
subring that is a direct sum `⊕ i, J i • y i` with nonzero ideal coefficients spans the same
subspace over the larger field as the family `y`.
-/

public section

namespace TauCeti.Submodule

variable {A : Type*} [Ring A] {M : Type*} [AddCommGroup M] [Module A M]

/-- If one coefficient of `x` in a finite span is a unit, then `x` can replace that generator. -/
theorem span_insert_erase_eq_span_of_isUnit [DecidableEq M] {s : Finset M} {i x : M}
    {f : M → A} (hi : i ∈ s) (hf : ∑ a ∈ s, f a • a = x) (hfi : IsUnit (f i)) :
    _root_.Submodule.span A ((insert x (s.erase i)) : Set M) =
      _root_.Submodule.span A (s : Set M) := by
  have hx : x ∈ _root_.Submodule.span A (s : Set M) :=
    hf ▸ sum_mem fun a ha ↦ Submodule.smul_mem _ _ (Submodule.subset_span ha)
  have hi' : i ∈ _root_.Submodule.span A (insert x (s.erase i : Set M)) := by
    refine (Submodule.smul_mem_iff_of_isUnit _ hfi).mp (Submodule.mem_span_insert.mpr
      ⟨1, -∑ a ∈ s.erase i, f a • a,
        neg_mem (sum_mem fun a ha ↦ Submodule.smul_mem _ _ (Submodule.subset_span ha)), ?_⟩)
    rw [one_smul, ← hf, ← Finset.add_sum_erase _ _ hi, add_neg_cancel_right]
  calc _ = _root_.Submodule.span A (insert i (insert x (s.erase i : Set M))) :=
        (Submodule.span_insert_eq_span hi').symm
    _ = _root_.Submodule.span A (insert x (s : Set M)) := by
      rw [Set.insert_comm, ← Finset.coe_insert, Finset.insert_erase hi]
    _ = _ := Submodule.span_insert_eq_span hx

end TauCeti.Submodule

namespace Submodule

variable {K V : Type*} [DivisionSemiring K] [AddCommMonoid V] [Module K V]

/-- If a nonzero member of a submodule lies in the span of `y`, then `y` also belongs to
the submodule. -/
theorem mem_of_mem_span_singleton_of_ne_zero (P : Submodule K V) {x y : V}
    (hx : x ∈ P) (hx0 : x ≠ 0) (hxy : x ∈ K ∙ y) : y ∈ P := by
  obtain ⟨c, rfl⟩ := mem_span_singleton.mp hxy
  exact (P.smul_mem_iff (left_ne_zero_of_smul hx0)).mp hx

section Action

open Pointwise

variable {R M G : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Monoid G]
  [DistribMulAction G M] [SMulCommClass G R M]

/-- Acting on the line through `v` gives the line through the image of `v`. -/
theorem smul_span_singleton (g : G) (v : M) : g • (R ∙ v) = R ∙ (g • v) := by
  rw [smul_span, Set.smul_set_singleton]

end Action

section GroupAction

open Pointwise

variable {D W G : Type*} [DivisionRing D] [AddCommGroup W] [Module D W] [Group G]
  [DistribMulAction G W] [SMulCommClass G D W]

/-- A group element stabilizes the line through `v` exactly when `g • v` is a multiple of `v`. -/
theorem smul_span_singleton_eq_iff {g : G} {v : W} :
    g • (D ∙ v) = D ∙ v ↔ ∃ c : D, g • v = c • v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  rw [smul_span_singleton, span_singleton_eq_span_singleton]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨((z⁻¹ : Dˣ) : D), by rw [← Units.smul_def]; exact eq_inv_smul_iff.mpr hz⟩
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := left_ne_zero_of_smul (hc ▸ (smul_ne_zero_iff_ne g).mpr hv)
    exact ⟨(Units.mk0 c hc0)⁻¹, by simp [hc, Units.smul_def, smul_smul, hc0]⟩

end GroupAction

section IdealCoefficients

variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V]

/-- If `Λ = ⊕ i, J i • y i` with every `J i` nonzero, then `y` spans the same `K`-subspace as
`Λ`. -/
theorem span_range_eq_span_of_forall_mem_iff [FaithfulSMul R K] {ι : Type*} [Fintype ι]
    {Λ : Submodule R V} {y : ι → V} {J : ι → Ideal R} (hJ : ∀ i, J i ≠ ⊥)
    (hmem : ∀ x, x ∈ Λ ↔ ∃ c : ι → R, (∀ i, c i ∈ J i) ∧ ∑ i, c i • y i = x) :
    span K (Set.range y) = span K (Λ : Set V) := by
  classical
  refine le_antisymm (span_le.2 <| Set.range_subset_iff.2 fun i ↦ ?_) (span_le.2 fun x hx ↦ ?_)
  · obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hJ i)
    have hsum : ∑ k, (Pi.single i b : ι → R) k • y k = b • y i := by
      rw [Fintype.sum_eq_single i fun k hk ↦ by simp [hk]]
      simp
    have hbΛ : b • y i ∈ Λ := hsum ▸ (hmem _).2 ⟨_, fun k ↦ by
      by_cases hk : k = i
      · subst hk
        simpa using hb
      · simp [hk], rfl⟩
    have hb' : algebraMap R K b ≠ 0 :=
      (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R K)).2 hb0
    rw [← inv_smul_smul₀ hb' (y i), algebraMap_smul]
    exact smul_mem _ _ (subset_span hbΛ)
  · obtain ⟨c, -, rfl⟩ := (hmem x).1 hx
    exact sum_mem fun i _ ↦ by
      rw [← algebraMap_smul K]
      exact smul_mem _ _ (subset_span ⟨i, rfl⟩)

end IdealCoefficients

end Submodule
