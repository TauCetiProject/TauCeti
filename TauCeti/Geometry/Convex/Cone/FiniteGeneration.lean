/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Geometry.Convex.Cone.DualFinite
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import TauCeti.Geometry.Convex.Cone.Relations
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Finite generation under a halfspace cut

A finite generating family for a pointed cone can be cut by a linear halfspace:
retain its nonnegative generators and add boundary combinations of opposite-sign
generators. Support reduction proves that these generate the whole intersection.
The argument is algebraic and allows lineality.

## Provenance

Adapted from `Mei/Geometry/Convex/Cone/FiniteGeneration.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`68536122a97fed8e87bc6870b9427151971b9ab2`, licensed under Apache 2.0.
-/

public section

open scoped BigOperators

section

variable {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]

namespace LinearMap

/-- The combination `(-f v) • u + f u • v`, which always lies in the kernel of `f`.
Its coefficients are nonnegative when `f v ≤ 0 ≤ f u`. -/
def boundaryCombination (f : V →ₗ[K] K) (u v : V) : V :=
  (-f v) • u + f u • v

/-- The boundary combination uses the explicit coefficients `-f v` and `f u`. -/
theorem boundaryCombination_def (f : V →ₗ[K] K) (u v : V) :
    f.boundaryCombination u v = (-f v) • u + f u • v := by
  simp only [boundaryCombination]

/-- The cutting functional vanishes on a boundary combination. -/
@[simp]
theorem map_boundaryCombination (f : V →ₗ[K] K) (u v : V) :
    f (f.boundaryCombination u v) = 0 := by
  simp [boundaryCombination, map_add, map_smul, smul_eq_mul]
  ring

end LinearMap

variable [LinearOrder K]

namespace Finset

/-- The finite family obtained by retaining nonnegative generators and adding
boundary combinations of every pair with opposite strict signs. -/
noncomputable def halfspaceGenerators (s : Finset V) (f : V →ₗ[K] K) : Finset V := by
  classical
  exact s.filter (fun v => 0 ≤ f v) ∪
    ((s ×ˢ s).filter (fun p => 0 < f p.1 ∧ f p.2 < 0)).image
      (fun p => f.boundaryCombination p.1 p.2)

/-- A cut generator is either retained from the original family or is an explicit
boundary combination of two original generators with opposite strict signs. -/
@[simp]
theorem mem_halfspaceGenerators_iff {s : Finset V} {f : V →ₗ[K] K} {x : V} :
    x ∈ halfspaceGenerators s f ↔ (x ∈ s ∧ 0 ≤ f x) ∨
      ∃ u ∈ s, ∃ v ∈ s, 0 < f u ∧ f v < 0 ∧ f.boundaryCombination u v = x := by
  classical
  simp only [halfspaceGenerators, Finset.mem_union, Finset.mem_filter, Finset.mem_image,
    Finset.mem_product, Prod.exists, exists_and_left, and_assoc]

end Finset

end

section

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V]

namespace PointedCone

/-- Subtracting a suitable boundary pair removes a coefficient while preserving
nonnegativity and the value of the cutting functional. -/
private theorem exists_boundaryCombination_reduction {ι : Type*} [Fintype ι]
    (v : ι → V) (f : V →ₗ[K] K) (c : ι → K) (hc : 0 ≤ c)
    {i j : ι} (hci : c i ≠ 0) (hcj : c j ≠ 0) (hi : 0 < f (v i)) (hj : f (v j) < 0) :
    ∃ (r : K) (c' : ι → K), 0 < r ∧ 0 ≤ c' ∧
      Function.support c' ⊂ Function.support c ∧
      f (Fintype.linearCombination K v c') = f (Fintype.linearCombination K v c) ∧
      Fintype.linearCombination K v c =
        Fintype.linearCombination K v c' + r • f.boundaryCombination (v i) (v j) := by
  classical
  have hij : i ≠ j := by
    intro he
    exact (not_lt_of_ge hi.le) (he ▸ hj)
  let k : ι → K := Pi.single i (-f (v j)) + Pi.single j (f (v i))
  have hsupport : ∀ a, c a = 0 → k a = 0 := by
    intro a ha
    have hai : a ≠ i := fun he => hci (he ▸ ha)
    have haj : a ≠ j := fun he => hcj (he ▸ ha)
    simp [k, hai, haj]
  have hkpos : 0 < k i := by
    simpa [k, Pi.single_apply, hij] using neg_pos.mpr hj
  obtain ⟨r, hr, hc', hss⟩ :=
    TauCeti.exists_pos_sub_smul_nonneg_support_ssubset hc
      (Function.support k).toFinite hsupport ⟨i, hkpos⟩
  have hLk : Fintype.linearCombination K v k = f.boundaryCombination (v i) (v j) := by
    simp [k, map_add, Fintype.linearCombination_apply_single,
      LinearMap.boundaryCombination_def]
  exact ⟨r, c - r • k, hr, hc', hss,
    by simp [map_sub, map_smul, hLk], by simp [map_sub, map_smul, hLk]⟩

/-- A nonnegative finite combination satisfying the cutting inequality lies in
any cone containing the retained generators and opposite-sign boundary pairs. -/
private theorem linearCombination_mem_of_nonneg {ι : Type*} [Fintype ι]
    (D : PointedCone K V) (v : ι → V) (f : V →ₗ[K] K)
    (hgood : ∀ i, 0 ≤ f (v i) → v i ∈ D)
    (hpair : ∀ i j, 0 < f (v i) → f (v j) < 0 → f.boundaryCombination (v i) (v j) ∈ D)
    (c : ι → K) (hc : 0 ≤ c) (hf : 0 ≤ f (Fintype.linearCombination K v c)) :
    Fintype.linearCombination K v c ∈ D := by
  classical
  let L := Fintype.linearCombination K v
  -- Induct on the number of nonzero coefficients. Opposite-sign generators
  -- give a boundary pair whose subtraction removes at least one coefficient.
  have aux : ∀ n : ℕ, ∀ c : ι → K,
      (Function.support c).toFinite.toFinset.card = n → 0 ≤ c → 0 ≤ f (L c) → L c ∈ D := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro c hn hc hf
      by_cases hneg : ∃ j, c j ≠ 0 ∧ f (v j) < 0
      · obtain ⟨j, hcj, hj⟩ := hneg
        -- Mathlib's finite-sum witnesses supply a positive term, whether the sum
        -- is strictly positive or zero; nonnegative coefficients give its sign.
        have hsum : 0 ≤ ∑ i, c i * f (v i) := by
          simpa [L, Fintype.linearCombination_apply, map_sum, map_smul, smul_eq_mul] using hf
        have hex : ∃ i ∈ Finset.univ, 0 < c i * f (v i) := by
          rcases lt_or_eq_of_le hsum with h | h
          · exact Finset.exists_lt_of_sum_lt (by simpa using h)
          · exact Finset.exists_pos_of_sum_zero_of_exists_nonzero _ h.symm
              ⟨j, Finset.mem_univ _, mul_ne_zero hcj hj.ne⟩
        obtain ⟨i, _, hci⟩ := hex
        obtain ⟨hci, hi⟩ := (mul_pos_iff.mp hci).resolve_right
          (fun h => not_lt_of_ge (hc i) h.1)
        obtain ⟨r, c', hr, hc', hss, hfn, he⟩ :=
          exists_boundaryCombination_reduction v f c hc hci.ne' hcj hi hj
        have hstrict : (Function.support c').toFinite.toFinset ⊂
            (Function.support c).toFinite.toFinset := by
          rw [Set.Finite.toFinset_ssubset, Set.Finite.coe_toFinset]
          exact hss
        have hcard : (Function.support c').toFinite.toFinset.card < n := by
          rw [← hn]
          exact Finset.card_lt_card hstrict
        rw [he]
        exact D.add_mem (ih _ hcard c' rfl hc' (hfn ▸ hf))
          (PointedCone.smul_mem D hr.le (hpair i j hi hj))
      · -- With no negative-image generator in the support, each summand lies in D.
        dsimp only [L]
        rw [Fintype.linearCombination_apply]
        apply D.sum_mem
        intro i _
        by_cases hi : c i = 0
        · simp [hi]
        · have hfi : 0 ≤ f (v i) := le_of_not_gt (fun h => hneg ⟨i, hi, h⟩)
          exact PointedCone.smul_mem D (hc i) (hgood i hfi)
  exact aux _ c rfl hc hf

end PointedCone

namespace Finset

open PointedCone

/-- The retained generators and boundary pairs generate exactly the intersection
of the original cone with the nonnegative halfspace of `f`. -/
theorem hull_halfspaceGenerators (s : Finset V) (f : V →ₗ[K] K) :
    hull K (halfspaceGenerators s f : Set V) =
      hull K (s : Set V) ⊓ dual (LinearMap.id : Module.Dual K V →ₗ[K] Module.Dual K V) {f} := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro z hz
    rcases mem_halfspaceGenerators_iff.mp hz with ⟨hzs, hfz⟩ | ⟨u, hu, v, hv, hfu, hfv, rfl⟩
    · exact ⟨subset_hull hzs, by simpa using hfz⟩
    · refine ⟨?_, ?_⟩
      · exact (hull K (s : Set V)).add_mem
          (PointedCone.smul_mem _ (neg_nonneg.mpr hfv.le) (subset_hull hu))
          (PointedCone.smul_mem _ hfu.le (subset_hull hv))
      · simp
  · intro x hx
    let v : s → V := fun i => i.val
    have he : Set.range v = (s : Set V) := by
      ext y
      simp [v]
    have hxC := hx.1
    rw [← he] at hxC
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (Nonneg K)).mp hxC
    have hc' : Fintype.linearCombination K v (fun i => (c i : K)) = x := by
      simpa only [Fintype.linearCombination_apply, Nonneg.coe_smul] using hc
    have hfx : 0 ≤ f x := by simpa using hx.2
    rw [← hc']
    apply PointedCone.linearCombination_mem_of_nonneg _ v f
    · intro i hi
      apply subset_hull
      exact mem_halfspaceGenerators_iff.mpr (Or.inl ⟨i.property, hi⟩)
    · intro i j hi hj
      apply subset_hull
      exact mem_halfspaceGenerators_iff.mpr
        (Or.inr ⟨i.val, i.property, j.val, j.property, hi, hj, rfl⟩)
    · exact fun i => (c i).property
    · simpa only [hc'] using hfx

end Finset

namespace PointedCone

/-- Intersecting a finitely generated pointed cone with a linear halfspace
preserves finite generation, without any salience or ambient dimension assumption. -/
theorem _root_.Submodule.FG.inf_cone_dual_singleton {C : PointedCone K V} (hC : C.FG)
    (f : V →ₗ[K] K) :
    (C ⊓ dual (LinearMap.id : Module.Dual K V →ₗ[K] Module.Dual K V) {f}).FG := by
  obtain ⟨s, rfl⟩ := hC
  rw [← Finset.hull_halfspaceGenerators]
  exact Submodule.fg_span (s.halfspaceGenerators f).finite_toSet

/-- A cone given by finitely many linear inequalities in a finite-dimensional
space is finitely generated. The pairing may be arbitrary and degenerate. -/
theorem DualFG.fg {M N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [Module.Finite K N]
    {p : M →ₗ[K] N →ₗ[K] K} {C : PointedCone K N} (hC : C.DualFG p) : C.FG := by
  classical
  obtain ⟨s, rfl⟩ := hC
  induction s using Finset.induction_on with
  | empty => simpa using (Module.Finite.fg_top : (⊤ : PointedCone K N).FG)
  | @insert a s ha ih =>
    rw [Finset.coe_insert, dual_insert]
    have he : dual p {a} =
        dual (LinearMap.id : Module.Dual K N →ₗ[K] Module.Dual K N) {p a} := by
      ext y
      simp
    rw [he, inf_comm]
    exact ih.inf_cone_dual_singleton (p a)

end PointedCone

end
