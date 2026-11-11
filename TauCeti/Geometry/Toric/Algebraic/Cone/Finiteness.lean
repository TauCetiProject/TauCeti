/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Finiteness
import TauCeti.Algebra.Group.Submonoid.Finiteness
import TauCeti.Geometry.Convex.Cone.Alternative

/-!
# Finite generation of lattice points in rational cones

The lattice points in a lattice-rational cone form a finitely generated additive monoid, with no
salience assumption (Gordan's lemma for lattice points). Integral characters separate a lattice
point outside the cone from the cone, so membership of a lattice point in the cone is tested by the
characters of its dual semigroup. This is the lattice-point form of the bipolar theorem.

The separation argument applies the integral Tucker theorem
`TauCeti.exists_nat_sum_nsmul_eq_zero_and_forall_coeff_add_dual_pos` to the lattice generators of
the cone together with the negative of the lattice point. Finite generation then follows as for
`TauCeti.Toric.IsLatticeRational.fg_dualSemigroup`: the lattice points are the preimage of the
nonnegative orthant under the evaluation of the finitely many generators of the dual semigroup.

## Main declarations

* `TauCeti.Toric.IsLatticeRational.exists_mem_dualSemigroup_neg_of_notMem`: a lattice point outside
  a lattice-rational cone is separated from it by an integral character.
* `TauCeti.Toric.IsLatticeRational.mem_iff_forall_dualSemigroup_nonneg`: membership of a lattice
  point in a lattice-rational cone is nonnegativity of every character of the dual semigroup.
* `TauCeti.Toric.IsLatticeRational.fg_comap_toAddSubmonoid`: Gordan's lemma for the lattice points
  of a lattice-rational cone.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.2, Proposition 1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §1.2, Proposition 1.2.17.

Adapted from `Mei/Geometry/Toric/Algebraic/Cone/Finiteness.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`, released under Apache 2.0.
-/

public section

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

/-- An integral character separates a lattice point outside a lattice-rational cone: it is
nonnegative on the cone and strictly negative on the given lattice point. -/
theorem IsLatticeRational.exists_mem_dualSemigroup_neg_of_notMem (hσ : IsLatticeRational i σ)
    (hi : IsIntegralLattice i) {n : N} (hn : i n ∉ σ) :
    ∃ m ∈ dualSemigroup hi σ, m n < 0 := by
  classical
  have := hi.free
  have := hi.finite
  obtain ⟨s, rfl⟩ := isLatticeRational_iff.mp hσ
  let v : Option s → N := Option.elim' (-n) fun a => a
  obtain ⟨c, m, hrel, hm, hpos⟩ :=
    TauCeti.exists_nat_sum_nsmul_eq_zero_and_forall_coeff_add_dual_pos v
  have heq : ∑ a : s, c (some a) • (a : N) = c none • n := by
    apply Eq.symm
    simpa [v, Fintype.sum_option, neg_add_eq_zero] using hrel
  -- A positive coefficient of `-n` would put a positive multiple of `i n` in the cone.
  have hc : c none = 0 := by
    by_contra hne
    have hmem : (c none : ℝ) • i n ∈ PointedCone.hull ℝ (i '' (s : Set N)) := by
      rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, ← heq, map_sum]
      exact Submodule.sum_mem _ fun a _ => by
        rw [map_nsmul]
        exact Submodule.smul_of_tower_mem _ _
          (PointedCone.subset_hull (Set.mem_image_of_mem i a.property))
    exact hn ((PointedCone.smul_mem_iff _
      (by exact_mod_cast Nat.pos_of_ne_zero hne)).mp hmem)
  refine ⟨m, (mem_dualSemigroup_hull_image hi _ m).mpr ?_, ?_⟩
  · intro a ha
    simpa [v] using hm (some ⟨a, ha⟩)
  · have := hpos none
    simpa [hc, v] using this

/-- Integral bipolarity at lattice points: a lattice point lies in a lattice-rational cone exactly
when every character of the dual semigroup is nonnegative on it. -/
theorem IsLatticeRational.mem_iff_forall_dualSemigroup_nonneg (hσ : IsLatticeRational i σ)
    (hi : IsIntegralLattice i) (n : N) :
    i n ∈ σ ↔ ∀ m ∈ dualSemigroup hi σ, 0 ≤ m n := by
  refine ⟨fun hn m hm => ?_, fun hn => ?_⟩
  · simpa using (mem_dualSemigroup hi m).mp hm hn
  · by_contra hnot
    obtain ⟨m, hm, hneg⟩ := hσ.exists_mem_dualSemigroup_neg_of_notMem hi hnot
    exact (not_lt_of_ge (hn m hm)) hneg

/-- **Gordan's lemma for lattice points.** The lattice points of a lattice-rational cone form a
finitely generated additive submonoid. The cone may contain lines. -/
theorem IsLatticeRational.fg_comap_toAddSubmonoid (hσ : IsLatticeRational i σ)
    (hi : IsIntegralLattice i) : (σ.toAddSubmonoid.comap i).FG := by
  classical
  have : AddMonoid.FG N := AddGroup.fg_iff_addMonoid_fg.mp
    (Module.Finite.iff_addGroup_fg.mp hi.finite)
  obtain ⟨s, hs⟩ := AddSubmonoid.isAddFG_iff.mp
    ((AddMonoid.fg_iff_addSubmonoid_fg _).mp (hσ.fg_dualSemigroup hi))
  -- Finitely many generators of the dual semigroup already test membership of lattice points.
  have hmem (n : N) : i n ∈ σ ↔ ∀ m ∈ s, 0 ≤ m n := by
    rw [hσ.mem_iff_forall_dualSemigroup_nonneg hi]
    refine ⟨fun hn m hm => hn m (hs ▸ AddSubmonoid.subset_closure hm), fun hn m hm => ?_⟩
    rw [← hs] at hm
    induction hm using AddSubmonoid.closure_induction with
    | mem m hm => exact hn m hm
    | zero => simp
    | add a b _ _ iha ihb => simpa using add_nonneg iha ihb
  let ev : N →+ (s → ℤ) := AddMonoidHom.pi fun m => m.val
  let cast : (s → ℕ) →+ (s → ℤ) := (Nat.castAddMonoidHom ℤ).compLeft s
  have hfg : ((AddMonoidHom.mrange cast).comap ev).FG := by
    rw [AddMonoidHom.mrange_eq_map]
    exact ((AddMonoid.FG.fg_top (M := s → ℕ)).map cast).comap ev
  convert hfg using 1
  ext n
  rw [AddSubmonoid.mem_comap, AddSubmonoid.mem_comap, AddMonoidHom.mem_mrange,
    Submodule.mem_toAddSubmonoid, hmem]
  refine ⟨fun hn => ⟨fun m => (m.val n).toNat, funext fun m => ?_⟩, ?_⟩
  · exact Int.toNat_of_nonneg (hn m.val m.property)
  · rintro ⟨a, ha⟩ m hm
    have h : (a ⟨m, hm⟩ : ℤ) = m n := congrFun ha ⟨m, hm⟩
    exact h ▸ Int.natCast_nonneg _

end TauCeti.Toric
