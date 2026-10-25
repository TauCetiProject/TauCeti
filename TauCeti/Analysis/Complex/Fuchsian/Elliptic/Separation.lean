/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Systole
import TauCeti.Analysis.Complex.UpperHalfPlane.Stabilizer
import TauCeti.Analysis.Complex.UpperHalfPlane.Displacement
import TauCeti.Topology.MetricSpace.IsometricSMul

/-!
# Separation of elliptic thin neighbourhoods

For a cofinite Fuchsian group there is a positive displacement threshold such that two
nonidentity elliptic elements with different fixed points have disjoint displacement sublevel
sets. More generally, if an elliptic element and any other group element both move a point less
than this threshold, the second element fixes the elliptic centre. Unlike the fixed-point-free
Margulis lemma, this threshold depends on the group, through its positive hyperbolic systole.

These are the elliptic separation estimates used in decomposing a cofinite quotient into a
compact thick part and cusp and elliptic thin neighbourhoods. They also give uniform separation
of the elliptic points upstairs, and hence uniformly sized disjoint stabilizer balls.
No compactness of the cusp compactification or finiteness of the elliptic orbits is assumed.

The argument combines the positive systole theorem with the commutator trace formula
`Matrix.SpecialLinearGroup.trace_commutatorElement_of_smul_eq_self`: the commutator of a
nontrivial elliptic element with an element moving its centre is hyperbolic, while its
displacement is at most twice the sum of the two factor displacements.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Chapters 7 and 9.
* Riccardo Benedetti and Carlo Petronio, *Lectures on Hyperbolic Geometry*, Chapter D
  (thick-thin decomposition).
-/

public section

open Metric MulAction Set UpperHalfPlane TauCeti
open scoped MatrixGroups commutatorElement Pointwise

namespace Subgroup

variable {Γ : Subgroup PSL(2, ℝ)}

/-- A hyperbolic systole bound controls the sum of the displacements of an elliptic element
and any group element moving its fixed point. -/
theorem le_two_mul_dist_add_dist_of_smul_eq_self {δ : ℝ}
    (hδ : ∀ A : SL(2, ℝ), (A : PSL(2, ℝ)) ∈ Γ →
      2 < |(A : Matrix (Fin 2) (Fin 2) ℝ).trace| → ∀ x : ℍ, δ ≤ dist (A • x) x)
    {g h : PSL(2, ℝ)} (hg : g ∈ Γ) (hh : h ∈ Γ) (hg1 : g ≠ 1) {z : ℍ}
    (hgz : g • z = z) (hhz : h • z ≠ z) (x : ℍ) :
    δ ≤ 2 * (dist (g • x) x + dist (h • x) x) := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective h
  have hAz : A • z = z := by simpa only [pslMk_smul] using hgz
  have hBz : B • z ≠ z := by simpa only [pslMk_smul] using hhz
  have htr := Matrix.SpecialLinearGroup.two_lt_trace_commutatorElement_of_smul_eq_self
    hAz hg1 hBz
  have hmem : ((⁅A, B⁆ : SL(2, ℝ)) : PSL(2, ℝ)) ∈ Γ := by
    simpa only [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv] using
      Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hg hh) (Γ.inv_mem hg)) (Γ.inv_mem hh)
  have hlow := hδ ⁅A, B⁆ hmem (htr.trans_le (le_abs_self _)) x
  exact hlow.trans (by simpa only [pslMk_smul] using dist_commutatorElement_smul_le A B x)

/-- In a cofinite group, elements with sufficiently small displacement near an elliptic thin
point fix its elliptic centre. The threshold is uniform in the elements and points. -/
theorem IsCofinite.exists_pos_smul_eq_self_of_dist_lt (hΓ : Γ.IsCofinite) :
    ∃ ε > 0, ∀ g ∈ Γ, ∀ h ∈ Γ, ∀ z x : ℍ, g ≠ 1 → g • z = z →
      dist (g • x) x < ε → dist (h • x) x < ε → h • z = z := by
  obtain ⟨δ, hδ, hsyst⟩ := hΓ.exists_pos_le_dist_smul_of_two_lt_abs_trace
  refine ⟨δ / 4, by positivity, fun g hg h hh z x hg1 hgz hgx hhx ↦ ?_⟩
  by_contra hhz
  have := le_two_mul_dist_add_dist_of_smul_eq_self hsyst hg hh hg1 hgz hhz x
  linarith

/-- In a cofinite group, small displacement neighbourhoods of nontrivial elliptic elements
with different fixed points are disjoint. This includes different lifts of the same elliptic
orbit. -/
theorem IsCofinite.exists_pos_disjoint_elliptic_displacement_sets (hΓ : Γ.IsCofinite) :
    ∃ ε > 0, ∀ g ∈ Γ, ∀ h ∈ Γ, ∀ z w : ℍ, g ≠ 1 → h ≠ 1 →
      g • z = z → h • w = w → z ≠ w →
      Disjoint {x : ℍ | dist (g • x) x < ε} {x : ℍ | dist (h • x) x < ε} := by
  obtain ⟨ε, hε, hsmall⟩ := hΓ.exists_pos_smul_eq_self_of_dist_lt
  refine ⟨ε, hε, fun g hg h hh z w hg1 hh1 hgz hhw hzw ↦ disjoint_left.mpr ?_⟩
  intro x hgx hhx
  have hhz := hsmall g hg h hh z x hg1 hgz hgx hhx
  exact hh1 (Matrix.ProjectiveSpecialLinearGroup.eq_one_of_smul_eq_self_of_smul_eq_self
    hhz hhw hzw.symm)

/-- The elliptic fixed points upstairs in a cofinite Fuchsian group are uniformly separated
in the hyperbolic metric. The separation constant does not depend on the stabilizer orders. -/
theorem IsCofinite.exists_pos_le_dist_of_stabilizer_ne_bot (hΓ : Γ.IsCofinite) :
    ∃ r > 0, ∀ z w : ℍ, stabilizer Γ z ≠ ⊥ → stabilizer Γ w ≠ ⊥ → z ≠ w →
      r ≤ dist z w := by
  obtain ⟨ε, hε, hsmall⟩ := hΓ.exists_pos_smul_eq_self_of_dist_lt
  refine ⟨ε / 2, by positivity, fun z w hz hw hzw ↦ ?_⟩
  obtain ⟨g, hg, hg1⟩ := (stabilizer Γ z).bot_or_exists_ne_one.resolve_left hz
  obtain ⟨h, hh, hh1⟩ := (stabilizer Γ w).bot_or_exists_ne_one.resolve_left hw
  have hgz : (g : PSL(2, ℝ)) • z = z := mem_stabilizer_iff.mp hg
  have hhw : (h : PSL(2, ℝ)) • w = w := mem_stabilizer_iff.mp hh
  have hg1' : (g : PSL(2, ℝ)) ≠ 1 := fun he ↦ hg1 (Subtype.ext he)
  have hh1' : (h : PSL(2, ℝ)) ≠ 1 := fun he ↦ hh1 (Subtype.ext he)
  by_contra! hdist
  have hhz : (h : PSL(2, ℝ)) • z = z := by
    apply hsmall g g.property h h.property z z hg1' hgz
    · simpa only [hgz, dist_self] using hε
    · have htri := dist_triangle ((h : PSL(2, ℝ)) • z) w z
      have heq : dist ((h : PSL(2, ℝ)) • z) w = dist z w := by
        calc
          _ = dist ((h : PSL(2, ℝ)) • z) ((h : PSL(2, ℝ)) • w) :=
            congrArg (dist ((h : PSL(2, ℝ)) • z)) hhw.symm
          _ = dist z w := dist_smul _ _ _
      rw [heq, dist_comm w z] at htri
      linarith
  exact hh1' (Matrix.ProjectiveSpecialLinearGroup.eq_one_of_smul_eq_self_of_smul_eq_self
    hhz hhw hzw.symm)

/-- Small elliptic displacement neighbourhoods have disjoint translates outside the centre
stabilizer. The same threshold works for every nonidentity elliptic element of a cofinite group. -/
theorem IsCofinite.exists_pos_disjoint_smul_elliptic_displacement_set (hΓ : Γ.IsCofinite) :
    ∃ ε > 0, ∀ g ∈ Γ, ∀ z : ℍ, g ≠ 1 → g • z = z → ∀ h ∈ Γ, h • z ≠ z →
      Disjoint (h • {x : ℍ | dist (g • x) x < ε}) {x : ℍ | dist (g • x) x < ε} := by
  obtain ⟨ε, hε, hdisj⟩ := hΓ.exists_pos_disjoint_elliptic_displacement_sets
  refine ⟨ε, hε, fun g hg z hg1 hgz h hh hhz ↦ ?_⟩
  have hconj : h * g * h⁻¹ ∈ Γ := Γ.mul_mem (Γ.mul_mem hh hg) (Γ.inv_mem hh)
  have hconj1 : h * g * h⁻¹ ≠ 1 := by
    intro he
    apply hg1
    simpa [MulAut.conj_apply, mul_assoc] using congrArg (MulAut.conj h⁻¹) he
  have hfix : (h * g * h⁻¹) • (h • z) = h • z := by
    simp only [mul_smul, inv_smul_smul, hgz]
  have heq : h • {x : ℍ | dist (g • x) x < ε} =
      {x : ℍ | dist ((h * g * h⁻¹) • x) x < ε} := by
    ext x
    simp only [mem_smul_set_iff_inv_smul_mem, mem_ofPred_eq, dist_conj_smul]
  rw [heq]
  exact hdisj _ hconj g hg _ z hconj1 hg1 hfix hgz hhz

/-- A cofinite group admits a uniform radius for stabilizer balls at all elliptic points:
translates by elements outside the point stabilizer are disjoint. -/
theorem IsCofinite.exists_pos_disjoint_smul_ball_of_stabilizer_ne_bot (hΓ : Γ.IsCofinite) :
    ∃ r > 0, ∀ z : ℍ, stabilizer Γ z ≠ ⊥ → ∀ g : Γ, g • z ≠ z →
      Disjoint (g • ball z r) (ball z r) := by
  obtain ⟨r, hr, hsep⟩ := hΓ.exists_pos_le_dist_of_stabilizer_ne_bot
  refine ⟨r / 2, by positivity, fun z hz g hgz ↦ ?_⟩
  have hgz' : stabilizer Γ (g • z) ≠ ⊥ := by
    rw [stabilizer_smul_eq_stabilizer_map_conj]
    exact fun he ↦ hz
      (((stabilizer Γ z).map_eq_bot_iff_of_injective (MulAut.conj g).injective).mp he)
  rw [Metric.smul_ball]
  exact ball_disjoint_ball (by linarith [hsep (g • z) z hgz' hz hgz])

end Subgroup
