/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Rational.Sweep
public import TauCeti.Analysis.Convex.Polyhedron.Rational.LocallyClosed

/-!
# Polyhedral encounters along finite affine segments

The parameters for which a segment in a fixed lattice direction meets a closed
rational-normal polyhedron in its open time interval form a rational semilinear
set. Both its starting point and its duration may depend affinely on the parameter,
with rational linear parts. Tangencies and singleton intersections are retained.

The theorem characterizes the exact encounter set without transversality assumptions,
including zero slope and segments parallel to a wall's hyperplanes. Since rational
semilinearity is preserved by complements, it also characterizes avoidance of the
polyhedron by the whole open segment.

Adapted from `Mei/Geometry/Convex/Polyhedron/Rational/Segment.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public section

namespace TauCeti

variable {N V W : Type*} [AddCommGroup N] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  {j : N →+ W} {h : TauCeti.Toric.IsIntegralLattice j}

section Elimination

/-- Eliminating a strictly bounded parameter with rational slopes preserves
rational semilinearity. The base functionals `g j` and upper bound `T` may vary
affinely with rational linear parts and arbitrary real constant terms. -/
theorem isRationalSemilinear_setOf_exists_pos_lt_affine_le {κ : Type*} [Finite κ]
    (g : κ → W →ᴬ[ℝ] ℝ) (a : κ → ℝ) (T : W →ᴬ[ℝ] ℝ)
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear)
    (ha : ∀ j, ∃ q : ℚ, a j = (q : ℝ))
    (hT : Toric.IsRationalFunctional h T.toAffineMap.linear) :
    IsRationalSemilinear h {x | ∃ t : ℝ, 0 < t ∧ t < T x ∧ ∀ j, g j x + a j * t ≤ 0} := by
  have hs : IsRationalSemilinear h {x | (-T) x < 0} :=
    .setOf_neg hT.neg
  have hz := IsRationalSemilinear.iInter (fun j : {j // a j = 0} =>
    IsRationalSemilinear.setOf_nonpos (g := g j.val) (hg j.val))
  have hp := IsRationalSemilinear.iInter (fun j : {j // 0 < a j} =>
    IsRationalSemilinear.setOf_neg (g := g j.val) (hg j.val))
  have hn := IsRationalSemilinear.iInter (fun j : {j // a j < 0} =>
    IsRationalSemilinear.setOf_neg (g := g j.val + a j.val • T)
      ((hg j.val).add (by
        obtain ⟨q, hq⟩ := ha j.val
        rw [hq]
        have qm : (((q : ℝ) • T).toAffineMap.linear) = (q : ℝ) • T.toAffineMap.linear :=
          AffineMap.smul_linear (q : ℝ) T.toAffineMap
        rw [qm]
        exact hT.rat_smul q)))
  have hpair := IsRationalSemilinear.iInter
    (fun jk : {j // a j < 0} × {j // 0 < a j} =>
      IsRationalSemilinear.setOf_nonpos
        (g := nonnegElimFamily g a (.inr jk))
        (rational_linear_nonnegElimFamily g hg a ha (.inr jk)))
  convert (((hs.inter hz).inter hp).inter hn).inter hpair using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
    ContinuousAffineMap.neg_apply, neg_lt_zero, ContinuousAffineMap.add_apply,
    ContinuousAffineMap.smul_apply, smul_eq_mul, nonnegElimFamily_pair_apply,
    Subtype.forall, Prod.forall]
  have he := exists_pos_lt_mul_le_iff (a := a) (b := fun j => -g j x) (T := T x)
  have he' : (∃ t : ℝ, 0 < t ∧ t < T x ∧ ∀ j, g j x + a j * t ≤ 0) ↔
      0 < T x ∧ (∀ j, a j = 0 → 0 ≤ -g j x) ∧
        (∀ j, 0 < a j → 0 < -g j x) ∧
        (∀ j, a j < 0 → a j * T x < -g j x) ∧
        (∀ j k, a j < 0 → 0 < a k → a j * -g k x ≤ a k * -g j x) := by
    refine (exists_congr fun t => and_congr_right fun _ => and_congr_right fun _ =>
      forall_congr' fun j => ?_).trans he
    constructor <;> intro hj <;> linarith
  rw [he']
  constructor
  · rintro ⟨ht, hz, hp, hn, hpair⟩
    exact ⟨⟨⟨⟨ht, fun j hj => by linarith [hz j hj]⟩,
      fun j hj => by linarith [hp j hj]⟩, fun j hj => by linarith [hn j hj]⟩,
      fun j hj k hk => by linarith [hpair j k hj hk]⟩
  · rintro ⟨⟨⟨⟨ht, hz⟩, hp⟩, hn⟩, hpair⟩
    exact ⟨ht, fun j hj => by linarith [hz j hj],
      fun j hj => by linarith [hp j hj], fun j hj => by linarith [hn j hj],
      fun j k hj hk => by linarith [hpair j hj k hk]⟩

end Elimination

/-- For a lattice direction `w` and affine starting point `X` and duration `T`
with rational linear parts, the parameters in `W` for which the open segment
`X x + (0, T x) • i w` meets `P` form a rational semilinear set. Tangencies, zero
directions, and singleton intersections are retained. -/
theorem IsRationalNormalPolyhedron.isRationalSemilinear_setOf_exists_pos_lt_add_smul_mem
    {N' : Type*} [AddCommGroup N'] {i' : N' →+ W}
    {h' : TauCeti.Toric.IsIntegralLattice i'} {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
    {P : Set V} (hP : IsRationalNormalPolyhedron h P) (w : N)
    (X : W →ᴬ[ℝ] V) (T : W →ᴬ[ℝ] ℝ)
    (hX : Toric.IsRationalLinearMap h' h X.toAffineMap.linear)
    (hT : Toric.IsRationalFunctional h' T.toAffineMap.linear) :
    IsRationalSemilinear h' {x | ∃ t : ℝ, 0 < t ∧ t < T x ∧ X x + t • i w ∈ P} := by
  obtain ⟨Q, rfl⟩ := isRationalNormalPolyhedron_iff.mp hP
  have happ (j) (x : W) (t : ℝ) : (Q.inequality j) (X x + t • i w) =
      (Q.inequality j) (X x) + (Q.inequality j).linear (i w) * t := by
    rw [add_comm (X x)]
    simpa [vadd_eq_add, mul_comm, add_comm] using
      (Q.inequality j).toAffineMap.map_vadd (X x) (t • i w)
  simp_rw [RationalAffinePolyhedron.mem_carrier, happ]
  exact isRationalSemilinear_setOf_exists_pos_lt_affine_le
    (fun j => (Q.inequality j).comp X) (fun j => (Q.inequality j).linear (i w)) T
    (fun j => hX.map_functional (Q.rational_linear j))
    (fun j => (Q.rational_linear j).exists_rat_apply w) hT

end TauCeti
