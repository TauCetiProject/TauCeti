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
set. Both its starting point and its duration may depend affinely on the endpoint,
with rational linear parts. Tangencies and singleton intersections are retained.

The proof eliminates the time variable using `exists_pos_lt_mul_le_iff`.
The strict interval bounds give strict resultant inequalities, while pairs of
weak support inequalities give weak resultants. Complements therefore describe
avoidance by the entire open segment, including segments parallel to a wall.

Adapted from `Mei/Geometry/Convex/Polyhedron/Rational/Segment.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public section

namespace TauCeti.Convex

variable {N V W : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- Eliminating a strictly bounded parameter with rational slopes preserves
rational semilinearity. Offsets and interval lengths may vary affinely. -/
theorem isRationalSemilinear_setOf_exists_pos_lt_affine_le {κ : Type*} [Finite κ]
    (g : κ → V →ᴬ[ℝ] ℝ) (a : κ → ℝ) (T : V →ᴬ[ℝ] ℝ)
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
          calc
            (((q : ℝ) • T).toAffineMap.linear) =
                (((q : ℝ) • T).contLinear : V →ₗ[ℝ] ℝ) :=
              (ContinuousAffineMap.coe_contLinear_eq_linear _).symm
            _ = (((q : ℝ) • T.contLinear : V →L[ℝ] ℝ) : V →ₗ[ℝ] ℝ) :=
              congrArg ContinuousLinearMap.toLinearMap (ContinuousAffineMap.smul_contLinear _ T)
            _ = (q : ℝ) • (T.contLinear : V →ₗ[ℝ] ℝ) :=
              ContinuousLinearMap.toLinearMap_smul _ _
            _ = (q : ℝ) • T.toAffineMap.linear :=
              congrArg ((q : ℝ) • ·) (ContinuousAffineMap.coe_contLinear_eq_linear T)
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

/-- The open part of a finite segment meets a rational-normal polyhedron on a
semilinear endpoint domain. The direction may be tangent or zero. -/
theorem isRationalSemilinear_setOf_exists_pos_lt_add_smul_mem
    {N' : Type*} [AddCommGroup N'] {i' : N' →+ W}
    {h' : TauCeti.Toric.IsIntegralLattice i'}
    {P : Set V} (hP : IsRationalNormalPolyhedron h P) (w : N)
    (X : W →ᴬ[ℝ] V) (T : W →ᴬ[ℝ] ℝ)
    (hX : Toric.IsRationalLinearMap h' h X.toAffineMap.linear)
    (hT : Toric.IsRationalFunctional h' T.toAffineMap.linear) :
    IsRationalSemilinear h' {x | ∃ t : ℝ, 0 < t ∧ t < T x ∧ X x + t • i w ∈ P} := by
  obtain ⟨Q, rfl⟩ := isRationalNormalPolyhedron_iff.mp hP
  have happ (j) (x : W) (t : ℝ) : (Q.inequality j) (X x + t • i w) =
      (Q.inequality j) (X x) + (Q.inequality j).linear (i w) * t := by
    have hc (z : V) : (Q.inequality j).contLinear z = (Q.inequality j).linear z :=
      LinearMap.congr_fun (ContinuousAffineMap.coe_contLinear_eq_linear (Q.inequality j)) z
    calc
      (Q.inequality j) (X x + t • i w) = (Q.inequality j).contLinear (t • i w) +
          (Q.inequality j) (X x) := by
        simpa only [vadd_eq_add, add_comm] using
          (Q.inequality j).map_vadd (X x) (t • i w)
      _ = (Q.inequality j) (X x) + (Q.inequality j).linear (i w) * t := by
        rw [map_smul, hc (i w)]
        simp only [smul_eq_mul, add_comm, mul_comm]
  simp_rw [RationalAffinePolyhedron.mem_carrier, happ]
  exact isRationalSemilinear_setOf_exists_pos_lt_affine_le
    (fun j => (Q.inequality j).comp X) (fun j => (Q.inequality j).linear (i w)) T
    (fun j => hX.map_functional (Q.rational_linear j))
    (fun j => (Q.rational_linear j).exists_rat_apply w) hT

end TauCeti.Convex
