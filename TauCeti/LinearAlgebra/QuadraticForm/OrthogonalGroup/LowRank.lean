/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

/-!
# Orthogonal groups in dimension one

On a free module of rank one over an integral domain every linear endomorphism is a scalar `c`,
and `c` preserves a nonzero quadratic map valued in a torsion-free module exactly when
`c * c = 1`, that is when `c = 1` or `c = -1`. So the orthogonal group of such a quadratic map on
a line is `{1, -1}`, of order two when `2 ≠ 0`. Over any commutative ring, the reflection in any
vector of invertible norm on a free module of rank one is `-1`.

Together with the triviality of the special orthogonal group in rank at most one
(`QuadraticMap.specialOrthogonalGroup_eq_bot_of_finrank_le_one`), this is the dimension-one
boundary case of the orthogonal-group calculations: for `Q x = a x²` with `a ≠ 0` over a field,
the group `O(Q)` is `{±1}`, `SO(Q)` is trivial, and `-1` is the reflection in every nonzero vector.
The last fact is what computes the spinor norm of `-1` as the square class of `a`
(`CliffordAlgebra.orthogonalSpinorNorm_negOrthogonal_smul_sq`).

## Main results

* `TauCeti.QuadraticMap.mem_orthogonalGroup_iff_of_finrank_eq_one`: in rank one, the isometries of
  a nonzero quadratic map valued in a torsion-free module are exactly `1` and `-1`.
* `TauCeti.QuadraticMap.eq_one_or_eq_negOrthogonal_of_finrank_eq_one`: the same dichotomy for
  elements of the orthogonal group.
* `TauCeti.QuadraticMap.card_orthogonalGroup_of_finrank_eq_one`: if moreover `2 ≠ 0`, the
  orthogonal group has exactly two elements.
* `QuadraticMap.reflection_eq_neg_of_finrank_eq_one` and
  `QuadraticMap.reflectionOrthogonal_eq_negOrthogonal_of_finrank_eq_one`: in rank one, the
  reflection in any vector of invertible norm is `-1`.
-/

public section

namespace TauCeti.QuadraticMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Free R M] [AddCommGroup N] [Module R N]

section Domain

variable [IsDomain R]

/-- **The orthogonal group of a line.** On a free module of rank one over a domain, the isometries
of a nonzero quadratic map valued in a torsion-free module are exactly `1` and `-1`. -/
theorem mem_orthogonalGroup_iff_of_finrank_eq_one [Module.IsTorsionFree R N]
    {Q : QuadraticMap R M N} (hQ : Q ≠ 0) (hM : Module.finrank R M = 1) {f : M ≃ₗ[R] M} :
    f ∈ orthogonalGroup Q ↔ f = 1 ∨ f = LinearEquiv.neg R := by
  refine ⟨fun hf ↦ ?_, ?_⟩
  · obtain ⟨c, hc⟩ :=
      (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hM f.toLinearMap).exists
    replace hc (m : M) : f m = c • m := by simpa using LinearMap.congr_fun hc m
    obtain ⟨m, hm⟩ : ∃ m, Q m ≠ 0 := by
      by_contra! h
      exact hQ (QuadraticMap.ext h)
    -- Evaluating `Q (f m) = Q m` at a vector of nonzero value forces `c * c = 1`.
    have hcc : c * c = 1 := by
      have h : (c * c - 1) • Q m = 0 := by
        rw [sub_smul, one_smul, ← QuadraticMap.map_smul, ← hc, map_app_of_mem_orthogonalGroup hf,
          sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero_iff_left hm).mp h)
    rcases mul_self_eq_one_iff.mp hcc with rfl | rfl
    · exact .inl (LinearEquiv.ext fun m ↦ by simp [hc])
    · exact .inr (LinearEquiv.ext fun m ↦ by simp [hc])
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Q.neg_mem_orthogonalGroup

/-- In rank one, every isometry of a nonzero quadratic map is `1` or `Q.negOrthogonal`. -/
theorem eq_one_or_eq_negOrthogonal_of_finrank_eq_one [Module.IsTorsionFree R N]
    {Q : QuadraticMap R M N} (hQ : Q ≠ 0) (hM : Module.finrank R M = 1) (g : orthogonalGroup Q) :
    g = 1 ∨ g = Q.negOrthogonal :=
  ((mem_orthogonalGroup_iff_of_finrank_eq_one hQ hM).mp g.2).imp
    (fun h ↦ Subtype.ext (by simpa using h)) (fun h ↦ Subtype.ext (by simpa using h))

/-- **The orthogonal group of a line has order two.** On a free module of rank one over a domain
in which `2 ≠ 0`, a nonzero quadratic map valued in a torsion-free module has exactly the two
isometries `1` and `-1`. -/
theorem card_orthogonalGroup_of_finrank_eq_one [NeZero (2 : R)] [Module.IsTorsionFree R N]
    {Q : QuadraticMap R M N} (hQ : Q ≠ 0) (hM : Module.finrank R M = 1) :
    Nat.card (orthogonalGroup Q) = 2 := by
  have : Nontrivial M := Module.nontrivial_of_finrank_eq_succ hM
  refine Nat.card_eq_two_iff.mpr ⟨1, Q.negOrthogonal,
    Q.negOrthogonal_ne_one.symm, Set.eq_univ_of_forall fun g ↦ ?_⟩
  rcases eq_one_or_eq_negOrthogonal_of_finrank_eq_one hQ hM g with rfl | rfl <;> simp

end Domain

section Reflection

variable (Q : QuadraticForm R M) (v : M) [Invertible (Q v)]

/-- **In rank one, every reflection is `-1`.** The reflection in a vector of invertible norm on a
free module of rank one over a commutative ring is negation. -/
theorem _root_.QuadraticMap.reflection_eq_neg_of_finrank_eq_one (hM : Module.finrank R M = 1) :
    reflection Q v = LinearEquiv.neg R := by
  nontriviality R
  let e := (Module.nonempty_linearEquiv_of_finrank_eq_one hM).some
  -- Invertibility of the norm makes the coordinate of `v` a unit, even with zero divisors.
  have he (m : M) : e.symm m • e 1 = m := by simp [← e.map_smul]
  have hv : IsUnit (e.symm v) := by
    have hQv := isUnit_of_invertible (Q v)
    rw [← he v, Q.map_smul, smul_eq_mul] at hQv
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hQv)
  have h : reflection Q v (e 1) = -(e 1) := hv.isSMulRegular M <| by
    simp [← map_smul, he]
  exact LinearEquiv.ext fun m ↦ by
    simpa only [← map_smul, he, smul_neg, LinearEquiv.neg_apply] using
      congrArg (fun x ↦ e.symm m • x) h

/-- In rank one, the bundled reflection in a vector of invertible norm is `Q.negOrthogonal`. -/
theorem _root_.QuadraticMap.reflectionOrthogonal_eq_negOrthogonal_of_finrank_eq_one
    (hM : Module.finrank R M = 1) :
    reflectionOrthogonal Q v = Q.negOrthogonal :=
  Subtype.ext <| by
    rw [coe_reflectionOrthogonal, QuadraticMap.coe_negOrthogonal,
      Q.reflection_eq_neg_of_finrank_eq_one v hM]

end Reflection

end TauCeti.QuadraticMap
