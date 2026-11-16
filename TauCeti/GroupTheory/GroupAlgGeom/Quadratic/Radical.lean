/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Basic
import TauCeti.GroupTheory.FreeGroup.Centralizer

/-!
# Radicals of standard quadratic equations: the equation `x² d = 1`

Let `S = 1` be a standard quadratic equation over a group `G` which has a solution in `G`. Its
radical `R(S)` is in general larger than the normal closure of `S`, and [IFT] lists the radicals
of the equations of small atomic rank over a freely discriminated group. This file treats the
one-variable equation `x² d = 1`.

If `x ↦ s` is a solution in `G`, then `d = b²` with `b = s⁻¹`, and the equation reads
`x² = (b⁻¹)²`. A freely discriminated group has unique roots, so the equation has the same
solutions as `x b = 1`, and the group `⟨G, x | x b = 1⟩` is `G` itself. Hence `R(S)` is the
normal closure of `x b` in `G[x]`. It is strictly larger than the normal closure of `S`, since
`x b` does not lie in the latter. If the equation has no solution in `G`, its radical is the
whole group `G[x]`, so over a group with unique roots the radical of `x² d = 1` is never the
normal closure of the equation.

The only property of the group in which the solutions are taken that the argument uses is
uniqueness of roots (`HasUniqueRoots`), which holds in residually free groups and in torsion-free
commutative-transitive groups. The descriptions of the radical are in one variable, as in the
source: with further variables `Y` in the ambient alphabet, the same description of the radical
is equivalent to `G[Y]` being separated by `G`.

## Main results

* `TauCeti.GroupAlgGeom.Quadratic.Standard.Rad_toWord_nonorientableCoeff_one_zero`: if `b² = d`,
  the radical of `x² d` is the normal closure of `x b`.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.exists_sq_eq_and_Rad_toWord_nonorientableCoeff_one_zero`:
  if `x² d = 1` has a solution in `G`, then `d = b²` for some `b` and the radical is the normal
  closure of `x b`.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.normalClosure_toWord_nonorientableCoeff_one_zero_ne_Rad`:
  over a group with unique roots, the radical of `x² d = 1` is not the normal closure of the
  equation.
* `TauCeti.GroupAlgGeom.Quadratic.rad_sq_mul_sq`: over `F(a, b)`, the radical of `x² a²` is the
  normal closure of `x a`.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.7, Theorem 2 (2).
* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §3, Form 3.
-/

public section

open Monoid.Coprod Subgroup

namespace TauCeti.GroupAlgGeom.Quadratic

variable {G H X : Type*} [Group G] [Group H]

namespace Standard

variable {x : Fin 1 → X} {z : Fin 0 → X} {inj : (Sum.elim x z).Injective} {c : Fin 0 → G}
  {hc : ∀ j, c j ≠ 1} {d : G} {hd : d ≠ 1}

/-- Over a group `H` with unique roots and injective coefficients, the radical of the
one-variable standard quadratic equation `x² d = 1` with `d = b²` is the normal closure of
`x b`. -/
theorem Rad_toWord_nonorientableCoeff_one_zero [Subsingleton X] [HasUniqueRoots H] {ι : G →* H}
    (hι : Function.Injective ι) {b : G} (hb : b ^ 2 = d) :
    Rad ι {(nonorientableCoeff 1 0 one_pos x z inj c hc d hd).toWord} =
      normalClosure {inr (FreeGroup.of (x 0)) * inl b} := by
  subst hb
  rw [toWord_nonorientableCoeff_one_zero, Rad_pow_mul_inl_pow_eq_normalClosure hι two_ne_zero]

/-- If the one-variable standard quadratic equation `x² d = 1` over a group `G` with unique roots
has a solution in `G`, then `d = b²` for some `b ∈ G`, and the radical of the equation is the
normal closure of `x b`. -/
theorem exists_sq_eq_and_Rad_toWord_nonorientableCoeff_one_zero [Subsingleton X] [HasUniqueRoots G]
    (hS : (V (.id G) {(nonorientableCoeff 1 0 one_pos x z inj c hc d hd).toWord}).Nonempty) :
    ∃ b : G, b ^ 2 = d ∧
      Rad (.id G) {(nonorientableCoeff 1 0 one_pos x z inj c hc d hd).toWord} =
        normalClosure {inr (FreeGroup.of (x 0)) * inl b} := by
  obtain ⟨v, hv⟩ := hS
  have hv : v (x 0) ^ 2 * d = 1 := by
    simpa [eval_inr_of] using hv
  have hb : (v (x 0))⁻¹ ^ 2 = d := by rw [inv_pow, inv_eq_of_mul_eq_one_right hv]
  exact ⟨_, hb, Rad_toWord_nonorientableCoeff_one_zero Function.injective_id hb⟩

/-- Over a group `G` with unique roots, the radical of the standard quadratic equation `x² d = 1`
is not the normal closure of the equation. -/
theorem normalClosure_toWord_nonorientableCoeff_one_zero_ne_Rad [HasUniqueRoots G] :
    normalClosure {(nonorientableCoeff 1 0 one_pos x z inj c hc d hd).toWord} ≠
      Rad (.id G) {(nonorientableCoeff 1 0 one_pos x z inj c hc d hd).toWord} := by
  rw [toWord_nonorientableCoeff_one_zero]
  -- Some `x b` lies in the radical: any `b` if there is no solution, `b = s⁻¹` for a solution `s`.
  obtain ⟨b, hb⟩ : ∃ b : G,
      inr (FreeGroup.of (x 0)) * inl b ∈ Rad (.id G) {inr (FreeGroup.of (x 0)) ^ 2 * inl d} := by
    rcases (V (.id G) {(inr (FreeGroup.of (x 0)) : GX G X) ^ 2 * inl d}).eq_empty_or_nonempty
      with hV | ⟨v, hv⟩
    · exact ⟨1, by simp [mem_Rad, hV]⟩
    have hv : v (x 0) ^ 2 * d = 1 := by simpa [eval_inr_of] using hv
    refine ⟨(v (x 0))⁻¹, ?_⟩
    rw [← inv_eq_of_mul_eq_one_right hv, ← inv_pow, Rad_pow_mul_inl_pow two_ne_zero]
    exact normalClosure_le_Rad _ (subset_normalClosure rfl)
  intro h
  exact inr_of_mul_inl_notMem_normalClosure_pow_mul_inl (n := 2) (by decide) (x 0) b d (h ▸ hb)

end Standard

/-! ### Examples -/

section Examples

open FreeGroup

/-- Over `G = F(a, b)` with one variable `x`, the radical of `x² a²` is the normal closure of
`x a`. -/
theorem rad_sq_mul_sq :
    Rad (.id (FreeGroup (Fin 2)))
        {(inr (of ()) : GX (FreeGroup (Fin 2)) Unit) ^ 2 * inl (of 0 ^ 2)} =
      normalClosure {inr (of ()) * inl (of 0)} :=
  Rad_pow_mul_inl_pow_eq_normalClosure Function.injective_id two_ne_zero () (of 0)

end Examples

end TauCeti.GroupAlgGeom.Quadratic
