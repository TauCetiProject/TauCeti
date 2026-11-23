/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Basic
public import TauCeti.GroupTheory.GroupAlgGeom.Twist
public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Discrimination

/-!
# Twists of a point in an extension of a centralizer

Let `A` be an element of the free `G`-group `G[X]`, attach to every variable `x` a pair of
integers `(l, r) = e x`, and let `v : X → H` be a point. The substitution
`x ↦ A ^ (k * l) * x * A ^ (k * r)` (`TauCeti.GroupAlgGeom.twistHom (A ^ k) e`) composed with `v`
gives a one-parameter family of points of `H`. Following [IFT], §7.2, (84)–(85), the parameter
`k` is replaced by a new letter: in the extension `H(u, t)` of the centralizer of an element `u`
the point `twistLift u v e` takes the value `t ^ l * v x * t ^ r` at `x`. For `u = A(v)` the
retractions `t ↦ u ^ k` of `H(u, t)` map it back to the twisted points; more generally, the
retraction `t ↦ u ^ k` maps it to `v` composed with the substitution for any `B` with
`B(v) = u ^ k` (`retraction_comp_twistLift`, `retraction_comp_eval_twistLift`).

When `H` is a CSA group with the big powers property, `A(v) ≠ 1` and the substitution fixes `A`,
every element `w` of `G[X]` fixed by the substitution takes the same value at the lifted point as
at `v` (`eval_twistLift`), for every `u` commuting with `A(v)` (for instance a root of `A(v)`):
for `u = A(v)` the retractions `t ↦ u ^ k` with `k` large separate `H(u, t)` and send both values
to `w(v)`, and the general case follows along the map `H(A(v), t) → H(u, t)` fixing `H` and `t`.
In particular the lifted point of a solution of a system fixed by the substitution is again a
solution (`twistLift_mem_V`). This is one step of the construction, in [IFT], Proposition 4, of a
`G`-homomorphism from the coordinate group of a regular quadratic equation to an iterated
extension of centralizers.

## Main definitions

* `TauCeti.GroupAlgGeom.Lift.twistLift u v e`: the point `x ↦ t ^ l * v x * t ^ r` of the
  extension of the centralizer of `u`.

## Main results

* `TauCeti.GroupAlgGeom.Lift.retraction_comp_twistLift`: if `B(v) = u ^ k`, the retraction
  `t ↦ u ^ k` maps the lifted point to `v` composed with the substitution for `B`;
  `TauCeti.GroupAlgGeom.Lift.retraction_comp_eval_twistLift` is the same statement for the
  evaluation homomorphisms.
* `TauCeti.GroupAlgGeom.Lift.eval_twistLift`: elements fixed by the substitution take the same
  value at the lifted point as at `v`.
* `TauCeti.GroupAlgGeom.Lift.twistLift_mem_V`: lifting along a substitution fixing a system takes
  solutions to solutions.
* `TauCeti.GroupAlgGeom.Lift.twistLift_mem_V_oneCommutatorEquation`: for the equation
  `x⁻¹ y⁻¹ x y = a⁻¹ b⁻¹ a b` over the free group `F(a, b)`
  (`TauCeti.GroupAlgGeom.Quadratic.oneCommutatorEquation`) and the twist `y ↦ x y`, the solution
  `(a, b)` lifts to the solution `(a, t b)`.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.5 and §7.2, (84)–(88) and Proposition 4.
-/

public section

open Monoid.Coprod TauCeti.LimitGroup

namespace TauCeti.GroupAlgGeom.Lift

variable {G H X : Type*} [Group G] [Group H]

section TwistLift

variable (u : H) (v : X → H) (e : X → ℤ × ℤ)

/-- The point of the extension `H(u, t)` of the centralizer of `u` whose value at the variable `x`
is `t ^ l * v x * t ^ r`, where `(l, r) = e x`. For `u = A(v)` this is the lift of `v` along the
twist `x ↦ A ^ l * x * A ^ r`, the parameter of the powers of the twist being replaced by `t`. -/
def twistLift : X → CentralizerExt u 1 :=
  fun x => CentralizerExt.t 0 ^ (e x).1 * CentralizerExt.of (v x) * CentralizerExt.t 0 ^ (e x).2

@[simp]
theorem twistLift_apply (x : X) : twistLift u v e x =
    CentralizerExt.t 0 ^ (e x).1 * CentralizerExt.of (v x) * CentralizerExt.t 0 ^ (e x).2 := (rfl)

end TwistLift

section Retraction

variable {ι : G →* H} {v : X → H} {u : H} {B : GX G X}

/-- If `u ^ k = B(v)`, the retraction `t ↦ u ^ k` of the extension of the centralizer of `u` maps
the lifted point to the composite of `v` with the substitution `x ↦ B ^ l * x * B ^ r`. For
`u = A(v)` and `B = A ^ k` this is `v` composed with the substitution for `A ^ k`, the `k`-th power
of the twist by `A` when the substitutions for `A` and for `A⁻¹` fix `A` (`twist_zpow_apply`). -/
theorem retraction_comp_twistLift (e : X → ℤ × ℤ) (k : Fin 1 → ℤ) (hB : u ^ k 0 = eval ι v B) :
    ⇑(CentralizerExt.retraction k) ∘ twistLift u v e =
      wordMap ι (fun x => twistHom B e (inr (FreeGroup.of x))) v := by
  funext x
  simp [hB]

/-- If `u ^ k = B(v)`, the retraction `t ↦ u ^ k` composed with evaluation at the lifted point is
evaluation at `v` composed with the substitution `x ↦ B ^ l * x * B ^ r`. -/
theorem retraction_comp_eval_twistLift (e : X → ℤ × ℤ) (k : Fin 1 → ℤ)
    (hB : u ^ k 0 = eval ι v B) :
    (CentralizerExt.retraction k).comp (eval (CentralizerExt.of.comp ι) (twistLift u v e)) =
      (eval ι v).comp (twistHom B e) := by
  rw [MonoidHom.comp_eval, ← MonoidHom.comp_assoc, CentralizerExt.retraction_comp_of,
    MonoidHom.id_comp, retraction_comp_twistLift e k hB, twistHom_def, eval_comp_eval]
  simp

/-- If `u ^ k = B(v)`, the retraction `t ↦ u ^ k` of the value of `w` at the lifted point is the
value at `v` of the substitution for `B` applied to `w`. -/
theorem retraction_eval_twistLift (e : X → ℤ × ℤ) (k : Fin 1 → ℤ) (hB : u ^ k 0 = eval ι v B)
    (w : GX G X) :
    CentralizerExt.retraction k (eval (CentralizerExt.of.comp ι) (twistLift u v e) w) =
      eval ι v (twistHom B e w) :=
  DFunLike.congr_fun (retraction_comp_eval_twistLift e k hB) w

variable {A : GX G X} {e : X → ℤ × ℤ}

/-- The case `u = A(v)` of `eval_twistLift`. -/
private theorem eval_twistLift_self (hBP : Group.IsBP H) (hCSA : Group.IsCSA H)
    (hA : eval ι v A ≠ 1) (h₁ : twistHom A e A = A) {w : GX G X} (hw : twistHom A e w = w) :
    eval (CentralizerExt.of.comp ι) (twistLift (eval ι v A) v e) w =
      CentralizerExt.of (eval ι v w) := by
  -- Otherwise the quotient of the two sides would survive the retractions `t ↦ A(v) ^ n` for all
  -- large `n`, but each of them sends both sides to `w(v)`.
  by_contra hne
  obtain ⟨N, hN⟩ := CentralizerExt.exists_forall_retraction_ne_one hBP hCSA hA
    (mul_inv_eq_one.not.mpr hne)
  have hB : eval ι v A ^ (N : ℤ) = eval ι v (A ^ N) := by rw [zpow_natCast, map_pow]
  exact hN N le_rfl <| by
    simp [retraction_eval_twistLift e (fun _ => (N : ℤ)) hB,
      twistHom_pow_apply_eq_self_of_apply_eq_self h₁ hw]

/-- Let `H` be a CSA group with the big powers property, `A(v) ≠ 1`, and `u` an element commuting
with `A(v)`. An element of `G[X]` fixed by the twist by `A`, when the twist fixes `A`, has the same
value at the point lifted to the extension of the centralizer of `u` as at `v`. -/
theorem eval_twistLift (hBP : Group.IsBP H) (hCSA : Group.IsCSA H) (hA : eval ι v A ≠ 1)
    (hu : Commute (eval ι v A) u) (h₁ : twistHom A e A = A) {w : GX G X}
    (hw : twistHom A e w = w) :
    eval (CentralizerExt.of.comp ι) (twistLift u v e) w = CentralizerExt.of (eval ι v w) := by
  -- The centralizer of `A(v)` lies in that of `u`, so `H(A(v), t)` maps to `H(u, t)` over `H`
  -- with `t ↦ t`, and this map sends the point lifted to `H(A(v), t)` to the one lifted to
  -- `H(u, t)`.
  let φ : CentralizerExt (eval ι v A) 1 →* CentralizerExt u 1 :=
    CentralizerExt.lift CentralizerExt.of CentralizerExt.t CentralizerExt.commute_t_t
      fun c hc => CentralizerExt.commute_of_t <| Subgroup.mem_centralizer_singleton_iff.2
        ((Group.isCommTransitive_iff H).1 hCSA.isCommTransitive c _ u hA
          (Subgroup.mem_centralizer_singleton_iff.1 hc) hu).eq
  have h := congrArg φ (eval_twistLift_self hBP hCSA hA h₁ hw)
  rw [← MonoidHom.comp_apply, MonoidHom.comp_eval, ← MonoidHom.comp_assoc,
    show ⇑φ ∘ twistLift (eval ι v A) v e = twistLift u v e from funext fun x => by simp [φ]] at h
  simpa [φ] using h

/-- Let `H` be a CSA group with the big powers property, `v` a solution in `H` of a system `S`
with `A(v) ≠ 1`, and `u` an element commuting with `A(v)`. If the twist by `A` fixes `A` and
every equation of `S`, the point lifted to the extension of the centralizer of `u` is a solution
of `S`. -/
theorem twistLift_mem_V (hBP : Group.IsBP H) (hCSA : Group.IsCSA H) (hA : eval ι v A ≠ 1)
    (hu : Commute (eval ι v A) u) (h₁ : twistHom A e A = A) {S : Set (GX G X)}
    (hS : ∀ s ∈ S, twistHom A e s = s) (hv : v ∈ V ι S) :
    twistLift u v e ∈ V (CentralizerExt.of.comp ι) S :=
  mem_V.2 fun s hs => by
    rw [eval_twistLift hBP hCSA hA hu h₁ (hS s hs), mem_V.1 hv s hs, map_one]

end Retraction

/-! ### The one-commutator equation -/

/-- For the equation `x⁻¹ y⁻¹ x y = a⁻¹ b⁻¹ a b` over the free group `F(a, b)`, lifting the
solution `(a, b)` along the twist `y ↦ x y` gives the solution `(a, t b)` in the extension of the
centralizer of `a`. -/
theorem twistLift_mem_V_oneCommutatorEquation :
    twistLift (FreeGroup.of 0) ![.of 0, .of 1] (Pi.single 1 (1, 0)) ∈
      V CentralizerExt.of
        {Quadratic.oneCommutatorEquation (.of 0 : FreeGroup (Fin 2)) (.of 1)} := by
  rw [← MonoidHom.comp_id CentralizerExt.of]
  refine twistLift_mem_V (A := inr (.of 0)) FreeGroup.isBP IsFreeGroup.isCSA (by simp) (by simp)
    (by simp) ?_ ?_ <;>
    simp [mem_V, Quadratic.oneCommutatorEquation_def, commutatorElement_def, mul_assoc]

end TauCeti.GroupAlgGeom.Lift
