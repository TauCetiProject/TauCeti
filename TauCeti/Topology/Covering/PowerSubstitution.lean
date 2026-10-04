/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.PuncturedStarConvex
public import TauCeti.Topology.Homotopy.Monodromy.Basic

import Mathlib.Analysis.LocallyConvex.WithSeminorms
import TauCeti.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Lifting a power substitution through a finite covering of a punctured disc

Let `U` be a simply connected, locally path connected space, for instance a polydisc, which is
open and convex. Let `D* = ball 0 R \ {0}` be a punctured disc in `ℂ`, and let `p : E → U × D*` be
a covering map whose fibre over a point has `d` points. Going around the puncture permutes that
fibre, and the permutation has order dividing `d !`. The substitution `t = s ^ n` with `d ! ∣ n`
unwinds it. If `D'* = ball 0 R' \ {0}` with `R' ^ n ≤ R`, the map `(w, s) ↦ (w, s ^ n)` from
`U × D'*` to `U × D*` lifts through `p`, uniquely once the value at one point is fixed. The `d`
points of the fibre therefore extend to `d` lifts that are distinct at every point.

The proof applies the lifting criterion
`IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`. A loop class of `U × D*` is
determined by the degree of the direction of its second coordinate
(`TauCeti.fundamentalGroupMulEquiv_comp_map_directionFrom_comp_snd_bijective`). The substitution
multiplies that degree by `n` (`Circle.fundamentalGroupMulEquiv_map_pow`), so it sends every loop
class of `U × D'*` to an `n`-th power. Over a fibre with `d` points, the `n`-th power of every loop
class has trivial monodromy (`IsCoveringMap.monodromyPerm_pow_eq_one`), so it lifts to a loop.

This is the topological step of the Puiseux theorem with parameters. Let a monic polynomial in `z`
have analytic coefficients on `U × D` and a discriminant that vanishes only on `U × {0}`. Over
`U × D*` its roots form a covering with `d` sheets, `d` the degree. After the substitution
`t = s ^ n` with `n = d !`, the lifts of the base point are `d` single-valued root functions.

## Main definitions and results

* `TauCeti.powerSubstitution`: the map `(w, s) ↦ (w, s ^ n)` from `U × (ball 0 R' \ {0})` to
  `U × (ball 0 R \ {0})`.
* `IsCoveringMap.existsUnique_continuousMap_lifts_powerSubstitution`: if the fibre over the image
  of `a` has `d` points and `d !` divides `n`, the power substitution has a unique lift through
  the covering map taking a prescribed value at `a`.
* `IsCoveringMap.exists_continuousMap_lifts_powerSubstitution`: the points of that fibre extend to
  lifts of the power substitution which are pairwise distinct at every point.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 1.33 (the
  lifting criterion) and Proposition 1.34 (uniqueness of lifts).
* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 4 (the Puiseux
  theorem with parameters).
-/

public section

noncomputable section

open Function Metric Set

namespace TauCeti

variable (U : Type*) [TopologicalSpace U] {E : Type*} [TopologicalSpace E] {n : ℕ} {R R' : ℝ}

/-- The `n`-th power maps the punctured ball of radius `R'` into that of radius `R` when
`R' ^ n ≤ R`. -/
private theorem pow_mem_ball_zero_diff_singleton (hn : n ≠ 0) (hR : R' ^ n ≤ R) {t : ℂ}
    (ht : t ∈ ball (0 : ℂ) R' \ {0}) : t ^ n ∈ ball (0 : ℂ) R \ {0} := by
  refine ⟨?_, pow_ne_zero n ht.2⟩
  rw [mem_ball_zero_iff, norm_pow]
  exact (pow_lt_pow_left₀ (mem_ball_zero_iff.1 ht.1) (norm_nonneg _) hn).trans_le hR

/-- The **power substitution** `(w, s) ↦ (w, s ^ n)` from `U × (ball 0 R' \ {0})` to
`U × (ball 0 R \ {0})`, for `n ≠ 0` and `R' ^ n ≤ R`. -/
def powerSubstitution (hn : n ≠ 0) (hR : R' ^ n ≤ R) :
    C(U × ↥(ball (0 : ℂ) R' \ {0}), U × ↥(ball (0 : ℂ) R \ {0})) :=
  (ContinuousMap.id U).prodMap
    ⟨fun s => ⟨(s : ℂ) ^ n, pow_mem_ball_zero_diff_singleton hn hR s.2⟩,
      Continuous.subtype_mk (by fun_prop) _⟩

@[simp]
theorem powerSubstitution_apply_fst (hn : n ≠ 0) (hR : R' ^ n ≤ R)
    (a : U × ↥(ball (0 : ℂ) R' \ {0})) : (powerSubstitution U hn hR a).1 = a.1 :=
  (rfl)

@[simp]
theorem coe_powerSubstitution_apply_snd (hn : n ≠ 0) (hR : R' ^ n ≤ R)
    (a : U × ↥(ball (0 : ℂ) R' \ {0})) :
    ((powerSubstitution U hn hR a).2 : ℂ) = (a.2 : ℂ) ^ n :=
  (rfl)

variable {U}

/-- The direction of the second coordinate of the power substitution is the `n`-th power of the
direction of the second coordinate. -/
private theorem directionFrom_comp_snd_comp_powerSubstitution (hn : n ≠ 0) (hR : R' ^ n ≤ R) :
    (((0 : ℂ).directionFrom (ball 0 R)).comp ContinuousMap.snd).comp
        (powerSubstitution U hn hR) =
      (⟨(· ^ n), continuous_pow n⟩ : C(Circle, Circle)).comp
        (((0 : ℂ).directionFrom (ball 0 R')).comp ContinuousMap.snd) := by
  ext a
  simp [div_pow]

/-- **Lifting the power substitution.** Let `p : E → U × (ball 0 R \ {0})` be a covering map, with
`U` simply connected and locally path connected. If the fibre over the image of `a` under the power
substitution `(w, s) ↦ (w, s ^ n)` is finite with `d` points, and `d !` divides `n`, then the power
substitution has a unique continuous lift through `p` taking any prescribed value `e` of that fibre
at `a`. -/
theorem _root_.IsCoveringMap.existsUnique_continuousMap_lifts_powerSubstitution
    [SimplyConnectedSpace U] [LocallyPathConnectedSpace U]
    {p : E → U × ↥(ball (0 : ℂ) R \ {0})} (hp : IsCoveringMap p) (hn : n ≠ 0) (hR : R' ^ n ≤ R)
    {a : U × ↥(ball (0 : ℂ) R' \ {0})} [Finite (p ⁻¹' {powerSubstitution U hn hR a})]
    (hdvd : (Nat.card (p ⁻¹' {powerSubstitution U hn hR a})).factorial ∣ n) {e : E}
    (he : p e = powerSubstitution U hn hR a) :
    ∃! F : C(U × ↥(ball (0 : ℂ) R' \ {0}), E), F a = e ∧ p ∘ F = powerSubstitution U hn hR := by
  set q := powerSubstitution U hn hR
  have hR' : 0 < R' := (norm_nonneg _).trans_lt (mem_ball_zero_iff.1 a.2.2.1)
  have := pathConnectedSpace_ball_diff_singleton 0 hR'
  have : LocallyPathConnectedSpace ↥(ball (0 : ℂ) R' \ {0}) :=
    (isOpen_ball.sdiff isClosed_singleton).locallyPathConnectedSpace
  refine hp.existsUnique_continuousMap_lifts_of_range_le he ?_
  rintro _ ⟨g, rfl⟩
  -- The degree of the direction of the second coordinate identifies `π₁(U × (ball 0 R \ {0}))`
  -- with `ℤ`, and the power substitution multiplies it by `n`.
  let dA := ((0 : ℂ).directionFrom (ball 0 R')).comp
    (ContinuousMap.snd : C(U × ↥(ball (0 : ℂ) R' \ {0}), _))
  let dX := ((0 : ℂ).directionFrom (ball 0 R)).comp
    (ContinuousMap.snd : C(U × ↥(ball (0 : ℂ) R \ {0}), _))
  let W := (Circle.fundamentalGroupMulEquiv _).toMonoidHom.comp (FundamentalGroup.map dX (q a))
  have hW : Bijective W := fundamentalGroupMulEquiv_comp_map_directionFrom_comp_snd_bijective (q a)
  let pow : C(Circle, Circle) := ⟨(· ^ n), continuous_pow n⟩
  have hd : dX.comp q = pow.comp dA := directionFrom_comp_snd_comp_powerSubstitution hn hR
  have hWq : W (FundamentalGroup.map q a g) =
      Circle.fundamentalGroupMulEquiv _ (FundamentalGroup.map dA a g) ^ n := by
    have h₁ : W (FundamentalGroup.map q a g) =
        Circle.fundamentalGroupMulEquiv _ (FundamentalGroup.map (dX.comp q) a g) :=
      congrArg (Circle.fundamentalGroupMulEquiv _) (FundamentalGroupoid.map_comp_map dX q g).symm
    -- rewriting `dX.comp q` also changes the base point of the circle, so it is done on a
    -- statement whose base point is that of `FundamentalGroup.map (dX.comp q) a`
    have h₂ : Circle.fundamentalGroupMulEquiv _ (FundamentalGroup.map (dX.comp q) a g) =
        Circle.fundamentalGroupMulEquiv _ (FundamentalGroup.map (pow.comp dA) a g) := by
      rw [hd]
    rw [h₁, h₂]
    exact (congrArg _ (FundamentalGroupoid.map_comp_map pow dA g)).trans
      (Circle.fundamentalGroupMulEquiv_map_pow n _)
  -- So the image of `g` is an `n`-th power, which has trivial monodromy.
  obtain ⟨h, hh⟩ := hW.2 (Circle.fundamentalGroupMulEquiv _ (FundamentalGroup.map dA a g))
  have hgh : W (FundamentalGroup.map q a g) = W (h ^ n) := by rw [hWq, map_pow, hh]
  rw [hW.1 hgh]
  refine (hp.monodromy_eq_self_iff_mem_range ⟨e, he⟩ (h ^ n)).1 ?_
  rw [← IsCoveringMap.coe_monodromyPerm, hp.monodromyPerm_pow_eq_one hdvd h]
  exact Equiv.Perm.one_apply _

/-- **The points of a fibre extend to pointwise distinct lifts of the power substitution.** Under
the hypotheses of `IsCoveringMap.existsUnique_continuousMap_lifts_powerSubstitution`, each point
`e` of the fibre over the image of `a` is the value at `a` of a lift `F e` of the power
substitution, and at every point `b` the values `F e b` are pairwise distinct. -/
theorem _root_.IsCoveringMap.exists_continuousMap_lifts_powerSubstitution
    [SimplyConnectedSpace U] [LocallyPathConnectedSpace U]
    {p : E → U × ↥(ball (0 : ℂ) R \ {0})} (hp : IsCoveringMap p) (hn : n ≠ 0) (hR : R' ^ n ≤ R)
    (a : U × ↥(ball (0 : ℂ) R' \ {0})) [Finite (p ⁻¹' {powerSubstitution U hn hR a})]
    (hdvd : (Nat.card (p ⁻¹' {powerSubstitution U hn hR a})).factorial ∣ n) :
    ∃ F : p ⁻¹' {powerSubstitution U hn hR a} → C(U × ↥(ball (0 : ℂ) R' \ {0}), E),
      (∀ e, F e a = e ∧ p ∘ F e = powerSubstitution U hn hR) ∧ ∀ b, Injective fun e ↦ F e b := by
  choose F hF using fun e : p ⁻¹' {powerSubstitution U hn hR a} ↦
    (hp.existsUnique_continuousMap_lifts_powerSubstitution hn hR hdvd e.2).exists
  refine ⟨F, hF, fun b e e' h ↦ Subtype.ext ?_⟩
  have hR' : 0 < R' := (norm_nonneg _).trans_lt (mem_ball_zero_iff.1 a.2.2.1)
  have := pathConnectedSpace_ball_diff_singleton 0 hR'
  -- two lifts agreeing at `b` agree everywhere, in particular at `a`
  rw [← (hF e).1, ← (hF e').1,
    hp.eq_of_comp_eq (F e).continuous (F e').continuous ((hF e).2.trans (hF e').2.symm) b h]

end TauCeti
