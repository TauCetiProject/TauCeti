/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.LocalCondition
import Mathlib.Analysis.Real.Sqrt
import Mathlib.FieldTheory.IsRealClosed.Real
import TauCeti.Algebra.Group.PowMonoidHom
import TauCeti.Analysis.Complex.Polynomial.RealQuadratic
import TauCeti.RingTheory.AdjoinRoot.Factors
import TauCeti.RingTheory.Polynomial.Resultant.AdjoinRoot

/-!
# The local condition of explicit `2`-descent at a real place

Let `W : y² = f(x) = x³ + a₂x² + a₄x + a₆` be an elliptic curve in characteristic `≠ 2` normal
form, with étale algebra `W.A = K[X]⧸(f)`, square classes `W.M` and descent map
`μ : W(K) → W.M`, as in `TauCeti/AlgebraicGeometry/EllipticCurve/MordellWeil/XSubT.lean`.

At a root `e ∈ K` of `f`, evaluation `T ↦ e` induces a homomorphism
`W.evalM he : W.M → Kˣ/(Kˣ)²`. On the image of `μ` it is computed by
`evalM_μX_of_ne`, `μX x ↦ x - e` for `x ≠ e`, and `evalM_μX_self`, `μX e ↦ f'(e)`.

Over `ℝ` these values determine everything. A square class is trivial exactly when its value at
every real root of `f` is (`eq_one_iff_forall_evalM_eq_one_real`): by the Chinese remainder theorem
(`AdjoinRoot.modPow_mk_eq_one_iff_forall_factors`) `ℝ[X]⧸(f)` is `ℝ³` when `f` has three real
roots, and `ℝ × ℂ` when it has one, and every complex number is a square. The image of `μ` is
then cut out by the norm condition and the sign at the **smallest** real root `e` of `f`
(`mem_range_μ_iff_real`). Indeed `f < 0` to the left of `e`, so
every real point has `x ≥ e`, and `μ` takes the value `x - e > 0` there, or `f'(e) > 0` at
`x = e`. Conversely, if `f` has three real roots `e < e₂ < e₃`, a class with square norm and
positive at `e` has the same sign at `e₂` and `e₃`. If both signs are positive the class is
trivial. If both are negative it is `μ(e, 0)`, the class of the point on the bounded component of
`W(ℝ)`.

This is the archimedean local condition of explicit `2`-descent
(`mem_localCondition_real_iff`): a global class satisfies it at a real embedding exactly when its
image there has square norm and is positive at the smallest real root of the cubic.

## Main definitions

* `WeierstrassCurve.Affine.evalA`: evaluation `W.A → K` at a root of `f`.
* `WeierstrassCurve.Affine.evalM`: the value of a square class of `W.A` at a root of `f`.

## Main results

* `WeierstrassCurve.Affine.evalM_μX_of_ne`, `WeierstrassCurve.Affine.evalM_μX_self`: the values of
  the descent map at a root of `f`, over any field.
* `WeierstrassCurve.Affine.eq_one_iff_forall_evalM_eq_one_real`: over `ℝ`, a square class is trivial
  exactly when it is trivial at every real root of `f`.
* `WeierstrassCurve.Affine.evalM_μ₀_eq_one_real`: over `ℝ`, every value of `μ` is positive at the
  smallest real root of `f`.
* `WeierstrassCurve.Affine.mem_range_μ_iff_real`: over `ℝ`, the image of `μ` is the set of classes
  with square norm that are positive at the smallest real root of `f`.
* `WeierstrassCurve.Affine.mem_localCondition_real_iff`: the local condition of `2`-descent at a
  real embedding.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.1.
-/

public section

open Polynomial

namespace WeierstrassCurve

namespace Affine

section Field

variable {K : Type*} [Field K] (W : Affine K)

/-- **Evaluation at a root of `f`**: the ring homomorphism `W.A → K` sending `T` to a root `e` of
`f`. It is `AdjoinRoot.lift` at `e`, with the root hypothesis in the `Polynomial.eval` spelling
that the descent constructions use. -/
noncomputable def evalA {e : K} (he : W.f.eval e = 0) : W.A →+* K :=
  AdjoinRoot.lift (RingHom.id K) e he

/-- The value at `e` of the class of `p` is `p.eval e`. This is the characteristic lemma for
`evalA`, and the `simp` normal form. -/
@[simp]
lemma evalA_mk {e : K} (he : W.f.eval e = 0) (p : K[X]) :
    W.evalA he (AdjoinRoot.mk W.f p) = p.eval e :=
  AdjoinRoot.lift_mk he p

/-- Evaluation at a root of `f` fixes the constants. -/
@[simp]
lemma evalA_of {e : K} (he : W.f.eval e = 0) (x : K) : W.evalA he (AdjoinRoot.of W.f x) = x :=
  AdjoinRoot.lift_of he

/-- Evaluation at a root `e` of `f` sends the generator `T` to `e`. -/
@[simp]
lemma evalA_root {e : K} (he : W.f.eval e = 0) : W.evalA he (AdjoinRoot.root W.f) = e :=
  AdjoinRoot.lift_root he

/-- **The value of a square class at a root of `f`.** For a root `e ∈ K` of `f`, evaluation
`W.A → K`, `T ↦ e`, carries squares to squares, so it induces a homomorphism from the square
classes of `W.A` to those of `K`. -/
noncomputable def evalM {e : K} (he : W.f.eval e = 0) :
    W.M →* Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range :=
  QuotientGroup.map _ _ (Units.map (W.evalA he : W.A →* K)) <| by
    rintro _ ⟨v, rfl⟩
    refine ⟨Units.map (W.evalA he : W.A →* K) v, ?_⟩
    simp only [powMonoidHom_apply]
    exact (map_pow _ _ _).symm

/-- The value at a root `e` of `f` of the class of a unit `u` of `W.A` is the class of the value
of `u` at `e`. This is the characteristic lemma for `evalM`, and the `simp` normal form. -/
@[simp]
lemma evalM_mk {e : K} (he : W.f.eval e = 0) (u : W.Aˣ) :
    W.evalM he u = (Units.map (W.evalA he : W.A →* K) u :
      Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) :=
  (rfl)

/-- A root `t ≠ e` of `f` is a root of the cofactor `fCofactor e`, since
`f = fCofactor e · (X - e)`. -/
private lemma isRoot_fCofactor_of_ne {e t : K} (he : W.f.eval e = 0) (ht : W.f.eval t = 0)
    (hte : t ≠ e) : (W.fCofactor e).IsRoot t := by
  rw [W.f_eq_mul_of_eval_eq_zero he, eval_mul, eval_sub, eval_X, eval_C] at ht
  exact (mul_eq_zero.mp ht).resolve_right (sub_ne_zero.mpr hte)

variable [W.IsElliptic] [W.IsCharNeTwoNF]

/-- **The descent map at a root `e` of `f`, away from `e`**: for `x ≠ e`, the class `μX x` takes
the value `x - e` at `e`. When `x` is itself a root of `f`, the correction `fCofactor x` of the
representative vanishes at `e`, because `f = fCofactor x · (X - x)` vanishes there. -/
lemma evalM_μX_of_ne {e x : K} (he : W.f.eval e = 0) (hxe : x ≠ e) :
    W.evalM he (W.μX x) =
      (Units.mk0 (x - e) (sub_ne_zero.mpr hxe) : Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) := by
  by_cases hx : W.f.eval x = 0
  · rw [μX_of_eval_f_eq_zero hx, evalM_mk]
    congr 2
    ext
    simpa using (W.isRoot_fCofactor_of_ne hx he hxe.symm).eq_zero
  · rw [μX_of_eval_f_ne_zero hx, evalM_mk]
    congr 2
    ext
    simp

/-- **The descent map at a root `e` of `f`, at `e` itself**: the class `μX e` takes the value
`f'(e) = 3e² + 2a₂e + a₄` at `e`, the value there of the correction `fCofactor e`. -/
lemma evalM_μX_self {e : K} (he : W.f.eval e = 0) :
    W.evalM he (W.μX e) =
      (Units.mk0 (3 * e ^ 2 + 2 * W.a₂ * e + W.a₄) (W.deriv_f_ne_zero he) :
        Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) := by
  rw [μX_of_eval_f_eq_zero he, evalM_mk]
  congr 2
  ext
  simp
  ring

end Field

section Real

variable (W : Affine ℝ)

/-- Over `ℝ`, the value at a root `e` of `f` of the class of a unit `u` of `W.A` is trivial exactly
when `u` is positive at `e`. -/
lemma evalM_mk_eq_one_iff_real {e : ℝ} (he : W.f.eval e = 0) (u : W.Aˣ) :
    W.evalM he u = 1 ↔ 0 < W.evalA he (u : W.A) := by
  have hne : W.evalA he (u : W.A) ≠ 0 := (u.isUnit.map _).ne_zero
  rw [evalM_mk, TauCeti.powMonoidHom_range_mk_eq_one_iff_exists_pow]
  simp only [Units.coe_map, MonoidHom.coe_ofClass]
  refine ⟨fun ⟨z, hz⟩ ↦ hz ▸ lt_of_le_of_ne (sq_nonneg z) (hz ▸ hne).symm,
    fun h ↦ ⟨_, Real.sq_sqrt h.le⟩⟩

/-- A root `r` of the cofactor `fCofactor e` splits it as `(X - r) (X - r')`, where
`r' = -(e + a₂) - r` is the other root. -/
private lemma fCofactor_eq_mul_of_isRoot {e r : ℝ} (hr : (W.fCofactor e).IsRoot r) :
    W.fCofactor e = (X - C r) * (X - C (-(e + W.a₂) - r)) := by
  have hr' : e ^ 2 + W.a₂ * e + W.a₄ = -r ^ 2 - (e + W.a₂) * r := by
    simp only [IsRoot, eval_add, eval_pow, eval_X, eval_mul, eval_C] at hr
    linear_combination hr
  simp only [fCofactor, hr', map_sub, map_neg, map_add, map_mul, map_pow]
  ring

/-- An element of positive norm that is positive at a root `e` of `f` and negative at another
root is negative at every root other than `e`: the norm is the product of the values at the three
roots. -/
private lemma eval_neg_of_ne {e t₀ : ℝ} (he : W.f.eval e = 0) {p : ℝ[X]}
    (hp : 0 < Algebra.norm ℝ (AdjoinRoot.mk W.f p)) (hpe : 0 < p.eval e)
    (ht₀ : W.f.eval t₀ = 0) (hpt₀ : p.eval t₀ < 0) {t : ℝ} (ht : W.f.eval t = 0) (hte : t ≠ e) :
    p.eval t < 0 := by
  have ht₀e : t₀ ≠ e := by rintro rfl; exact hpt₀.not_gt hpe
  have hfac := W.fCofactor_eq_mul_of_isRoot (W.isRoot_fCofactor_of_ne he ht₀ ht₀e)
  set t₁ := -(e + W.a₂) - t₀
  have hnorm : Algebra.norm ℝ (AdjoinRoot.mk W.f p) = p.eval e * (p.eval t₀ * p.eval t₁) := by
    rw [AdjoinRoot.norm_mk_eq_prod_eval (r := ![e, t₀, t₁]), Fin.prod_univ_three]
    · simp [mul_assoc]
    · rw [W.f_eq_mul_of_eval_eq_zero he, hfac, Fin.prod_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      ring
  have hpt₁ : p.eval t₁ < 0 := by
    rw [hnorm] at hp
    nlinarith [mul_pos_iff.mp hp, pos_of_mul_pos_right hp hpe.le]
  have := W.isRoot_fCofactor_of_ne he ht hte
  rw [hfac, IsRoot, eval_mul, eval_sub, eval_sub, eval_X, eval_C, eval_C, mul_eq_zero,
    sub_eq_zero, sub_eq_zero] at this
  rcases this with rfl | rfl
  exacts [hpt₀, hpt₁]

variable [W.IsElliptic] [W.IsCharNeTwoNF]

/-- If `e` is the smallest real root of `f`, the cofactor `fCofactor e = f / (X - e)` is positive
on `(-∞, e]`. Either it has no real root, or both of its roots are roots of `f` larger than `e`. -/
private lemma eval_fCofactor_pos {e : ℝ} (he : W.f.eval e = 0)
    (hmin : ∀ x, W.f.eval x = 0 → e ≤ x) {t : ℝ} (ht : t ≤ e) : 0 < (W.fCofactor e).eval t := by
  have hge : (W.fCofactor e).eval e ≠ 0 := by
    rw [eval_fCofactor_self]
    exact W.deriv_f_ne_zero he
  by_contra hle
  push Not at hle
  -- a monic quadratic that is not positive at `t` has a root `r ≥ t`
  obtain ⟨r, hr, htr⟩ : ∃ r, (W.fCofactor e).IsRoot r ∧ t ≤ r := by
    set B := e + W.a₂
    set c := e ^ 2 + W.a₂ * e + W.a₄
    have hg : (W.fCofactor e).eval t = t ^ 2 + B * t + c := by simp [fCofactor, B, c]
    have hD : 0 ≤ B ^ 2 - 4 * c := by nlinarith [sq_nonneg (2 * t + B)]
    refine ⟨(-B + √(B ^ 2 - 4 * c)) / 2, ?_, ?_⟩
    · simp only [IsRoot, fCofactor, eval_add, eval_pow, eval_X, eval_mul, eval_C]
      linear_combination (Real.sq_sqrt hD) / 4
    · nlinarith [Real.sq_sqrt hD, Real.sqrt_nonneg (B ^ 2 - 4 * c)]
  have hfac := W.fCofactor_eq_mul_of_isRoot hr
  have hroot (s : ℝ) (hs : (W.fCofactor e).IsRoot s) : e < s := by
    refine lt_of_le_of_ne (hmin s ?_) fun hes ↦ hge (hes ▸ hs)
    rw [W.f_eq_mul_of_eval_eq_zero he, eval_mul, hs.eq_zero, zero_mul]
  have h₁ := hroot r hr
  have h₂ := hroot (-(e + W.a₂) - r) (by rw [hfac]; simp)
  rw [hfac, eval_mul, eval_sub, eval_sub, eval_X, eval_C, eval_C] at hle
  nlinarith

/-- **Every value of the descent map is positive at the smallest real root of `f`.** Every real
point has `x ≥ e`, since `f < 0` on `(-∞, e)`; the value is `x - e > 0` for `x ≠ e`, and
`f'(e) > 0` at `x = e`. -/
theorem evalM_μ₀_eq_one_real {e : ℝ} (he : W.f.eval e = 0) (hmin : ∀ x, W.f.eval x = 0 → e ≤ x)
    (P : W.Point) : W.evalM he (W.μ₀ P) = 1 := by
  match P with
  | 0 => simp
  | .some x y h =>
    rw [μ₀_some]
    rcases eq_or_ne x e with rfl | hxe
    · rw [evalM_μX_self, TauCeti.powMonoidHom_range_mk_eq_one_iff_exists_pow]
      have hpos := W.eval_fCofactor_pos he hmin le_rfl
      rw [eval_fCofactor_self] at hpos
      exact ⟨_, Real.sq_sqrt hpos.le⟩
    · rw [evalM_μX_of_ne W he hxe, TauCeti.powMonoidHom_range_mk_eq_one_iff_exists_pow]
      have hpos : 0 < x - e := by
        refine sub_pos.mpr (lt_of_not_ge fun hxe' ↦ ?_)
        have hf := (W.equation_iff_eval_f_eq_sq x y).mp h.1
        rw [W.f_eq_mul_of_eval_eq_zero he, eval_mul, eval_sub, eval_X, eval_C] at hf
        nlinarith [W.eval_fCofactor_pos he hmin hxe', sq_nonneg y,
          sub_neg.mpr (lt_of_le_of_ne hxe' hxe)]
      exact ⟨_, Real.sq_sqrt hpos.le⟩

/-- **Square classes over `ℝ` are detected at the real roots of `f`.** A class in `W.M` is trivial
exactly when its value at every real root of `f` is trivial. By the Chinese remainder theorem
`W.A` is `ℝ³` when `f` has three real roots and `ℝ × ℂ` when it has one, and every complex number
is a square. -/
theorem eq_one_iff_forall_evalM_eq_one_real (m : W.M) :
    m = 1 ↔ ∀ (t : ℝ) (ht : W.f.eval t = 0), W.evalM ht m = 1 := by
  refine ⟨fun hm _ _ ↦ hm ▸ map_one _, fun h ↦ ?_⟩
  induction m using QuotientGroup.induction_on with | H u => ?_
  obtain ⟨q, hq⟩ := AdjoinRoot.mk_surjective (u : W.A)
  rw [AdjoinRoot.modPow_mk_eq_one_iff_forall_factors W.f_ne_zero W.squarefree_f]
  intro p
  rw [TauCeti.powMonoidHom_range_mk_eq_one_iff_exists_pow]
  have hproj : ((Units.map
      (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p).toRingHom.toMonoidHom u :
      (AdjoinRoot (p : ℝ[X]))ˣ) : AdjoinRoot (p : ℝ[X])) = AdjoinRoot.mk _ q := by
    rw [Units.coe_map, ← hq]
    exact AdjoinRoot.projFactor_mk _ _ _ _
  rw [hproj]
  by_cases hp1 : (p : ℝ[X]).natDegree = 1
  · -- a linear factor `X - t`: the component is the value at the root `t`, which is positive
    set t := Factors.linearEquivRoots ⟨p, hp1⟩
    have hpt : (p : ℝ[X]) = X - C (t : ℝ) := by
      rw [← Factors.linearEquivRoots_symm_apply, Equiv.symm_apply_apply]
    have hqt : 0 < q.eval (t : ℝ) := by
      simpa [← hq] using (W.evalM_mk_eq_one_iff_real t.property u).mp (h t t.property)
    refine ⟨AdjoinRoot.mk _ (C √(q.eval (t : ℝ))), ?_⟩
    rw [← map_pow, AdjoinRoot.mk_eq_mk, ← C_pow, Real.sq_sqrt hqt.le, hpt]
    exact dvd_sub_comm.mp (X_sub_C_dvd_sub_C_eval)
  · -- otherwise the factor is an irreducible quadratic, and its quotient is `ℂ`
    have hle : (p : ℝ[X]).natDegree ≤ 3 :=
      W.natDegree_f ▸ natDegree_le_of_dvd p.dvd W.f_ne_zero
    have hroot : ∀ x, ¬(p : ℝ[X]).IsRoot x := fun x hx ↦
      hp1 (natDegree_eq_of_degree_eq_some (degree_eq_one_of_irreducible_of_root p.irreducible hx))
    have h3 : (p : ℝ[X]).natDegree ≠ 3 := fun h3 ↦ by
      obtain ⟨x, hx⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree (f := (p : ℝ[X])) (by
        rw [h3]; decide)
      exact hroot x hx
    have h0 := p.irreducible.natDegree_pos
    obtain ⟨w, hw⟩ := AdjoinRoot.isSquare_of_irreducible_of_natDegree_eq_two p.irreducible
      (by omega) (AdjoinRoot.mk _ q)
    exact ⟨w, by rw [sq, hw]⟩

variable [DecidableEq ℝ]

/-- **The image of the descent map over `ℝ`.** Let `e` be the smallest real root of `f`. A square
class lies in the image of `μ : W(ℝ) → W.M` exactly when it has square norm and its value at `e`
is trivial, that is, positive.

When `f` has a single real root the image is trivial. When `f` has three real roots
`e < e₂ < e₃` it consists of the classes with signs `(+, +, +)` and `(+, -, -)` at `(e, e₂, e₃)`;
the second is the value of `μ` at `(e, 0)`, on the bounded component of `W(ℝ)`. -/
theorem mem_range_μ_iff_real {e : ℝ} (he : W.f.eval e = 0) (hmin : ∀ x, W.f.eval x = 0 → e ≤ x)
    (m : W.M) : m ∈ (μ (W := W)).range ↔ W.normM m = 1 ∧ W.evalM he m = 1 := by
  refine ⟨?_, fun ⟨hN, hm⟩ ↦ ?_⟩
  · rintro ⟨P, rfl⟩
    rw [← ofAdd_toAdd P, μ_apply]
    exact ⟨normM_μ₀_eq_one _, W.evalM_μ₀_eq_one_real he hmin _⟩
  by_cases hall : ∀ (t : ℝ) (ht : W.f.eval t = 0), W.evalM ht m = 1
  · rw [(W.eq_one_iff_forall_evalM_eq_one_real m).mpr hall]
    exact one_mem _
  -- otherwise `m` is the value of `μ` at the `2`-torsion point `(e, 0)`
  push Not at hall
  obtain ⟨t₀, ht₀, hmt₀⟩ := hall
  induction m using QuotientGroup.induction_on with | H u => ?_
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (u : W.A)
  have hev (t : ℝ) (ht : W.f.eval t = 0) :
      W.evalA ht (u : W.A) = p.eval t := by simp [← hp]
  have hpe : 0 < p.eval e := hev e he ▸ (W.evalM_mk_eq_one_iff_real he u).mp hm
  have hpt₀ : p.eval t₀ < 0 := by
    refine lt_of_le_of_ne (not_lt.mp fun h ↦ hmt₀ ?_) fun h ↦ ?_
    · exact (W.evalM_mk_eq_one_iff_real ht₀ u).mpr (hev t₀ ht₀ ▸ h)
    · exact (u.isUnit.map (W.evalA ht₀)).ne_zero (hev t₀ ht₀ ▸ h)
  have hnorm : 0 < Algebra.norm ℝ (AdjoinRoot.mk W.f p) := by
    rw [normM_mk, TauCeti.powMonoidHom_range_mk_eq_one_iff_exists_pow] at hN
    obtain ⟨z, hz⟩ := hN
    have hu : Algebra.norm ℝ (u : W.A) ≠ 0 := (u.isUnit.map (Algebra.norm ℝ)).ne_zero
    simp only [Units.coe_map] at hz
    rw [hp, ← hz]
    exact lt_of_le_of_ne (sq_nonneg z) (hz ▸ hu).symm
  set ρ := (W.isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero he).unit
  have key : (u : W.M) * ρ = 1 := by
    rw [← QuotientGroup.mk_mul, W.eq_one_iff_forall_evalM_eq_one_real]
    intro t ht
    rw [evalM_mk_eq_one_iff_real, Units.val_mul, map_mul, hev t ht, IsUnit.unit_spec, evalA_mk]
    rw [eval_add, eval_sub, eval_C, eval_X]
    rcases eq_or_ne t e with rfl | hte
    · rw [sub_self, zero_add]
      exact mul_pos hpe (W.eval_fCofactor_pos he hmin le_rfl)
    · rw [(W.isRoot_fCofactor_of_ne he ht hte).eq_zero, add_zero]
      exact mul_pos_of_neg_of_neg (W.eval_neg_of_ne he hnorm hpe ht₀ hpt₀ ht hte)
        (sub_neg.mpr (lt_of_le_of_ne (hmin t ht) hte.symm))
  refine ⟨.ofAdd (.some e 0 (W.nonsingular_of_eval_f_eq_zero he)), ?_⟩
  rw [μ_apply, μ₀_some, μX_of_eval_f_eq_zero he]
  exact ((mul_eq_one_iff_eq_inv.mp key).trans (M.inv_eq_self _)).symm

end Real

/-- **The local condition of explicit `2`-descent at a real place.** Let `W` be a curve over a
field `K` with an embedding `K → ℝ`, and `e` the smallest real root of the cubic of the base
change `W⁄ℝ`. A square class over `K` satisfies the local condition at `ℝ` exactly when its
restriction has square norm and is positive at `e`. -/
theorem mem_localCondition_real_iff {K : Type*} [Field K] [Algebra K ℝ] (W : Affine K)
    [W.IsElliptic] [W.IsCharNeTwoNF] {e : ℝ} (he : (W⁄ℝ).toAffine.f.eval e = 0)
    (hmin : ∀ x, (W⁄ℝ).toAffine.f.eval x = 0 → e ≤ x) (m : W.M) :
    m ∈ W.localCondition ℝ ↔
      (W⁄ℝ).toAffine.normM (W.localRes ℝ m) = 1 ∧
        (W⁄ℝ).toAffine.evalM he (W.localRes ℝ m) = 1 := by
  classical
  rw [mem_localCondition_iff, mem_range_μ_iff_real _ he hmin]

end Affine

end WeierstrassCurve
