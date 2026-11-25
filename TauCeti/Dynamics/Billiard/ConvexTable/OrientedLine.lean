/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.ConvexTable.Exit
public import TauCeti.Dynamics.Billiard.OrientedLine
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.LocalAtTarget
import TauCeti.Analysis.Complex.Circle.Basic

/-!
# Oriented lines and the phase cylinder of a convex table

An oriented line of the plane `ℂ` is represented by a pair `(e, c) ∈ Circle × ℝ`: the line
`{z | e × z = c}` (`TauCeti.orientedLineSet`), oriented by its direction `e`, where
`a × b = Im (conj a * b)`. The line through `z` with direction `e` is `(e, e × z)`
(`TauCeti.orientedLineThrough`), and:

* `TauCeti.orientedLineSet_eq_range`: the line `(e, c)` is `{z + t e : t ∈ ℝ}` for any of its
  points `z`;
* `TauCeti.orientedLineThrough_eq_iff`: two (direction, point) pairs give the same oriented line
  exactly when the directions agree and the points differ by a multiple of the direction, so every
  oriented line has exactly one representation;
* `TauCeti.orientedLineSet_neg`, `TauCeti.orientedLineSet_eq_orientedLineSet_iff`: reversing the
  orientation, `(e, c) ↦ (−e, −c)`, keeps the point set, and two representations have the same
  point set exactly when they are equal or opposite.

For a convex table `γ` with unit tangent `τ`, the oriented line of the state `(s, δ)` is
`Λ(s, δ) = (exp(iδ) τ(s), exp(iδ) τ(s) × γ(s))` (`TauCeti.ConvexTable.orientedLine`), the line
along which the ball leaves `γ(s)` at the angle `δ`. It contains the exit point `γ(s₁)` of §1.3
(`TauCeti.ConvexTable.apply_exitParam_mem_orientedLineSet`). The main result is that `Λ` is a
homeomorphism from the phase cylinder `AddCircle ℓ × (0, π)` onto the set of oriented lines meeting
the interior of the region `Ω` bounded by `γ` (`TauCeti.ConvexTable.orientedLineHomeomorph`),
which is open (`TauCeti.ConvexTable.isOpen_setOf_orientedLineSet_inter_interior_nonempty`):

* for `δ ∈ (0, π)` the line meets the interior of `Ω`, and the tangent lines (`sin δ = 0`) do not
  (`TauCeti.ConvexTable.orientedLineSet_orientedLine_inter_interior_nonempty`,
  `TauCeti.ConvexTable.orientedLineSet_orientedLine_inter_interior_eq_empty`);
* `Λ` is injective on the phase cylinder
  (`TauCeti.ConvexTable.orientedLine_eq_orientedLine_iff`), by the injectivity of the oriented
  lines of `TauCeti.StrictConvexBilliardTable`;
* every line meeting the interior of `Ω` is `Λ` of its entry state
  (`TauCeti.ConvexTable.exists_orientedLine_eq`): the point where the line enters `Ω` is the last
  point of `Ω` before an interior point, in the reverse direction, and lies on the curve;
* the inverse is continuous because `Λ` extends continuously to the compact closed cylinder
  `AddCircle ℓ × [0, π]`, so it is a closed map there, and the phase cylinder is exactly the
  preimage of the lines meeting the interior of `Ω`.

## References

* M. Bialy and A. E. Mironov, *The Birkhoff–Poritsky conjecture for centrally-symmetric billiard
  tables*, Ann. of Math. 196 (2022), Section 2.
-/

public section

noncomputable section

open Function Set Filter Topology Complex
open scoped ComplexConjugate

namespace TauCeti

/-! ### Oriented lines of the plane -/

/-- The point set `{z | e × z = c}` of the oriented line `p = (e, c) ∈ Circle × ℝ`, where
`a × b = Im (conj a * b)`; the line is oriented by its direction `e`. -/
def orientedLineSet (p : Circle × ℝ) : Set ℂ :=
  {z | (conj (p.1 : ℂ) * z).im = p.2}

theorem mem_orientedLineSet {p : Circle × ℝ} {z : ℂ} :
    z ∈ orientedLineSet p ↔ (conj (p.1 : ℂ) * z).im = p.2 :=
  Iff.rfl

/-- The oriented line `(e, e × z)` through `z` with direction `e`. -/
def orientedLineThrough (e : Circle) (z : ℂ) : Circle × ℝ :=
  (e, (conj (e : ℂ) * z).im)

theorem orientedLineThrough_def (e : Circle) (z : ℂ) :
    orientedLineThrough e z = (e, (conj (e : ℂ) * z).im) :=
  (rfl)

theorem mem_orientedLineSet_orientedLineThrough (e : Circle) (z : ℂ) :
    z ∈ orientedLineSet (orientedLineThrough e z) :=
  mem_orientedLineSet.2 rfl

/-- Moving along the direction `e` does not change `e × z`. -/
theorem im_conj_mul_add_smul (e : Circle) (z : ℂ) (t : ℝ) :
    (conj (e : ℂ) * (z + t • (e : ℂ))).im = (conj (e : ℂ) * z).im := by
  rw [mul_add, real_smul, mul_left_comm, Circle.conj_coe_mul_self, mul_one, add_im, ofReal_im,
    add_zero]

/-- The oriented line `(e, c)` is `{z + t e : t ∈ ℝ}` for any of its points `z`. -/
theorem orientedLineSet_eq_range {p : Circle × ℝ} {z : ℂ} (hz : z ∈ orientedLineSet p) :
    orientedLineSet p = range fun t : ℝ => z + t • (p.1 : ℂ) := by
  ext w
  refine ⟨fun hw => ⟨(conj (p.1 : ℂ) * (w - z)).re, ?_⟩, ?_⟩
  · have him : (conj (p.1 : ℂ) * (w - z)).im = 0 := by
      rw [mul_sub, sub_im, hw, hz, sub_self]
    have hreal : ((conj (p.1 : ℂ) * (w - z)).re : ℂ) = conj (p.1 : ℂ) * (w - z) :=
      Complex.ext (by simp) (by simp [him])
    simp only
    rw [real_smul, hreal]
    linear_combination (w - z) * Circle.conj_coe_mul_self p.1
  · rintro ⟨t, rfl⟩
    rw [mem_orientedLineSet, im_conj_mul_add_smul, hz]

/-- **Every oriented line has exactly one representation.** The oriented lines through `z` with
direction `e` and through `z'` with direction `e'` agree exactly when `e = e'` and `z' − z` is a
real multiple of `e`. -/
theorem orientedLineThrough_eq_iff {e e' : Circle} {z z' : ℂ} :
    orientedLineThrough e z = orientedLineThrough e' z' ↔
      e = e' ∧ ∃ t : ℝ, z' = z + t • (e : ℂ) := by
  constructor
  · intro h
    have he : e = e' := congrArg Prod.fst h
    subst he
    have hz' : z' ∈ orientedLineSet (orientedLineThrough e z) := (congrArg Prod.snd h).symm
    rw [orientedLineSet_eq_range (mem_orientedLineSet_orientedLineThrough e z)] at hz'
    obtain ⟨t, ht⟩ := hz'
    exact ⟨rfl, t, ht.symm⟩
  · rintro ⟨rfl, t, rfl⟩
    rw [orientedLineThrough_def, orientedLineThrough_def, im_conj_mul_add_smul]

/-- **Reversing the orientation** `(e, c) ↦ (−e, −c)` keeps the point set of the line. -/
@[simp]
theorem orientedLineSet_neg (p : Circle × ℝ) : orientedLineSet (-p) = orientedLineSet p := by
  ext z
  simp only [mem_orientedLineSet, Prod.fst_neg, Prod.snd_neg, Circle.coe_neg, map_neg, neg_mul,
    neg_im, neg_inj]

/-- A point of the line `(e, c)`: `c i e`. -/
theorem smul_I_mul_mem_orientedLineSet (p : Circle × ℝ) :
    p.2 • (I * (p.1 : ℂ)) ∈ orientedLineSet p := by
  rw [mem_orientedLineSet, real_smul, mul_left_comm, mul_left_comm (conj _),
    Circle.conj_coe_mul_self, mul_one, mul_comm]
  simp

/-- Two representations have the same point set exactly when they are equal or opposite. -/
theorem orientedLineSet_eq_orientedLineSet_iff {p q : Circle × ℝ} :
    orientedLineSet p = orientedLineSet q ↔ q = p ∨ q = -p := by
  refine ⟨fun h => ?_, ?_⟩
  · set z := p.2 • (I * (p.1 : ℂ))
    have hz : z ∈ orientedLineSet p := smul_I_mul_mem_orientedLineSet p
    have hze : z + (1 : ℝ) • (p.1 : ℂ) ∈ orientedLineSet p := by
      rw [orientedLineSet_eq_range hz]
      exact ⟨1, rfl⟩
    rw [h, mem_orientedLineSet] at hz hze
    -- `u = conj e' e` is a real point of the circle.
    set u : Circle := q.1⁻¹ * p.1 with hu
    have hu' : (u : ℂ) = conj (q.1 : ℂ) * p.1 := by
      rw [hu, Circle.coe_mul, Circle.coe_inv_eq_conj]
    have huim : (u : ℂ).im = 0 := by
      rw [one_smul, mul_add, add_im, hz] at hze
      rw [hu']
      linarith
    have hpe : (p.1 : ℂ) = q.1 * u := by
      rw [hu', ← mul_assoc, Circle.coe_mul_conj_self, one_mul]
    have hqz : (conj (q.1 : ℂ) * z).im = q.2 := hz
    rcases (Circle.im_coe_eq_zero_iff u).1 huim with hu1 | hu1
    · have he : q.1 = p.1 := Circle.ext (by rw [hpe, hu1, Circle.coe_one, mul_one])
      refine Or.inl (Prod.ext he ?_)
      rw [← hqz, he]
      simp [z, real_smul, mul_left_comm, Circle.conj_coe_mul_self]
    · have he : q.1 = -p.1 :=
        Circle.ext (by rw [Circle.coe_neg, hpe, hu1, Circle.coe_neg, Circle.coe_one]; ring)
      refine Or.inr (Prod.ext he ?_)
      rw [← hqz, he, Prod.snd_neg]
      simp [z, real_smul, mul_left_comm, Circle.conj_coe_mul_self]
  · rintro (rfl | rfl)
    · rfl
    · exact (orientedLineSet_neg p).symm

/-! ### The oriented lines of a convex table -/

namespace ConvexTable

attribute [local instance] Complex.finrank_real_complex_fact

variable {k : ℕ∞} {ℓ : ℝ} [Fact (0 < ℓ)] (T : ConvexTable k ℓ)

/-- The unit tangent `τ(s)` of a table, as a point of the unit circle. -/
def tangent (s : ℝ) : Circle :=
  ⟨deriv T s, mem_sphere_zero_iff_norm.2 (T.norm_deriv s)⟩

@[simp]
theorem coe_tangent (s : ℝ) : (T.tangent s : ℂ) = deriv T s :=
  (rfl)

theorem continuous_tangent : Continuous T.tangent :=
  T.continuous_deriv.subtype_mk _

/-- The **oriented line** `Λ(s, δ) = (exp(iδ) τ(s), exp(iδ) τ(s) × γ(s))` of the state `(s, δ)`:
the line through `γ(s)` with direction `exp(iδ) τ(s)`. -/
def orientedLine (s δ : ℝ) : Circle × ℝ :=
  orientedLineThrough (Circle.exp δ * T.tangent s) (T s)

theorem orientedLine_def (s δ : ℝ) :
    T.orientedLine s δ = orientedLineThrough (Circle.exp δ * T.tangent s) (T s) :=
  (rfl)

@[simp]
theorem coe_orientedLine_fst (s δ : ℝ) :
    ((T.orientedLine s δ).1 : ℂ) = exp (δ * I) * deriv T s := by
  simp [orientedLine_def, orientedLineThrough_def, Circle.coe_exp]

theorem orientedLine_snd (s δ : ℝ) :
    (T.orientedLine s δ).2 = (conj (exp (δ * I) * deriv T s) * T s).im := by
  simp [orientedLine_def, orientedLineThrough_def, Circle.coe_exp]

theorem continuous_orientedLine : Continuous fun x : ℝ × ℝ => T.orientedLine x.1 x.2 := by
  have hdir : Continuous fun x : ℝ × ℝ => Circle.exp x.2 * T.tangent x.1 :=
    (Circle.exp.continuous.comp continuous_snd).mul (T.continuous_tangent.comp continuous_fst)
  refine hdir.prodMk (continuous_im.comp ?_)
  exact (continuous_conj.comp (continuous_subtypeVal.comp hdir)).mul
    (T.continuous.comp continuous_fst)

theorem periodic_orientedLine (δ : ℝ) : Periodic (fun s => T.orientedLine s δ) ℓ := fun s => by
  have h1 : T.tangent (s + ℓ) = T.tangent s := Circle.ext (by simp [T.periodic_deriv s])
  simp only [orientedLine_def, h1, T.periodic s]

/-- The table point `γ(s)` lies on the line `Λ(s, δ)`. -/
theorem apply_mem_orientedLineSet (s δ : ℝ) : T s ∈ orientedLineSet (T.orientedLine s δ) :=
  mem_orientedLineSet_orientedLineThrough _ _

/-- The points `γ(s) + r exp(iδ) τ(s)` lie on the line `Λ(s, δ)`. -/
theorem add_smul_mem_orientedLineSet (s δ r : ℝ) :
    T s + r • (exp (δ * I) * deriv T s) ∈ orientedLineSet (T.orientedLine s δ) := by
  rw [← coe_orientedLine_fst, mem_orientedLineSet, im_conj_mul_add_smul]
  exact T.apply_mem_orientedLineSet s δ

/-- **The line leaves at the exit point.** For `0 < δ < π`, the exit point `γ(s₁)` of §1.3 lies on
the line `Λ(s, δ)`. -/
theorem apply_exitParam_mem_orientedLineSet {s δ : ℝ} (hδ : δ ∈ Ioo 0 Real.pi) :
    T (T.exitParam s δ) ∈ orientedLineSet (T.orientedLine s δ) := by
  rw [eq_add_of_sub_eq' (T.apply_exitParam_sub_eq_norm_smul hδ)]
  exact T.add_smul_mem_orientedLineSet s δ _

/-- For `0 < δ < π`, the line `Λ(s, δ)` meets the interior of the region `Ω`. -/
theorem orientedLineSet_orientedLine_inter_interior_nonempty {s δ : ℝ} (hδ : δ ∈ Ioo 0 Real.pi) :
    (orientedLineSet (T.orientedLine s δ) ∩ interior T.region).Nonempty := by
  obtain ⟨r, hr⟩ := (T.eventually_add_smul_mem_interior_region (s := s) hδ).exists
  exact ⟨_, T.add_smul_mem_orientedLineSet s δ r, hr⟩

/-- **Tangent lines miss the interior.** If `sin δ = 0`, the line `Λ(s, δ)` is the tangent line at
`γ(s)` and does not meet the interior of `Ω`. -/
theorem orientedLineSet_orientedLine_inter_interior_eq_empty {s δ : ℝ} (hδ : Real.sin δ = 0) :
    orientedLineSet (T.orientedLine s δ) ∩ interior T.region = ∅ := by
  refine eq_empty_of_forall_notMem fun z ⟨hz, hint⟩ => ?_
  have hpos := (T.mem_interior_region_iff.1 hint) s
  have hline : (conj (exp (δ * I) * deriv T s) * (z - T s)).im = 0 := by
    rw [mem_orientedLineSet, coe_orientedLine_fst, orientedLine_snd] at hz
    rw [mul_sub, sub_im, hz, sub_self]
  have hcos := Real.sin_eq_zero_iff_cos_eq.1 hδ
  rw [map_mul, mul_assoc, ← exp_conj, map_mul, conj_ofReal, conj_I, mul_neg, ← neg_mul,
    exp_mul_I] at hline
  set w := conj (deriv T s) * (z - T s)
  have : ((Real.cos (-δ) : ℂ) + (Real.sin (-δ) : ℂ) * I) * w =
      (Real.cos δ : ℂ) * w - (Real.sin δ : ℂ) * (I * w) := by
    rw [Real.cos_neg, Real.sin_neg]; push_cast; ring
  rw [← ofReal_neg, ← ofReal_cos, ← ofReal_sin, this, hδ] at hline
  simp only [ofReal_zero, zero_mul, sub_zero, mul_im, ofReal_re, ofReal_im, zero_mul,
    add_zero] at hline
  rcases hcos with h | h <;> rw [h] at hline <;> linarith

/-- **Injectivity on the phase cylinder.** For `δ ∈ (0, π)` and `δ' ∈ [0, π]`, the states `(s, δ)`
and `(s', δ')` have the same oriented line exactly when `s ≡ s'` modulo `ℓ` and `δ = δ'`. -/
theorem orientedLine_eq_orientedLine_iff {s s' δ δ' : ℝ} (hδ : δ ∈ Ioo 0 Real.pi)
    (hδ' : δ' ∈ Icc 0 Real.pi) :
    T.orientedLine s δ = T.orientedLine s' δ' ↔ (s : AddCircle ℓ) = s' ∧ δ = δ' := by
  set χ := T.toStrictConvexBilliardTable
  set g : Circle × ℝ → ℂ × ℝ := fun p => ((p.1 : ℂ), p.2)
  have key (t ε : ℝ) (hε : ε ∈ Icc 0 Real.pi) :
      χ.orientedLine t (Real.cos ε) = g (T.orientedLine t ε) := by
    rw [StrictConvexBilliardTable.orientedLine_def,
      T.toStrictConvexBilliardTable_outgoingDir_cos hε, Complex.areaForm,
      coe_toStrictConvexBilliardTable]
    exact Prod.ext (T.coe_orientedLine_fst t ε).symm (T.orientedLine_snd t ε).symm
  have hinj : Injective g := fun p q h =>
    Prod.ext (Circle.ext (congrArg Prod.fst h :)) (congrArg Prod.snd h :)
  refine hinj.eq_iff.symm.trans ?_
  rw [← key s δ (Ioo_subset_Icc_self hδ), ← key s' δ' hδ',
    χ.orientedLine_eq_orientedLine_iff (Real.mapsTo_cos_Ioo hδ), coe_toStrictConvexBilliardTable,
    T.apply_eq_apply_iff, Real.injOn_cos.eq_iff (Ioo_subset_Icc_self hδ) hδ']

/-- The ray from an interior point `z₀` of `Ω` in the direction `−e` meets the curve: the last
point of `Ω` on it is not interior, so it is a point `γ(s)`. -/
private theorem exists_apply_eq_sub_smul {z₀ : ℂ} (hint : z₀ ∈ interior T.region) (e : Circle) :
    ∃ r : ℝ, 0 ≤ r ∧ ∃ s, T s = z₀ - r • (e : ℂ) := by
  -- The parameters `r ≥ 0` with `z₀ − r e ∈ Ω` form a compact set; take the largest.
  set S : Set ℝ := {r | 0 ≤ r ∧ z₀ - r • (e : ℂ) ∈ T.region}
  obtain ⟨M, hM⟩ := T.isCompact_region.isBounded.subset_closedBall 0
  have hSb : S ⊆ Icc 0 (‖z₀‖ + M) := fun r ⟨hr, hrΩ⟩ => by
    refine ⟨hr, ?_⟩
    have h1 : ‖z₀ - r • (e : ℂ)‖ ≤ M := by simpa using hM hrΩ
    have h2 : r = ‖z₀ - (z₀ - r • (e : ℂ))‖ := by simp [abs_of_nonneg hr]
    rw [h2]
    exact (norm_sub_le _ _).trans (by linarith)
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ((Metric.isBounded_Icc _ _).subset hSb)
    exact isClosed_Ici.inter (T.isClosed_region.preimage (by fun_prop))
  have hS0 : (0 : ℝ) ∈ S := ⟨le_rfl, by simpa using interior_subset hint⟩
  set r₀ := sSup S
  have hr₀ : r₀ ∈ S := hSc.sSup_mem ⟨0, hS0⟩
  set w := z₀ - r₀ • (e : ℂ)
  -- The last point `w` of `Ω` is not interior, so it lies on the curve.
  have hw : w ∉ interior T.region := by
    intro hw
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior w hw
    have hmem : r₀ + ε / 2 ∈ S := by
      refine ⟨by linarith [hr₀.1], interior_subset (hball ?_)⟩
      rw [Metric.mem_ball, dist_eq_norm]
      have : z₀ - (r₀ + ε / 2) • (e : ℂ) - w = -((ε / 2) • (e : ℂ)) := by simp only [w]; module
      rw [this, norm_neg, norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg (by positivity)]
      linarith
    have := le_csSup hSc.bddAbove hmem
    linarith
  obtain ⟨s, hs⟩ : w ∈ range T := by
    by_contra h
    exact hw (by rw [T.interior_region]; exact ⟨hr₀.2, h⟩)
  exact ⟨r₀, hr₀.1, s, hs⟩

/-- **Surjectivity onto the lines meeting the interior.** Every oriented line meeting the interior
of `Ω` is `Λ(s, δ)` for some `s` and `δ ∈ (0, π)`: its entry state. -/
theorem exists_orientedLine_eq {p : Circle × ℝ}
    (hp : (orientedLineSet p ∩ interior T.region).Nonempty) :
    ∃ s, ∃ δ ∈ Ioo 0 Real.pi, T.orientedLine s δ = p := by
  obtain ⟨z₀, hz₀, hint⟩ := hp
  set e : ℂ := (p.1 : ℂ)
  -- The entry point `w = γ(s)` is the last point of `Ω` before `z₀`, in the reverse direction.
  obtain ⟨r₀, hr₀, s, hs⟩ := T.exists_apply_eq_sub_smul hint p.1
  set w := z₀ - r₀ • e
  -- The direction points to the left of `τ(s)`, so it is `exp(iδ) τ(s)` with `δ ∈ (0, π)`.
  have hleft : 0 < (conj (deriv T s) * e).im := by
    have h := (T.mem_interior_region_iff.1 hint) s
    have hz : z₀ - T s = r₀ • e := by rw [hs]; simp only [w]; abel
    rw [hz, real_smul, mul_left_comm, im_ofReal_mul] at h
    exact pos_of_mul_pos_right h hr₀
  set u : Circle := (T.tangent s)⁻¹ * p.1
  have hu : (u : ℂ) = conj (deriv T s) * e := by
    rw [Circle.coe_mul, Circle.coe_inv_eq_conj, coe_tangent]
  have harg : arg (u : ℂ) ∈ Ioo 0 Real.pi := by
    rw [hu]
    refine ⟨lt_of_le_of_ne (arg_nonneg_iff.2 hleft.le) fun h => ?_,
      arg_lt_pi_iff.2 (Or.inr hleft.ne')⟩
    exact hleft.ne' (arg_eq_zero_iff.1 h.symm).2
  refine ⟨s, arg (u : ℂ), harg, ?_⟩
  have hdir : Circle.exp (arg (u : ℂ)) * T.tangent s = p.1 := by
    rw [Circle.exp_arg, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [orientedLine_def, hdir, orientedLineThrough_def]
  refine Prod.ext rfl ?_
  have hw' : w = z₀ + (-r₀) • e := by simp only [w]; module
  change (conj e * T s).im = p.2
  rw [hs, hw']
  exact (im_conj_mul_add_smul p.1 z₀ (-r₀)).trans hz₀

/-- **The lines meeting the interior form an open set.** If `z₀` is an interior point on the line
`(e, c)`, then `z₀ + (c' − e' × z₀) i e'` lies on the nearby line `(e', c')`, close to `z₀`. -/
theorem isOpen_setOf_orientedLineSet_inter_interior_nonempty :
    IsOpen {p : Circle × ℝ | (orientedLineSet p ∩ interior T.region).Nonempty} := by
  refine isOpen_iff_mem_nhds.2 fun p ⟨z₀, hz₀, hint⟩ => ?_
  set f : Circle × ℝ → ℂ := fun q => z₀ + (q.2 - (conj (q.1 : ℂ) * z₀).im) • (I * (q.1 : ℂ))
  have hf : Continuous f := by
    simp only [f, real_smul]
    fun_prop
  have hfp : f p = z₀ := by
    simp only [f]
    rw [hz₀, sub_self, zero_smul, add_zero]
  have hmem (q : Circle × ℝ) : f q ∈ orientedLineSet q := by
    rw [mem_orientedLineSet]
    simp only [f, mul_add, add_im, real_smul]
    rw [mul_left_comm, mul_left_comm (conj (q.1 : ℂ)), Circle.conj_coe_mul_self, mul_one]
    simp
  filter_upwards [hf.continuousAt.preimage_mem_nhds (hfp ▸ isOpen_interior.mem_nhds hint)]
    with q hq
  exact ⟨f q, hmem q, hq⟩

/-- `Λ` on `AddCircle ℓ × ℝ`. -/
def circleOrientedLine (x : AddCircle ℓ × ℝ) : Circle × ℝ :=
  (T.periodic_orientedLine x.2).lift x.1

@[simp]
theorem circleOrientedLine_mk (s δ : ℝ) :
    T.circleOrientedLine ((s : AddCircle ℓ), δ) = T.orientedLine s δ :=
  (rfl)

theorem continuous_circleOrientedLine : Continuous T.circleOrientedLine :=
  ((QuotientAddGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id).isQuotientMap
    (X := ℝ × ℝ)).continuous_iff.2 T.continuous_orientedLine

/-- `Λ` on the compact closed cylinder `AddCircle ℓ × [0, π]`. -/
private def closedLine (x : AddCircle ℓ × Icc 0 Real.pi) : Circle × ℝ :=
  T.circleOrientedLine (x.1, x.2)

private theorem continuous_closedLine : Continuous T.closedLine :=
  T.continuous_circleOrientedLine.comp (continuous_fst.prodMk
    (continuous_subtypeVal.comp continuous_snd))

/-- The set of oriented lines meeting the interior of `Ω`. -/
private abbrev interiorLines : Set (Circle × ℝ) :=
  {p | (orientedLineSet p ∩ interior T.region).Nonempty}

private theorem mem_preimage_closedLine_iff (x : AddCircle ℓ × Icc 0 Real.pi) :
    x ∈ T.closedLine ⁻¹' T.interiorLines ↔ (x.2 : ℝ) ∈ Ioo 0 Real.pi := by
  obtain ⟨⟨s, ⟨δ, hδ⟩⟩, rfl⟩ : ∃ y : ℝ × Icc 0 Real.pi, ((y.1 : AddCircle ℓ), y.2) = x :=
    ⟨((QuotientAddGroup.mk_surjective x.1).choose, x.2),
      Prod.ext (QuotientAddGroup.mk_surjective x.1).choose_spec rfl⟩
  refine ⟨fun h => ?_, fun h => T.orientedLineSet_orientedLine_inter_interior_nonempty h⟩
  refine ⟨hδ.1.lt_of_ne fun h0 => ?_, hδ.2.lt_of_ne fun hπ => ?_⟩
  · have := T.orientedLineSet_orientedLine_inter_interior_eq_empty (s := s) (δ := δ)
      (by rw [← h0, Real.sin_zero])
    exact h.ne_empty this
  · have := T.orientedLineSet_orientedLine_inter_interior_eq_empty (s := s) (δ := δ)
      (by rw [hπ, Real.sin_pi])
    exact h.ne_empty this

/-- The restriction of `Λ` to the phase cylinder, onto the lines meeting the interior. -/
private def restrictedLine :
    T.closedLine ⁻¹' T.interiorLines → T.interiorLines :=
  T.interiorLines.restrictPreimage T.closedLine

private theorem bijective_restrictedLine : Bijective T.restrictedLine := by
  constructor
  · rintro ⟨⟨a, ⟨δ, hδ⟩⟩, hx⟩ ⟨⟨a', ⟨δ', hδ'⟩⟩, hx'⟩ h
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective a
    obtain ⟨s', rfl⟩ := QuotientAddGroup.mk_surjective a'
    have hIoo := (T.mem_preimage_closedLine_iff _).1 hx
    have h' : T.orientedLine s δ = T.orientedLine s' δ' := congrArg Subtype.val h
    obtain ⟨hss, hδδ⟩ := (T.orientedLine_eq_orientedLine_iff hIoo hδ').1 h'
    subst hδδ
    exact Subtype.ext (Prod.ext hss rfl)
  · rintro ⟨p, hp⟩
    obtain ⟨s, δ, hδ, rfl⟩ := T.exists_orientedLine_eq hp
    exact ⟨⟨((s : AddCircle ℓ), ⟨δ, Ioo_subset_Icc_self hδ⟩),
      (T.mem_preimage_closedLine_iff _).2 hδ⟩, rfl⟩

/-- The phase cylinder as the preimage of the lines meeting the interior. -/
private def phaseCylinderEquiv :
    AddCircle ℓ × Ioo 0 Real.pi ≃ₜ T.closedLine ⁻¹' T.interiorLines where
  toFun x := ⟨(x.1, ⟨x.2, Ioo_subset_Icc_self x.2.property⟩),
    (T.mem_preimage_closedLine_iff _).2 x.2.property⟩
  invFun x := (x.val.1, ⟨x.val.2, (T.mem_preimage_closedLine_iff _).1 x.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- **The phase cylinder is the space of oriented lines meeting the interior.** The map
`Λ(s, δ) = (exp(iδ) τ(s), exp(iδ) τ(s) × γ(s))` is a homeomorphism from `AddCircle ℓ × (0, π)`
onto the set of oriented lines meeting the interior of the region `Ω`. Its inverse sends such a
line to its entry state. -/
def orientedLineHomeomorph :
    AddCircle ℓ × Ioo 0 Real.pi ≃ₜ
      {p : Circle × ℝ // (orientedLineSet p ∩ interior T.region).Nonempty} :=
  T.phaseCylinderEquiv.trans
    ((Equiv.ofBijective _ T.bijective_restrictedLine).toHomeomorphOfContinuousClosed
      (T.continuous_closedLine.restrictPreimage)
      (T.continuous_closedLine.isClosedMap.restrictPreimage _))

@[simp]
theorem coe_orientedLineHomeomorph_apply (s : ℝ) (δ : Ioo 0 Real.pi) :
    (T.orientedLineHomeomorph ((s : AddCircle ℓ), δ) : Circle × ℝ) = T.orientedLine s δ :=
  (rfl)

end ConvexTable

end TauCeti
