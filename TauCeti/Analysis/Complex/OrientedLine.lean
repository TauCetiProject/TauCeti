/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import TauCeti.Analysis.Complex.Circle.Basic

/-!
# Oriented lines of the complex plane

An oriented line of the plane `ℂ` is represented by a pair `(e, c) ∈ Circle × ℝ`: the line
`{z | e × z = c}` (`TauCeti.orientedLineSet`), oriented by its direction `e`, where
`a × b = Im (conj a * b)`. The line through `z` with direction `e` is `(e, e × z)`
(`TauCeti.orientedLineThrough`), and:

* `TauCeti.orientedLineSet_eq_range`: the line `(e, c)` is `{z + t e : t ∈ ℝ}` for any of its
  points `z`;
* `TauCeti.orientedLineThrough_eq_iff`: two (direction, point) pairs give the same oriented line
  exactly when the directions agree and the points differ by a multiple of the direction;
* `TauCeti.orientedLineSet_neg`, `TauCeti.orientedLineSet_eq_orientedLineSet_iff`: reversing the
  orientation, `(e, c) ↦ (−e, −c)`, keeps the point set, and two representations have the same
  point set exactly when they are equal or opposite;
* `TauCeti.isOpen_setOf_orientedLineSet_inter_nonempty`: the oriented lines meeting an open set
  form an open set, and `TauCeti.neg_mem_setOf_orientedLineSet_inter_nonempty_iff`: reversing the
  orientation preserves the oriented lines meeting any set.
-/

public section

noncomputable section

open Set Complex
open scoped ComplexConjugate

namespace TauCeti

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
    z ∈ orientedLineSet (orientedLineThrough e z) := by
  rw [mem_orientedLineSet, orientedLineThrough_def]

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
    rw [mem_orientedLineSet, Circle.im_conj_mul_add_smul, hz]

/-- Two (direction, point) pairs give the same oriented line exactly when the directions agree and
the points differ by a real multiple of the direction: the oriented lines through `z` with
direction `e` and through `z'` with direction `e'` agree exactly when `e = e'` and
`z' = z + t e` for some real `t`. -/
theorem orientedLineThrough_eq_iff {e e' : Circle} {z z' : ℂ} :
    orientedLineThrough e z = orientedLineThrough e' z' ↔
      e = e' ∧ ∃ t : ℝ, z' = z + t • (e : ℂ) := by
  constructor
  · intro h
    have he : e = e' := congrArg Prod.fst h
    subst he
    have hz' : z' ∈ orientedLineSet (orientedLineThrough e z) := by
      rw [h]
      exact mem_orientedLineSet_orientedLineThrough e z'
    rw [orientedLineSet_eq_range (mem_orientedLineSet_orientedLineThrough e z)] at hz'
    obtain ⟨t, ht⟩ := hz'
    exact ⟨rfl, t, ht.symm⟩
  · rintro ⟨rfl, t, rfl⟩
    rw [orientedLineThrough_def, orientedLineThrough_def, Circle.im_conj_mul_add_smul]

/-- **Reversing the orientation** `(e, c) ↦ (−e, −c)` keeps the point set of the line. -/
@[simp]
theorem orientedLineSet_neg (p : Circle × ℝ) : orientedLineSet (-p) = orientedLineSet p := by
  ext z
  simp only [mem_orientedLineSet, Prod.fst_neg, Prod.snd_neg, Circle.coe_neg, map_neg, neg_mul,
    neg_im, neg_inj]

/-- A point of the line `(e, c)`: `c i e`. -/
theorem smul_I_mul_mem_orientedLineSet (p : Circle × ℝ) :
    p.2 • (I * (p.1 : ℂ)) ∈ orientedLineSet p :=
  mem_orientedLineSet.2 (Circle.im_conj_mul_smul_I_mul p.1 p.2)

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
    rcases (Circle.im_coe_eq_zero_iff u).1 huim with hu1 | hu1
    · have he : q.1 = p.1 := Circle.ext (by rw [hpe, hu1, Circle.coe_one, mul_one])
      refine Or.inl (Prod.ext he ?_)
      rw [← hz, he, Circle.im_conj_mul_smul_I_mul]
    · have he : q.1 = -p.1 :=
        Circle.ext (by rw [Circle.coe_neg, hpe, hu1, Circle.coe_neg, Circle.coe_one]; ring)
      refine Or.inr (Prod.ext he ?_)
      have hz' : z = (-p.2) • (I * ((-p.1 : Circle) : ℂ)) := by
        simp only [z, Circle.coe_neg, neg_smul, smul_neg, mul_neg, neg_neg]
      rw [← hz, he, Prod.snd_neg, hz', Circle.im_conj_mul_smul_I_mul]
  · rintro (rfl | rfl)
    · rfl
    · exact (orientedLineSet_neg p).symm

/-- Reversing the orientation `(e, c) ↦ (−e, −c)` preserves the oriented lines meeting `U`. -/
theorem neg_mem_setOf_orientedLineSet_inter_nonempty_iff {U : Set ℂ} {p : Circle × ℝ} :
    -p ∈ {q : Circle × ℝ | (orientedLineSet q ∩ U).Nonempty} ↔
      p ∈ {q : Circle × ℝ | (orientedLineSet q ∩ U).Nonempty} := by
  rw [mem_ofPred_eq, mem_ofPred_eq, orientedLineSet_neg]

/-- **The lines meeting an open set form an open set.** -/
theorem isOpen_setOf_orientedLineSet_inter_nonempty {U : Set ℂ} (hU : IsOpen U) :
    IsOpen {p : Circle × ℝ | (orientedLineSet p ∩ U).Nonempty} := by
  refine isOpen_iff_mem_nhds.2 fun p ⟨z₀, hz₀, hU₀⟩ => ?_
  -- If `z₀ ∈ U` lies on the line `(e, c)`, then `z₀ + (c' − e' × z₀) i e'` lies on the nearby
  -- line `(e', c')`, close to `z₀`.
  set f : Circle × ℝ → ℂ := fun q => z₀ + (q.2 - (conj (q.1 : ℂ) * z₀).im) • (I * (q.1 : ℂ))
  have hf : Continuous f := by
    simp only [f, real_smul]
    fun_prop
  have hfp : f p = z₀ := by
    simp only [f]
    rw [hz₀, sub_self, zero_smul, add_zero]
  have hmem (q : Circle × ℝ) : f q ∈ orientedLineSet q := by
    rw [mem_orientedLineSet, mul_add, add_im, Circle.im_conj_mul_smul_I_mul, add_sub_cancel]
  filter_upwards [hf.continuousAt.preimage_mem_nhds (hfp ▸ hU.mem_nhds hU₀)] with q hq
  exact ⟨f q, hmem q, hq⟩

end TauCeti
