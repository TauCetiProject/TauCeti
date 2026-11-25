/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.Continuous
public import TauCeti.Dynamics.Billiard.Inverse

/-!
# Oriented-line coordinates of billiard states

Let `χ` be an arclength parametrization of the boundary of a strictly convex billiard table
(`TauCeti.StrictConvexBilliardTable`) in an oriented Euclidean plane `E`, with period `L` and area
form `ω`. An oriented line of `E` is represented by a pair `(e, c)` of a unit vector `e`, its
direction, and a real number `c`: the line `{z | ω(e, z) = c}` oriented by `e`. Reversing the
orientation sends `(e, c)` to `-(e, c) = (-e, -c)`, the same point set.

A collision state `(s, v)` of the strip `ℝ × (-1, 1)` determines the oriented line along which the
ball leaves `χ(s)`:

`Λ(s, v) = (u, ω(u, χ(s)))`, where `u = outgoingDir s v`

(`TauCeti.StrictConvexBilliardTable.orientedLine`). It contains `χ(s)` and the next collision point
`χ(t)` (`TauCeti.StrictConvexBilliardTable.areaForm_orientedLine_fst_apply_nextParam`), it is
continuous (`TauCeti.StrictConvexBilliardTable.continuous_orientedLine`), and it is `L`-periodic in
`s` (`TauCeti.StrictConvexBilliardTable.orientedLine_add_period`).

* **Injectivity.** Two states of the strip have the same oriented line exactly when they have the
  same base point `χ(s)` and the same tangential component
  (`TauCeti.StrictConvexBilliardTable.orientedLine_eq_orientedLine_iff`). A second state on the
  same oriented line would have its base point on the chord from `χ(s)`, so at the next collision
  point `χ(t)`, where the direction points out of the table, while every outgoing direction points
  into it.
* **Time reversal reverses the line.** With `ι(s, v) = (s, -v)` and the next-collision map `B`,
  `Λ ∘ ι ∘ B = -Λ` on the strip
  (`TauCeti.StrictConvexBilliardTable.orientedLine_nextParam_neg_nextTangential`): the reversed
  state at the next collision point leaves along `-u` from a point of the same line.

That `Λ` is a homeomorphism from the space of collision states onto the open set of oriented lines
meeting the interior of the table is not proved here.

## References

* M. Bialy and A. E. Mironov, *The Birkhoff–Poritsky conjecture for centrally-symmetric billiard
  tables*, Ann. of Math. 196 (2022), Section 2.
-/

public section

noncomputable section

open Function Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (Module.finrank ℝ E = 2)]

namespace StrictConvexBilliardTable

variable {o : Orientation ℝ E (Fin 2)} (χ : StrictConvexBilliardTable o)

/-- The **oriented line** of a collision state `(s, v)`: the pair `(u, ω(u, χ(s)))` of the
outgoing direction `u` and the value of the area form `ω(u, ·)` on the line, which represents the
line `{z | ω(u, z) = ω(u, χ(s))}` through `χ(s)` oriented by `u`. -/
def orientedLine (s v : ℝ) : E × ℝ :=
  (χ.outgoingDir s v, o.areaForm (χ.outgoingDir s v) (χ s))

theorem orientedLine_def (s v : ℝ) :
    χ.orientedLine s v = (χ.outgoingDir s v, o.areaForm (χ.outgoingDir s v) (χ s)) :=
  (rfl)

@[simp]
theorem orientedLine_fst (s v : ℝ) : (χ.orientedLine s v).1 = χ.outgoingDir s v :=
  (rfl)

@[simp]
theorem orientedLine_snd (s v : ℝ) :
    (χ.orientedLine s v).2 = o.areaForm (χ.outgoingDir s v) (χ s) :=
  (rfl)

/-- The next collision point lies on the oriented line of the state. -/
theorem areaForm_orientedLine_fst_apply_nextParam {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    o.areaForm (χ.orientedLine s v).1 (χ (χ.nextParam s v)) = (χ.orientedLine s v).2 := by
  have h := χ.areaForm_outgoingDir_sub_nextParam (s := s) hv
  rw [map_sub, sub_eq_zero] at h
  exact h

theorem continuous_orientedLine : Continuous fun x : ℝ × ℝ ↦ χ.orientedLine x.1 x.2 :=
  χ.continuous_outgoingDir.prodMk <| by
    simpa [Orientation.areaForm'_apply] using
      o.areaForm'.continuous₂.comp₂ χ.continuous_outgoingDir (χ.continuous.comp continuous_fst)

@[simp]
theorem orientedLine_add_period (s v : ℝ) :
    χ.orientedLine (s + χ.period) v = χ.orientedLine s v := by
  rw [orientedLine_def, orientedLine_def, χ.outgoingDir_add_period, χ.periodic]

/-- **Time reversal reverses the oriented line**: the state `(t, -w)` at the next collision point
with reversed tangential component has the oriented line of `(s, v)` with the reverse orientation,
`Λ(ι(B(s, v))) = -Λ(s, v)`. -/
theorem orientedLine_nextParam_neg_nextTangential {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    χ.orientedLine (χ.nextParam s v) (-χ.nextTangential s v) = -χ.orientedLine s v := by
  have h := χ.areaForm_orientedLine_fst_apply_nextParam (s := s) hv
  simp only [orientedLine_fst, orientedLine_snd] at h
  rw [orientedLine_def, χ.outgoingDir_nextParam_neg_nextTangential hv, map_neg,
    LinearMap.neg_apply, h, Prod.neg_mk, orientedLine_def]

/-- States with the same base point and the same tangential component have the same oriented
line. -/
theorem orientedLine_eq_orientedLine_of_apply_eq {s s' : ℝ} (h : χ s = χ s') (v : ℝ) :
    χ.orientedLine s v = χ.orientedLine s' v := by
  rw [orientedLine_def, orientedLine_def, χ.outgoingDir_eq_outgoingDir_of_apply_eq h, h]

/-- **The oriented line determines the state.** A state `(s, v)` of the strip and any state
`(s', v')` have the same oriented line exactly when they have the same base point and the same
tangential component. Only `v` needs to lie in `(-1, 1)`: for `v' = ±1` the direction is tangent
at `χ(s')`, and for `|v'| > 1` it is not a unit vector, so such a state never shares the line of
`(s, v)`. -/
theorem orientedLine_eq_orientedLine_iff {s v s' v' : ℝ} (hv : v ∈ Ioo (-1) 1) :
    χ.orientedLine s v = χ.orientedLine s' v' ↔ χ s = χ s' ∧ v = v' := by
  refine ⟨fun h ↦ ?_, fun ⟨hs, hvv⟩ ↦ ?_⟩
  · have he : χ.outgoingDir s v = χ.outgoingDir s' v' := congrArg Prod.fst h
    have hc := congrArg Prod.snd h
    simp only [orientedLine_snd, ← he] at hc
    have hss : χ s = χ s' := by
      by_contra hne
      -- The representative `t ∈ [s, s + L)` of `s'` is the next collision parameter.
      set t := toIcoMod χ.period_pos s s' with ht_def
      have hts : χ t = χ s' := by
        rw [ht_def, ← self_sub_toIcoDiv_zsmul]
        exact χ.periodic.sub_zsmul_eq _
      have htI : t ∈ Ioo s (s + χ.period) :=
        ⟨(toIcoMod_mem_Ico χ.period_pos s s').1.lt_of_ne
          fun hst ↦ hne ((congrArg χ hst).trans hts), (toIcoMod_mem_Ico χ.period_pos s s').2⟩
      have ht : t = χ.nextParam s v := χ.eq_nextParam_of_areaForm_eq_zero hv htI <| by
        rw [hts, map_sub, hc, sub_self]
      -- At the next collision point the direction points out of the table, at `s'` into it.
      have hout := χ.areaForm_deriv_nextParam_outgoingDir_neg (s := s) hv
      rw [← ht, χ.deriv_eq_deriv_of_apply_eq hts, he, areaForm_deriv_outgoingDir] at hout
      exact absurd hout (not_lt.2 (Real.sqrt_nonneg _))
    refine ⟨hss, ?_⟩
    rw [← χ.inner_deriv_outgoingDir s v, he, χ.deriv_eq_deriv_of_apply_eq hss,
      inner_deriv_outgoingDir]
  · rw [χ.orientedLine_eq_orientedLine_of_apply_eq hs, hvv]

end StrictConvexBilliardTable

end TauCeti
