/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Projectivization.CoordLine
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle.Canonical
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle.Sum
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# The tangent bundle of projective space along the coordinate line is `𝒪(2) ⊕ 𝒪(1)ᵐ`

Let `𝕜` be a complete nontrivially normed field and `ℓ : ℙ¹ → ℙᵐ⁺¹` the coordinate line
`[v₀ : v₁] ↦ [v₀ : v₁ : 0 : ⋯ : 0]` (`Projectivization.coordLine`). This file proves that the
pullback `ℓ* Tℙᵐ⁺¹` of the tangent bundle is the split bundle `𝒪(2) ⊕ 𝒪(1)ᵐ` on `ℙ¹`
(`Projectivization.twistSumCore (lineTwist m)`, the summand `0` being `𝒪(2)` and the others
`𝒪(1)`), as analytic vector bundles (`Projectivization.coordLineTangentDiffeomorph`). For `𝕜 = ℂ`
this is the holomorphic splitting `ℓ* TℂPⁿ ≅ 𝒪(2) ⊕ 𝒪(1)ⁿ⁻¹`. In every chart, the summand `𝒪(2)`
is the coordinate along the line and the summands `𝒪(1)` are the coordinates normal to it. For
`m = 0` the line is the identity of `ℙ¹`, and the statement is `Tℙ¹ ≅ 𝒪(2)`.

**Coordinates along the line.** For `a ∈ {0, 1}`, the standard affine chart `a` of `ℙᵐ⁺¹` has the
coordinates `vⱼ / vₐ` for `j ≠ a`. On the line its first coordinate is `v_b / vₐ`, for the other
index `b` of the line, and its normal coordinates vanish
(`Projectivization.affineChart_castLE_coordLine`). At a point of the line, the derivative of the
change from the chart `a` to the chart `b ≠ a` is the diagonal matrix `(-t², t, …, t)` with
`t = vₐ / v_b` (`Projectivization.hasFDerivAt_affineChart_castLE_symm_trans`,
`Projectivization.tangentCoordChange_coordLineCenter`). Up to the sign `-1` on the tangent
coordinate, these are the transitions `t²` of `𝒪(2)` and `t` of `𝒪(1)`.

**The isomorphism.** As for the canonical bundle of `ℙ¹`
(`Projectivization.twistEquivCanonicalBundle`), the sign is absorbed by the signs `εₐ` of the
Euler form (`Projectivization.eulerFormSign`): reading a tangent vector of `ℙᵐ⁺¹` at a point of
the line in the chart `a`, and multiplying its tangent coordinate by `εₐ`, gives a vector of
`𝒪(2) ⊕ 𝒪(1)ᵐ` in the frame of the chart `a`, and this does not depend on `a`
(`Projectivization.twistSumCore_coordChange_lineFrameSign_mul`). These fibrewise isomorphisms
(`Projectivization.coordLineTangentEquiv`) are analytic in the trivializations
(`Projectivization.contMDiff_coordLineTangentEquiv`), so they form an analytic diffeomorphism of
total spaces over `ℙ¹`.

Combined with the vanishing `H¹(ℂP¹, 𝒪(k)) = 0` for `k ≥ -1`, the splitting
`ℓ* TℂPⁿ ≅ 𝒪(2) ⊕ 𝒪(1)ⁿ⁻¹` gives `H¹(ℂP¹, ℓ* TℂPⁿ) = 0`: the linearized Cauchy–Riemann operator
along `ℓ` is onto, so `ℓ` is regular as a holomorphic sphere in `ℂPⁿ`.

## Main declarations

* `Projectivization.lineTwist m`: the twists `(2, 1, …, 1)` of `𝒪(2) ⊕ 𝒪(1)ᵐ`.
* `Projectivization.tangentCoordChange_coordLineCenter`: the tangent coordinate changes of
  `ℙᵐ⁺¹` between the charts of the line, at the points of the line.
* `Projectivization.coordLineTangentEquiv`: the fibrewise isomorphisms
  `T_{ℓ x}ℙᵐ⁺¹ ≃ (𝒪(2) ⊕ 𝒪(1)ᵐ)ₓ`.
* `Projectivization.coordLineTangentDiffeomorph`: the analytic diffeomorphism of total spaces
  `ℓ* Tℙᵐ⁺¹ ≃ 𝒪(2) ⊕ 𝒪(1)ᵐ` over `ℙ¹`.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0, §5 and
  Chapter 1, §1 (the tangent bundle of projective space).
* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*, in *Algebraic
  geometry, Santa Cruz 1995*, Proc. Sympos. Pure Math. 62, Part 2, AMS, 1997, Lemma 10 (the
  vanishing of `H¹(C, μ* T_X)` for genus-zero maps to convex targets such as `ℙʳ`).
-/

public noncomputable section

open Bundle Set
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace Projectivization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] (m : ℕ)

/-! ### The tangent coordinate changes along the coordinate line -/

section TangentCoordChange

variable {m}

/-- **The tangent coordinate changes along the line.** At a point `x` of the line in the affine
opens `a ≠ b` of `ℙ¹`, the derivative of the change from the chart `a` to the chart `b` of `ℙᵐ⁺¹`
is the diagonal matrix `(-t², t, …, t)`, for the transition `t = xₐ / x_b` of `𝒪(1)`. -/
theorem tangentCoordChange_coordLineCenter {a b : Fin 2} (hab : a ≠ b) {x : ℙ 𝕜 (Fin 2 → 𝕜)}
    (ha : x ∈ affineOpen a) (hb : x ∈ affineOpen b) :
    tangentCoordChange 𝓘(𝕜, Fin (m + 1) → 𝕜) (coordLineCenter a) (coordLineCenter b)
        (coordLine m x) =
      ContinuousLinearMap.mul 𝕜 (Fin (m + 1) → 𝕜)
        (Fin.cons (-(twistTransition 1 a b x ^ 2)) fun _ ↦ twistTransition 1 a b x) := by
  have hz : x.rep b / x.rep a ≠ 0 :=
    div_ne_zero ((mem_affineOpen_iff b x).1 hb) ((mem_affineOpen_iff a x).1 ha)
  have hd := (hasFDerivAt_affineChart_castLE_symm_trans (m := m) hab hz).fderiv
  rw [PartialEquiv.coe_trans] at hd
  have hchart : tangentCoordChange 𝓘(𝕜, Fin (m + 1) → 𝕜) (coordLineCenter a) (coordLineCenter b)
      (coordLine m x) = fderiv 𝕜 (affineChart (Fin.castLE (Nat.le_add_left 2 m) b) ∘
        (affineChart (Fin.castLE (Nat.le_add_left 2 m) a)).symm)
        (affineChart (Fin.castLE (Nat.le_add_left 2 m) a) (coordLine m x)) := by
    simp [chartAt_coordLineCenter]
  rw [hchart, affineChart_castLE_coordLine hab, hd, twistTransition_def, zpow_one, inv_div]

end TangentCoordChange

/-! ### The frames of `𝒪(2) ⊕ 𝒪(1)ᵐ` -/

section Frame

variable {m}

variable (m) in
/-- The twists `(2, 1, …, 1)` of the split bundle `𝒪(2) ⊕ 𝒪(1)ᵐ` on `ℙ¹`. -/
def lineTwist : Fin (m + 1) → ℤ :=
  Fin.cons 2 fun _ ↦ 1

@[simp]
theorem lineTwist_zero : lineTwist m 0 = 2 :=
  (rfl)

@[simp]
theorem lineTwist_succ (l : Fin m) : lineTwist m l.succ = 1 :=
  (rfl)

/-- The sign `(εₐ, 1, …, 1)` relating the coordinates of a tangent vector in the chart `a` of
`ℙᵐ⁺¹` to those of the corresponding vector of `𝒪(2) ⊕ 𝒪(1)ᵐ` in the frame of the chart `a`:
the tangent coordinate carries the sign `εₐ = eulerFormSign a` of the Euler form, as in the
isomorphism `𝒪(-2) ≃ K_ℙ¹`. -/
def lineFrameSign (a : Fin 2) : Fin (m + 1) → 𝕜 :=
  Fin.cons (eulerFormSign a) 1

@[simp]
theorem lineFrameSign_zero (a : Fin 2) : lineFrameSign (𝕜 := 𝕜) (m := m) a 0 = eulerFormSign a :=
  (rfl)

@[simp]
theorem lineFrameSign_succ (a : Fin 2) (l : Fin m) : lineFrameSign (𝕜 := 𝕜) a l.succ = 1 :=
  (rfl)

/-- The sign of a frame is an involution. -/
theorem lineFrameSign_mul_self (a : Fin 2) :
    lineFrameSign (𝕜 := 𝕜) (m := m) a * lineFrameSign a = 1 := by
  funext l
  refine Fin.cases ?_ (fun l ↦ ?_) l <;> simp [eulerFormSign_mul_self]

/-- **The frames agree.** At a point `x` of the line in the affine opens `a` and `b` of `ℙ¹`,
reading a tangent vector of `ℙᵐ⁺¹` in the chart `a` and multiplying it by the sign of the frame `a`
gives the vector of `𝒪(2) ⊕ 𝒪(1)ᵐ` whose coordinates in the frame `b` are those of the tangent
vector in the chart `b`, multiplied by the sign of the frame `b`. -/
theorem twistSumCore_coordChange_lineFrameSign_mul {a b : Fin 2} {x : ℙ 𝕜 (Fin 2 → 𝕜)}
    (ha : x ∈ affineOpen a) (hb : x ∈ affineOpen b) (w : Fin (m + 1) → 𝕜) :
    (twistSumCore (lineTwist m)).coordChange a b x (lineFrameSign a * w) =
      lineFrameSign b *
        tangentCoordChange 𝓘(𝕜, Fin (m + 1) → 𝕜) (coordLineCenter a) (coordLineCenter b)
          (coordLine m x) w := by
  rcases eq_or_ne a b with rfl | hab
  · rw [tangentCoordChange_self (by rw [extChartAt_source]; exact
        coordLine_mem_chartAt_coordLineCenter_source ha),
      (twistSumCore (lineTwist m)).coordChange_self _ _ (by rwa [twistSumCore_baseSet])]
  rw [tangentCoordChange_coordLineCenter hab ha hb]
  funext l
  have hab' := eulerFormSign_mul_of_ne (𝕜 := 𝕜) hab
  have hb' := eulerFormSign_mul_self (𝕜 := 𝕜) b
  refine Fin.cases ?_ (fun l ↦ ?_) l
  · simp only [twistSumCore_coordChange_apply, lineTwist_zero, Pi.mul_apply, lineFrameSign_zero,
      Fin.cons_zero, ContinuousLinearMap.mul_apply']
    rw [show (2 : ℤ) = 1 + 1 from rfl, twistTransition_add 1 1 ha hb]
    linear_combination (twistTransition 1 a b x * twistTransition 1 a b x * w 0) *
      (eulerFormSign b * hab' - eulerFormSign a * hb')
  · simp

end Frame

/-! ### The isomorphism -/

section Equiv

variable {m}

/-- The bundled analytic coordinate line, along which the tangent bundle of `ℙᵐ⁺¹` is pulled
back. -/
def coordLineContMDiffMap :
    C^ω⟮𝓘(𝕜, Fin 1 → 𝕜), ℙ 𝕜 (Fin 2 → 𝕜); 𝓘(𝕜, Fin (m + 1) → 𝕜), ℙ 𝕜 (Fin (m + 2) → 𝕜)⟯ :=
  ⟨coordLine m, contMDiff_coordLine m ω⟩

/-- The bundled coordinate line is the coordinate line. -/
@[simp]
theorem coe_coordLineContMDiffMap : ⇑(coordLineContMDiffMap (𝕜 := 𝕜) (m := m)) = coordLine m :=
  (rfl)

variable (𝕜 m) in
/-- The pullback `ℓ* Tℙᵐ⁺¹` of the tangent bundle of `ℙᵐ⁺¹` along the coordinate line `ℓ`: its
fibre at `x ∈ ℙ¹` is the tangent space of `ℙᵐ⁺¹` at `ℓ x`. -/
abbrev CoordLineTangentSpace : ℙ 𝕜 (Fin 2 → 𝕜) → Type _ :=
  (coordLineContMDiffMap (𝕜 := 𝕜) (m := m) : ℙ 𝕜 (Fin 2 → 𝕜) → ℙ 𝕜 (Fin (m + 2) → 𝕜)) *ᵖ
    (TangentSpace 𝓘(𝕜, Fin (m + 1) → 𝕜))

/-- The tangent vector of `ℙᵐ⁺¹` at `ℓ x` read in the frame of the preferred chart `a` of `x`:
its coordinates in the chart `a` of `ℙᵐ⁺¹`, with the tangent coordinate multiplied by `εₐ`. -/
private def coordLineTangentMap (x : ℙ 𝕜 (Fin 2 → 𝕜)) :
    (Fin (m + 1) → 𝕜) →L[𝕜] (Fin (m + 1) → 𝕜) :=
  (ContinuousLinearMap.mul 𝕜 (Fin (m + 1) → 𝕜)
    (lineFrameSign ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x))).comp
    (tangentCoordChange 𝓘(𝕜, Fin (m + 1) → 𝕜) (coordLine m x)
      (coordLineCenter ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x)) (coordLine m x))

/-- The inverse of `coordLineTangentMap x`. -/
private def coordLineTangentMapInv (x : ℙ 𝕜 (Fin 2 → 𝕜)) :
    (Fin (m + 1) → 𝕜) →L[𝕜] (Fin (m + 1) → 𝕜) :=
  (tangentCoordChange 𝓘(𝕜, Fin (m + 1) → 𝕜)
      (coordLineCenter ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x)) (coordLine m x)
      (coordLine m x)).comp
    (ContinuousLinearMap.mul 𝕜 (Fin (m + 1) → 𝕜)
      (lineFrameSign ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x)))

private theorem coordLine_mem_inter (x : ℙ 𝕜 (Fin 2 → 𝕜)) :
    coordLine m x ∈ (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜) (coordLine m x)).source ∩
      (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜)
        (coordLineCenter ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x))).source ∩
      (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜) (coordLine m x)).source := by
  have hc := coordLine_mem_chartAt_coordLineCenter_source (𝕜 := 𝕜) (m := m)
    (mem_affineOpen_twistSumCore_indexAt (lineTwist m) x)
  simp only [extChartAt_source]
  exact ⟨⟨mem_chart_source _ _, hc⟩, mem_chart_source _ _⟩

private theorem coordLine_mem_inter' (x : ℙ 𝕜 (Fin 2 → 𝕜)) :
    coordLine m x ∈ (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜)
        (coordLineCenter ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x))).source ∩
      (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜) (coordLine m x)).source ∩
      (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜)
        (coordLineCenter ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x))).source := by
  have h := coordLine_mem_inter (𝕜 := 𝕜) (m := m) x
  exact ⟨⟨h.1.2, h.2⟩, h.1.2⟩

private theorem coordLineTangentMap_coordLineTangentMapInv (x : ℙ 𝕜 (Fin 2 → 𝕜))
    (v : Fin (m + 1) → 𝕜) :
    coordLineTangentMap x (coordLineTangentMapInv x v) = v := by
  simp only [coordLineTangentMap, coordLineTangentMapInv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply']
  rw [tangentCoordChange_comp (coordLine_mem_inter' x), tangentCoordChange_self, ← mul_assoc,
    lineFrameSign_mul_self, one_mul]
  rw [extChartAt_source]
  exact coordLine_mem_chartAt_coordLineCenter_source
    (mem_affineOpen_twistSumCore_indexAt (lineTwist m) x)

private theorem coordLineTangentMapInv_coordLineTangentMap (x : ℙ 𝕜 (Fin 2 → 𝕜))
    (v : Fin (m + 1) → 𝕜) :
    coordLineTangentMapInv x (coordLineTangentMap x v) = v := by
  simp only [coordLineTangentMap, coordLineTangentMapInv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply', ← mul_assoc, lineFrameSign_mul_self, one_mul]
  rw [tangentCoordChange_comp (coordLine_mem_inter x), tangentCoordChange_self]
  rw [extChartAt_source]
  exact mem_chart_source _ _

/-- **The fibres of `ℓ* Tℙᵐ⁺¹ ≅ 𝒪(2) ⊕ 𝒪(1)ᵐ`.** At `x ∈ ℙ¹`, with preferred chart `a`, a tangent
vector of `ℙᵐ⁺¹` at `ℓ x` goes to the vector of `𝒪(2) ⊕ 𝒪(1)ᵐ` whose coordinates in the frame of
the chart `a` are its coordinates in the chart `a` of `ℙᵐ⁺¹`, the tangent coordinate multiplied by
the sign `εₐ` of the Euler form (`Projectivization.coordLineTangentEquiv_apply`). -/
def coordLineTangentEquiv (x : ℙ 𝕜 (Fin 2 → 𝕜)) :
    CoordLineTangentSpace 𝕜 m x ≃L[𝕜]
      (twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).Fiber x :=
  -- Both fibres are the model space `Fin (m + 1) → 𝕜`, by definition.
  ContinuousLinearEquiv.ofContinuousLinearMap (coordLineTangentMap x) (coordLineTangentMapInv x)
    (ContinuousLinearMap.ext (coordLineTangentMap_coordLineTangentMapInv x))
    (ContinuousLinearMap.ext (coordLineTangentMapInv_coordLineTangentMap x))

/-- At `x`, with preferred chart `a`, the image of a tangent vector `v` of `ℙᵐ⁺¹` at `ℓ x` has the
coordinates of `v` in the chart `a` of `ℙᵐ⁺¹`, the tangent coordinate multiplied by `εₐ`. -/
@[simp]
theorem coordLineTangentEquiv_apply (x : ℙ 𝕜 (Fin 2 → 𝕜))
    (v : CoordLineTangentSpace 𝕜 m x) :
    (coordLineTangentEquiv x v : Fin (m + 1) → 𝕜) =
      lineFrameSign ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x) *
        tangentCoordChange 𝓘(𝕜, Fin (m + 1) → 𝕜) (coordLine m x)
          (coordLineCenter ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x))
          (coordLine m x) v :=
  (rfl)

/-- At `x`, with preferred chart `a`, the tangent vector of `ℙᵐ⁺¹` at `ℓ x` corresponding to a
vector of `𝒪(2) ⊕ 𝒪(1)ᵐ` with coordinates `c` in the frame of the chart `a` has the coordinates `c`
in the chart `a` of `ℙᵐ⁺¹`, the tangent coordinate multiplied by `εₐ`. -/
@[simp]
theorem coordLineTangentEquiv_symm_apply (x : ℙ 𝕜 (Fin 2 → 𝕜)) (c : Fin (m + 1) → 𝕜) :
    ((coordLineTangentEquiv x).symm c : Fin (m + 1) → 𝕜) =
      tangentCoordChange 𝓘(𝕜, Fin (m + 1) → 𝕜)
        (coordLineCenter ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x)) (coordLine m x)
        (coordLine m x)
        (lineFrameSign ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x) * c) :=
  (rfl)

/-- **The isomorphism in the trivializations of a chart.** Read in the trivialization of
`𝒪(2) ⊕ 𝒪(1)ᵐ` at `x₀`, with preferred chart `a₀`, the image of a tangent vector `v` of `ℙᵐ⁺¹` at
`ℓ x` is its reading in the chart `a₀` of `ℙᵐ⁺¹`, multiplied by the sign of the frame `a₀`. -/
theorem trivializationAt_coordLineTangentEquiv (x₀ : ℙ 𝕜 (Fin 2 → 𝕜)) {x : ℙ 𝕜 (Fin 2 → 𝕜)}
    (hx : x ∈ affineOpen ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x₀))
    (v : CoordLineTangentSpace 𝕜 m x) :
    (trivializationAt (Fin (m + 1) → 𝕜) (twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).Fiber x₀
        ⟨x, coordLineTangentEquiv x v⟩).2 =
      lineFrameSign ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x₀) *
        tangentCoordChange 𝓘(𝕜, Fin (m + 1) → 𝕜) (coordLine m x)
          (coordLineCenter ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x₀))
          (coordLine m x) v := by
  have ha := mem_affineOpen_twistSumCore_indexAt (𝕜 := 𝕜) (lineTwist m) x
  rw [twistSumCore_trivializationAt_snd (lineTwist m) x₀ x (coordLineTangentEquiv x v),
    coordLineTangentEquiv_apply]
  refine (twistSumCore_coordChange_lineFrameSign_mul ha hx _).trans ?_
  have hsrc : coordLine m x ∈ (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜) (coordLine m x)).source ∩
      (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜)
        (coordLineCenter ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x))).source ∩
      (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜)
        (coordLineCenter ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x₀))).source := by
    simp only [extChartAt_source]
    exact ⟨⟨mem_chart_source _ _, coordLine_mem_chartAt_coordLineCenter_source ha⟩,
      coordLine_mem_chartAt_coordLineCenter_source hx⟩
  -- The tangent space at `ℓ x` is the model space `Fin (m + 1) → 𝕜`, by definition.
  let v' : Fin (m + 1) → 𝕜 := v
  exact congrArg (lineFrameSign _ * ·) (tangentCoordChange_comp (v := v') hsrc)

/-- The change from the chart of `ℓ x₀` to the chart `a` of `ℙᵐ⁺¹`, read along the line, is
analytic near `x₀` when `x₀` lies in the affine open `a` of `ℙ¹`. -/
private theorem contMDiffAt_tangentCoordChange_coordLine {x₀ : ℙ 𝕜 (Fin 2 → 𝕜)} {a : Fin 2}
    (ha : x₀ ∈ affineOpen a) :
    ContMDiffAt 𝓘(𝕜, Fin 1 → 𝕜) 𝓘(𝕜, (Fin (m + 1) → 𝕜) →L[𝕜] Fin (m + 1) → 𝕜) ω
      (fun x ↦ tangentCoordChange 𝓘(𝕜, Fin (m + 1) → 𝕜) (coordLine m x₀) (coordLineCenter a)
        (coordLine m x))
      x₀ :=
  (TauCeti.Manifold.contMDiffAt_tangentCoordChange (by
    rw [extChartAt_source]; exact coordLine_mem_chartAt_coordLineCenter_source ha)).comp x₀
    (contMDiff_coordLine m ω x₀)

/-- **The isomorphism `ℓ* Tℙᵐ⁺¹ ≃ 𝒪(2) ⊕ 𝒪(1)ᵐ` is analytic.** The map of total spaces given by the
fibrewise isomorphisms `Projectivization.coordLineTangentEquiv` is analytic; for `𝕜 = ℂ` it is
holomorphic. -/
theorem contMDiff_coordLineTangentEquiv :
    ContMDiff (𝓘(𝕜, Fin 1 → 𝕜).prod 𝓘(𝕜, Fin (m + 1) → 𝕜))
      (𝓘(𝕜, Fin 1 → 𝕜).prod 𝓘(𝕜, Fin (m + 1) → 𝕜)) ω
      (fun q : TotalSpace (Fin (m + 1) → 𝕜) (CoordLineTangentSpace 𝕜 m) ↦
        TotalSpace.mk' (Fin (m + 1) → 𝕜)
          (E := (twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).Fiber) q.proj
          (coordLineTangentEquiv q.proj q.snd)) := by
  intro q₀
  have ha₀ := mem_affineOpen_twistSumCore_indexAt (𝕜 := 𝕜) (lineTwist m) q₀.proj
  -- The tangent vector read in the chart of `ℓ x₀` is analytic on the total space.
  have hT := (Bundle.contMDiffAt_totalSpace_iff.1
    (Bundle.Pullback.contMDiff_lift (E := TangentSpace 𝓘(𝕜, Fin (m + 1) → 𝕜))
      (coordLineContMDiffMap (𝕜 := 𝕜) (m := m))
      (coordLineContMDiffMap (𝕜 := 𝕜) (m := m)).contMDiff q₀)).2
  -- In the trivializations at `x₀`, the isomorphism is this reading followed by the analytic change
  -- to the chart `a₀` and the sign of the frame `a₀`.
  have hfib := (ContinuousLinearMap.mul 𝕜 (Fin (m + 1) → 𝕜)
      (lineFrameSign ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt
        q₀.proj))).contMDiff.contMDiffAt.comp q₀
      (((contMDiffAt_tangentCoordChange_coordLine (m := m) ha₀).comp q₀
        (contMDiffAt_proj _)).clm_apply hT)
  refine Bundle.contMDiffAt_totalSpace_iff.2 ⟨contMDiffAt_proj _, ?_⟩
  have hline : Continuous (coordLine (𝕜 := 𝕜) m) :=
    (coordLineContMDiffMap (𝕜 := 𝕜) (m := m)).contMDiff.continuous
  have hnhds : ∀ᶠ q : TotalSpace (Fin (m + 1) → 𝕜) (CoordLineTangentSpace 𝕜 m) in nhds q₀,
      q.proj ∈ affineOpen ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt q₀.proj) ∩
        coordLine m ⁻¹' (chartAt (Fin (m + 1) → 𝕜) (coordLine (𝕜 := 𝕜) m q₀.proj)).source :=
    (FiberBundle.continuous_proj (Fin (m + 1) → 𝕜)
      (CoordLineTangentSpace 𝕜 m)).continuousAt.preimage_mem_nhds
        (((isOpen_affineOpen _).inter ((chartAt _ _).open_source.preimage hline)).mem_nhds
          ⟨ha₀, mem_chart_source _ _⟩)
  refine hfib.congr_of_eventuallyEq (hnhds.mono fun ⟨p, v⟩ hq ↦ ?_)
  refine (trivializationAt_coordLineTangentEquiv q₀.proj hq.1 v).trans ?_
  have hsrc : coordLine m p ∈ (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜) (coordLine m p)).source ∩
      (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜) (coordLine m q₀.proj)).source ∩
      (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜) (coordLineCenter
        ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt q₀.proj))).source := by
    simp only [extChartAt_source]
    exact ⟨⟨mem_chart_source _ _, hq.2⟩, coordLine_mem_chartAt_coordLineCenter_source hq.1⟩
  -- The tangent space at `ℓ p` is the model space `Fin (m + 1) → 𝕜`, by definition, and the
  -- trivialization of the tangent bundle at `ℓ x₀` reads a vector at `ℓ p` by the change from the
  -- chart of `ℓ p` to the chart of `ℓ x₀`.
  let v' : Fin (m + 1) → 𝕜 := v
  have htriv : (trivializationAt (Fin (m + 1) → 𝕜) (TangentSpace 𝓘(𝕜, Fin (m + 1) → 𝕜))
      (Pullback.lift (⇑(coordLineContMDiffMap (𝕜 := 𝕜) (m := m))) q₀).proj
      (Pullback.lift (⇑(coordLineContMDiffMap (𝕜 := 𝕜) (m := m))) ⟨p, v⟩)).2 =
        tangentCoordChange 𝓘(𝕜, Fin (m + 1) → 𝕜) (coordLine m p) (coordLine m q₀.proj)
          (coordLine m p) v' :=
    TangentBundle.trivializationAt_snd_eq_tangentCoordChange (x := coordLine m q₀.proj)
      (y := coordLine m p) v'
  simp only [Function.comp_apply, ContinuousLinearMap.mul_apply']
  rw [htriv]
  exact congrArg (lineFrameSign _ * ·) (tangentCoordChange_comp (v := v') hsrc).symm

variable [CompleteSpace 𝕜]

/-- **The tangent bundle of `ℙᵐ⁺¹` along the coordinate line is `𝒪(2) ⊕ 𝒪(1)ᵐ`.** The fibrewise
isomorphisms `Projectivization.coordLineTangentEquiv` form a `C^n` diffeomorphism, for every `n` and
hence analytic at `n = ω`, from the total space of the pullback `ℓ* Tℙᵐ⁺¹` of the tangent bundle
along the coordinate line `ℓ` to the total space of the split bundle `𝒪(2) ⊕ 𝒪(1)ᵐ`, over the
identity of `ℙ¹`. For `𝕜 = ℂ` it is a biholomorphism of total spaces. -/
def coordLineTangentDiffeomorph (n : ℕ∞ω) :
    TotalSpace (Fin (m + 1) → 𝕜)
        (CoordLineTangentSpace 𝕜 m) ≃ₘ^n⟮𝓘(𝕜, Fin 1 → 𝕜).prod 𝓘(𝕜, Fin (m + 1) → 𝕜),
        𝓘(𝕜, Fin 1 → 𝕜).prod 𝓘(𝕜, Fin (m + 1) → 𝕜)⟯
      TotalSpace (Fin (m + 1) → 𝕜) (twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).Fiber :=
  TauCeti.bundleDiffeomorph coordLineTangentEquiv (contMDiff_coordLineTangentEquiv.of_le le_top)

@[simp]
theorem coordLineTangentDiffeomorph_apply (n : ℕ∞ω)
    (q : TotalSpace (Fin (m + 1) → 𝕜)
      (CoordLineTangentSpace 𝕜 m)) :
    coordLineTangentDiffeomorph n q = ⟨q.proj, coordLineTangentEquiv q.proj q.snd⟩ :=
  TauCeti.bundleDiffeomorph_apply _ _ q

@[simp]
theorem coordLineTangentDiffeomorph_symm_apply (n : ℕ∞ω)
    (q : TotalSpace (Fin (m + 1) → 𝕜) (twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).Fiber) :
    (coordLineTangentDiffeomorph n).symm q = ⟨q.proj, (coordLineTangentEquiv q.proj).symm q.snd⟩ :=
  TauCeti.bundleDiffeomorph_symm_apply _ _ q

/-- The isomorphism `ℓ* Tℙᵐ⁺¹ ≃ 𝒪(2) ⊕ 𝒪(1)ᵐ` lies over the identity of `ℙ¹`. -/
theorem proj_coordLineTangentDiffeomorph (n : ℕ∞ω)
    (q : TotalSpace (Fin (m + 1) → 𝕜)
      (CoordLineTangentSpace 𝕜 m)) :
    (coordLineTangentDiffeomorph n q).proj = q.proj := by
  simp

end Equiv

end Projectivization
