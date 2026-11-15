/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Positive.FunctionalCalculus
public import TauCeti.Geometry.Symplectic.AlmostComplex.Topology

/-!
# The unitary frame of a compatible complex structure

Let `ω` be a symplectic form on a finite-dimensional real inner product space `V` whose inner
product is the metric of an `ω`-compatible complex structure `J₀`, that is
`⟪u, v⟫ = ω(u, J₀ v)`; for instance `V = ℂⁿ` with `J₀ = i` and `ω = Im ⟪·, ·⟫`. Every other
`ω`-compatible complex structure `J` is conjugate to `J₀` by a symplectic isomorphism, and there
is a canonical choice:

`Φ = √(-J J₀)`,

the positive square root, for the functional calculus of the inner product, of the operator
`Q = -J J₀`. Here `Q` is symmetric and positive definite because `⟪Q u, u⟫ = ω(J₀ u, J J₀ u)`, and
`Q J₀ Q = J₀`, so conjugation by the orthogonal map `J₀` inverts `Q`. Uniqueness of positive square
roots carries this to `Φ`:

* `Φ J₀ Φ = J₀` (`AlmostComplexStructure.unitaryFrame_mul_mul_self`), so `Φ` is symplectic,
  `ω(Φ u, Φ v) = ω(u, v)` (`AlmostComplexStructure.apply_unitaryFrame_unitaryFrame`);
* `J Φ = Φ J₀` (`AlmostComplexStructure.mul_unitaryFrame`), since `J = Q J₀ = Φ² J₀`;
* hence `Φ` is an isometry from `⟪·, ·⟫ = ω(·, J₀ ·)` to the metric `ω(·, J ·)` of `J`
  (`AlmostComplexStructure.associatedBilinForm_unitaryFrame_unitaryFrame`).

So `Φ` is a *unitary frame* of `(V, ω, J)` modelled on `(V, ω, J₀)`. Among positive operators it
is characterized by the two identities `Φ J₀ Φ = J₀` and `J Φ = Φ J₀`
(`AlmostComplexStructure.eq_unitaryFrame_iff`), and `J₀` has the frame `1`. Being given by the
functional calculus, it involves no choice of basis, and it depends smoothly on `J`
(`ContDiff.unitaryFrame`). Along a smooth loop of compatible structures `J_t`, for example the
almost complex structures along a Hamiltonian orbit, the frames `Φ_t` form a smooth loop of
symplectic isomorphisms with `J_t Φ_t = Φ_t J₀`: a unitary trivialization along the loop, in
which every `J_t` becomes the constant `J₀`.

## Main definitions

* `TauCeti.AlmostComplexStructure.unitaryFrame J₀ J`: the operator `√(-J J₀)`.

## Main results

* `TauCeti.AlmostComplexStructure.isStrictlyPositive_neg_mul`: `Q = -J J₀` is positive definite.
* `TauCeti.AlmostComplexStructure.isStrictlyPositive_unitaryFrame`: `Φ` is positive definite, and
  `TauCeti.AlmostComplexStructure.unitaryFrame_mul_self`: `Φ² = Q`.
* `TauCeti.AlmostComplexStructure.unitaryFrame_mul_mul_self`: `Φ J₀ Φ = J₀`.
* `TauCeti.AlmostComplexStructure.mul_unitaryFrame` and
  `TauCeti.AlmostComplexStructure.apply_unitaryFrame_apply`: `J Φ = Φ J₀`.
* `TauCeti.AlmostComplexStructure.apply_unitaryFrame_unitaryFrame`: `ω(Φ u, Φ v) = ω(u, v)`.
* `TauCeti.AlmostComplexStructure.associatedBilinForm_unitaryFrame_unitaryFrame`:
  `ω(Φ u, J Φ v) = ⟪u, v⟫`.
* `TauCeti.AlmostComplexStructure.eq_unitaryFrame_iff`: the characterization among positive
  operators.
* `ContDiff.unitaryFrame`: smooth families of compatible structures have smooth frames.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 2.5 (compatible complex structures and the polar decomposition
  `J = J₀ Q`).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2 (unitary trivializations along periodic orbits).
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace TauCeti

namespace AlmostComplexStructure

variable {V : Type*} [NormedAddCommGroup V]

section Algebra

variable [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- `Q = -J J₀` satisfies `Q J₀ Q = J₀`, so that conjugation by `J₀` inverts `Q`. -/
private theorem neg_mul_mul_neg_mul (J₀ J : AlmostComplexStructure V) :
    -(LinearMap.toContinuousLinearMap J.toLinearMap *
        LinearMap.toContinuousLinearMap J₀.toLinearMap) *
      LinearMap.toContinuousLinearMap J₀.toLinearMap *
      -(LinearMap.toContinuousLinearMap J.toLinearMap *
        LinearMap.toContinuousLinearMap J₀.toLinearMap) =
      LinearMap.toContinuousLinearMap J₀.toLinearMap := by
  have h := toContinuousLinearMap_mul_self J
  have h₀ := toContinuousLinearMap_mul_self J₀
  set j := LinearMap.toContinuousLinearMap J.toLinearMap
  set j₀ := LinearMap.toContinuousLinearMap J₀.toLinearMap
  calc -(j * j₀) * j₀ * -(j * j₀) = j * (j₀ * j₀) * (j * j₀) := by noncomm_ring
    _ = j₀ := by rw [h₀, mul_neg_one, neg_mul, ← mul_assoc, h, neg_mul, one_mul, neg_neg]

/-- `J = Q J₀` for `Q = -J J₀`. -/
private theorem neg_mul_mul (J₀ J : AlmostComplexStructure V) :
    -(LinearMap.toContinuousLinearMap J.toLinearMap *
        LinearMap.toContinuousLinearMap J₀.toLinearMap) *
      LinearMap.toContinuousLinearMap J₀.toLinearMap =
      LinearMap.toContinuousLinearMap J.toLinearMap := by
  rw [neg_mul, mul_assoc, toContinuousLinearMap_mul_self, mul_neg_one, neg_neg]

end Algebra

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {ω : SymplecticForm V}
  {J₀ J : AlmostComplexStructure V}

/-- The **unitary frame** of a complex structure `J` modelled on `J₀`: the positive square root
`Φ = √(-J J₀)`. When the inner product of `V` is the metric `ω(·, J₀ ·)` of an `ω`-compatible
`J₀` and `J` is `ω`-compatible, it is a symplectic isomorphism with `J Φ = Φ J₀`
(`AlmostComplexStructure.mul_unitaryFrame`,
`AlmostComplexStructure.apply_unitaryFrame_unitaryFrame`). -/
def unitaryFrame (J₀ J : AlmostComplexStructure V) : V →L[ℝ] V :=
  CFC.sqrt (-(LinearMap.toContinuousLinearMap J.toLinearMap *
    LinearMap.toContinuousLinearMap J₀.toLinearMap))

/-- The defining formula of the unitary frame. -/
theorem unitaryFrame_def (J₀ J : AlmostComplexStructure V) :
    J₀.unitaryFrame J = CFC.sqrt (-(LinearMap.toContinuousLinearMap J.toLinearMap *
      LinearMap.toContinuousLinearMap J₀.toLinearMap)) :=
  (rfl)

/-- The unitary frame of `J₀` modelled on itself is the identity. -/
@[simp]
theorem unitaryFrame_self (J₀ : AlmostComplexStructure V) : J₀.unitaryFrame J₀ = 1 := by
  rw [unitaryFrame_def, toContinuousLinearMap_mul_self, neg_neg, CFC.sqrt_one]

/-- The unitary frame is a positive operator. -/
theorem unitaryFrame_nonneg (J₀ J : AlmostComplexStructure V) : 0 ≤ J₀.unitaryFrame J :=
  CFC.sqrt_nonneg _

section Compatible

variable (hJ₀ : ∀ u v, ω u (J₀ v) = ⟪u, v⟫_ℝ) (hJ : ω.Compatible J)
include hJ₀

omit [FiniteDimensional ℝ V] in
/-- If the inner product is the metric `ω(·, J₀ ·)`, then `ω(u, v) = -⟪u, J₀ v⟫`. -/
private theorem apply_eq_neg_inner (u v : V) : ω u v = -⟪u, J₀ v⟫_ℝ := by
  have h := hJ₀ u (J₀ v)
  rw [apply_apply] at h
  simp only [map_neg] at h
  linarith

omit [FiniteDimensional ℝ V] in
/-- If the inner product is the metric `ω(·, J₀ ·)`, then `J₀` is skew-adjoint. -/
private theorem inner_apply_left (u v : V) : ⟪J₀ u, v⟫_ℝ = -⟪u, J₀ v⟫_ℝ := by
  rw [real_inner_comm, ← hJ₀, apply_apply, ← apply_eq_neg_inner hJ₀ u v]
  simp only [map_neg]
  linarith [ω.neg_eq u v]

/-- If the inner product is the metric `ω(·, J₀ ·)`, then the adjoint of `J₀` is `-J₀ = J₀⁻¹`: it
is a unitary element of the operator algebra. -/
private theorem star_toContinuousLinearMap :
    star (LinearMap.toContinuousLinearMap J₀.toLinearMap) =
      -LinearMap.toContinuousLinearMap J₀.toLinearMap := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun u v ↦ ?_).symm
  have h := inner_apply_left hJ₀ u v
  simp only [_root_.neg_apply, inner_neg_left,
    LinearMap.coe_toContinuousLinearMap'] at h ⊢
  linarith

include hJ in
/-- The operator `Q = -J J₀` is positive definite: `⟪Q u, u⟫ = ω(J₀ u, J J₀ u)`. -/
theorem isStrictlyPositive_neg_mul :
    IsStrictlyPositive (-(LinearMap.toContinuousLinearMap J.toLinearMap *
      LinearMap.toContinuousLinearMap J₀.toLinearMap)) := by
  -- `⟪Q u, v⟫ = ω(J₀ u, J J₀ v)`, which is symmetric in `u` and `v` and positive on the diagonal.
  have hQ (u v : V) : ⟪(-(LinearMap.toContinuousLinearMap J.toLinearMap *
      LinearMap.toContinuousLinearMap J₀.toLinearMap)) u, v⟫_ℝ = ω (J₀ u) (J (J₀ v)) := by
    have h₁ := hJ₀ (J (J₀ u)) v
    have h₂ := hJ.invariant.apply_add_apply_eq_zero (J₀ u) (J₀ v)
    simp only [_root_.neg_apply, mul_apply_eq_comp,
      inner_neg_left, LinearMap.coe_toContinuousLinearMap'] at h₁ h₂ ⊢
    linarith
  refine ((isUnit_toContinuousLinearMap J).mul
    (isUnit_toContinuousLinearMap J₀)).neg.isStrictlyPositive ?_
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff]
  refine ⟨fun u v ↦ ?_, fun u ↦ ?_⟩
  · rw [ContinuousLinearMap.coe_coe, hQ, real_inner_comm, hQ, hJ.associatedBilinForm_apply_swap]
  · rw [hQ]
    by_cases hu0 : J₀ u = 0
    · simp [hu0]
    · exact (hJ.associated_pos hu0).le

include hJ in
/-- The unitary frame of a compatible structure is positive definite. -/
theorem isStrictlyPositive_unitaryFrame : IsStrictlyPositive (J₀.unitaryFrame J) :=
  (isStrictlyPositive_neg_mul hJ₀ hJ).sqrt

include hJ in
/-- The unitary frame of a compatible structure is invertible. -/
theorem isUnit_unitaryFrame : IsUnit (J₀.unitaryFrame J) :=
  (isStrictlyPositive_unitaryFrame hJ₀ hJ).isUnit

include hJ in
/-- The unitary frame squares to `Q = -J J₀`. -/
theorem unitaryFrame_mul_self :
    J₀.unitaryFrame J * J₀.unitaryFrame J = -(LinearMap.toContinuousLinearMap J.toLinearMap *
      LinearMap.toContinuousLinearMap J₀.toLinearMap) :=
  CFC.sqrt_mul_sqrt_self _ (isStrictlyPositive_neg_mul hJ₀ hJ).nonneg

include hJ in
/-- **The unitary frame is symplectic**, in operator form: `Φ J₀ Φ = J₀`. Conjugation by the
orthogonal map `J₀` inverts `Q = -J J₀`, so it inverts the positive square root `Φ` of `Q`. -/
theorem unitaryFrame_mul_mul_self :
    J₀.unitaryFrame J * LinearMap.toContinuousLinearMap J₀.toLinearMap * J₀.unitaryFrame J =
      LinearMap.toContinuousLinearMap J₀.toLinearMap := by
  have hQ := isStrictlyPositive_neg_mul hJ₀ hJ
  have hΦ := unitaryFrame_mul_self hJ₀ hJ
  have hstar := star_toContinuousLinearMap hJ₀
  have hsq : Ring.inverse (J₀.unitaryFrame J) = CFC.sqrt (Ring.inverse
      (-(LinearMap.toContinuousLinearMap J.toLinearMap *
        LinearMap.toContinuousLinearMap J₀.toLinearMap))) := by
    rw [unitaryFrame_def, CFC.sqrt_ringInverse]
  set Q := -(LinearMap.toContinuousLinearMap J.toLinearMap *
    LinearMap.toContinuousLinearMap J₀.toLinearMap)
  set Φ := J₀.unitaryFrame J
  set j₀ := LinearMap.toContinuousLinearMap J₀.toLinearMap
  have h₀ : j₀ * -j₀ = 1 := by rw [mul_neg, toContinuousLinearMap_mul_self, neg_neg]
  have h₀' : -j₀ * j₀ = 1 := by rw [neg_mul, toContinuousLinearMap_mul_self, neg_neg]
  -- `R = J₀ Φ J₀⁻¹` is a positive square root of `J₀ Q J₀⁻¹ = Q⁻¹`, so it is `Φ⁻¹`.
  have hinv : Ring.inverse Q = j₀ * Q * -j₀ := by
    rw [← hQ.isUnit.unit_spec, Ring.inverse_unit]
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [IsUnit.unit_spec, ← mul_assoc, ← mul_assoc, neg_mul_mul_neg_mul, h₀]
  have hR : j₀ * Φ * -j₀ = Ring.inverse Φ := by
    rw [hsq, hinv]
    refine (CFC.sqrt_unique ?_ ?_).symm
    · rw [← hΦ]
      calc j₀ * Φ * -j₀ * (j₀ * Φ * -j₀) = j₀ * Φ * (-j₀ * j₀) * Φ * -j₀ := by noncomm_ring
        _ = j₀ * (Φ * Φ) * -j₀ := by rw [h₀', mul_one, mul_assoc j₀ Φ Φ]
    · rw [← hstar]
      exact star_right_conjugate_nonneg (unitaryFrame_nonneg J₀ J) j₀
  calc Φ * j₀ * Φ = Φ * j₀ * Φ * (-j₀ * j₀) := by rw [h₀', mul_one]
    _ = Φ * (j₀ * Φ * -j₀) * j₀ := by noncomm_ring
    _ = j₀ := by
        rw [hR, Ring.mul_inverse_cancel _ (isUnit_unitaryFrame hJ₀ hJ), one_mul]

include hJ in
/-- **The unitary frame intertwines the complex structures**: `J Φ = Φ J₀`. -/
theorem mul_unitaryFrame :
    LinearMap.toContinuousLinearMap J.toLinearMap * J₀.unitaryFrame J =
      J₀.unitaryFrame J * LinearMap.toContinuousLinearMap J₀.toLinearMap := by
  rw [← neg_mul_mul J₀ J, ← unitaryFrame_mul_self hJ₀ hJ, mul_assoc, mul_assoc,
    ← mul_assoc _ _ (J₀.unitaryFrame J), unitaryFrame_mul_mul_self hJ₀ hJ]

include hJ in
/-- The unitary frame intertwines the complex structures, pointwise: `J (Φ v) = Φ (J₀ v)`. -/
theorem apply_unitaryFrame_apply (v : V) : J (J₀.unitaryFrame J v) = J₀.unitaryFrame J (J₀ v) := by
  simpa using congrArg (· v) (mul_unitaryFrame hJ₀ hJ)

include hJ in
/-- **The unitary frame is symplectic**: `ω(Φ u, Φ v) = ω(u, v)`. -/
theorem apply_unitaryFrame_unitaryFrame (u v : V) :
    ω (J₀.unitaryFrame J u) (J₀.unitaryFrame J v) = ω u v := by
  have hsymm := (ContinuousLinearMap.nonneg_iff_isPositive.1
    (unitaryFrame_nonneg J₀ J)).inner_left_eq_inner_right
  have h := congrArg (· v) (unitaryFrame_mul_mul_self hJ₀ hJ)
  simp only [mul_apply_eq_comp, LinearMap.coe_toContinuousLinearMap'] at h
  rw [apply_eq_neg_inner hJ₀, apply_eq_neg_inner hJ₀, hsymm, ← h]

include hJ in
/-- **The unitary frame is an isometry** from the inner product `⟪·, ·⟫ = ω(·, J₀ ·)` to the
metric `ω(·, J ·)` of `J`: `ω(Φ u, J Φ v) = ⟪u, v⟫`. -/
theorem associatedBilinForm_unitaryFrame_unitaryFrame (u v : V) :
    ω.associatedBilinForm J (J₀.unitaryFrame J u) (J₀.unitaryFrame J v) = ⟪u, v⟫_ℝ := by
  rw [SymplecticForm.associatedBilinForm_apply, apply_unitaryFrame_apply hJ₀ hJ,
    apply_unitaryFrame_unitaryFrame hJ₀ hJ, hJ₀]

include hJ in
/-- **Characterization of the unitary frame.** A positive operator `P` is the unitary frame of a
compatible `J` exactly when it is symplectic, `P J₀ P = J₀`, and intertwines the complex
structures, `J P = P J₀`. -/
theorem eq_unitaryFrame_iff {P : V →L[ℝ] V} (hP : 0 ≤ P) :
    P = J₀.unitaryFrame J ↔
      P * LinearMap.toContinuousLinearMap J₀.toLinearMap * P =
          LinearMap.toContinuousLinearMap J₀.toLinearMap ∧
        LinearMap.toContinuousLinearMap J.toLinearMap * P =
          P * LinearMap.toContinuousLinearMap J₀.toLinearMap := by
  refine ⟨?_, fun ⟨hs, hi⟩ ↦ ?_⟩
  · rintro rfl
    exact ⟨unitaryFrame_mul_mul_self hJ₀ hJ, mul_unitaryFrame hJ₀ hJ⟩
  -- The two identities force `P² = -J J₀`, and positive square roots are unique.
  have h₀ := toContinuousLinearMap_mul_self J₀
  set j := LinearMap.toContinuousLinearMap J.toLinearMap
  set j₀ := LinearMap.toContinuousLinearMap J₀.toLinearMap
  have hPP : P * P = -(j * j₀) :=
    calc P * P = -(P * (j₀ * j₀) * P) := by rw [h₀]; noncomm_ring
      _ = -(j * (P * j₀ * P)) := by rw [← mul_assoc j, ← mul_assoc j, hi]; noncomm_ring
      _ = -(j * j₀) := by rw [hs]
  rw [unitaryFrame_def]
  exact (CFC.sqrt_unique hPP hP).symm

end Compatible

end AlmostComplexStructure

end TauCeti

open TauCeti

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {J : E → AlmostComplexStructure V} {n : WithTop ℕ∞}

/-- **The unitary frame depends smoothly on the complex structure.** For a `C^n` family `J_x` of
compatible complex structures, the unitary frames `Φ_x = √(-J_x J₀)` form a `C^n` family of
operators. -/
theorem ContDiff.unitaryFrame
    (h : ContDiff ℝ n fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap)
    (hJ₀ : ∀ u v, ω u (J₀ v) = ⟪u, v⟫_ℝ) (hJ : ∀ x, ω.Compatible (J x)) :
    ContDiff ℝ n fun x ↦ J₀.unitaryFrame (J x) :=
  ContinuousLinearMap.contDiffOn_sqrt.comp_contDiff
    (h.mul contDiff_const).neg fun x ↦ AlmostComplexStructure.isStrictlyPositive_neg_mul hJ₀ (hJ x)
