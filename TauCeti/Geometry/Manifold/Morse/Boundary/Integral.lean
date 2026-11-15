/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Sign
public import TauCeti.Geometry.Manifold.Morse.Boundary.Square

/-!
# The integral Morse boundary on a compact manifold

Let `f` be a Morse function on a compact boundaryless manifold `M` and `X` an adapted
pseudo-gradient. Choose, at every critical point `p`, a Morse chart `φ p` and an orientation
`o p` of its space of coordinates of negative weight, that is, an orientation of the unstable
manifold `W^u(p)`. The integral Morse chains are the finitely supported `ℤ`-valued functions on the
critical points of `f`, and the coefficient of `q` in the integral boundary of `p` is the number of
trajectories from `p` to `q` counted with the signs
`TauCeti.IsAdaptedPseudoGradient.trajectorySign` when `ind p = ind q + 1`, and zero otherwise.

This file defines this boundary and proves the facts about it that do not need the orientation of
the compactified index-two trajectory spaces:

* **Degree and filtration.** The boundary lowers the Morse index by one and strictly lowers the
  critical value.
* **Reduction modulo two.** When `X` is linear in each chart `φ p` and satisfies the Morse–Smale
  condition, every sign is `±1`, so reducing the coefficients modulo two turns the integral
  boundary into the mod-two Morse boundary
  `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary`.
* **Change of orientations.** Two families `o` and `o'` of orientations differ at each critical
  point by a sign `ε p = ±1` (`TauCeti.morseOrientationSign`). The coefficient of `q` in the
  boundary of `p` changes by `ε p * ε q`, so the chain isomorphism multiplying the coefficient of
  each `p` by `ε p` (`TauCeti.morseOrientationChange`) intertwines the two boundaries.
* **The square counts broken trajectories with signs.** Under the Morse–Smale condition, the
  coefficient of `r` in `∂ (∂ p)` is the sum, over the broken index-two trajectories from `p` to
  `r` (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySet`), of the products of the signs
  of their two components. So `∂ ∘ ∂ = 0` holds exactly when these signed counts vanish. This is
  the algebraic half of `∂² = 0` over `ℤ`; the geometric half, that the two ends of each component
  of the compactified space of index-two trajectories carry opposite signs, is not proved here.

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `morseTrajectorySign`: the sign of the trajectory from `p` to `q` through a point, and `0` when
  the indices are not consecutive.
* `integralMorseBoundaryCoeff`: the coefficient of `q` in the integral boundary of `p`.
* `integralMorseBoundary`: the integral Morse boundary, an endomorphism of the free `ℤ`-module on
  the critical points.
* `IsMorseSmale.mapRange_intCast_integralMorseBoundary`: its reduction modulo two is the mod-two
  Morse boundary.
* `integralMorseBoundary_comp_morseOrientationChange`: changing the orientations conjugates the
  boundary by `morseOrientationChange`.
* `IsMorseSmale.integralMorseBoundary_integralMorseBoundary_single_apply` and
  `IsMorseSmale.integralMorseBoundary_comp_integralMorseBoundary_eq_zero_iff`: `∂ ∘ ∂` counts
  broken trajectories with signs.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations of the descending manifolds, the signed
  counts and the Morse complex over `ℤ`).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex with integer coefficients).
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-! ### Changes of orientation -/

section OrientationChange

variable {φ : ∀ p : criticalPoints 𝓘(ℝ, E) f, MorseChart E f p}
  (o o' : ∀ p : criticalPoints 𝓘(ℝ, E) f,
    Orientation ℝ ({i // (φ p).weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))

open scoped Classical in
/-- The sign comparing two families of orientations of the unstable manifolds at a critical point
`p`: `1` where `o' p = o p` and `-1` otherwise. Since the unstable manifold at `p` has dimension
`ind p`, the orientation `o' p` is then `-o p`. -/
noncomputable def morseOrientationSign (p : criticalPoints 𝓘(ℝ, E) f) : ℤ :=
  if o' p = o p then 1 else -1

variable {o o'} {p : criticalPoints 𝓘(ℝ, E) f}

/-- The orientation sign is `1` where the two orientations agree. -/
@[simp]
theorem morseOrientationSign_of_eq (h : o' p = o p) : morseOrientationSign o o' p = 1 := by
  simp [morseOrientationSign, h]

/-- The orientation sign is `-1` where the two orientations differ. -/
@[simp]
theorem morseOrientationSign_of_ne (h : o' p ≠ o p) : morseOrientationSign o o' p = -1 := by
  simp [morseOrientationSign, h]

/-- The orientation sign of a family against itself is `1`. -/
theorem morseOrientationSign_self : morseOrientationSign o o p = 1 :=
  morseOrientationSign_of_eq rfl

/-- The orientation sign is symmetric. -/
theorem morseOrientationSign_comm : morseOrientationSign o o' p = morseOrientationSign o' o p := by
  by_cases h : o' p = o p
  · rw [morseOrientationSign_of_eq h, morseOrientationSign_of_eq h.symm]
  · rw [morseOrientationSign_of_ne h, morseOrientationSign_of_ne (Ne.symm h)]

/-- The orientation sign squares to `1`. -/
@[simp]
theorem morseOrientationSign_mul_self :
    morseOrientationSign o o' p * morseOrientationSign o o' p = 1 := by
  by_cases h : o' p = o p
  · rw [morseOrientationSign_of_eq h, one_mul]
  · rw [morseOrientationSign_of_ne h, neg_mul_neg, one_mul]

/-- The orientation sign is `-1` where the second orientation is the reverse of the first. -/
@[simp]
theorem morseOrientationSign_of_eq_neg (h : o' p = -o p) : morseOrientationSign o o' p = -1 :=
  morseOrientationSign_of_ne (h ▸ Module.Ray.ne_neg_self (o p)).symm

variable (o o')

/-- The **orientation change** of the integral Morse chains: the `ℤ`-linear map multiplying the
coefficient of each critical point `p` by the orientation sign `ε p` comparing `o p` with `o' p`.
It is its own inverse (`TauCeti.morseOrientationChange_symm`). -/
noncomputable def morseOrientationChange :
    (criticalPoints 𝓘(ℝ, E) f →₀ ℤ) ≃ₗ[ℤ] (criticalPoints 𝓘(ℝ, E) f →₀ ℤ) :=
  LinearEquiv.ofLinearMap
    (Finsupp.linearCombination ℤ fun p ↦ Finsupp.single p (morseOrientationSign o o' p))
    (Finsupp.linearCombination ℤ fun p ↦ Finsupp.single p (morseOrientationSign o o' p))
    (Finsupp.lhom_ext fun p a ↦ by simp [Finsupp.smul_single, mul_assoc])
    (Finsupp.lhom_ext fun p a ↦ by simp [Finsupp.smul_single, mul_assoc])

variable {o o'}

/-- The orientation change multiplies the coefficient of `p` by the orientation sign at `p`. -/
@[simp]
theorem morseOrientationChange_apply (c : criticalPoints 𝓘(ℝ, E) f →₀ ℤ) :
    morseOrientationChange o o' c p = morseOrientationSign o o' p * c p := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, Finsupp.add_apply, hc, hd, Finsupp.add_apply, mul_add]
  | single q a =>
    rw [morseOrientationChange, LinearEquiv.coe_ofLinearMap, Finsupp.linearCombination_single,
      Finsupp.smul_single, smul_eq_mul, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs with h
    · rw [h, mul_comm]
    · rw [mul_zero]

/-- The orientation change is its own inverse. -/
@[simp]
theorem morseOrientationChange_symm :
    (morseOrientationChange o o').symm = morseOrientationChange o o' :=
  (rfl)

/-- The orientation change of a family against itself is the identity. -/
@[simp]
theorem morseOrientationChange_self : morseOrientationChange o o = LinearEquiv.refl ℤ _ := by
  ext c p
  simp

/-- The orientation change does not depend on the order of the two families. -/
theorem morseOrientationChange_comm :
    morseOrientationChange o o' = morseOrientationChange o' o := by
  ext c p
  simp [morseOrientationSign_comm (o := o)]

end OrientationChange

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X) (hf : IsMorse 𝓘(ℝ, E) f)
  (φ : ∀ p : criticalPoints 𝓘(ℝ, E) f, MorseChart E f p)
  (o : ∀ p : criticalPoints 𝓘(ℝ, E) f,
    Orientation ℝ ({i // (φ p).weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))

omit [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M] in
include hX in
/-- **Morse charts linearizing an adapted pseudo-gradient exist at every critical point.** This
supplies the charts `φ` for which the integral Morse boundary reduces to the mod-two one. -/
theorem exists_forall_morseChart_linear :
    ∃ φ : ∀ p : criticalPoints 𝓘(ℝ, E) f, MorseChart E f p,
      ∀ p : criticalPoints 𝓘(ℝ, E) f, ∀ y ∈ (φ p).toChart.source,
        (φ p).coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ p).toChart y (X y)) =
          fun i ↦ -((φ p).weight i * (φ p).coord ((φ p).toChart y) i) :=
  ⟨fun p ↦ (hX.exists_morseChart p (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.2)).choose,
    fun p ↦ (hX.exists_morseChart p (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.2)).choose_spec⟩

/-! ### Signs and coefficients -/

open scoped Classical in
/-- The **sign of the trajectory** from the critical point `p` to the critical point `q` through
the point `y`, for the Morse charts `φ` and the orientations `o` of the unstable manifolds:
`TauCeti.IsAdaptedPseudoGradient.trajectorySign` when `ind p = ind q + 1`, and `0` otherwise. -/
noncomputable def morseTrajectorySign (p q : criticalPoints 𝓘(ℝ, E) f) (y : M) : ℤ :=
  if hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 then
    hX.trajectorySign (φ p) (φ q) (o p) (o q) hpq y
  else 0

/-- The **coefficient of `q` in the integral Morse boundary of `p`**: the number of trajectories
from `p` to `q`, read on the middle level, counted with their signs. It is the signed count
`TauCeti.IsAdaptedPseudoGradient.signedTrajectoryCount` when `ind p = ind q + 1`
(`integralMorseBoundaryCoeff_eq_signedTrajectoryCount`) and `0` otherwise. -/
noncomputable def integralMorseBoundaryCoeff (p q : criticalPoints 𝓘(ℝ, E) f) : ℤ :=
  ∑ᶠ y ∈ hX.morseTrajectorySlice p q, hX.morseTrajectorySign φ o p q y

variable {hX φ o} {p q : criticalPoints 𝓘(ℝ, E) f} {y : M}

/-- For critical points of consecutive index, the sign is the trajectory sign. -/
theorem morseTrajectorySign_of_eq
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    hX.morseTrajectorySign φ o p q y = hX.trajectorySign (φ p) (φ q) (o p) (o q) hpq y := by
  rw [morseTrajectorySign, dite_eq_left hpq]

/-- The sign vanishes between critical points whose indices are not consecutive. -/
@[simp]
theorem morseTrajectorySign_of_ne
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p ≠ manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    hX.morseTrajectorySign φ o p q y = 0 := by
  rw [morseTrajectorySign, dite_eq_right hpq]

/-- **Changing the orientations multiplies the sign by the orientation signs at both ends.** -/
theorem morseTrajectorySign_of_orientation
    (o' : ∀ p : criticalPoints 𝓘(ℝ, E) f,
      Orientation ℝ ({i // (φ p).weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p))) :
    hX.morseTrajectorySign φ o' p q y =
      morseOrientationSign o o' p * morseOrientationSign o o' q *
        hX.morseTrajectorySign φ o p q y := by
  by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
  · rw [morseTrajectorySign_of_eq hpq, morseTrajectorySign_of_eq hpq]
    -- At each end, `o'` agrees with `o` or with its reverse.
    have hcard (r : criticalPoints 𝓘(ℝ, E) f) :
        Fintype.card (Fin (manifoldMorseIndex 𝓘(ℝ, E) f r)) =
          Module.finrank ℝ ({i // (φ r).weight i < 0} → ℝ) := by
      rw [Fintype.card_fin, (φ r).finrank_negativeWeight_fun]
    rcases (o' p).eq_or_eq_neg (o p) (hcard p) with hop | hop <;>
    rcases (o' q).eq_or_eq_neg (o q) (hcard q) with hoq | hoq <;>
    simp [hop, hoq]
  · simp [hpq]

/-- **Each sign is `±1`** on the trajectories between critical points of consecutive index, when
`X` is linear in the Morse charts `φ` and satisfies the Morse–Smale condition. -/
theorem morseTrajectorySign_eq_one_or_eq_neg_one (hMS : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (hφp : ∀ y ∈ (φ p).toChart.source,
      (φ p).coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ p).toChart y (X y)) =
        fun i ↦ -((φ p).weight i * (φ p).coord ((φ p).toChart y) i))
    (hφq : ∀ y ∈ (φ q).toChart.source,
      (φ q).coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ q).toChart y (X y)) =
        fun i ↦ -((φ q).weight i * (φ q).coord ((φ q).toChart y) i))
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) :
    hX.morseTrajectorySign φ o p q y = 1 ∨ hX.morseTrajectorySign φ o p q y = -1 := by
  rw [morseTrajectorySign_of_eq hpq]
  exact trajectorySign_eq_one_or_eq_neg_one hφp hφq hMS hf hy

variable (hX φ o) in
/-- The defining formula of the coefficient. -/
theorem integralMorseBoundaryCoeff_def (p q : criticalPoints 𝓘(ℝ, E) f) :
    hX.integralMorseBoundaryCoeff φ o p q =
      ∑ᶠ y ∈ hX.morseTrajectorySlice p q, hX.morseTrajectorySign φ o p q y :=
  (rfl)

/-- **For critical points of consecutive index, the coefficient is the signed count** of the
trajectories from `p` to `q`. -/
theorem integralMorseBoundaryCoeff_eq_signedTrajectoryCount
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    hX.integralMorseBoundaryCoeff φ o p q =
      hX.signedTrajectoryCount (φ p) (φ q) (o p) (o q) hpq := by
  simp only [integralMorseBoundaryCoeff_def, signedTrajectoryCount_def,
    morseTrajectorySign_of_eq hpq]

/-- The coefficient vanishes between critical points whose indices are not consecutive. -/
@[simp]
theorem integralMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p ≠ manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    hX.integralMorseBoundaryCoeff φ o p q = 0 := by
  simp [integralMorseBoundaryCoeff_def, hpq]

/-- **The integral boundary lowers the Morse index by one:** a nonzero coefficient joins critical
points whose indices differ by one. -/
theorem morseIndex_eq_add_one_of_integralMorseBoundaryCoeff_ne_zero
    (hpq : hX.integralMorseBoundaryCoeff φ o p q ≠ 0) :
    manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 := by
  by_contra hind
  exact hpq (integralMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hind)

/-- **The integral boundary lowers the critical value:** a nonzero coefficient joins critical
points with strictly decreasing critical value. -/
theorem value_lt_of_integralMorseBoundaryCoeff_ne_zero
    (hpq : hX.integralMorseBoundaryCoeff φ o p q ≠ 0) : f q < f p := by
  have hind := morseIndex_eq_add_one_of_integralMorseBoundaryCoeff_ne_zero hpq
  have hne : (p : M) ≠ q := fun he ↦ by
    rw [he] at hind
    omega
  obtain ⟨z, hz, -⟩ := exists_ne_zero_of_finsum_mem_ne_zero hpq
  exact hX.value_lt_of_mem_morseTrajectorySlice hne hz

/-- The coefficient vanishes unless the critical value drops. -/
theorem integralMorseBoundaryCoeff_eq_zero_of_value_le (hpq : f p ≤ f q) :
    hX.integralMorseBoundaryCoeff φ o p q = 0 := by
  by_contra hne
  exact (value_lt_of_integralMorseBoundaryCoeff_ne_zero hne).not_ge hpq

/-- **Changing the orientations multiplies the coefficient by the orientation signs at both
ends.** -/
theorem integralMorseBoundaryCoeff_of_orientation
    (o' : ∀ p : criticalPoints 𝓘(ℝ, E) f,
      Orientation ℝ ({i // (φ p).weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p))) :
    hX.integralMorseBoundaryCoeff φ o' p q =
      morseOrientationSign o o' p * morseOrientationSign o o' q *
        hX.integralMorseBoundaryCoeff φ o p q := by
  simp only [integralMorseBoundaryCoeff_def, morseTrajectorySign_of_orientation (o := o) o',
    mul_finsum_mem]

/-- **The coefficients reduce modulo two to the mod-two Morse boundary.** When `X` is linear in the
Morse charts `φ` and satisfies the Morse–Smale condition, the coefficient of `q` in the integral
boundary of `p`, reduced modulo two, is its coefficient in the mod-two Morse boundary. -/
theorem IsMorseSmale.intCast_integralMorseBoundaryCoeff (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f)
    (hφp : ∀ y ∈ (φ p).toChart.source,
      (φ p).coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ p).toChart y (X y)) =
        fun i ↦ -((φ p).weight i * (φ p).coord ((φ p).toChart y) i))
    (hφq : ∀ y ∈ (φ q).toChart.source,
      (φ q).coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ q).toChart y (X y)) =
        fun i ↦ -((φ q).weight i * (φ q).coord ((φ q).toChart y) i)) :
    (hX.integralMorseBoundaryCoeff φ o p q : ZMod 2) = h.morseBoundaryCoeff hf p q := by
  by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
  · rw [integralMorseBoundaryCoeff_eq_signedTrajectoryCount hpq,
      h.morseBoundaryCoeff_eq_intCast_signedTrajectoryCount hf hφp hφq]
  · rw [integralMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hpq,
      h.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf hpq, Int.cast_zero]

/-! ### The integral boundary -/

variable (hX φ o) in
/-- **The integral Morse boundary.** The `ℤ`-linear endomorphism of the free `ℤ`-module on the
critical points of `f` sending a critical point `p` to the sum of the critical points `q` with
`ind q = ind p - 1`, each weighted by the number of trajectories from `p` to `q` counted with the
signs determined by the orientations `o` of the unstable manifolds. -/
noncomputable def integralMorseBoundary :
    (criticalPoints 𝓘(ℝ, E) f →₀ ℤ) →ₗ[ℤ] (criticalPoints 𝓘(ℝ, E) f →₀ ℤ) :=
  haveI := hf.finite_criticalPoints.to_subtype
  Finsupp.linearCombination ℤ fun p ↦
    Finsupp.ofSupportFinite (hX.integralMorseBoundaryCoeff φ o p) (toFinite _)

/-- The coefficient of `q` in the integral boundary of a chain `c` is the sum over the critical
points `p` of `c p` times the coefficient `integralMorseBoundaryCoeff` of `q` in the boundary of
`p`. -/
theorem integralMorseBoundary_apply (c : criticalPoints 𝓘(ℝ, E) f →₀ ℤ)
    (q : criticalPoints 𝓘(ℝ, E) f) :
    hX.integralMorseBoundary hf φ o c q =
      c.sum fun p a ↦ a * hX.integralMorseBoundaryCoeff φ o p q := by
  simp [integralMorseBoundary, Finsupp.linearCombination_apply, Finsupp.ofSupportFinite_coe]

/-- The coefficient of `q` in the integral boundary of `a • p` is `a` times the coefficient
`integralMorseBoundaryCoeff` of `q` in the boundary of `p`. -/
@[simp]
theorem integralMorseBoundary_single_apply (p q : criticalPoints 𝓘(ℝ, E) f) (a : ℤ) :
    hX.integralMorseBoundary hf φ o (Finsupp.single p a) q =
      a * hX.integralMorseBoundaryCoeff φ o p q := by
  rw [integralMorseBoundary_apply, Finsupp.sum_single_index (zero_mul _)]

/-- **Reduction modulo two.** When `X` is linear in the Morse charts `φ` and satisfies the
Morse–Smale condition, reducing the coefficients of the integral boundary of a chain modulo two
gives the mod-two Morse boundary of its reduction, whatever the orientations `o`. -/
theorem IsMorseSmale.mapRange_intCast_integralMorseBoundary (h : hX.IsMorseSmale)
    (hφ : ∀ p : criticalPoints 𝓘(ℝ, E) f, ∀ y ∈ (φ p).toChart.source,
      (φ p).coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ p).toChart y (X y)) =
        fun i ↦ -((φ p).weight i * (φ p).coord ((φ p).toChart y) i))
    (c : criticalPoints 𝓘(ℝ, E) f →₀ ℤ) :
    Finsupp.mapRange (Int.cast : ℤ → ZMod 2) Int.cast_zero (hX.integralMorseBoundary hf φ o c) =
      h.morseBoundary hf (Finsupp.mapRange Int.cast Int.cast_zero c) := by
  ext q
  rw [Finsupp.mapRange_apply, integralMorseBoundary_apply, IsMorseSmale.morseBoundary_apply,
    Finsupp.sum_mapRange_index fun _ ↦ zero_mul _, Finsupp.sum, Finsupp.sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Int.cast_mul, h.intCast_integralMorseBoundaryCoeff hf (hφ p) (hφ q)]

/-- **Changing the orientations conjugates the integral boundary by the orientation change.** For
two families `o` and `o'` of orientations of the unstable manifolds, the orientation change
`TauCeti.morseOrientationChange o o'` is a chain isomorphism from the integral Morse chains with
the boundary for `o` to those with the boundary for `o'`. -/
theorem integralMorseBoundary_comp_morseOrientationChange
    (o' : ∀ p : criticalPoints 𝓘(ℝ, E) f,
      Orientation ℝ ({i // (φ p).weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p))) :
    hX.integralMorseBoundary hf φ o' ∘ₗ (morseOrientationChange o o' : _ →ₗ[ℤ] _) =
      (morseOrientationChange o o' : _ →ₗ[ℤ] _) ∘ₗ hX.integralMorseBoundary hf φ o := by
  classical
  refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, morseOrientationChange_apply,
    integralMorseBoundary_single_apply]
  -- The change sends `a • p` to `(ε p * a) • p`.
  have hp : morseOrientationChange o o' (Finsupp.single p a) =
      Finsupp.single p (morseOrientationSign o o' p * a) := by
    ext r
    rw [morseOrientationChange_apply, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs with h
    · rw [h]
    · rw [mul_zero]
  rw [hp, integralMorseBoundary_single_apply, integralMorseBoundaryCoeff_of_orientation (o := o) o']
  -- Both sides are `ε p² * ε q * a * n = ε q * a * n`.
  linear_combination (a * morseOrientationSign o o' q * hX.integralMorseBoundaryCoeff φ o p q) *
    (morseOrientationSign_mul_self (o := o) (o' := o') (p := p))

/-! ### The square of the integral boundary -/

namespace IsMorseSmale

variable (h : hX.IsMorseSmale)
include h

/-- **`∂ ∘ ∂` counts broken trajectories with signs.** Under the Morse–Smale condition, the
coefficient of `r` in the integral boundary of the integral boundary of a critical point `p` is the
sum, over the broken index-two trajectories `(q, z₁, z₂)` from `p` to `r`, of the product of the
signs of the trajectory from `p` to `q` through `z₁` and of the trajectory from `q` to `r` through
`z₂`. -/
theorem integralMorseBoundary_integralMorseBoundary_single_apply
    (p r : criticalPoints 𝓘(ℝ, E) f) :
    hX.integralMorseBoundary hf φ o (hX.integralMorseBoundary hf φ o (Finsupp.single p 1)) r =
      ∑ᶠ x ∈ hX.morseBrokenTrajectorySet p r,
        hX.morseTrajectorySign φ o p x.1 x.2.1 * hX.morseTrajectorySign φ o x.1 r x.2.2 := by
  classical
  have := hf.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f)
  have hfin := h.finite_morseBrokenTrajectorySet hf p r
  -- Sort the broken trajectories by their intermediate critical point `q`.
  rw [integralMorseBoundary_apply, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _,
    finsum_mem_eq_finite_toFinset_sum _ hfin,
    ← Finset.sum_fiberwise hfin.toFinset Prod.fst]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [integralMorseBoundary_single_apply, one_mul]
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1
  · -- The fiber over `q` is a copy of the pairs of trajectories through `q`.
    have h₁ := h.finite_morseTrajectorySlice hf hind.1
    have h₂ := h.finite_morseTrajectorySlice hf hind.2
    have hfib : hfin.toFinset.filter (fun x ↦ x.1 = q) =
        (h₁.toFinset ×ˢ h₂.toFinset).map ⟨Prod.mk q, Prod.mk_right_injective q⟩ := by
      ext ⟨q', z₁, z₂⟩
      simp only [Finset.mem_filter, Finite.mem_toFinset, mem_morseBrokenTrajectorySet,
        Finset.mem_map, Finset.mem_product, Function.Embedding.coeFn_mk, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨-, -, hz₁, hz₂⟩, rfl⟩
        exact ⟨(z₁, z₂), ⟨hz₁, hz₂⟩, rfl, rfl⟩
      · rintro ⟨⟨w₁, w₂⟩, ⟨hw₁, hw₂⟩, rfl, hw⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ hw
        exact ⟨⟨hind.1, hind.2, hw₁, hw₂⟩, rfl⟩
    rw [hfib, Finset.sum_map, Finset.sum_product, integralMorseBoundaryCoeff_def,
      integralMorseBoundaryCoeff_def, finsum_mem_eq_finite_toFinset_sum _ h₁,
      finsum_mem_eq_finite_toFinset_sum _ h₂, Finset.sum_mul_sum]
    rfl
  · -- Otherwise there are no broken trajectories through `q`, and one of the counts vanishes.
    have hempty : hfin.toFinset.filter (fun x ↦ x.1 = q) = ∅ := by
      refine Finset.filter_false_of_mem fun x hx hxq ↦ hind ?_
      rw [Finite.mem_toFinset, mem_morseBrokenTrajectorySet] at hx
      exact hxq ▸ ⟨hx.1, hx.2.1⟩
    rw [hempty, Finset.sum_empty]
    rcases not_and_or.mp hind with hpq | hqr
    · simp [hpq]
    · simp [hqr]

/-- **`∂² = 0` over `ℤ` reduces to counting broken trajectories with signs.** Under the
Morse–Smale condition, the integral Morse boundary squares to zero exactly when, between any two
critical points, the broken index-two trajectories counted with the products of the signs of
their components sum to zero. -/
theorem integralMorseBoundary_comp_integralMorseBoundary_eq_zero_iff :
    hX.integralMorseBoundary hf φ o ∘ₗ hX.integralMorseBoundary hf φ o = 0 ↔
      ∀ p r : criticalPoints 𝓘(ℝ, E) f,
        ∑ᶠ x ∈ hX.morseBrokenTrajectorySet p r,
          hX.morseTrajectorySign φ o p x.1 x.2.1 * hX.morseTrajectorySign φ o x.1 r x.2.2 = 0 := by
  simp_rw [← h.integralMorseBoundary_integralMorseBoundary_single_apply hf]
  constructor
  · intro h0 p r
    simpa using DFunLike.congr_fun (LinearMap.congr_fun h0 (Finsupp.single p 1)) r
  · intro h0
    refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun r ↦ ?_
    -- The boundary of `a • p` is `a` times the boundary of `p`.
    rw [LinearMap.comp_apply, ← Finsupp.smul_single_one, map_smul, map_smul]
    simp [h0]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
