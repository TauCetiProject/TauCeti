/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Integrable
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Torus
import TauCeti.Geometry.Symplectic.Hamiltonian.Complete
import TauCeti.Geometry.Symplectic.Manifold.Opens
import TauCeti.Topology.Compactness.Compact

/-!
# The invariant tori of the bound Kepler problem

A particle of mass `m > 0` in the plane `V` moving in the attractive Kepler potential `-κ / r`,
`κ > 0`, has the energy `H(q, p) = ‖p‖² / (2m) - κ / ‖q‖` and the angular momentum
`L(q, p) = q₁p₂ - q₂p₁`, written in an orthonormal basis `b` of `V`. Off the collision set `q = 0`
they form the completely integrable system `F = (H, L)`
(`TauCeti.isIntegrableSystem_centralForceEnergyMomentum`). This file shows that its bound motions
with nonzero angular momentum fill out invariant tori.

* **Bounded noncollision motion.** At a state with negative energy `E` and angular momentum
  `ℓ ≠ 0`, the distance `‖q‖` lies between the pericentre and apocentre radii of `(E, ℓ)`
  (`TauCeti.norm_fst_mem_Icc_keplerPeriapsisRadius_keplerApoapsisRadius`), and the energy is at
  least the circular energy `-m κ² / (2 ℓ²)`
  (`TauCeti.centralForceHamiltonian_kepler_min_le`). Hence the common level of `H = E` and
  `L = ℓ` off the collision set is compact
  (`TauCeti.isCompact_setOf_centralForceHamiltonian_kepler_eq`).
* **Regularity.** Above the circular energy, `dH` and `dL` are independent at every state of the
  level (`TauCeti.isRegularPoint_centralForceEnergyMomentum_kepler`). At the circular energy the
  level is a single circular orbit, made of critical points.
* **The bound phase space.** The states off the collision set with `H < 0` and `L ≠ 0` form an
  open union of levels of `F` (`TauCeti.keplerBoundPhaseSpace`). With the restriction of the
  standard symplectic form, the levels of `F` in it are compact
  (`TauCeti.isCompact_keplerBoundPhaseSpace_preimage_singleton`), so the Hamiltonian vector fields
  of `H` and `L` are complete there
  (`TauCeti.isCompleteVectorField_hamiltonianVectorField_keplerBoundPhaseSpace`). On the whole
  punctured phase space the Kepler flow is not complete, since motions with `L = 0` fall into the
  collision set in finite time.
* **Liouville tori.** By the topological Liouville–Arnold theorem
  (`TauCeti.SmoothTwoForm.IsSymplectic.nonempty_homeomorph_unitAddTorus`), every connected
  component of a level of `F` in the bound phase space with energy above the circular energy is
  homeomorphic to the torus `(ℝ / ℤ)²`
  (`TauCeti.nonempty_homeomorph_unitAddTorus_keplerBoundPhaseSpace`).

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 8 and 49.
-/

public section

noncomputable section

open Function Set
open scoped InnerProductSpace Manifold ContDiff Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (b : OrthonormalBasis (Fin 2) ℝ V) {m κ : ℝ}

/-! ### Bounded noncollision motion -/

/-- **The circular energy bounds the Kepler energy from below.** Off the collision set, the energy
of a state with nonzero angular momentum `ℓ` is at least the energy `-m κ² / (2 ℓ²)` of the
circular orbit with angular momentum `ℓ`. -/
theorem centralForceHamiltonian_kepler_min_le (hm : 0 < m) {x : V × V} (hq : x.1 ≠ 0)
    (hℓ : angularMomentum (b 0) (b 1) x ≠ 0) :
    -(m * κ ^ 2) / (2 * angularMomentum (b 0) (b 1) x ^ 2) ≤
      centralForceHamiltonian m (fun r ↦ -κ / r) x :=
  (effectivePotential_kepler_min_le hm hℓ (norm_ne_zero_iff.2 hq)).trans
    (effectivePotential_le_centralForceHamiltonian hm.le hq (sq_angularMomentum b x))

/-- **Bound Kepler motions avoid collision and escape.** Off the collision set, at a state of
negative energy `E` and nonzero angular momentum `ℓ`, the distance `‖q‖` lies between the
pericentre and apocentre radii of `(E, ℓ)`. These radii are positive
(`TauCeti.kepler_turningRadii_pos_le`). -/
theorem norm_fst_mem_Icc_keplerPeriapsisRadius_keplerApoapsisRadius (hm : 0 < m) (hκ : 0 < κ)
    {x : V × V} (hq : x.1 ≠ 0) (hE : centralForceHamiltonian m (fun r ↦ -κ / r) x < 0)
    (hℓ : angularMomentum (b 0) (b 1) x ≠ 0) :
    ‖x.1‖ ∈ Icc
      (keplerPeriapsisRadius m κ (angularMomentum (b 0) (b 1) x)
        (centralForceHamiltonian m (fun r ↦ -κ / r) x))
      (keplerApoapsisRadius m κ (angularMomentum (b 0) (b 1) x)
        (centralForceHamiltonian m (fun r ↦ -κ / r) x)) :=
  (effectivePotential_kepler_le_iff hm hκ hℓ (centralForceHamiltonian_kepler_min_le b hm hq hℓ) hE
    (norm_pos_iff.2 hq)).1 (effectivePotential_le_centralForceHamiltonian hm.le hq
      (sq_angularMomentum b x))

/-- The energy and the angular momentum of the Kepler problem are jointly continuous off the
collision set. -/
private theorem continuousAt_kepler_energyMomentum {x : V × V} (hq : x.1 ≠ 0) :
    ContinuousAt (fun x : V × V ↦
      (centralForceHamiltonian m (fun r ↦ -κ / r) x, angularMomentum (b 0) (b 1) x)) x :=
  (continuousAt_centralForceHamiltonian
    (continuousAt_const.div continuousAt_id (norm_ne_zero_iff.2 hq))).prodMk
      (hasFDerivAt_angularMomentum (b 0) (b 1) x).continuousAt

/-- **Bound Kepler levels are compact.** For `m, κ > 0`, a negative energy `E` and a nonzero
angular momentum `ℓ`, the states off the collision set with energy `E` and angular momentum `ℓ`
form a compact set. It is empty below the circular energy `-m κ² / (2 ℓ²)`. -/
theorem isCompact_setOf_centralForceHamiltonian_kepler_eq [FiniteDimensional ℝ V] (hm : 0 < m)
    (hκ : 0 < κ) {E ℓ : ℝ} (hE : E < 0) (hℓ : ℓ ≠ 0) :
    IsCompact {x : V × V | x.1 ≠ 0 ∧ centralForceHamiltonian m (fun r ↦ -κ / r) x = E ∧
      angularMomentum (b 0) (b 1) x = ℓ} := by
  by_cases hmin : -(m * κ ^ 2) / (2 * ℓ ^ 2) ≤ E
  swap
  · -- Below the circular energy the level is empty.
    convert isCompact_empty using 1
    refine eq_empty_of_forall_notMem fun x hx ↦ hmin ?_
    obtain ⟨hq, hxE, hxℓ⟩ := hx
    rw [← hxE, ← hxℓ]
    exact centralForceHamiltonian_kepler_min_le b hm hq (hxℓ ▸ hℓ)
  set r₁ := keplerPeriapsisRadius m κ ℓ E
  set r₂ := keplerApoapsisRadius m κ ℓ E
  obtain ⟨hr₁, hr₁₂⟩ : 0 < r₁ ∧ r₁ ≤ r₂ := kepler_turningRadii_pos_le hm hκ hℓ hmin hE
  -- The level lies in the compact set `A` of states with `r₁ ≤ ‖q‖ ≤ r₂` and `‖p‖² ≤ 2 m κ / r₁`,
  -- on which the energy is continuous.
  set A := {x : V × V | ‖x.1‖ ∈ Icc r₁ r₂ ∧ ‖x.2‖ ^ 2 ≤ 2 * m * κ / r₁}
  have hAc : IsClosed A :=
    (isClosed_Icc.preimage continuous_fst.norm).inter
      (isClosed_le (continuous_snd.norm.pow 2) continuous_const)
  have hA : IsCompact A := by
    refine Metric.isCompact_of_isClosed_isBounded hAc
      ((Metric.isBounded_closedBall (x := 0) (r := r₂ + (1 + 2 * m * κ / r₁))).subset ?_)
    rintro x ⟨⟨-, hx₁⟩, hx₂⟩
    have hp : ‖x.2‖ ≤ 1 + 2 * m * κ / r₁ := by nlinarith [norm_nonneg x.2]
    have hpos : 0 ≤ 2 * m * κ / r₁ := by positivity
    rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff]
    constructor <;> linarith
  have hq (x : V × V) (hx : x ∈ A) : x.1 ≠ 0 :=
    norm_pos_iff.1 (hr₁.trans_le hx.1.1)
  have hcont : ContinuousOn (fun x : V × V ↦
      (centralForceHamiltonian m (fun r ↦ -κ / r) x, angularMomentum (b 0) (b 1) x)) A :=
    fun x hx ↦ (continuousAt_kepler_energyMomentum b (hq x hx)).continuousWithinAt
  -- A state of the level lies in `A`, since `‖p‖² = 2 m (E + κ / ‖q‖) < 2 m κ / ‖q‖`.
  have hsub (x : V × V) (hx : x.1 ≠ 0) (hxE : centralForceHamiltonian m (fun r ↦ -κ / r) x = E)
      (hxℓ : angularMomentum (b 0) (b 1) x = ℓ) : x ∈ A := by
    have hI := norm_fst_mem_Icc_keplerPeriapsisRadius_keplerApoapsisRadius b hm hκ hx
      (hxE ▸ hE) (hxℓ ▸ hℓ)
    rw [hxE, hxℓ] at hI
    refine ⟨hI, ?_⟩
    have hH : ‖x.2‖ ^ 2 / (2 * m) + -κ / ‖x.1‖ = E := by
      rw [← hxE]
      exact (centralForceHamiltonian_apply m _ x.1 x.2).symm
    have hκr : κ / ‖x.1‖ ≤ κ / r₁ := div_le_div_of_nonneg_left hκ.le hr₁ hI.1
    have hp : ‖x.2‖ ^ 2 = 2 * m * (E + κ / ‖x.1‖) := by
      rw [← hH]
      field_simp
      ring
    rw [hp, mul_div_assoc]
    nlinarith
  have heq : {x : V × V | x.1 ≠ 0 ∧ centralForceHamiltonian m (fun r ↦ -κ / r) x = E ∧
      angularMomentum (b 0) (b 1) x = ℓ} = A ∩ (fun x : V × V ↦
        (centralForceHamiltonian m (fun r ↦ -κ / r) x, angularMomentum (b 0) (b 1) x)) ⁻¹'
          {(E, ℓ)} := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff, Prod.mk.injEq]
    exact ⟨fun ⟨hx, hxE, hxℓ⟩ ↦ ⟨hsub x hx hxE hxℓ, hxE, hxℓ⟩,
      fun ⟨hx, hxE, hxℓ⟩ ↦ ⟨hq x hx, hxE, hxℓ⟩⟩
  rw [heq]
  exact hA.of_isClosed_subset (hcont.preimage_isClosed_of_isClosed hAc isClosed_singleton)
    inter_subset_left

/-- **Above the circular energy, Kepler states are regular.** At a state off the collision set
with nonzero angular momentum `ℓ` and energy above the circular energy `-m κ² / (2 ℓ²)`, the
differentials of the energy and of the angular momentum are linearly independent. -/
theorem isRegularPoint_centralForceEnergyMomentum_kepler (hm : m ≠ 0) {x : V × V} (hq : x.1 ≠ 0)
    (hℓ : angularMomentum (b 0) (b 1) x ≠ 0)
    (hE : -(m * κ ^ 2) / (2 * angularMomentum (b 0) (b 1) x ^ 2) <
      centralForceHamiltonian m (fun r ↦ -κ / r) x) :
    IsRegularPoint 𝓘(ℝ, V × V) 𝓘(ℝ, Fin 2 → ℝ)
      (centralForceEnergyMomentum b m (fun r ↦ -κ / r)) x := by
  have hr : ‖x.1‖ ≠ 0 := norm_ne_zero_iff.2 hq
  rw [isRegularPoint_centralForceEnergyMomentum_iff b hm (hasDerivAt_kepler_potential κ hr) hq]
  rintro ⟨h0, hU'⟩
  -- A critical point lies on the circular orbit `‖q‖ = ℓ² / (m κ)` and has the circular energy.
  have hcirc : angularMomentum (b 0) (b 1) x ^ 2 - m * κ * ‖x.1‖ = 0 := by
    field_simp at hU'
    linear_combination -hU'
  have hH := (centralForceHamiltonian_eq_effectivePotential_iff (U := fun r ↦ -κ / r) hm hq
    (sq_angularMomentum b x)).2
    (radialMomentum_eq_zero_iff.2 h0)
  have hmin := effectivePotential_kepler_sub_min (κ := κ) hm hℓ hr
  rw [hcirc, ← hH, zero_pow two_ne_zero, zero_div] at hmin
  rw [neg_div] at hE
  linarith

/-! ### The bound phase space -/

/-- The **bound phase space** of the Kepler problem: the open set of states `(q, p)` off the
collision set with negative energy `‖p‖² / (2m) - κ / ‖q‖` and nonzero angular momentum. It is a
union of common levels of the energy and the angular momentum. For `m, κ > 0`, with the restriction
of the standard symplectic form both Hamiltonian flows are complete on it
(`TauCeti.isCompleteVectorField_hamiltonianVectorField_keplerBoundPhaseSpace`). -/
def keplerBoundPhaseSpace (m κ : ℝ) : TopologicalSpace.Opens (V × V) where
  carrier := {x | x.1 ≠ 0 ∧ centralForceHamiltonian m (fun r ↦ -κ / r) x < 0 ∧
    angularMomentum (b 0) (b 1) x ≠ 0}
  is_open' := by
    have hcont : ContinuousOn (fun x : V × V ↦
        (centralForceHamiltonian m (fun r ↦ -κ / r) x, angularMomentum (b 0) (b 1) x))
        {x | x.1 ≠ 0} :=
      fun x hx ↦ (continuousAt_kepler_energyMomentum b hx).continuousWithinAt
    exact hcont.isOpen_inter_preimage (isOpen_ne_fun continuous_fst continuous_const)
      (isOpen_Iio.prod isOpen_ne)

/-- Membership in the bound phase space of the Kepler problem. -/
@[simp]
theorem mem_keplerBoundPhaseSpace {x : V × V} :
    x ∈ keplerBoundPhaseSpace b m κ ↔ x.1 ≠ 0 ∧
      centralForceHamiltonian m (fun r ↦ -κ / r) x < 0 ∧ angularMomentum (b 0) (b 1) x ≠ 0 :=
  Iff.rfl

/-- The energy–momentum map of the Kepler problem is smooth off the collision set. -/
private theorem contDiffAt_centralForceEnergyMomentum_kepler {n : WithTop ℕ∞} {x : V × V}
    (hq : x.1 ≠ 0) : ContDiffAt ℝ n (centralForceEnergyMomentum b m (fun r ↦ -κ / r)) x :=
  contDiffAt_centralForceEnergyMomentum b
    (contDiffAt_const.div contDiffAt_id (norm_ne_zero_iff.2 hq)) hq

/-- The energy–momentum map of the Kepler problem is smooth on the bound phase space. -/
theorem contMDiff_centralForceEnergyMomentum_keplerBoundPhaseSpace :
    ContMDiff 𝓘(ℝ, V × V) 𝓘(ℝ, Fin 2 → ℝ) ∞
      (centralForceEnergyMomentum b m (fun r ↦ -κ / r) ∘
        (Subtype.val : keplerBoundPhaseSpace b m κ → V × V)) :=
  fun x ↦ (contDiffAt_centralForceEnergyMomentum_kepler b x.2.1).contMDiffAt.comp x
    (contMDiff_subtype_val x)

/-- **The levels of the Kepler problem in its bound phase space are compact.** For `m, κ > 0`,
the states of the bound phase space sharing the energy and the angular momentum of a given one
form a compact set. -/
theorem isCompact_keplerBoundPhaseSpace_preimage_singleton [FiniteDimensional ℝ V] (hm : 0 < m)
    (hκ : 0 < κ) (x : keplerBoundPhaseSpace b m κ) :
    IsCompact ((centralForceEnergyMomentum b m (fun r ↦ -κ / r) ∘
      (Subtype.val : keplerBoundPhaseSpace b m κ → V × V)) ⁻¹'
      {centralForceEnergyMomentum b m (fun r ↦ -κ / r) x}) := by
  obtain ⟨hq, hE, hℓ⟩ := x.2
  rw [Subtype.isCompact_iff]
  convert isCompact_setOf_centralForceHamiltonian_kepler_eq b hm hκ hE hℓ using 1
  ext y
  simp only [mem_image, mem_preimage, comp_apply, mem_singleton_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2.1, (centralForceEnergyMomentum_eq_iff b).1 hy⟩
  · rintro ⟨hy, hyE, hyℓ⟩
    exact ⟨⟨y, hy, hyE ▸ hE, hyℓ ▸ hℓ⟩, (centralForceEnergyMomentum_eq_iff b).2 ⟨hyE, hyℓ⟩, rfl⟩

/-- The energy and the angular momentum Poisson-commute on the bound phase space. -/
private theorem poissonBracket_centralForceEnergyMomentum_keplerBoundPhaseSpace
    [FiniteDimensional ℝ V] (i j : Fin 2) (x : keplerBoundPhaseSpace b m κ) :
    SmoothTwoForm.poissonBracket
      (SmoothForm.mpullback (Subtype.val : keplerBoundPhaseSpace b m κ → V × V)
        contMDiff_subtype_val (stdSymplecticForm (V := V)).constSmooth)
      (fun y ↦ (centralForceEnergyMomentum b m (fun r ↦ -κ / r) ∘ Subtype.val) y i)
      (fun y ↦ (centralForceEnergyMomentum b m (fun r ↦ -κ / r) ∘ Subtype.val) y j) x = 0 :=
  poissonBracket_centralForceEnergyMomentum_comp_subtypeVal b (W := keplerBoundPhaseSpace b m κ)
    ((differentiableOn_const _).div differentiableOn_id fun _ hr ↦ ne_of_gt hr)
    (fun _ hy ↦ hy.1) i j x

/-- **The Kepler flows are complete on the bound phase space.** For `m, κ > 0`, with the
restriction of the standard symplectic form, the Hamiltonian vector fields of the energy and of the
angular momentum are complete on the bound phase space. -/
theorem isCompleteVectorField_hamiltonianVectorField_keplerBoundPhaseSpace
    [FiniteDimensional ℝ V] (hm : 0 < m) (hκ : 0 < κ) (i : Fin 2) :
    IsCompleteVectorField (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : keplerBoundPhaseSpace b m κ → V × V)
        contMDiff_subtype_val (stdSymplecticForm (V := V)).constSmooth)
      fun y ↦ (centralForceEnergyMomentum b m (fun r ↦ -κ / r) ∘ Subtype.val) y i) := by
  have hσ := (SymplecticForm.isNondegenerate_constSmooth
    (stdSymplecticForm (V := V))).mpullback_subtype_val (keplerBoundPhaseSpace b m κ)
  have hF := contMDiff_centralForceEnergyMomentum_keplerBoundPhaseSpace b (m := m) (κ := κ)
  have hFi (j : Fin 2) := contMDiff_pi_module_iff.1 hF j
  have hv := hσ.contMDiff_hamiltonianVectorField (n := 1) (by simp) ((hFi i).of_le (by simp))
  rw [isCompleteVectorField_iff_maximalIntegralCurveInterval]
  intro x
  refine maximalIntegralCurveInterval_eq_univ_of_isCompact_of_mapsTo hv
    (zero_mem_maximalIntegralCurveInterval hv.contMDiffAt)
    (isCompact_keplerBoundPhaseSpace_preimage_singleton b hm hκ x) fun t ht ↦ funext fun j ↦ ?_
  -- Both integrals are first integrals of each other, so the curves stay in the level of `x`.
  have hfirst := SmoothTwoForm.isFirstIntegral_iff.2
    (poissonBracket_centralForceEnergyMomentum_keplerBoundPhaseSpace b (m := m) (κ := κ) j i)
  exact hfirst.apply_maximalIntegralCurve hσ ((hFi i).of_le (by simp))
    ((hFi j).mdifferentiable (by simp)) ht

/-! ### Liouville tori -/

/-- **Bound Kepler levels are Liouville tori.** Let `m, κ > 0`, and let `x` be a state of the bound
phase space with energy `E` and angular momentum `ℓ`, where `E` is above the circular energy
`-m κ² / (2 ℓ²)`. Then the connected component of `x` in its common level of the energy and the
angular momentum is homeomorphic to the torus `(ℝ / ℤ)²`. -/
theorem nonempty_homeomorph_unitAddTorus_keplerBoundPhaseSpace [FiniteDimensional ℝ V]
    (hm : 0 < m) (hκ : 0 < κ) (x : keplerBoundPhaseSpace b m κ)
    (hx : -(m * κ ^ 2) / (2 * angularMomentum (b 0) (b 1) (x : V × V) ^ 2) <
      centralForceHamiltonian m (fun r ↦ -κ / r) (x : V × V)) :
    Nonempty (connectedComponentIn
      ((centralForceEnergyMomentum b m (fun r ↦ -κ / r) ∘
        (Subtype.val : keplerBoundPhaseSpace b m κ → V × V)) ⁻¹'
          {centralForceEnergyMomentum b m (fun r ↦ -κ / r) x}) x ≃ₜ UnitAddTorus (Fin 2)) := by
  refine ((SymplecticForm.isSymplectic_constSmooth _).mpullback_subtype_val
    (keplerBoundPhaseSpace b m κ)).nonempty_homeomorph_unitAddTorus
    (contMDiff_centralForceEnergyMomentum_keplerBoundPhaseSpace b)
    (poissonBracket_centralForceEnergyMomentum_keplerBoundPhaseSpace b)
    (isCompleteVectorField_hamiltonianVectorField_keplerBoundPhaseSpace b hm hκ) (fun y hy ↦ ?_)
    ?_ ((isCompact_keplerBoundPhaseSpace_preimage_singleton b hm hκ
      x).connectedComponentIn x)
  · -- A state of the level has the energy and angular momentum of `x`, so it is regular.
    have hFy := connectedComponentIn_subset _ _ hy
    simp only [mem_preimage, comp_apply, mem_singleton_iff] at hFy
    obtain ⟨hE, hℓ⟩ := (centralForceEnergyMomentum_eq_iff b).1 hFy
    exact (isRegularPoint_centralForceEnergyMomentum_kepler b hm.ne' y.2.1 (hℓ ▸ x.2.2.2)
      (by rwa [hE, hℓ])).comp (isRegularPoint_subtype_val y)
  · rw [Module.finrank_prod, Module.finrank_eq_card_basis b.toBasis]
    simp

end TauCeti
