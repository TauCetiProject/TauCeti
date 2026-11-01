/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.CompletedGroupAlgebra
public import TauCeti.NumberTheory.Padics.Measure.UnitCoordinates
public import TauCeti.NumberTheory.Padics.Measure.JointFiniteProjection

/-!
# The weak topology in finite unit coordinates

Integral measures on the p-adic units embed as a closed subspace of the product of their
finite unit coordinates. Their image is exactly the compatible families, and reconstruction
from such families is continuous. Reducing each coordinate modulo every power of the prime
gives another closed embedding, into a product of finite discrete rings. Consequently weak
convergence is equivalent to eventual equality of each joint finite projection.

Compactness is supplied by the existing comparison with the completed group algebra,
`AbstractMeasure.compactSpace_integralMeasures_weak`. No topology instance is installed on
measures: every occurrence below explicitly selects `AbstractMeasure.WeakTopology`.

## References

J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, Definition 3.5,
Remark 3.11, Proposition 3.16 and Remark 3.18.
-/

public noncomputable section

open ContinuousMap Topology Filter
open scoped AbstractMeasure

namespace TauCeti

variable {p : ℕ} [Fact p.Prime]

/-- Integral unit-coordinate families compatible under pushforward between finite unit groups. -/
def compatibleUnitCoordinates (p : ℕ) [Fact p.Prime] :
    Set (∀ n : ℕ, (ZMod (p ^ n))ˣ → ℤ_[p]) :=
  {c | ∀ (m n : ℕ) (h : m ≤ n),
    (Finsupp.equivFunOnFinite.symm (c n)).mapDomain
      (ZMod.unitsMap (pow_dvd_pow p h)) = Finsupp.equivFunOnFinite.symm (c m)}

/-- Membership in the compatible families is compatibility at every pair of depths. -/
@[simp]
theorem mem_compatibleUnitCoordinates_iff (c : ∀ n : ℕ, (ZMod (p ^ n))ˣ → ℤ_[p]) :
    c ∈ compatibleUnitCoordinates p ↔ ∀ (m n : ℕ) (h : m ≤ n),
      (Finsupp.equivFunOnFinite.symm (c n)).mapDomain
        (ZMod.unitsMap (pow_dvd_pow p h)) = Finsupp.equivFunOnFinite.symm (c m) := (Iff.rfl)

end TauCeti

namespace AbstractMeasure

variable {p : ℕ} [Fact p.Prime]

/-- The finite unit coordinates of a measure, with coefficient functions rather than finitely
supported functions so that the target carries its usual product topology. -/
def unitCoordinates {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    D(ℤ_[p]ˣ, R) →ₗ[R] ∀ n : ℕ, (ZMod (p ^ n))ˣ → R :=
  LinearMap.pi fun n ↦ (Finsupp.linearEquivFunOnFinite R R _).toLinearMap.comp
    (finiteProjection (↑(PadicInt.unitsToZModPow (p := p) n)))

@[simp]
theorem unitCoordinates_apply {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (μ : D(ℤ_[p]ˣ, R)) (n : ℕ) (a : (ZMod (p ^ n))ˣ) :
    unitCoordinates μ n a = finiteProjection (↑(PadicInt.unitsToZModPow (p := p) n)) μ a := (rfl)

/-- Finite unit coordinates determine a measure. -/
theorem unitCoordinates_injective {R : Type*} [NormedCommRing R] :
    Function.Injective (unitCoordinates (p := p) (R := R)) := by
  intro μ ν h
  apply finiteProjection_unitsToZModPow_ext μ ν
  intro n
  ext a
  exact congrArg (fun c ↦ c n a) h

/-- Taking finite unit coordinates is weakly continuous. -/
theorem continuous_unitCoordinates_weak {R : Type*} [NormedCommRing R] :
    @Continuous _ _ (WeakTopology (X := ℤ_[p]ˣ) (R := R) (E := R)) inferInstance
      (unitCoordinates (p := p) (R := R)) := by
  let : TopologicalSpace D(ℤ_[p]ˣ, R) := WeakTopology
  refine continuous_pi fun n ↦ ?_
  exact (continuous_finiteProjection (R := R)
    (↑(PadicInt.unitsToZModPow (p := p) n))).congr fun μ ↦ by
      funext a
      exact (unitCoordinates_apply μ n a).symm

/-- Integral unit coordinates give a closed embedding for the weak topology. In particular,
they induce exactly that topology, not the continuous-dual operator-norm topology. -/
theorem isClosedEmbedding_unitCoordinates_weak :
    @IsClosedEmbedding _ _ (WeakTopology (X := ℤ_[p]ˣ) (R := ℤ_[p]) (E := ℤ_[p]))
      inferInstance (unitCoordinates (p := p) (R := ℤ_[p])) := by
  let : TopologicalSpace D(ℤ_[p]ˣ, ℤ_[p]) := WeakTopology
  let : CompactSpace D(ℤ_[p]ˣ, ℤ_[p]) := compactSpace_integralMeasures_weak
  exact continuous_unitCoordinates_weak.isClosedEmbedding unitCoordinates_injective

/-- The image of integral unit coordinates consists precisely of the families compatible
under the pushforwards between finite unit groups. The finite-support conversion does not
impose an extra condition, since each unit quotient is finite. -/
theorem range_unitCoordinates :
    Set.range (unitCoordinates (p := p) (R := ℤ_[p])) =
      TauCeti.compatibleUnitCoordinates p := by
  ext c
  rw [TauCeti.mem_compatibleUnitCoordinates_iff]
  constructor
  · rintro ⟨μ, rfl⟩ m n h
    have hc (k : ℕ) : Finsupp.equivFunOnFinite.symm (unitCoordinates μ k) =
        finiteProjection (↑(PadicInt.unitsToZModPow (p := p) k)) μ := by
      ext a
      simp
    simpa only [hc] using mapDomain_finiteProjection_unitsToZModPow μ m n h
  · intro hc
    refine ⟨TauCeti.ofUnitCoordinates (fun n ↦ Finsupp.equivFunOnFinite.symm (c n)) hc, ?_⟩
    funext n a
    simp [TauCeti.finiteProjection_ofUnitCoordinates]

/-- Joint coordinates record finite unit coefficients at independent coefficient precision
`r` and group depth `n`. Each target ring has its discrete topology. -/
def jointUnitCoordinates : D(ℤ_[p]ˣ, ℤ_[p]) →+
    ∀ r n : ℕ, (ZMod (p ^ n))ˣ → ZMod (p ^ r) where
  toFun μ r n a := jointFiniteProjection r (↑(PadicInt.unitsToZModPow (p := p) n)) μ a
  map_zero' := by ext r n a; simp
  map_add' μ ν := by ext r n a; simp

/-- A joint unit coordinate is the coefficient of the corresponding joint finite projection. -/
theorem jointUnitCoordinates_apply_eq_jointFiniteProjection (μ : D(ℤ_[p]ˣ, ℤ_[p]))
    (r n : ℕ) (a : (ZMod (p ^ n))ˣ) :
    jointUnitCoordinates μ r n a =
      jointFiniteProjection r (↑(PadicInt.unitsToZModPow (p := p) n)) μ a := (rfl)

@[simp]
theorem jointUnitCoordinates_apply (μ : D(ℤ_[p]ˣ, ℤ_[p])) (r n : ℕ)
    (a : (ZMod (p ^ n))ˣ) :
    jointUnitCoordinates μ r n a = PadicInt.toZModPow r (unitCoordinates μ n a) := by
  simp [jointUnitCoordinates_apply_eq_jointFiniteProjection, finiteProjection_apply]

/-- Joint finite unit coordinates separate integral measures. -/
theorem jointUnitCoordinates_injective :
    Function.Injective (jointUnitCoordinates (p := p)) := by
  intro μ ν h
  apply unitCoordinates_injective
  funext n a
  apply PadicInt.ext_of_toZModPow.mp
  intro r
  simpa only [jointUnitCoordinates_apply] using congrArg (fun c ↦ c r n a) h

/-- Joint finite unit coordinates vary continuously in the weak topology. -/
theorem continuous_jointUnitCoordinates_weak :
    @Continuous _ _ (WeakTopology (X := ℤ_[p]ˣ) (R := ℤ_[p]) (E := ℤ_[p]))
      inferInstance (jointUnitCoordinates (p := p)) := by
  let : TopologicalSpace D(ℤ_[p]ˣ, ℤ_[p]) := WeakTopology
  refine continuous_pi fun r ↦ continuous_pi fun n ↦ continuous_pi fun a ↦ ?_
  exact ((PadicInt.continuous_toZModPow r).comp
    ((continuous_apply a).comp ((continuous_apply n).comp
      continuous_unitCoordinates_weak))).congr fun μ ↦ (jointUnitCoordinates_apply μ r n a).symm

/-- Joint finite unit coordinates give a closed embedding into a product of finite discrete
rings. Both coefficient precision and unit-group depth are allowed to vary independently. -/
theorem isClosedEmbedding_jointUnitCoordinates_weak :
    @IsClosedEmbedding _ _ (WeakTopology (X := ℤ_[p]ˣ) (R := ℤ_[p]) (E := ℤ_[p]))
      inferInstance (jointUnitCoordinates (p := p)) := by
  let : TopologicalSpace D(ℤ_[p]ˣ, ℤ_[p]) := WeakTopology
  let : CompactSpace D(ℤ_[p]ˣ, ℤ_[p]) := compactSpace_integralMeasures_weak
  exact continuous_jointUnitCoordinates_weak.isClosedEmbedding jointUnitCoordinates_injective

/-- Weak convergence of integral unit measures is equivalent to eventual equality of every
joint finite projection. This holds for arbitrary filters, not just sequences. -/
theorem tendsto_weak_iff_jointFiniteProjection {ι : Type*} {l : Filter ι}
    {μ : ι → D(ℤ_[p]ˣ, ℤ_[p])} {ν : D(ℤ_[p]ˣ, ℤ_[p])} :
    @Tendsto _ _ μ l (@nhds _ (WeakTopology (X := ℤ_[p]ˣ) (R := ℤ_[p]) (E := ℤ_[p])) ν) ↔
      ∀ r n : ℕ, ∀ᶠ i in l,
        jointFiniteProjection r
          (↑(PadicInt.unitsToZModPow (p := p) n) : C(ℤ_[p]ˣ, (ZMod (p ^ n))ˣ)) (μ i) =
          jointFiniteProjection r
            (↑(PadicInt.unitsToZModPow (p := p) n) : C(ℤ_[p]ˣ, (ZMod (p ^ n))ˣ)) ν := by
  let : TopologicalSpace D(ℤ_[p]ˣ, ℤ_[p]) := WeakTopology
  rw [isClosedEmbedding_jointUnitCoordinates_weak.tendsto_nhds_iff]
  simp only [tendsto_pi_nhds, Function.comp_apply]
  constructor
  · intro h r n
    have ha (a : (ZMod (p ^ n))ˣ) := h r n a
    simp only [tendsto_pure, nhds_discrete,
      jointUnitCoordinates_apply_eq_jointFiniteProjection] at ha
    filter_upwards [eventually_all.mpr ha] with i hi
    exact Finsupp.ext hi
  · intro h r n a
    rw [nhds_discrete, tendsto_pure]
    filter_upwards [h r n] with i hi
    simpa only [jointUnitCoordinates_apply_eq_jointFiniteProjection] using
      congrArg (fun c ↦ c a) hi

end AbstractMeasure

namespace TauCeti

variable {p : ℕ} [Fact p.Prime]

/-- Reconstruction of a measure from compatible integral unit coordinates is continuous for
the product topology on coordinates and the weak topology on measures. -/
theorem continuous_ofUnitCoordinates_weak :
    @Continuous _ _ inferInstance
      (AbstractMeasure.WeakTopology (X := ℤ_[p]ˣ) (R := ℤ_[p]) (E := ℤ_[p]))
      (fun c : compatibleUnitCoordinates p ↦
        ofUnitCoordinates (fun n ↦ Finsupp.equivFunOnFinite.symm (c.val n))
          ((mem_compatibleUnitCoordinates_iff c.val).mp c.property)) := by
  let : TopologicalSpace D(ℤ_[p]ˣ, ℤ_[p]) := AbstractMeasure.WeakTopology
  apply AbstractMeasure.isClosedEmbedding_unitCoordinates_weak.isEmbedding.continuous_iff.mpr
  convert continuous_subtype_val using 1
  funext c n a
  simp [finiteProjection_ofUnitCoordinates]

end TauCeti
