/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.CompletedGroupAlgebra
public import TauCeti.NumberTheory.Padics.Measure.UnitCoordinates
public import Mathlib.Topology.Algebra.LinearTopology
import TauCeti.Topology.Algebra.Group.Profinite.Limit

/-!
# Congruence neighbourhoods of integral unit measures

The kernel of finite unit coordinates at coefficient precision `r` and group depth `n` is an
open ideal of the convolution algebra of integral measures on `ℤ_pˣ`. These ideals form a
neighbourhood basis of zero for the weak topology. The diagonal `r = n` already forms a
decreasing basis, making the topology linear over `ℤ_p` (and over the measure algebra itself).

The coefficient precision and group depth are independent. In particular precision zero gives
the whole ring, rather than imposing a condition at a nonzero precision. All primes, including
two, are allowed. No global topology instance is installed on measures.

## References

Rodrigues Jacinto and Williams, *An introduction to p-adic L-functions*, Definition 3.5,
Proposition 3.16 and Remark 3.18.
-/

public noncomputable section

open ContinuousMap Filter Topology
open scoped AbstractMeasure

namespace AbstractMeasure

variable {p : ℕ} [Fact p.Prime]

/-- The ideal of integral unit measures whose coordinates at depth `n` vanish modulo `p ^ r`. -/
def unitCongruenceIdeal (r n : ℕ) : Ideal D(ℤ_[p]ˣ, ℤ_[p]) :=
  RingHom.ker ((PadicInt.unitsToZModPow (p := p) n).jointFiniteProjectionRingHom r)

/-- Membership in a congruence ideal means vanishing of the corresponding joint projection. -/
@[simp]
theorem mem_unitCongruenceIdeal (r n : ℕ) (μ : D(ℤ_[p]ˣ, ℤ_[p])) :
    μ ∈ unitCongruenceIdeal (p := p) r n ↔
      jointFiniteProjection r (PadicInt.unitsToZModPow (p := p) n).toContinuousMap μ = 0 := by
  simp [unitCongruenceIdeal, ContinuousMonoidHom.jointFiniteProjectionRingHom_apply]

/-- Precision zero imposes no congruence condition. -/
@[simp]
theorem unitCongruenceIdeal_zero_precision (n : ℕ) : unitCongruenceIdeal (p := p) 0 n = ⊤ := by
  apply top_unique
  intro μ _
  exact (mem_unitCongruenceIdeal 0 n μ).mpr
    (jointFiniteProjection_zero_precision
      (PadicInt.unitsToZModPow (p := p) n).toContinuousMap μ)

/-- Increasing either coefficient precision or unit depth makes a congruence ideal smaller. -/
theorem unitCongruenceIdeal_antitone {r s m n : ℕ} (hrs : r ≤ s) (hmn : m ≤ n) :
    unitCongruenceIdeal (p := p) s n ≤ unitCongruenceIdeal (p := p) r m := by
  intro μ hμ
  rw [mem_unitCongruenceIdeal] at hμ ⊢
  have hprec : jointFiniteProjection r
      (PadicInt.unitsToZModPow (p := p) n).toContinuousMap μ = 0 := by
    rw [← jointFiniteProjection_cast r s hrs, hμ]
    exact Finsupp.mapRange_zero
  let t : C((ZMod (p ^ n))ˣ, (ZMod (p ^ m))ˣ) :=
    equivFnOfDiscrete.symm (ZMod.unitsMap (pow_dvd_pow p hmn))
  have ht : t.comp (PadicInt.unitsToZModPow (p := p) n).toContinuousMap =
      (PadicInt.unitsToZModPow (p := p) m).toContinuousMap := by
    ext u
    simp [t]
  rw [← ht, jointFiniteProjection_comp, hprec, Finsupp.mapDomain_zero]

/-- The diagonal congruence ideals separate integral unit measures. -/
theorem iInf_unitCongruenceIdeal_diag :
    ⨅ n, unitCongruenceIdeal (p := p) n n = ⊥ := by
  apply le_antisymm _ bot_le
  intro μ hμ
  apply (Submodule.mem_bot _).mpr
  apply finiteProjection_unitsToZModPow_ext
  intro n
  apply Finsupp.ext
  intro a
  apply PadicInt.ext_of_toZModPow.mp
  intro r
  have h := unitCongruenceIdeal_antitone (Nat.le_max_left r n) (Nat.le_max_right r n)
    (Ideal.mem_iInf.mp hμ (max r n))
  rw [mem_unitCongruenceIdeal] at h
  simpa [jointFiniteProjection_apply, finiteProjection_apply] using
    congrArg (fun c ↦ c a) h

section Weak

/-- Congruence ideals are open for the weak topology of integral unit measures. -/
theorem isOpen_unitCongruenceIdeal (r n : ℕ) :
    @IsOpen _ WeakTopology (unitCongruenceIdeal (p := p) r n : Set D(ℤ_[p]ˣ, ℤ_[p])) := by
  let : TopologicalSpace D(ℤ_[p]ˣ, ℤ_[p]) := WeakTopology
  have hcont : Continuous (fun μ : D(ℤ_[p]ˣ, ℤ_[p]) ↦ fun a : (ZMod (p ^ n))ˣ ↦
      jointFiniteProjection r (PadicInt.unitsToZModPow (p := p) n).toContinuousMap μ a) := by
    apply continuous_pi
    intro a
    simpa only [Function.comp_def, jointFiniteProjection_apply, finiteProjection_apply] using
      (PadicInt.continuous_toZModPow r).comp
        ((continuous_apply a).comp
          (continuous_finiteProjection (PadicInt.unitsToZModPow (p := p) n).toContinuousMap))
  convert (isOpen_discrete ({0} : Set ((ZMod (p ^ n))ˣ → ZMod (p ^ r)))).preimage
    hcont using 1
  ext μ
  simp [Finsupp.ext_iff, funext_iff]

/-- The diagonal congruence ideals form a decreasing neighbourhood basis at zero. -/
theorem hasAntitoneBasis_nhds_zero_unitCongruenceIdeal :
    (@nhds D(ℤ_[p]ˣ, ℤ_[p]) WeakTopology 0).HasAntitoneBasis
      (fun n ↦ (unitCongruenceIdeal (p := p) n n : Set D(ℤ_[p]ˣ, ℤ_[p]))) := by
  let : TopologicalSpace D(ℤ_[p]ˣ, ℤ_[p]) := WeakTopology
  let : IsTopologicalRing D(ℤ_[p]ˣ, ℤ_[p]) := isTopologicalRing_integralMeasures_weak
  let : CompactSpace D(ℤ_[p]ˣ, ℤ_[p]) := compactSpace_integralMeasures_weak
  -- Apply the compact-group basis theorem to the additive groups of the ideals.
  let N : ℕ → Subgroup (Multiplicative D(ℤ_[p]ˣ, ℤ_[p])) := fun n ↦
    (unitCongruenceIdeal (p := p) n n).toAddSubgroup.toSubgroup
  have hN : ⨅ n, N n = ⊥ := by
    ext μ
    simp only [Subgroup.mem_iInf, N, Multiplicative.mem_toSubgroup,
      Submodule.mem_toAddSubgroup, Subgroup.mem_bot, ← Submodule.mem_iInf,
      iInf_unitCongruenceIdeal_diag, Submodule.mem_bot]
    exact Multiplicative.toAdd.injective.eq_iff
  exact TauCeti.hasAntitoneBasis_nhds_one_of_iInf_eq_bot
    (N := N) (fun _ _ h ↦ unitCongruenceIdeal_antitone h h)
    (fun n ↦ isOpen_unitCongruenceIdeal n n) hN

/-- All pairs of coefficient precision and unit depth give a neighbourhood basis at zero. -/
theorem hasBasis_nhds_zero_unitCongruenceIdeal :
    (@nhds D(ℤ_[p]ˣ, ℤ_[p]) WeakTopology 0).HasBasis (fun _ : ℕ × ℕ ↦ True)
      (fun i ↦ (unitCongruenceIdeal (p := p) i.1 i.2 : Set D(ℤ_[p]ˣ, ℤ_[p]))) := by
  refine hasAntitoneBasis_nhds_zero_unitCongruenceIdeal.toHasBasis.to_hasBasis
    (fun n _ ↦ ⟨(n, n), trivial, subset_rfl⟩) ?_
  rintro ⟨r, n⟩ _
  exact ⟨max r n, trivial,
    unitCongruenceIdeal_antitone (Nat.le_max_left r n) (Nat.le_max_right r n)⟩

/-- The weak topology on integral unit measures is linear over `ℤ_p`. -/
theorem isLinearTopology_unitMeasures_weak :
    @IsLinearTopology ℤ_[p] D(ℤ_[p]ˣ, ℤ_[p]) _ _ _ WeakTopology := by
  let : TopologicalSpace D(ℤ_[p]ˣ, ℤ_[p]) := WeakTopology
  exact IsLinearTopology.mk_of_hasBasis ℤ_[p]
    (s := fun n ↦ (unitCongruenceIdeal (p := p) n n).restrictScalars ℤ_[p])
    hasAntitoneBasis_nhds_zero_unitCongruenceIdeal.toHasBasis

/-- The same weak topology is linear over the convolution algebra of measures itself. -/
theorem isLinearTopology_unitMeasures_self_weak :
    @IsLinearTopology D(ℤ_[p]ˣ, ℤ_[p]) D(ℤ_[p]ˣ, ℤ_[p]) _ _ _ WeakTopology := by
  let : TopologicalSpace D(ℤ_[p]ˣ, ℤ_[p]) := WeakTopology
  exact IsLinearTopology.mk_of_hasBasis _ hasAntitoneBasis_nhds_zero_unitCongruenceIdeal.toHasBasis

end Weak

-- Precision zero keeps a nonzero Dirac measure.
example : dirac ℤ_[2] (1 : ℤ_[2]ˣ) ∈ unitCongruenceIdeal 0 3 := by
  rw [unitCongruenceIdeal_zero_precision]
  trivial

-- Precision one does not keep that atom, even at group depth zero.
example : dirac ℤ_[2] (1 : ℤ_[2]ˣ) ∉ unitCongruenceIdeal 1 0 := by
  rw [mem_unitCongruenceIdeal, jointFiniteProjection_dirac]
  simp [Finsupp.single_eq_zero]

-- At depth one the dyadic sign atoms coincide, at depth two they differ.
example : dirac ℤ_[2] (1 : ℤ_[2]ˣ) - dirac ℤ_[2] (-1 : ℤ_[2]ˣ) ∈
    unitCongruenceIdeal 1 1 := by
  rw [mem_unitCongruenceIdeal, map_sub, jointFiniteProjection_dirac, jointFiniteProjection_dirac]
  have hneg : PadicInt.unitsToZModPow (p := 2) 1 (-1) = 1 := by
    apply Units.ext
    norm_num [PadicInt.coe_unitsToZModPow_apply]
    decide
  simp [hneg]

example : dirac ℤ_[2] (1 : ℤ_[2]ˣ) - dirac ℤ_[2] (-1 : ℤ_[2]ˣ) ∉
    unitCongruenceIdeal 1 2 := by
  rw [mem_unitCongruenceIdeal]
  intro h
  have h1 := congrArg (fun c : (ZMod (2 ^ 2))ˣ →₀ ZMod (2 ^ 1) ↦ c 1) h
  have hneg : PadicInt.unitsToZModPow (p := 2) 2 (-1) ≠ 1 := by
    intro heq
    have := congrArg (fun u : (ZMod (2 ^ 2))ˣ ↦ (u : ZMod (2 ^ 2))) heq
    norm_num [PadicInt.coe_unitsToZModPow_apply] at this
    exact (by decide : (-1 : ZMod (2 ^ 2)) ≠ 1) this
  rw [map_sub, jointFiniteProjection_dirac, jointFiniteProjection_dirac] at h1
  simp [hneg] at h1

end AbstractMeasure
