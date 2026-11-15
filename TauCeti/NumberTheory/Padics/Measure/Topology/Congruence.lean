/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.TowerCoordinates
public import Mathlib.Topology.Algebra.LinearTopology
import TauCeti.Topology.Algebra.Group.Profinite.Limit

/-!
# Congruence neighbourhoods of integral measures along a finite quotient tower

For a compact group with a tower of finite quotients, the kernel of joint coordinates at
coefficient precision `r` and group depth `n` is an open ideal of its convolution algebra of
integral measures. These ideals form a neighbourhood basis of zero for the weak topology.
The diagonal `r = n` already forms a decreasing basis, making the topology linear over `ℤ_p`
and over the measure algebra itself.

Specialising to `FiniteQuotientTower.unitTower p` gives the congruence neighbourhoods on `ℤ_pˣ`;
`FiniteQuotientTower.padicTower p` gives those on the additive group `ℤ_p`. The coefficient
precision and group depth are independent. Precision zero gives the whole ring. All primes,
including two, are allowed. No global topology instance is installed on measures.

## References

Rodrigues Jacinto and Williams, *An introduction to p-adic L-functions*, Definition 3.5,
Proposition 3.16 and Remark 3.18.
-/

public noncomputable section

open ContinuousMap Filter Topology AbstractMeasure

namespace TauCeti.FiniteQuotientTower

variable {p : ℕ} [Fact p.Prime]
  {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  {A : ℕ → Type*} [∀ n, Group (A n)] [∀ n, TopologicalSpace (A n)]
  [∀ n, DiscreteTopology (A n)] [∀ n, Finite (A n)] (T : FiniteQuotientTower Γ A)

/-- Integral measures whose coordinates at tower depth `n` vanish modulo `p ^ r`. -/
def congruenceIdeal (r n : ℕ) : Ideal D(Γ, ℤ_[p]) :=
  RingHom.ker ((T.q n).jointFiniteProjectionRingHom r)

/-- Membership in a congruence ideal means vanishing of the corresponding joint projection. -/
@[simp]
theorem mem_congruenceIdeal (r n : ℕ) (μ : D(Γ, ℤ_[p])) :
    μ ∈ T.congruenceIdeal r n ↔ jointFiniteProjection r (T.q n : C(Γ, A n)) μ = 0 := by
  simp [congruenceIdeal, ContinuousMonoidHom.jointFiniteProjectionRingHom_apply]

/-- Precision zero imposes no congruence condition. -/
@[simp]
theorem congruenceIdeal_zero_precision (n : ℕ) : T.congruenceIdeal (p := p) 0 n = ⊤ := by
  apply top_unique
  intro μ _
  exact (T.mem_congruenceIdeal 0 n μ).mpr
    (jointFiniteProjection_zero_precision (T.q n : C(Γ, A n)) μ)

/-- Increasing either coefficient precision or tower depth makes a congruence ideal smaller. -/
theorem congruenceIdeal_anti {r s m n : ℕ} (hrs : r ≤ s) (hmn : m ≤ n) :
    T.congruenceIdeal (p := p) s n ≤ T.congruenceIdeal r m := by
  intro μ hμ
  rw [mem_congruenceIdeal] at hμ ⊢
  have hprec : jointFiniteProjection r (T.q n : C(Γ, A n)) μ = 0 := by
    rw [← jointFiniteProjection_cast r s hrs, hμ]
    exact Finsupp.mapRange_zero
  have hq : (T.q m : C(Γ, A m)) =
      (⟨T.t hmn, continuous_of_discreteTopology⟩ : C(A n, A m)).comp (T.q n) := by
    ext
    simp
  rw [hq, jointFiniteProjection_comp, hprec, Finsupp.mapDomain_zero]

/-- The diagonal congruence ideals separate integral measures. -/
theorem iInf_congruenceIdeal_diag_eq_bot :
    ⨅ n, T.congruenceIdeal (p := p) n n = ⊥ := by
  apply le_antisymm _ bot_le
  intro μ hμ
  apply (Submodule.mem_bot _).mpr
  apply towerCoordinates_injective T
  apply Subtype.ext
  funext n
  apply Finsupp.ext
  intro a
  apply PadicInt.ext_of_toZModPow.mp
  intro r
  have h := T.congruenceIdeal_anti (Nat.le_max_left r n) (Nat.le_max_right r n)
    (Ideal.mem_iInf.mp hμ (max r n))
  rw [mem_congruenceIdeal] at h
  simpa [towerCoordinates_apply, jointFiniteProjection_apply, finiteProjection_apply] using
    congrArg (fun c ↦ c a) h

/-- Congruence ideals are open for the weak topology of integral measures. -/
theorem isOpen_congruenceIdeal (r n : ℕ) :
    @IsOpen _ WeakTopology (T.congruenceIdeal (p := p) r n : Set D(Γ, ℤ_[p])) := by
  let : TopologicalSpace D(Γ, ℤ_[p]) := WeakTopology
  convert (isOpen_discrete ({0} : Set (A n → ZMod (p ^ r)))).preimage
    (continuous_jointFiniteProjection r (T.q n : C(Γ, A n))) using 1
  ext μ
  simp [Finsupp.ext_iff, funext_iff]

/-- The diagonal congruence ideals form a decreasing neighbourhood basis at zero. -/
theorem hasAntitoneBasis_nhds_zero_congruenceIdeal :
    (@nhds D(Γ, ℤ_[p]) WeakTopology 0).HasAntitoneBasis
      (fun n ↦ (T.congruenceIdeal (p := p) n n : Set D(Γ, ℤ_[p]))) := by
  let : TopologicalSpace D(Γ, ℤ_[p]) := WeakTopology
  have := T.totallySeparatedSpace
  let : IsTopologicalRing D(Γ, ℤ_[p]) := isTopologicalRing_integralMeasures_weak
  let : CompactSpace D(Γ, ℤ_[p]) := compactSpace_integralMeasures_weak
  -- Apply the compact-group basis theorem to the additive groups of the ideals.
  let N : ℕ → Subgroup (Multiplicative D(Γ, ℤ_[p])) := fun n ↦
    (T.congruenceIdeal (p := p) n n).toAddSubgroup.toSubgroup
  have hN : ⨅ n, N n = ⊥ := by
    ext μ
    simp only [Subgroup.mem_iInf, N, Multiplicative.mem_toSubgroup,
      Submodule.mem_toAddSubgroup, Subgroup.mem_bot, ← Submodule.mem_iInf,
      iInf_congruenceIdeal_diag_eq_bot, Submodule.mem_bot]
    exact Multiplicative.toAdd.injective.eq_iff
  exact TauCeti.hasAntitoneBasis_nhds_one_of_iInf_eq_bot
    (N := N) (fun _ _ h ↦ T.congruenceIdeal_anti h h)
    (fun n ↦ T.isOpen_congruenceIdeal n n) hN

/-- All pairs of coefficient precision and tower depth give a neighbourhood basis at zero. -/
theorem hasBasis_nhds_zero_congruenceIdeal :
    (@nhds D(Γ, ℤ_[p]) WeakTopology 0).HasBasis (fun _ : ℕ × ℕ ↦ True)
      (fun i ↦ (T.congruenceIdeal (p := p) i.1 i.2 : Set D(Γ, ℤ_[p]))) := by
  refine T.hasAntitoneBasis_nhds_zero_congruenceIdeal.toHasBasis.to_hasBasis
    (fun n _ ↦ ⟨(n, n), trivial, subset_rfl⟩) ?_
  rintro ⟨r, n⟩ _
  exact ⟨max r n, trivial,
    T.congruenceIdeal_anti (Nat.le_max_left r n) (Nat.le_max_right r n)⟩

include T in
/-- The weak topology on integral measures along a tower is linear over `ℤ_p`. -/
theorem isLinearTopology_integralMeasures_weak :
    @IsLinearTopology ℤ_[p] D(Γ, ℤ_[p]) _ _ _ WeakTopology := by
  let : TopologicalSpace D(Γ, ℤ_[p]) := WeakTopology
  exact IsLinearTopology.mk_of_hasBasis ℤ_[p]
    (s := fun n ↦ (T.congruenceIdeal (p := p) n n).restrictScalars ℤ_[p])
    T.hasAntitoneBasis_nhds_zero_congruenceIdeal.toHasBasis

include T in
/-- The weak topology is linear over the convolution algebra of measures itself. -/
theorem isLinearTopology_integralMeasures_self_weak :
    @IsLinearTopology D(Γ, ℤ_[p]) D(Γ, ℤ_[p]) _ _ _ WeakTopology := by
  let : TopologicalSpace D(Γ, ℤ_[p]) := WeakTopology
  exact IsLinearTopology.mk_of_hasBasis _ T.hasAntitoneBasis_nhds_zero_congruenceIdeal.toHasBasis

-- Precision zero keeps a nonzero Dirac measure.
example : dirac ℤ_[2] (1 : ℤ_[2]ˣ) ∈ (unitTower 2).congruenceIdeal 0 3 := by
  rw [congruenceIdeal_zero_precision]
  trivial

-- Precision one does not keep that atom, even at group depth zero.
example : dirac ℤ_[2] (1 : ℤ_[2]ˣ) ∉ (unitTower 2).congruenceIdeal 1 0 := by
  rw [mem_congruenceIdeal, jointFiniteProjection_dirac]
  simp [Finsupp.single_eq_zero]

-- At depth one the dyadic sign atoms coincide, at depth two they differ.
example : dirac ℤ_[2] (1 : ℤ_[2]ˣ) - dirac ℤ_[2] (-1 : ℤ_[2]ˣ) ∈
    (unitTower 2).congruenceIdeal 1 1 := by
  rw [mem_congruenceIdeal, map_sub, jointFiniteProjection_dirac, jointFiniteProjection_dirac]
  have hneg : PadicInt.unitsToZModPow (p := 2) 1 (-1) = 1 := by
    apply Units.ext
    norm_num [PadicInt.coe_unitsToZModPow_apply]
    decide
  simp [hneg]

example : dirac ℤ_[2] (1 : ℤ_[2]ˣ) - dirac ℤ_[2] (-1 : ℤ_[2]ˣ) ∉
    (unitTower 2).congruenceIdeal 1 2 := by
  rw [mem_congruenceIdeal]
  intro h
  have h1 := congrArg (fun c : (ZMod (2 ^ 2))ˣ →₀ ZMod (2 ^ 1) ↦ c 1) h
  have hneg : PadicInt.unitsToZModPow (p := 2) 2 (-1) ≠ 1 := by
    intro heq
    have := congrArg (fun u : (ZMod (2 ^ 2))ˣ ↦ (u : ZMod (2 ^ 2))) heq
    norm_num [PadicInt.coe_unitsToZModPow_apply] at this
    exact (by decide : (-1 : ZMod (2 ^ 2)) ≠ 1) this
  rw [map_sub, jointFiniteProjection_dirac, jointFiniteProjection_dirac] at h1
  simp [hneg] at h1

end TauCeti.FiniteQuotientTower
