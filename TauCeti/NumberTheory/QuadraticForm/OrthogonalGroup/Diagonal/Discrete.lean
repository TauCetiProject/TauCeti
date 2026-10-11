/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.Diagonal.Full
public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.Integral.CompactOpen
import TauCeti.NumberTheory.Padics.RatCast
import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# Rational orthogonal and Spin points are discrete in the full adeles

Let `Q` be a quadratic form on a finite-dimensional rational vector space `V`, and let `U` be
compatible compact-open reference data whose orthogonal reference subgroups are, at almost every
prime, contained in the stabilizer of the `ℤ_p`-span of a fixed rational basis `b`. This file
proves that the rational points `O(V)(ℚ)`, `SO(V)(ℚ)` and `Spin(V)(ℚ)` form discrete subgroups of
the full adelic groups `O(V)(𝔸)`, `SO(V)(𝔸)` and `Spin(V)(𝔸)` built from `U`.

For `O` the argument is the classical one. In the neighbourhood of the identity consisting of the
adelic isometries whose real component has matrix entries of absolute value less than `2` in `b`,
and whose `p`-adic components are integral in `b` at every prime, a rational isometry has a matrix
whose entries are `p`-adic integers at every prime, hence integers, and of absolute value less
than `2`. Only finitely many rational isometries qualify, so the identity is isolated in the
diagonal image. The real factor is what bounds the size of these integer entries.

For `SO` the neighbourhood is pulled back along the injective inclusion `SO → O`, and for `Spin`
along `Spin → SO`, whose rational fibres have at most two points for a nondegenerate form.

The integral reference family `OrthogonalCompactOpens.integral` of a basis satisfies the
integrality hypothesis at every prime, so its rational points are discrete in its full adelic
groups.

## Main results

* `OrthogonalCompactOpens.discreteTopology_range_fullAdelicOrthogonalDiagonal`,
  `OrthogonalCompactOpens.discreteTopology_range_fullAdelicSpecialOrthogonalDiagonal`,
  `OrthogonalCompactOpens.discreteTopology_range_fullAdelicSpinDiagonal`: the rational points
  are discrete in the full adelic groups.
* `OrthogonalCompactOpens.discreteTopology_range_fullAdelicOrthogonalDiagonal_integral` and its
  `SO` and `Spin` companions: the same for the integral family of a basis.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §101.
* V. Platonov, A. Rapinchuk, *Algebraic Groups and Number Theory* (1994), §5.1.
-/

public section

namespace TauCeti
namespace QuadraticMap
namespace OrthogonalCompactOpens

open Filter Module
open _root_.QuadraticMap
open scoped TensorProduct Topology

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
  {Q : QuadraticForm ℚ V} (U : OrthogonalCompactOpens Q)
  {ι : Type*} [Fintype ι] [DecidableEq ι] {b : Basis ι ℚ V}

/-- Some neighbourhood of the identity in full adelic `O` contains the diagonal images of only
finitely many rational isometries. -/
private theorem exists_mem_nhds_finite_preimage_fullAdelicOrthogonalDiagonal
    (hU : ∀ᶠ p : Nat.Primes in cofinite,
      U.orthogonal p ≤ integralOrthogonalSubgroup (Q.baseChange ℚ_[p]) (b.baseChange ℚ_[p])) :
    ∃ W ∈ 𝓝 (1 : U.fullAdelicOrthogonal), (U.fullAdelicOrthogonalDiagonal ⁻¹' W).Finite := by
  -- The matrix of a real isometry in the scalar extension of `b`.
  let M : orthogonalGroup (Q.baseChange ℝ) → Matrix ι ι ℝ := fun g ↦
    LinearMap.toMatrix (b.baseChange ℝ) (b.baseChange ℝ)
      (g : ℝ ⊗[ℚ] V ≃ₗ[ℝ] ℝ ⊗[ℚ] V).toLinearMap
  have hM : Continuous M := by
    -- Supply the real automorphism-group witness explicitly, as for the full adelic groups.
    let : IsTopologicalGroup (ℝ ⊗[ℚ] V ≃ₗ[ℝ] ℝ ⊗[ℚ] V) := inferInstance
    exact (IsModuleTopology.continuous_of_linearMap
      (LinearMap.toMatrixAlgEquiv (b.baseChange ℝ)).toLinearMap).comp
      (continuous_linearEquiv_toLinearMap.comp continuous_subtype_val)
  -- Real isometries with small matrix entries, and finite adeles integral at every prime.
  let A : Set (orthogonalGroup (Q.baseChange ℝ)) := {g | ∀ i j, |M g i j| < 2}
  let B : Subgroup U.finiteAdelicOrthogonal := integralSubgroupOf U.orthogonal
    fun p ↦ U.orthogonal p ⊓ integralOrthogonalSubgroup (Q.baseChange ℚ_[p]) (b.baseChange ℚ_[p])
  have hA : IsOpen A := by
    simp only [A, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦
      isOpen_lt (continuous_abs.comp ((continuous_apply j).comp ((continuous_apply i).comp hM)))
        continuous_const
  have hB : IsOpen (B : Set U.finiteAdelicOrthogonal) :=
    isOpen_forall_mem_of_eventually_eq _ _
      (fun p ↦ (U.isOpen_orthogonal p).inter (isOpen_integralOrthogonalSubgroup _ _))
      (hU.mono fun p hp ↦ (inf_eq_left.mpr hp).symm)
  have h1A : (1 : orthogonalGroup (Q.baseChange ℝ)) ∈ A := fun i j ↦ by
    simp only [M, OneMemClass.coe_one, LinearEquiv.coe_toLinearMap_one,
      LinearMap.toMatrix_id_eq_basis_toMatrix, Basis.toMatrix_self, Matrix.one_apply]
    split_ifs <;> norm_num
  refine ⟨A ×ˢ (B : Set U.finiteAdelicOrthogonal), (hA.prod hB).mem_nhds ⟨h1A, B.one_mem⟩, ?_⟩
  -- Such a rational isometry has a matrix with entries in `{-1, 0, 1}`.
  let T : Set (ι → ι → ℚ) := Set.univ.pi fun _ ↦ Set.univ.pi fun _ ↦
    ((↑) : ℤ → ℚ) '' Set.Ioo (-2) 2
  have hT : T.Finite := Set.Finite.pi fun _ ↦ Set.Finite.pi fun _ ↦ (Set.finite_Ioo _ _).image _
  refine (hT.preimage (f := fun g : orthogonalGroup Q ↦
    (LinearMap.toMatrix b b (g : V ≃ₗ[ℚ] V).toLinearMap : ι → ι → ℚ)) ?_).subset ?_
  · exact ((LinearMap.toMatrix b b).injective.comp
      (LinearEquiv.toLinearMap_injective.comp Subtype.val_injective)).injOn
  · rintro g ⟨hgA, hgB⟩ i - j -
    set q := LinearMap.toMatrix b b (g : V ≃ₗ[ℚ] V).toLinearMap i j
    have hreal : |(q : ℝ)| < 2 := by
      simpa only [M, fullAdelicOrthogonalDiagonal_apply, toMatrix_orthogonalGroupBaseChange,
        Matrix.map_apply, eq_ratCast] using hgA i j
    have hden : q.den = 1 := Padic.forall_norm_rat_le_one_iff_den_eq_one.mp fun p ↦ by
      have hp := (Subgroup.mem_inf.mp ((mem_integralSubgroupOf _ _ _).mp hgB p)).2
      rw [mem_integralOrthogonalSubgroup_iff_norm] at hp
      simpa only [fullAdelicOrthogonalDiagonal_apply, finiteAdelicOrthogonalDiagonal_apply,
        toMatrix_orthogonalGroupBaseChange, Matrix.map_apply, eq_ratCast] using hp.1 i j
    have hq : |q.num| < 2 := by
      rw [← Rat.coe_int_num_of_den_eq_one hden] at hreal
      exact_mod_cast hreal
    exact ⟨q.num, abs_lt.mp hq, Rat.coe_int_num_of_den_eq_one hden⟩

/-- Some neighbourhood of the identity in full adelic `SO` contains the diagonal images of only
finitely many rational proper isometries. -/
private theorem exists_mem_nhds_finite_preimage_fullAdelicSpecialOrthogonalDiagonal
    (hU : ∀ᶠ p : Nat.Primes in cofinite,
      U.orthogonal p ≤ integralOrthogonalSubgroup (Q.baseChange ℚ_[p]) (b.baseChange ℚ_[p])) :
    ∃ W ∈ 𝓝 (1 : U.fullAdelicSpecialOrthogonal),
      (U.fullAdelicSpecialOrthogonalDiagonal ⁻¹' W).Finite := by
  obtain ⟨W, hW, hfin⟩ := U.exists_mem_nhds_finite_preimage_fullAdelicOrthogonalDiagonal hU
  refine ⟨U.fullAdelicSpecialOrthogonalToOrthogonal ⁻¹' W,
    U.continuous_fullAdelicSpecialOrthogonalToOrthogonal.continuousAt.preimage_mem_nhds
      (by rwa [map_one]), ?_⟩
  rw [← Set.preimage_comp, ← MonoidHom.coe_comp,
    fullAdelicSpecialOrthogonalToOrthogonal_comp_fullAdelicSpecialOrthogonalDiagonal,
    MonoidHom.coe_comp, Set.preimage_comp]
  exact hfin.preimage specialOrthogonalToOrthogonal_injective.injOn

/-- Some neighbourhood of the identity in full adelic `Spin` contains the diagonal images of only
finitely many rational Spin points. -/
private theorem exists_mem_nhds_finite_preimage_fullAdelicSpinDiagonal (hQ : Q.Nondegenerate)
    (hU : ∀ᶠ p : Nat.Primes in cofinite,
      U.orthogonal p ≤ integralOrthogonalSubgroup (Q.baseChange ℚ_[p]) (b.baseChange ℚ_[p])) :
    ∃ W ∈ 𝓝 (1 : U.fullAdelicSpin), (U.fullAdelicSpinDiagonal ⁻¹' W).Finite := by
  obtain ⟨W, hW, hfin⟩ :=
    U.exists_mem_nhds_finite_preimage_fullAdelicSpecialOrthogonalDiagonal hU
  refine ⟨U.fullAdelicSpinToSpecialOrthogonal ⁻¹' W,
    U.continuous_fullAdelicSpinToSpecialOrthogonal.continuousAt.preimage_mem_nhds
      (by rwa [map_one]), ?_⟩
  rw [← Set.preimage_comp, ← MonoidHom.coe_comp,
    fullAdelicSpinToSpecialOrthogonal_comp_fullAdelicSpinDiagonal,
    MonoidHom.coe_comp, Set.preimage_comp]
  -- The rational projection `Spin → SO` has fibres with at most two points.
  refine hfin.preimage' fun y _ ↦ ?_
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact (Set.subsingleton_singleton.preimage
      (CliffordAlgebra.spinToSpecialOrthogonal_bijective_of_subsingleton Q).injective).finite
  · rcases Set.eq_empty_or_nonempty (CliffordAlgebra.spinToSpecialOrthogonal Q ⁻¹' {y}) with
      h | ⟨x, hx⟩
    · rw [h]
      exact Set.finite_empty
    refine (Set.toFinite {x, CliffordAlgebra.spinGroup.negOne Q hQ.ne_zero * x}).subset
      fun z hz ↦ ?_
    exact CliffordAlgebra.eq_or_eq_negOne_mul_of_spinToSpecialOrthogonal_eq Q hQ z x
      (hz.trans hx.symm)

/-- **Rational isometries are discrete in the full adeles.** If the orthogonal reference
subgroups of `U` are, at almost every prime, integral in a rational basis `b`, then the diagonal
image of `O(V)(ℚ)` is a discrete subgroup of `O(V)(𝔸)`. -/
theorem discreteTopology_range_fullAdelicOrthogonalDiagonal
    (hU : ∀ᶠ p : Nat.Primes in cofinite,
      U.orthogonal p ≤ integralOrthogonalSubgroup (Q.baseChange ℚ_[p]) (b.baseChange ℚ_[p])) :
    DiscreteTopology U.fullAdelicOrthogonalDiagonal.range := by
  obtain ⟨W, hW, hfin⟩ := U.exists_mem_nhds_finite_preimage_fullAdelicOrthogonalDiagonal hU
  exact MonoidHom.discreteTopology_range_of_finite_preimage _ hW hfin

/-- **Rational proper isometries are discrete in the full adeles.** If the orthogonal reference
subgroups of `U` are, at almost every prime, integral in a rational basis `b`, then the diagonal
image of `SO(V)(ℚ)` is a discrete subgroup of `SO(V)(𝔸)`. -/
theorem discreteTopology_range_fullAdelicSpecialOrthogonalDiagonal
    (hU : ∀ᶠ p : Nat.Primes in cofinite,
      U.orthogonal p ≤ integralOrthogonalSubgroup (Q.baseChange ℚ_[p]) (b.baseChange ℚ_[p])) :
    DiscreteTopology U.fullAdelicSpecialOrthogonalDiagonal.range := by
  obtain ⟨W, hW, hfin⟩ :=
    U.exists_mem_nhds_finite_preimage_fullAdelicSpecialOrthogonalDiagonal hU
  exact MonoidHom.discreteTopology_range_of_finite_preimage _ hW hfin

/-- **Rational Spin points are discrete in the full adeles.** For a nondegenerate form, if the
orthogonal reference subgroups of `U` are, at almost every prime, integral in a rational basis
`b`, then the diagonal image of `Spin(V)(ℚ)` is a discrete subgroup of `Spin(V)(𝔸)`. -/
theorem discreteTopology_range_fullAdelicSpinDiagonal (hQ : Q.Nondegenerate)
    (hU : ∀ᶠ p : Nat.Primes in cofinite,
      U.orthogonal p ≤ integralOrthogonalSubgroup (Q.baseChange ℚ_[p]) (b.baseChange ℚ_[p])) :
    DiscreteTopology U.fullAdelicSpinDiagonal.range := by
  obtain ⟨W, hW, hfin⟩ := U.exists_mem_nhds_finite_preimage_fullAdelicSpinDiagonal hQ hU
  exact MonoidHom.discreteTopology_range_of_finite_preimage _ hW hfin

variable (b)

/-- The rational isometries are discrete in the full adelic orthogonal group of the integral
reference family of a basis. -/
theorem discreteTopology_range_fullAdelicOrthogonalDiagonal_integral (hQ : Q.Nondegenerate) :
    DiscreteTopology (integral Q hQ b).fullAdelicOrthogonalDiagonal.range :=
  discreteTopology_range_fullAdelicOrthogonalDiagonal _ (b := b)
    (.of_forall fun p ↦ (integral_orthogonal Q hQ b p).le)

/-- The rational proper isometries are discrete in the full adelic special orthogonal group of
the integral reference family of a basis. -/
theorem discreteTopology_range_fullAdelicSpecialOrthogonalDiagonal_integral
    (hQ : Q.Nondegenerate) :
    DiscreteTopology (integral Q hQ b).fullAdelicSpecialOrthogonalDiagonal.range :=
  discreteTopology_range_fullAdelicSpecialOrthogonalDiagonal _ (b := b)
    (.of_forall fun p ↦ (integral_orthogonal Q hQ b p).le)

/-- The rational Spin points are discrete in the full adelic Spin group of the integral reference
family of a basis. -/
theorem discreteTopology_range_fullAdelicSpinDiagonal_integral (hQ : Q.Nondegenerate) :
    DiscreteTopology (integral Q hQ b).fullAdelicSpinDiagonal.range :=
  discreteTopology_range_fullAdelicSpinDiagonal _ hQ (b := b)
    (.of_forall fun p ↦ (integral_orthogonal Q hQ b p).le)

end

end OrthogonalCompactOpens
end QuadraticMap
end TauCeti
