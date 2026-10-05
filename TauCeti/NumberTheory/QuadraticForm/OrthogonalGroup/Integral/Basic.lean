/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.Topology.Algebra.QuadraticForm.OrthogonalGroup.Closed
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Instances.Matrix
import TauCeti.LinearAlgebra.QuadraticForm.SpecialOrthogonal.Hyperbolic

/-!
# Integral orthogonal subgroups in a basis

For a basis of a quadratic space over `ℚ_[p]`, the integral orthogonal subgroup consists of
isometries whose matrices and inverse matrices have entries in `ℤ_[p]`. Both conditions are
included, so the construction is a subgroup even for a degenerate quadratic form. This is the
reference family used to form restricted products of local orthogonal groups.

The subgroup is compact and open in the canonical forward-and-inverse topology on linear
isometries. For a rational quadratic space and a rational basis, every rational isometry belongs
to these subgroups at all but finitely many primes. No integrality of the quadratic form itself
is required: the exceptional primes come from the denominators of the isometry and its inverse.

-/

public section

namespace TauCeti
namespace QuadraticMap

open Module Filter
open scoped TensorProduct Topology

noncomputable section

variable {p : ℕ} [Fact p.Prime] {V ι : Type*}
  [AddCommGroup V] [Module ℚ_[p] V] [Fintype ι] [DecidableEq ι]
  (Q : QuadraticForm ℚ_[p] V) (b : Basis ι ℚ_[p] V)

/-- The subgroup of isometries integral in `b` in both directions. Equivalently, these
isometries preserve the `ℤ_[p]`-span of the basis as a set. -/
def integralOrthogonalSubgroup : Subgroup (orthogonalGroup Q) :=
  let f := (LinearMap.toMatrixAlgEquiv b).symm.toMonoidHom.comp
    (PadicInt.Coe.ringHom.mapMatrix.toMonoidHom)
  (MonoidHom.mrange f).units.comap
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv ℚ_[p] V).symm.toMonoidHom.comp
      (orthogonalGroup Q).subtype)

/-- Membership is integrality of the matrix entries of both the isometry and its inverse. -/
@[simp]
theorem mem_integralOrthogonalSubgroup_iff (g : orthogonalGroup Q) :
    g ∈ integralOrthogonalSubgroup Q b ↔
      (∀ i j, LinearMap.toMatrix b b (g : V ≃ₗ[ℚ_[p]] V).toLinearMap i j ∈
        PadicInt.subring p) ∧
      (∀ i j, LinearMap.toMatrix b b (g⁻¹ : V ≃ₗ[ℚ_[p]] V).toLinearMap i j ∈
        PadicInt.subring p) := by
  have hrange (a : Module.End ℚ_[p] V) :
      a ∈ MonoidHom.mrange ((LinearMap.toMatrixAlgEquiv b).symm.toMonoidHom.comp
        PadicInt.Coe.ringHom.mapMatrix.toMonoidHom) ↔
      ∀ i j, LinearMap.toMatrix b b a i j ∈ PadicInt.subring p := by
    constructor
    · rintro ⟨m, rfl⟩ i j
      -- Matrix and monoid coercions obscure the algebra-equivalence cancellation.
      change (LinearMap.toMatrixAlgEquiv b)
        ((LinearMap.toMatrixAlgEquiv b).symm (m.map PadicInt.Coe.ringHom)) i j ∈ _
      rw [AlgEquiv.apply_symm_apply]
      exact (m i j).property
    · intro h
      refine ⟨fun i j ↦ ⟨_, h i j⟩, ?_⟩
      exact (LinearMap.toMatrixAlgEquiv b).symm_apply_apply a
  -- The unit equivalence identifies its value and inverse value with the two underlying
  -- endomorphisms. Unfold only this construction before applying the range characterization.
  unfold integralOrthogonalSubgroup
  rw [Subgroup.mem_comap, Submonoid.mem_units_iff]
  exact and_congr (hrange _) (hrange _)

/-- The same membership test written as bounds on the `p`-adic norms of the entries. -/
theorem mem_integralOrthogonalSubgroup_iff_norm (g : orthogonalGroup Q) :
    g ∈ integralOrthogonalSubgroup Q b ↔
      (∀ i j, ‖LinearMap.toMatrix b b (g : V ≃ₗ[ℚ_[p]] V).toLinearMap i j‖ ≤ 1) ∧
      (∀ i j, ‖LinearMap.toMatrix b b (g⁻¹ : V ≃ₗ[ℚ_[p]] V).toLinearMap i j‖ ≤ 1) := by
  simp [PadicInt.mem_subring_iff]

/-- Transporting the basis along an isometry transports the integral orthogonal subgroup. -/
theorem mem_integralOrthogonalSubgroup_orthogonalGroupCongr
    {W : Type*} [AddCommGroup W] [Module ℚ_[p] W] {Q' : QuadraticForm ℚ_[p] W}
    (e : Q.IsometryEquiv Q') (g : orthogonalGroup Q) :
    orthogonalGroupCongr e g ∈ integralOrthogonalSubgroup Q' (b.map e.toLinearEquiv) ↔
      g ∈ integralOrthogonalSubgroup Q b := by
  have hm (g : orthogonalGroup Q) :
      LinearMap.toMatrix (b.map e.toLinearEquiv) (b.map e.toLinearEquiv)
        (orthogonalGroupCongr e g : W ≃ₗ[ℚ_[p]] W).toLinearMap =
      LinearMap.toMatrix b b (g : V ≃ₗ[ℚ_[p]] V).toLinearMap := by
    ext i j
    simp [LinearMap.toMatrix_apply, coe_orthogonalGroupCongr_apply]
  simp only [mem_integralOrthogonalSubgroup_iff, ← Subgroup.coe_inv, ← map_inv, hm]

/-- The integral orthogonal subgroup is open in the canonical topology on isometries. -/
theorem isOpen_integralOrthogonalSubgroup :
    IsOpen (integralOrthogonalSubgroup Q b : Set (orthogonalGroup Q)) := by
  let : FiniteDimensional ℚ_[p] V := Module.Finite.of_basis b
  have hc : Continuous (fun g : orthogonalGroup Q ↦
      LinearMap.toMatrix b b (g : V ≃ₗ[ℚ_[p]] V).toLinearMap) :=
    (IsModuleTopology.continuous_of_linearMap
      (LinearMap.toMatrixAlgEquiv b).toLinearMap).comp
      (continuous_linearEquiv_toLinearMap.comp continuous_subtype_val)
  have ho : IsOpen (PadicInt.subring p : Set ℚ_[p]) := by
    simpa using PadicInt.isOpenEmbedding_coe.isOpen_range
  have hset : (integralOrthogonalSubgroup Q b : Set (orthogonalGroup Q)) =
      {g : orthogonalGroup Q | ∀ i j, LinearMap.toMatrix b b (g : V ≃ₗ[ℚ_[p]] V).toLinearMap i j ∈
        PadicInt.subring p} ∩
      {g : orthogonalGroup Q | ∀ i j, LinearMap.toMatrix b b (g⁻¹ : V ≃ₗ[ℚ_[p]] V).toLinearMap i j ∈
        PadicInt.subring p} := by
    ext g
    exact mem_integralOrthogonalSubgroup_iff Q b g
  rw [hset]
  simp only [Set.ofPred_forall]
  exact (isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦
    ho.preimage ((continuous_apply j).comp ((continuous_apply i).comp hc))).inter
    (isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦
      ho.preimage ((continuous_apply j).comp ((continuous_apply i).comp
        (hc.comp continuous_inv))))

/-- The integral orthogonal subgroup is compact, including for degenerate forms. -/
theorem isCompact_integralOrthogonalSubgroup :
    IsCompact (integralOrthogonalSubgroup Q b : Set (orthogonalGroup Q)) := by
  let : FiniteDimensional ℚ_[p] V := Module.Finite.of_basis b
  let : Invertible (2 : ℚ_[p]) := invertibleOfNonzero two_ne_zero
  let : IsModuleTopology ℚ_[p] (Matrix ι ι ℚ_[p]) :=
    inferInstanceAs (IsModuleTopology ℚ_[p] (ι → ι → ℚ_[p]))
  let : CompactSpace (Matrix ι ι ℤ_[p]) := inferInstanceAs (CompactSpace (ι → ι → ℤ_[p]))
  let f := (LinearMap.toMatrixAlgEquiv b).symm.toMonoidHom.comp
    (PadicInt.Coe.ringHom.mapMatrix.toMonoidHom)
  have hf : Continuous f :=
    (IsModuleTopology.continuous_of_linearMap
      (LinearMap.toMatrixAlgEquiv b).symm.toLinearMap).comp
      (continuous_pi fun i ↦ continuous_pi fun j ↦
        continuous_subtype_val.comp ((continuous_apply j).comp (continuous_apply i)))
  have hcompact : IsCompact ((MonoidHom.mrange f).units : Set (Module.End ℚ_[p] V)ˣ) :=
    Submonoid.units_isCompact (isCompact_range hf)
  let e := generalLinearContinuousMulEquiv (K := ℚ_[p]) (V := V)
  have he := e.symm.toHomeomorph.isClosedEmbedding.comp
    (isClosed_orthogonalGroup Q).isClosedEmbedding_subtypeVal
  convert he.isCompact_preimage hcompact using 1
  ext g
  simp only [Set.mem_preimage, Function.comp_apply]
  -- `toHomeomorph` and the continuous multiplicative equivalence use the same function;
  -- this coercion is definitional, so rewriting the algebraic equivalence below needs it exposed.
  rw [show e.symm.toHomeomorph (g : V ≃ₗ[ℚ_[p]] V) = e.symm (g : V ≃ₗ[ℚ_[p]] V) from rfl]
  have heq : e.symm (g : V ≃ₗ[ℚ_[p]] V) =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv ℚ_[p] V).symm
        (g : V ≃ₗ[ℚ_[p]] V) :=
    congrArg (fun e : (Module.End ℚ_[p] V)ˣ ≃* V ≃ₗ[ℚ_[p]] V ↦
      e.symm (g : V ≃ₗ[ℚ_[p]] V)) coe_generalLinearContinuousMulEquiv
  rw [heq]
  rfl

section Rational

/-- Two is invertible over the rational coefficients used for scalar extension. -/
local instance invertibleTwoRat : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
  (Q₀ : QuadraticForm ℚ W) (b₀ : Basis ι ℚ W)

/-- Avoiding the denominators of the entries of an isometry and its inverse ensures local
integrality. This gives an explicit finite exceptional set. -/
theorem mem_integralOrthogonalSubgroup_baseChange_of_not_dvd_den
    (g : orthogonalGroup Q₀)
    (hg : ∀ i j, ¬ p ∣ (LinearMap.toMatrix b₀ b₀ (g : W ≃ₗ[ℚ] W).toLinearMap i j).den)
    (hginv : ∀ i j, ¬ p ∣ (LinearMap.toMatrix b₀ b₀ (g⁻¹ : W ≃ₗ[ℚ] W).toLinearMap i j).den) :
    orthogonalGroupBaseChange (A := ℚ_[p]) Q₀ g ∈
      integralOrthogonalSubgroup (Q₀.baseChange ℚ_[p]) (b₀.baseChange ℚ_[p]) := by
  rw [mem_integralOrthogonalSubgroup_iff_norm]
  constructor
  · rw [toMatrix_orthogonalGroupBaseChange]
    exact fun i j ↦ Padic.norm_rat_le_one (hg i j)
  · have hinv := map_inv (orthogonalGroupBaseChange (A := ℚ_[p]) Q₀) g
    -- Rewrite the inverse inside the subgroup before forgetting to a linear equivalence.
    convert (show ∀ i j, ‖LinearMap.toMatrix (b₀.baseChange ℚ_[p]) (b₀.baseChange ℚ_[p])
      (orthogonalGroupBaseChange (A := ℚ_[p]) Q₀ g⁻¹ :
        ℚ_[p] ⊗[ℚ] W ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[ℚ] W).toLinearMap i j‖ ≤ 1 from by
      rw [toMatrix_orthogonalGroupBaseChange]
      exact fun i j ↦ Padic.norm_rat_le_one (hginv i j)) using 1
    rw [hinv]
    rfl

/-- Every rational isometry is integral in a fixed rational basis at almost every prime, in
both directions. Thus its local scalar extensions define a point of the restricted product
relative to the integral orthogonal subgroups. -/
theorem eventually_mem_integralOrthogonalSubgroup (g : orthogonalGroup Q₀) :
    ∀ᶠ p : Nat.Primes in cofinite,
      let _ : Fact (p : ℕ).Prime := ⟨p.property⟩
      orthogonalGroupBaseChange (A := ℚ_[p]) Q₀ g ∈
        integralOrthogonalSubgroup (Q₀.baseChange ℚ_[p]) (b₀.baseChange ℚ_[p]) := by
  have hden (q : ℚ) : ∀ᶠ p : Nat.Primes in cofinite, ¬ (p : ℕ) ∣ q.den := by
    apply Filter.eventually_cofinite.mpr
    apply (Set.finite_Iic q.den).preimage Subtype.val_injective.injOn |>.subset
    intro p hp
    exact Nat.le_of_dvd q.den_pos (not_not.mp hp)
  have hg := Filter.eventually_all.mpr fun i ↦ Filter.eventually_all.mpr fun j ↦
    hden (LinearMap.toMatrix b₀ b₀ (g : W ≃ₗ[ℚ] W).toLinearMap i j)
  have hginv := Filter.eventually_all.mpr fun i ↦ Filter.eventually_all.mpr fun j ↦
    hden (LinearMap.toMatrix b₀ b₀ (g⁻¹ : W ≃ₗ[ℚ] W).toLinearMap i j)
  filter_upwards [hg, hginv] with p hp hpinv
  let : Fact (p : ℕ).Prime := ⟨p.property⟩
  exact mem_integralOrthogonalSubgroup_baseChange_of_not_dvd_den Q₀ b₀ g hp hpinv

-- A non-integral rational isometry of `x₀² - x₁²`: the torus parameter `2` has entry `5/4`.
-- It is nevertheless integral in the base-changed standard basis at almost every prime.
example : ∃ g : orthogonalGroup (hyperbolicPlane ℚ),
    LinearMap.toMatrix (Pi.basisFun ℚ (Fin 2)) (Pi.basisFun ℚ (Fin 2))
      (g : (Fin 2 → ℚ) ≃ₗ[ℚ] (Fin 2 → ℚ)).toLinearMap 0 0 = 5 / 4 ∧
    (∀ᶠ p : Nat.Primes in cofinite,
      let _ : Fact (p : ℕ).Prime := ⟨p.property⟩
      orthogonalGroupBaseChange (A := ℚ_[p]) (hyperbolicPlane ℚ) g ∈
        integralOrthogonalSubgroup ((hyperbolicPlane ℚ).baseChange ℚ_[p])
          ((Pi.basisFun ℚ (Fin 2)).baseChange ℚ_[p])) := by
  let t : ℚˣ := Units.mk0 2 (by norm_num)
  let g := _root_.QuadraticMap.specialOrthogonalToOrthogonal
    (hyperbolicPlane ℚ) (hyperbolicTorus ℚ t)
  refine ⟨g, ?_, eventually_mem_integralOrthogonalSubgroup _ _ g⟩
  norm_num [g, LinearMap.toMatrix_apply, _root_.QuadraticMap.coe_specialOrthogonalToOrthogonal,
    hyperbolicTorus_apply, t, invOf_eq_inv]

end Rational
end

end QuadraticMap
end TauCeti
