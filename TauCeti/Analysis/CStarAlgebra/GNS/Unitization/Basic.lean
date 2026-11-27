/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.RightRepresentation
public import TauCeti.Analysis.CStarAlgebra.GNS.Uniqueness
public import TauCeti.Analysis.CStarAlgebra.State.Unitization
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import TauCeti.Algebra.Algebra.Unitization
import TauCeti.Analysis.Normed.Operator.Dense

/-!
# Unitization of the GNS representation

For a positive functional `τ` on a possibly nonunital C⋆-algebra `A`, the classes of an
increasing approximate unit of `A` converge to the class of the unit in the GNS space of the
norm-preserving extension `τ.unitization`. The distance estimate gives this convergence using
Mathlib's `PositiveContinuousLinearMap.tendsto_nhds_opNorm`, which supplies the scalar limit
of `τ` on the approximate unit. Thus the classes from `A` are already dense there.

The resulting unitary `PositiveContinuousLinearMap.gnsEquivUnitization` identifies the two
GNS representations on `A`. Pulling the class of the unit back gives a cyclic vector for the
original representation, realizing `τ` even when `A` has no unit. For a tracial functional
this vector is also cyclic for the right action. The construction uses
`PositiveLinearMap.gnsEquiv`, the uniqueness theorem for cyclic realizations.

## References

* G. J. Murphy, *C⋆-Algebras and Operator Theory*, §3.3.
-/

public section

noncomputable section

open Filter Topology
open scoped ComplexOrder InnerProductSpace

namespace PositiveContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →P[ℂ] ℂ)

private theorem tendsto_unitization_toGNS {l : Filter A} (hl : l.IsIncreasingApproximateUnit) :
    Tendsto (fun e : A => τ.unitization.toGNS (e : Unitization ℂ A)) l
      (𝓝 τ.unitization.gnsVector) := by
  have hre : Tendsto (fun e : A => (τ e).re) l (𝓝 ‖(τ : A →L[ℂ] ℂ)‖) := by
    simpa only [Function.comp_def, Complex.ofReal_re] using
      (Complex.continuous_re.tendsto _).comp (τ.tendsto_nhds_opNorm hl)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (.of_forall fun _ => norm_nonneg _) ?_
    (by simpa using (hre.const_sub ‖(τ : A →L[ℂ] ℂ)‖).sqrt)
  filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he he₁
  rw [norm_sub_rev]
  apply Real.le_sqrt_of_sq_le
  simpa only [norm_unitization, unitization_apply_inr] using
    τ.unitization.norm_gnsVector_sub_toGNS_sq_le ((Unitization.inr_nonneg_iff ℂ).mpr he)
      (by simpa only [Unitization.norm_inr] using he₁)

private theorem denseRange_toGNS_inr_of_tendsto {l : Filter A} [l.NeBot]
    (f : Unitization ℂ A →ₚ[ℂ] ℂ)
    (hlim : Tendsto (fun e : A => f.toGNS (e : Unitization ℂ A)) l (𝓝 f.gnsVector)) :
    DenseRange (fun a : A => f.toGNS (a : Unitization ℂ A)) := by
  intro v
  refine f.denseRange_toGNS.induction_on v isClosed_closure fun x => ?_
  have h := ((f.gnsNonUnitalStarAlgHom x).continuous.tendsto _).comp hlim
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_gnsVector,
    ← PositiveLinearMap.toGNS_apply] at h
  refine mem_closure_of_tendsto h (.of_forall fun e => ?_)
  exact ⟨x.fst • e + x.snd * e, by
    simp only [Function.comp_apply, PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_toGNS,
      Unitization.mul_inr]⟩

/-- The canonical unitary identifying the GNS space of a positive functional with that of
its norm-preserving extension to the unitization. -/
def gnsEquivUnitization : τ.GNS ≃ₗᵢ[ℂ] τ.unitization.GNS :=
  τ.gnsEquiv
    (τ.unitization.gnsNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A))
    τ.unitization.gnsVector
    (by
      simpa using denseRange_toGNS_inr_of_tendsto τ.unitization.toPositiveLinearMap
        (τ.tendsto_unitization_toGNS (CStarAlgebra.increasingApproximateUnit A)))
    (by simp)

/-- The unitization unitary sends the class of `a` to the class of its inclusion. -/
@[simp]
theorem gnsEquivUnitization_apply_coe (a : A) :
    τ.gnsEquivUnitization (τ.toPreGNS a : τ.GNS) =
      (τ.unitization.toPreGNS (a : Unitization ℂ A) : τ.unitization.GNS) := by
  simp [gnsEquivUnitization]

/-- The unitization unitary is uniquely determined by sending the class of each element
to the class of its inclusion. -/
theorem gnsEquivUnitization_unique (U : τ.GNS ≃ₗᵢ[ℂ] τ.unitization.GNS)
    (hU : ∀ a : A, U (τ.toGNS a) = τ.unitization.toGNS (a : Unitization ℂ A)) :
    U = τ.gnsEquivUnitization := by
  unfold gnsEquivUnitization
  apply PositiveLinearMap.gnsEquiv_unique
  intro a
  simpa using hU a

/-- The unitization unitary intertwines the original action and the restriction of the
unital action. -/
@[simp]
theorem gnsEquivUnitization_intertwines (a : A) (v : τ.GNS) :
    τ.gnsEquivUnitization (τ.gnsNonUnitalStarAlgHom a v) =
      τ.unitization.gnsNonUnitalStarAlgHom a (τ.gnsEquivUnitization v) := by
  simp [gnsEquivUnitization]

/-- The inverse unitization unitary sends the class of the inclusion of `a` to the class of `a`. -/
@[simp]
theorem gnsEquivUnitization_symm_apply_coe (a : A) :
    τ.gnsEquivUnitization.symm
        (τ.unitization.toPreGNS (a : Unitization ℂ A) : τ.unitization.GNS) =
      (τ.toPreGNS a : τ.GNS) := by
  apply τ.gnsEquivUnitization.injective
  simp

/-- The inverse unitization unitary intertwines the restricted unital action with the
original action. -/
@[simp]
theorem gnsEquivUnitization_symm_intertwines (a : A) (v : τ.unitization.GNS) :
    τ.gnsEquivUnitization.symm (τ.unitization.gnsNonUnitalStarAlgHom a v) =
      τ.gnsNonUnitalStarAlgHom a (τ.gnsEquivUnitization.symm v) := by
  apply τ.gnsEquivUnitization.injective
  simp

/-- Conjugating an original GNS operator by the unitization unitary gives the
unitization GNS operator of the included element. -/
@[simp]
theorem gnsEquivUnitization_conjStarAlgEquiv (a : A) :
    τ.gnsEquivUnitization.conjStarAlgEquiv (τ.gnsNonUnitalStarAlgHom a) =
      τ.unitization.gnsNonUnitalStarAlgHom (a : Unitization ℂ A) := by
  ext v
  simp

/-- Conjugating the unitization GNS operator of an included element by the inverse
unitary recovers the original GNS operator. -/
@[simp]
theorem gnsEquivUnitization_symm_conjStarAlgEquiv (a : A) :
    τ.gnsEquivUnitization.symm.conjStarAlgEquiv
        (τ.unitization.gnsNonUnitalStarAlgHom (a : Unitization ℂ A)) =
      τ.gnsNonUnitalStarAlgHom a := by
  ext v
  simp

/-- The canonical cyclic vector of a possibly nonunital GNS representation, obtained by
transporting the class of the adjoined unit. -/
def gnsNonUnitalVector : τ.GNS :=
  τ.gnsEquivUnitization.symm τ.unitization.gnsVector

/-- The inverse unitization unitary sends the class of the adjoined unit to the canonical vector. -/
@[simp]
theorem gnsEquivUnitization_symm_gnsVector :
    τ.gnsEquivUnitization.symm τ.unitization.gnsVector = τ.gnsNonUnitalVector :=
  (rfl)

/-- The unitization unitary sends the canonical vector to the class of the adjoined unit. -/
@[simp]
theorem gnsEquivUnitization_gnsNonUnitalVector :
    τ.gnsEquivUnitization τ.gnsNonUnitalVector = τ.unitization.gnsVector := by
  rw [← τ.gnsEquivUnitization_symm_gnsVector, LinearIsometryEquiv.apply_symm_apply]

/-- The squared norm of the canonical vector is the norm of the functional. In particular,
the vector of a state has norm one. -/
theorem norm_gnsNonUnitalVector_sq : ‖τ.gnsNonUnitalVector‖ ^ 2 = ‖(τ : A →L[ℂ] ℂ)‖ := by
  rw [← τ.gnsEquivUnitization_symm_gnsVector, LinearIsometryEquiv.norm_map]
  simpa only [coe_toPositiveLinearMap, unitization_apply_one, ← Complex.ofReal_pow,
    Complex.ofReal_re] using
    congrArg Complex.re τ.unitization.norm_gnsVector_sq

/-- Acting on the canonical vector produces the GNS class of the acting element. -/
@[simp]
theorem gnsNonUnitalStarAlgHom_apply_gnsNonUnitalVector (a : A) :
    τ.gnsNonUnitalStarAlgHom a τ.gnsNonUnitalVector = (τ.toPreGNS a : τ.GNS) := by
  apply τ.gnsEquivUnitization.injective
  simp

/-- The GNS classes of an eventually norm-bounded left approximate identity converge in norm
to the canonical vector. -/
theorem tendsto_toGNS_gnsNonUnitalVector {l : Filter A} {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a : A, Tendsto (fun e => e * a) l (𝓝 a)) :
    Tendsto τ.toGNS l (𝓝 τ.gnsNonUnitalVector) := by
  have hbound : ∀ᶠ e in l, ‖τ.gnsNonUnitalStarAlgHom e‖ ≤ C :=
    hC.mono fun e he => (NonUnitalStarAlgHom.norm_apply_le τ.gnsNonUnitalStarAlgHom e).trans he
  have hstrong := ContinuousLinearMap.tendsto_apply_of_dense
    (g := ContinuousLinearMap.id ℂ τ.GNS) τ.denseRange_toGNS hbound
    (by
      rintro _ ⟨a, rfl⟩
      simpa only [Function.comp_def, PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_toGNS,
        ContinuousLinearMap.id_apply] using (τ.toGNS.continuous.tendsto a).comp (hl a))
    τ.gnsNonUnitalVector
  simpa only [gnsNonUnitalStarAlgHom_apply_gnsNonUnitalVector, ContinuousLinearMap.id_apply,
    ← PositiveLinearMap.toGNS_apply] using hstrong

/-- Pairing the canonical vector with the class of `a` recovers the original functional. -/
@[simp]
theorem inner_gnsNonUnitalVector_coe (a : A) :
    ⟪τ.gnsNonUnitalVector, (τ.toPreGNS a : τ.GNS)⟫_ℂ = τ a := by
  rw [← τ.gnsEquivUnitization.inner_map_map]
  simp

/-- The canonical vector is cyclic for the action of the original algebra. -/
theorem denseRange_gnsNonUnitalStarAlgHom_gnsNonUnitalVector :
    DenseRange (fun a : A => τ.gnsNonUnitalStarAlgHom a τ.gnsNonUnitalVector) := by
  simpa only [gnsNonUnitalStarAlgHom_apply_gnsNonUnitalVector, ← PositiveLinearMap.toGNS_apply]
    using τ.denseRange_toGNS

/-- For a tracial functional, the right action on the canonical vector also gives algebra
classes. -/
@[simp]
theorem gnsRightNonUnitalStarAlgHom_apply_gnsNonUnitalVector
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) (b : Aᵐᵒᵖ) :
    τ.gnsRightNonUnitalStarAlgHom hτ b τ.gnsNonUnitalVector = (τ.toPreGNS b.unop : τ.GNS) := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  have h := ((τ.gnsRightNonUnitalStarAlgHom hτ b).continuous.tendsto _).comp
    (τ.tendsto_toGNS_gnsNonUnitalVector hl.eventually_norm hl.tendsto_mul_right)
  refine tendsto_nhds_unique h ?_
  rw [← PositiveLinearMap.toGNS_apply]
  refine ((τ.toGNS.continuous.tendsto _).comp (hl.tendsto_mul_right b.unop)).congr fun e => ?_
  simpa only [Function.comp_apply, MulOpposite.op_unop] using
    (τ.gnsRightNonUnitalStarAlgHom_apply_toGNS hτ b.unop e).symm

/-- The canonical vector of a tracial functional is cyclic for the opposite algebra. -/
theorem denseRange_gnsRightNonUnitalStarAlgHom_gnsNonUnitalVector
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) :
    DenseRange (fun b : Aᵐᵒᵖ => τ.gnsRightNonUnitalStarAlgHom hτ b τ.gnsNonUnitalVector) := by
  simpa only [gnsRightNonUnitalStarAlgHom_apply_gnsNonUnitalVector,
    ← PositiveLinearMap.toGNS_apply, Function.comp_def] using
      τ.denseRange_toGNS.comp MulOpposite.unop_surjective.denseRange (by fun_prop)

/-- On a unital algebra the canonical vector is the class of its own unit. -/
@[simp]
theorem gnsNonUnitalVector_eq_gnsVector {B : Type*} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] (σ : B →P[ℂ] ℂ) : σ.gnsNonUnitalVector = σ.gnsVector := by
  have hl := Filter.IsIncreasingApproximateUnit.pure_one B
  exact tendsto_nhds_unique
    (σ.tendsto_toGNS_gnsNonUnitalVector hl.eventually_norm hl.tendsto_mul_right)
    (by simpa [PositiveLinearMap.gnsVector_eq_toGNS_one] using tendsto_pure_nhds σ.toGNS 1)

end PositiveContinuousLinearMap
