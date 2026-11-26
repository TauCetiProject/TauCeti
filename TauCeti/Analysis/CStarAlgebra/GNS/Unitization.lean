/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.Uniqueness
public import TauCeti.Analysis.CStarAlgebra.GNS.VonNeumannAlgebra
public import TauCeti.Analysis.CStarAlgebra.State.Unitization
public import TauCeti.Analysis.VonNeumannAlgebra.Cyclic
import TauCeti.Algebra.Algebra.Unitization

/-!
# Unitization of the GNS representation

For a positive functional `τ` on a possibly nonunital C⋆-algebra `A`, the classes of an
increasing approximate unit of `A` converge to the class of the unit in the GNS space of the
norm-preserving extension `τ.unitization`. Thus the classes from `A` are already dense there.

The resulting unitary `PositiveContinuousLinearMap.gnsEquivUnitization` identifies the two
GNS representations on `A` and their generated von Neumann algebras. Pulling the class of the
unit back gives a cyclic vector for the original representation, realizing `τ` even when
`A` has no unit. For a tracial functional this vector is also cyclic for the right action
and separating for the GNS von Neumann algebra. The construction uses
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

/-- The classes of an increasing approximate unit converge to the cyclic vector of the
norm-preserving extension. -/
theorem tendsto_unitization_toGNS_inr {l : Filter A} (hl : l.IsIncreasingApproximateUnit) :
    Tendsto (fun e : A => τ.unitization.toGNS e) l (𝓝 τ.unitization.gnsVector) := by
  have hre : Tendsto (fun e : A => (τ e).re) l (𝓝 ‖(τ : A →L[ℂ] ℂ)‖) := by
    simpa [Function.comp_def] using
      (Complex.continuous_re.tendsto _).comp (τ.tendsto_nhds_opNorm hl)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (.of_forall fun _ => norm_nonneg _) ?_
    (by simpa using (hre.const_sub ‖(τ : A →L[ℂ] ℂ)‖).sqrt)
  filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he he₁
  apply Real.le_sqrt_of_sq_le
  have hs := congrArg Complex.re (τ.unitization.norm_toGNS_sq (e : Unitization ℂ A))
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, coe_toPositiveLinearMap,
    ← Unitization.inr_star, ← Unitization.inr_mul, unitization_apply_inr, he.star_eq] at hs
  have hee : (τ (e * e)).re ≤ (τ e).re :=
    (Complex.le_def.mp (τ.mono (CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one he he₁))).1
  have hΩ := congrArg Complex.re τ.unitization.norm_gnsVector_sq
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, coe_toPositiveLinearMap,
    unitization_apply_one] at hΩ
  rw [norm_sub_rev, @norm_sub_sq ℂ, RCLike.re_to_complex, hs, hΩ]
  simp only [PositiveLinearMap.toGNS_apply, PositiveLinearMap.inner_gnsVector_coe,
    coe_toPositiveLinearMap, unitization_apply_inr]
  linarith

/-- The classes from the original algebra are dense in the GNS space of its unitization
extension. -/
theorem denseRange_unitization_toGNS_inr :
    DenseRange (fun a : A => τ.unitization.toGNS a) := by
  intro v
  refine τ.unitization.denseRange_toGNS.induction_on v isClosed_closure fun x => ?_
  have h := ((τ.unitization.gnsNonUnitalStarAlgHom x).continuous.tendsto _).comp
    (τ.tendsto_unitization_toGNS_inr (CStarAlgebra.increasingApproximateUnit A))
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_gnsVector,
    ← PositiveLinearMap.toGNS_apply] at h
  refine mem_closure_of_tendsto h (.of_forall fun e => ?_)
  exact ⟨x.fst • e + x.snd * e, by
    simp only [Function.comp_apply, PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_toGNS,
      Unitization.mul_inr]⟩

/-- The canonical unitary identifying the GNS space of a positive functional with that of
its norm-preserving extension to the unitization. -/
def gnsEquivUnitization : τ.GNS ≃ₗᵢ[ℂ] τ.unitization.GNS :=
  τ.gnsEquiv (τ.unitization.gnsNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A))
    τ.unitization.gnsVector (by simpa using τ.denseRange_unitization_toGNS_inr) (by simp)

/-- The unitization unitary sends the class of `a` to the class of its inclusion. -/
@[simp]
theorem gnsEquivUnitization_apply_coe (a : A) :
    τ.gnsEquivUnitization (τ.toPreGNS a : τ.GNS) =
      (τ.unitization.toPreGNS (a : Unitization ℂ A) : τ.unitization.GNS) := by
  simp [gnsEquivUnitization]

/-- The unitization unitary intertwines the original action and the restriction of the
unital action. -/
@[simp]
theorem gnsEquivUnitization_intertwines (a : A) (v : τ.GNS) :
    τ.gnsEquivUnitization (τ.gnsNonUnitalStarAlgHom a v) =
      τ.unitization.gnsNonUnitalStarAlgHom a (τ.gnsEquivUnitization v) := by
  simp [gnsEquivUnitization]

/-- Unitary transport identifies the von Neumann algebras generated before and after
unitization. -/
@[simp]
theorem mapLinearIsometryEquiv_gnsEquivUnitization :
    VonNeumannAlgebra.mapLinearIsometryEquiv τ.gnsEquivUnitization τ.gnsVonNeumannAlgebra =
      τ.unitization.gnsVonNeumannAlgebra := by
  have hπ (a : A) : τ.gnsEquivUnitization.conjStarAlgEquiv (τ.gnsNonUnitalStarAlgHom a) =
      τ.unitization.gnsNonUnitalStarAlgHom a := by
    ext v
    simp
  rw [PositiveLinearMap.gnsVonNeumannAlgebra_def τ.toPositiveLinearMap,
    VonNeumannAlgebra.mapLinearIsometryEquiv_adjoin, ← Set.range_comp]
  simp_rw [Function.comp_def, hπ]
  let M := VonNeumannAlgebra.adjoin (Set.range fun a : A => τ.unitization.gnsNonUnitalStarAlgHom a)
  refine le_antisymm (VonNeumannAlgebra.adjoin_le_iff.mpr ?_) ?_
  · rintro _ ⟨a, rfl⟩
    exact τ.unitization.gnsNonUnitalStarAlgHom_mem_gnsVonNeumannAlgebra a
  · rw [PositiveLinearMap.gnsVonNeumannAlgebra_eq_adjoin_range_gnsStarAlgHom,
      VonNeumannAlgebra.adjoin_le_iff, Set.range_subset_iff]
    intro x
    rw [← Unitization.inl_fst_add_inr_snd_eq x, map_add, ← Unitization.algebraMap_eq_inl,
      AlgHomClass.commutes]
    exact add_mem (M.toStarSubalgebra.algebraMap_mem _) (VonNeumannAlgebra.subset_adjoin _ ⟨_, rfl⟩)

/-- The canonical cyclic vector of a possibly nonunital GNS representation, obtained by
transporting the class of the adjoined unit. -/
def gnsNonUnitalVector : τ.GNS :=
  τ.gnsEquivUnitization.symm τ.unitization.gnsVector

/-- The unitization unitary sends the canonical vector to the class of the adjoined unit. -/
@[simp]
theorem gnsEquivUnitization_gnsNonUnitalVector :
    τ.gnsEquivUnitization τ.gnsNonUnitalVector = τ.unitization.gnsVector := by
  simp [gnsNonUnitalVector]

/-- The squared norm of the canonical vector is the norm of the functional. In particular,
the vector of a state has norm one. -/
theorem norm_gnsNonUnitalVector_sq : ‖τ.gnsNonUnitalVector‖ ^ 2 = ‖(τ : A →L[ℂ] ℂ)‖ := by
  simpa [gnsNonUnitalVector, ← Complex.ofReal_pow] using
    congrArg Complex.re τ.unitization.norm_gnsVector_sq

/-- The classes of any increasing approximate unit converge in norm to the canonical vector. -/
theorem tendsto_toGNS_gnsNonUnitalVector {l : Filter A} (hl : l.IsIncreasingApproximateUnit) :
    Tendsto τ.toGNS l (𝓝 τ.gnsNonUnitalVector) := by
  rw [τ.gnsEquivUnitization.toHomeomorph.isEmbedding.tendsto_nhds_iff]
  simpa [Function.comp_def] using τ.tendsto_unitization_toGNS_inr hl

/-- Acting on the canonical vector produces the GNS class of the acting element. -/
@[simp]
theorem gnsNonUnitalStarAlgHom_apply_gnsNonUnitalVector (a : A) :
    τ.gnsNonUnitalStarAlgHom a τ.gnsNonUnitalVector = τ.toGNS a := by
  apply τ.gnsEquivUnitization.injective
  simp

/-- Pairing the canonical vector with the class of `a` recovers the original functional. -/
@[simp]
theorem inner_gnsNonUnitalVector_coe (a : A) :
    ⟪τ.gnsNonUnitalVector, (τ.toPreGNS a : τ.GNS)⟫_ℂ = τ a := by
  rw [← τ.gnsEquivUnitization.inner_map_map]
  simp

/-- The canonical vector is cyclic for the action of the original algebra. -/
theorem denseRange_gnsNonUnitalStarAlgHom_gnsNonUnitalVector :
    DenseRange (fun a : A => τ.gnsNonUnitalStarAlgHom a τ.gnsNonUnitalVector) := by
  simpa only [gnsNonUnitalStarAlgHom_apply_gnsNonUnitalVector] using τ.denseRange_toGNS

/-- For a tracial functional, the right action on the canonical vector also gives algebra
classes. -/
@[simp]
theorem gnsRightNonUnitalStarAlgHom_apply_gnsNonUnitalVector
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) (b : Aᵐᵒᵖ) :
    τ.gnsRightNonUnitalStarAlgHom hτ b τ.gnsNonUnitalVector = τ.toGNS b.unop := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  have h := ((τ.gnsRightNonUnitalStarAlgHom hτ b).continuous.tendsto _).comp
    (τ.tendsto_toGNS_gnsNonUnitalVector hl)
  refine tendsto_nhds_unique h ?_
  simpa [Function.comp_def] using
    (τ.toGNS.continuous.tendsto _).comp (hl.tendsto_mul_right b.unop)

/-- The canonical vector of a tracial functional is cyclic for the opposite algebra. -/
theorem denseRange_gnsRightNonUnitalStarAlgHom_gnsNonUnitalVector
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) :
    DenseRange (fun b : Aᵐᵒᵖ => τ.gnsRightNonUnitalStarAlgHom hτ b τ.gnsNonUnitalVector) := by
  simpa only [gnsRightNonUnitalStarAlgHom_apply_gnsNonUnitalVector, Function.comp_def] using
    τ.denseRange_toGNS.comp MulOpposite.unop_surjective.denseRange (by fun_prop)

/-- The canonical vector of a tracial positive functional is separating for its generated
von Neumann algebra. -/
theorem isSeparating_gnsNonUnitalVector (hτ : ∀ a b, τ (a * b) = τ (b * a)) :
    τ.gnsVonNeumannAlgebra.IsSeparating τ.gnsNonUnitalVector := by
  rw [VonNeumannAlgebra.isSeparating_iff_isCyclic_commutant, VonNeumannAlgebra.isCyclic_iff]
  refine (τ.denseRange_gnsRightNonUnitalStarAlgHom_gnsNonUnitalVector hτ).mono ?_
  rintro _ ⟨b, rfl⟩
  exact ⟨_, τ.gnsRightNonUnitalStarAlgHom_mem_commutant hτ b, rfl⟩

/-- On a unital algebra the canonical vector is the class of its own unit. -/
@[simp]
theorem gnsNonUnitalVector_eq_gnsVector {B : Type*} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] (σ : B →P[ℂ] ℂ) : σ.gnsNonUnitalVector = σ.gnsVector := by
  exact tendsto_nhds_unique (σ.tendsto_toGNS_gnsNonUnitalVector (.pure_one B))
    (by simpa [PositiveLinearMap.gnsVector_eq_toGNS_one] using tendsto_pure_nhds σ.toGNS 1)

end PositiveContinuousLinearMap
