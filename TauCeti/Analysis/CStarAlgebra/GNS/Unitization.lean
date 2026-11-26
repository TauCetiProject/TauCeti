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

private theorem norm_unitization_gnsVector_sq :
    ‖τ.unitization.gnsVector‖ ^ 2 = ‖(τ : A →L[ℂ] ℂ)‖ := by
  have h : ofClass (R := ℂ) τ.unitization.toPositiveLinearMap = τ.unitization :=
    PositiveContinuousLinearMap.ext fun _ => by simp
  rw [PositiveLinearMap.norm_gnsVector_sq_eq_opNorm, h, norm_unitization]

/-- For a positive contraction, the squared distance from its unitization GNS class to the
class of the adjoined unit is bounded by `‖τ‖ - (τ e).re`. -/
theorem norm_unitization_gnsVector_sub_toGNS_sq_le {e : A} (he : 0 ≤ e) (he₁ : ‖e‖ ≤ 1) :
    ‖τ.unitization.gnsVector - τ.unitization.toGNS (e : Unitization ℂ A)‖ ^ 2 ≤
      ‖(τ : A →L[ℂ] ℂ)‖ - (τ e).re := by
  have hs : ‖τ.unitization.toGNS (e : Unitization ℂ A)‖ ^ 2 = (τ (e * e)).re := by
    simpa [← Complex.ofReal_pow, ← Unitization.inr_star, ← Unitization.inr_mul, he.star_eq] using
      congrArg Complex.re (τ.unitization.norm_toGNS_sq (e : Unitization ℂ A))
  have hee : (τ (e * e)).re ≤ (τ e).re :=
    (Complex.le_def.mp (τ.mono (CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one he he₁))).1
  calc
    ‖τ.unitization.gnsVector - τ.unitization.toGNS (e : Unitization ℂ A)‖ ^ 2 =
        ‖(τ : A →L[ℂ] ℂ)‖ - 2 * (τ e).re + (τ (e * e)).re := by
      rw [@norm_sub_sq ℂ, τ.norm_unitization_gnsVector_sq, hs]
      simp
    _ ≤ _ := by linarith

private theorem tendsto_zero_of_eventually_le_norm_unitization_gnsVector_sub_toGNS {l : Filter A}
    (hl : l.IsIncreasingApproximateUnit) {g : A → ℝ} (hg₀ : ∀ᶠ e in l, 0 ≤ g e)
    (hg : ∀ᶠ e in l, g e ≤ ‖τ.unitization.gnsVector - τ.unitization.toGNS e‖) :
    Tendsto g l (𝓝 0) := by
  have hre : Tendsto (fun e : A => (τ e).re) l (𝓝 ‖(τ : A →L[ℂ] ℂ)‖) := by
    simpa [Function.comp_def] using
      (Complex.continuous_re.tendsto _).comp (τ.tendsto_nhds_opNorm hl)
  refine squeeze_zero' hg₀ ?_
    (by simpa using (hre.const_sub ‖(τ : A →L[ℂ] ℂ)‖).sqrt)
  filter_upwards [hg, hl.eventually_nonneg, hl.eventually_norm] with e h he he₁
  exact h.trans (Real.le_sqrt_of_sq_le (τ.norm_unitization_gnsVector_sub_toGNS_sq_le he he₁))

/-- The canonical unitary identifying the GNS space of a positive functional with that of
its norm-preserving extension to the unitization. -/
def gnsEquivUnitization : τ.GNS ≃ₗᵢ[ℂ] τ.unitization.GNS := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  have hlim : Tendsto (fun e : A => τ.unitization.toGNS e) (CStarAlgebra.approximateUnit A)
      (𝓝 τ.unitization.gnsVector) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact τ.tendsto_zero_of_eventually_le_norm_unitization_gnsVector_sub_toGNS hl
      (.of_forall fun _ => norm_nonneg _) (.of_forall fun _ => (norm_sub_rev _ _).le)
  have hcyc : DenseRange (fun a : A => τ.unitization.toGNS a) := by
    intro v
    refine τ.unitization.denseRange_toGNS.induction_on v isClosed_closure fun x => ?_
    have h := ((τ.unitization.gnsNonUnitalStarAlgHom x).continuous.tendsto _).comp hlim
    rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_gnsVector,
      ← PositiveLinearMap.toGNS_apply] at h
    refine mem_closure_of_tendsto h (.of_forall fun e => ?_)
    exact ⟨x.fst • e + x.snd * e, by
      simp only [Function.comp_apply, PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_toGNS,
        Unitization.mul_inr]⟩
  exact τ.gnsEquiv
    (τ.unitization.gnsNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A))
    τ.unitization.gnsVector (by simpa using hcyc) (by simp)

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
  exact τ.norm_unitization_gnsVector_sq

/-- The classes of any increasing approximate unit converge in norm to the canonical vector. -/
theorem tendsto_toGNS_gnsNonUnitalVector {l : Filter A} (hl : l.IsIncreasingApproximateUnit) :
    Tendsto τ.toGNS l (𝓝 τ.gnsNonUnitalVector) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine τ.tendsto_zero_of_eventually_le_norm_unitization_gnsVector_sub_toGNS hl
    (.of_forall fun _ => norm_nonneg _) (.of_forall fun e => ?_)
  rw [← τ.gnsEquivUnitization.norm_map, map_sub, norm_sub_rev]
  simp

/-- Acting on the canonical vector produces the GNS class of the acting element. -/
@[simp]
theorem gnsNonUnitalStarAlgHom_apply_gnsNonUnitalVector (a : A) :
    τ.gnsNonUnitalStarAlgHom a τ.gnsNonUnitalVector = (τ.toPreGNS a : τ.GNS) := by
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
    (τ.tendsto_toGNS_gnsNonUnitalVector hl)
  refine tendsto_nhds_unique h ?_
  simpa [Function.comp_def] using
    (τ.toGNS.continuous.tendsto _).comp (hl.tendsto_mul_right b.unop)

/-- The canonical vector of a tracial functional is cyclic for the opposite algebra. -/
theorem denseRange_gnsRightNonUnitalStarAlgHom_gnsNonUnitalVector
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) :
    DenseRange (fun b : Aᵐᵒᵖ => τ.gnsRightNonUnitalStarAlgHom hτ b τ.gnsNonUnitalVector) := by
  simpa only [gnsRightNonUnitalStarAlgHom_apply_gnsNonUnitalVector,
    ← PositiveLinearMap.toGNS_apply, Function.comp_def] using
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
