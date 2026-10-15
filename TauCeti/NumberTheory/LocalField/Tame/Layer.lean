/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Tame.Quotient
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Quotient

/-!
# The finite tame layer attached to a finite Galois quotient

For an open normal subgroup `U` of the absolute Galois group of a perfect nonarchimedean
local field `K`, let `L` be the fixed field of `P_K U`, where `P_K` is wild inertia.
This is a finite Galois, tamely ramified extension. Its Galois group is canonically
`G_K / (P_K U)` and admits a generating pair whose second element has order prime to
the residue characteristic.

The exact fixing-subgroup equation identifies this arithmetic layer with the subgroup
used in the pro-`p` class-module extension. The generating pair permits the tame-frame
relation-module construction to be applied to this layer of any finite Galois quotient.
The local-field structures on `L` may be any structures compatible with `K`.
Its canonical embedding into the separable closure identifies the arithmetic fixing subgroup
with the same product `P_K U` in the algebraic-closure model.

The quotient comparison specializes `TauCeti.absoluteGaloisGroupQuotientEquiv`, and the pair
is the image of the frame supplied by `TauCeti.exists_tameFrame_quotient`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  proof of (7.4.1).
-/

public noncomputable section

open ValuativeRel IntermediateField

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The open normal subgroup `P_K U` associated with a finite Galois quotient. -/
def tameLayerSubgroup (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    OpenNormalSubgroup (Field.absoluteGaloisGroup K) where
  toSubgroup := wildInertiaSubgroup K ⊔ U.toSubgroup
  isOpen' := Subgroup.isOpen_mono le_sup_right U.isOpen
  isNormal' := inferInstance

/-- The subgroup defining the tame layer is the product of wild inertia and `U`. -/
@[simp]
theorem tameLayerSubgroup_toSubgroup
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    (tameLayerSubgroup K U).toSubgroup = wildInertiaSubgroup K ⊔ U.toSubgroup :=
  (rfl)

/-- The fixed field of `P_K U` inside the algebraic closure of `K`. Over a perfect local
field it is a finite tame Galois layer. -/
def tameLayer (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    IntermediateField K (AlgebraicClosure K) :=
  fixedField (tameLayerSubgroup K U).toSubgroup

/-- The tame layer is the fixed field of the product of wild inertia and `U`. -/
theorem tameLayer_def (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    tameLayer K U = fixedField (wildInertiaSubgroup K ⊔ U.toSubgroup) :=
  (rfl)

/-- Membership in the tame layer means being fixed by both wild inertia and `U`. -/
@[simp]
theorem mem_tameLayer_iff (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (x : AlgebraicClosure K) :
    x ∈ tameLayer K U ↔
      (∀ σ ∈ wildInertiaSubgroup K,
        DFunLike.coe (F := Gal(AlgebraicClosure K/K)) σ x = x) ∧
        (∀ σ ∈ U, DFunLike.coe (F := Gal(AlgebraicClosure K/K)) σ x = x) := by
  -- Specify the automorphism carrier because the absolute Galois group has no
  -- function coercion of its own.
  have h := Subgroup.fixedField_sup (K := K) (M := AlgebraicClosure K)
    (wildInertiaSubgroup K) U.toSubgroup
  exact (congrArg (x ∈ ·) h).to_iff.trans
    ((mem_fixedField_iff _ _).and (mem_fixedField_iff _ _))

/-- The automorphisms fixing the tame layer are exactly `P_K U`. -/
@[simp]
theorem fixingSubgroup_tameLayer (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    (tameLayer K U).fixingSubgroup = wildInertiaSubgroup K ⊔ U.toSubgroup := by
  exact fixingSubgroup_fixedField (tameLayerSubgroup K U).isClosed

variable [PerfectField K]

/-- The tame layer is finite over `K`, since `P_K U` is open. -/
instance finiteDimensional_tameLayer (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    FiniteDimensional K (tameLayer K U) := by
  apply (InfiniteGalois.isOpen_iff_finite _).mp
  rw [fixingSubgroup_tameLayer]
  exact (tameLayerSubgroup K U).isOpen

/-- The tame layer is Galois over `K`, since `P_K U` is normal. -/
instance isGalois_tameLayer (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    IsGalois K (tameLayer K U) := by
  apply (InfiniteGalois.normal_iff_isGalois _).mp
  rw [fixingSubgroup_tameLayer]
  exact (tameLayerSubgroup K U).isNormal'

/-- The canonical inclusion of the finite tame layer into the separable closure. -/
def tameLayerEmbedding (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    tameLayer K U →ₐ[K] SeparableClosure K :=
  inclusion (le_separableClosure K (AlgebraicClosure K) (tameLayer K U))

/-- The separable-closure inclusion preserves the original algebraic-closure coordinates. -/
@[simp]
theorem coe_tameLayerEmbedding (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (x : tameLayer K U) :
    (tameLayerEmbedding K U x : AlgebraicClosure K) = x :=
  (rfl)

/-- Restriction to the tame layer agrees in the algebraic and separable closure models. -/
theorem tameLayerEmbedding_restrictNormalHom
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (σ : Field.absoluteGaloisGroup K) :
    (tameLayerEmbedding K U).restrictNormalHom (absoluteGaloisGroupRestrictEquiv K σ) =
      AlgEquiv.restrictNormalHom (tameLayer K U) σ := by
  apply (tameLayerEmbedding K U).restrictNormalHom_eq_iff.mpr
  intro x
  apply Subtype.val_injective
  exact (coe_absoluteGaloisGroupRestrictEquiv_apply K σ (tameLayerEmbedding K U x)).trans
    (AlgEquiv.restrictNormal_commutes σ (tameLayer K U) x).symm

/-- The subgroup fixing the embedded tame layer pulls back to the product of wild inertia
and the prescribed open normal subgroup. -/
theorem galoisSubgroup_tameLayerEmbedding_comap
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    (galoisSubgroup K (tameLayer K U) (tameLayerEmbedding K U)).toSubgroup.comap
        (absoluteGaloisGroupRestrictEquiv K).toMulEquiv.toMonoidHom =
      wildInertiaSubgroup K ⊔ U.toSubgroup := by
  rw [galoisSubgroup_toSubgroup, ← AlgHom.ker_restrictNormalHom]
  ext σ
  simp only [Subgroup.mem_comap, MonoidHom.mem_ker]
  refine (congrArg (· = 1) (tameLayerEmbedding_restrictNormalHom K U σ)).to_iff.trans ?_
  -- Mathlib's kernel equation uses the automorphism-group presentation of the
  -- absolute Galois group, whose derived group instance is hidden by the wrapper.
  change σ ∈ (AlgEquiv.restrictNormalHom (tameLayer K U) :
    Gal(AlgebraicClosure K/K) →* Gal(tameLayer K U/K)).ker ↔ _
  rw [IntermediateField.restrictNormalHom_ker, fixingSubgroup_tameLayer]
  rfl

/-- The finite quotient by `P_K U` is the Galois group of the associated tame layer. -/
def quotientTameLayerEquiv (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    Field.absoluteGaloisGroup K ⧸ (tameLayerSubgroup K U).toSubgroup ≃ₜ*
      Gal(tameLayer K U/K) :=
  -- Specify both carriers: the fixing subgroup uses the automorphism group instances,
  -- while the source quotient uses the derived absolute Galois group instances.
  ((show Field.absoluteGaloisGroup K ≃ₜ* Gal(AlgebraicClosure K/K) from
      ContinuousMulEquiv.refl _).quotientCongr
    (tameLayerSubgroup K U).toSubgroup (tameLayer K U).fixingSubgroup
    (by
      change (tameLayerSubgroup K U).toSubgroup.map (MonoidHom.id _) = _
      rw [Subgroup.map_id]
      exact (fixingSubgroup_tameLayer K U).symm)).trans
      (absoluteGaloisGroupQuotientEquiv K (tameLayer K U))

/-- The quotient identification is restriction of automorphisms to the tame layer. -/
@[simp]
theorem quotientTameLayerEquiv_mk (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (σ : Field.absoluteGaloisGroup K) :
    quotientTameLayerEquiv K U (QuotientGroup.mk σ) =
      AlgEquiv.restrictNormalHom (tameLayer K U) σ := by
  rw [quotientTameLayerEquiv, ContinuousMulEquiv.trans_apply,
    ContinuousMulEquiv.quotientCongr_mk
      (show Field.absoluteGaloisGroup K ≃ₜ* Gal(AlgebraicClosure K/K) from
        ContinuousMulEquiv.refl _)]
  exact absoluteGaloisGroupQuotientEquiv_mk σ

/-- The inverse quotient identification sends a restricted automorphism back to its class. -/
@[simp]
theorem quotientTameLayerEquiv_symm_restrictNormalHom
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (σ : Field.absoluteGaloisGroup K) :
    (quotientTameLayerEquiv K U).symm (AlgEquiv.restrictNormalHom (tameLayer K U) σ) =
      QuotientGroup.mk σ := by
  rw [← quotientTameLayerEquiv_mk, ContinuousMulEquiv.symm_apply_apply]

/-- The layer fixed by `P_K U` is tamely ramified for any compatible local-field structures. -/
theorem isTamelyRamified_tameLayer (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    [ValuativeRel (tameLayer K U)] [TopologicalSpace (tameLayer K U)]
    [IsNonarchimedeanLocalField (tameLayer K U)] [ValuativeExtension K (tameLayer K U)] :
    IsTamelyRamified K (tameLayer K U) := by
  apply (le_maximalTameExtension_iff (tameLayer K U)).mp
  rw [← InfiniteGalois.fixedField_fixingSubgroup (maximalTameExtension K (AlgebraicClosure K)),
    IntermediateField.le_iff_le, fixingSubgroup_tameLayer,
    ← wildInertiaSubgroup_def]
  exact le_sup_left

/-- The Galois group of the tame layer has a generating pair with second element of order
prime to the residue characteristic. This is the frame for the integral relation module. -/
theorem exists_tameFrame_tameLayer (p : ℕ) [CharP 𝓀[K] p]
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    ∃ σ τ : Gal(tameLayer K U/K), Subgroup.closure {σ, τ} = ⊤ ∧ ¬ p ∣ orderOf τ := by
  obtain ⟨σ, τ, _, _, hframe⟩ := exists_tameFrame_quotient K p
  obtain ⟨hgen, hτ⟩ := hframe (tameLayerSubgroup K U) (by simp)
  let e := quotientTameLayerEquiv K U
  have he : e.toMulEquiv.toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr e.surjective
  refine ⟨e (QuotientGroup.mk σ), e (QuotientGroup.mk τ), ?_, ?_⟩
  · have h := congrArg (Subgroup.map e.toMulEquiv.toMonoidHom) hgen
    rw [MonoidHom.map_closure, Set.image_pair, Subgroup.map_top, he] at h
    exact h
  · exact hτ ∘ (e.toMulEquiv.orderOf_eq _ ▸ ·)

end TauCeti
