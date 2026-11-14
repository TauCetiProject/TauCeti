/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.LinearDisjoint
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.TensorProduct
public import TauCeti.FieldTheory.Separable.Regular
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import TauCeti.FieldTheory.AlgebraicClosure
import TauCeti.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.FieldTheory.RatFunc.Transcendental
import TauCeti.RingTheory.TensorProduct.IsDomain
import TauCeti.RingTheory.TensorProduct.Reduced

/-!
# Constant field extensions of regular fields

Let `F / k` be a field extension that is geometrically reduced and has exact constants, for
instance one with a separating element and exact constants. Then `F` is a regular extension of `k`
(`TauCeti.isDomain_tensorProduct_of_isGeometricallyReduced`), so `F ⊗[k] k'` is a domain for every
algebraic extension `k' / k`, separable or not. Hence multiplication `F ⊗[k] k' → F · k'` is an
isomorphism onto the constant field extension, discharging the domain hypothesis of
`TauCeti.productMap_bijective_of_constantCompositum_eq_top`. For a function field `F`, this says
that the function field of the curve after an algebraic extension of the constants is
`F ⊗[k] k'`.

For arbitrary extensions `k' / k`, linear disjointness of `F` and `k'` is equivalent to injectivity
of `F ⊗[k] k' → F'`, making `F · k'` a fraction field of `F ⊗[k] k'`, descending exact constants,
ascending exact constants and geometric reducedness, and following from a shared parameter.

## Main results

* `TauCeti.productMap_bijective_of_isGeometricallyReduced`: for `F` geometrically reduced with
  exact constants, multiplication `F ⊗[k] k' → F · k'` is an isomorphism for every algebraic
  extension `k' / k`.
* `TauCeti.productMap_bijective_of_separating`: the same for `F` with a separating element and
  exact constants.
* `TauCeti.isFractionRing_tensorProduct_of_linearDisjoint` and
  `TauCeti.linearDisjoint_of_transcendental_of_isDomain`: arbitrary constant field extensions.

## References

* S. Lang, *Introduction to Algebraic Geometry*, Interscience, 1958, Chapter III, Section 1.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
-/

public section

open scoped TensorProduct IntermediateField IntermediateField.algebraAdjoinAdjoin

namespace TauCeti

section Algebraic

variable {k F k' F' : Type*} [Field k] [Field F] [Algebra k F] [Field k'] [Field F'] [Algebra k k']
  [Algebra k F'] [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra.IsAlgebraic k k']

/-- **A constant field extension of a regular field is a tensor product.** If `F` is geometrically
reduced with exact constants, then multiplication `F ⊗[k] k' → F · k'` is bijective for every
algebraic extension `k' / k`, separable or not. -/
theorem productMap_bijective_of_isGeometricallyReduced (hex : IsIntegrallyClosedIn k F)
    [Algebra.IsGeometricallyReduced k F] (h : constantCompositum F k' F' = ⊤) :
    Function.Bijective (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F')) :=
  have := isDomain_tensorProduct_of_isGeometricallyReduced hex k'
  productMap_bijective_of_constantCompositum_eq_top h

/-- **A constant field extension of a separably generated field is a tensor product.** If `F` has
a separating element and exact constants, then multiplication `F ⊗[k] k' → F · k'` is bijective for
every algebraic extension `k' / k`, separable or not. -/
theorem productMap_bijective_of_separating (hex : IsIntegrallyClosedIn k F) {x : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] (h : constantCompositum F k' F' = ⊤) :
    Function.Bijective (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F')) :=
  have := isGeometricallyReduced_of_separating hx
  productMap_bijective_of_isGeometricallyReduced hex h

end Algebraic

section LinearDisjoint

variable {k F k' F' : Type*} [Field k] [Field F] [Algebra k F] [Field k'] [Field F'] [Algebra k k']
  [Algebra k F'] [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- Multiplication `F ⊗[k] k' → F'` is injective iff `k'` and `F` are linearly disjoint over `k`. -/
theorem productMap_injective_iff_linearDisjoint :
    Function.Injective (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F')) ↔
      (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F := by
  let fF := IsScalarTower.toAlgHom k F F'
  let fk' := IsScalarTower.toAlgHom k k' F'
  rw [IntermediateField.linearDisjoint_iff, AlgHom.fieldRange_toSubalgebra,
    Subalgebra.linearDisjoint_comm, Subalgebra.linearDisjoint_iff_injective]
  let e := Algebra.TensorProduct.congr (AlgEquiv.ofInjective fF fF.injective)
    (AlgEquiv.ofInjective fk' fk'.injective)
  have h : Algebra.TensorProduct.productMap fF fk' =
      (fF.range.mulMap fk'.range).comp e.toAlgHom := by ext x <;> rfl
  rw [h, AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, Function.Injective.of_comp_iff' _ e.bijective]

/-- **A linearly disjoint compositum is the fraction field of the tensor product.** -/
theorem isFractionRing_tensorProduct_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) :
    letI := (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F')).toRingHom.toAlgebra
    IsFractionRing (F ⊗[k] k') F' := by
  let π := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
    (IsScalarTower.toAlgHom k k' F')
  let _ := π.toRingHom.toAlgebra
  have hπ : Function.Injective (algebraMap (F ⊗[k] k') F') :=
    productMap_injective_iff_linearDisjoint.mpr H
  have : IsDomain (F ⊗[k] k') := hπ.isDomain (algebraMap (F ⊗[k] k') F')
  let ψ : FractionRing (F ⊗[k] k') →+* F' := IsFractionRing.lift hπ
  have hcomp : ψ.comp (algebraMap (F ⊗[k] k') (FractionRing (F ⊗[k] k'))) =
      algebraMap (F ⊗[k] k') F' := RingHom.ext (IsFractionRing.lift_algebraMap hπ)
  have hleft : (algebraMap (F ⊗[k] k') F') ∘
      (Algebra.TensorProduct.includeLeft : F →ₐ[k] F ⊗[k] k') = algebraMap F F' := by
    funext x; simp [π, RingHom.algebraMap_toAlgebra]
  have hright : (algebraMap (F ⊗[k] k') F') ∘
      (Algebra.TensorProduct.includeRight : k' →ₐ[k] F ⊗[k] k') = algebraMap k' F' := by
    funext x; simp [π, RingHom.algebraMap_toAlgebra]
  have hrange : (algebraMap (F ⊗[k] k') F').range =
      Subring.closure (Set.range (algebraMap F F') ∪ Set.range (algebraMap k' F')) := by
    rw [RingHom.range_eq_map, ← Algebra.TensorProduct.closure_range_union_range_eq_top k F k',
      RingHom.map_closure, Set.image_union, ← Set.range_comp, ← Set.range_comp, hleft, hright]
  have htop : ψ.fieldRange = ⊤ := by
    rw [IsFractionRing.ringHom_fieldRange_eq_of_comp_eq_of_range_eq hcomp hrange,
      ← IntermediateField.adjoin_toSubfield, ← constantCompositum_def, h,
      IntermediateField.top_toSubfield]
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors (F ⊗[k] k'))
    (AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective ψ
      ⟨ψ.injective, RingHom.fieldRange_eq_top_iff.mp htop⟩) (IsFractionRing.lift_algebraMap hπ))

/-- **Exact constants descend along any linearly disjoint extension.** -/
theorem isIntegrallyClosedIn_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hex' : IsIntegrallyClosedIn k' F') : IsIntegrallyClosedIn k F := by
  refine isIntegrallyClosedIn_iff_forall_isAlgebraic.mpr fun x hx ↦ ?_
  obtain ⟨c, hc⟩ := isIntegrallyClosedIn_iff_forall_isAlgebraic.mp hex' _
    ((hx.algHom (IsScalarTower.toAlgHom k F F')).tower_top k')
  have hmem : algebraMap F F' x ∈
      (IsScalarTower.toAlgHom k k' F').fieldRange ⊓ (IsScalarTower.toAlgHom k F F').fieldRange :=
    ⟨⟨c, hc⟩, ⟨x, rfl⟩⟩
  rw [(IntermediateField.linearDisjoint_iff'.mpr H).inf_eq_bot, IntermediateField.mem_bot] at hmem
  obtain ⟨a, ha⟩ := hmem
  exact ⟨a, (algebraMap F F').injective (by rwa [← IsScalarTower.algebraMap_apply k F F'])⟩

omit [Field F'] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] in
private noncomputable def tensorProductRightEquiv (F : Type*) [Field F] [Algebra k F]
    (Ω : Type*) [CommRing Ω] [Algebra k Ω] [Algebra k' Ω] [IsScalarTower k k' Ω] :
    letI : Algebra k' (F ⊗[k] k') := Algebra.TensorProduct.rightAlgebra
    ((F ⊗[k] k') ⊗[k'] Ω) ≃+* F ⊗[k] Ω :=
  letI : Algebra k' (F ⊗[k] k') := Algebra.TensorProduct.rightAlgebra
  let eSwap : F ⊗[k] k' ≃ₐ[k'] k' ⊗[k] F :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm k F k').toRingEquiv) fun _ ↦ rfl
  (((Algebra.TensorProduct.congr eSwap (AlgEquiv.refl : Ω ≃ₐ[k'] Ω)).toRingEquiv.trans
      (Algebra.TensorProduct.comm k' (k' ⊗[k] F) Ω).toRingEquiv).trans
    (Algebra.TensorProduct.cancelBaseChange k k' Ω Ω F).toRingEquiv).trans
    (Algebra.TensorProduct.comm k Ω F).toRingEquiv

/-- **Exact constants ascend along a linearly disjoint constant extension of a regular field.** -/
theorem _root_.IsIntegrallyClosedIn.of_constantCompositum_eq_top_of_linearDisjoint
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) : IsIntegrallyClosedIn k' F' := by
  let _ : Algebra k' (F ⊗[k] k') := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra (F ⊗[k] k') F' := (Algebra.TensorProduct.productMap
    (IsScalarTower.toAlgHom k F F') (IsScalarTower.toAlgHom k k' F')).toRingHom.toAlgebra
  have : IsScalarTower k' (F ⊗[k] k') F' :=
    .of_algebraMap_eq fun _ ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsFractionRing (F ⊗[k] k') F' := isFractionRing_tensorProduct_of_linearDisjoint H h
  have := isDomain_tensorProduct_of_isGeometricallyReduced hex (AlgebraicClosure k')
  have : IsDomain ((F ⊗[k] k') ⊗[k'] AlgebraicClosure k') :=
    (tensorProductRightEquiv (k := k) (k' := k') F (AlgebraicClosure k')).toMulEquiv.isDomain
  have : IsDomain (F' ⊗[k'] AlgebraicClosure k') :=
    isDomain_tensorProduct_of_isLocalization (nonZeroDivisors (F ⊗[k] k')) le_rfl
      F' (AlgebraicClosure k')
  exact algebraicClosure_eq_bot_iff_isIntegrallyClosedIn.mp
    (algebraicClosure_eq_bot_of_isDomain_tensorProduct (AlgebraicClosure k'))

/-- **Geometric reducedness ascends along any linearly disjoint constant extension.** -/
theorem isGeometricallyReduced_of_constantCompositum_eq_top_of_linearDisjoint
    [Algebra.IsGeometricallyReduced k F]
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) : Algebra.IsGeometricallyReduced k' F' := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  let C := AlgebraicClosure k; let Ω := AlgebraicClosure k'
  let j : C →ₐ[k] Ω := IsAlgClosed.lift
  algebraize [j.toRingHom]
  have : IsScalarTower k C Ω := .of_algebraMap_eq fun c ↦ (j.commutes c).symm
  have : IsReduced (C ⊗[k] F) := (Algebra.isGeometricallyReduced_field_iff k F).mp inferInstance
  have : IsReduced (Ω ⊗[C] (C ⊗[k] F)) := inferInstance
  let eC := (Algebra.TensorProduct.comm k F Ω).toRingEquiv.trans
    (Algebra.TensorProduct.cancelBaseChange k C Ω Ω F).symm.toRingEquiv
  have : IsReduced (F ⊗[k] Ω) := isReduced_of_injective eC eC.injective
  let _ : Algebra k' (F ⊗[k] k') := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra (F ⊗[k] k') F' := (Algebra.TensorProduct.productMap
    (IsScalarTower.toAlgHom k F F') (IsScalarTower.toAlgHom k k' F')).toRingHom.toAlgebra
  have : IsScalarTower k' (F ⊗[k] k') F' :=
    .of_algebraMap_eq fun _ ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsFractionRing (F ⊗[k] k') F' := isFractionRing_tensorProduct_of_linearDisjoint H h
  let e := tensorProductRightEquiv (k := k) (k' := k') F Ω
  have : IsReduced ((F ⊗[k] k') ⊗[k'] Ω) := isReduced_of_injective e e.injective
  have : IsReduced (F' ⊗[k'] Ω) :=
    isReduced_tensorProduct_of_isLocalization (nonZeroDivisors (F ⊗[k] k')) F' Ω
  exact isReduced_of_injective (Algebra.TensorProduct.comm k' Ω F')
    (Algebra.TensorProduct.comm k' Ω F').injective

/-- Over algebraically closed `k`, `F` is relatively algebraically closed in `F · k'`. -/
theorem isIntegrallyClosedIn_of_isAlgClosed_of_linearDisjoint [IsAlgClosed k]
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) : IsIntegrallyClosedIn F F' := by
  have : Algebra.IsGeometricallyReduced k k' := inferInstance
  have hcomm : constantCompositum k' F F' = ⊤ := by
    rw [← IntermediateField.toSubfield_inj, IntermediateField.top_toSubfield,
      constantCompositum_def, IntermediateField.adjoin_toSubfield, Set.union_comm,
      ← IntermediateField.adjoin_toSubfield, ← constantCompositum_def, h,
      IntermediateField.top_toSubfield]
  exact IsIntegrallyClosedIn.of_constantCompositum_eq_top_of_linearDisjoint
    isIntegrallyClosedIn_of_isAlgClosed H.symm' hcomm

section Parameter

private theorem linearIndependent_fieldRange {M : Type*} [Field M] [Algebra k M] [Algebra k' M]
    [IsScalarTower k k' M] {ι : Type*} {v : ι → M} (hv : LinearIndependent k' v) :
    LinearIndependent (IsScalarTower.toAlgHom k k' M).fieldRange v := by
  let ek' := (IsScalarTower.toAlgHom k k' M).equivFieldRange
  refine hv.map_of_injective_injective ek'.symm (AddMonoidHom.id M) (by simp) (by simp) fun c z ↦ ?_
  have hc : (ek' (ek'.symm c) : M) = (c : M) := congrArg Subtype.val (ek'.apply_symm_apply c)
  rw [AlgHom.equivFieldRange_apply_coe, IsScalarTower.toAlgHom_apply] at hc
  simp [Algebra.smul_def, hc]

private theorem linearDisjoint_adjoin_simple_of_transcendental {y : F'}
    (hy' : Transcendental k' y) :
    (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint k⟮y⟯ := by
  set A := (IsScalarTower.toAlgHom k k' F').fieldRange
  set S : Subalgebra k F' := Algebra.adjoin k {y}
  have hy : Transcendental k y := fun ha ↦ hy' (ha.tower_top k')
  let eS : Polynomial k ≃ₐ[k] S :=
    (AlgEquiv.ofInjective (Polynomial.aeval y) (transcendental_iff_injective.mp hy)).trans
      (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval k y).symm)
  let bS : Module.Basis ℕ k S := (Polynomial.basisMonomials k).map eS.toLinearEquiv
  have hbS : LinearIndependent A (S.val ∘ bS) :=
    (show S.val ∘ bS = fun n : ℕ ↦ y ^ n by ext n; simp [bS, eS]) ▸
      linearIndependent_fieldRange hy'.linearIndependent_pow
  have hAS : A.toSubalgebra.LinearDisjoint S := Subalgebra.LinearDisjoint.of_basis_right _ _ bS hbS
  let a := Module.Basis.ofVectorSpace k A
  exact IntermediateField.LinearDisjoint.of_basis_left a
    ((LinearIndependent.iff_fractionRing S k⟮y⟯).mp
      (hAS.symm.linearIndependent_right_of_flat a.linearIndependent))

private theorem linearDisjoint_of_transcendental_of_linearIndependent {x : F}
    (hx' : Transcendental k' (algebraMap F F' x)) {ι : Type*} (b : Module.Basis ι k⟮x⟯ F)
    (hb : LinearIndependent k'⟮algebraMap F F' x⟯ (algebraMap F F' ∘ b)) :
    (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F := by
  set y := algebraMap F F' x
  let γ := Module.Basis.ofVectorSpace k k⟮x⟯
  let B := γ.smulTower b
  have hmap : (k⟮x⟯ : IntermediateField k F).map (IsScalarTower.toAlgHom k F F') = k⟮y⟯ := by
    simp [y, IntermediateField.adjoin_map]
  have hle : k⟮y⟯ ≤ (k'⟮y⟯).restrictScalars k :=
    IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.mem_adjoin_simple_self k' y)
  let j : k⟮x⟯ ≃ₐ[k] k⟮y⟯ :=
    (k⟮x⟯.equivMap (IsScalarTower.toAlgHom k F F')).trans (IntermediateField.equivOfEq hmap)
  have hγ : LinearIndependent k' (algebraMap k⟮y⟯ F' ∘ (γ.map j.toLinearEquiv)) :=
    (linearDisjoint_adjoin_simple_of_transcendental hx').linearIndependent_algebraMap_comp
      (γ.map j.toLinearEquiv).linearIndependent
  let γ' : _ → k'⟮y⟯ := fun m ↦ ⟨j (γ m), hle (j (γ m)).2⟩
  have hγ' : LinearIndependent k' γ' := LinearIndependent.of_comp (k'⟮y⟯).val.toLinearMap hγ
  have hprod : LinearIndependent k' (algebraMap F F' ∘ B) := by
    convert linearIndependent_smul hγ' hb using 1
    ext ⟨m, i⟩
    have hj : (j (γ m) : F') = algebraMap F F' (γ m) := by simp [j]
    simp [B, Module.Basis.smulTower_apply, γ', Algebra.smul_def, hj]
  exact IntermediateField.LinearDisjoint.of_basis_right' B (linearIndependent_fieldRange hprod)

/-- **Linear disjointness over a shared parameter from degree preservation.** -/
theorem linearDisjoint_of_transcendental_of_finrank_eq (h : constantCompositum F k' F' = ⊤) {x : F}
    (hx' : Transcendental k' (algebraMap F F' x)) [FiniteDimensional k⟮x⟯ F]
    (hn : Module.finrank k'⟮algebraMap F F' x⟯ F' = Module.finrank k⟮x⟯ F) :
    (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F := by
  let b := Module.finBasis k⟮x⟯ F
  have hspan := span_range_basis_of_isAlgebraic_constantCompositum h k⟮x⟯ b
  rw [IntermediateField.range_algebraMap_adjoin_simple,
    IntermediateField.adjoin_adjoin_right] at hspan
  exact linearDisjoint_of_transcendental_of_linearIndependent hx' b
    (linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge (by rw [Fintype.card_fin, ← hn]))

omit [Field F'] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] in
private theorem isDomain_parameter_tensorProduct {C C' : Type*} [Field C] [Field C']
    [Algebra k C] [Algebra C F] [IsScalarTower k C F] [Algebra k C'] [Algebra k' C']
    [Algebra C C'] [IsScalarTower k k' C'] [IsScalarTower k C C']
    (HC : (IsScalarTower.toAlgHom k k' C').fieldRange.LinearDisjoint C)
    (hC : constantCompositum C k' C' = ⊤) [IsDomain (F ⊗[k] k')] : IsDomain (C' ⊗[C] F) := by
  let π₀ := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k C C')
    (IsScalarTower.toAlgHom k k' C')
  let _ : Algebra (C ⊗[k] k') C' := π₀.toRingHom.toAlgebra
  have : IsScalarTower C (C ⊗[k] k') C' := ⟨fun a z w ↦ by
    change π₀ (a • z) * w = a • (π₀ z * w)
    rw [Algebra.smul_def a z, map_mul, Algebra.smul_def a (π₀ z * w), mul_assoc]
    congr 1; simp [π₀, Algebra.TensorProduct.algebraMap_apply]⟩
  have : IsFractionRing (C ⊗[k] k') C' := isFractionRing_tensorProduct_of_linearDisjoint HC hC
  let eDom : ((C ⊗[k] k') ⊗[C] F) ≃+* F ⊗[k] k' :=
    (Algebra.TensorProduct.comm C (C ⊗[k] k') F).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange k C C F k').toRingEquiv
  have : IsDomain ((C ⊗[k] k') ⊗[C] F) := eDom.toMulEquiv.isDomain
  exact isDomain_tensorProduct_of_isLocalization (nonZeroDivisors (C ⊗[k] k')) le_rfl C' F

/-- **Linear disjointness over a shared parameter when `F ⊗[k] k'` is a domain.** -/
theorem linearDisjoint_of_transcendental_of_isDomain {x : F}
    (hx' : Transcendental k' (algebraMap F F' x)) [Algebra.IsAlgebraic k⟮x⟯ F]
    [IsDomain (F ⊗[k] k')] : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F := by
  set y := algebraMap F F' x
  have hle : (k⟮x⟯.map (IsScalarTower.toAlgHom k F F')) ≤ (k'⟮y⟯).restrictScalars k := by
    rw [IntermediateField.adjoin_map, Set.image_singleton, IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.mem_adjoin_simple_self k' y
  let ι : k⟮x⟯ →ₐ[k] k'⟮y⟯ :=
    ((IsScalarTower.toAlgHom k F F').comp k⟮x⟯.val).codRestrict
      ((k'⟮y⟯).restrictScalars k).toSubalgebra fun z ↦ hle ⟨z, z.2, rfl⟩
  let _ : Algebra k⟮x⟯ k'⟮y⟯ := ι.toRingHom.toAlgebra
  have : IsScalarTower k k⟮x⟯ k'⟮y⟯ := .of_algebraMap_eq fun c ↦ (ι.commutes c).symm
  have : IsScalarTower k⟮x⟯ k'⟮y⟯ F' := .of_algebraMap_eq' rfl
  let x₀ : k⟮x⟯ := ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩
  let y₀ : k'⟮y⟯ := ι x₀
  have hy₀ : Transcendental k' y₀ := (transcendental_algebraMap_iff (k'⟮y⟯).val.injective).mp hx'
  have hcomp : constantCompositum k⟮x⟯ k' k'⟮y⟯ = ⊤ := by
    let E : IntermediateField k' k'⟮y⟯ :=
      (constantCompositum k⟮x⟯ k' k'⟮y⟯).toSubfield.toIntermediateField
        (algebraMap_mem_constantCompositum _ _ _)
    have hE : k'⟮y₀⟯ ≤ E := IntermediateField.adjoin_simple_le_iff.mpr
      ((constantCompositum k⟮x⟯ k' k'⟮y⟯).algebraMap_mem x₀)
    refine eq_top_iff.mpr fun z _ ↦ hE ?_
    obtain ⟨w, hw, hwz⟩ : (z : F') ∈ (k'⟮y₀⟯).map (k'⟮y⟯).val := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]; exact z.2
    exact Subtype.ext hwz.symm ▸ hw
  have HC : (IsScalarTower.toAlgHom k k' k'⟮y⟯).fieldRange.LinearDisjoint k⟮x⟯ := by
    have hle₀ : k⟮x⟯ ≤ (k⟮y₀⟯.map ((k'⟮y⟯).val.restrictScalars k)).comap
        (IsScalarTower.toAlgHom k F F') :=
      IntermediateField.adjoin_simple_le_iff.mpr
        ⟨y₀, IntermediateField.mem_adjoin_simple_self k y₀, rfl⟩
    rw [IntermediateField.linearDisjoint_iff]
    refine Subalgebra.LinearDisjoint.of_le_right_of_flat
      (linearDisjoint_adjoin_simple_of_transcendental hy₀) ?_
    rintro _ ⟨z, rfl⟩; obtain ⟨w, hw, hwz⟩ := hle₀ z.2; exact ⟨⟨w, hw⟩, Subtype.ext hwz⟩
  have : IsDomain (k'⟮y⟯ ⊗[k⟮x⟯] F) := isDomain_parameter_tensorProduct HC hcomp
  let _ : Field (k'⟮y⟯ ⊗[k⟮x⟯] F) :=
    (Algebra.TensorProduct.isField_of_isAlgebraic k⟮x⟯ k'⟮y⟯ F (.inr inferInstance)).toField
  let ψ : k'⟮y⟯ ⊗[k⟮x⟯] F →ₐ[k'⟮y⟯] F' :=
    Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId k'⟮y⟯ F')
      (IsScalarTower.toAlgHom k⟮x⟯ F F')
  let b := Module.Basis.ofVectorSpace k⟮x⟯ F
  have hfun : algebraMap F F' ∘ b = ψ.toLinearMap ∘ b.baseChange k'⟮y⟯ := by ext i; simp [ψ]
  exact linearDisjoint_of_transcendental_of_linearIndependent hx' b <| hfun ▸
    (b.baseChange k'⟮y⟯).linearIndependent.map' ψ.toLinearMap
      (LinearMap.ker_eq_bot.mpr ψ.toRingHom.injective)

/-- Linear disjointness over a shared parameter for regular `F / k`. -/
theorem linearDisjoint_of_isGeometricallyReduced_of_transcendental
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F] {x : F}
    (hx' : Transcendental k' (algebraMap F F' x)) [Algebra.IsAlgebraic k⟮x⟯ F] :
    (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F :=
  have := isDomain_tensorProduct_of_isGeometricallyReduced hex k'
  linearDisjoint_of_transcendental_of_isDomain hx'

end Parameter

section RatFunc

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']

/-- Linear disjointness in a compatible `RatFunc` tower for regular `F / k`. -/
theorem linearDisjoint_of_isGeometricallyReduced_ratFunc
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    [Algebra.IsAlgebraic (RatFunc k) F]
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) :
    (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F := by
  have hx : Transcendental k (algebraMap (RatFunc k) F RatFunc.X) :=
    (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (RatFunc k) F)).mpr RatFunc.transcendental_X
  have hx' : Transcendental k' (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) :=
    hX ▸ (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (RatFunc k') F')).mpr RatFunc.transcendental_X
  let e := RatFunc.algEquivOfTranscendental _ hx
  have : Algebra.IsAlgebraic k⟮algebraMap (RatFunc k) F RatFunc.X⟯ F := ⟨fun w ↦ by
    obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := RatFunc k) w
    have hew : (algebraMap k⟮algebraMap (RatFunc k) F RatFunc.X⟯ F).comp e.toRingHom =
        algebraMap (RatFunc k) F := RingHom.ext coe_algEquivOfTranscendental_algebraMap_X_apply
    refine ⟨p.map e.toRingHom, Polynomial.map_ne_zero hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hew, ← Polynomial.aeval_def, hp]⟩
  exact linearDisjoint_of_isGeometricallyReduced_of_transcendental hex hx'

/-- **A regular function field over `k(t)` keeps its degree under any constant extension.** -/
theorem finrank_ratFunc_eq_of_isGeometricallyReduced [FiniteDimensional (RatFunc k) F]
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    (h : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) :
    Module.finrank (RatFunc k') F' = Module.finrank (RatFunc k) F := by
  have H := linearDisjoint_of_isGeometricallyReduced_ratFunc hex hX
  have : FiniteDimensional k⟮algebraMap (RatFunc k) F RatFunc.X⟯ F :=
    Module.finite_of_finrank_pos
      (finrank_adjoin_algebraMap_X (k := k) (F := F) ▸ Module.finrank_pos)
  rw [← finrank_adjoin_algebraMap_X (k := k') (F := F'), ← hX,
    finrank_over_adjoin_simple_eq_of_linearDisjoint H h, finrank_adjoin_algebraMap_X]

/-- **Degree preservation over `k(t)` implies linear disjointness of constants.** -/
theorem linearDisjoint_of_finrank_ratFunc_eq [FiniteDimensional (RatFunc k) F]
    (h : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    (hn : Module.finrank (RatFunc k') F' = Module.finrank (RatFunc k) F) :
    (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F := by
  have hx' : Transcendental k' (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) :=
    hX ▸ (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (RatFunc k') F')).mpr RatFunc.transcendental_X
  have : FiniteDimensional k⟮algebraMap (RatFunc k) F RatFunc.X⟯ F :=
    Module.finite_of_finrank_pos
      (finrank_adjoin_algebraMap_X (k := k) (F := F) ▸ Module.finrank_pos)
  refine linearDisjoint_of_transcendental_of_finrank_eq h hx' ?_
  rw [hX, finrank_adjoin_algebraMap_X, finrank_adjoin_algebraMap_X, hn]

end RatFunc

end LinearDisjoint

end TauCeti
