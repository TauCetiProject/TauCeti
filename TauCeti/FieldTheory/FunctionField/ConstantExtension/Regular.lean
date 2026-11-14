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
field extension `k' / k`, algebraic or transcendental.

When `k' / k` is algebraic, `F ⊗[k] k'` is already a field and multiplication
`F ⊗[k] k' → F · k'` is an isomorphism (`TauCeti.productMap_bijective_of_isGeometricallyReduced`).
When `k' / k` may be transcendental, linear disjointness of `F` and `k'` in an ambient field `F'`
is equivalent to injectivity of `F ⊗[k] k' → F'` (`TauCeti.productMap_injective_iff_linearDisjoint`)
and identifies `F · k'` with the fraction field of `F ⊗[k] k'`
(`TauCeti.isFractionRing_tensorProduct_of_linearDisjoint`). Under linear disjointness, exactness of
constants descends unconditionally (`TauCeti.isIntegrallyClosedIn_of_linearDisjoint`), while
exactness of constants and geometric reducedness ascend along any linearly disjoint compositum
(`IsIntegrallyClosedIn.of_constantCompositum_eq_top_of_linearDisjoint`,
`TauCeti.isGeometricallyReduced_of_constantCompositum_eq_top_of_linearDisjoint`). Symmetrizing the
two factors shows that over an algebraically closed base field `k`, `F` is relatively algebraically
closed in every linearly disjoint compositum `F · k'`
(`TauCeti.isIntegrallyClosedIn_of_isAlgClosed_of_linearDisjoint`).

Over a shared parameter `x ∈ F` whose image stays transcendental over `k'`, linear disjointness of
`F` and `k'` follows automatically either when `F ⊗[k] k'` is a domain and `F / k(x)` is algebraic
(`TauCeti.linearDisjoint_of_transcendental_of_isDomain`), or when `F' = F · k'` has the same finite
degree over `k'(x)` as `F` has over `k(x)`
(`TauCeti.linearDisjoint_of_transcendental_of_finrank_eq`).

## Main results

* `TauCeti.productMap_bijective_of_isGeometricallyReduced` and
  `TauCeti.productMap_bijective_of_separating`: for `F` regular over `k`, multiplication
  `F ⊗[k] k' → F · k'` is bijective for every algebraic extension `k' / k`.
* `TauCeti.productMap_injective_iff_linearDisjoint` and
  `TauCeti.isFractionRing_tensorProduct_of_linearDisjoint`: linear disjointness is injectivity of
  `F ⊗[k] k' → F'` and makes `F · k'` a fraction field of `F ⊗[k] k'`.
* `TauCeti.isIntegrallyClosedIn_of_linearDisjoint`,
  `IsIntegrallyClosedIn.of_constantCompositum_eq_top_of_linearDisjoint`,
  `TauCeti.isGeometricallyReduced_of_constantCompositum_eq_top_of_linearDisjoint`, and
  `TauCeti.isIntegrallyClosedIn_of_isAlgClosed_of_linearDisjoint`: descent and ascent of exact
  constants and geometric reducedness along linearly disjoint constant extensions.
* `TauCeti.linearDisjoint_of_transcendental_of_isDomain` and
  `TauCeti.linearDisjoint_of_transcendental_of_finrank_eq`: automatic linear disjointness over a
  shared transcendental parameter, together with their `RatFunc` specializations.

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

/-- Multiplication `F ⊗[k] k' → F'` is injective precisely when `k'` and `F` are linearly disjoint
over `k` inside `F'`. No algebraicity assumption on either extension is needed. -/
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
      (fF.range.mulMap fk'.range).comp e.toAlgHom := by
    ext x <;> rfl
  rw [h, AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, Function.Injective.of_comp_iff' _ e.bijective]

/-- **A linearly disjoint compositum is the fraction field of the tensor product.** If `F` and `k'`
are linearly disjoint over `k` in `F'` and `F' = F · k'`, then `F'` is a fraction field of the
domain `F ⊗[k] k'` under multiplication. -/
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
      algebraMap (F ⊗[k] k') F' :=
    RingHom.ext (IsFractionRing.lift_algebraMap hπ)
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
  have hfield := IsFractionRing.ringHom_fieldRange_eq_of_comp_eq_of_range_eq hcomp hrange
  have htop : ψ.fieldRange = ⊤ := by
    rw [hfield, ← IntermediateField.adjoin_toSubfield, ← constantCompositum_def, h,
      IntermediateField.top_toSubfield]
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors (F ⊗[k] k'))
    (AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective ψ
      ⟨ψ.injective, RingHom.fieldRange_eq_top_iff.mp htop⟩) (IsFractionRing.lift_algebraMap hπ))

/-- **Exact constants descend along any linearly disjoint extension.** If `F` and `k'` are linearly
disjoint over `k` in `F'` and `k'` is relatively algebraically closed in `F'`, then `k` is
relatively algebraically closed in `F`: any element of `F` algebraic over `k` lies in `k' ∩ F = k`.
The extension `k' / k` may be transcendental. -/
theorem isIntegrallyClosedIn_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hex' : IsIntegrallyClosedIn k' F') : IsIntegrallyClosedIn k F := by
  refine isIntegrallyClosedIn_iff_forall_isAlgebraic.mpr fun x hx ↦ ?_
  have hx' : IsAlgebraic k' (algebraMap F F' x) :=
    (hx.algHom (IsScalarTower.toAlgHom k F F')).tower_top k'
  obtain ⟨c, hc⟩ := isIntegrallyClosedIn_iff_forall_isAlgebraic.mp hex' _ hx'
  have hmem : algebraMap F F' x ∈
      (IsScalarTower.toAlgHom k k' F').fieldRange ⊓
        (IsScalarTower.toAlgHom k F F').fieldRange :=
    ⟨⟨c, hc⟩, ⟨x, rfl⟩⟩
  rw [(IntermediateField.linearDisjoint_iff'.mpr H).inf_eq_bot,
    IntermediateField.mem_bot] at hmem
  obtain ⟨a, ha⟩ := hmem
  exact ⟨a, (algebraMap F F').injective (by rwa [← IsScalarTower.algebraMap_apply k F F'])⟩

/-- If `F / k` is regular and `F' = F · k'` linearly disjointly, then
`F' ⊗[k'] AlgebraicClosure k'` is a domain: it is a localization of
`(F ⊗[k] k') ⊗[k'] AlgebraicClosure k' ≃ F ⊗[k] AlgebraicClosure k'`. -/
private theorem isDomain_tensorProduct_algebraicClosure_of_linearDisjoint
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) :
    IsDomain (F' ⊗[k'] AlgebraicClosure k') := by
  let _ : Algebra k' (F ⊗[k] k') := Algebra.TensorProduct.rightAlgebra
  let π := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
    (IsScalarTower.toAlgHom k k' F')
  let _ : Algebra (F ⊗[k] k') F' := π.toRingHom.toAlgebra
  have : IsScalarTower k' (F ⊗[k] k') F' := .of_algebraMap_eq fun c ↦ by
    simp [π, RingHom.algebraMap_toAlgebra]
  have : IsFractionRing (F ⊗[k] k') F' := isFractionRing_tensorProduct_of_linearDisjoint H h
  have := isDomain_tensorProduct_of_isGeometricallyReduced hex (AlgebraicClosure k')
  let eSwap : F ⊗[k] k' ≃ₐ[k'] k' ⊗[k] F :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm k F k').toRingEquiv) fun _ ↦ rfl
  let e : ((F ⊗[k] k') ⊗[k'] AlgebraicClosure k') ≃ₐ[k] F ⊗[k] AlgebraicClosure k' :=
    ((((Algebra.TensorProduct.congr eSwap
      (AlgEquiv.refl : AlgebraicClosure k' ≃ₐ[k'] _)).trans
        (Algebra.TensorProduct.comm k' (k' ⊗[k] F) (AlgebraicClosure k'))).restrictScalars k).trans
      ((Algebra.TensorProduct.cancelBaseChange k k' (AlgebraicClosure k')
        (AlgebraicClosure k') F).restrictScalars k)).trans
      (Algebra.TensorProduct.comm k (AlgebraicClosure k') F)
  have : IsDomain ((F ⊗[k] k') ⊗[k'] AlgebraicClosure k') := e.toMulEquiv.isDomain
  exact isDomain_tensorProduct_of_isLocalization (nonZeroDivisors (F ⊗[k] k')) le_rfl
    F' (AlgebraicClosure k')

/-- **Exact constants ascend along a linearly disjoint constant extension of a regular field.** If
`F` is geometrically reduced with exact constants `k`, and `F' = F · k'` linearly disjointly over
`k`, then `k'` is relatively algebraically closed in `F'`. The extension `k' / k` may be
transcendental. -/
theorem _root_.IsIntegrallyClosedIn.of_constantCompositum_eq_top_of_linearDisjoint
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) : IsIntegrallyClosedIn k' F' :=
  have := isDomain_tensorProduct_algebraicClosure_of_linearDisjoint hex H h
  algebraicClosure_eq_bot_iff_isIntegrallyClosedIn.mp
    (algebraicClosure_eq_bot_of_isDomain_tensorProduct (AlgebraicClosure k'))

/-- **Geometric reducedness ascends along any linearly disjoint constant extension.** Unlike ascent
of exact constants, `k` need not be integrally closed in `F`. -/
theorem isGeometricallyReduced_of_constantCompositum_eq_top_of_linearDisjoint
    [Algebra.IsGeometricallyReduced k F]
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) : Algebra.IsGeometricallyReduced k' F' := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  let C := AlgebraicClosure k
  let Ω := AlgebraicClosure k'
  let j : C →ₐ[k] Ω := IsAlgClosed.lift
  algebraize [j.toRingHom]
  have : IsScalarTower k C Ω := .of_algebraMap_eq fun c ↦ (j.commutes c).symm
  have : IsReduced (C ⊗[k] F) := (Algebra.isGeometricallyReduced_field_iff k F).mp inferInstance
  have : IsReduced (Ω ⊗[C] (C ⊗[k] F)) := inferInstance
  let eC := (Algebra.TensorProduct.comm k F Ω).trans
    ((Algebra.TensorProduct.cancelBaseChange k C Ω Ω F).symm.restrictScalars k)
  have : IsReduced (F ⊗[k] Ω) := isReduced_of_injective eC eC.injective
  let _ : Algebra k' (F ⊗[k] k') := Algebra.TensorProduct.rightAlgebra
  let π := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
    (IsScalarTower.toAlgHom k k' F')
  let _ : Algebra (F ⊗[k] k') F' := π.toRingHom.toAlgebra
  have : IsScalarTower k' (F ⊗[k] k') F' := .of_algebraMap_eq fun c ↦ by
    simp [π, RingHom.algebraMap_toAlgebra]
  have : IsFractionRing (F ⊗[k] k') F' := isFractionRing_tensorProduct_of_linearDisjoint H h
  let eSwap : F ⊗[k] k' ≃ₐ[k'] k' ⊗[k] F :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm k F k').toRingEquiv) fun _ ↦ rfl
  let e : ((F ⊗[k] k') ⊗[k'] Ω) ≃ₐ[k] F ⊗[k] Ω :=
    ((((Algebra.TensorProduct.congr eSwap (AlgEquiv.refl : Ω ≃ₐ[k'] Ω)).trans
        (Algebra.TensorProduct.comm k' (k' ⊗[k] F) Ω)).restrictScalars k).trans
      ((Algebra.TensorProduct.cancelBaseChange k k' Ω Ω F).restrictScalars k)).trans
      (Algebra.TensorProduct.comm k Ω F)
  have : IsReduced ((F ⊗[k] k') ⊗[k'] Ω) := isReduced_of_injective e e.injective
  have : IsReduced (F' ⊗[k'] Ω) :=
    isReduced_tensorProduct_of_isLocalization (nonZeroDivisors (F ⊗[k] k')) F' Ω
  exact isReduced_of_injective (Algebra.TensorProduct.comm k' Ω F')
    (Algebra.TensorProduct.comm k' Ω F').injective

/-- **Over an algebraically closed base field, `F` is relatively algebraically closed in any
linearly disjoint compositum `F · k'`.** Since `k` is algebraically closed, `k' / k` is itself a
regular extension, so interchanging the roles of `F` and `k'` makes `F` integrally closed in `F'`.
For instance, `(AlgebraicClosure ℚ)(C)` is relatively algebraically closed in `ℂ(C)` for any curve
`C` over `AlgebraicClosure ℚ`. -/
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

/-- Linear independence over `k'` transfers to the image `IntermediateField` of `k'` in `M`. -/
private theorem linearIndependent_fieldRange {M : Type*} [Field M] [Algebra k M] [Algebra k' M]
    [IsScalarTower k k' M] {ι : Type*} {v : ι → M} (hv : LinearIndependent k' v) :
    LinearIndependent (IsScalarTower.toAlgHom k k' M).fieldRange v := by
  let ek' := (IsScalarTower.toAlgHom k k' M).equivFieldRange
  refine hv.map_of_injective_injective ek'.symm (AddMonoidHom.id M) (by simp) (by simp) fun c z ↦ ?_
  have hc : (ek' (ek'.symm c) : M) = (c : M) := congrArg Subtype.val (ek'.apply_symm_apply c)
  rw [AlgHom.equivFieldRange_apply_coe, IsScalarTower.toAlgHom_apply] at hc
  simp [Algebra.smul_def, hc]

/-- If `y ∈ F'` is transcendental over `k'`, then `k'` and `k(y)` are linearly disjoint over `k`. -/
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
  have hbS : LinearIndependent A (S.val ∘ bS) := by
    have hfun : S.val ∘ bS = fun n : ℕ ↦ y ^ n := by
      ext n
      simp [bS, eS]
    rw [hfun]
    exact linearIndependent_fieldRange hy'.linearIndependent_pow
  have hAS : A.toSubalgebra.LinearDisjoint S := Subalgebra.LinearDisjoint.of_basis_right _ _ bS hbS
  let a := Module.Basis.ofVectorSpace k A
  have haK : LinearIndependent k⟮y⟯ (A.val ∘ a) :=
    (LinearIndependent.iff_fractionRing S k⟮y⟯).mp
      (hAS.symm.linearIndependent_right_of_flat a.linearIndependent)
  exact IntermediateField.LinearDisjoint.of_basis_left a haK

/-- If `x ∈ F` stays transcendental over `k'` in `F'` and a `k(x)`-basis of `F` stays linearly
independent over `k'(x)`, then `k'` and `F` are linearly disjoint over `k`. -/
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
  have hγ' : LinearIndependent k' γ' :=
    LinearIndependent.of_comp (k'⟮y⟯).val.toLinearMap hγ
  have hprod : LinearIndependent k' (algebraMap F F' ∘ B) := by
    have hsmul := linearIndependent_smul hγ' hb
    convert hsmul using 1
    ext ⟨m, i⟩
    have hj : (j (γ m) : F') = algebraMap F F' (γ m) := by simp [j]
    simp [B, Module.Basis.smulTower_apply, γ', Algebra.smul_def, hj]
  exact IntermediateField.LinearDisjoint.of_basis_right' B (linearIndependent_fieldRange hprod)

/-- **Linear disjointness over a shared parameter from degree preservation.** If `F' = F · k'`,
`x ∈ F` stays transcendental over `k'` in `F'`, and `[F' : k'(x)] = [F : k(x)]` with `F / k(x)`
finite, then `k'` and `F` are linearly disjoint over `k`. -/
theorem linearDisjoint_of_transcendental_of_finrank_eq
    (h : constantCompositum F k' F' = ⊤) {x : F}
    (hx' : Transcendental k' (algebraMap F F' x)) [FiniteDimensional k⟮x⟯ F]
    (hn : Module.finrank k'⟮algebraMap F F' x⟯ F' = Module.finrank k⟮x⟯ F) :
    (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F := by
  let b := Module.finBasis k⟮x⟯ F
  have hspan := span_range_basis_of_isAlgebraic_constantCompositum h k⟮x⟯ b
  rw [IntermediateField.range_algebraMap_adjoin_simple,
    IntermediateField.adjoin_adjoin_right] at hspan
  have hb : LinearIndependent k'⟮algebraMap F F' x⟯ (algebraMap F F' ∘ b) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge
      (by rw [Fintype.card_fin, ← hn])
  exact linearDisjoint_of_transcendental_of_linearIndependent hx' b hb

omit [Field F] [Algebra k F] [Field F'] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- `RatFunc k'` is the fraction field of `(RatFunc k) ⊗[k] k'` under `X ↦ X`. -/
private theorem isFractionRing_ratFunc_tensorProduct :
    letI : Algebra (RatFunc k) (RatFunc k') :=
      ratFuncAlgebraOfTranscendental (fun ha ↦ RatFunc.transcendental_X (ha.tower_top k'))
    haveI : IsScalarTower k (RatFunc k) (RatFunc k') :=
      isScalarTower_ratFuncAlgebraOfTranscendental _
    letI := (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k (RatFunc k) (RatFunc k'))
      (IsScalarTower.toAlgHom k k' (RatFunc k'))).toRingHom.toAlgebra
    IsFractionRing ((RatFunc k) ⊗[k] k') (RatFunc k') := by
  have hX : Transcendental k (RatFunc.X : RatFunc k') :=
    fun ha ↦ RatFunc.transcendental_X (ha.tower_top k')
  let _ : Algebra (RatFunc k) (RatFunc k') := ratFuncAlgebraOfTranscendental hX
  have : IsScalarTower k (RatFunc k) (RatFunc k') := isScalarTower_ratFuncAlgebraOfTranscendental hX
  have hXeq : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X :=
    algebraMap_ratFuncAlgebraOfTranscendental_X hX
  have hcomp : constantCompositum (RatFunc k) k' (RatFunc k') = ⊤ := by
    let E : IntermediateField k' (RatFunc k') :=
      (constantCompositum (RatFunc k) k' (RatFunc k')).toSubfield.toIntermediateField
        (algebraMap_mem_constantCompositum (RatFunc k) k' (RatFunc k'))
    have hE : E = ⊤ := eq_top_iff.mpr <| RatFunc.adjoin_X.symm.le.trans <|
      IntermediateField.adjoin_simple_le_iff.mpr
        (hXeq ▸ (constantCompositum (RatFunc k) k' (RatFunc k')).algebraMap_mem RatFunc.X)
    exact eq_top_iff.mpr fun f _ ↦ (hE ▸ IntermediateField.mem_top : f ∈ E)
  have : FiniteDimensional k⟮(RatFunc.X : RatFunc k)⟯ (RatFunc k) :=
    Module.finite_of_finrank_pos
      (finrank_adjoin_algebraMap_X (k := k) (F := RatFunc k) ▸ Module.finrank_pos)
  have H₀ : (IsScalarTower.toAlgHom k k' (RatFunc k')).fieldRange.LinearDisjoint (RatFunc k) := by
    refine linearDisjoint_of_transcendental_of_finrank_eq hcomp
      (hXeq ▸ RatFunc.transcendental_X) ?_
    rw [hXeq,
      show (RatFunc.X : RatFunc k') = algebraMap (RatFunc k') (RatFunc k') RatFunc.X from rfl,
      show (RatFunc.X : RatFunc k) = algebraMap (RatFunc k) (RatFunc k) RatFunc.X from rfl,
      finrank_adjoin_algebraMap_X, finrank_adjoin_algebraMap_X, Module.finrank_self,
      Module.finrank_self]
  exact isFractionRing_tensorProduct_of_linearDisjoint H₀ hcomp

omit [Field F'] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- Localizing `F ⊗[k] k' ≃ ((RatFunc k) ⊗[k] k') ⊗[RatFunc k] F` shows that
`(RatFunc k') ⊗[RatFunc k] F` is a domain whenever `F ⊗[k] k'` is. -/
private theorem isDomain_ratFunc_tensorProduct_of_isDomain [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [IsDomain (F ⊗[k] k')] :
    letI : Algebra (RatFunc k) (RatFunc k') :=
      ratFuncAlgebraOfTranscendental (fun ha ↦ RatFunc.transcendental_X (ha.tower_top k'))
    IsDomain ((RatFunc k') ⊗[RatFunc k] F) := by
  have hX : Transcendental k (RatFunc.X : RatFunc k') :=
    fun ha ↦ RatFunc.transcendental_X (ha.tower_top k')
  let _ : Algebra (RatFunc k) (RatFunc k') := ratFuncAlgebraOfTranscendental hX
  have : IsScalarTower k (RatFunc k) (RatFunc k') := isScalarTower_ratFuncAlgebraOfTranscendental hX
  let π₀ := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k (RatFunc k) (RatFunc k'))
    (IsScalarTower.toAlgHom k k' (RatFunc k'))
  let _ : Algebra ((RatFunc k) ⊗[k] k') (RatFunc k') := π₀.toRingHom.toAlgebra
  have : IsScalarTower (RatFunc k) ((RatFunc k) ⊗[k] k') (RatFunc k') := ⟨fun a z w ↦ by
    change π₀ (a • z) * w = a • (π₀ z * w)
    rw [Algebra.smul_def a z, map_mul, Algebra.smul_def a (π₀ z * w), mul_assoc]
    congr 1; simp [π₀, Algebra.TensorProduct.algebraMap_apply]⟩
  have : IsFractionRing ((RatFunc k) ⊗[k] k') (RatFunc k') := isFractionRing_ratFunc_tensorProduct
  let eDom : (((RatFunc k) ⊗[k] k') ⊗[RatFunc k] F) ≃+* F ⊗[k] k' :=
    (Algebra.TensorProduct.comm (RatFunc k) ((RatFunc k) ⊗[k] k') F).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange k (RatFunc k) (RatFunc k) F k').toRingEquiv
  have : IsDomain (((RatFunc k) ⊗[k] k') ⊗[RatFunc k] F) := eDom.toMulEquiv.isDomain
  exact isDomain_tensorProduct_of_isLocalization (nonZeroDivisors ((RatFunc k) ⊗[k] k'))
    le_rfl (RatFunc k') F

/-- **Linear disjointness over a shared parameter when `F ⊗[k] k'` is a domain.** If `x ∈ F` stays
transcendental over `k'` in `F'`, `F / k(x)` is algebraic, and `F ⊗[k] k'` is a domain, then `k'`
and `F` are linearly disjoint over `k`. -/
theorem linearDisjoint_of_transcendental_of_isDomain {x : F}
    (hx' : Transcendental k' (algebraMap F F' x)) [Algebra.IsAlgebraic k⟮x⟯ F]
    [IsDomain (F ⊗[k] k')] :
    (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F := by
  set y := algebraMap F F' x
  have hy : Transcendental k y := fun ha ↦ hx' (ha.tower_top k')
  have hx : Transcendental k x :=
    (transcendental_algebraMap_iff (algebraMap F F').injective).mp hy
  have hX : Transcendental k (RatFunc.X : RatFunc k') :=
    fun ha ↦ RatFunc.transcendental_X (ha.tower_top k')
  let _ : Algebra (RatFunc k) F := ratFuncAlgebraOfTranscendental hx
  let _ : Algebra (RatFunc k') F' := ratFuncAlgebraOfTranscendental hx'
  let _ : Algebra (RatFunc k) (RatFunc k') := ratFuncAlgebraOfTranscendental hX
  let _ : Algebra (RatFunc k) F' := ratFuncAlgebraOfTranscendental hy
  have : IsScalarTower k (RatFunc k) F := isScalarTower_ratFuncAlgebraOfTranscendental hx
  have : IsScalarTower (RatFunc k) (RatFunc k') F' :=
    isScalarTower_ratFunc_ratFunc_of_transcendental hy hx' hX
  have : IsScalarTower (RatFunc k) F F' :=
    isScalarTower_ratFuncAlgebraOfTranscendental_algebraMap hx
  have : Algebra.IsAlgebraic (RatFunc k) F := ⟨fun w ↦ by
    obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := k⟮x⟯) w
    let ex := (RatFunc.algEquivOfTranscendental x hx).symm
    have hex : (algebraMap (RatFunc k) F).comp ex.toRingHom = algebraMap k⟮x⟯ F := by
      ext z; simp [ex, algebraMap_ratFuncAlgebraOfTranscendental_apply]
    refine ⟨p.map ex.toRingHom, Polynomial.map_ne_zero hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hex, ← Polynomial.aeval_def, hp]⟩
  have : IsDomain ((RatFunc k') ⊗[RatFunc k] F) := isDomain_ratFunc_tensorProduct_of_isDomain
  let _ : Field ((RatFunc k') ⊗[RatFunc k] F) :=
    (Algebra.TensorProduct.isField_of_isAlgebraic (RatFunc k) (RatFunc k') F
      (.inr inferInstance)).toField
  let ψ : (RatFunc k') ⊗[RatFunc k] F →ₐ[RatFunc k'] F' :=
    Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId (RatFunc k') F')
      (IsScalarTower.toAlgHom (RatFunc k) F F')
  let b := Module.Basis.ofVectorSpace k⟮x⟯ F
  let bR : Module.Basis _ (RatFunc k) F :=
    b.mapCoeffs (RatFunc.algEquivOfTranscendental x hx).symm.toRingEquiv fun c w ↦ by
      simp [Algebra.smul_def, algebraMap_ratFuncAlgebraOfTranscendental_apply]
  have hbR : LinearIndependent (RatFunc k') (algebraMap F F' ∘ b) := by
    have hfun : algebraMap F F' ∘ b = ψ.toLinearMap ∘ bR.baseChange (RatFunc k') := by
      ext i; simp [ψ, bR]
    rw [hfun]
    exact (bR.baseChange (RatFunc k')).linearIndependent.map' ψ.toLinearMap
      (LinearMap.ker_eq_bot.mpr ψ.toRingHom.injective)
  let ey := RatFunc.algEquivOfTranscendental y hx'
  have hby : LinearIndependent k'⟮y⟯ (algebraMap F F' ∘ b) :=
    hbR.map_of_injective_injective ey.symm (AddMonoidHom.id F') (by simp) (by simp) fun c z ↦ by
      have hc : algebraMap (RatFunc k') F' (ey.symm c) = (c : F') := by
        simp [ey, algebraMap_ratFuncAlgebraOfTranscendental_apply]
      simp [Algebra.smul_def, hc]
  exact linearDisjoint_of_transcendental_of_linearIndependent hx' b hby

/-- If `F / k` is geometrically reduced with exact constants, `F / k(x)` is algebraic, and `x` stays
transcendental over `k'` in `F'`, then `k'` and `F` are linearly disjoint over `k`. -/
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

/-- In a `RatFunc` tower where `t` acts compatibly on `F` and `F'`, if `F / k` is geometrically
reduced with exact constants and `F / k(t)` is algebraic, then `k'` and `F` are linearly disjoint
over `k`. The constant extension `k' / k` may be transcendental. -/
theorem linearDisjoint_of_isGeometricallyReduced_ratFunc
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    [Algebra.IsAlgebraic (RatFunc k) F]
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) :
    (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F := by
  have hx : Transcendental k (algebraMap (RatFunc k) F RatFunc.X) :=
    (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (RatFunc k) F)).mpr RatFunc.transcendental_X
  have hx' : Transcendental k' (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) := by
    rw [hX]
    exact (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (RatFunc k') F')).mpr RatFunc.transcendental_X
  let e := RatFunc.algEquivOfTranscendental _ hx
  have : Algebra.IsAlgebraic k⟮algebraMap (RatFunc k) F RatFunc.X⟯ F := ⟨fun w ↦ by
    obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := RatFunc k) w
    have hew : (algebraMap k⟮algebraMap (RatFunc k) F RatFunc.X⟯ F).comp e.toRingHom =
        algebraMap (RatFunc k) F :=
      RingHom.ext coe_algEquivOfTranscendental_algebraMap_X_apply
    refine ⟨p.map e.toRingHom, Polynomial.map_ne_zero hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hew, ← Polynomial.aeval_def, hp]⟩
  exact linearDisjoint_of_isGeometricallyReduced_of_transcendental hex hx'

/-- **A regular function field over `k(t)` keeps its degree under any constant extension**: if `F`
is geometrically reduced with exact constants `k`, `F' = F · k'`, and `t` acts compatibly, then
`[F' : k'(t)] = [F : k(t)]`, whether `k' / k` is algebraic or transcendental. -/
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

/-- **Degree preservation over `k(t)` implies linear disjointness of constants**: if `F' = F · k'`,
`t` acts compatibly, and `[F' : k'(t)] = [F : k(t)]`, then `k'` and `F` are linearly disjoint over
`k`. -/
theorem linearDisjoint_of_finrank_ratFunc_eq [FiniteDimensional (RatFunc k) F]
    (h : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    (hn : Module.finrank (RatFunc k') F' = Module.finrank (RatFunc k) F) :
    (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F := by
  have hx' : Transcendental k' (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) := by
    rw [hX]
    exact (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (RatFunc k') F')).mpr RatFunc.transcendental_X
  have : FiniteDimensional k⟮algebraMap (RatFunc k) F RatFunc.X⟯ F :=
    Module.finite_of_finrank_pos
      (finrank_adjoin_algebraMap_X (k := k) (F := F) ▸ Module.finrank_pos)
  refine linearDisjoint_of_transcendental_of_finrank_eq h hx' ?_
  rw [hX, finrank_adjoin_algebraMap_X, finrank_adjoin_algebraMap_X, hn]

end RatFunc

end LinearDisjoint

end TauCeti
