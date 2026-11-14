/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.FractionField
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.TensorProduct
import TauCeti.FieldTheory.AlgebraicClosure
import TauCeti.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.FieldTheory.RatFunc.Transcendental
import TauCeti.RingTheory.TensorProduct.IsDomain

/-!
# Constant field extensions of regular fields

Let `F / k` be a field extension that is geometrically reduced and has exact constants, for
instance one with a separating element and exact constants. Then `F` is a regular extension of `k`
(`TauCeti.isDomain_tensorProduct_of_isGeometricallyReduced`), so `F ⊗[k] k'` is a domain for every
field extension `k' / k`. When `k' / k` is algebraic, multiplication `F ⊗[k] k' → F · k'` is an
isomorphism onto the constant field extension, discharging the domain hypothesis of
`TauCeti.productMap_bijective_of_constantCompositum_eq_top`. For a function field `F`, this says
that the function field of the curve after an algebraic extension of the constants is
`F ⊗[k] k'`.

For arbitrary extensions `k' / k`, exactness of constants ascends along any linearly disjoint
compositum `F · k'`, and when `F` is algebraic over a shared transcendental parameter (or over
`k(t)`), regularity of `F / k` supplies linear disjointness and degree preservation over `k'(t)`.

## Main results

* `TauCeti.productMap_bijective_of_isGeometricallyReduced` and
  `TauCeti.productMap_bijective_of_separating`: for `F` regular over `k`, multiplication
  `F ⊗[k] k' → F · k'` is an isomorphism for every algebraic extension `k' / k`.
* `IsIntegrallyClosedIn.of_constantCompositum_eq_top_of_linearDisjoint`: exact constants ascend
  along a linearly disjoint constant extension of a regular field.
* `TauCeti.linearDisjoint_of_transcendental_of_isDomain`,
  `TauCeti.linearDisjoint_of_isGeometricallyReduced_of_transcendental`, and
  `TauCeti.linearDisjoint_of_isGeometricallyReduced_ratFunc`: linear disjointness over a shared
  parameter or `RatFunc` tower.
* `TauCeti.finrank_ratFunc_eq_of_isGeometricallyReduced`: a regular function field over `k(t)`
  keeps its degree `[F · k' : k'(t)] = [F : k(t)]` under any constant extension.

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
  let e : ((F ⊗[k] k') ⊗[k'] AlgebraicClosure k') ≃+* F ⊗[k] AlgebraicClosure k' :=
    (Algebra.TensorProduct.comm k' (F ⊗[k] k') (AlgebraicClosure k')).toRingEquiv.trans <|
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl : AlgebraicClosure k' ≃ₐ[k'] AlgebraicClosure k')
        (Algebra.TensorProduct.commRight k k' F).symm).toRingEquiv.trans <|
      (Algebra.TensorProduct.cancelBaseChange k k' k' (AlgebraicClosure k') F).toRingEquiv.trans
        (Algebra.TensorProduct.comm k (AlgebraicClosure k') F).toRingEquiv
  have : IsDomain ((F ⊗[k] k') ⊗[k'] AlgebraicClosure k') := e.toMulEquiv.isDomain
  have : IsDomain (F' ⊗[k'] AlgebraicClosure k') :=
    isDomain_tensorProduct_of_isLocalization (nonZeroDivisors (F ⊗[k] k')) le_rfl
      F' (AlgebraicClosure k')
  exact algebraicClosure_eq_bot_iff_isIntegrallyClosedIn.mp
    (algebraicClosure_eq_bot_of_isDomain_tensorProduct (AlgebraicClosure k'))

section Parameter

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
  have : IsScalarTower C (C ⊗[k] k') C' :=
    .of_algebraMap_eq fun a ↦ by simp [π₀, RingHom.algebraMap_toAlgebra]
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
      (IntermediateField.linearDisjoint_adjoin_simple_of_transcendental hy₀) ?_
    rintro _ ⟨z, rfl⟩; obtain ⟨w, hw, hwz⟩ := hle₀ z.2; exact ⟨⟨w, hw⟩, Subtype.ext hwz⟩
  have : IsDomain (k'⟮y⟯ ⊗[k⟮x⟯] F) := isDomain_parameter_tensorProduct HC hcomp
  let _ : Field (k'⟮y⟯ ⊗[k⟮x⟯] F) :=
    (Algebra.TensorProduct.isField_of_isAlgebraic k⟮x⟯ k'⟮y⟯ F (.inr inferInstance)).toField
  let ψ : k'⟮y⟯ ⊗[k⟮x⟯] F →ₐ[k'⟮y⟯] F' :=
    Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId k'⟮y⟯ F')
      (IsScalarTower.toAlgHom k⟮x⟯ F F')
  let b := Module.Basis.ofVectorSpace k⟮x⟯ F
  have hfun : algebraMap F F' ∘ b = ψ.toLinearMap ∘ b.baseChange k'⟮y⟯ := by ext i; simp [ψ]
  exact IntermediateField.linearDisjoint_of_transcendental_of_linearIndependent hx' b <| hfun ▸
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

/-- Linear disjointness in a compatible `RatFunc` tower for `F` algebraic over `k(t)` and regular
over `k`. -/
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

end RatFunc

end LinearDisjoint

end TauCeti
