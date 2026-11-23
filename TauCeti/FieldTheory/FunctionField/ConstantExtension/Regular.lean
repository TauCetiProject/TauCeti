/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.FractionField
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.TensorProduct
public import TauCeti.FieldTheory.Separable.Regular
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.KrullDimension.Zero
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
field extension `k' / k`. When `k' / k` is algebraic, multiplication `F ⊗[k] k' → F · k'` is an
isomorphism onto the constant field extension, discharging the domain hypothesis of
`TauCeti.productMap_bijective_of_constantCompositum_eq_top`. For a function field `F`, this says
that the function field of the curve after an algebraic extension of the constants is
`F ⊗[k] k'`.

Because `F · k'` is therefore the fraction field of `F ⊗[k] k'`, scalar stability of regular
extensions (`TauCeti.isIntegrallyClosedIn_right_of_isFractionRing_tensorProduct`) implies that
`k'` is again the exact constant field of `F · k'`, even when `k' / k` is inseparable. Compare
`IsIntegrallyClosedIn.of_constantCompositum_eq_top`, which drops geometric reducedness of `F / k`
at the cost of requiring `k' / k` to be separable. Geometric reducedness of `F · k'` over `k'`
holds for every geometrically reduced `F / k` and algebraic `k' / k` without assuming exact
constants, since `F ⊗[k] k'` is reduced, integral over the field `F` (hence zero-dimensional), and
maps onto `F · k'`, identifying `F · k'` with the localization of `F ⊗[k] k'` at the kernel.

For arbitrary extensions `k' / k`, exactness of constants ascends along any linearly disjoint
compositum `F · k'`, and when `F` is algebraic over a shared transcendental parameter (or over
`k(t)`), regularity of `F / k` supplies linear disjointness and degree preservation over `k'(t)`.

## Main results

* `TauCeti.productMap_bijective_of_isGeometricallyReduced` and
  `TauCeti.productMap_bijective_of_separating`: for `F` regular over `k`, multiplication
  `F ⊗[k] k' → F · k'` is an isomorphism for every algebraic extension `k' / k`.
* `TauCeti.isDomain_tensorProduct_of_constantCompositum_eq_top_of_isGeometricallyReduced`: for any
  algebraic `k' / k` and domain `k'`-algebra `A`, `(F · k') ⊗[k'] A` is a domain.
* `TauCeti.isIntegrallyClosedIn_of_constantCompositum_eq_top_of_isGeometricallyReduced`: `k'` is
  exact in `F · k'` when `F / k` is regular, whether or not `k' / k` is separable.
* `TauCeti.isGeometricallyReduced_of_constantCompositum_eq_top_of_isGeometricallyReduced`: `F · k'`
  is geometrically reduced over `k'` whenever `F / k` is geometrically reduced and `k' / k` is
  algebraic, with no exact-constants or separability hypothesis.
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

section Stability

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

/-- **An algebraic constant field extension of a regular field stays regular.** If `F / k` is
geometrically reduced with exact constants and `F' = F · k'` for an algebraic extension `k' / k`
(separable or inseparable), then `F' ⊗[k'] A` is a domain for every domain `k'`-algebra `A`. -/
theorem isDomain_tensorProduct_of_constantCompositum_eq_top_of_isGeometricallyReduced
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    (h : constantCompositum F k' F' = ⊤) (A : Type*) [CommRing A] [IsDomain A] [Algebra k' A] :
    IsDomain (F' ⊗[k'] A) := by
  have := isDomain_tensorProduct_of_isGeometricallyReduced hex k'
  let _ : Field (F ⊗[k] k') :=
    (Algebra.TensorProduct.isField_of_isAlgebraic k F k' (.inr inferInstance)).toField
  set π := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
    (IsScalarTower.toAlgHom k k' F')
  let _ : Algebra (F ⊗[k] k') F' := π.toRingHom.toAlgebra
  have : IsScalarTower k' (F ⊗[k] k') F' := .of_algebraMap_eq fun c ↦ by
    simp [RingHom.algebraMap_toAlgebra, π]
  have hπ : Function.Bijective π :=
    productMap_bijective_of_isGeometricallyReduced (k := k) hex h
  have : IsFractionRing (F ⊗[k] k') F' :=
    .of_algEquiv (AlgEquiv.ofRingEquiv
      (f := RingEquiv.ofBijective π.toRingHom
        (by rwa [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]))
      fun x ↦ by simp [RingHom.algebraMap_toAlgebra])
  exact isDomain_tensorProduct_right_of_isFractionRing_tensorProduct (K := k') (Q := F') hex A

/-- **Exact constants after any algebraic constant extension of a regular field.** If `F / k` is
geometrically reduced with exact constants and `F' = F · k'` for an algebraic extension `k' / k`
(separable or inseparable), then `k'` is the exact constant field of `F'`. -/
theorem isIntegrallyClosedIn_of_constantCompositum_eq_top_of_isGeometricallyReduced
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    (h : constantCompositum F k' F' = ⊤) :
    IsIntegrallyClosedIn k' F' := by
  have := isDomain_tensorProduct_of_constantCompositum_eq_top_of_isGeometricallyReduced
    hex h (AlgebraicClosure k')
  exact isIntegrallyClosedIn_of_isDomain_tensorProduct (k := k') (A := F') (AlgebraicClosure k')

/-- **Geometric reducedness after any algebraic constant extension.** If `F / k` is geometrically
reduced and `F' = F · k'` for an algebraic extension `k' / k` (separable or inseparable), then `F'`
is geometrically reduced over `k'`, without assuming exact constants. -/
theorem isGeometricallyReduced_of_constantCompositum_eq_top_of_isGeometricallyReduced
    [Algebra.IsGeometricallyReduced k F] (h : constantCompositum F k' F' = ⊤) :
    Algebra.IsGeometricallyReduced k' F' := by
  have : Algebra.IsGeometricallyReduced k' (F ⊗[k] k') :=
    isGeometricallyReduced_tensorProduct_right k'
  have : Algebra.IsIntegral k k' := Algebra.IsAlgebraic.isIntegral
  have : Ring.KrullDimLE 0 (F ⊗[k] k') := Ring.KrullDimLE.mk₀ fun p hp ↦
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := F) p (by
      rw [Ideal.eq_bot_of_prime (p.under F)]
      exact Ideal.bot_isMaximal)
  let π₀ := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
    (IsScalarTower.toAlgHom k k' F')
  let π : F ⊗[k] k' →ₐ[k'] F' :=
    { toRingHom := π₀.toRingHom
      commutes' c := by simp [π₀, Algebra.TensorProduct.right_algebraMap_apply] }
  have hπ_surj : Function.Surjective π := fun y ↦ by
    obtain ⟨x, hx⟩ := productMap_surjective_of_constantCompositum_eq_top (k := k) h y
    exact ⟨x, by simpa [π, π₀] using hx⟩
  let m : Ideal (F ⊗[k] k') := RingHom.ker π.toRingHom
  have hm_prime : m.IsPrime := RingHom.ker_isPrime π.toRingHom
  have hm_min : m ∈ minimalPrimes (F ⊗[k] k') := by
    rw [Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isPrime]
    exact hm_prime
  let L := Localization.AtPrime m
  have : Algebra.IsGeometricallyReduced k' L :=
    isGeometricallyReduced_of_isLocalization m.primeCompl L
  have : IsReduced L := Algebra.isReduced_of_isGeometricallyReduced (k := k') (A := L)
  have : Ring.KrullDimLE 0 L := Ring.KrullDimLE.of_isLocalization m hm_min L
  let _ : Field L := Ring.KrullDimLE.isField_of_isReduced.toField
  let f : L →ₐ[k'] F' :=
    IsLocalization.liftAlgHom (M := m.primeCompl) (f := π) fun y ↦
      isUnit_iff_ne_zero.mpr (by simpa [m] using y.property)
  have hf_inj : Function.Injective f := by
    rw [← AlgHom.coe_toRingHom]
    exact (f : L →+* F').injective
  have hf_surj : Function.Surjective f := fun y ↦ by
    obtain ⟨x, rfl⟩ := hπ_surj y
    exact ⟨algebraMap (F ⊗[k] k') L x, by simp [f]⟩
  exact Algebra.IsGeometricallyReduced.of_algEquiv (AlgEquiv.ofBijective f ⟨hf_inj, hf_surj⟩)

end Stability

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

/-- **Linear disjointness over a shared parameter when `F ⊗[k] k'` is a domain.** -/
theorem linearDisjoint_of_transcendental_of_isDomain {x : F}
    (hx' : Transcendental k' (algebraMap F F' x)) [Algebra.IsAlgebraic k⟮x⟯ F]
    [IsDomain (F ⊗[k] k')] : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F := by
  set y := algebraMap F F' x
  have hle : k⟮x⟯.map (IsScalarTower.toAlgHom k F F') ≤ (k'⟮y⟯).restrictScalars k := by
    simpa [IntermediateField.adjoin_map] using IntermediateField.mem_adjoin_simple_self k' y
  let ι : k⟮x⟯ →ₐ[k] k'⟮y⟯ :=
    ((IsScalarTower.toAlgHom k F F').comp k⟮x⟯.val).codRestrict
      ((k'⟮y⟯).restrictScalars k).toSubalgebra fun z ↦ hle ⟨z, z.property, rfl⟩
  let _ : Algebra k⟮x⟯ k'⟮y⟯ := ι.toRingHom.toAlgebra
  have : IsScalarTower k k⟮x⟯ k'⟮y⟯ := .of_algebraMap_eq fun c ↦ (ι.commutes c).symm
  have : IsScalarTower k⟮x⟯ k'⟮y⟯ F' := .of_algebraMap_eq' rfl
  let x₀ : k⟮x⟯ := ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩
  let y₀ : k'⟮y⟯ := ι x₀
  have hy₀ : Transcendental k' y₀ := (transcendental_algebraMap_iff (k'⟮y⟯).val.injective).mp hx'
  have hcomp : constantCompositum k⟮x⟯ k' k'⟮y⟯ = ⊤ := eq_top_iff.mpr fun z _ ↦ by
    have hE : k'⟮y₀⟯ ≤ (constantCompositum k⟮x⟯ k' k'⟮y⟯).toSubfield.toIntermediateField
        (algebraMap_mem_constantCompositum _ _ _) :=
      IntermediateField.adjoin_simple_le_iff.mpr
        ((constantCompositum k⟮x⟯ k' k'⟮y⟯).algebraMap_mem x₀)
    obtain ⟨w, hw, hwz⟩ : (z : F') ∈ (k'⟮y₀⟯).map (k'⟮y⟯).val := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]; exact z.property
    exact hE (Subtype.ext hwz.symm ▸ hw)
  have HC : (IsScalarTower.toAlgHom k k' k'⟮y⟯).fieldRange.LinearDisjoint k⟮x⟯ := by
    have hle₀ : k⟮x⟯ ≤ (k⟮y₀⟯.map ((k'⟮y⟯).val.restrictScalars k)).comap
        (IsScalarTower.toAlgHom k F F') :=
      IntermediateField.adjoin_simple_le_iff.mpr
        ⟨y₀, IntermediateField.mem_adjoin_simple_self k y₀, rfl⟩
    rw [IntermediateField.linearDisjoint_iff]
    refine Subalgebra.LinearDisjoint.of_le_right_of_flat
      (IntermediateField.linearDisjoint_adjoin_simple_of_transcendental hy₀) ?_
    rintro _ ⟨z, rfl⟩; obtain ⟨w, hw, hwz⟩ := hle₀ z.property; exact ⟨⟨w, hw⟩, Subtype.ext hwz⟩
  let π₀ := Algebra.TensorProduct.productMap
    (IsScalarTower.toAlgHom k k⟮x⟯ k'⟮y⟯) (IsScalarTower.toAlgHom k k' k'⟮y⟯)
  let _ : Algebra (k⟮x⟯ ⊗[k] k') k'⟮y⟯ := π₀.toRingHom.toAlgebra
  have : IsScalarTower k⟮x⟯ (k⟮x⟯ ⊗[k] k') k'⟮y⟯ :=
    .of_algebraMap_eq (R := k⟮x⟯) (S := k⟮x⟯ ⊗[k] k') (A := k'⟮y⟯) fun _ ↦ by
      simp [π₀, RingHom.algebraMap_toAlgebra]
  have : IsFractionRing _ _ := isFractionRing_tensorProduct_of_linearDisjoint HC hcomp
  have := isDomain_tensorProduct_of_isLocalization_tensorProduct_left
    (nonZeroDivisors (k⟮x⟯ ⊗[k] k')) le_rfl k'⟮y⟯ F
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
