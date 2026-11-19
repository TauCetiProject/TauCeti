/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.LinearDisjoint
public import TauCeti.FieldTheory.Separable.Regular
public import TauCeti.RingTheory.TensorProduct.FractionRing
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.PolynomialAlgebra
import TauCeti.FieldTheory.AlgebraicClosure
import TauCeti.FieldTheory.RatFunc.Transcendental
import TauCeti.RingTheory.TensorProduct.IsDomain

/-!
# Constant extension through the fraction field of a tensor product

Suppose `F ⊗[k] K` is a domain. Its fraction field, with the scalar maps from both
factors, is the linearly disjoint compositum `F · K`. If `F/k` is a one-variable
function field, it is therefore a one-variable function field over `K` too, and
`[Frac(F ⊗[k] K) : K(x)] = [F : k(x)]` for every transcendental parameter `x`.
The extension `K/k` need not be algebraic.

The domain hypothesis is available from
`TauCeti.isDomain_tensorProduct_of_separating` for a separably generated field with
exact constants. We retain the actual fraction-field carrier, rather than asserting
that the tensor product itself is a field. The results also apply to any specified
fraction field with compatible scalar maps.

Conversely, inside any common overfield `F'` of `F` and `k'` over `k`, if `F ⊗[k] k'` is a
domain and some `x ∈ F` with `F / k(x)` algebraic stays transcendental over `k'` in `F'`, then
multiplication `F ⊗[k] k' → F'` is injective (`TauCeti.productMap_injective_of_transcendental`).
Thus `F` and `k'` are linearly disjoint in `F'` (`TauCeti.linearDisjoint_of_transcendental`),
even when `F'` strictly contains `F · k'`. When `F' = F · k'`, `F'` is the fraction field of
`F ⊗[k] k'` (`TauCeti.isFractionRing_of_productMap_injective`,
`TauCeti.fractionRingTensorEquivOfInjective`), and if `F / k` is geometrically reduced with exact
constants then `k'` is the exact constant field of `F'`
(`IsIntegrallyClosedIn.of_constantCompositum_eq_top_of_transcendental`).

## Main definitions

* `TauCeti.fractionRingTensorEquivOfInjective`: the canonical `k`-algebra isomorphism
  `FractionRing (F ⊗[k] k') ≃ₐ[k] F'` when multiplication is injective and `F' = F · k'`.

## Main results

* `TauCeti.IsFunctionField.of_isFractionRing_tensorProduct` and
  `TauCeti.IsFunctionField.fractionRing_tensorProduct`: a fraction field of `F ⊗[k] K` is a
  one-variable function field over `K`.
* `TauCeti.finrank_over_adjoin_simple_eq_of_isFractionRing_tensorProduct`: degree preservation
  over a parameter.
* `TauCeti.productMap_injective_of_transcendental` and
  `TauCeti.isFractionRing_of_productMap_injective`: multiplication embeds `F ⊗[k] k'` into `F'`
  and identifies `F' = F · k'` with its fraction field.
* `TauCeti.linearDisjoint_of_transcendental`: linear disjointness of `F` and `k'` inside any
  common overfield `F'`, without assuming `F' = F · k'`.
* `IsIntegrallyClosedIn.of_constantCompositum_eq_top_of_transcendental`: persistence of exact
  constants across arbitrary constant extensions.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
* S. Lang, *Algebra*, the theory of linearly disjoint field extensions.
-/

public section

open Polynomial
open scoped TensorProduct IntermediateField nonZeroDivisors

namespace TauCeti

section OfFractionRing

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

variable {k F K Q : Type*} [Field k] [Field F] [Field K] [Field Q]
  [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q]
  [Algebra k Q] [Algebra F Q] [Algebra K Q]
  [IsScalarTower k (F ⊗[k] K) Q] [IsScalarTower F (F ⊗[k] K) Q]
  [IsScalarTower K (F ⊗[k] K) Q] [IsScalarTower k F Q] [IsScalarTower k K Q]
  [IsFractionRing (F ⊗[k] K) Q]

/-- A fraction field of a domain tensor product is a one-variable function field
over the enlarged constants. -/
theorem IsFunctionField.of_isFractionRing_tensorProduct (hF : IsFunctionField k F) :
    IsFunctionField K Q :=
  hF.of_constantCompositum_eq_top_of_linearDisjoint
    (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (by
      rw [constantCompositum_def]
      exact adjoin_range_right_eq_top_of_isFractionRing_tensorProduct (k := k))

/-- Tensor-fraction-field extension of constants preserves the degree over a parameter.
Neither the constants nor the relative extension need be separable. -/
theorem finrank_over_adjoin_simple_eq_of_isFractionRing_tensorProduct (x : F)
    [FiniteDimensional k⟮x⟯ F] :
    Module.finrank K⟮algebraMap F Q x⟯ Q = Module.finrank k⟮x⟯ F :=
  finrank_over_adjoin_simple_eq_of_linearDisjoint
    (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (by
      rw [constantCompositum_def]
      exact adjoin_range_right_eq_top_of_isFractionRing_tensorProduct (k := k)) x

/-- If `F/k` is a geometrically reduced one-variable function field with exact constants,
then the fraction field of `F ⊗[k] K` is a one-variable function field over `K`.
The enlarged constant field may be transcendental over the original one. -/
theorem IsFunctionField.fractionRing_tensorProduct (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F] :
    letI := isDomain_tensorProduct_of_isGeometricallyReduced hex K
    IsFunctionField K (FractionRing (F ⊗[k] K)) := by
  have := isDomain_tensorProduct_of_isGeometricallyReduced hex K
  exact hF.of_isFractionRing_tensorProduct

end OfFractionRing

section TensorFractionField

variable {k F k' F' : Type*} [Field k] [Field F] [Field k'] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k F'] [Algebra F F'] [Algebra k' F']
  [IsScalarTower k F F'] [IsScalarTower k k' F']

/-- Multiplication `k(x) ⊗[k] k' → F'` is injective whenever the image of `x` in `F'` is
transcendental over `k'`: clearing denominators in `k[X]` reduces to `k[X] ⊗[k] k' ≃ k'[X] → F'`. -/
private theorem productMap_adjoin_injective_of_transcendental {x : F}
    (hx' : Transcendental k' (algebraMap F F' x)) :
    Function.Injective (Algebra.TensorProduct.productMap
      ((IsScalarTower.toAlgHom k F F').comp k⟮x⟯.val) (IsScalarTower.toAlgHom k k' F')) := by
  have hx : Transcendental k x := fun halg ↦ by
    have halg' : IsAlgebraic k (algebraMap F F' x) := halg.algHom (IsScalarTower.toAlgHom k F F')
    exact hx' (halg'.extendScalars (algebraMap k k').injective)
  let ψ : k[X] →ₐ[k] k⟮x⟯ := aeval (IntermediateField.AdjoinSimple.gen k x)
  have hψinj : Function.Injective ψ := by
    have hcomp : k⟮x⟯.val.comp ψ = aeval x := by ext; simp [ψ]
    exact Function.Injective.of_comp (f := k⟮x⟯.val)
      (by rw [← AlgHom.coe_comp, hcomp]; exact transcendental_iff_injective.mp hx)
  let π₀ : k[X] ⊗[k] k' →ₐ[k] F' := Algebra.TensorProduct.productMap
    (((IsScalarTower.toAlgHom k F F').comp k⟮x⟯.val).comp ψ) (IsScalarTower.toAlgHom k k' F')
  have hπ₀ : Function.Injective π₀ := by
    let e : k[X] ⊗[k] k' ≃ₐ[k] k'[X] :=
      (Algebra.TensorProduct.comm k k[X] k').trans (polyEquivTensor k k').symm
    have hcomp : π₀ = ((aeval (algebraMap F F' x) : k'[X] →ₐ[k'] F').restrictScalars k).comp
        e.toAlgHom := by
      apply Algebra.TensorProduct.ext
      · ext
        simp [π₀, ψ, e, polyEquivTensor_symm_apply_tmul_eq_smul]
      · ext c
        simp [π₀, e, polyEquivTensor_symm_apply_tmul_eq_smul, Algebra.smul_def]
    have hcoe : ⇑π₀ = ⇑(aeval (algebraMap F F' x) : k'[X] →ₐ[k'] F') ∘ ⇑e := by
      rw [hcomp]; rfl
    rw [hcoe]
    exact (transcendental_iff_injective.mp hx').comp e.injective
  let ρ : k[X] ⊗[k] k' →ₐ[k] k⟮x⟯ ⊗[k] k' :=
    Algebra.TensorProduct.map ψ (AlgHom.id k k')
  have hclear (u : k⟮x⟯ ⊗[k] k') :
      ∃ d : k[X], d ≠ 0 ∧ ∃ v : k[X] ⊗[k] k', (ψ d ⊗ₜ[k] (1 : k')) * u = ρ v := by
    refine TensorProduct.inductionOn
      (motive := fun u ↦ ∃ d : k[X], d ≠ 0 ∧ ∃ v : k[X] ⊗[k] k', (ψ d ⊗ₜ[k] (1 : k')) * u = ρ v)
      u (fun z c ↦ ?_) (fun u₁ u₂ ⟨d₁, hd₁, v₁, hv₁⟩ ⟨d₂, hd₂, v₂, hv₂⟩ ↦ ?_)
    · let e := RatFunc.algEquivOfTranscendental x hx
      obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (M := k[X]⁰) (S := RatFunc k) (e.symm z)
      have heval (r : k[X]) : e (algebraMap k[X] (RatFunc k) r) = ψ r :=
        RatFunc.algEquivOfTranscendental_algebraMap x hx r
      have hz : ψ q * z = ψ p := by
        simpa [map_mul, heval, mul_comm] using congr_arg e hpq
      refine ⟨q, mem_nonZeroDivisors_iff_ne_zero.mp q.2, p ⊗ₜ[k] c, ?_⟩
      simp [ρ, hz]
    · refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, (d₂ ⊗ₜ[k] 1) * v₁ + (d₁ ⊗ₜ[k] 1) * v₂, ?_⟩
      have h1 : (ψ (d₁ * d₂) ⊗ₜ[k] (1 : k')) * u₁ = ρ ((d₂ ⊗ₜ[k] 1) * v₁) := by
        calc (ψ (d₁ * d₂) ⊗ₜ[k] (1 : k')) * u₁
            = (ψ d₂ ⊗ₜ[k] 1) * ((ψ d₁ ⊗ₜ[k] 1) * u₁) := by
                rw [map_mul, mul_comm (ψ d₁) (ψ d₂), ← mul_assoc,
                  Algebra.TensorProduct.tmul_mul_tmul, one_mul]
          _ = ρ ((d₂ ⊗ₜ[k] 1) * v₁) := by rw [hv₁, map_mul]; simp [ρ]
      have h2 : (ψ (d₁ * d₂) ⊗ₜ[k] (1 : k')) * u₂ = ρ ((d₁ ⊗ₜ[k] 1) * v₂) := by
        calc (ψ (d₁ * d₂) ⊗ₜ[k] (1 : k')) * u₂
            = (ψ d₁ ⊗ₜ[k] 1) * ((ψ d₂ ⊗ₜ[k] 1) * u₂) := by
                rw [map_mul, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
          _ = ρ ((d₁ ⊗ₜ[k] 1) * v₂) := by rw [hv₂, map_mul]; simp [ρ]
      rw [mul_add, h1, h2, map_add]
  set π₁ := Algebra.TensorProduct.productMap
    ((IsScalarTower.toAlgHom k F F').comp k⟮x⟯.val) (IsScalarTower.toAlgHom k k' F')
  refine (injective_iff_map_eq_zero π₁).mpr fun u hu ↦ ?_
  obtain ⟨d, hd, v, hv⟩ := hclear u
  have hcomp : π₁.comp ρ = π₀ := by ext <;> simp [π₁, π₀, ρ]
  have hv0 : π₀ v = 0 := by
    have := congr_arg π₁ hv
    rw [map_mul, hu, mul_zero] at this
    exact (congr($hcomp v)).symm.trans this.symm
  rw [(injective_iff_map_eq_zero π₀).mp hπ₀ v hv0, map_zero] at hv
  have hd0 : ψ d ≠ 0 := fun h0 ↦ hd ((injective_iff_map_eq_zero ψ).mp hψinj d h0)
  calc u = ((ψ d)⁻¹ ⊗ₜ[k] (1 : k') * (ψ d ⊗ₜ[k] 1)) * u := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ hd0, mul_one,
            ← Algebra.TensorProduct.one_def, one_mul]
    _ = ((ψ d)⁻¹ ⊗ₜ[k] (1 : k')) * ((ψ d ⊗ₜ[k] 1) * u) := mul_assoc _ _ _
    _ = 0 := by rw [hv, mul_zero]

/-- **Injectivity of multiplication on `F ⊗[k] k'` for transcendental constant extensions.** If
`F ⊗[k] k'` is a domain and some `x ∈ F` with `F / k(x)` algebraic stays transcendental over `k'`
in `F'`, then multiplication `F ⊗[k] k' → F'` is injective. -/
theorem productMap_injective_of_transcendental [IsDomain (F ⊗[k] k')] {x : F}
    [Algebra.IsAlgebraic k⟮x⟯ F] (hx' : Transcendental k' (algebraMap F F' x)) :
    Function.Injective (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F')) := by
  let π := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
    (IsScalarTower.toAlgHom k k' F')
  let ρ : k⟮x⟯ ⊗[k] k' →ₐ[k] F ⊗[k] k' :=
    Algebra.TensorProduct.map k⟮x⟯.val (AlgHom.id k k')
  have hπ₁ : Function.Injective (π.comp ρ) := by
    have hcomp : π.comp ρ = Algebra.TensorProduct.productMap
        ((IsScalarTower.toAlgHom k F F').comp k⟮x⟯.val) (IsScalarTower.toAlgHom k k' F') := by
      ext <;> simp [π, ρ]
    rw [hcomp]
    exact productMap_adjoin_injective_of_transcendental hx'
  let _ : Algebra (k⟮x⟯ ⊗[k] k') (F ⊗[k] k') := ρ.toRingHom.toAlgebra
  have hInt (z : F ⊗[k] k') : IsIntegral (k⟮x⟯ ⊗[k] k') z := by
    have hz : z ∈ (⊤ : Subring (F ⊗[k] k')) := trivial
    rw [← Algebra.TensorProduct.closure_range_union_range_eq_top k F k'] at hz
    refine Subring.closure_induction (fun y hy ↦ ?_) isIntegral_zero isIntegral_one
      (fun _ _ _ _ ↦ IsIntegral.add) (fun _ _ ↦ IsIntegral.neg)
      (fun _ _ _ _ ↦ IsIntegral.mul) hz
    rcases hy with ⟨f, rfl⟩ | ⟨c, rfl⟩
    · exact (Algebra.IsIntegral.isIntegral (R := k⟮x⟯) f).map_of_comp_eq
        (Algebra.TensorProduct.includeLeft : k⟮x⟯ →ₐ[k] k⟮x⟯ ⊗[k] k').toRingHom
        (Algebra.TensorProduct.includeLeft : F →ₐ[k] F ⊗[k] k').toRingHom
        (by ext y; simp [RingHom.algebraMap_toAlgebra, ρ])
    · simpa [RingHom.algebraMap_toAlgebra, ρ] using
        (isIntegral_algebraMap (R := k⟮x⟯ ⊗[k] k') (A := F ⊗[k] k') (x := 1 ⊗ₜ[k] c))
  have : Algebra.IsIntegral (k⟮x⟯ ⊗[k] k') (F ⊗[k] k') := ⟨hInt⟩
  have : Nontrivial (k⟮x⟯ ⊗[k] k') := ρ.toRingHom.domain_nontrivial
  refine (RingHom.injective_iff_ker_eq_bot π.toRingHom).mpr <|
    Ideal.eq_bot_of_under_eq_bot (R := k⟮x⟯ ⊗[k] k') (I := RingHom.ker π.toRingHom) ?_
  refine eq_bot_iff.mpr fun y hy ↦ ?_
  rw [Ideal.mem_under, RingHom.mem_ker, RingHom.algebraMap_toAlgebra] at hy
  exact Ideal.mem_bot.mpr <| (injective_iff_map_eq_zero (π.comp ρ)).mp hπ₁ y hy

/-- **Fraction-field presentation of an arbitrary constant extension.** If `F ⊗[k] k'` is a domain,
multiplication `F ⊗[k] k' → F'` is injective, and `F' = F · k'`, then `F'` is the fraction field
of `F ⊗[k] k'` along multiplication. -/
theorem isFractionRing_of_productMap_injective [IsDomain (F ⊗[k] k')]
    (hπ : Function.Injective (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F')))
    (hcomp : constantCompositum F k' F' = ⊤) :
    letI := (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F')).toRingHom.toAlgebra
    IsFractionRing (F ⊗[k] k') F' := by
  let π := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
    (IsScalarTower.toAlgHom k k' F')
  let _ : Algebra (F ⊗[k] k') F' := π.toRingHom.toAlgebra
  let i : FractionRing (F ⊗[k] k') →ₐ[F ⊗[k] k'] F' :=
    IsFractionRing.liftAlgHom (K := FractionRing (F ⊗[k] k')) (g := Algebra.ofId (F ⊗[k] k') F') hπ
  have hs : π.toRingHom.range =
      Subring.closure (Set.range (algebraMap F F') ∪ Set.range (algebraMap k' F')) := by
    rw [RingHom.range_eq_map, ← Algebra.TensorProduct.closure_range_union_range_eq_top k F k',
      RingHom.map_closure, Set.image_union, ← Set.range_comp, ← Set.range_comp]
    congr 2 <;> ext <;> simp [π]
  have hrange := IsFractionRing.ringHom_fieldRange_eq_of_comp_eq_of_range_eq
    (g := π.toRingHom) (f := i.toRingHom)
    (RingHom.ext fun z ↦ IsFractionRing.lift_algebraMap hπ z) hs
  have htop : (constantCompositum F k' F').toSubfield = ⊤ := by
    rw [hcomp, IntermediateField.top_toSubfield]
  rw [constantCompositum_def, IntermediateField.adjoin_toSubfield] at htop
  have hbij : Function.Bijective i := ⟨i.toRingHom.injective,
    RingHom.fieldRange_eq_top_iff.mp (hrange.trans htop)⟩
  exact IsFractionRing.of_algEquiv (AlgEquiv.ofBijective i hbij)

/-- **Canonical isomorphism `FractionRing (F ⊗[k] k') ≃ₐ[k] F'`** for an arbitrary constant
extension with `F ⊗[k] k'` a domain and multiplication injective. -/
noncomputable def fractionRingTensorEquivOfInjective [IsDomain (F ⊗[k] k')]
    (hπ : Function.Injective (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F')))
    (hcomp : constantCompositum F k' F' = ⊤) :
    FractionRing (F ⊗[k] k') ≃ₐ[k] F' := by
  let _ : Algebra (F ⊗[k] k') F' := (Algebra.TensorProduct.productMap
    (IsScalarTower.toAlgHom k F F') (IsScalarTower.toAlgHom k k' F')).toRingHom.toAlgebra
  have : IsScalarTower k (F ⊗[k] k') F' := .of_algebraMap_eq fun c ↦ by
    simp [RingHom.algebraMap_toAlgebra]
  have := isFractionRing_of_productMap_injective hπ hcomp
  exact (IsLocalization.algEquiv (F ⊗[k] k')⁰ (FractionRing (F ⊗[k] k')) F').restrictScalars k

@[simp]
theorem fractionRingTensorEquivOfInjective_algebraMap_tmul [IsDomain (F ⊗[k] k')]
    (hπ : Function.Injective (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F')))
    (hcomp : constantCompositum F k' F' = ⊤) (f : F) (c : k') :
    fractionRingTensorEquivOfInjective hπ hcomp
      (algebraMap (F ⊗[k] k') (FractionRing (F ⊗[k] k')) (f ⊗ₜ[k] c)) =
      algebraMap F F' f * algebraMap k' F' c := by
  let _ : Algebra (F ⊗[k] k') F' := (Algebra.TensorProduct.productMap
    (IsScalarTower.toAlgHom k F F') (IsScalarTower.toAlgHom k k' F')).toRingHom.toAlgebra
  have : IsScalarTower k (F ⊗[k] k') F' := .of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra]
  have := isFractionRing_of_productMap_injective hπ hcomp
  rw [fractionRingTensorEquivOfInjective, AlgEquiv.coe_restrictScalars, AlgEquiv.commutes]
  simp [RingHom.algebraMap_toAlgebra]

/-- **Linear disjointness of `F` and `k'` inside any common overfield `F'`** once a parameter
`x ∈ F` with `F / k(x)` algebraic stays transcendental over `k'` and `F ⊗[k] k'` is a domain. -/
theorem linearDisjoint_of_transcendental [IsDomain (F ⊗[k] k')]
    {x : F} [Algebra.IsAlgebraic k⟮x⟯ F] (hx' : Transcendental k' (algebraMap F F' x)) :
    (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F := by
  let π := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
    (IsScalarTower.toAlgHom k k' F')
  have hπ : Function.Injective π := productMap_injective_of_transcendental (k := k) hx'
  have H := (Subalgebra.LinearDisjoint.include_range k F k').map π hπ
  rw [IntermediateField.linearDisjoint_iff, AlgHom.fieldRange_toSubalgebra]
  have hleft : π.comp Algebra.TensorProduct.includeLeft = IsScalarTower.toAlgHom k F F' := by
    ext f
    simp [π]
  have hright : π.comp Algebra.TensorProduct.includeRight = IsScalarTower.toAlgHom k k' F' := by
    ext c
    simp [π]
  simpa only [← AlgHom.range_comp, hleft, hright] using H.symm

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower in
/-- **Exactness of constants under arbitrary constant field extension.** If `F / k` is
geometrically reduced with exact constants, `F' = F · k'`, and some `x ∈ F` with `F / k(x)`
algebraic stays transcendental over `k'`, then `k'` is integrally closed in `F'`. -/
theorem _root_.IsIntegrallyClosedIn.of_constantCompositum_eq_top_of_transcendental
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F] {x : F}
    [Algebra.IsAlgebraic k⟮x⟯ F] (hx' : Transcendental k' (algebraMap F F' x))
    (hcomp : constantCompositum F k' F' = ⊤) :
    IsIntegrallyClosedIn k' F' := by
  have : IsDomain (F ⊗[k] k') := isDomain_tensorProduct_of_isGeometricallyReduced hex k'
  let _ : Algebra (F ⊗[k] k') F' := (Algebra.TensorProduct.productMap
    (IsScalarTower.toAlgHom k F F') (IsScalarTower.toAlgHom k k' F')).toRingHom.toAlgebra
  have : IsScalarTower k' (F ⊗[k] k') F' := .of_algebraMap_eq fun c ↦ by
    simp [RingHom.algebraMap_toAlgebra]
  have := isFractionRing_of_productMap_injective
    (productMap_injective_of_transcendental (k := k) hx') hcomp
  let L := AlgebraicClosure k'
  have : IsDomain (F ⊗[k] L) := isDomain_tensorProduct_of_isGeometricallyReduced hex L
  have : IsDomain (L ⊗[k] F) := (Algebra.TensorProduct.comm k L F).toMulEquiv.isDomain
  have : IsDomain (L ⊗[k'] (k' ⊗[k] F)) :=
    (Algebra.TensorProduct.cancelBaseChange k k' k' L F).toMulEquiv.isDomain
  have : IsDomain ((k' ⊗[k] F) ⊗[k'] L) :=
    (Algebra.TensorProduct.comm k' (k' ⊗[k] F) L).toMulEquiv.isDomain
  let e : F ⊗[k] k' ≃ₐ[k'] k' ⊗[k] F :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm k F k').toRingEquiv) fun _ ↦ rfl
  have : IsDomain ((F ⊗[k] k') ⊗[k'] L) :=
    (Algebra.TensorProduct.congr e (AlgEquiv.refl : L ≃ₐ[k'] L)).toMulEquiv.isDomain
  have : IsDomain (F' ⊗[k'] L) :=
    isDomain_tensorProduct_of_isLocalization (F ⊗[k] k')⁰ le_rfl F' L
  exact algebraicClosure_eq_bot_iff_isIntegrallyClosedIn.mp
    (algebraicClosure_eq_bot_of_isDomain_tensorProduct L)

end TensorFractionField

end TauCeti
