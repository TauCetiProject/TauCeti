/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.TamelyRamified
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.Algebra.Algebra.NatCast
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import TauCeti.FieldTheory.IntermediateField.ScalarTower
import TauCeti.RingTheory.DiscreteValuationRing.BaseChange.Unramified
import TauCeti.RingTheory.DiscreteValuationRing.Kummer.Basic
import TauCeti.RingTheory.DiscreteValuationRing.Kummer.Characterization
import TauCeti.RingTheory.DiscreteValuationRing.Kummer.Unit
import TauCeti.RingTheory.Etale.IntegralClosure
import TauCeti.RingTheory.IntegralClosure.TensorProduct
import TauCeti.RingTheory.Localization.Integral
import TauCeti.RingTheory.Unramified.Field

/-!
# Base change of tamely ramified extensions of a discrete valuation ring

Let `A → A'` be an extension of discrete valuation rings with fraction fields `K ⊆ K'`, and let
`L / K` be a finite separable extension. If `L` is tamely ramified with respect to `A`, then every
factor field `L'` of `K' ⊗[K] L` is tamely ramified with respect to `A'` (Stacks, Lemma 15.116.9
(0EXY), the tame half).

Write the image of a uniformizer `π` of `A` in `A'` as `u' ϖ' ^ m` for a unit `u'` and a uniformizer
`ϖ'` of `A'`, and let `e₀` be the common tame exponent of `L` over `A`
(`TauCeti.Algebra.IsTamelyRamifiedWRT.exists_ramificationIdx_dvd`). Over an algebraic closure of a
factor field `L'` of `K' ⊗[K] L`, extracting `e₀`-th roots `β'` of `ϖ'` and `γ'` of `u'` gives an
`e₀`-th root `α' = γ' β' ^ m` of `π`. Then `L(α') / K(α')` is unramified over `A[α']`
(`TauCeti.Algebra.IsTamelyRamifiedWRT.isUnramifiedWRT_adjoin_of_pow_eq_of_irreducible`), while
`K'(β')(γ') / K'(β')` is unramified over `A'[β']` because `u'` and `e₀` are units in `A'[β']`
(`TauCeti.IsDiscreteValuationRing.isUnramifiedWRT_adjoin_of_pow_eq_of_isUnit`). Tensoring the two
finite étale integral closures exhibits `L'(β', γ')` as a field quotient of the generic fibre of a
finite étale `A'[β']`-algebra, hence unramified over `A'[β']`, which forces `L'` to be tamely
ramified with respect to `A'`. As in the unramified case, `A → A'` need not be a local
homomorphism.

## Main results

* `TauCeti.Algebra.IsTamelyRamifiedWRT.baseChange`: tamely ramified extensions of a discrete
  valuation ring are stable under base change (Stacks, Lemma 15.116.9, tame case).

## References

* [Stacks Project, Lemma 15.116.7](https://stacks.math.columbia.edu/tag/0EXW).
* [Stacks Project, Lemma 15.116.9](https://stacks.math.columbia.edu/tag/0EXY).
-/

public section

universe v

open scoped TensorProduct
open _root_.IntermediateField IsLocalRing

namespace TauCeti.Algebra

section BaseChange

/-- Surjectivity of the generic-fibre map onto the double root extension `L'(β', γ')` inside `Ω'`,
factored out from `isUnramifiedWRT_adjoin_roots_in_overfield`. -/
private theorem surjective_compositum_lift
    {K L K' L' Ω' K₁ L₁ A₁ : Type*}
    [Field K] [Field L] [Algebra K L] [Field K'] [Algebra K K']
    [Field L'] [Algebra K' L'] [Algebra L L']
    [Field Ω'] [Algebra L' Ω'] [Algebra K' Ω'] [Algebra L Ω']
    [IsScalarTower K' L' Ω'] [IsScalarTower L L' Ω']
    [CommRing A₁] [Field K₁] [Algebra A₁ K₁] [IsFractionRing A₁ K₁]
    [Field L₁] [Algebra A₁ L₁] [Algebra K₁ L₁] [IsScalarTower A₁ K₁ L₁]
    [Algebra.IsAlgebraic K₁ L₁] [Algebra L L₁]
    {β' γ' : Ω'}
    [Algebra K'⟮β'⟯ (IntermediateField.adjoin L' ({β', γ'} : Set Ω'))]
    (φ : K' ⊗[K] L →ₐ[K'] L') (hφ : Function.Surjective φ)
    (hφL : ∀ l : L, φ (1 ⊗ₜ[K] l) = algebraMap L L' l)
    (hβ'_int : IsIntegral K' β') (hγ'_int : IsIntegral K' γ')
    (ιK : K₁ →+* (K'⟮β'⟯)⟮γ'⟯)
    (ιL₁ : L₁ →+* IntermediateField.adjoin L' ({β', γ'} : Set Ω'))
    (hιL : ∀ l : L, (ιL₁ (algebraMap L L₁ l) : Ω') = algebraMap L Ω' l)
    (hιsmul : ∀ (c : K₁) (x : L₁), (ιL₁ (c • x) : Ω') = (ιK c : Ω') * (ιL₁ x : Ω'))
    (hιK'₁ : ∀ x : K'⟮β'⟯,
      (algebraMap K'⟮β'⟯ (IntermediateField.adjoin L' ({β', γ'} : Set Ω')) x : Ω') = x)
    (ιK'₂ : (K'⟮β'⟯)⟮γ'⟯ →ₐ[K'⟮β'⟯] IntermediateField.adjoin L' ({β', γ'} : Set Ω'))
    (hιK'₂ : ∀ x : (K'⟮β'⟯)⟮γ'⟯, (ιK'₂ x : Ω') = x)
    {T : Type*} [CommRing T]
    (χ : T →+* IntermediateField.adjoin L' ({β', γ'} : Set Ω'))
    (hK'₁_R : ∀ x : K'⟮β'⟯,
      algebraMap K'⟮β'⟯ (IntermediateField.adjoin L' ({β', γ'} : Set Ω')) x ∈ χ.range)
    (hγ'_R : ιK'₂ (AdjoinSimple.gen K'⟮β'⟯ γ') ∈ χ.range)
    (hB₁_R : ∀ b : integralClosure A₁ L₁, ιL₁ b ∈ χ.range) :
    Function.Surjective χ := by
  let E'' : IntermediateField L' Ω' := IntermediateField.adjoin L' ({β', γ'} : Set Ω')
  let R : Subring E'' := χ.range
  let R_K'₁ : Subalgebra K'⟮β'⟯ E'' := { R with algebraMap_mem' := hK'₁_R }
  have hK'₂_R : ∀ z : (K'⟮β'⟯)⟮γ'⟯, ιK'₂ z ∈ R := fun z ↦
    TauCeti.IntermediateField.map_mem_of_gen_mem_subalgebra
      hγ'_int.tower_top.isAlgebraic ιK'₂ (S := R_K'₁) hγ'_R z
  have hL₁_R (w : L₁) : ιL₁ w ∈ R := by
    have hw : w ∈ Submodule.span K₁ (integralClosure A₁ L₁ : Set L₁) :=
      span_integralClosure_eq_top (A := A₁) (K := K₁) (L := L₁) ▸ Submodule.mem_top
    refine Submodule.span_induction (fun b hb ↦ hB₁_R ⟨b, hb⟩)
      (by rw [map_zero]; exact R.zero_mem)
      (fun x y _ _ hx hy ↦ by rw [map_add]; exact R.add_mem hx hy) (fun c x _ hx ↦ ?_) hw
    have hmul : ιL₁ (c • x) = ιK'₂ (ιK c) * ιL₁ x :=
      Subtype.ext (by rw [MulMemClass.coe_mul, hιK'₂, hιsmul])
    exact hmul ▸ R.mul_mem (hK'₂_R (ιK c)) hx
  have hL'_R (w : L') : algebraMap L' E'' w ∈ R := by
    obtain ⟨t, rfl⟩ := hφ w
    refine TensorProduct.inductionOn t (fun k' l ↦ ?_)
      (fun x y hx hy ↦ by rw [map_add, map_add]; exact R.add_mem hx hy)
    have hk' : algebraMap L' E'' (algebraMap K' L' k') =
        algebraMap K'⟮β'⟯ E'' (algebraMap K' K'⟮β'⟯ k') :=
      Subtype.ext (by rw [IntermediateField.coe_algebraMap_apply,
        ← IsScalarTower.algebraMap_apply K' L' Ω', hιK'₁, IntermediateField.coe_algebraMap_apply])
    have hl : algebraMap L' E'' (φ (1 ⊗ₜ[K] l)) = ιL₁ (algebraMap L L₁ l) :=
      Subtype.ext (by rw [hφL, IntermediateField.coe_algebraMap_apply,
        ← IsScalarTower.algebraMap_apply L L' Ω', hιL])
    have htmul : φ (k' ⊗ₜ[K] l) = algebraMap K' L' k' * φ (1 ⊗ₜ[K] l) := by
      have hk : k' ⊗ₜ[K] l = k' • ((1 : K') ⊗ₜ[K] l) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hk, map_smul, Algebra.smul_def]
    rw [htmul, map_mul, hk', hl]
    exact R.mul_mem (hK'₁_R _) (hL₁_R _)
  let R_L' : Subalgebra L' E'' := { R with algebraMap_mem' := hL'_R }
  have hsub : ({β', γ'} : Set Ω') ⊆ (R_L'.map E''.val : Subalgebra L' Ω') :=
    Set.insert_subset_iff.mpr
      ⟨⟨algebraMap K'⟮β'⟯ E'' (AdjoinSimple.gen K' β'), hK'₁_R _, hιK'₁ _⟩,
        Set.singleton_subset_iff.mpr ⟨ιK'₂ (AdjoinSimple.gen K'⟮β'⟯ γ'), hγ'_R, hιK'₂ _⟩⟩
  have halg : ∀ x ∈ ({β', γ'} : Set Ω'), IsAlgebraic L' x := fun x hx ↦ by
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · exact hx.symm ▸ hβ'_int.tower_top.isAlgebraic
    · exact (Set.mem_singleton_iff.mp hx).symm ▸ hγ'_int.tower_top.isAlgebraic
  intro z
  have hz₀ : (z : Ω') ∈ E''.toSubalgebra := z.2
  rw [adjoin_toSubalgebra_of_isAlgebraic halg] at hz₀
  obtain ⟨w, hw, hwz⟩ := Subalgebra.mem_map.mp (Algebra.adjoin_le hsub hz₀)
  exact Subtype.ext hwz ▸ hw

/-- Assembles the `K'₁`-algebra map `K'₁ ⊗[A'₁] (A'₂ ⊗[A₁] B₁) →ₐ[K'₁] E''` from compatible ring
homomorphisms out of `A'₂` and `B₁`. -/
private def lift_compositum_tensor
    {A₁ A'₁ K'₁ A'₂ B₁ E'' : Type*} [CommRing A₁] [CommRing A'₁] [CommRing K'₁]
    [CommRing A'₂] [CommRing B₁] [CommRing E'']
    [Algebra A'₁ K'₁] [Algebra A'₁ A'₂] [Algebra A₁ A'₂] [Algebra A₁ B₁] [Algebra K'₁ E'']
    (fA'₂ : A'₂ →+* E'') (fB₁ : B₁ →+* E'')
    (hA₁ : ∀ a : A₁, fB₁ (algebraMap A₁ B₁ a) = fA'₂ (algebraMap A₁ A'₂ a))
    (hA'₁ : ∀ y : A'₁, fA'₂ (algebraMap A'₁ A'₂ y) = algebraMap K'₁ E'' (algebraMap A'₁ K'₁ y)) :
    K'₁ ⊗[A'₁] (A'₂ ⊗[A₁] B₁) →ₐ[K'₁] E'' :=
  letI : Algebra A₁ E'' := (fA'₂.comp (algebraMap A₁ A'₂)).toAlgebra
  letI : Algebra A'₁ E'' := ((algebraMap K'₁ E'').comp (algebraMap A'₁ K'₁)).toAlgebra
  haveI : IsScalarTower A'₁ K'₁ E'' := .of_algebraMap_eq fun _ ↦ rfl
  let fA'₂_a : A'₂ →ₐ[A₁] E'' := { fA'₂ with commutes' := fun _ ↦ rfl }
  let fB₁_a : B₁ →ₐ[A₁] E'' := { fB₁ with commutes' := hA₁ }
  let ψ₀ : A'₂ ⊗[A₁] B₁ →ₐ[A₁] E'' := Algebra.TensorProduct.lift fA'₂_a fB₁_a fun _ _ ↦ .all _ _
  let ψ : A'₂ ⊗[A₁] B₁ →ₐ[A'₁] E'' :=
    { ψ₀.toRingHom with
      commutes' := fun y ↦ by
        simp [ψ₀, fA'₂_a, Algebra.TensorProduct.algebraMap_apply, RingHom.algebraMap_toAlgebra,
          hA'₁] }
  Algebra.TensorProduct.lift (Algebra.ofId K'₁ E'') ψ fun _ _ ↦ .all _ _

/-- Over abstract fields `K'₁` and `E''` and finite étale algebras `A'₂ / A'₁` and `B₁ / A₁`, if
the induced `K'₁`-algebra map `K'₁ ⊗[A'₁] (A'₂ ⊗[A₁] B₁) →ₐ[K'₁] E''` is surjective whenever its
range contains `algebraMap K'₁ E''`, `fA'₂ γ'₀`, and `fB₁`, then `E''` is unramified over `A'₁`. -/
private theorem isUnramifiedWRT_of_compositum_closures
    (A₁ B₁ A'₁ K'₁ A'₂ E'' : Type v)
    [CommRing A₁] [CommRing B₁] [Algebra A₁ B₁] [Algebra.Etale A₁ B₁] [Module.Finite A₁ B₁]
    [CommRing A'₁] [IsDomain A'₁] [IsDiscreteValuationRing A'₁]
    [Field K'₁] [Algebra A'₁ K'₁] [IsFractionRing A'₁ K'₁]
    [CommRing A'₂] [Algebra A'₁ A'₂] [Algebra A₁ A'₂] [Algebra.Etale A'₁ A'₂]
    [Module.Finite A'₁ A'₂]
    [Field E''] [Algebra A'₁ E''] [Algebra K'₁ E''] [IsScalarTower A'₁ K'₁ E'']
    (fA'₂ : A'₂ →+* E'') (fB₁ : B₁ →+* E'')
    (hA₁ : ∀ a : A₁, fB₁ (algebraMap A₁ B₁ a) = fA'₂ (algebraMap A₁ A'₂ a))
    (hA'₁ : ∀ y : A'₁, fA'₂ (algebraMap A'₁ A'₂ y) = algebraMap K'₁ E'' (algebraMap A'₁ K'₁ y))
    (γ'₀ : A'₂)
    (hsurj : ∀ {T : Type v} [CommRing T] (χ : T →+* E''),
      (∀ x : K'₁, algebraMap K'₁ E'' x ∈ χ.range) →
      fA'₂ γ'₀ ∈ χ.range →
      (∀ b : B₁, fB₁ b ∈ χ.range) →
      Function.Surjective χ) :
    IsUnramifiedWRT A'₁ E'' := by
  let S' := A'₂ ⊗[A₁] B₁
  have : Algebra.Etale A'₁ S' := .comp A'₁ A'₂ S'
  have : Module.Finite A'₁ S' := .trans A'₂ S'
  let χ : K'₁ ⊗[A'₁] S' →ₐ[K'₁] E'' := lift_compositum_tensor fA'₂ fB₁ hA₁ hA'₁
  have hχ : Function.Surjective χ :=
    hsurj χ.toRingHom
      (fun x ↦ ⟨x ⊗ₜ[A'₁] (1 : S'), by simp [χ, lift_compositum_tensor]⟩)
      ⟨(1 : K'₁) ⊗ₜ[A'₁] (γ'₀ ⊗ₜ[A₁] (1 : B₁)), by simp [χ, lift_compositum_tensor]⟩
      (fun b ↦ ⟨(1 : K'₁) ⊗ₜ[A'₁] ((1 : A'₂) ⊗ₜ[A₁] b), by simp [χ, lift_compositum_tensor]⟩)
  exact χ.isUnramifiedWRT_of_surjective hχ

/-- If `γ' ^ e₀ = algebraMap A' Ω' x` with `0 < e₀`, the generator of `K'₁(γ')` is integral over
`integralClosure A' K'₁`. -/
private theorem isIntegral_adjoinSimple_gen_of_pow_eq
    {A' K'₁ Ω' : Type*} [CommRing A'] [Field K'₁] [Field Ω'] [Algebra A' K'₁]
    [Algebra A' Ω'] [Algebra K'₁ Ω'] [IsScalarTower A' K'₁ Ω']
    {γ' : Ω'} {e₀ : ℕ} (he₀_pos : 0 < e₀) {x : A'} (hγ' : γ' ^ e₀ = algebraMap A' Ω' x) :
    IsIntegral (integralClosure A' K'₁) (AdjoinSimple.gen K'₁ γ') := by
  have h : AdjoinSimple.gen K'₁ γ' ^ e₀ = algebraMap A' K'₁⟮γ'⟯ x :=
    (AdjoinSimple.gen_pow_eq_algebraMap_iff K'₁).mpr hγ'
  exact (IsIntegral.of_pow he₀_pos (h ▸ isIntegral_algebraMap (R := A'))).tower_top

/-- If `x ∈ E` for an intermediate field `E / L / K` inside `Ω'`, there is a `K`-algebra
homomorphism `K⟮x⟯ →ₐ[K] E` preserving underlying elements of `Ω'`. -/
private theorem exists_adjoinSimple_algHom
    {K L Ω' : Type*} [Field K] [Field L] [Field Ω'] [Algebra K L] [Algebra K Ω'] [Algebra L Ω']
    [IsScalarTower K L Ω'] {E : IntermediateField L Ω'} {x : Ω'} (hx : x ∈ E) :
    ∃ ι : K⟮x⟯ →ₐ[K] E, ∀ z : K⟮x⟯, (ι z : Ω') = z :=
  ⟨(E.restrictScalarsAlgEquiv K).toAlgHom.comp
    (inclusion (adjoin_simple_le_iff.mpr hx : K⟮x⟯ ≤ E.restrictScalars K)),
    fun z ↦ by simp⟩

/-- If `β', γ' ∈ E` for an intermediate field `E / L' / K'` inside `Ω'` equipped with a compatible
`K'⟮β'⟯`-algebra structure, there is a `K'⟮β'⟯`-algebra homomorphism `(K'⟮β'⟯)⟮γ'⟯ →ₐ[K'⟮β'⟯] E`
preserving underlying elements of `Ω'`. -/
private theorem exists_adjoinSimple_adjoinSimple_algHom
    {K' L' Ω' : Type*} [Field K'] [Field L'] [Field Ω']
    [Algebra K' L'] [Algebra K' Ω'] [Algebra L' Ω'] [IsScalarTower K' L' Ω']
    {E : IntermediateField L' Ω'} {β' γ' : Ω'} [Algebra K'⟮β'⟯ E] [IsScalarTower K'⟮β'⟯ E Ω']
    (hβ' : β' ∈ E) (hγ' : γ' ∈ E) :
    ∃ ι : (K'⟮β'⟯)⟮γ'⟯ →ₐ[K'⟮β'⟯] E, ∀ z : (K'⟮β'⟯)⟮γ'⟯, (ι z : Ω') = z := by
  have hle : ((K'⟮β'⟯)⟮γ'⟯).restrictScalars K' ≤ E.restrictScalars K' := by
    rw [adjoin_simple_adjoin_simple]
    exact adjoin_le_iff.mpr (Set.insert_subset_iff.mpr ⟨hβ', Set.singleton_subset_iff.mpr hγ'⟩)
  let ι₀ : (K'⟮β'⟯)⟮γ'⟯ →ₐ[K'] E :=
    ((E.restrictScalarsAlgEquiv K').toAlgHom.comp (inclusion hle)).comp
      (((K'⟮β'⟯)⟮γ'⟯).restrictScalarsAlgEquiv K').symm.toAlgHom
  have hι₀ (z : (K'⟮β'⟯)⟮γ'⟯) : (ι₀ z : Ω') = z := by simp [ι₀]
  exact ⟨{ ι₀.toRingHom with
    commutes' := fun x ↦ (algebraMap E Ω').injective <| by
      rw [← IsScalarTower.algebraMap_apply K'⟮β'⟯ E Ω']
      simp [hι₀] }, hι₀⟩

/-- Compatibility of `A → A'₁` and `ιK : K₁ →+* K'₂` in an ambient ring `Ω'` induces an algebra
structure `integralClosure A K₁ → integralClosure A'₁ K'₂` via
`TauCeti.integralClosureMapAlgebra`. -/
private theorem exists_integralClosureMapAlgebra
    {A A' A'₁ K₁ K'₂ Ω' : Type*} [CommRing A] [CommRing A'] [CommRing A'₁]
    [CommRing K₁] [CommRing K'₂] [CommRing Ω']
    [Algebra A A'] [Algebra A' A'₁] [Algebra A K₁] [Algebra A'₁ K'₂]
    [Algebra A Ω'] [Algebra A' Ω'] [Algebra K₁ Ω'] [Algebra K'₂ Ω']
    [IsScalarTower A A' Ω'] [IsScalarTower A K₁ Ω']
    (hA'₁ : ∀ r : A', algebraMap K'₂ Ω' (algebraMap A'₁ K'₂ (algebraMap A' A'₁ r)) =
      algebraMap A' Ω' r)
    (hK'₂ : Function.Injective (algebraMap K'₂ Ω'))
    (ιK : K₁ →+* K'₂) (hιK : ∀ z : K₁, algebraMap K'₂ Ω' (ιK z) = algebraMap K₁ Ω' z) :
    ∃ (_ : Algebra (integralClosure A K₁) (integralClosure A'₁ K'₂)),
      ∀ a : integralClosure A K₁,
        algebraMap K'₂ Ω' (algebraMap (integralClosure A K₁) (integralClosure A'₁ K'₂) a :
          integralClosure A'₁ K'₂) = algebraMap K₁ Ω' a := by
  let : Algebra K₁ K'₂ := ιK.toAlgebra
  let : Algebra A A'₁ := ((algebraMap A' A'₁).comp (algebraMap A A')).toAlgebra
  let : Algebra A K'₂ := ((algebraMap A'₁ K'₂).comp (algebraMap A A'₁)).toAlgebra
  have : IsScalarTower A A'₁ K'₂ := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A K₁ K'₂ := .of_algebraMap_eq fun a ↦ hK'₂ <| by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, RingHom.algebraMap_toAlgebra,
      RingHom.comp_apply, hA'₁, ← IsScalarTower.algebraMap_apply A A' Ω',
      RingHom.algebraMap_toAlgebra, hιK, ← IsScalarTower.algebraMap_apply A K₁ Ω']
  let := integralClosureMapAlgebra A K₁ A'₁ K'₂
  refine ⟨inferInstance, fun a ↦ ?_⟩
  rw [coe_algebraMap_integralClosureMapAlgebra A K₁ A'₁ K'₂, RingHom.algebraMap_toAlgebra, hιK]

variable {A K L A' K' L' : Type*}
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A'] [Field K'] [Algebra A' K']
  [IsFractionRing A' K'] [Algebra A A'] [Algebra A K'] [Algebra K K'] [IsScalarTower A A' K']
  [IsScalarTower A K K'] [Field L'] [Algebra K' L'] [Algebra A' L'] [IsScalarTower A' K' L']

/-- For a tamely ramified extension `L / K` over `A` and an `e₀`-th root `α'` of a uniformizer `π`
of `A` in an extension `Ω'` of `L` (where `0 < e₀` is divisible by all ramification indices over
`A`), `integralClosure A K(α')` is a discrete valuation ring with fraction field `K(α')` and
`integralClosure A[α'] L(α')` is finite étale over `A[α'] := integralClosure A K(α')`. -/
private theorem etale_and_finite_over_adjoin_root_of_tame
    {Ω' : Type*} [Field Ω'] [Algebra K Ω'] [Algebra L Ω'] [Algebra A Ω']
    [IsScalarTower K L Ω'] [IsScalarTower A K Ω']
    (h : IsTamelyRamifiedWRT A L) {π : A} (hπ : Irreducible π) {e₀ : ℕ} (he₀_pos : 0 < e₀)
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      P.ramificationIdx A ∣ e₀)
    {α' : Ω'} (hα' : α' ^ e₀ = algebraMap A Ω' π) :
    letI := (TauCeti.IntermediateField.adjoinBaseChange K L α').toAlgebra
    ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮α'⟯),
      letI := hDVR
      IsFractionRing (integralClosure A K⟮α'⟯) K⟮α'⟯ ∧
        Algebra.IsAlgebraic K⟮α'⟯ L⟮α'⟯ ∧
        Algebra.Etale (integralClosure A K⟮α'⟯) (integralClosure (integralClosure A K⟮α'⟯) L⟮α'⟯) ∧
        Module.Finite (integralClosure A K⟮α'⟯)
          (integralClosure (integralClosure A K⟮α'⟯) L⟮α'⟯) := by
  let := (TauCeti.IntermediateField.adjoinBaseChange K L α').toAlgebra
  obtain ⟨hDVR, hunrL₁, _, _⟩ :=
    h.isUnramifiedWRT_adjoin_of_pow_eq_of_irreducible (K := K) hπ hdvd hα'
  let := hDVR
  have hdegKα := TauCeti.IsDiscreteValuationRing.finrank_adjoin_of_pow_eq_of_irreducible
    (K := K) hπ hα'
  have : FiniteDimensional K K⟮α'⟯ := Module.finite_of_finrank_pos (hdegKα ▸ he₀_pos)
  have : IsFractionRing (integralClosure A K⟮α'⟯) K⟮α'⟯ :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K K⟮α'⟯ _
  have := IsScalarTower.subalgebra A K⟮α'⟯ L⟮α'⟯ (integralClosure A K⟮α'⟯)
  have := IsScalarTower.subalgebra' (integralClosure A K⟮α'⟯) L⟮α'⟯ L⟮α'⟯
    (integralClosure (integralClosure A K⟮α'⟯) L⟮α'⟯)
  exact ⟨hDVR, ‹_›, Algebra.IsAlgebraic.of_finite K⟮α'⟯ L⟮α'⟯,
    (isUnramifiedWRT_iff_etale (integralClosure A K⟮α'⟯) K⟮α'⟯ L⟮α'⟯).mp hunrL₁,
    IsIntegralClosure.finite (integralClosure A K⟮α'⟯) K⟮α'⟯ L⟮α'⟯
      (integralClosure (integralClosure A K⟮α'⟯) L⟮α'⟯)⟩

/-- In an overfield `Ω'` of `K'` containing `e₀`-th roots `β'` of a uniformizer `ϖ'` of `A'` and
`γ'` of a unit `u'` of `A'` (with `e₀` invertible in `A'`), `K'(β')` is tamely ramified over `A'`
and `integralClosure A'₁ K'(β')(γ')` is finite étale over `A'₁ := integralClosure A' K'(β')`. -/
private theorem etale_and_finite_over_adjoin_uniformizer_root
    {Ω' : Type*} [Field Ω'] [Algebra K' Ω'] [Algebra A' Ω'] [IsScalarTower A' K' Ω']
    {ϖ' : A'} (hϖ' : Irreducible ϖ') {u' : A'ˣ} {e₀ : ℕ} (he₀_A' : IsUnit (e₀ : A'))
    {β' γ' : Ω'} (hβ' : β' ^ e₀ = algebraMap A' Ω' ϖ') (hγ' : γ' ^ e₀ = algebraMap A' Ω' u')
    [IsDiscreteValuationRing (integralClosure A' K'⟮β'⟯)] :
    IsTamelyRamifiedWRT A' K'⟮β'⟯ ∧
      IsFractionRing (integralClosure A' K'⟮β'⟯) K'⟮β'⟯ ∧
      Algebra.Etale (integralClosure A' K'⟮β'⟯)
        (integralClosure (integralClosure A' K'⟮β'⟯) (K'⟮β'⟯)⟮γ'⟯) ∧
      Module.Finite (integralClosure A' K'⟮β'⟯)
        (integralClosure (integralClosure A' K'⟮β'⟯) (K'⟮β'⟯)⟮γ'⟯) := by
  have he₀_pos : 0 < e₀ := Nat.pos_of_ne_zero he₀_A'.neZero_natCast.out
  have he₀_res' : IsUnit (e₀ : A' ⧸ maximalIdeal A') := by
    simpa using he₀_A'.map (Ideal.Quotient.mk (maximalIdeal A'))
  let K'₁ : IntermediateField K' Ω' := K'⟮β'⟯
  let A'₁ := integralClosure A' K'₁
  have hK'₁_tame : IsTamelyRamifiedWRT A' K'₁ :=
    (TauCeti.IsDiscreteValuationRing.isTamelyRamifiedWRT_adjoin_iff_of_pow_eq_of_irreducible
      hϖ' hβ').mpr he₀_res'
  have hdegK'₁ := TauCeti.IsDiscreteValuationRing.finrank_adjoin_of_pow_eq_of_irreducible
    (K := K') hϖ' hβ'
  have : FiniteDimensional K' K'₁ := Module.finite_of_finrank_pos (hdegK'₁ ▸ he₀_pos)
  have : IsFractionRing A'₁ K'₁ := IsIntegralClosure.isFractionRing_of_finite_extension A' K' K'₁ _
  have he₀_A'₁ : IsUnit (e₀ : A'₁) := by simpa using he₀_A'.map (algebraMap A' A'₁)
  have hγ'A'₁ : γ' ^ e₀ = algebraMap A'₁ Ω' (algebraMap A' A'₁ u') := by
    rwa [← IsScalarTower.algebraMap_apply A' A'₁ Ω']
  obtain ⟨hunrK'₂, _, _⟩ :=
    TauCeti.IsDiscreteValuationRing.isUnramifiedWRT_adjoin_of_pow_eq_of_isUnit
      (A := A'₁) (K := K'₁) (u'.isUnit.map (algebraMap A' A'₁)) he₀_A'₁ hγ'A'₁
  have := IsScalarTower.subalgebra A' K'₁ (K'⟮β'⟯)⟮γ'⟯ A'₁
  have := IsScalarTower.subalgebra' A'₁ (K'⟮β'⟯)⟮γ'⟯ (K'⟮β'⟯)⟮γ'⟯
    (integralClosure A'₁ (K'⟮β'⟯)⟮γ'⟯)
  exact ⟨hK'₁_tame, ‹_›,
    (isUnramifiedWRT_iff_etale A'₁ K'₁ (K'⟮β'⟯)⟮γ'⟯).mp hunrK'₂,
    IsIntegralClosure.finite A'₁ K'₁ (K'⟮β'⟯)⟮γ'⟯ (integralClosure A'₁ (K'⟮β'⟯)⟮γ'⟯)⟩

omit [IsDomain A'] [IsDiscreteValuationRing A'] [IsFractionRing A' K'] [Algebra A K']
  [IsScalarTower A A' K'] [IsScalarTower A K K'] [Algebra A' L'] [IsScalarTower A' K' L'] in
/-- Under the hypotheses of `isTamelyRamifiedWRT_of_roots_in_overfield`, the double root extension
`L'(β', γ')` inside `Ω'` is unramified with respect to `integralClosure A' K'(β')`. -/
private theorem isUnramifiedWRT_adjoin_roots_in_overfield
    [Algebra L L']
    {Ω' : Type v} [Field Ω'] [Algebra L' Ω'] [Algebra K' Ω'] [Algebra A' Ω']
    [Algebra L Ω'] [Algebra K Ω'] [Algebra A Ω']
    [IsScalarTower K' L' Ω'] [IsScalarTower A' K' Ω']
    [IsScalarTower L L' Ω'] [IsScalarTower K L Ω'] [IsScalarTower A K Ω']
    [IsScalarTower K K' Ω'] [IsScalarTower A A' Ω']
    (h : IsTamelyRamifiedWRT A L) (φ : K' ⊗[K] L →ₐ[K'] L') (hφ : Function.Surjective φ)
    (hφL : ∀ l : L, φ (1 ⊗ₜ[K] l) = algebraMap L L' l)
    {π : A} (hπ : Irreducible π) {ϖ' : A'} {u' : A'ˣ} {m e₀ : ℕ} (he₀_pos : 0 < e₀)
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      P.ramificationIdx A ∣ e₀)
    {β' γ' : Ω'} (hβ' : β' ^ e₀ = algebraMap A' Ω' ϖ') (hγ' : γ' ^ e₀ = algebraMap A' Ω' u')
    (hα' : (γ' * β' ^ m) ^ e₀ = algebraMap A Ω' π)
    [IsDiscreteValuationRing (integralClosure A' K'⟮β'⟯)]
    [IsFractionRing (integralClosure A' K'⟮β'⟯) K'⟮β'⟯]
    [Algebra.Etale (integralClosure A' K'⟮β'⟯)
      (integralClosure (integralClosure A' K'⟮β'⟯) (K'⟮β'⟯)⟮γ'⟯)]
    [Module.Finite (integralClosure A' K'⟮β'⟯)
      (integralClosure (integralClosure A' K'⟮β'⟯) (K'⟮β'⟯)⟮γ'⟯)]
    [Algebra K'⟮β'⟯ (IntermediateField.adjoin L' ({β', γ'} : Set Ω'))]
    [IsScalarTower (integralClosure A' K'⟮β'⟯) K'⟮β'⟯
      (IntermediateField.adjoin L' ({β', γ'} : Set Ω'))]
    [IsScalarTower K'⟮β'⟯ (IntermediateField.adjoin L' ({β', γ'} : Set Ω')) Ω'] :
    IsUnramifiedWRT (integralClosure A' K'⟮β'⟯)
      (IntermediateField.adjoin L' ({β', γ'} : Set Ω')) := by
  let α' : Ω' := γ' * β' ^ m
  let := (TauCeti.IntermediateField.adjoinBaseChange K L α').toAlgebra
  obtain ⟨hDVR, _, _, _, _⟩ :=
    etale_and_finite_over_adjoin_root_of_tame (K := K) h hπ he₀_pos hdvd hα'
  have := hDVR
  let A₁ := integralClosure A K⟮α'⟯
  let B₁ := integralClosure A₁ L⟮α'⟯
  let A'₁ := integralClosure A' K'⟮β'⟯
  let A'₂ := integralClosure A'₁ (K'⟮β'⟯)⟮γ'⟯
  let E'' : IntermediateField L' Ω' := IntermediateField.adjoin L' ({β', γ'} : Set Ω')
  have hβ'_mem : β' ∈ E'' := IntermediateField.subset_adjoin L' _ (Set.mem_insert β' {γ'})
  have hγ'_mem : γ' ∈ E'' := IntermediateField.subset_adjoin L' _ (Set.mem_insert_of_mem β' rfl)
  obtain ⟨ιK'₂, hιK'₂_coe⟩ :=
    exists_adjoinSimple_adjoinSimple_algHom (K' := K') (E := E'') hβ'_mem hγ'_mem
  obtain ⟨ιK, hιK_coe⟩ := exists_adjoinSimple_algHom (K := K) (E := (K'⟮β'⟯)⟮γ'⟯)
    (x := α') (mul_mem (mem_adjoin_simple_self K'⟮β'⟯ γ')
      (pow_mem (((K'⟮β'⟯)⟮γ'⟯).algebraMap_mem (AdjoinSimple.gen K' β')) m))
  obtain ⟨_, hA₁A'₂_coe⟩ := exists_integralClosureMapAlgebra (A := A) (A' := A') (A'₁ := A'₁)
    (K₁ := K⟮α'⟯) (K'₂ := (K'⟮β'⟯)⟮γ'⟯) (Ω' := Ω') (fun _ ↦ rfl)
    (algebraMap (K'⟮β'⟯)⟮γ'⟯ Ω').injective ιK.toRingHom fun z ↦ by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, IntermediateField.algebraMap_apply,
        IntermediateField.algebraMap_apply, hιK_coe]
  obtain ⟨ιL₁, hιL₁_coe⟩ :=
    exists_adjoinSimple_algHom (K := L) (E := E'') (x := α') (mul_mem hγ'_mem (pow_mem hβ'_mem m))
  have hA₁ (a : A₁) : (ιL₁.toRingHom.comp (algebraMap B₁ L⟮α'⟯)) (algebraMap A₁ B₁ a) =
      (ιK'₂.toRingHom.comp (algebraMap A'₂ (K'⟮β'⟯)⟮γ'⟯)) (algebraMap A₁ A'₂ a) := by
    apply Subtype.ext
    have hL : (((ιL₁.toRingHom.comp (algebraMap B₁ L⟮α'⟯)) (algebraMap A₁ B₁ a) : E'') : Ω') =
        (a.1 : Ω') := by
      rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hιL₁_coe]
      exact TauCeti.IntermediateField.coe_adjoinBaseChange K L α' a.1
    have hR : (((ιK'₂.toRingHom.comp (algebraMap A'₂ (K'⟮β'⟯)⟮γ'⟯))
        (algebraMap A₁ A'₂ a) : E'') : Ω') = (a.1 : Ω') := by
      rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hιK'₂_coe]
      exact hA₁A'₂_coe a
    exact hL.trans hR.symm
  have hA'₁ (y : A'₁) : (ιK'₂.toRingHom.comp (algebraMap A'₂ (K'⟮β'⟯)⟮γ'⟯)) (algebraMap A'₁ A'₂ y) =
      algebraMap K'⟮β'⟯ E'' (algebraMap A'₁ K'⟮β'⟯ y) :=
    Subtype.ext (by
      rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hιK'₂_coe,
        ← IntermediateField.algebraMap_apply E'',
        ← IsScalarTower.algebraMap_apply K'⟮β'⟯ E'' Ω']
      rfl)
  have hβ'_intK' : IsIntegral K' β' :=
    (IsIntegral.of_pow he₀_pos (hβ' ▸ isIntegral_algebraMap (R := A'))).tower_top
  have hγ'_intK' : IsIntegral K' γ' :=
    (IsIntegral.of_pow he₀_pos (hγ' ▸ isIntegral_algebraMap (R := A'))).tower_top
  exact isUnramifiedWRT_of_compositum_closures A₁ B₁ A'₁ K'⟮β'⟯ A'₂ E''
    (ιK'₂.toRingHom.comp (algebraMap A'₂ (K'⟮β'⟯)⟮γ'⟯)) (ιL₁.toRingHom.comp (algebraMap B₁ L⟮α'⟯))
    hA₁ hA'₁ ⟨AdjoinSimple.gen K'⟮β'⟯ γ', isIntegral_adjoinSimple_gen_of_pow_eq he₀_pos hγ'⟩
    (fun χ h1 h2 h3 ↦ surjective_compositum_lift (K := K) (L := L) (K' := K') (L' := L')
      (Ω' := Ω') (K₁ := K⟮α'⟯) (L₁ := L⟮α'⟯) (A₁ := A₁) φ hφ hφL hβ'_intK' hγ'_intK'
      ιK.toRingHom ιL₁.toRingHom
      (fun l ↦ by
        rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hιL₁_coe,
          IntermediateField.coe_algebraMap_apply])
      (fun c x ↦ by
        rw [Algebra.smul_def, map_mul, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          MulMemClass.coe_mul, hιL₁_coe, hιL₁_coe, RingHom.algebraMap_toAlgebra,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          TauCeti.IntermediateField.coe_adjoinBaseChange,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hιK_coe])
      (fun x ↦ by
        rw [← IntermediateField.algebraMap_apply E'',
          ← IsScalarTower.algebraMap_apply K'⟮β'⟯ E'' Ω', IntermediateField.algebraMap_apply])
      ιK'₂ hιK'₂_coe χ h1 h2 h3)

omit [Algebra A K'] [IsScalarTower A A' K'] [IsScalarTower A K K'] in
/-- Given an ambient overfield `Ω'` of `L'` containing `e₀`-th roots `β'` of a uniformizer `ϖ'` of
`A'` and `γ'` of a unit `u'` of `A'` with `(γ' * β' ^ m) ^ e₀ = π`, the compositum `L'(β', γ')` is
unramified over `integralClosure A' K'(β')`, so `L'` is tamely ramified with respect to `A'`. -/
private theorem isTamelyRamifiedWRT_of_roots_in_overfield
    [FiniteDimensional K' L'] [Algebra.IsSeparable K' L']
    [Algebra L L']
    {Ω' : Type*} [Field Ω'] [Algebra L' Ω'] [Algebra K' Ω'] [Algebra A' Ω']
    [Algebra L Ω'] [Algebra K Ω'] [Algebra A Ω']
    [IsScalarTower K' L' Ω'] [IsScalarTower A' K' Ω'] [IsScalarTower A' L' Ω']
    [IsScalarTower L L' Ω'] [IsScalarTower K L Ω'] [IsScalarTower A K Ω']
    [IsScalarTower K K' Ω'] [IsScalarTower A A' Ω']
    (h : IsTamelyRamifiedWRT A L) (φ : K' ⊗[K] L →ₐ[K'] L') (hφ : Function.Surjective φ)
    (hφL : ∀ l : L, φ (1 ⊗ₜ[K] l) = algebraMap L L' l)
    {π : A} (hπ : Irreducible π) {ϖ' : A'} (hϖ' : Irreducible ϖ') {u' : A'ˣ} {m e₀ : ℕ}
    (he₀_A' : IsUnit (e₀ : A'))
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      P.ramificationIdx A ∣ e₀)
    {β' γ' : Ω'} (hβ' : β' ^ e₀ = algebraMap A' Ω' ϖ') (hγ' : γ' ^ e₀ = algebraMap A' Ω' u')
    (hα' : (γ' * β' ^ m) ^ e₀ = algebraMap A Ω' π) :
    IsTamelyRamifiedWRT A' L' := by
  have he₀_pos : 0 < e₀ := Nat.pos_of_ne_zero he₀_A'.neZero_natCast.out
  have :=
    IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_adjoin_of_pow_eq_of_irreducible
      (K := K') hϖ' hβ'
  obtain ⟨hK'₁_tame, _, _, _⟩ :=
    etale_and_finite_over_adjoin_uniformizer_root (K' := K') hϖ' he₀_A' hβ' hγ'
  let E'' : IntermediateField L' Ω' := IntermediateField.adjoin L' ({β', γ'} : Set Ω')
  have hβ'_mem : β' ∈ E'' :=
    IntermediateField.subset_adjoin L' ({β', γ'} : Set Ω') (Set.mem_insert β' {γ'})
  let ιK'₁ : K'⟮β'⟯ →ₐ[K'] E'' :=
    (E''.restrictScalarsAlgEquiv K').toAlgHom.comp
      (inclusion (adjoin_simple_le_iff.mpr hβ'_mem : K'⟮β'⟯ ≤ E''.restrictScalars K'))
  let : Algebra K'⟮β'⟯ E'' := ιK'₁.toAlgebra
  have : IsScalarTower K'⟮β'⟯ E'' Ω' := .of_algebraMap_eq fun x ↦ by
    simp [RingHom.algebraMap_toAlgebra, ιK'₁]
  have : IsScalarTower A' K'⟮β'⟯ E'' := .of_algebraMap_eq fun a ↦
    (algebraMap E'' Ω').injective (by simp only [← IsScalarTower.algebraMap_apply])
  have hunr : IsUnramifiedWRT (integralClosure A' K'⟮β'⟯) E'' :=
    isUnramifiedWRT_adjoin_roots_in_overfield h φ hφ hφL hπ he₀_pos hdvd hβ' hγ' hα'
  exact (hK'₁_tame.trans hunr.isTamelyRamifiedWRT).tower_bot K'

/-- Tamely ramified extensions of a discrete valuation ring are stable under base change: if `L` is
tamely ramified with respect to `A`, then every factor `L'` of `K' ⊗[K] L`, given by a surjective
`K'`-algebra map `φ : K' ⊗[K] L → L'`, is tamely ramified with respect to `A'`. -/
@[stacks 0EXY "tame case"]
theorem IsTamelyRamifiedWRT.baseChange (h : IsTamelyRamifiedWRT A L) (φ : K' ⊗[K] L →ₐ[K'] L')
    (hφ : Function.Surjective φ) : IsTamelyRamifiedWRT A' L' := by
  obtain ⟨_, _⟩ := φ.finiteDimensional_and_isSeparable_of_surjective_of_isSeparable hφ
  obtain ⟨π, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨ϖ', hϖ'⟩ := _root_.IsDiscreteValuationRing.exists_irreducible A'
  have := FaithfulSMul.of_field_isFractionRing A A' K K'
  have hπA' : algebraMap A A' π ≠ 0 :=
    (FaithfulSMul.algebraMap_eq_zero_iff A A').not.mpr hπ.ne_zero
  obtain ⟨m, u', hπ_eq⟩ := _root_.IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπA' hϖ'
  obtain ⟨e₀, he₀_pos, he₀_res, hdvd⟩ := h.exists_ramificationIdx_dvd (K := K)
  have he₀_A : IsUnit (e₀ : A) :=
    (isUnit_map_iff (residue A) _).mp (by rw [map_natCast]; exact he₀_res)
  have he₀_A' : IsUnit (e₀ : A') := by simpa using he₀_A.map (algebraMap A A')
  -- Embed `L` into `L'` via `φ` and extract `e₀`-th roots in `AlgebraicClosure L'`.
  let : Algebra K L' := ((algebraMap K' L').comp (algebraMap K K')).toAlgebra
  let : Algebra A L' := ((algebraMap A' L').comp (algebraMap A A')).toAlgebra
  have : IsScalarTower K K' L' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A A' L' := .of_algebraMap_eq fun _ ↦ rfl
  let jL : L →ₐ[K] L' := (φ.restrictScalars K).comp Algebra.TensorProduct.includeRight
  let : Algebra L L' := jL.toAlgebra
  have : IsScalarTower K L L' := .of_algHom jL
  have : IsScalarTower A K L' := .of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply A K K',
      IsScalarTower.algebraMap_apply A A' K', ← IsScalarTower.algebraMap_apply A' K' L']
  let Ω' := AlgebraicClosure L'
  obtain ⟨β', hβ'⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A' Ω' ϖ') he₀_pos
  obtain ⟨γ', hγ'⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A' Ω' u') he₀_pos
  have hα' : (γ' * β' ^ m) ^ e₀ = algebraMap A Ω' π := by
    rw [mul_pow, ← pow_mul, mul_comm m e₀, pow_mul, hγ', hβ', ← map_pow, ← map_mul, ← hπ_eq,
      ← IsScalarTower.algebraMap_apply A A' Ω']
  exact isTamelyRamifiedWRT_of_roots_in_overfield h φ hφ
    (fun l ↦ by simp [jL, RingHom.algebraMap_toAlgebra]) hπ hϖ' he₀_A' hdvd hβ' hγ' hα'

end BaseChange

end TauCeti.Algebra
