/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.TamelyRamified
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.Algebra.Algebra.Hom
import TauCeti.FieldTheory.IntermediateField.Adjoin.BaseChange
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.RingTheory.AdjoinRoot.Basic
import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.Basic
import TauCeti.RingTheory.DiscreteValuationRing.BaseChange.Kummer
import TauCeti.RingTheory.DiscreteValuationRing.BaseChange.Unramified
import TauCeti.RingTheory.DiscreteValuationRing.Kummer
import TauCeti.RingTheory.IntegralClosure.TensorProduct
import TauCeti.RingTheory.Unramified.Field

/-!
# Base change of tamely ramified extensions of a discrete valuation ring

Let `A → A'` be a homomorphism of discrete valuation rings with compatible fraction fields
`K → K'`, and let `L / K` be a finite separable extension. If `L` is tamely ramified with respect
to `A`, then every field factor `L'` of `K' ⊗[K] L`, presented by a surjective `K'`-algebra map
`φ : K' ⊗[K] L →ₐ[K'] L'`, is tamely ramified with respect to `A'` (Stacks, Lemma 15.116.9 (0EXY),
the tamely ramified half).

Geometrically, this is the codimension-one local stalk input to pullback stability of covers that
are tamely ramified with respect to a divisor on normal schemes (Stacks, Lemma 58.31.5 (0EYD)).

## Usage notes

* The homomorphism `A → A'` is not required to be local (`IsLocalHom` is not assumed); only
  compatibility with the fraction-field extension `K → K'` (`[IsScalarTower A A' K']` and
  `[IsScalarTower A K K']`) is used.
* `[FiniteDimensional K' L']` and `[Algebra.IsSeparable K' L']` are not assumed on the target
  factor `L'`: finite-dimensionality over `K'` is deduced from `Function.Surjective φ`, and
  separability of `L' / K'` is not needed in the proof (and holds automatically via
  `AlgHom.finiteDimensional_and_isSeparable_of_surjective`).

## Main results

* `TauCeti.Algebra.IsTamelyRamifiedWRT.baseChange`: every factor of `K' ⊗[K] L` is tamely ramified
  with respect to `A'` when `L` is tamely ramified with respect to `A`.

## References

* [Stacks Project, Lemma 15.116.9](https://stacks.math.columbia.edu/tag/0EXY).
* [Stacks Project, Lemma 58.31.5](https://stacks.math.columbia.edu/tag/0EYD).
-/

public section

open scoped TensorProduct
open IsLocalRing Polynomial _root_.IntermediateField

namespace TauCeti.Algebra

section Helpers

/-- Over the `A`-side Kummer discrete valuation ring `integralClosure A K(α₁)`, the integral closure
in `L(α₁)` is finite étale when `L` is finite separable and tamely ramified with respect to `A` and
every maximal ideal's ramification index divides `e`. -/
private theorem etale_integralClosure_adjoin_of_tame
    {A : Type*} (K : Type*) {L E' : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Field E'] [Algebra A E'] [Algebra K E'] [Algebra L E']
    [IsScalarTower A K E'] [IsScalarTower K L E']
    (h : IsTamelyRamifiedWRT A L) {π : A} (hπ : Irreducible π) {e : ℕ} (he : 0 < e) {α₁ : E'}
    (hα₁ : α₁ ^ e = algebraMap A E' π)
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal], P.ramificationIdx A ∣ e) :
    letI := (TauCeti.IntermediateField.adjoinBaseChange K L α₁).toAlgebra
    ∃ (_ : IsDiscreteValuationRing (integralClosure A K⟮α₁⟯)),
      Algebra.Etale (integralClosure A K⟮α₁⟯)
        (integralClosure (integralClosure A K⟮α₁⟯) L⟮α₁⟯) ∧
      Module.Finite (integralClosure A K⟮α₁⟯)
        (integralClosure (integralClosure A K⟮α₁⟯) L⟮α₁⟯) := by
  let := (TauCeti.IntermediateField.adjoinBaseChange K L α₁).toAlgebra
  let : Module (integralClosure A K⟮α₁⟯)
      (integralClosure (integralClosure A K⟮α₁⟯) L⟮α₁⟯) := Algebra.toModule
  let : SMul (integralClosure A K⟮α₁⟯)
      (integralClosure (integralClosure A K⟮α₁⟯) L⟮α₁⟯) := Algebra.toSMul
  have : IsScalarTower (integralClosure A K⟮α₁⟯)
      (integralClosure (integralClosure A K⟮α₁⟯) L⟮α₁⟯) L⟮α₁⟯ := .of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨hDVR, hunr⟩ := h.isUnramifiedWRT_adjoin_root (K := K) hπ hα₁ hdvd
  have := hDVR
  have hαK : AdjoinSimple.gen K α₁ ^ e = algebraMap A K⟮α₁⟯ π :=
    (algebraMap K⟮α₁⟯ E').injective <| by
      rw [map_pow, AdjoinSimple.algebraMap_gen, hα₁,
        IsScalarTower.algebraMap_apply A K K⟮α₁⟯, ← IsScalarTower.algebraMap_apply K K⟮α₁⟯ E',
        ← IsScalarTower.algebraMap_apply A K E']
  have hdeg := IsDiscreteValuationRing.finrank_eq_of_pow_eq_of_irreducible hπ hαK
    (_root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top α₁)
  have : FiniteDimensional K K⟮α₁⟯ := Module.finite_of_finrank_pos (hdeg ▸ he)
  have : IsFractionRing (integralClosure A K⟮α₁⟯) K⟮α₁⟯ :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K K⟮α₁⟯ _
  have : IsScalarTower (integralClosure A K⟮α₁⟯) K⟮α₁⟯ L⟮α₁⟯ := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A L E' := .to₁₃₄ A K L E'
  have hintL : IsIntegral L α₁ :=
    (IsIntegral.of_pow he (hα₁ ▸ isIntegral_algebraMap (R := A))).tower_top
  have hsurj := TauCeti.IntermediateField.surjective_adjoinBaseChange_tensorProduct K L hintL
  obtain ⟨_, _⟩ := AlgHom.finiteDimensional_and_isSeparable_of_surjective
    (TauCeti.IntermediateField.adjoinBaseChangeTensorLift K L α₁) hsurj
  have hFin : Module.Finite (integralClosure A K⟮α₁⟯)
      (integralClosure (integralClosure A K⟮α₁⟯) L⟮α₁⟯) :=
    IsIntegralClosure.finite (integralClosure A K⟮α₁⟯) K⟮α₁⟯ L⟮α₁⟯
      (integralClosure (integralClosure A K⟮α₁⟯) L⟮α₁⟯)
  exact ⟨hDVR, (isUnramifiedWRT_iff_etale (integralClosure A K⟮α₁⟯) K⟮α₁⟯ L⟮α₁⟯).mp hunr, hFin⟩

/-- Tensoring a unit standard tame cover `S' = A'₁[y]/(y ^ e - u₁)` over `A₁` with a finite étale
`A₁`-algebra `B_E` produces a finite étale `A'₁`-algebra whose generic fibre maps onto `E'` whenever
`E'` is generated as a ring by `K'₁`, an `e`-th root `γ₁` of `u₁`, and the image of `B_E`. -/
private theorem isUnramifiedWRT_of_standardTameCover_tensor
    {A₁ B_E A'₁ : Type*} (K'₁ : Type*) {E' : Type*} [CommRing A₁] [CommRing B_E] [Algebra A₁ B_E]
    [CommRing A'₁] [IsDomain A'₁] [IsDiscreteValuationRing A'₁]
    [Field K'₁] [Algebra A'₁ K'₁] [IsFractionRing A'₁ K'₁]
    [Field E'] [Algebra K'₁ E'] [Algebra A'₁ E'] [IsScalarTower A'₁ K'₁ E']
    (hEtale : Algebra.Etale A₁ B_E) (hFin : Module.Finite A₁ B_E)
    {u₁ : A'₁} (hu₁ : IsUnit u₁) {e : ℕ} (heA'₁ : IsUnit (e : A'₁))
    {γ₁ : E'} (hγ₁ : γ₁ ^ e = algebraMap A'₁ E' u₁)
    (f : A₁ →+* standardTameCover A'₁ u₁ e) (gB_ring : B_E →+* E')
    (hcomp : ∀ a₁ : A₁, gB_ring (algebraMap A₁ B_E a₁) =
      AdjoinRoot.liftAlgHom (X ^ e - C u₁) (Algebra.ofId A'₁ E') γ₁ (by simp [hγ₁]) (f a₁))
    (hgenE' : ∀ R : Subring E',
      (∀ x : K'₁, algebraMap K'₁ E' x ∈ R) → γ₁ ∈ R → (∀ b : B_E, gB_ring b ∈ R) →
        ∀ z : E', z ∈ R) :
    IsUnramifiedWRT A'₁ E' := by
  have := hEtale; have := hFin
  have : NeZero e := ⟨by rintro rfl; simp at heA'₁⟩
  let S' := standardTameCover A'₁ u₁ e
  have : Algebra.Etale A'₁ S' := standardTameCover_etale hu₁ heA'₁
  let ψS' : S' →ₐ[A'₁] E' :=
    AdjoinRoot.liftAlgHom (X ^ e - C u₁) (Algebra.ofId A'₁ E') γ₁ (by simp [hγ₁])
  let : Algebra A₁ S' := f.toAlgebra
  let : Algebra A₁ E' := (ψS'.toRingHom.comp f).toAlgebra
  let ψS'_A₁ : S' →ₐ[A₁] E' := { toRingHom := ψS'.toRingHom, commutes' := fun _ ↦ rfl }
  let gB : B_E →ₐ[A₁] E' := { toRingHom := gB_ring, commutes' := hcomp }
  let T := S' ⊗[A₁] B_E
  have : IsScalarTower A'₁ S' T := .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.Etale A'₁ T := .comp A'₁ S' T
  have : Module.Finite A'₁ T := .trans S' T
  let ψT₀ : T →ₐ[A₁] E' :=
    Algebra.TensorProduct.lift (R := A₁) (S := A₁) ψS'_A₁ gB fun _ _ ↦ .all _ _
  let ψT : T →ₐ[A'₁] E' :=
    { toRingHom := ψT₀.toRingHom
      commutes' := fun a'₁ ↦ by simp [ψT₀, T, ψS'_A₁] }
  have hψT (s : S') (b : B_E) : ψT (s ⊗ₜ[A₁] b) = ψS' s * gB_ring b := by
    simp only [ψT, ψT₀, AlgHom.coe_mk, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [Algebra.TensorProduct.lift_tmul]
    rfl
  let χ : K'₁ ⊗[A'₁] T →ₐ[K'₁] E' :=
    Algebra.TensorProduct.lift (Algebra.ofId K'₁ E') ψT fun _ _ ↦ .all _ _
  have hχ : Function.Surjective χ := fun z ↦
    hgenE' χ.range.toSubring
      (fun x ↦ ⟨x ⊗ₜ 1, by simp [χ, Algebra.TensorProduct.lift_tmul]⟩)
      ⟨1 ⊗ₜ (AdjoinRoot.root (X ^ e - C u₁) ⊗ₜ 1), by
        simpa [χ, hψT] using AdjoinRoot.liftAlgHom_root ..⟩
      (fun b ↦ ⟨1 ⊗ₜ (1 ⊗ₜ b), by simp [χ, hψT]⟩) z
  exact χ.isUnramifiedWRT_of_surjective hχ

/-- Every subring `R` of `E' = L'(β', γ')` containing the image of `K'(β')`, `γ'`, and the images of
`φ (1 ⊗ b)` for all `b ∈ integralClosure A L` is all of `E'`. -/
private theorem mem_subring_compositum
    {A K L K' L' Ω' : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [Algebra.IsAlgebraic K L]
    [Field K'] [Algebra K K'] [Field L'] [Algebra K' L']
    [Field Ω'] [Algebra L' Ω'] [Algebra K' Ω'] [IsScalarTower K' L' Ω']
    (φ : K' ⊗[K] L →ₐ[K'] L') (hφ : Function.Surjective φ)
    {β' γ' : Ω'} (hβ'_alg : IsAlgebraic L' β') (hγ'_alg : IsAlgebraic L' γ') :
    let E' := ↥(_root_.IntermediateField.adjoin L' ({β', γ'} : Set Ω'))
    let β₁ : E' := ⟨β', subset_adjoin L' ({β', γ'} : Set Ω') (by simp)⟩
    let γ₁ : E' := ⟨γ', subset_adjoin L' ({β', γ'} : Set Ω') (by simp)⟩
    ∀ R : Subring E',
      (∀ x : K'⟮β₁⟯, algebraMap K'⟮β₁⟯ E' x ∈ R) →
      γ₁ ∈ R →
      (∀ b : integralClosure A L, algebraMap L' E' (φ ((1 : K') ⊗ₜ[K] (b : L))) ∈ R) →
      ∀ z : E', z ∈ R := by
  intro E' β₁ γ₁ R hK'₁ hγ₁ hB z
  have hk' (k' : K') : algebraMap K' E' k' ∈ R := by
    rw [IsScalarTower.algebraMap_apply K' K'⟮β₁⟯ E']
    exact hK'₁ (algebraMap K' K'⟮β₁⟯ k')
  let S_K' : Subalgebra K' L' :=
    { (R.comap (algebraMap L' E')) with
      algebraMap_mem' := fun k' ↦ by
        simpa [← IsScalarTower.algebraMap_apply K' L' E'] using hk' k' }
  have hspan : Submodule.span K'
      (Set.range fun b : integralClosure A L ↦ φ ((1 : K') ⊗ₜ[K] (b : L))) = ⊤ := by
    have h := congrArg (Submodule.map φ.toLinearMap)
      (span_one_tmul_integralClosure_eq_top (A := A) (K := K) (L := L) (K' := K'))
    rw [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.mpr hφ, ← Set.range_comp] at h
    exact h
  have hl' (l' : L') : algebraMap L' E' l' ∈ R := by
    have hle : (⊤ : Submodule K' L') ≤ S_K'.toSubmodule := by
      rw [← hspan, Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      exact hB b
    exact hle Submodule.mem_top
  let R₀ : Subalgebra L' E' := { R with algebraMap_mem' := hl' }
  have hβ₁R : β₁ ∈ R₀ := by
    rw [← AdjoinSimple.algebraMap_gen K' β₁]
    exact hK'₁ (AdjoinSimple.gen K' β₁)
  have hγ₁R : γ₁ ∈ R₀ := hγ₁
  have hadj : Algebra.adjoin L' ({β', γ'} : Set Ω') ≤
      R₀.map (_root_.IntermediateField.val _) := by
    refine Algebra.adjoin_le ?_
    rintro x (rfl | rfl)
    · exact ⟨β₁, hβ₁R, rfl⟩
    · exact ⟨γ₁, hγ₁R, rfl⟩
  have hz : z.1 ∈ Algebra.adjoin L' ({β', γ'} : Set Ω') := by
    rw [← adjoin_toSubalgebra_of_isAlgebraic]
    · exact z.2
    · rintro x (rfl | rfl)
      · exact hβ'_alg
      · exact hγ'_alg
  obtain ⟨y, hy, hyz⟩ := hadj hz
  exact Subtype.ext hyz ▸ hy

/-- When `π ∈ A` maps in `A'₁` to `u₁ * (b'₁ ^ e) ^ m`, the standard cover
`S' = A'₁[y]/(y ^ e - u₁)` receives `integralClosure A K(α₁)` (for `α₁ = γ₁ * b'₁ ^ m` and
`γ₁ ^ e = u₁` in `E'`) compatibly with evaluation at `γ₁` into `E'`. -/
private theorem exists_ringHom_standardTameCover_of_pow_eq
    {A K A'₁ E' : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing A'₁] [Algebra A A'₁]
    [Field E'] [Algebra A E'] [Algebra K E'] [IsScalarTower A K E']
    [Algebra A'₁ E'] [IsScalarTower A A'₁ E']
    {π : A} (hπ : Irreducible π) {u₁ b'₁ : A'₁} {m e : ℕ}
    (hπ_A'₁ : algebraMap A A'₁ π = u₁ * (b'₁ ^ e) ^ m)
    {γ₁ α₁ : E'} (hγ₁ : γ₁ ^ e = algebraMap A'₁ E' u₁)
    (hα₁_def : α₁ = γ₁ * algebraMap A'₁ E' b'₁ ^ m) :
    α₁ ^ e = algebraMap A E' π ∧
      ∃ f : integralClosure A K⟮α₁⟯ →+* standardTameCover A'₁ u₁ e,
        ∀ a₁ : integralClosure A K⟮α₁⟯,
          algebraMap K⟮α₁⟯ E' (a₁ : K⟮α₁⟯) = AdjoinRoot.liftAlgHom (X ^ e - C u₁)
            (Algebra.ofId A'₁ E') γ₁ (by simp [hγ₁]) (f a₁) := by
  let S' := standardTameCover A'₁ u₁ e
  let s : S' := AdjoinRoot.root (X ^ e - C u₁) * algebraMap A'₁ S' b'₁ ^ m
  have hs : s ^ e = algebraMap A S' π := by
    rw [IsScalarTower.algebraMap_apply A A'₁ S', hπ_A'₁]
    simp only [s, S', standardTameCover, mul_pow, AdjoinRoot.root_X_pow_sub_C_pow,
      AdjoinRoot.algebraMap_eq, map_mul, map_pow]
    ring
  let ψS' : S' →ₐ[A'₁] E' :=
    AdjoinRoot.liftAlgHom (X ^ e - C u₁) (Algebra.ofId A'₁ E') γ₁ (by simp [hγ₁])
  let ψS'_A : S' →ₐ[A] E' := ψS'.restrictScalars A
  have hψs : ψS'_A s = α₁ := by
    rw [AlgHom.restrictScalars_apply, map_mul, map_pow, AlgHom.commutes,
      AdjoinRoot.liftAlgHom_root, hα₁_def]
  have hα₁ : α₁ ^ e = algebraMap A E' π := by
    rw [← hψs, ← map_pow, hs, AlgHom.commutes]
  have hαK : AdjoinSimple.gen K α₁ ^ e = algebraMap A K⟮α₁⟯ π :=
    (algebraMap K⟮α₁⟯ E').injective <| by
      rw [map_pow, AdjoinSimple.algebraMap_gen, hα₁,
        IsScalarTower.algebraMap_apply A K K⟮α₁⟯, ← IsScalarTower.algebraMap_apply K K⟮α₁⟯ E',
        ← IsScalarTower.algebraMap_apply A K E']
  have hgenK := _root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top (F := K) α₁
  let ιA₁E' : integralClosure A K⟮α₁⟯ →ₐ[A] E' :=
    ((K⟮α₁⟯).val.restrictScalars A).comp (integralClosure A K⟮α₁⟯).val
  let fA₁ : integralClosure A K⟮α₁⟯ →ₐ[A] S' :=
    IsDiscreteValuationRing.liftIntegralClosureOfPowEq hπ hαK hgenK s hs
  have hfA₁ : ψS'_A.comp fA₁ = ιA₁E' :=
    (IsDiscreteValuationRing.powerBasisIntegralClosureOfPowEq hπ hαK hgenK).algHom_ext <| by
      rw [AlgHom.comp_apply]
      simp [fA₁, hψs, ιA₁E']
  exact ⟨hα₁, fA₁.toRingHom, fun a₁ ↦ (congrArg (· a₁) hfA₁).symm⟩

/-- In an extension `E'` equipped with compatible `A`, `K`, `L`, `A'`, and `K'`-algebra structures
and `e`-th roots `β₁` of `ϖ` and `γ₁` of `u`, `E'` is unramified over
`integralClosure A' K'(β₁)`. -/
private theorem isUnramifiedWRT_kummer_of_compositum
    {A : Type*} (K : Type*) {L A' K' E' : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A']
    [Field K'] [Algebra A' K'] [IsFractionRing A' K'] [Algebra A A']
    [Field E'] [Algebra A E'] [Algebra K E'] [Algebra L E']
    [Algebra A' E'] [Algebra K' E']
    [IsScalarTower A A' E'] [IsScalarTower A K E'] [IsScalarTower K L E'] [IsScalarTower A' K' E']
    (h : IsTamelyRamifiedWRT A L)
    {π : A} (hπ : Irreducible π) {ϖ : A'} (hϖ : Irreducible ϖ)
    {m e : ℕ} {u : A'ˣ} (hπ_eq : algebraMap A A' π = ↑u * ϖ ^ m)
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal], P.ramificationIdx A ∣ e)
    (heA' : IsUnit (e : A'))
    {β₁ γ₁ : E'} (hβ₁ : β₁ ^ e = algebraMap A' E' ϖ) (hγ₁ : γ₁ ^ e = algebraMap A' E' (u : A'))
    (hgenE' : ∀ R : Subring E',
      (∀ x : K'⟮β₁⟯, algebraMap K'⟮β₁⟯ E' x ∈ R) → γ₁ ∈ R →
      (∀ b : integralClosure A L, algebraMap L E' (b : L) ∈ R) →
      ∀ z : E', z ∈ R) :
    ∃ (_ : IsDiscreteValuationRing (integralClosure A' K'⟮β₁⟯)),
      IsUnramifiedWRT (integralClosure A' K'⟮β₁⟯) E' := by
  have he_pos : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at heA')
  have : IsScalarTower A L E' := .to₁₃₄ A K L E'
  have hβK' : AdjoinSimple.gen K' β₁ ^ e = algebraMap A' K'⟮β₁⟯ ϖ :=
    (algebraMap K'⟮β₁⟯ E').injective <| by
      rw [map_pow, AdjoinSimple.algebraMap_gen, hβ₁,
        IsScalarTower.algebraMap_apply A' K' K'⟮β₁⟯, ← IsScalarTower.algebraMap_apply K' K'⟮β₁⟯ E',
        ← IsScalarTower.algebraMap_apply A' K' E']
  have hgenβ' := _root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top (F := K') β₁
  have hDVR' :=
    IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible
      hϖ hβK' hgenβ'
  have : FiniteDimensional K' K'⟮β₁⟯ := Module.finite_of_finrank_pos
    ((IsDiscreteValuationRing.finrank_eq_of_pow_eq_of_irreducible hϖ hβK' hgenβ') ▸ he_pos)
  have : IsFractionRing (integralClosure A' K'⟮β₁⟯) K'⟮β₁⟯ :=
    IsIntegralClosure.isFractionRing_of_finite_extension A' K' K'⟮β₁⟯ _
  let A'₁ := integralClosure A' K'⟮β₁⟯
  let : Algebra A A'₁ := ((algebraMap A' A'₁).comp (algebraMap A A')).toAlgebra
  have : IsScalarTower A A' A'₁ := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A' K'⟮β₁⟯ E' := .to₁₃₄ A' K' K'⟮β₁⟯ E'
  have : IsScalarTower A' A'₁ E' := IsScalarTower.subalgebra' A' K'⟮β₁⟯ E' A'₁
  have : IsScalarTower A A'₁ E' := .to₁₃₄ A A' A'₁ E'
  let b'₁ : A'₁ := ⟨AdjoinSimple.gen K' β₁, IsIntegral.of_pow he_pos (hβK' ▸ isIntegral_algebraMap)⟩
  have hb'₁_pow : b'₁ ^ e = algebraMap A' A'₁ ϖ :=
    Subtype.ext (by simpa only [Subalgebra.coe_pow, Subalgebra.coe_algebraMap] using hβK')
  have hπ_A'₁ : algebraMap A A'₁ π = algebraMap A' A'₁ u * (b'₁ ^ e) ^ m := by
    rw [hb'₁_pow, ← map_pow, ← map_mul, ← hπ_eq, ← IsScalarTower.algebraMap_apply A A' A'₁]
  have hγ₁_A'₁ : γ₁ ^ e = algebraMap A'₁ E' (algebraMap A' A'₁ u) := by
    rwa [← IsScalarTower.algebraMap_apply A' A'₁ E']
  let α₁ : E' := γ₁ * algebraMap A'₁ E' b'₁ ^ m
  obtain ⟨hα₁, fA₁, hfA₁⟩ :=
    exists_ringHom_standardTameCover_of_pow_eq (K := K) hπ hπ_A'₁ hγ₁_A'₁ (α₁ := α₁) rfl
  let := (TauCeti.IntermediateField.adjoinBaseChange K L α₁).toAlgebra
  obtain ⟨_, hEtale, hFin⟩ := etale_integralClosure_adjoin_of_tame K h hπ he_pos hα₁ hdvd
  have : IsScalarTower A K L⟮α₁⟯ := .to₁₂₄ A K L L⟮α₁⟯
  have : IsScalarTower A K⟮α₁⟯ L⟮α₁⟯ :=
    IsScalarTower.of_algHom ((TauCeti.IntermediateField.adjoinBaseChange K L α₁).restrictScalars A)
  have : IsScalarTower (integralClosure A K⟮α₁⟯) K⟮α₁⟯ L⟮α₁⟯ := .of_algebraMap_eq fun _ ↦ rfl
  let B_E := integralClosure (integralClosure A K⟮α₁⟯) L⟮α₁⟯
  let gB : B_E →+* E' := (L⟮α₁⟯).val.toRingHom.comp B_E.val.toRingHom
  refine ⟨hDVR', isUnramifiedWRT_of_standardTameCover_tensor K'⟮β₁⟯ hEtale hFin
    (u.isUnit.map _) (by simpa using heA'.map (algebraMap A' A'₁)) hγ₁_A'₁ fA₁ gB
    (fun a₁ ↦ by
      simpa [gB, B_E, IsScalarTower.algebraMap_apply (integralClosure A K⟮α₁⟯) K⟮α₁⟯ L⟮α₁⟯,
        AlgHom.algebraMap_toAlgebra_apply] using hfA₁ a₁)
    fun R hK'₁ hγR hBR ↦ hgenE' R hK'₁ hγR fun b ↦
      hBR (⟨algebraMap L L⟮α₁⟯ b, (b.2.map (IsScalarTower.toAlgHom A L L⟮α₁⟯)).tower_top⟩ : B_E)⟩

/-- Deducing `IsTamelyRamifiedWRT A' L'` once an extension `E' / L'` has been constructed with
`e`-th roots `β₁` of a uniformizer `ϖ` of `A'` and `γ₁` of the unit `u` from `π = u * ϖ ^ m`. -/
private theorem isTamelyRamifiedWRT_of_kummer_compositum
    {A K L A' K' L' E' : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A']
    [Field K'] [Algebra A' K'] [IsFractionRing A' K']
    [Algebra A A'] [Algebra A K'] [Algebra K K'] [IsScalarTower A A' K'] [IsScalarTower A K K']
    [Field L'] [Algebra K' L'] [Algebra A' L'] [IsScalarTower A' K' L'] [FiniteDimensional K' L']
    [Field E'] [Algebra A' E'] [Algebra K' E'] [Algebra L' E']
    [IsScalarTower A' K' E'] [IsScalarTower K' L' E']
    (h : IsTamelyRamifiedWRT A L) (φ : K' ⊗[K] L →ₐ[K'] L')
    {π : A} (hπ : Irreducible π) {ϖ : A'} (hϖ : Irreducible ϖ)
    {m e : ℕ} {u : A'ˣ} (hπ_eq : algebraMap A A' π = ↑u * ϖ ^ m)
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal], P.ramificationIdx A ∣ e)
    (heA' : IsUnit (e : A'))
    {β₁ γ₁ : E'} (hβ₁ : β₁ ^ e = algebraMap A' E' ϖ) (hγ₁ : γ₁ ^ e = algebraMap A' E' (u : A'))
    (hgenE' : ∀ R : Subring E',
      (∀ x : K'⟮β₁⟯, algebraMap K'⟮β₁⟯ E' x ∈ R) → γ₁ ∈ R →
      (∀ b : integralClosure A L, algebraMap L' E' (φ ((1 : K') ⊗ₜ[K] (b : L))) ∈ R) →
      ∀ z : E', z ∈ R) :
    IsTamelyRamifiedWRT A' L' := by
  let : Algebra A E' := ((algebraMap A' E').comp (algebraMap A A')).toAlgebra
  let : Algebra K E' := ((algebraMap K' E').comp (algebraMap K K')).toAlgebra
  let : Algebra L E' := ((algebraMap L' E').comp (φ.toRingHom.comp
    (Algebra.TensorProduct.includeRight : L →ₐ[K] K' ⊗[K] L).toRingHom)).toAlgebra
  have : IsScalarTower A A' E' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A K' E' := .to₁₃₄ A A' K' E'
  have : IsScalarTower K K' E' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A K E' := .to₁₂₄ A K K' E'
  have : IsScalarTower K L E' := .of_algebraMap_eq fun k ↦ by
    simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply K K' (K' ⊗[K] L), AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply K' L' E']
  obtain ⟨_, hunrE'⟩ := isUnramifiedWRT_kummer_of_compositum K h hπ hϖ hπ_eq hdvd heA'
    hβ₁ hγ₁ hgenE'
  have he_res' : IsUnit (e : A' ⧸ maximalIdeal A') := by
    simpa using heA'.map (Ideal.Quotient.mk (maximalIdeal A'))
  exact IsDiscreteValuationRing.isTamelyRamifiedWRT_of_isUnramifiedWRT_of_pow_eq_of_irreducible
    hϖ he_res' hβ₁ hunrE'

end Helpers

section BaseChange

variable {A K L A' K' L' : Type*}
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A'] [Field K'] [Algebra A' K']
  [IsFractionRing A' K'] [Algebra A A'] [Algebra A K'] [Algebra K K'] [IsScalarTower A A' K']
  [IsScalarTower A K K'] [Field L'] [Algebra K' L'] [Algebra A' L'] [IsScalarTower A' K' L']

/-- Let `A → A'` be a map of discrete valuation rings with compatible fraction fields `K → K'` (not
required to be local), and let `L / K` be a finite separable extension. If `L` is tamely ramified
with respect to `A`, then every field factor `L'` of `K' ⊗[K] L`, given by a surjective `K'`-algebra
map `φ : K' ⊗[K] L →ₐ[K'] L'`, is tamely ramified with respect to `A'`. -/
@[stacks 0EXY "tamely ramified case"]
theorem IsTamelyRamifiedWRT.baseChange (h : IsTamelyRamifiedWRT A L) (φ : K' ⊗[K] L →ₐ[K'] L')
    (hφ : Function.Surjective φ) : IsTamelyRamifiedWRT A' L' := by
  have : FiniteDimensional K' L' := .of_surjective φ.toLinearMap hφ
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A'
  have : FaithfulSMul A K' := .trans A K K'
  have : FaithfulSMul A A' := .tower_bot A A' K'
  obtain ⟨m, u, hπ_eq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A A')).mpr hπ.ne_zero) hϖ
  obtain ⟨e, he_res, hdvd⟩ := h.exists_isUnit_forall_ramificationIdx_dvd K
  have heA : IsUnit (e : A) :=
    (isUnit_map_iff (IsLocalRing.residue A) _).mp (by rw [map_natCast]; exact he_res)
  have heA' : IsUnit (e : A') := by simpa using heA.map (algebraMap A A')
  have he_pos : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at heA)
  let Ω' := AlgebraicClosure L'
  have : IsScalarTower A' K' Ω' := .to₁₂₄ A' K' L' Ω'
  obtain ⟨β', hβ'⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A' Ω' ϖ) he_pos
  obtain ⟨γ', hγ'⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A' Ω' (u : A')) he_pos
  let F' := _root_.IntermediateField.adjoin L' ({β', γ'} : Set Ω')
  have : IsScalarTower A' K' F' := .to₁₂₄ A' K' L' F'
  let β₁ : F' := ⟨β', subset_adjoin L' ({β', γ'} : Set Ω') (by simp)⟩
  let γ₁ : F' := ⟨γ', subset_adjoin L' ({β', γ'} : Set Ω') (by simp)⟩
  have hβ₁ : β₁ ^ e = algebraMap A' F' ϖ :=
    (algebraMap F' Ω').injective <| by
      rw [map_pow, IntermediateField.algebraMap_apply, hβ',
        IsScalarTower.algebraMap_apply A' L' F', ← IsScalarTower.algebraMap_apply L' F' Ω',
        ← IsScalarTower.algebraMap_apply A' L' Ω']
  have hγ₁ : γ₁ ^ e = algebraMap A' F' (u : A') :=
    (algebraMap F' Ω').injective <| by
      rw [map_pow, IntermediateField.algebraMap_apply, hγ',
        IsScalarTower.algebraMap_apply A' L' F', ← IsScalarTower.algebraMap_apply L' F' Ω',
        ← IsScalarTower.algebraMap_apply A' L' Ω']
  exact isTamelyRamifiedWRT_of_kummer_compositum h φ hπ hϖ hπ_eq hdvd heA' hβ₁ hγ₁
    (mem_subring_compositum φ hφ
      (IsIntegral.of_pow he_pos (hβ' ▸ isIntegral_algebraMap (R := A'))).tower_top.isAlgebraic
      (IsIntegral.of_pow he_pos (hγ' ▸ isIntegral_algebraMap (R := A'))).tower_top.isAlgebraic)

end BaseChange

end TauCeti.Algebra
