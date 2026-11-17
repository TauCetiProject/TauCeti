/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.TamelyRamified
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.Basic
import TauCeti.RingTheory.DiscreteValuationRing.AbhyankarLemma
import TauCeti.RingTheory.DiscreteValuationRing.BaseChange.Unramified
import TauCeti.RingTheory.DiscreteValuationRing.Kummer
import TauCeti.RingTheory.IntegralClosure.TensorProduct

/-!
# Base change of tamely ramified extensions of a discrete valuation ring

Let `A → A'` be a ring map of discrete valuation rings with compatible fraction fields `K → K'`,
not necessarily local, and let `L / K` be a finite separable extension. The algebra `K' ⊗[K] L` is
a finite product of fields, and its factors are the fields `L'` receiving a surjective
`K'`-algebra map `φ : K' ⊗[K] L → L'`. If `L` is tamely ramified with respect to `A`, then every
such factor `L'` is tamely ramified with respect to `A'`
(`TauCeti.Algebra.IsTamelyRamifiedWRT.baseChange`, Stacks, Lemma 15.116.9 (0EXY), the tamely
ramified case).

## Main results

* `TauCeti.Algebra.IsTamelyRamifiedWRT.baseChange`: every factor of `K' ⊗[K] L` is tamely ramified
  with respect to `A'` when `L` is tamely ramified with respect to `A`
  (Stacks, Lemma 15.116.9 (0EXY)).

## References

* [Stacks Project, Lemma 15.116.9](https://stacks.math.columbia.edu/tag/0EXY).
-/

public section

open IntermediateField IsLocalRing Polynomial
open scoped TensorProduct

namespace TauCeti.Algebra

-- Map an `A`-algebra `A₁ ≃ A[x]/(x^e − π)` to the standard tame cover `T = A'₁[y]/(y^e − u')` by
-- `x ↦ y · β ^ r` when `π = u' π' ^ r` and `β ^ e = π'`, compatibly with embeddings into `Ω`.
private theorem exists_algHom_standardTameCover
    {A A' A₁ A'₁ Ω : Type*}
    [CommRing A] [CommRing A'] [CommRing A₁] [CommRing A'₁] [CommRing Ω]
    [Algebra A A'] [Algebra A A₁] [Algebra A' A'₁] [Algebra A Ω] [Algebra A' Ω]
    [Algebra A₁ Ω] [Algebra A'₁ Ω]
    [IsScalarTower A A' Ω] [IsScalarTower A A₁ Ω] [IsScalarTower A' A'₁ Ω]
    {π : A} {π' : A'} {r : ℕ} {u' : A'ˣ} (hπA' : algebraMap A A' π = (u' : A') * π' ^ r)
    {e : ℕ} {βA'₁ : A'₁} (hβ : βA'₁ ^ e = algebraMap A' A'₁ π')
    {p : A[X]} (hp : p = X ^ e - C π) (eA₁ : A₁ ≃ₐ[A] AdjoinRoot p)
    {γ : Ω} (hγ : γ ^ e = algebraMap A' Ω u')
    (hroot : algebraMap A₁ Ω (eA₁.symm (AdjoinRoot.root p)) =
      γ * algebraMap A'₁ Ω βA'₁ ^ r) :
    let T := TauCeti.standardTameCover A'₁ (algebraMap A' A'₁ u') e
    letI : Algebra A T := ((algebraMap A'₁ T).comp ((algebraMap A' A'₁).comp
      (algebraMap A A'))).toAlgebra
    ∃ (f : A₁ →ₐ[A] T) (gT : T →ₐ[A'₁] Ω),
      ∀ x : A₁, gT (f x) = algebraMap A₁ Ω x := by
  subst hp
  let T := TauCeti.standardTameCover A'₁ (algebraMap A' A'₁ u') e
  let : Algebra A T := ((algebraMap A'₁ T).comp ((algebraMap A' A'₁).comp
    (algebraMap A A'))).toAlgebra
  let img : T := AdjoinRoot.root (X ^ e - C (algebraMap A' A'₁ u')) *
    algebraMap A'₁ T (βA'₁ ^ r)
  have hy : AdjoinRoot.root (X ^ e - C (algebraMap A' A'₁ u')) ^ e =
      algebraMap A'₁ T (algebraMap A' A'₁ u') := by
    have h0 := AdjoinRoot.eval₂_root (X ^ e - C (algebraMap A' A'₁ u'))
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h0
    exact h0
  have himg_pow : img ^ e = algebraMap A T π :=
    calc img ^ e = algebraMap A'₁ T (algebraMap A' A'₁ u') *
            algebraMap A'₁ T ((βA'₁ ^ e) ^ r) := by
          rw [mul_pow, hy, ← map_pow, ← pow_mul, mul_comm r e, pow_mul]
      _ = algebraMap A'₁ T (algebraMap A' A'₁ ((u' : A') * π' ^ r)) := by
          rw [hβ, ← map_pow, ← map_mul, ← map_mul]
      _ = algebraMap A T π := by
          rw [← hπA', RingHom.algebraMap_toAlgebra, RingHom.comp_apply, RingHom.comp_apply]
  have himg : eval₂ (Algebra.ofId A T) img (X ^ e - C π) = 0 := by
    simp [himg_pow]
  let liftF := AdjoinRoot.liftAlgHom (X ^ e - C π) (Algebra.ofId A T) img himg
  let f : A₁ →ₐ[A] T := liftF.comp eA₁.toAlgHom
  have hγ_root : eval₂ (Algebra.ofId A'₁ Ω) γ (X ^ e - C (algebraMap A' A'₁ u')) = 0 := by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, AlgHom.coe_toRingHom, Algebra.ofId_apply,
      ← IsScalarTower.algebraMap_apply A' A'₁ Ω, hγ, sub_self]
  let gT : T →ₐ[A'₁] Ω :=
    AdjoinRoot.liftAlgHom (X ^ e - C (algebraMap A' A'₁ u')) (Algebra.ofId A'₁ Ω) γ hγ_root
  refine ⟨f, gT, fun x ↦ ?_⟩
  have hgT_A (a : A) : gT (algebraMap A T a) = algebraMap A Ω a := by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, RingHom.comp_apply, gT.commutes,
      ← IsScalarTower.algebraMap_apply A' A'₁ Ω, ← IsScalarTower.algebraMap_apply A A' Ω]
  let lhs : TauCeti.standardTameCover A π e →ₐ[A] Ω :=
    { gT.toRingHom.comp liftF.toRingHom with
      commutes' := fun a ↦ by
        simp only [RingHom.toFun_eq_coe, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, liftF.commutes, hgT_A] }
  let rhs : TauCeti.standardTameCover A π e →ₐ[A] Ω :=
    (IsScalarTower.toAlgHom A A₁ Ω).comp eA₁.symm.toAlgHom
  have hagree : lhs = rhs := AdjoinRoot.algHom_ext <| by
    simp only [lhs, rhs, liftF, AlgHom.coe_mk, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, AdjoinRoot.liftAlgHom_root, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      IsScalarTower.coe_toAlgHom', img, map_mul, map_pow, gT, AlgHom.commutes]
    rw [AdjoinRoot.liftAlgHom_root, hroot]
  simpa only [f, lhs, rhs, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_mk,
    RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.symm_apply_apply,
    IsScalarTower.coe_toAlgHom'] using AlgHom.congr_fun hagree (eA₁ x)

-- Specialize `exists_algHom_standardTameCover` to the Kummer DVRs `A₁ = integralClosure A K(α)`
-- and `A'₁ = integralClosure A' K'(β)` when `α = γ β ^ r`, `α ^ e = π`, `β ^ e = π'`, `γ ^ e = u'`.
private theorem exists_algHom_integralClosure_standardTameCover
    {A K A' K' Ω : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] [CommRing A'] [Field K'] [Algebra A' K'] [Algebra A A']
    [Field Ω] [Algebra A Ω] [Algebra K Ω] [Algebra A' Ω] [Algebra K' Ω]
    [IsScalarTower A K Ω] [IsScalarTower A' K' Ω] [IsScalarTower A A' Ω]
    {π : A} (hπ : Irreducible π) {π' : A'} {r : ℕ} {u' : A'ˣ}
    (hπA' : algebraMap A A' π = (u' : A') * π' ^ r)
    {e : ℕ} (he0 : e ≠ 0) {α β γ : Ω}
    (hαK : AdjoinSimple.gen K α ^ e = algebraMap A K⟮α⟯ π)
    (hβK' : AdjoinSimple.gen K' β ^ e = algebraMap A' K'⟮β⟯ π')
    (hγ : γ ^ e = algebraMap A' Ω u') (hα_eq : α = γ * β ^ r) :
    let A₁ := integralClosure A K⟮α⟯
    let A'₁ := integralClosure A' K'⟮β⟯
    let T := TauCeti.standardTameCover A'₁ (algebraMap A' A'₁ u') e
    letI : Algebra A T := ((algebraMap A'₁ T).comp ((algebraMap A' A'₁).comp
      (algebraMap A A'))).toAlgebra
    ∃ (f : A₁ →ₐ[A] T) (gT : T →ₐ[A'₁] Ω),
      ∀ x : A₁, gT (f x) = algebraMap A₁ Ω x := by
  let A₁ := integralClosure A K⟮α⟯
  let A'₁ := integralClosure A' K'⟮β⟯
  have : IsScalarTower A A₁ Ω := .of_algebraMap_eq fun a ↦ by
    rw [Subalgebra.algebraMap_def, Subalgebra.coe_algebraMap,
      IsScalarTower.algebraMap_apply A K K⟮α⟯,
      ← IsScalarTower.algebraMap_apply K K⟮α⟯ Ω,
      ← IsScalarTower.algebraMap_apply A K Ω]
  have : IsScalarTower A' A'₁ Ω := .of_algebraMap_eq fun a' ↦ by
    rw [Subalgebra.algebraMap_def, Subalgebra.coe_algebraMap,
      IsScalarTower.algebraMap_apply A' K' K'⟮β⟯,
      ← IsScalarTower.algebraMap_apply K' K'⟮β⟯ Ω,
      ← IsScalarTower.algebraMap_apply A' K' Ω]
  have hβA'₁_mem : AdjoinSimple.gen K' β ∈ A'₁ := (mem_integralClosure_iff _ _).mpr
    (IsIntegral.of_pow (Nat.pos_of_ne_zero he0) (hβK' ▸ isIntegral_algebraMap))
  let βA'₁ : A'₁ := ⟨AdjoinSimple.gen K' β, hβA'₁_mem⟩
  have hβA'₁_pow : βA'₁ ^ e = algebraMap A' A'₁ π' := Subtype.ext (by
    simpa [βA'₁, Subalgebra.coe_algebraMap] using hβK')
  have : FaithfulSMul A K⟮α⟯ := .trans A K K⟮α⟯
  have : Module.IsTorsionFree A K⟮α⟯ := FaithfulSMul.to_isTorsionFree ..
  have hαint : IsIntegral A (AdjoinSimple.gen K α) :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero he0) (hαK ▸ isIntegral_algebraMap)
  have hmin : minpoly A (AdjoinSimple.gen K α) = X ^ e - C π :=
    IsDiscreteValuationRing.minpoly_eq_of_pow_eq_of_irreducible hπ hαK
  have heqA₁ : A₁ = Algebra.adjoin A {AdjoinSimple.gen K α} :=
    IsDiscreteValuationRing.integralClosure_eq_adjoin_of_pow_eq_of_irreducible hπ hαK
      (adjoin_adjoinSimple_gen_eq_top α)
  let eA₁ : A₁ ≃ₐ[A] AdjoinRoot (minpoly A (AdjoinSimple.gen K α)) :=
    (Subalgebra.equivOfEq _ _ heqA₁).trans (minpoly.equivAdjoin hαint).symm
  have hroot : algebraMap A₁ Ω
      (eA₁.symm (AdjoinRoot.root (minpoly A (AdjoinSimple.gen K α)))) =
      γ * algebraMap A'₁ Ω βA'₁ ^ r := by
    have h2 : minpoly.equivAdjoin hαint (AdjoinRoot.root (minpoly A (AdjoinSimple.gen K α))) =
        ⟨AdjoinSimple.gen K α, Algebra.subset_adjoin rfl⟩ := by
      rw [minpoly.coe_equivAdjoin, AdjoinRoot.Minpoly.toAdjoin, AdjoinRoot.liftAlgHom_root]
    have h1 : (eA₁.symm (AdjoinRoot.root (minpoly A (AdjoinSimple.gen K α))) : K⟮α⟯) =
        AdjoinSimple.gen K α := by
      simp [eA₁, h2]
    exact (congrArg (IntermediateField.val K⟮α⟯) h1).trans hα_eq
  exact exists_algHom_standardTameCover hπA' hβA'₁_pow hmin eA₁ hγ hroot

-- Given an unramified extension `L₁ / K₁` over `A₁` (`B₁ = integralClosure A₁ L₁` finite étale
-- over `A₁`), a finite étale `A'₁`-algebra `T` receiving `A₁`, and compatible embeddings into `Ω`,
-- the image `E ⊆ Ω` of `K'₁ ⊗[A'₁] (T ⊗[A₁] B₁)` is unramified over `A'₁` and contains `L'`.
private theorem exists_unramified_overfield_of_etale_cover
    {A K L K' L' A₁ K₁ L₁ A'₁ K'₁ T Ω : Type*}
    [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [Algebra.IsAlgebraic K L]
    [Field K'] [Algebra K K'] [Field L'] [Algebra K' L']
    (φ : K' ⊗[K] L →ₐ[K'] L') (hφ : Function.Surjective φ)
    [CommRing A₁] [IsDomain A₁] [IsDiscreteValuationRing A₁] [Algebra A A₁]
    [Field K₁] [Algebra A₁ K₁] [IsFractionRing A₁ K₁]
    [Field L₁] [Algebra L L₁] [Algebra K₁ L₁] [Algebra A L₁] [Algebra A₁ L₁]
    [IsScalarTower A L L₁] [IsScalarTower A A₁ L₁] [IsScalarTower A₁ K₁ L₁]
    [FiniteDimensional K₁ L₁] [Algebra.IsSeparable K₁ L₁]
    (hU : IsUnramifiedWRT A₁ L₁)
    [CommRing A'₁] [IsDomain A'₁] [IsDiscreteValuationRing A'₁]
    [Field K'₁] [Algebra K' K'₁] [Algebra A'₁ K'₁] [IsFractionRing A'₁ K'₁]
    [CommRing T] [Algebra A'₁ T] [Algebra A T] [Algebra.Etale A'₁ T] [Module.Finite A'₁ T]
    [Field Ω] [Algebra L' Ω] [Algebra K' Ω] [Algebra K'₁ Ω] [Algebra A'₁ Ω]
    [Algebra A₁ Ω] [Algebra L₁ Ω] [IsScalarTower K' L' Ω] [IsScalarTower K' K'₁ Ω]
    [IsScalarTower A'₁ K'₁ Ω] [IsScalarTower A₁ L₁ Ω]
    (f : A₁ →ₐ[A] T) (gT : T →ₐ[A'₁] Ω)
    (hfg : ∀ x : A₁, gT (f x) = algebraMap A₁ Ω x)
    (hL : ∀ x : L, algebraMap L₁ Ω (algebraMap L L₁ x) =
      algebraMap L' Ω (φ ((1 : K') ⊗ₜ[K] x))) :
    ∃ E : IntermediateField K'₁ Ω,
      IsUnramifiedWRT A'₁ E ∧ ∀ z : L', algebraMap L' Ω z ∈ E := by
  let B₁ := integralClosure A₁ L₁
  have : Algebra.Etale A₁ B₁ := (isUnramifiedWRT_iff_etale A₁ K₁ L₁).mp hU
  have : Module.Finite A₁ B₁ := IsIntegralClosure.finite A₁ K₁ L₁ _
  let : Algebra A₁ T := f.toAlgebra
  let S := T ⊗[A₁] B₁
  have : Algebra.Etale T S := inferInstance
  have : Module.Finite T S := inferInstance
  have : Algebra.Etale A'₁ S := Algebra.Etale.comp A'₁ T S
  have : Module.Finite A'₁ S := .trans T S
  let gT_A₁ : T →ₐ[A₁] Ω := { gT.toRingHom with commutes' := fun x ↦ hfg x }
  let gB₁ : B₁ →ₐ[A₁] Ω := (IsScalarTower.toAlgHom A₁ L₁ Ω).comp B₁.val
  let ψ_A₁ : S →ₐ[A₁] Ω := Algebra.TensorProduct.lift gT_A₁ gB₁ fun _ _ ↦ .all _ _
  let ψ : S →ₐ[A'₁] Ω :=
    { ψ_A₁.toRingHom with
      commutes' := fun a' ↦ by
        simp only [S, RingHom.toFun_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.algebraMap_apply, ψ_A₁, Algebra.TensorProduct.lift_tmul,
          gT_A₁, AlgHom.coe_mk, gT.commutes, map_one, mul_one] }
  let χ₀ : K'₁ ⊗[A'₁] S →ₐ[K'₁] Ω :=
    Algebra.TensorProduct.lift (Algebra.ofId K'₁ Ω) ψ fun _ _ ↦ .all _ _
  have : Module.Finite K'₁ (K'₁ ⊗[A'₁] S) := inferInstance
  have : Module.Finite K'₁ χ₀.range :=
    Module.Finite.of_surjective χ₀.rangeRestrict.toLinearMap χ₀.rangeRestrict_surjective
  let E : IntermediateField K'₁ Ω :=
    χ₀.range.toIntermediateField' (isField_of_isIntegral_of_isField' (Field.toIsField K'₁))
  let χ : K'₁ ⊗[A'₁] S →ₐ[K'₁] E :=
    { toRingHom := χ₀.toRingHom.codRestrict E.toSubring fun x ↦ ⟨x, rfl⟩
      commutes' := fun k ↦ Subtype.ext (χ₀.commutes k) }
  have hχ : Function.Surjective χ := fun ⟨_, x, hx⟩ ↦ ⟨x, Subtype.ext hx⟩
  refine ⟨E, χ.isUnramifiedWRT_of_surjective hχ, ?_⟩
  -- `L'` is spanned over `K'` by `{φ (1 ⊗ₜ b) | b ∈ integralClosure A L}`, which land in `E`.
  have hspan := TauCeti.span_map_one_tmul_integralClosure_eq_top (A := A) φ.toLinearMap hφ
  have hsub : Submodule.map (IsScalarTower.toAlgHom K' L' Ω).toLinearMap ⊤ ≤
      E.toSubalgebra.toSubmodule.restrictScalars K' := by
    rw [← hspan, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    have hbB₁ : algebraMap L L₁ b ∈ B₁ :=
      (b.2.map (IsScalarTower.toAlgHom A L L₁)).tower_top
    let b₁ : B₁ := ⟨algebraMap L L₁ b, hbB₁⟩
    refine ⟨1 ⊗ₜ[A'₁] (1 ⊗ₜ[A₁] b₁), ?_⟩
    dsimp only [χ₀, ψ, ψ_A₁, gB₁, S]
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, map_one,
      one_mul, AlgHom.coe_mk, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact hL b
  exact fun z ↦ hsub ⟨z, Submodule.mem_top, rfl⟩

variable {A K L A' K' L' : Type*}
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A'] [Field K'] [Algebra A' K']
  [IsFractionRing A' K'] [Algebra A A'] [Algebra A K'] [Algebra K K'] [IsScalarTower A A' K']
  [IsScalarTower A K K'] [Field L'] [Algebra K' L'] [Algebra A' L'] [IsScalarTower A' K' L']

/-- A uniformizer `π` of `A` maps to a nonzero element of `A'` and therefore factors as
`u' * π' ^ r` for a unit `u'` and a uniformizer `π'` of `A'` (with `r = 0` when `A → A'` is
non-local). -/
private theorem exists_uniformizer_eq_unit_mul_pow (K K' : Type*)
    [Field K] [Algebra A K] [IsFractionRing A K] [Field K'] [Algebra A' K']
    [Algebra A K'] [Algebra K K'] [IsScalarTower A A' K']
    [IsScalarTower A K K'] {π : A} (hπ : Irreducible π) {π' : A'} (hπ' : Irreducible π') :
    ∃ (r : ℕ) (u' : A'ˣ), algebraMap A A' π = (u' : A') * π' ^ r := by
  have hπA'_ne : algebraMap A A' π ≠ 0 := fun h0 ↦ hπ.ne_zero <| by
    have hK' : algebraMap K K' (algebraMap A K π) = 0 := by
      rw [← IsScalarTower.algebraMap_apply A K K', IsScalarTower.algebraMap_apply A A' K', h0,
        map_zero]
    exact IsFractionRing.injective A K ((algebraMap K K').injective (by simpa using hK'))
  exact IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπA'_ne hπ'

-- Tame base change inside an opaque algebraically closed overfield `Ω` of `L'`, avoiding `whnf`
-- unfolding of `AlgebraicClosure L'` inside `IntermediateField` instances: write `π = u' π' ^ r`,
-- extract `e`-th roots `β` of `π'` and `γ` of `u'`, set `α = γ β ^ r`, apply global Abhyankar's
-- lemma to `L(α) / K(α)`, base-change along `A₁ → T = A'₁[y]/(y^e − u')`, and descend from the
-- resulting unramified overfield `E ⊇ L'` over `A'₁ = integralClosure A' K'(β)`.
private theorem isTamelyRamifiedWRT_baseChange_of_isAlgClosed
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
    [Algebra A Ω] [Algebra K Ω] [Algebra L Ω] [Algebra A' Ω] [Algebra K' Ω] [Algebra L' Ω]
    [IsScalarTower A K Ω] [IsScalarTower K L Ω] [IsScalarTower A L Ω]
    [IsScalarTower A' K' Ω] [IsScalarTower K' L' Ω] [IsScalarTower A' L' Ω]
    [IsScalarTower A A' Ω]
    (h : IsTamelyRamifiedWRT A L) (φ : K' ⊗[K] L →ₐ[K'] L') (hφ : Function.Surjective φ)
    (hL : ∀ x : L, algebraMap L Ω x = algebraMap L' Ω (φ ((1 : K') ⊗ₜ[K] x))) :
    IsTamelyRamifiedWRT A' L' := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨π', hπ'⟩ := IsDiscreteValuationRing.exists_irreducible A'
  obtain ⟨r, u', hπA'⟩ := exists_uniformizer_eq_unit_mul_pow K K' hπ hπ'
  obtain ⟨e, he_κA, hdvd⟩ := h.exists_isUnit_ramificationIdx_dvd K
  have he_A' : IsUnit (e : A') := by
    have he_A : IsUnit (e : A) := (isUnit_map_iff (IsLocalRing.residue A) _).mp (by
      rw [map_natCast]; exact he_κA)
    simpa using he_A.map (algebraMap A A')
  have he_κA' : IsUnit (e : A' ⧸ maximalIdeal A') := by
    simpa using he_A'.map (Ideal.Quotient.mk (maximalIdeal A'))
  have he0 : e ≠ 0 := by rintro rfl; simp at he_κA
  -- Extract `e`-th roots `β` of `π'` and `γ` of `u'`, and set `α = γ β ^ r` (`α ^ e = π`).
  obtain ⟨β, hβ⟩ :=
    IsAlgClosed.exists_pow_nat_eq (algebraMap A' Ω π') (Nat.pos_of_ne_zero he0)
  obtain ⟨γ, hγ⟩ :=
    IsAlgClosed.exists_pow_nat_eq (algebraMap A' Ω u') (Nat.pos_of_ne_zero he0)
  let α : Ω := γ * β ^ r
  have hα : α ^ e = algebraMap A Ω π := by
    rw [mul_pow, ← pow_mul, mul_comm r e, pow_mul, hγ, hβ, ← map_pow, ← map_mul, ← hπA',
      ← IsScalarTower.algebraMap_apply A A' Ω]
  -- By global Abhyankar's lemma, `L(α)` is unramified over `A₁ = integralClosure A K(α)`.
  let := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
  obtain ⟨_, hU_A₁⟩ := h.isUnramifiedWRT_adjoin_root (K := K) hπ hα hdvd
  let A₁ := integralClosure A K⟮α⟯
  have : IsScalarTower A K L⟮α⟯ := .of_algebraMap_eq fun a ↦ by
    simp [IsScalarTower.algebraMap_apply A L L⟮α⟯,
      IsScalarTower.algebraMap_apply K L L⟮α⟯, ← IsScalarTower.algebraMap_apply A K L]
  have : IsScalarTower A K⟮α⟯ L⟮α⟯ :=
    IsScalarTower.of_algHom ((TauCeti.IntermediateField.adjoinBaseChange K L α).restrictScalars A)
  have : IsScalarTower A A₁ L⟮α⟯ := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A₁ K⟮α⟯ L⟮α⟯,
      ← IsScalarTower.algebraMap_apply A A₁ K⟮α⟯,
      ← IsScalarTower.algebraMap_apply A K⟮α⟯ L⟮α⟯]
  have hαK : AdjoinSimple.gen K α ^ e = algebraMap A K⟮α⟯ π :=
    Subtype.ext (by simpa [IsScalarTower.algebraMap_apply A K K⟮α⟯,
      IsScalarTower.algebraMap_apply A K Ω] using hα)
  have : IsFractionRing A₁ K⟮α⟯ :=
    IsDiscreteValuationRing.isFractionRing_integralClosure_of_pow_eq_of_irreducible hπ hαK
      (adjoin_adjoinSimple_gen_eq_top α)
  have : FiniteDimensional K⟮α⟯ L⟮α⟯ :=
    TauCeti.IntermediateField.finiteDimensional_adjoinBaseChange K L α
  have : Algebra.IsSeparable K⟮α⟯ L⟮α⟯ :=
    TauCeti.IntermediateField.isSeparable_adjoinBaseChange K L α
  -- Build the Kummer DVR `A'₁ = integralClosure A' K'(β)` and the standard tame cover `T`.
  let A'₁ := integralClosure A' K'⟮β⟯
  have hβK' : AdjoinSimple.gen K' β ^ e = algebraMap A' K'⟮β⟯ π' :=
    Subtype.ext (by simpa [IsScalarTower.algebraMap_apply A' K' K'⟮β⟯,
      IsScalarTower.algebraMap_apply A' K' Ω] using hβ)
  have hgenβ : K'⟮AdjoinSimple.gen K' β⟯ = ⊤ := adjoin_adjoinSimple_gen_eq_top β
  have : IsDiscreteValuationRing A'₁ :=
    IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible
      hπ' hβK' hgenβ
  have : IsFractionRing A'₁ K'⟮β⟯ :=
    IsDiscreteValuationRing.isFractionRing_integralClosure_of_pow_eq_of_irreducible hπ' hβK' hgenβ
  let T := TauCeti.standardTameCover A'₁ (algebraMap A' A'₁ u') e
  have : Algebra.Etale A'₁ T :=
    TauCeti.standardTameCover_etale (u'.isUnit.map _)
      (by simpa using he_A'.map (algebraMap A' A'₁))
  have : NeZero e := ⟨he0⟩
  have : Module.Finite A'₁ T := inferInstance
  let : Algebra A T := ((algebraMap A'₁ T).comp ((algebraMap A' A'₁).comp
    (algebraMap A A'))).toAlgebra
  -- Obtain `f : A₁ → T` compatible with `gT : T → Ω`, and apply finite étale base change.
  have : IsScalarTower A' K'⟮β⟯ Ω := .of_algebraMap_eq fun a' ↦ by
    rw [IsScalarTower.algebraMap_apply A' K' K'⟮β⟯,
      ← IsScalarTower.algebraMap_apply K' K'⟮β⟯ Ω,
      ← IsScalarTower.algebraMap_apply A' K' Ω]
  have : IsScalarTower A'₁ K'⟮β⟯ Ω := Subalgebra.isScalarTower_left (integralClosure A' K'⟮β⟯)
  have : IsScalarTower A₁ L⟮α⟯ Ω := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply A₁ K⟮α⟯ L⟮α⟯]
    exact (TauCeti.IntermediateField.coe_adjoinBaseChange K L α (x : K⟮α⟯)).symm
  obtain ⟨f, gT, hfg⟩ :=
    exists_algHom_integralClosure_standardTameCover hπ hπA' he0 hαK hβK' hγ rfl
  obtain ⟨E, hUnramE, hL'_mem⟩ :=
    exists_unramified_overfield_of_etale_cover (A := A) (K := K) (L := L)
      (A₁ := A₁) (K₁ := K⟮α⟯) (L₁ := L⟮α⟯) (A'₁ := A'₁) (K'₁ := K'⟮β⟯) (T := T)
      (Ω := Ω) φ hφ hU_A₁ f gT hfg fun x ↦ hL x
  -- Descend tame ramification from `E` (unramified over `A'₁`) to `L'`.
  let : Algebra L' E := RingHom.toAlgebra
    { toFun := fun z ↦ ⟨algebraMap L' Ω z, hL'_mem z⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ ↦ Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ ↦ Subtype.ext (map_add _ _ _) }
  have : IsScalarTower A' L' E := .of_algebraMap_eq fun a' ↦
    Subtype.ext (IsScalarTower.algebraMap_apply A' L' Ω a')
  have : FiniteDimensional K' L' := Module.Finite.of_surjective φ.toLinearMap hφ
  have : Algebra.FormallyUnramified K L :=
    (Algebra.FormallyUnramified.iff_isSeparable K L).mpr inferInstance
  have : Algebra.FormallyUnramified K' L' := .of_surjective φ hφ
  have : Algebra.IsSeparable K' L' :=
    (Algebra.FormallyUnramified.iff_isSeparable K' L').mp inferInstance
  exact IsDiscreteValuationRing.isTamelyRamifiedWRT_of_isUnramifiedWRT_of_pow_eq_of_irreducible
    hπ' he_κA' hβK' hgenβ hUnramE

/-- Tamely ramified extensions of a discrete valuation ring are stable under base change: if `L` is
tamely ramified with respect to `A`, then every factor `L'` of `K' ⊗[K] L`, given by a surjective
`K'`-algebra map `φ : K' ⊗[K] L → L'`, is tamely ramified with respect to `A'`. -/
@[stacks 0EXY "tamely ramified case"]
theorem IsTamelyRamifiedWRT.baseChange (h : IsTamelyRamifiedWRT A L)
    (φ : K' ⊗[K] L →ₐ[K'] L') (hφ : Function.Surjective φ) : IsTamelyRamifiedWRT A' L' := by
  -- Install compatible algebra structures on `L'`, hence automatically on `AlgebraicClosure L'`.
  let : Algebra K L' := ((algebraMap K' L').comp (algebraMap K K')).toAlgebra
  have : IsScalarTower K K' L' := .of_algebraMap_eq fun _ ↦ by simp [RingHom.algebraMap_toAlgebra]
  let : Algebra A L' := ((algebraMap A' L').comp (algebraMap A A')).toAlgebra
  have : IsScalarTower A A' L' := .of_algebraMap_eq fun _ ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower A K' L' := .of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply A A' K',
      ← IsScalarTower.algebraMap_apply A' K' L']
  have : IsScalarTower A K L' := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply K K' L', ← IsScalarTower.algebraMap_apply A K K',
      ← IsScalarTower.algebraMap_apply A K' L']
  let : Algebra L L' :=
    (φ.toRingHom.comp
      (Algebra.TensorProduct.includeRight : L →ₐ[K] K' ⊗[K] L).toRingHom).toAlgebra
  have : IsScalarTower K L L' := .of_algebraMap_eq fun k ↦ by
    simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul, ← Algebra.TensorProduct.algebraMap_apply,
      IsScalarTower.algebraMap_apply K K' (K' ⊗[K] L), AlgHom.commutes]
  have : IsScalarTower A L L' := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply K L L',
      ← IsScalarTower.algebraMap_apply A K L']
  exact isTamelyRamifiedWRT_baseChange_of_isAlgClosed (Ω := AlgebraicClosure L') h φ hφ
    fun x ↦ by
      simp [IsScalarTower.algebraMap_apply L L' (AlgebraicClosure L'),
        RingHom.algebraMap_toAlgebra]

end TauCeti.Algebra
