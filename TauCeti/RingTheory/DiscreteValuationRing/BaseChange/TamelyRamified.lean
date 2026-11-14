/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.KummerCharacterization
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Unramified.Field
import TauCeti.Algebra.Algebra.NatCast
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.Basic
import TauCeti.RingTheory.DiscreteValuationRing.BaseChange.Unramified
import TauCeti.RingTheory.DiscreteValuationRing.Kummer
import TauCeti.RingTheory.Etale.IntegralClosure
import TauCeti.RingTheory.IntegralClosure.TensorProduct
import TauCeti.RingTheory.Localization.Integral

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
(`TauCeti.Algebra.IsTamelyRamifiedWRT.adjoin_root`), while `K'(β', γ') / K'(β')` is unramified over
`A'[β']` because `u'` and `e₀` are units in `A'[β']`
(`TauCeti.IsDiscreteValuationRing.isUnramifiedWRT_of_pow_eq_of_isUnit`). Tensoring the two finite
étale integral closures exhibits `L'(β', γ')` as a field quotient of the generic fibre of a finite
étale `A'[β']`-algebra, hence unramified over `A'[β']`, which forces `L'` to be tamely ramified with
respect to `A'`. As in the unramified case, `A → A'` need not be a local homomorphism.

## Main results

* `TauCeti.IsDiscreteValuationRing.isUnramifiedWRT_of_pow_eq_of_isUnit`: adjoining an `n`-th root
  of a unit of `A`, with `n` invertible in `A`, gives an extension unramified with respect to `A`.
* `TauCeti.Algebra.IsTamelyRamifiedWRT.baseChange`: tamely ramified extensions of a discrete
  valuation ring are stable under base change (Stacks, Lemma 15.116.9, tame case).

## References

* [Stacks Project, Lemma 15.116.7](https://stacks.math.columbia.edu/tag/0EXW).
* [Stacks Project, Lemma 15.116.9](https://stacks.math.columbia.edu/tag/0EXY).
-/

public section

universe v

open scoped TensorProduct
open _root_.IntermediateField IsLocalRing Polynomial

namespace TauCeti.IsDiscreteValuationRing

section UnitRoot

variable {A K L : Type*} [CommRing A] [IsDomain A] [_root_.IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]

omit [IsFractionRing A K] in
/-- When `L = K(γ)` for an `n`-th root `γ` of `u ∈ A` with `n` invertible in `A`, the generic fibre
`K ⊗[A] A[x]/(x ^ n - u)` maps surjectively onto `L`. -/
private theorem exists_surjective_tensor_standardTameCover {u : A} {n : ℕ} (hn : IsUnit (n : A))
    {γ : L} (hγ : γ ^ n = algebraMap A L u) (hgen : K⟮γ⟯ = ⊤) :
    ∃ χ : K ⊗[A] standardTameCover A u n →ₐ[K] L, Function.Surjective χ := by
  have hn₀ : n ≠ 0 := hn.neZero_natCast.out
  let ψ : standardTameCover A u n →ₐ[A] L :=
    AdjoinRoot.liftAlgHom (X ^ n - C u) (Algebra.ofId A L) γ (by simp [hγ])
  let χ : K ⊗[A] standardTameCover A u n →ₐ[K] L :=
    Algebra.TensorProduct.lift (Algebra.ofId K L) ψ fun _ _ ↦ .all _ _
  refine ⟨χ, ?_⟩
  have hγ_int : IsIntegral K γ :=
    (IsIntegral.of_pow (Nat.pos_of_ne_zero hn₀) (hγ ▸ isIntegral_algebraMap (R := A))).tower_top
  have hadj : Algebra.adjoin K ({γ} : Set L) = ⊤ :=
    (adjoin_simple_eq_top_iff_of_isAlgebraic hγ_int.isAlgebraic).mp hgen
  have hmem : γ ∈ χ.range :=
    ⟨1 ⊗ₜ[A] AdjoinRoot.root (X ^ n - C u), by simp [χ, ψ]⟩
  have htop : χ.range = ⊤ :=
    top_unique (hadj ▸ Algebra.adjoin_le (Set.singleton_subset_iff.mpr hmem))
  intro x
  have hx : x ∈ χ.range := htop ▸ Algebra.mem_top
  exact (AlgHom.mem_range χ).mp hx

/-- **Adjoining a tame root of a unit is unramified.** Let `A` be a discrete valuation ring with
fraction field `K`. If `L` is generated over `K` by an `n`-th root `γ` of a unit `u` of `A`, with
`n` invertible in `A`, then `L` is unramified with respect to `A`. -/
theorem isUnramifiedWRT_of_pow_eq_of_isUnit {u : A} (hu : IsUnit u) {n : ℕ} (hn : IsUnit (n : A))
    {γ : L} (hγ : γ ^ n = algebraMap A L u) (hgen : K⟮γ⟯ = ⊤) :
    Algebra.IsUnramifiedWRT A L := by
  have := hn.neZero_natCast
  have := standardTameCover_etale hu hn
  obtain ⟨χ, hχ⟩ := exists_surjective_tensor_standardTameCover hn hγ hgen
  exact χ.isUnramifiedWRT_of_surjective hχ

/-- Under the hypotheses of `isUnramifiedWRT_of_pow_eq_of_isUnit`, the integral closure of `A` in
`L` is finite étale over `A`. -/
private theorem etale_and_finite_integralClosure_of_pow_eq_of_isUnit {u : A} (hu : IsUnit u)
    {n : ℕ} (hn : IsUnit (n : A)) {γ : L} (hγ : γ ^ n = algebraMap A L u) (hgen : K⟮γ⟯ = ⊤) :
    Algebra.Etale A (integralClosure A L) ∧ Module.Finite A (integralClosure A L) := by
  have := hn.neZero_natCast
  have := standardTameCover_etale hu hn
  have : IsIntegrallyClosedIn A K :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mp inferInstance
  obtain ⟨χ, hχ⟩ := exists_surjective_tensor_standardTameCover hn hγ hgen
  have : FiniteDimensional K L := Module.Finite.of_surjective χ.toLinearMap hχ
  have : Algebra.Etale A (integralClosure A L) := χ.etale_integralClosure_of_surjective hχ
  have : Algebra.IsSeparable K L :=
    have : Algebra.FormallyUnramified K L := .of_surjective χ hχ
    (Algebra.FormallyUnramified.iff_isSeparable K L).mp this
  exact ⟨‹_›, IsIntegralClosure.finite A K L _⟩

end UnitRoot

end TauCeti.IsDiscreteValuationRing

namespace TauCeti.Algebra

section BaseChange

/-- If `x` is integral over `F` and an `F`-subalgebra `S` of `M` contains the image of the
distinguished generator of `F(x)` under `f : F(x) →ₐ[F] M`, then `S` contains the entire image of
`f`. -/
private theorem map_mem_of_gen_mem_subalgebra {F Ω M : Type*} [Field F] [Field Ω] [Algebra F Ω]
    [CommSemiring M] [Algebra F M] {x : Ω} (hx : IsIntegral F x)
    (f : F⟮x⟯ →ₐ[F] M) {S : Subalgebra F M} (hmem : f (AdjoinSimple.gen F x) ∈ S)
    (z : F⟮x⟯) : f z ∈ S := by
  have hadj : Algebra.adjoin F ({AdjoinSimple.gen F x} : Set F⟮x⟯) = ⊤ :=
    (adjoin_simple_eq_top_iff_of_isAlgebraic
      ((AdjoinSimple.isIntegral_gen F x).mpr hx).isAlgebraic).mp
      (_root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top x)
  have hgen : AdjoinSimple.gen F x ∈ S.comap f := (Subalgebra.mem_comap _ _ _).mpr hmem
  have htop : S.comap f = ⊤ :=
    top_unique (hadj ▸ Algebra.adjoin_le (Set.singleton_subset_iff.mpr hgen))
  exact (Subalgebra.mem_comap _ _ _).mp (htop ▸ Algebra.mem_top : z ∈ S.comap f)

/-- Membership underlying `adjoinSimpleInclusionRingHom`. -/
private theorem mem_of_adjoin_simple_mem {F₁ F₂ Ω : Type*} [Field F₁] [Field F₂] [Field Ω]
    [Algebra F₁ Ω] [Algebra F₂ Ω] {x : Ω} {E : IntermediateField F₂ Ω}
    (hF₁ : ∀ c : F₁, algebraMap F₁ Ω c ∈ E) (hx : x ∈ E) {z : Ω} (hz : z ∈ F₁⟮x⟯) :
    z ∈ E :=
  let E' : IntermediateField F₁ Ω :=
    { E.toSubalgebra with algebraMap_mem' := hF₁, inv_mem' := E.inv_mem' }
  IsConcreteLE.le_iff.mp (adjoin_simple_le_iff (K := E').mpr hx) hz

/-- If `E : IntermediateField F₂ Ω` contains `x` and the image of `F₁`, then `F₁(x) ⊆ E` inside `Ω`,
yielding a canonical ring homomorphism `F₁(x) →+* E` preserving ambient values. -/
private def adjoinSimpleInclusionRingHom {F₁ F₂ Ω : Type*} [Field F₁] [Field F₂] [Field Ω]
    [Algebra F₁ Ω] [Algebra F₂ Ω] {x : Ω} {E : IntermediateField F₂ Ω}
    (hF₁ : ∀ c : F₁, algebraMap F₁ Ω c ∈ E) (hx : x ∈ E) : F₁⟮x⟯ →+* E where
  toFun z := ⟨z.1, mem_of_adjoin_simple_mem hF₁ hx z.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A ring homomorphism `g : K₁ →+* K'₂` compatible with `A → A'₁ → K'₂` restricts to a ring
homomorphism `integralClosure A K₁ →+* integralClosure A'₁ K'₂`. -/
private def mapIntegralClosure
    {A K₁ A'₁ K'₂ : Type*} [CommRing A] [CommRing K₁] [Algebra A K₁]
    [CommRing A'₁] [CommRing K'₂] [Algebra A'₁ K'₂]
    (φ : A →+* A'₁) (g : K₁ →+* K'₂)
    (hg : ∀ r : A, g (algebraMap A K₁ r) = algebraMap A'₁ K'₂ (φ r)) :
    integralClosure A K₁ →+* integralClosure A'₁ K'₂ where
  toFun a := ⟨g a.1, a.2.map_of_comp_eq φ g (RingHom.ext fun r ↦ (hg r).symm)⟩
  map_one' := Subtype.ext g.map_one
  map_mul' _ _ := Subtype.ext (g.map_mul _ _)
  map_zero' := Subtype.ext g.map_zero
  map_add' _ _ := Subtype.ext (g.map_add _ _)

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
    (φ : K' ⊗[K] L →ₐ[K'] L') (hφ : Function.Surjective φ)
    (hφL : ∀ l : L, φ (1 ⊗ₜ[K] l) = algebraMap L L' l)
    {β' γ' : Ω'} (hβ'_int : IsIntegral L' β') (hγ'_intL : IsIntegral L' γ')
    (hγ'_intK : IsIntegral K'⟮β'⟯ γ')
    (ιK : K₁ →+* (K'⟮β'⟯)⟮γ'⟯)
    (ιL₁ : L₁ →+* IntermediateField.adjoin L' ({β', γ'} : Set Ω'))
    (hιL : ∀ l : L, (ιL₁ (algebraMap L L₁ l) : Ω') = algebraMap L Ω' l)
    (hιsmul : ∀ (c : K₁) (x : L₁), (ιL₁ (c • x) : Ω') = (ιK c : Ω') * (ιL₁ x : Ω'))
    (ιK'₁ : K'⟮β'⟯ →+* IntermediateField.adjoin L' ({β', γ'} : Set Ω'))
    (hιK'₁ : ∀ x : K'⟮β'⟯, (ιK'₁ x : Ω') = x)
    (ιK'₂ : (K'⟮β'⟯)⟮γ'⟯ →+* IntermediateField.adjoin L' ({β', γ'} : Set Ω'))
    (hιK'₂ : ∀ x : (K'⟮β'⟯)⟮γ'⟯, (ιK'₂ x : Ω') = x)
    {T : Type*} [CommRing T]
    (χ : T →+* IntermediateField.adjoin L' ({β', γ'} : Set Ω'))
    (hK'₁_R : ∀ x : K'⟮β'⟯, ιK'₁ x ∈ χ.range)
    (hγ'_R : ιK'₂ (AdjoinSimple.gen K'⟮β'⟯ γ') ∈ χ.range)
    (hB₁_R : ∀ b : integralClosure A₁ L₁, ιL₁ b ∈ χ.range) :
    Function.Surjective χ := by
  let E'' : IntermediateField L' Ω' := IntermediateField.adjoin L' ({β', γ'} : Set Ω')
  let R : Subring E'' := χ.range
  have hK'₂_R : ∀ z : (K'⟮β'⟯)⟮γ'⟯, ιK'₂ z ∈ R := by
    let : Algebra K'⟮β'⟯ E'' := ιK'₁.toAlgebra
    have hιK'₂_alg (x : K'⟮β'⟯) :
        ιK'₂ (algebraMap K'⟮β'⟯ (K'⟮β'⟯)⟮γ'⟯ x) = algebraMap K'⟮β'⟯ E'' x :=
      Subtype.ext (by rw [hιK'₂, RingHom.algebraMap_toAlgebra, hιK'₁]; rfl)
    let ιK'₂_a : (K'⟮β'⟯)⟮γ'⟯ →ₐ[K'⟮β'⟯] E'' := { ιK'₂ with commutes' := hιK'₂_alg }
    let R_K'₁ : Subalgebra K'⟮β'⟯ E'' := { R with algebraMap_mem' := hK'₁_R }
    exact fun z ↦ map_mem_of_gen_mem_subalgebra hγ'_intK ιK'₂_a (S := R_K'₁) hγ'_R z
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
    have hk' : algebraMap L' E'' (algebraMap K' L' k') = ιK'₁ (algebraMap K' K'⟮β'⟯ k') :=
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
      ⟨⟨ιK'₁ (AdjoinSimple.gen K' β'), hK'₁_R _, hιK'₁ _⟩,
        Set.singleton_subset_iff.mpr ⟨ιK'₂ (AdjoinSimple.gen K'⟮β'⟯ γ'), hγ'_R, hιK'₂ _⟩⟩
  have halg : ∀ x ∈ ({β', γ'} : Set Ω'), IsAlgebraic L' x := fun x hx ↦ by
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · exact hx.symm ▸ hβ'_int.isAlgebraic
    · exact (Set.mem_singleton_iff.mp hx).symm ▸ hγ'_intL.isAlgebraic
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

private theorem lift_compositum_tensor_tmul_one
    {A₁ A'₁ K'₁ A'₂ B₁ E'' : Type*} [CommRing A₁] [CommRing A'₁] [CommRing K'₁]
    [CommRing A'₂] [CommRing B₁] [CommRing E'']
    [Algebra A'₁ K'₁] [Algebra A'₁ A'₂] [Algebra A₁ A'₂] [Algebra A₁ B₁] [Algebra K'₁ E'']
    (fA'₂ : A'₂ →+* E'') (fB₁ : B₁ →+* E'')
    (hA₁ : ∀ a : A₁, fB₁ (algebraMap A₁ B₁ a) = fA'₂ (algebraMap A₁ A'₂ a))
    (hA'₁ : ∀ y : A'₁, fA'₂ (algebraMap A'₁ A'₂ y) = algebraMap K'₁ E'' (algebraMap A'₁ K'₁ y))
    (x : K'₁) :
    lift_compositum_tensor fA'₂ fB₁ hA₁ hA'₁ (x ⊗ₜ[A'₁] (1 : A'₂ ⊗[A₁] B₁)) =
      algebraMap K'₁ E'' x := by
  simp [lift_compositum_tensor]

private theorem lift_compositum_tensor_one_tmul_left
    {A₁ A'₁ K'₁ A'₂ B₁ E'' : Type*} [CommRing A₁] [CommRing A'₁] [CommRing K'₁]
    [CommRing A'₂] [CommRing B₁] [CommRing E'']
    [Algebra A'₁ K'₁] [Algebra A'₁ A'₂] [Algebra A₁ A'₂] [Algebra A₁ B₁] [Algebra K'₁ E'']
    (fA'₂ : A'₂ →+* E'') (fB₁ : B₁ →+* E'')
    (hA₁ : ∀ a : A₁, fB₁ (algebraMap A₁ B₁ a) = fA'₂ (algebraMap A₁ A'₂ a))
    (hA'₁ : ∀ y : A'₁, fA'₂ (algebraMap A'₁ A'₂ y) = algebraMap K'₁ E'' (algebraMap A'₁ K'₁ y))
    (a : A'₂) :
    lift_compositum_tensor fA'₂ fB₁ hA₁ hA'₁ ((1 : K'₁) ⊗ₜ[A'₁] (a ⊗ₜ[A₁] (1 : B₁))) =
      fA'₂ a := by
  simp [lift_compositum_tensor]

private theorem lift_compositum_tensor_one_tmul_right
    {A₁ A'₁ K'₁ A'₂ B₁ E'' : Type*} [CommRing A₁] [CommRing A'₁] [CommRing K'₁]
    [CommRing A'₂] [CommRing B₁] [CommRing E'']
    [Algebra A'₁ K'₁] [Algebra A'₁ A'₂] [Algebra A₁ A'₂] [Algebra A₁ B₁] [Algebra K'₁ E'']
    (fA'₂ : A'₂ →+* E'') (fB₁ : B₁ →+* E'')
    (hA₁ : ∀ a : A₁, fB₁ (algebraMap A₁ B₁ a) = fA'₂ (algebraMap A₁ A'₂ a))
    (hA'₁ : ∀ y : A'₁, fA'₂ (algebraMap A'₁ A'₂ y) = algebraMap K'₁ E'' (algebraMap A'₁ K'₁ y))
    (b : B₁) :
    lift_compositum_tensor fA'₂ fB₁ hA₁ hA'₁ ((1 : K'₁) ⊗ₜ[A'₁] ((1 : A'₂) ⊗ₜ[A₁] b)) =
      fB₁ b := by
  simp [lift_compositum_tensor]

/-- Over an abstract discrete valuation ring `R`, an extension unramified with respect to `R` has
finite étale integral closure. -/
private theorem etale_and_finite_of_isUnramifiedWRT
    {R F E : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [Field E] [Algebra R E] [Algebra F E] [IsScalarTower R F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (h : IsUnramifiedWRT R E) :
    Algebra.Etale R (integralClosure R E) ∧ Module.Finite R (integralClosure R E) :=
  ⟨(isUnramifiedWRT_iff_etale R F E).mp h, IsIntegralClosure.finite R F E _⟩

/-- Over abstract fields `K'₁` and `E''` and finite étale algebras `A'₂ / A'₁` and `B₁ / A₁`, if
the induced `K'₁`-algebra map `K'₁ ⊗[A'₁] (A'₂ ⊗[A₁] B₁) →ₐ[K'₁] E''` is surjective whenever its
range contains `algebraMap K'₁ E''`, `fA'₂ γ'₀`, and `fB₁`, then `E''` is unramified over `A'₁`. -/
private theorem isUnramifiedWRT_of_compositum_closures
    (A₁ B₁ A'₁ K'₁ A'₂ E'' : Type v)
    [CommRing A₁] [CommRing B₁] [Algebra A₁ B₁] [Algebra.Etale A₁ B₁] [Module.Finite A₁ B₁]
    [CommRing A'₁] [IsDomain A'₁] [IsDiscreteValuationRing A'₁]
    [Field K'₁] [Algebra A'₁ K'₁] [IsFractionRing A'₁ K'₁]
    [CommRing A'₂] [Algebra A'₁ A'₂] [Algebra.Etale A'₁ A'₂] [Module.Finite A'₁ A'₂]
    [Field E''] [Algebra A'₁ E''] [Algebra K'₁ E''] [IsScalarTower A'₁ K'₁ E'']
    (fA₁ : A₁ →+* A'₂) (fA'₂ : A'₂ →+* E'') (fB₁ : B₁ →+* E'')
    (hA₁ : ∀ a : A₁, fB₁ (algebraMap A₁ B₁ a) = fA'₂ (fA₁ a))
    (hA'₁ : ∀ y : A'₁, fA'₂ (algebraMap A'₁ A'₂ y) = algebraMap K'₁ E'' (algebraMap A'₁ K'₁ y))
    (γ'₀ : A'₂)
    (hsurj : ∀ {T : Type v} [CommRing T] (χ : T →+* E''),
      (∀ x : K'₁, algebraMap K'₁ E'' x ∈ χ.range) →
      fA'₂ γ'₀ ∈ χ.range →
      (∀ b : B₁, fB₁ b ∈ χ.range) →
      Function.Surjective χ) :
    IsUnramifiedWRT A'₁ E'' := by
  let : Algebra A₁ A'₂ := fA₁.toAlgebra
  let S' := A'₂ ⊗[A₁] B₁
  have : Algebra.Etale A'₁ S' := .comp A'₁ A'₂ S'
  have : Module.Finite A'₁ S' := .trans A'₂ S'
  let χ : K'₁ ⊗[A'₁] S' →ₐ[K'₁] E'' := lift_compositum_tensor fA'₂ fB₁ hA₁ hA'₁
  have hχ : Function.Surjective χ :=
    hsurj χ.toRingHom
      (fun x ↦ ⟨x ⊗ₜ[A'₁] (1 : S'), lift_compositum_tensor_tmul_one _ _ hA₁ hA'₁ x⟩)
      ⟨(1 : K'₁) ⊗ₜ[A'₁] (γ'₀ ⊗ₜ[A₁] (1 : B₁)),
        lift_compositum_tensor_one_tmul_left _ _ hA₁ hA'₁ γ'₀⟩
      (fun b ↦ ⟨(1 : K'₁) ⊗ₜ[A'₁] ((1 : A'₂) ⊗ₜ[A₁] b),
        lift_compositum_tensor_one_tmul_right _ _ hA₁ hA'₁ b⟩)
  exact χ.isUnramifiedWRT_of_surjective hχ

/-- If `γ' ^ e₀ = algebraMap A' Ω' x` with `0 < e₀`, the generator of `K'₁(γ')` is integral over
`integralClosure A' K'₁`. -/
private theorem isIntegral_adjoinSimple_gen_of_pow_eq
    {A' K'₁ Ω' : Type*} [CommRing A'] [Field K'₁] [Field Ω'] [Algebra A' K'₁]
    [Algebra A' Ω'] [Algebra K'₁ Ω'] [IsScalarTower A' K'₁ Ω']
    {γ' : Ω'} {e₀ : ℕ} (he₀_pos : 0 < e₀) {x : A'} (hγ' : γ' ^ e₀ = algebraMap A' Ω' x) :
    IsIntegral (integralClosure A' K'₁) (AdjoinSimple.gen K'₁ γ') := by
  have h : AdjoinSimple.gen K'₁ γ' ^ e₀ = algebraMap A' K'₁⟮γ'⟯ x := Subtype.ext (by
    rw [IsScalarTower.algebraMap_apply A' K'₁ K'₁⟮γ'⟯, IntermediateField.coe_algebraMap_apply,
      ← IsScalarTower.algebraMap_apply A' K'₁ Ω']
    exact hγ')
  exact (IsIntegral.of_pow he₀_pos (h ▸ isIntegral_algebraMap (R := A'))).tower_top

/-- Every field quotient of `K₁ ⊗[K] L` for a finite separable extension `L / K` is finite and
separable over `K₁`. -/
private theorem finiteDimensional_and_isSeparable_of_surjective
    {K K₁ L E : Type*} [Field K] [Field K₁] [Field L] [Field E]
    [Algebra K K₁] [Algebra K L] [Algebra K₁ E]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (φ : K₁ ⊗[K] L →ₐ[K₁] E) (hφ : Function.Surjective φ) :
    FiniteDimensional K₁ E ∧ Algebra.IsSeparable K₁ E := by
  have : FiniteDimensional K₁ E := Module.Finite.of_surjective φ.toLinearMap hφ
  have : Algebra.FormallyUnramified K L := .of_isSeparable K L
  have : Algebra.FormallyUnramified K₁ E := .of_surjective φ hφ
  exact ⟨‹_›, (Algebra.FormallyUnramified.iff_isSeparable K₁ E).mp ‹_›⟩

variable {A K L A' K' L' : Type*}
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A'] [Field K'] [Algebra A' K']
  [IsFractionRing A' K'] [Algebra A A'] [Algebra A K'] [Algebra K K'] [IsScalarTower A A' K']
  [IsScalarTower A K K'] [Field L'] [Algebra K' L'] [Algebra A' L'] [IsScalarTower A' K' L']

/-- For a tamely ramified extension `L / K` over `A` and an `e₀`-th root `α'` of a uniformizer `π`
of `A` in an extension `Ω'` of `L` (where `0 < e₀` is divisible by all ramification indices over
`A`), `integralClosure A K(α')` has fraction field `K(α')` and `integralClosure A[α'] L(α')` is
finite étale over `A[α'] := integralClosure A K(α')`. -/
private theorem etale_and_finite_over_adjoin_root_of_tame
    {Ω' : Type*} [Field Ω'] [Algebra K Ω'] [Algebra L Ω'] [Algebra A Ω']
    [IsScalarTower K L Ω'] [IsScalarTower A K Ω']
    (h : IsTamelyRamifiedWRT A L) {π : A} (hπ : Irreducible π) {e₀ : ℕ} (he₀_pos : 0 < e₀)
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      P.ramificationIdx A ∣ e₀)
    {α' : Ω'} (hα' : α' ^ e₀ = algebraMap A Ω' π)
    [IsDiscreteValuationRing (integralClosure A K⟮α'⟯)] :
    letI := (TauCeti.IntermediateField.adjoinBaseChange K L α').toAlgebra
    IsFractionRing (integralClosure A K⟮α'⟯) K⟮α'⟯ ∧
      Algebra.IsAlgebraic K⟮α'⟯ L⟮α'⟯ ∧
      Algebra.Etale (integralClosure A K⟮α'⟯) (integralClosure (integralClosure A K⟮α'⟯) L⟮α'⟯) ∧
      Module.Finite (integralClosure A K⟮α'⟯)
        (integralClosure (integralClosure A K⟮α'⟯) L⟮α'⟯) := by
  let := (TauCeti.IntermediateField.adjoinBaseChange K L α').toAlgebra
  have : IsScalarTower A L Ω' := .of_algebraMap_eq fun a ↦ by
    simp [IsScalarTower.algebraMap_apply A K Ω', IsScalarTower.algebraMap_apply A K L,
      IsScalarTower.algebraMap_apply K L Ω']
  have hα'_int : IsIntegral L α' :=
    (IsIntegral.of_pow he₀_pos (hα' ▸ isIntegral_algebraMap (R := A))).tower_top
  obtain ⟨_, _⟩ := finiteDimensional_and_isSeparable_of_surjective
    (TauCeti.IntermediateField.adjoinBaseChangeTensorLift K L α')
    (TauCeti.IntermediateField.surjective_adjoinBaseChange_tensorProduct K L hα'_int)
  have hunrL₁ : IsUnramifiedWRT (integralClosure A K⟮α'⟯) L⟮α'⟯ :=
    h.adjoin_root (K := K) hπ hdvd hα'
  have hdegKα := TauCeti.IsDiscreteValuationRing.finrank_adjoin_of_pow_eq_of_irreducible
    (K := K) hπ hα'
  have : FiniteDimensional K K⟮α'⟯ := Module.finite_of_finrank_pos (hdegKα ▸ he₀_pos)
  have : IsFractionRing (integralClosure A K⟮α'⟯) K⟮α'⟯ :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K K⟮α'⟯ _
  obtain ⟨hetale, hfin⟩ := etale_and_finite_of_isUnramifiedWRT (F := K⟮α'⟯) hunrL₁
  exact ⟨‹_›, Algebra.IsAlgebraic.of_finite K⟮α'⟯ L⟮α'⟯, hetale, hfin⟩

/-- In an overfield `Ω'` of `K'` containing `e₀`-th roots `β'` of a uniformizer `ϖ'` of `A'` and
`γ'` of a unit `u'` of `A'` (with `e₀` invertible in `A'`), `K'(β')` is tamely ramified over `A'`
and `integralClosure A'₁ K'(β')(γ')` is finite étale over `A'₁ := integralClosure A' K'(β')`. -/
private theorem etale_and_finite_over_adjoin_uniformizer_root
    {Ω' : Type*} [Field Ω'] [Algebra K' Ω'] [Algebra A' Ω'] [IsScalarTower A' K' Ω']
    {ϖ' : A'} (hϖ' : Irreducible ϖ') {u' : A'ˣ} {e₀ : ℕ}
    (he₀_pos : 0 < e₀) (he₀_A' : IsUnit (e₀ : A'))
    (he₀_res' : IsUnit (e₀ : A' ⧸ maximalIdeal A'))
    {β' γ' : Ω'} (hβ' : β' ^ e₀ = algebraMap A' Ω' ϖ') (hγ' : γ' ^ e₀ = algebraMap A' Ω' u')
    [IsDiscreteValuationRing (integralClosure A' K'⟮β'⟯)] :
    IsTamelyRamifiedWRT A' K'⟮β'⟯ ∧
      IsFractionRing (integralClosure A' K'⟮β'⟯) K'⟮β'⟯ ∧
      Algebra.Etale (integralClosure A' K'⟮β'⟯)
        (integralClosure (integralClosure A' K'⟮β'⟯) (K'⟮β'⟯)⟮γ'⟯) ∧
      Module.Finite (integralClosure A' K'⟮β'⟯)
        (integralClosure (integralClosure A' K'⟮β'⟯) (K'⟮β'⟯)⟮γ'⟯) := by
  let K'₁ : IntermediateField K' Ω' := K'⟮β'⟯
  have : IsScalarTower A' K'₁ Ω' := .to₁₃₄ A' K' K'₁ Ω'
  let A'₁ := integralClosure A' K'₁
  have hK'₁_tame : IsTamelyRamifiedWRT A' K'₁ :=
    TauCeti.IsDiscreteValuationRing.isTamelyRamifiedWRT_adjoin_of_pow_eq_of_irreducible
      hϖ' he₀_res' hβ'
  have hdegK'₁ := TauCeti.IsDiscreteValuationRing.finrank_adjoin_of_pow_eq_of_irreducible
    (K := K') hϖ' hβ'
  have : FiniteDimensional K' K'₁ := Module.finite_of_finrank_pos (hdegK'₁ ▸ he₀_pos)
  have : IsFractionRing A'₁ K'₁ := IsIntegralClosure.isFractionRing_of_finite_extension A' K' K'₁ _
  let K'₂ : IntermediateField K'₁ Ω' := K'₁⟮γ'⟯
  have : IsScalarTower A'₁ K'₁ K'₂ := ⟨fun y k z ↦ smul_assoc (y : K'₁) k z⟩
  have : IsScalarTower A' A'₁ K'₂ := ⟨fun a y z ↦ smul_assoc a (y : K'₁) z⟩
  have hγ'K'₂ : AdjoinSimple.gen K'₁ γ' ^ e₀ = algebraMap A'₁ K'₂ (algebraMap A' A'₁ u') :=
    Subtype.ext (by
      rw [← IsScalarTower.algebraMap_apply A' A'₁ K'₂, IsScalarTower.algebraMap_apply A' K'₁ K'₂,
        IntermediateField.coe_algebraMap_apply, ← IsScalarTower.algebraMap_apply A' K'₁ Ω']
      exact hγ')
  have he₀_A'₁ : IsUnit (e₀ : A'₁) := by simpa using he₀_A'.map (algebraMap A' A'₁)
  obtain ⟨hetale, hfin⟩ :=
    TauCeti.IsDiscreteValuationRing.etale_and_finite_integralClosure_of_pow_eq_of_isUnit
      (K := K'₁) (L := K'₂) (u'.isUnit.map (algebraMap A' A'₁)) he₀_A'₁ hγ'K'₂
      (_root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top γ')
  exact ⟨hK'₁_tame, ‹_›, hetale, hfin⟩

omit [IsDomain A'] [IsDiscreteValuationRing A'] [IsFractionRing A' K'] [Algebra A K']
  [IsScalarTower A A' K'] [IsScalarTower A K K'] [IsScalarTower A' K' L'] in
/-- Under the hypotheses of `isTamelyRamifiedWRT_of_roots_in_overfield`, the double root extension
`L'(β', γ')` inside `Ω'` is unramified with respect to `integralClosure A' K'(β')`. -/
private theorem isUnramifiedWRT_adjoin_roots_in_overfield
    [Algebra L L']
    {Ω' : Type v} [Field Ω'] [Algebra L' Ω'] [Algebra K' Ω'] [Algebra A' Ω']
    [Algebra L Ω'] [Algebra K Ω'] [Algebra A Ω']
    [IsScalarTower K' L' Ω'] [IsScalarTower A' K' Ω'] [IsScalarTower A' L' Ω']
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
    (hιK'₁ : ∀ x : K'⟮β'⟯,
      (algebraMap K'⟮β'⟯ (IntermediateField.adjoin L' ({β', γ'} : Set Ω')) x : Ω') = x) :
    IsUnramifiedWRT (integralClosure A' K'⟮β'⟯)
      (IntermediateField.adjoin L' ({β', γ'} : Set Ω')) := by
  let α' : Ω' := γ' * β' ^ m
  have :=
    TauCeti.IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_adjoin (K := K) hπ hα'
  let := (TauCeti.IntermediateField.adjoinBaseChange K L α').toAlgebra
  let A₁ := integralClosure A K⟮α'⟯
  let B₁ := integralClosure A₁ L⟮α'⟯
  let A'₁ := integralClosure A' K'⟮β'⟯
  let A'₂ := integralClosure A'₁ (K'⟮β'⟯)⟮γ'⟯
  obtain ⟨_, _, _, _⟩ := etale_and_finite_over_adjoin_root_of_tame (K := K) h hπ he₀_pos hdvd hα'
  have : IsScalarTower A' K'⟮β'⟯ Ω' := .to₁₃₄ A' K' K'⟮β'⟯ Ω'
  have : IsScalarTower A' A'₁ (K'⟮β'⟯)⟮γ'⟯ := ⟨fun a y z ↦ smul_assoc a (y : K'⟮β'⟯) z⟩
  let E'' : IntermediateField L' Ω' := IntermediateField.adjoin L' ({β', γ'} : Set Ω')
  have hβ'_mem : β' ∈ E'' := IntermediateField.subset_adjoin L' _ (Set.mem_insert β' {γ'})
  have hγ'_mem : γ' ∈ E'' := IntermediateField.subset_adjoin L' _ (Set.mem_insert_of_mem β' rfl)
  let ιK'₂ : (K'⟮β'⟯)⟮γ'⟯ →+* E'' := adjoinSimpleInclusionRingHom
    (fun x ↦ by change (x : Ω') ∈ E''; rw [← hιK'₁ x]; exact (algebraMap K'⟮β'⟯ E'' x).2) hγ'_mem
  let ιK : K⟮α'⟯ →+* (K'⟮β'⟯)⟮γ'⟯ := adjoinSimpleInclusionRingHom
    (fun k ↦ by
      rw [IsScalarTower.algebraMap_apply K K' Ω']
      exact ((K'⟮β'⟯)⟮γ'⟯).algebraMap_mem (algebraMap K' K'⟮β'⟯ (algebraMap K K' k)))
    (mul_mem (mem_adjoin_simple_self K'⟮β'⟯ γ')
      (pow_mem (((K'⟮β'⟯)⟮γ'⟯).algebraMap_mem (AdjoinSimple.gen K' β')) m))
  let fA₁ : A₁ →+* A'₂ := mapIntegralClosure ((algebraMap A' A'₁).comp (algebraMap A A')) ιK
    (fun r ↦ Subtype.ext (by
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply A' A'₁ (K'⟮β'⟯)⟮γ'⟯,
        IsScalarTower.algebraMap_apply A' K'⟮β'⟯ (K'⟮β'⟯)⟮γ'⟯,
        IntermediateField.coe_algebraMap_apply, ← IsScalarTower.algebraMap_apply A' K'⟮β'⟯ Ω',
        ← IsScalarTower.algebraMap_apply A A' Ω']
      change (algebraMap A K⟮α'⟯ r : Ω') = algebraMap A Ω' r
      rw [IsScalarTower.algebraMap_apply A K K⟮α'⟯, IntermediateField.coe_algebraMap_apply,
        ← IsScalarTower.algebraMap_apply A K Ω']))
  let ιL₁ : L⟮α'⟯ →+* E'' := adjoinSimpleInclusionRingHom
    (fun l ↦ by rw [IsScalarTower.algebraMap_apply L L' Ω']; exact E''.algebraMap_mem _)
    (mul_mem hγ'_mem (pow_mem hβ'_mem m))
  have hγ'_intA' : IsIntegral A' γ' := IsIntegral.of_pow he₀_pos (hγ' ▸ isIntegral_algebraMap)
  exact isUnramifiedWRT_of_compositum_closures A₁ B₁ A'₁ K'⟮β'⟯ A'₂ E'' fA₁
    (ιK'₂.comp (algebraMap A'₂ (K'⟮β'⟯)⟮γ'⟯)) (ιL₁.comp (algebraMap B₁ L⟮α'⟯))
    (fun a ↦ Subtype.ext (TauCeti.IntermediateField.coe_adjoinBaseChange K L α' a.1))
    (fun y ↦ Subtype.ext (hιK'₁ y.1).symm)
    ⟨AdjoinSimple.gen K'⟮β'⟯ γ', isIntegral_adjoinSimple_gen_of_pow_eq he₀_pos hγ'⟩
    (fun χ h1 h2 h3 ↦ surjective_compositum_lift (K := K) (L := L) (K' := K') (L' := L')
      (Ω' := Ω') (K₁ := K⟮α'⟯) (L₁ := L⟮α'⟯) (A₁ := A₁) φ hφ hφL
      ((IsIntegral.of_pow he₀_pos (hβ' ▸ isIntegral_algebraMap (R := A'))).tower_top)
      hγ'_intA'.tower_top hγ'_intA'.tower_top ιK ιL₁ (fun _ ↦ rfl)
      (fun c x ↦ by
        rw [Algebra.smul_def]
        exact congrArg (· * (x : Ω')) (TauCeti.IntermediateField.coe_adjoinBaseChange K L α' c))
      (algebraMap K'⟮β'⟯ E'') hιK'₁ ιK'₂ (fun _ ↦ rfl) χ h1 h2 h3)

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
    (he₀_pos : 0 < e₀) (he₀_A' : IsUnit (e₀ : A'))
    (he₀_res' : IsUnit (e₀ : A' ⧸ maximalIdeal A'))
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      P.ramificationIdx A ∣ e₀)
    {β' γ' : Ω'} (hβ' : β' ^ e₀ = algebraMap A' Ω' ϖ') (hγ' : γ' ^ e₀ = algebraMap A' Ω' u')
    (hα' : (γ' * β' ^ m) ^ e₀ = algebraMap A Ω' π) :
    IsTamelyRamifiedWRT A' L' := by
  have :=
    TauCeti.IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_adjoin (K := K') hϖ' hβ'
  obtain ⟨hK'₁_tame, _, _, _⟩ :=
    etale_and_finite_over_adjoin_uniformizer_root (K' := K') hϖ' he₀_pos he₀_A' he₀_res' hβ' hγ'
  let E'' : IntermediateField L' Ω' := IntermediateField.adjoin L' ({β', γ'} : Set Ω')
  have hβ'_mem : β' ∈ E'' :=
    IntermediateField.subset_adjoin L' ({β', γ'} : Set Ω') (Set.mem_insert β' {γ'})
  let ιK'₁ : K'⟮β'⟯ →+* E'' :=
    adjoinSimpleInclusionRingHom
      (fun k' ↦ by rw [IsScalarTower.algebraMap_apply K' L' Ω']; exact E''.algebraMap_mem _)
      hβ'_mem
  let : Algebra K'⟮β'⟯ E'' := ιK'₁.toAlgebra
  have : IsScalarTower A' K'⟮β'⟯ E'' := .of_algebraMap_eq fun a ↦ Subtype.ext (by
    rw [IsScalarTower.algebraMap_apply A' L' E'', IntermediateField.coe_algebraMap_apply,
      ← IsScalarTower.algebraMap_apply A' L' Ω']
    change algebraMap A' Ω' a = (algebraMap A' K'⟮β'⟯ a : Ω')
    rw [IsScalarTower.algebraMap_apply A' K' K'⟮β'⟯, IntermediateField.coe_algebraMap_apply,
      ← IsScalarTower.algebraMap_apply A' K' Ω'])
  have hunr : IsUnramifiedWRT (integralClosure A' K'⟮β'⟯) E'' :=
    isUnramifiedWRT_adjoin_roots_in_overfield h φ hφ hφL hπ he₀_pos hdvd hβ' hγ' hα' (fun _ ↦ rfl)
  exact (hK'₁_tame.trans hunr.isTamelyRamifiedWRT).tower_bot K'

/-- Tamely ramified extensions of a discrete valuation ring are stable under base change: if `L` is
tamely ramified with respect to `A`, then every factor `L'` of `K' ⊗[K] L`, given by a surjective
`K'`-algebra map `φ : K' ⊗[K] L → L'`, is tamely ramified with respect to `A'`. -/
@[stacks 0EXY "tame case"]
theorem IsTamelyRamifiedWRT.baseChange (h : IsTamelyRamifiedWRT A L) (φ : K' ⊗[K] L →ₐ[K'] L')
    (hφ : Function.Surjective φ) : IsTamelyRamifiedWRT A' L' := by
  have : FiniteDimensional K' L' := Module.Finite.of_surjective φ.toLinearMap hφ
  have : Algebra.FormallyUnramified K L := .of_isSeparable K L
  have : Algebra.FormallyUnramified K' L' := .of_surjective φ hφ
  have : Algebra.IsSeparable K' L' := (Algebra.FormallyUnramified.iff_isSeparable K' L').mp ‹_›
  obtain ⟨π, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨ϖ', hϖ'⟩ := _root_.IsDiscreteValuationRing.exists_irreducible A'
  have hπA' : algebraMap A A' π ≠ 0 := fun h0 ↦ by
    have hK' : algebraMap A K' π = 0 := by
      rw [IsScalarTower.algebraMap_apply A A' K', h0, map_zero]
    rw [IsScalarTower.algebraMap_apply A K K', map_eq_zero,
      IsFractionRing.to_map_eq_zero_iff] at hK'
    exact hπ.ne_zero hK'
  obtain ⟨m, u', hπ_eq⟩ := _root_.IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπA' hϖ'
  obtain ⟨e₀, he₀_pos, he₀_res, hdvd⟩ := h.exists_ramificationIdx_dvd (K := K)
  have he₀_A : IsUnit (e₀ : A) :=
    (isUnit_map_iff (residue A) _).mp (by rw [map_natCast]; exact he₀_res)
  have he₀_A' : IsUnit (e₀ : A') := by simpa using he₀_A.map (algebraMap A A')
  have he₀_res' : IsUnit (e₀ : A' ⧸ maximalIdeal A') := by
    simpa using he₀_A'.map (Ideal.Quotient.mk (maximalIdeal A'))
  -- Embed `L` into `L'` via `φ` and extract `e₀`-th roots in `AlgebraicClosure L'`.
  let jL : L →+* L' :=
    φ.toRingHom.comp (Algebra.TensorProduct.includeRight : L →ₐ[K] K' ⊗[K] L).toRingHom
  let : Algebra L L' := jL.toAlgebra
  let : Algebra K L' := ((algebraMap K' L').comp (algebraMap K K')).toAlgebra
  let : Algebra A L' := ((algebraMap A' L').comp (algebraMap A A')).toAlgebra
  have : IsScalarTower K K' L' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A A' L' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower K L L' := .of_algebraMap_eq fun x ↦ by
    have hx : (1 : K') ⊗ₜ[K] algebraMap K L x =
        algebraMap K' (K' ⊗[K] L) (algebraMap K K' x) := by
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul,
        ← Algebra.algebraMap_eq_smul_one, ← Algebra.TensorProduct.algebraMap_apply,
        IsScalarTower.algebraMap_apply K K' (K' ⊗[K] L)]
    exact (φ.commutes (algebraMap K K' x)).symm.trans (congrArg φ hx.symm)
  have : IsScalarTower A K L' := .of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply A K K',
      IsScalarTower.algebraMap_apply A A' K', ← IsScalarTower.algebraMap_apply A' K' L']
  let Ω' := AlgebraicClosure L'
  obtain ⟨β', hβ'⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A' Ω' ϖ') he₀_pos
  obtain ⟨γ', hγ'⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A' Ω' u') he₀_pos
  have hα' : (γ' * β' ^ m) ^ e₀ = algebraMap A Ω' π := by
    rw [mul_pow, ← pow_mul, mul_comm m e₀, pow_mul, hγ', hβ', ← map_pow, ← map_mul, ← hπ_eq,
      ← IsScalarTower.algebraMap_apply A A' Ω']
  exact isTamelyRamifiedWRT_of_roots_in_overfield h φ hφ (fun _ ↦ rfl) hπ hϖ' he₀_pos he₀_A'
    he₀_res' hdvd hβ' hγ' hα'

end BaseChange

end TauCeti.Algebra
