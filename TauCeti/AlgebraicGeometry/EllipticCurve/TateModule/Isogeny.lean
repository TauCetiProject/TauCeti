/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.LocalPolynomial
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.PotentialGoodReduction
-- Proof-only: the dual isogeny, with `φ̂ ∘ φ = [deg φ]` on points.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Basic
-- Proof-only: a nonzero morphism is onto on points over an algebraically closed field.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring
-- Proof-only: base change of morphisms commutes with the Galois action on points.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.BaseChange
-- Proof-only: an isogeny compares quadratic relations of a field endomorphism at `P` and `φ P`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.QuadraticRelation
-- Proof-only: isogenous curves have isogenous minimal equations.
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Isogeny
-- Proof-only: a prime different from the residue characteristic.
import TauCeti.Algebra.CharP.Lemmas
-- Proof-only: a `p`-primary image of a torsion point has a `p`-primary preimage.
import TauCeti.GroupTheory.Torsion
-- Proof-only: a prime different from the residue characteristic is nonzero in `K^{alg}`.
import TauCeti.NumberTheory.LocalField.NatCastValuation
-- Proof-only: Frobenius satisfies `X² - a_q X + q` on prime-to-`p` torsion at good reduction.
import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Frobenius
-- Proof-only: `E[ℓ]` is free of rank two over `ℤ/ℓ`, so it has a point of order `ℓ`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Torsion.Structure

/-!
# Isogenous curves have the same local factor at potentially good places

Let `φ : E₁ → E₂` be an isogeny of elliptic curves over a field `F`, and let `K` be an
algebraically closed extension of `F`. An `F`-automorphism `σ` of `K` that fixes every point of
`E₁(K)` of `ℓ`-power order also fixes every point of `E₂(K)` of `ℓ`-power order. Indeed `φ` is
onto `E₂(K)`; a point `Q` of order dividing `ℓ ^ k` is `φ P`, and `P` is killed by `deg φ · ℓ ^ k`,
because `φ̂ ∘ φ = [deg φ]`. Writing `deg φ = ℓ ^ a · m` with `ℓ ∤ m` and `u m ≡ 1 mod ℓ ^ k`, the
point `P₀ = u m P` has `ℓ`-power order and `φ P₀ = Q`
(`TauCeti.exists_mem_primaryComponent_apply_eq`). Since `φ` is defined over `F`, it commutes
with `σ`, so `σ Q = φ (σ P₀) = φ P₀ = Q`. Applied to `φ` and to its dual, this says that `σ` acts
trivially on the Tate module `T_ℓ E₁` exactly when it does on `T_ℓ E₂`.

Over a nonarchimedean local field `K`, the criteria of Néron, Ogg and Shafarevich read good
reduction and potential good reduction off the action of the inertia subgroup of
`Gal(K^{alg}/K)` on `T_ℓ E`, for a prime `ℓ` different from the residue characteristic. So
**isogenous curves have good reduction together** (Silverman AEC VII.7.2) and **potential good
reduction together**. Good reduction is a property of a minimal equation, so the first statement
is made for minimal equations and, for arbitrary equations, for the chosen minimal equations
`W.minimal 𝒪[K]`, whose reduction type decides the local factor of the `L`-function
(`WeierstrassCurve.localPolynomial`).

At good reduction **isogenous curves have reductions with the same Frobenius trace** `a_q`. An
arithmetic Frobenius lift `σ` satisfies `σ (σ P) = a_q • σ P - q • P` on the prime-to-`p` torsion
of each curve (`WeierstrassCurve.Affine.Point.map_map_eq_of_isArithFrobeniusLift`). If `P` is a
point of `E₁` of prime order `ℓ ≠ p`, applying `φ` to the relation for `E₁` and comparing with the
relation for `E₂` at `φ P` gives `(a₁ - a₂) • φ P = 0`, so `deg φ · (a₁ - a₂)` kills `P`. Taking
`ℓ` larger than this integer forces `a₁ = a₂`. The local polynomial is `1 - a_q T + q T²` at good
reduction, so isogenous curves have the same local polynomial there. At bad reduction that is
potentially good the local polynomial is `1`
(`WeierstrassCurve.localPolynomial_eq_one_of_hasPotentialGoodReduction_of_not_hasGoodReduction`),
so **isogenous curves have the same local polynomial wherever they have potential good
reduction**. This file does not separate split from nonsplit multiplicative reduction, the case
of reduction that is not potentially good.

## Main results

* `TauCeti.Isogeny.point_map_eq_self_of_nsmul_eq_zero`: an automorphism fixing the `ℓ`-power
  torsion of `E₁` fixes the `ℓ`-power torsion of an isogenous `E₂`.
* `TauCeti.Isogeny.tateModuleGaloisRepresentation_eq_one_iff`: an automorphism acts trivially on
  `T_ℓ E₁` exactly when it acts trivially on `T_ℓ E₂`.
* `TauCeti.Isogeny.hasGoodReduction_iff`: isogenous minimal equations over a local field have good
  reduction together.
* `TauCeti.Isogeny.hasGoodReduction_minimal_iff`: the same for the chosen minimal equations of
  isogenous curves.
* `TauCeti.Isogeny.hasPotentialGoodReduction_iff`: isogenous curves over a local field have
  potential good reduction together.
* `TauCeti.Isogeny.frobeniusTrace_reduction_eq`: isogenous minimal equations with good reduction
  have reductions with the same Frobenius trace.
* `TauCeti.Isogeny.localPolynomial_eq_of_hasGoodReduction`: at good reduction, isogenous curves
  have the same local polynomial.
* `TauCeti.Isogeny.localPolynomial_eq_of_hasPotentialGoodReduction`: at potential good reduction,
  isogenous curves have the same local polynomial.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.1, V.2.3.1,
  VII.7.1–VII.7.3.
-/

public section

open ValuativeRel WeierstrassCurve

namespace TauCeti.Isogeny

section Torsion

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K]

/-- **Isogenies carry fixed `ℓ`-power torsion to fixed `ℓ`-power torsion.** Let `φ : W₁ → W₂` be
an isogeny over `F`, let `K` be an algebraically closed extension of `F`, and let `ℓ` be a prime.
If an `F`-automorphism `σ` of `K` fixes every point of `W₁(K)` of order dividing a power of `ℓ`,
then it fixes every such point of `W₂(K)`. -/
theorem point_map_eq_self_of_nsmul_eq_zero {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic]
    [W₂.IsElliptic] (φ : Isogeny W₁ W₂) {ℓ : ℕ} (hℓ : ℓ.Prime) {σ : K ≃ₐ[F] K}
    (h : ∀ k, ∀ P : (W₁⁄K).toAffine.Point, ℓ ^ k • P = 0 → Affine.Point.map σ.toAlgHom P = P)
    {k : ℕ} {Q : (W₂⁄K).toAffine.Point} (hQ : ℓ ^ k • Q = 0) :
    Affine.Point.map σ.toAlgHom Q = Q := by
  set f := (Hom.ofIsogeny φ).map (algebraMap F K)
  have hf : f ≠ 0 := by
    rw [Ne, Hom.map_eq_zero_iff]
    exact Hom.ofIsogeny_ne_zero φ
  obtain ⟨P, rfl⟩ := Hom.pointMap_surjective hf Q
  -- restate `hQ` with the group law of the codomain of `f`, the same up to unfolding `W₂⁄K`
  replace hQ : ℓ ^ k • f.pointMap P = 0 := hQ
  -- `P` is killed by `deg φ · ℓ ^ k`, since `f̂ (f (ℓ ^ k • P)) = deg φ • ℓ ^ k • P`
  have hP : IsOfFinAddOrder P := by
    have hd := f.dual_pointMap_pointMap (ℓ ^ k • P)
    simp only [Hom.pointMap_nsmul, hQ, Hom.pointMap_zero, smul_smul] at hd
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨_, Nat.pos_of_ne_zero <| mul_ne_zero
      ((Hom.degree_eq_zero_iff f).not.2 hf) (pow_ne_zero k hℓ.ne_zero), hd.symm⟩
  -- so some point `P₀` of `ℓ`-power order has the same image as `P`
  obtain ⟨P₀, ⟨n, hP₀⟩, hfP₀⟩ :=
    exists_mem_primaryComponent_apply_eq f.pointMapHom hℓ hP ⟨k, by simpa using hQ⟩
  -- `f` commutes with `σ`, which fixes `P₀`
  have hσ := Hom.pointMap_map_algebraMap_map (Hom.ofIsogeny φ) σ.toAlgHom P₀
  simp only [Hom.pointMapHom_apply] at hfP₀
  rw [h _ _ hP₀, hfP₀] at hσ
  exact hσ.symm

variable {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **Isogenous curves have the same automorphisms acting trivially on the Tate module.** Let
`φ : W₁ → W₂` be an isogeny over `F`, let `K` be an algebraically closed extension of `F`, and let
`ℓ` be a prime invertible in `K`. If an `F`-automorphism `σ` of `K` acts trivially on `T_ℓ W₁`,
then it acts trivially on `T_ℓ W₂`. -/
theorem tateModuleGaloisRepresentation_eq_one (φ : Isogeny W₁.toAffine W₂.toAffine) {ℓ : ℕ}
    [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) {σ : K ≃ₐ[F] K}
    (h : W₁.tateModuleGaloisRepresentation ℓ σ = 1) :
    W₂.tateModuleGaloisRepresentation ℓ σ = 1 := by
  rw [WeierstrassCurve.tateModuleGaloisRepresentation_eq_one_iff hℓ] at h ⊢
  exact fun _ _ ↦ φ.point_map_eq_self_of_nsmul_eq_zero Fact.out h

/-- **Isogenous curves have the same automorphisms acting trivially on the Tate module**: for an
isogeny `φ : W₁ → W₂` over `F`, an algebraically closed extension `K` of `F` and a prime `ℓ`
invertible in `K`, an `F`-automorphism of `K` acts trivially on `T_ℓ W₁` exactly when it acts
trivially on `T_ℓ W₂`. -/
theorem tateModuleGaloisRepresentation_eq_one_iff (φ : Isogeny W₁.toAffine W₂.toAffine) {ℓ : ℕ}
    [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) {σ : K ≃ₐ[F] K} :
    W₁.tateModuleGaloisRepresentation ℓ σ = 1 ↔ W₂.tateModuleGaloisRepresentation ℓ σ = 1 :=
  ⟨φ.tateModuleGaloisRepresentation_eq_one hℓ, φ.dual.tateModuleGaloisRepresentation_eq_one hℓ⟩

end Torsion

section LocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **Isogenous curves have good reduction together** (Silverman AEC VII.7.2). Let `W₁` and `W₂`
be elliptic curves over a nonarchimedean local field `K`, given by minimal equations. If there is
an isogeny `W₁ → W₂`, then `W₁` has good reduction exactly when `W₂` does. -/
theorem hasGoodReduction_iff [IsMinimal 𝒪[K] W₁] [IsMinimal 𝒪[K] W₂]
    (φ : Isogeny W₁.toAffine W₂.toAffine) :
    W₁.HasGoodReduction 𝒪[K] ↔ W₂.HasGoodReduction 𝒪[K] := by
  classical
  obtain ⟨ℓ, hℓ, hℓ₀⟩ := exists_prime_natCast_ne_zero 𝓀[K]
  have := Fact.mk hℓ
  rw [W₁.hasGoodReduction_iff_tateModuleGaloisRepresentation_eq_one hℓ₀,
    W₂.hasGoodReduction_iff_tateModuleGaloisRepresentation_eq_one hℓ₀]
  exact forall₂_congr fun σ _ ↦
    φ.tateModuleGaloisRepresentation_eq_one_iff <|
      natCast_ne_zero_of_residueField_natCast_ne_zero hℓ₀

/-- **Isogenous curves have good reduction together**, read on the chosen minimal equations: if
there is an isogeny `W₁ → W₂` of elliptic curves over a nonarchimedean local field `K`, then the
minimal equation of `W₁` has good reduction exactly when that of `W₂` does. -/
theorem hasGoodReduction_minimal_iff (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (W₁.minimal 𝒪[K]).HasGoodReduction 𝒪[K] ↔ (W₂.minimal 𝒪[K]).HasGoodReduction 𝒪[K] := by
  obtain ⟨ψ⟩ := φ.nonempty_isogeny_minimal 𝒪[K]
  exact ψ.hasGoodReduction_iff

/-- **Isogenous curves have potential good reduction together.** If there is an isogeny
`W₁ → W₂` of elliptic curves over a nonarchimedean local field `K`, then `W₁` has potential good
reduction exactly when `W₂` does. -/
theorem hasPotentialGoodReduction_iff (φ : Isogeny W₁.toAffine W₂.toAffine) :
    W₁.HasPotentialGoodReduction 𝒪[K] ↔ W₂.HasPotentialGoodReduction 𝒪[K] := by
  classical
  obtain ⟨ℓ, hℓ, hℓ₀⟩ := exists_prime_natCast_ne_zero 𝓀[K]
  have := Fact.mk hℓ
  -- the elements of inertia acting trivially on one Tate module act trivially on the other
  have key {V₁ V₂ : WeierstrassCurve K} [V₁.IsElliptic] [V₂.IsElliptic]
      (ψ : Isogeny V₁.toAffine V₂.toAffine) (h : V₁.HasPotentialGoodReduction 𝒪[K]) :
      V₂.HasPotentialGoodReduction 𝒪[K] := by
    obtain ⟨M, _, hM⟩ := h.exists_tateModuleGaloisRepresentation_eq_one
    exact V₂.hasPotentialGoodReduction_of_tateModuleGaloisRepresentation_eq_one M hℓ₀
      fun σ hσ hσM ↦ ψ.tateModuleGaloisRepresentation_eq_one
        (natCast_ne_zero_of_residueField_natCast_ne_zero hℓ₀) (hM ℓ hℓ₀ σ hσ hσM)
  exact ⟨key φ, key φ.dual⟩

/-- **Isogenous curves have reductions with the same Frobenius trace** at good reduction. Let
`W₁` and `W₂` be elliptic curves over a nonarchimedean local field `K`, given by minimal equations,
and let `W₁` have good reduction. If there is an isogeny `W₁ → W₂`, the reductions of `W₁` and `W₂`
have the same Frobenius trace `a_q = q + 1 - #E(k)` over the residue field `k`. -/
theorem frobeniusTrace_reduction_eq [IsMinimal 𝒪[K] W₁] [IsMinimal 𝒪[K] W₂]
    (φ : Isogeny W₁.toAffine W₂.toAffine) (h : W₁.HasGoodReduction 𝒪[K]) :
    (W₁.reduction 𝒪[K]).frobeniusTrace = (W₂.reduction 𝒪[K]).frobeniusTrace := by
  classical
  have h₂ : W₂.HasGoodReduction 𝒪[K] := φ.hasGoodReduction_iff.mp h
  set a₁ := (W₁.reduction 𝒪[K]).frobeniusTrace
  set a₂ := (W₂.reduction 𝒪[K]).frobeniusTrace
  by_contra hne
  -- `N = deg φ · (a₁ - a₂)` is nonzero; pick a prime `ℓ > |N|` away from the residue characteristic
  set N : ℤ := φ.degree * (a₁ - a₂)
  have hN : N ≠ 0 := mul_ne_zero (by exact_mod_cast φ.degree_pos.ne') (sub_ne_zero.mpr hne)
  obtain ⟨ℓ, hℓ, hNℓ, hℓ₀⟩ := exists_prime_lt_natCast_ne_zero 𝓀[K] N.natAbs
  have := Fact.mk hℓ
  -- a point `P` of order `ℓ` on `W₁` over `K^{alg}`
  obtain ⟨b⟩ := nonempty_basis_torsionBy (W₁⁄(AlgebraicClosure K)) ℓ
    (natCast_ne_zero_of_residueField_natCast_ne_zero hℓ₀)
  set P : (W₁⁄(AlgebraicClosure K)).toAffine.Point := (b 0).1
  have hP0 : P ≠ 0 := fun h0 ↦ b.ne_zero 0 (Subtype.ext h0)
  have hℓP : ℓ • P = 0 := AddSubgroup.torsionBy.nsmul_iff.mp (b 0).2
  -- an arithmetic Frobenius lift `σ` satisfies `σ² - a σ + q = 0` on the `ℓ`-torsion of both
  -- curves, at `P` and at `φ P`; comparing them, `N` kills `P`
  obtain ⟨σ, hσ⟩ := exists_isArithFrobeniusLift K
  set f := (Hom.ofIsogeny φ).map (algebraMap K (AlgebraicClosure K))
  set Q : (W₂⁄(AlgebraicClosure K)).toAffine.Point := f.pointMap P
  have hℓQ : ℓ • Q = 0 :=
    (f.pointMap_nsmul ℓ P).symm.trans ((congrArg f.pointMap hℓP).trans f.pointMap_zero)
  have hNP : N • P = 0 := φ.degree_mul_sub_zsmul_eq_zero rfl
    (Affine.Point.map_map_eq_of_isArithFrobeniusLift h hσ hℓ₀ hℓP)
    (Affine.Point.map_map_eq_of_isArithFrobeniusLift h₂ hσ hℓ₀ hℓQ)
  -- hence `ℓ ∣ N`, which is impossible
  have hdvd : (ℓ : ℤ) ∣ N := by
    rw [← addOrderOf_eq_prime hℓP hP0]
    exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr hNP
  exact hN (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by simpa using hNℓ))

/-- **Isogenous curves have the same local factor at good reduction.** If there is an isogeny
`W₁ → W₂` of elliptic curves over a nonarchimedean local field `K` and the minimal equation of `W₁`
has good reduction, then the local polynomials (`WeierstrassCurve.localPolynomial`) of `W₁` and
`W₂` agree, both being `1 - a_q T + q T²` with the same Frobenius trace `a_q`. -/
theorem localPolynomial_eq_of_hasGoodReduction (φ : Isogeny W₁.toAffine W₂.toAffine)
    (h : (W₁.minimal 𝒪[K]).HasGoodReduction 𝒪[K]) :
    W₁.localPolynomial 𝒪[K] = W₂.localPolynomial 𝒪[K] := by
  obtain ⟨ψ⟩ := φ.nonempty_isogeny_minimal 𝒪[K]
  rw [WeierstrassCurve.localPolynomial_eq_of_hasGoodReduction _ W₁ h,
    WeierstrassCurve.localPolynomial_eq_of_hasGoodReduction _ W₂ (ψ.hasGoodReduction_iff.mp h),
    ψ.frobeniusTrace_reduction_eq h]

/-- **Isogenous curves have the same local factor at potential good reduction.** If there is an
isogeny `W₁ → W₂` of elliptic curves over a nonarchimedean local field `K` and `W₁` has potential
good reduction, then the local polynomials (`WeierstrassCurve.localPolynomial`) of `W₁` and `W₂`
agree: at good reduction they are `1 - a_q T + q T²` with the same `a_q`, and at bad reduction
both are `1`. -/
theorem localPolynomial_eq_of_hasPotentialGoodReduction (φ : Isogeny W₁.toAffine W₂.toAffine)
    (h : W₁.HasPotentialGoodReduction 𝒪[K]) :
    W₁.localPolynomial 𝒪[K] = W₂.localPolynomial 𝒪[K] := by
  by_cases hb : (W₁.minimal 𝒪[K]).HasGoodReduction 𝒪[K]
  · exact φ.localPolynomial_eq_of_hasGoodReduction hb
  rw [localPolynomial_eq_one_of_hasPotentialGoodReduction_of_not_hasGoodReduction _ h hb,
    localPolynomial_eq_one_of_hasPotentialGoodReduction_of_not_hasGoodReduction _
      (φ.hasPotentialGoodReduction_iff.1 h) (φ.hasGoodReduction_minimal_iff.not.1 hb)]

end LocalField

end TauCeti.Isogeny
