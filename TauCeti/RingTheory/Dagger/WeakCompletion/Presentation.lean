/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.WeakCompletion.Noetherian
import Mathlib.RingTheory.MvPolynomial.Ideal
import TauCeti.RingTheory.Dagger.WeakCompletion.Jacobson
import TauCeti.RingTheory.Ideal.KrullIntersection

/-!
# Quotient presentations of Monsky–Washnitzer weak completions

Let `O` be a commutative ring, `π : O`, and `f : R →ₐ[O] S` a surjective homomorphism of finitely
generated `O`-algebras. Without any noetherian hypothesis, the kernel of the induced surjection
`map π f : R† →ₐ[O] S†` of weak completions is the `π`-adic closure
`⨅ n, (ker f) · R† ⊔ (π)ⁿ` of the extended ideal `(ker f) · R†` (`ker_map_eq_iInf_of_surjective`).

When `R†` is noetherian, `π` lies in the Jacobson radical of `R†` (`algebraMap_mem_jacobson`), so
Krull's intersection theorem implies that every ideal of `R†` is `π`-adically closed
(`iInf_sup_span_pow_eq`). Consequently `ker (map π f) = (ker f) · R†` (`ker_map_of_surjective`),
and for any ideal `I` of `R` the weak completion of `R ⧸ I` is canonically `R† ⧸ (I · R†)`
(`quotientAlgEquiv`).

Over the noetherian valuation unit ball `O = K°` of a complete ultrametric field `K` with a nonzero
topologically nilpotent parameter `π ∈ O`, `O[X_σ]†` is the integral Monsky–Washnitzer algebra
`O⟨X_σ⟩†` (`polynomialEquiv`), which is noetherian (`intWashnitzerAlgebra.isNoetherianRing`).
Combining the two gives the fundamental presentation of weak completions as quotients of integral
Monsky–Washnitzer algebras (`presentationAlgEquiv`, `mvPolynomialQuotientEquiv`): for every finite
generating family `x : σ → S` with relation ideal `I = ker (aeval x)`,

```text
O⟨X_σ⟩† ⧸ (I · O⟨X_σ⟩†) ≃ₐ[O] S†,
```

compatibly with evaluation of overconvergent series and with the canonical map `S → S†`.

## Main definitions and results

* `TauCeti.Dagger.weakCompletion.ker_map_eq_iInf_of_surjective`: for surjective `f : R →ₐ[O] S`,
  `ker (map π f) = ⨅ n, (ker f).map (of π R) ⊔ (π)ⁿ` without noetherianity.
* `TauCeti.Dagger.weakCompletion.iInf_sup_span_pow_eq`: when `R†` is noetherian, every ideal `J` of
  `R†` satisfies `⨅ n, J ⊔ (π)ⁿ = J`.
* `TauCeti.Dagger.weakCompletion.ker_map_of_surjective` and
  `TauCeti.Dagger.weakCompletion.quotientKerMapAlgEquiv`: when `R†` is noetherian and `f` is
  surjective, `ker (map π f) = (ker f).map (of π R)` and `R† ⧸ (ker f).map (of π R) ≃ₐ[O] S†`.
* `TauCeti.Dagger.weakCompletion.quotientAlgEquiv`: `(R† ⧸ I.map (of π R)) ≃ₐ[O] (R ⧸ I)†`.
* `TauCeti.Dagger.weakCompletion.ker_evalIntWashnitzerAlgebra`: identification of the kernel of
  integral overconvergent evaluation at a finite generating family `x` as
  `(ker (aeval x)).map ofMvPolynomial`.
* `TauCeti.Dagger.weakCompletion.presentationAlgEquiv` and
  `TauCeti.Dagger.weakCompletion.mvPolynomialQuotientEquiv`: quotient presentations of `S†` and
  `(O[X_σ] ⧸ I)†` by the integral Monsky–Washnitzer algebra `O⟨X_σ⟩†`.

## References

* P. Monsky and G. Washnitzer, *Formal cohomology. I*, Ann. of Math. 88 (1968), §2, Theorem 2.1.
* M. van der Put, *The cohomology of Monsky and Washnitzer*, Mém. Soc. Math. France 23 (1986),
  §2, (2.1)–(2.2).
* H. Matsumura, *Commutative Ring Theory*, Theorem 8.10.
-/

public section

namespace TauCeti.Dagger.weakCompletion

open MvPolynomial

section General

variable {O R S : Type*} [CommRing O] [CommRing R] [CommRing S]
  [Algebra O R] [Algebra O S] (π : O)
  [Algebra.FiniteType O R] [Algebra.FiniteType O S]

/-- For a surjective algebra homomorphism `f : R →ₐ[O] S`, the kernel of `map π f : R† →ₐ[O] S†`
is the `π`-adic closure `⨅ n, (ker f).map (of π R) ⊔ (π)ⁿ` of the extended kernel. No
noetherianity, flatness, or separatedness hypothesis is needed. -/
theorem ker_map_eq_iInf_of_surjective {f : R →ₐ[O] S} (hf : Function.Surjective f) :
    RingHom.ker (map π f) =
      ⨅ n : ℕ, (RingHom.ker f).map (of π R) ⊔
        Ideal.span {algebraMap O (weakCompletion π R) π} ^ n := by
  have hker_le : (RingHom.ker f).map (of π R) ≤ RingHom.ker (map π f) := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker, map_of, RingHom.mem_ker.mp hr, map_zero]
  have hmap_pow (n : ℕ) :
      (Ideal.span {algebraMap O (weakCompletion π R) π} ^ n).map (map π f) ≤
        Ideal.span {algebraMap O (weakCompletion π S) π} ^ n := by
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, AlgHom.commutes]
  apply le_antisymm
  · intro z hz
    rw [Ideal.mem_iInf]
    intro n
    obtain ⟨r, hr⟩ := exists_sub_mem_span_pow π z n
    have hfr : f r ∈ Ideal.span {algebraMap O S π} ^ n := by
      have himg := hmap_pow n (Ideal.mem_map_of_mem _ hr)
      rw [map_sub, RingHom.mem_ker.mp hz, zero_sub, map_of, neg_mem_iff, ← ker_eval] at himg
      have hev := RingHom.mem_ker.mp himg
      rwa [eval_of, Ideal.Quotient.eq_zero_iff_mem] at hev
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hfr
    obtain ⟨s, hs⟩ := hfr
    obtain ⟨r', rfl⟩ := hf s
    have h1 : of π R (r - algebraMap O R π ^ n * r') ∈ (RingHom.ker f).map (of π R) := by
      refine Ideal.mem_map_of_mem _ ?_
      rw [RingHom.mem_ker, map_sub, map_mul, map_pow, f.commutes, ← hs, sub_self]
    have h2 : algebraMap O (weakCompletion π R) π ^ n * of π R r' ∈
        Ideal.span {algebraMap O (weakCompletion π R) π} ^ n :=
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.subset_span rfl) n)
    have hsum : z = of π R (r - algebraMap O R π ^ n * r') +
        ((z - of π R r) + algebraMap O (weakCompletion π R) π ^ n * of π R r') := by
      rw [map_sub, map_mul, map_pow, AlgHom.commutes]
      ring
    exact hsum ▸ Ideal.add_mem _ (Ideal.mem_sup_left h1)
      (Ideal.mem_sup_right (Ideal.add_mem _ hr h2))
  · intro z hz
    rw [RingHom.mem_ker]
    refine (IsHausdorff.eq_iff_smodEq (I := Ideal.span {algebraMap O (weakCompletion π S) π})).mpr
      fun n ↦ ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp (Ideal.mem_iInf.mp hz n)
    rw [map_add, RingHom.mem_ker.mp (hker_le hu), zero_add]
    exact hmap_pow n (Ideal.mem_map_of_mem _ hv)

/-- When the weak completion `R†` is noetherian, every ideal `J` of `R†` is `π`-adically closed:
`⨅ n, J ⊔ (π)ⁿ = J`. -/
theorem iInf_sup_span_pow_eq [IsNoetherianRing (weakCompletion π R)]
    (J : Ideal (weakCompletion π R)) :
    (⨅ n : ℕ, J ⊔ Ideal.span {algebraMap O (weakCompletion π R) π} ^ n) = J :=
  (Ideal.span {algebraMap O (weakCompletion π R) π}).iInf_sup_pow_eq_of_le_jacobson
    (span_algebraMap_le_jacobson π R) J

/-- When `R†` is noetherian and `f : R →ₐ[O] S` is surjective, the kernel of `map π f : R† →ₐ[O] S†`
is the ideal generated by the image of `ker f` in `R†`. -/
theorem ker_map_of_surjective [IsNoetherianRing (weakCompletion π R)] {f : R →ₐ[O] S}
    (hf : Function.Surjective f) :
    RingHom.ker (map π f) = (RingHom.ker f).map (of π R) :=
  (ker_map_eq_iInf_of_surjective π hf).trans (iInf_sup_span_pow_eq π _)

/-- A surjective algebra map `f : R →ₐ[O] S` with `R†` noetherian identifies `S†` with the quotient
of `R†` by the extended kernel of `f`. -/
noncomputable def quotientKerMapAlgEquiv [IsNoetherianRing (weakCompletion π R)] {f : R →ₐ[O] S}
    (hf : Function.Surjective f) :
    (weakCompletion π R ⧸ (RingHom.ker f).map (of π R)) ≃ₐ[O] weakCompletion π S :=
  (Ideal.quotientEquivAlgOfEq O (ker_map_of_surjective π hf).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (map_surjective π f hf))

@[simp]
theorem quotientKerMapAlgEquiv_mk [IsNoetherianRing (weakCompletion π R)] {f : R →ₐ[O] S}
    (hf : Function.Surjective f) (z : weakCompletion π R) :
    quotientKerMapAlgEquiv π hf (Ideal.Quotient.mk _ z) = map π f z := by
  simp [quotientKerMapAlgEquiv]

@[simp]
theorem quotientKerMapAlgEquiv_symm_map [IsNoetherianRing (weakCompletion π R)] {f : R →ₐ[O] S}
    (hf : Function.Surjective f) (z : weakCompletion π R) :
    (quotientKerMapAlgEquiv π hf).symm (map π f z) = Ideal.Quotient.mk _ z := by
  apply (quotientKerMapAlgEquiv π hf).injective
  simp

@[simp]
theorem quotientKerMapAlgEquiv_symm_of [IsNoetherianRing (weakCompletion π R)] {f : R →ₐ[O] S}
    (hf : Function.Surjective f) (r : R) :
    (quotientKerMapAlgEquiv π hf).symm (of π S (f r)) = Ideal.Quotient.mk _ (of π R r) := by
  apply (quotientKerMapAlgEquiv π hf).injective
  simp

/-- When `R†` is noetherian, the kernel of `R† → (R ⧸ I)†` is `I.map (of π R)`. -/
theorem ker_map_mkₐ [IsNoetherianRing (weakCompletion π R)] (I : Ideal R) :
    RingHom.ker (map π (Ideal.Quotient.mkₐ O I)) = I.map (of π R) := by
  rw [ker_map_of_surjective π Ideal.Quotient.mk_surjective, ← RingHom.ker_coe_toRingHom,
    Ideal.Quotient.mkₐ_ker]

/-- When `R†` is noetherian, weak completion commutes with quotients by arbitrary ideals:
`(R† ⧸ I · R†) ≃ₐ[O] (R ⧸ I)†`. -/
noncomputable def quotientAlgEquiv [IsNoetherianRing (weakCompletion π R)] (I : Ideal R) :
    (weakCompletion π R ⧸ I.map (of π R)) ≃ₐ[O] weakCompletion π (R ⧸ I) :=
  (Ideal.quotientEquivAlgOfEq O (ker_map_mkₐ π I).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (map_surjective π _ Ideal.Quotient.mk_surjective))

@[simp]
theorem quotientAlgEquiv_mk [IsNoetherianRing (weakCompletion π R)] (I : Ideal R)
    (z : weakCompletion π R) :
    quotientAlgEquiv π I (Ideal.Quotient.mk _ z) = map π (Ideal.Quotient.mkₐ O I) z := by
  simp [quotientAlgEquiv]

theorem quotientAlgEquiv_mk_of [IsNoetherianRing (weakCompletion π R)] (I : Ideal R) (r : R) :
    quotientAlgEquiv π I (Ideal.Quotient.mk _ (of π R r)) =
      of π (R ⧸ I) (Ideal.Quotient.mk I r) := by
  simp

@[simp]
theorem quotientAlgEquiv_symm_map [IsNoetherianRing (weakCompletion π R)] (I : Ideal R)
    (z : weakCompletion π R) :
    (quotientAlgEquiv π I).symm (map π (Ideal.Quotient.mkₐ O I) z) =
      Ideal.Quotient.mk _ z := by
  apply (quotientAlgEquiv π I).injective
  simp

@[simp]
theorem quotientAlgEquiv_symm_of_mk [IsNoetherianRing (weakCompletion π R)] (I : Ideal R)
    (r : R) :
    (quotientAlgEquiv π I).symm (of π (R ⧸ I) (Ideal.Quotient.mk I r)) =
      Ideal.Quotient.mk _ (of π R r) := by
  apply (quotientAlgEquiv π I).injective
  simp

end General

section IntWashnitzerPresentation

variable {K S σ : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CommRing S] [Algebra (Subring.unitClosedBall K) S]
  [Algebra.FiniteType (Subring.unitClosedBall K) S] [Finite σ]

local notation "O" => Subring.unitClosedBall K

/-- Over a noetherian valuation unit ball `O = K°`, the kernel of integral overconvergent
evaluation `O⟨X_σ⟩† →ₐ[O] S†` at a finite generating family `x : σ → S` is the ideal generated in
`O⟨X_σ⟩†` by the polynomial relations among the `xᵢ`. -/
theorem ker_evalIntWashnitzerAlgebra [IsNoetherianRing O] {π : O} (hπ : π ≠ 0)
    (hπ1 : ‖(π : K)‖ < 1) (x : σ → S) (hx : Algebra.adjoin O (Set.range x) = ⊤) :
    RingHom.ker (evalIntWashnitzerAlgebra hπ hπ1 x) =
      (RingHom.ker (MvPolynomial.aeval x)).map (intWashnitzerAlgebra.ofMvPolynomial σ K) := by
  have : IsNoetherianRing (weakCompletion π (MvPolynomial σ O)) := isNoetherianRing hπ hπ1
  have haeval : Function.Surjective (MvPolynomial.aeval (R := O) x) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
    exact hx
  have hker := ker_map_of_surjective π haeval
  let e := polynomialEquiv (σ := σ) hπ hπ1
  have hcomp : e.toAlgHom.comp (of π (MvPolynomial σ O)) =
      intWashnitzerAlgebra.ofMvPolynomial σ K :=
    AlgHom.ext fun p ↦ polynomialEquiv_of hπ hπ1 p
  rw [← hcomp, ← Ideal.map_mapₐ]
  ext g
  rw [RingHom.mem_ker, evalIntWashnitzerAlgebra_def, AlgHom.comp_apply, ← RingHom.mem_ker, hker]
  exact Ideal.symm_apply_mem_of_equiv_iff (f := e.toRingEquiv)

/-- **Monsky–Washnitzer presentation of a weak completion.** Over a noetherian valuation unit ball
`O = K°`, every finite generating family `x : σ → S` presents `S†` as the quotient of the integral
Monsky–Washnitzer algebra `O⟨X_σ⟩†` by the polynomial relation ideal `ker (aeval x) · O⟨X_σ⟩†`. -/
noncomputable def presentationAlgEquiv [IsNoetherianRing O] {π : O} (hπ : π ≠ 0)
    (hπ1 : ‖(π : K)‖ < 1) (x : σ → S) (hx : Algebra.adjoin O (Set.range x) = ⊤) :
    (intWashnitzerAlgebra σ K ⧸
      (RingHom.ker (MvPolynomial.aeval x)).map (intWashnitzerAlgebra.ofMvPolynomial σ K)) ≃ₐ[O]
      weakCompletion π S :=
  (Ideal.quotientEquivAlgOfEq O (ker_evalIntWashnitzerAlgebra hπ hπ1 x hx).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (evalIntWashnitzerAlgebra_surjective hπ hπ1 x hx))

@[simp]
theorem presentationAlgEquiv_mk [IsNoetherianRing O] {π : O} (hπ : π ≠ 0)
    (hπ1 : ‖(π : K)‖ < 1) (x : σ → S) (hx : Algebra.adjoin O (Set.range x) = ⊤)
    (g : intWashnitzerAlgebra σ K) :
    presentationAlgEquiv hπ hπ1 x hx (Ideal.Quotient.mk _ g) =
      evalIntWashnitzerAlgebra hπ hπ1 x g := by
  simp [presentationAlgEquiv]

theorem presentationAlgEquiv_mk_ofMvPolynomial [IsNoetherianRing O] {π : O} (hπ : π ≠ 0)
    (hπ1 : ‖(π : K)‖ < 1) (x : σ → S) (hx : Algebra.adjoin O (Set.range x) = ⊤)
    (p : MvPolynomial σ O) :
    presentationAlgEquiv hπ hπ1 x hx
      (Ideal.Quotient.mk _ (intWashnitzerAlgebra.ofMvPolynomial σ K p)) =
      of π S (MvPolynomial.aeval x p) := by
  simp

@[simp]
theorem presentationAlgEquiv_symm_evalIntWashnitzerAlgebra [IsNoetherianRing O] {π : O}
    (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1) (x : σ → S) (hx : Algebra.adjoin O (Set.range x) = ⊤)
    (g : intWashnitzerAlgebra σ K) :
    (presentationAlgEquiv hπ hπ1 x hx).symm (evalIntWashnitzerAlgebra hπ hπ1 x g) =
      Ideal.Quotient.mk _ g := by
  apply (presentationAlgEquiv hπ hπ1 x hx).injective
  simp

@[simp]
theorem presentationAlgEquiv_symm_of_aeval [IsNoetherianRing O] {π : O} (hπ : π ≠ 0)
    (hπ1 : ‖(π : K)‖ < 1) (x : σ → S) (hx : Algebra.adjoin O (Set.range x) = ⊤)
    (p : MvPolynomial σ O) :
    (presentationAlgEquiv hπ hπ1 x hx).symm (of π S (MvPolynomial.aeval x p)) =
      Ideal.Quotient.mk _ (intWashnitzerAlgebra.ofMvPolynomial σ K p) := by
  apply (presentationAlgEquiv hπ hπ1 x hx).injective
  simp

@[simp]
theorem presentationAlgEquiv_symm_of_apply [IsNoetherianRing O] {π : O} (hπ : π ≠ 0)
    (hπ1 : ‖(π : K)‖ < 1) (x : σ → S) (hx : Algebra.adjoin O (Set.range x) = ⊤) (i : σ) :
    (presentationAlgEquiv hπ hπ1 x hx).symm (of π S (x i)) =
      Ideal.Quotient.mk _ (intWashnitzerAlgebra.ofMvPolynomial σ K (MvPolynomial.X i)) := by
  simpa using presentationAlgEquiv_symm_of_aeval hπ hπ1 x hx (MvPolynomial.X i)

/-- **Presentation of the weak completion of a polynomial quotient.** For any ideal `I` of
`O[X_σ]` over a noetherian valuation unit ball `O = K°`, the weak completion `(O[X_σ] ⧸ I)†` is
canonically `O⟨X_σ⟩† ⧸ (I · O⟨X_σ⟩†)`, compatibly with `O[X_σ] ⧸ I → (O[X_σ] ⧸ I)†` on every
polynomial class. -/
noncomputable def mvPolynomialQuotientEquiv [IsNoetherianRing O] {π : O} (hπ : π ≠ 0)
    (hπ1 : ‖(π : K)‖ < 1) (I : Ideal (MvPolynomial σ O)) :
    (intWashnitzerAlgebra σ K ⧸ I.map (intWashnitzerAlgebra.ofMvPolynomial σ K)) ≃ₐ[O]
      weakCompletion π (MvPolynomial σ O ⧸ I) :=
  let x : σ → MvPolynomial σ O ⧸ I := fun i ↦ Ideal.Quotient.mk I (MvPolynomial.X i)
  have haeval : MvPolynomial.aeval x = Ideal.Quotient.mkₐ O I :=
    (MvPolynomial.mkₐ_eq_aeval I).symm
  have hx : Algebra.adjoin O (Set.range x) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval O x, haeval, AlgHom.range_eq_top]
    exact Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (MvPolynomial.aeval x) = I := by
    rw [haeval, ← RingHom.ker_coe_toRingHom, Ideal.Quotient.mkₐ_ker]
  (Ideal.quotientEquivAlgOfEq O
    (congrArg (Ideal.map (intWashnitzerAlgebra.ofMvPolynomial σ K)) hker.symm)).trans
    (presentationAlgEquiv hπ hπ1 x hx)

@[simp]
theorem mvPolynomialQuotientEquiv_mk [IsNoetherianRing O] {π : O} (hπ : π ≠ 0)
    (hπ1 : ‖(π : K)‖ < 1) (I : Ideal (MvPolynomial σ O)) (g : intWashnitzerAlgebra σ K) :
    mvPolynomialQuotientEquiv hπ hπ1 I (Ideal.Quotient.mk _ g) =
      evalIntWashnitzerAlgebra hπ hπ1 (fun i ↦ Ideal.Quotient.mk I (MvPolynomial.X i)) g := by
  simp [mvPolynomialQuotientEquiv]

theorem mvPolynomialQuotientEquiv_mk_ofMvPolynomial [IsNoetherianRing O] {π : O} (hπ : π ≠ 0)
    (hπ1 : ‖(π : K)‖ < 1) (I : Ideal (MvPolynomial σ O)) (p : MvPolynomial σ O) :
    mvPolynomialQuotientEquiv hπ hπ1 I
      (Ideal.Quotient.mk _ (intWashnitzerAlgebra.ofMvPolynomial σ K p)) =
      of π (MvPolynomial σ O ⧸ I) (Ideal.Quotient.mk I p) := by
  simp [(MvPolynomial.mkₐ_eq_aeval I).symm]

@[simp]
theorem mvPolynomialQuotientEquiv_symm_evalIntWashnitzerAlgebra [IsNoetherianRing O] {π : O}
    (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1) (I : Ideal (MvPolynomial σ O))
    (g : intWashnitzerAlgebra σ K) :
    (mvPolynomialQuotientEquiv hπ hπ1 I).symm
      (evalIntWashnitzerAlgebra hπ hπ1 (fun i ↦ Ideal.Quotient.mk I (MvPolynomial.X i)) g) =
      Ideal.Quotient.mk _ g := by
  apply (mvPolynomialQuotientEquiv hπ hπ1 I).injective
  simp

@[simp]
theorem mvPolynomialQuotientEquiv_symm_of_mk [IsNoetherianRing O] {π : O} (hπ : π ≠ 0)
    (hπ1 : ‖(π : K)‖ < 1) (I : Ideal (MvPolynomial σ O)) (p : MvPolynomial σ O) :
    (mvPolynomialQuotientEquiv hπ hπ1 I).symm
      (of π (MvPolynomial σ O ⧸ I) (Ideal.Quotient.mk I p)) =
      Ideal.Quotient.mk _ (intWashnitzerAlgebra.ofMvPolynomial σ K p) := by
  apply (mvPolynomialQuotientEquiv hπ hπ1 I).injective
  rw [AlgEquiv.apply_symm_apply, mvPolynomialQuotientEquiv_mk_ofMvPolynomial]

/-! Concrete presentations: Laurent polynomials `O[X, Y] ⧸ (X Y - 1)` and non-reduced quotients
`O[X] ⧸ (X²)`. -/

noncomputable example [IsNoetherianRing O] {π : O} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1) :
    (intWashnitzerAlgebra (Fin 2) K ⧸
      (Ideal.span {MvPolynomial.X (R := O) 0 * MvPolynomial.X 1 - 1}).map
        (intWashnitzerAlgebra.ofMvPolynomial (Fin 2) K)) ≃ₐ[O]
      weakCompletion π (MvPolynomial (Fin 2) O ⧸
        Ideal.span {MvPolynomial.X (R := O) 0 * MvPolynomial.X 1 - 1}) :=
  mvPolynomialQuotientEquiv hπ hπ1 _

noncomputable example [IsNoetherianRing O] {π : O} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1) :
    (intWashnitzerAlgebra (Fin 1) K ⧸
      (Ideal.span {(MvPolynomial.X (R := O) 0) ^ 2}).map
        (intWashnitzerAlgebra.ofMvPolynomial (Fin 1) K)) ≃ₐ[O]
      weakCompletion π (MvPolynomial (Fin 1) O ⧸
        Ideal.span {(MvPolynomial.X (R := O) 0) ^ 2}) :=
  mvPolynomialQuotientEquiv hπ hπ1 _

end IntWashnitzerPresentation

end TauCeti.Dagger.weakCompletion
