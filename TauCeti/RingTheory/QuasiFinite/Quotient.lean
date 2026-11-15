/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.QuasiFinite.Basic

import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.ZariskisMainTheorem
import TauCeti.RingTheory.KrullDimension.FiniteType

/-!
# Quasi-finiteness from fibre quotients and one-dimensional Noether normalization

Let `S` be an `R`-algebra of finite type and `q` a prime ideal of `S` lying over `p = q.under R`.
By Zariski's main theorem (`Algebra.QuasiFiniteAt.of_weaklyQuasiFiniteAt`), `S` is quasi-finite over
`R` at `q` as soon as the quotient `S ⧸ p S` is quasi-finite over `R` at the image of `q`. More
generally, if `J ≤ p S` is an ideal of `S` such that `S ⧸ J` is quasi-finite over `R` at the image
of `q` (or globally), then `S` is quasi-finite over `R` at `q`.

Both hypotheses are needed:
* Without `J ≤ (q.under R).map (algebraMap R S)`, take `R = k`, `S = k[X]`, and `J = q = (X)`:
  `S ⧸ J ≃ k` is finite over `k`, whereas `k[X]` is not quasi-finite over `k` at `(X)`.
* Without `Algebra.FiniteType R S`, let `R` be a discrete valuation ring with uniformizer `π` and
  fraction field `K`, and let `S = R + X K[X] ⊆ K[X]`. Then `π S = π R + X K[X]` is a maximal ideal
  `q` of `S` lying over `(π)` with `S ⧸ π S ≃ R ⧸ (π)` finite over `R`, yet
  `K ⊗[R] S_q ≃ K[X]_{(X)}` has dimension `1`, so `S` is not quasi-finite over `R` at `q`.

Combining this criterion with Noether normalization in Krull dimension at most `1` yields a
quasi-finite polynomial parameter lift modulo a maximal ideal `𝔪` of `R`: when `A` is of finite type
over `R` and `A ⧸ 𝔪 A` has Krull dimension at most `1`, there exists `a : A` such that for every
`x : A` congruent to `a` modulo `𝔪 A`, `A` is quasi-finite over `R[X]` (via `X ↦ x`) at every prime
containing `𝔪 A`.

## Main results

* `Algebra.QuasiFiniteAt.of_quasiFiniteAt_quotient`: for finite-type `S` over `R` and
  `J ≤ (q.under R).map (algebraMap R S)`, `Algebra.QuasiFiniteAt R p` at the image `p` of `q` in
  `S ⧸ J` implies `Algebra.QuasiFiniteAt R q`.
* `Algebra.QuasiFiniteAt.of_quasiFinite_quotient`: global `Algebra.QuasiFinite R (S ⧸ J)` with
  `J ≤ (q.under R).map (algebraMap R S)` implies `Algebra.QuasiFiniteAt R q`.
* `TauCeti.exists_finite_aeval_of_krullDimLE_one`: a finite-type algebra of Krull dimension at most
  `1` over a field `k` is module-finite over `k[X]` along `Polynomial.aeval x₀` for some `x₀`.
* `TauCeti.exists_forall_quasiFiniteAt_of_krullDimLE_one_quotient`: lifting `x₀` modulo `𝔪 A`
  produces `a : A` making every `x ≡ a (mod 𝔪 A)` quasi-finite over `R[X]` at all primes above `𝔪`.

## References

* [Stacks Project, Lemma 55.8.3 (0C2U)](https://stacks.math.columbia.edu/tag/0C2U), choosing a
  parameter `x ∈ A` modulo `𝔪_R A` that is quasi-finite along the special fibre.
-/

public section

open Polynomial

namespace Algebra.QuasiFiniteAt

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]

/-- If `S` is of finite type over `R`, `J` is an ideal of `S` contained in `(q.under R) S`, and
`S ⧸ J` is quasi-finite over `R` at the prime `p` corresponding to `q`, then `S` is quasi-finite
over `R` at `q`. -/
theorem of_quasiFiniteAt_quotient {J : Ideal S} {q : Ideal S} [q.IsPrime]
    (hJ : J ≤ (q.under R).map (algebraMap R S)) (p : Ideal (S ⧸ J)) [p.IsPrime]
    [Algebra.QuasiFiniteAt R p] (hp : p.comap (Ideal.Quotient.mk J) = q) :
    Algebra.QuasiFiniteAt R q := by
  have : Algebra.WeaklyQuasiFiniteAt R q := by
    rw [Algebra.weaklyQuasiFiniteAt_iff]
    let Sq := Localization.AtPrime q
    let I := (q.under R).map (algebraMap R Sq)
    let f : S →ₐ[R] Sq ⧸ I := IsScalarTower.toAlgHom R S (Sq ⧸ I)
    have hfJ : ∀ s ∈ J, f s = 0 := fun s hs ↦ by
      change Ideal.Quotient.mk I (algebraMap S Sq s) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem,
        show I = ((q.under R).map (algebraMap R S)).map (algebraMap S Sq) by
          simp [I, Ideal.map_map, ← IsScalarTower.algebraMap_eq]]
      exact Ideal.mem_map_of_mem _ (hJ hs)
    let φ₀ : S ⧸ J →ₐ[R] Sq ⧸ I := Ideal.Quotient.liftₐ J f hfJ
    let φ : Localization.AtPrime p →ₐ[R] Sq ⧸ I :=
      IsLocalization.liftAlgHom (M := p.primeCompl) (f := φ₀) <| by
        rintro ⟨y, hy⟩
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
        have hsq : s ∉ q := by simpa [← hp] using hy
        exact (IsLocalization.map_units Sq (⟨s, hsq⟩ : q.primeCompl)).map (Ideal.Quotient.mk I)
    refine .of_surjective_algHom φ fun z ↦ ?_
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl z
    have hsp : Ideal.Quotient.mk J s ∈ p.primeCompl := by simpa [← hp] using hs
    refine ⟨IsLocalization.mk' (Localization.AtPrime p) (Ideal.Quotient.mk J x) ⟨_, hsp⟩, ?_⟩
    simp only [φ, IsLocalization.liftAlgHom_apply, IsLocalization.lift_mk'_spec]
    change Ideal.Quotient.mk I _ = Ideal.Quotient.mk I _ * Ideal.Quotient.mk I _
    dsimp only [Sq]
    rw [← map_mul, IsLocalization.mk'_spec' (Localization.AtPrime q) x ⟨s, hs⟩]
  exact .of_weaklyQuasiFiniteAt q

/-- If `S` is of finite type over `R`, `J ≤ (q.under R) S`, and `S ⧸ J` is quasi-finite over `R`,
then `S` is quasi-finite over `R` at `q`. -/
theorem of_quasiFinite_quotient {J : Ideal S} {q : Ideal S} [q.IsPrime]
    (hJ : J ≤ (q.under R).map (algebraMap R S)) [Algebra.QuasiFinite R (S ⧸ J)] :
    Algebra.QuasiFiniteAt R q := by
  let I := (q.under R).map (algebraMap R S)
  have hJI : J ≤ I.comap (AlgHom.id R S) := by simpa using hJ
  have : Algebra.QuasiFinite R (S ⧸ I) :=
    .of_surjective_algHom (Ideal.quotientMapₐ I (AlgHom.id R S) hJI)
      (Ideal.quotientMap_surjective (H := hJI) Function.surjective_id)
  have : Algebra.WeaklyQuasiFiniteAt R q := inferInstance
  exact .of_weaklyQuasiFiniteAt q

end Algebra.QuasiFiniteAt

namespace TauCeti

/-- Surjectivity of `k[X] → MvPolynomial (Fin s) k` when `s ≤ 1`. -/
private lemma exists_surjective_algHom_mvPolynomial_of_le_one (k : Type*) [Field k] {s : ℕ}
    (hs : s ≤ 1) :
    ∃ φ : k[X] →ₐ[k] MvPolynomial (Fin s) k, Function.Surjective φ := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs with rfl | rfl
  · refine ⟨Polynomial.aeval 0, fun p ↦ ?_⟩
    induction p using MvPolynomial.induction_on with
    | C c => exact ⟨Polynomial.C c, by simp⟩
    | add p q hp hq =>
      obtain ⟨P, rfl⟩ := hp
      obtain ⟨Q, rfl⟩ := hq
      exact ⟨P + Q, map_add _ P Q⟩
    | mul_X p i _ => exact Fin.elim0 i
  · refine ⟨Polynomial.aeval (MvPolynomial.X 0), fun p ↦ ?_⟩
    induction p using MvPolynomial.induction_on with
    | C c => exact ⟨Polynomial.C c, by simp⟩
    | add p q hp hq =>
      obtain ⟨P, rfl⟩ := hp
      obtain ⟨Q, rfl⟩ := hq
      exact ⟨P + Q, map_add _ P Q⟩
    | mul_X p i hp =>
      obtain ⟨P, rfl⟩ := hp
      obtain rfl : i = 0 := Subsingleton.elim i 0
      exact ⟨P * Polynomial.X, by simp⟩

/-- **One-dimensional Noether normalization.** Every finite-type algebra `A₀` of Krull dimension at
most `1` over a field `k` is module-finite over `k[X]` via `Polynomial.aeval x₀` for some
`x₀ : A₀`. -/
theorem exists_finite_aeval_of_krullDimLE_one (k A₀ : Type*) [Field k] [CommRing A₀]
    [Algebra k A₀] [Algebra.FiniteType k A₀] [Ring.KrullDimLE 1 A₀] :
    ∃ x₀ : A₀, (Polynomial.aeval (R := k) x₀).toRingHom.Finite := by
  rcases subsingleton_or_nontrivial A₀ with _ | _
  · refine ⟨0, ?_⟩
    rw [RingHom.Finite]
    let : Module k[X] A₀ := RingHom.toModule (Polynomial.aeval (R := k) (0 : A₀)).toRingHom
    infer_instance
  · obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A₀
    have hdim : ringKrullDim A₀ = s := by
      simpa using
        ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial g.toRingHom hinj hfin.to_isIntegral
    have hs : s ≤ 1 := by
      have hle : (s : WithBot ℕ∞) ≤ (1 : ℕ) := hdim ▸ Ring.krullDimLE_iff.mp ‹_›
      exact mod_cast hle
    obtain ⟨φ, hφ⟩ := exists_surjective_algHom_mvPolynomial_of_le_one k hs
    refine ⟨g (φ Polynomial.X), ?_⟩
    have heq : Polynomial.aeval (R := k) (g (φ Polynomial.X)) = g.comp φ := by
      ext
      simp
    rw [heq]
    exact RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ hφ)

/-- Let `A` be a finite-type `R`-algebra and `𝔪` a maximal ideal of `R` such that `A ⧸ 𝔪 A` has
Krull dimension at most `1`. Then there exists `a : A` such that for every `x : A` with
`x - a ∈ 𝔪 A` and every prime `q` of `A` containing `𝔪 A`, `A` is quasi-finite over `R[X]` (via
`X ↦ x`) at `q`. -/
@[stacks 0C2U]
theorem exists_forall_quasiFiniteAt_of_krullDimLE_one_quotient {R A : Type*} [CommRing R]
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A] (𝔪 : Ideal R) [𝔪.IsMaximal]
    [Ring.KrullDimLE 1 (A ⧸ 𝔪.map (algebraMap R A))] :
    ∃ a : A, ∀ x : A, x - a ∈ 𝔪.map (algebraMap R A) →
      ∀ q : Ideal A, [q.IsPrime] → 𝔪.map (algebraMap R A) ≤ q →
        letI : Algebra R[X] A := (Polynomial.aeval (R := R) x).toRingHom.toAlgebra
        Algebra.QuasiFiniteAt R[X] q := by
  let J := 𝔪.map (algebraMap R A)
  let : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  let : Algebra (R ⧸ 𝔪) (A ⧸ J) := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have : IsScalarTower R (R ⧸ 𝔪) (A ⧸ J) := .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.FiniteType (R ⧸ 𝔪) (A ⧸ J) := .of_restrictScalars_finiteType R (R ⧸ 𝔪) (A ⧸ J)
  obtain ⟨x₀, hx₀⟩ := exists_finite_aeval_of_krullDimLE_one (R ⧸ 𝔪) (A ⧸ J)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := J) x₀
  refine ⟨a, fun x hxa q _ hq ↦ ?_⟩
  let : Algebra R[X] A := (Polynomial.aeval (R := R) x).toRingHom.toAlgebra
  have : IsScalarTower R R[X] A := .of_algebraMap_eq fun r ↦ by
    simp [RingHom.algebraMap_toAlgebra]
  have : Algebra.FiniteType R[X] A := .of_restrictScalars_finiteType R R[X] A
  have hx_mk : Ideal.Quotient.mk J x = x₀ := by
    rw [← ha, Ideal.Quotient.eq]
    exact hxa
  have hfin_quot : (algebraMap R[X] (A ⧸ J)).Finite := by
    have hfac : algebraMap R[X] (A ⧸ J) =
        (Polynomial.aeval (R := R ⧸ 𝔪) x₀).toRingHom.comp
          (Polynomial.mapRingHom (Ideal.Quotient.mk 𝔪)) := by
      rw [IsScalarTower.algebraMap_eq R[X] A (A ⧸ J), RingHom.algebraMap_toAlgebra]
      ext r
      · simpa using IsScalarTower.algebraMap_apply R (R ⧸ 𝔪) (A ⧸ J) r
      · simpa using hx_mk
    rw [hfac]
    exact hx₀.comp
      (RingHom.Finite.of_surjective _ (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective))
  have : Module.Finite R[X] (A ⧸ J) := hfin_quot
  have hJ : J ≤ (q.under R[X]).map (algebraMap R[X] A) := by
    dsimp only [J]
    rw [IsScalarTower.algebraMap_eq R R[X] A, ← Ideal.map_map]
    refine Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr ?_)
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq R R[X] A]
    exact Ideal.map_le_iff_le_comap.mp hq
  exact Algebra.QuasiFiniteAt.of_quasiFinite_quotient hJ

end TauCeti
