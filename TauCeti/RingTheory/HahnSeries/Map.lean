/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Coefficientwise maps of Hahn series

A ring homomorphism `f : R →+* S` induces the ring homomorphism `R⟦Γ⟧ →+* S⟦Γ⟧` applying `f` to
every coefficient. Mathlib provides the underlying map `HahnSeries.map` and its compatibility with
addition, multiplication and monomials; this file bundles it as a ring homomorphism, records that
it commutes with exponent embeddings and with the inclusion of power series, and shows that an
injective coefficient map preserves supports and orders.

For Laurent series `R⸨X⸩ = R⟦ℤ⟧` this is the base change of the coefficients, for instance
along a field embedding `K → L`, under which formal substitution and the other coefficient-level
constructions on Laurent series are natural.

## Main definitions

* `HahnSeries.mapRingHom f`: the coefficientwise ring homomorphism `R⟦Γ⟧ →+* S⟦Γ⟧`.

## Main results

* `HahnSeries.map_embDomain`: coefficientwise maps commute with exponent embeddings.
* `HahnSeries.map_ofPowerSeries`: coefficientwise maps commute with the inclusion of power
  series, `PowerSeries.map` on the source side.
* `HahnSeries.mem_map_rangeS`: the range of a coefficientwise map consists of the series
  with all coefficients in the range of the coefficient map.
* `HahnSeries.support_map_of_injective`, `HahnSeries.orderTop_map_of_injective`,
  `HahnSeries.order_map_of_injective`: an injective coefficient map preserves the support and
  the order.
* `HahnSeries.exists_mul_eval₂_C_eq_eval₂_C_of_mapRingHom`: for an algebra `L` over a field
  `K`, a relation `φ Q(ℓ) = P(ℓ)` with `P, Q` over `L`, `Q ≠ 0`, between series `φ, ℓ` with
  coefficients in `K` descends to such a relation with `P, Q` over `K`.

## Implementation notes

The descent applies a `K`-linear functional `f : L → K` to every coefficient. Since `φ` and `ℓ`
have coefficients in `K`, this sends `c • φ ℓⁱ` to `f c • φ ℓⁱ`, so it turns the relation over `L`
into the one whose coefficients are the images of those of `P` and `Q` under `f`. Choosing `f`
with `f` of the leading coefficient of `Q` equal to `1` keeps the new `Q` nonzero.
-/

public section

open scoped PowerSeries

namespace HahnSeries

variable {Γ Γ' R S T : Type*}

section Zero

variable [Zero R] [Zero S] {F : Type*} [FunLike F R S] [ZeroHomClass F R S]

section PartialOrder

variable [PartialOrder Γ]

/-- Coefficientwise maps commute with exponent embeddings. -/
theorem map_embDomain [PartialOrder Γ'] (f : Γ ↪o Γ') (x : R⟦Γ⟧) (g : F) :
    (embDomain f x).map g = embDomain f (x.map g) := by
  ext b
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hb
    simp
  · simp [embDomain_of_notMem_range hb]

/-- An injective coefficient map preserves the support. -/
@[simp]
theorem support_map_of_injective (x : R⟦Γ⟧) {g : F} (hg : Function.Injective g) :
    (x.map g).support = x.support := by
  ext a
  simp only [mem_support, map_coeff, ne_eq]
  rw [← map_zero g, hg.eq_iff]

end PartialOrder

/-- An injective coefficient map preserves `orderTop`. -/
@[simp]
theorem orderTop_map_of_injective [LinearOrder Γ] (x : R⟦Γ⟧) {g : F} (hg : Function.Injective g) :
    (x.map g).orderTop = x.orderTop := by
  obtain rfl | hx := eq_or_ne x 0
  · rw [orderTop_zero, orderTop_eq_top, ← support_eq_empty_iff, support_map_of_injective _ hg,
      support_zero]
  rw [orderTop_of_ne_zero hx]
  refine orderTop_eq_of_le ?_ fun b hb ↦ ?_
  · rw [support_map_of_injective x hg]
    exact x.isWF_support.min_mem _
  · rw [support_map_of_injective x hg] at hb
    exact x.isWF_support.min_le _ hb

/-- An injective coefficient map preserves the order of a nonzero series, and the junk value `0`
of the order of `0`. -/
@[simp]
theorem order_map_of_injective [LinearOrder Γ] [Zero Γ] (x : R⟦Γ⟧) {g : F}
    (hg : Function.Injective g) : (x.map g).order = x.order := by
  obtain rfl | hx := eq_or_ne x 0
  · rw [support_eq_empty_iff.mp ((support_map_of_injective _ hg).trans support_zero), order_zero,
      order_zero]
  have hx' : x.map g ≠ 0 := by
    rw [← support_nonempty_iff, support_map_of_injective x hg]
    exact support_nonempty_iff.mpr hx
  exact WithTop.coe_injective <| by
    rw [order_eq_orderTop_of_ne_zero hx', order_eq_orderTop_of_ne_zero hx,
      orderTop_map_of_injective x hg]

end Zero

section Semiring

variable [PartialOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
  [Semiring R] [Semiring S] [Semiring T]

/-- The ring homomorphism `R⟦Γ⟧ →+* S⟦Γ⟧` applying a ring homomorphism `f : R →+* S` to every
coefficient. -/
def mapRingHom (f : R →+* S) : R⟦Γ⟧ →+* S⟦Γ⟧ where
  toFun x := x.map f
  map_zero' := HahnSeries.map_zero (f : ZeroHom R S)
  map_one' := HahnSeries.map_one (f : R →*₀ S)
  map_add' _ _ := HahnSeries.map_add (f : R →+ S)
  map_mul' _ _ := HahnSeries.map_mul (f : R →ₙ+* S)

theorem mapRingHom_apply (f : R →+* S) (x : R⟦Γ⟧) : mapRingHom f x = x.map f :=
  (rfl)

@[simp]
theorem coeff_mapRingHom (f : R →+* S) (x : R⟦Γ⟧) (g : Γ) :
    (mapRingHom f x).coeff g = f (x.coeff g) :=
  (rfl)

@[simp]
theorem mapRingHom_id : mapRingHom (RingHom.id R) = RingHom.id R⟦Γ⟧ :=
  RingHom.ext fun _ ↦ HahnSeries.ext rfl

theorem mapRingHom_comp (f : R →+* S) (g : S →+* T) :
    mapRingHom (g.comp f) = (mapRingHom g).comp (mapRingHom f : R⟦Γ⟧ →+* S⟦Γ⟧) :=
  RingHom.ext fun _ ↦ HahnSeries.ext rfl

theorem mapRingHom_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (mapRingHom f : R⟦Γ⟧ →+* S⟦Γ⟧) := fun _ _ h ↦
  HahnSeries.ext <| funext fun g ↦ hf congr(($h).coeff g)

/-- A Hahn series is in the range of a coefficientwise map exactly when all its coefficients are
in the range of the coefficient map. Compare `Polynomial.mem_map_rangeS`. -/
theorem mem_map_rangeS {f : R →+* S} {x : S⟦Γ⟧} :
    x ∈ (mapRingHom f : R⟦Γ⟧ →+* S⟦Γ⟧).rangeS ↔ ∀ g, x.coeff g ∈ f.rangeS := by
  classical
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨y, rfl⟩ g
    exact ⟨y.coeff g, rfl⟩
  choose c hc using h
  refine ⟨⟨fun g ↦ if x.coeff g = 0 then 0 else c g, x.isPWO_support.mono fun g hg hx ↦ ?_⟩, ?_⟩
  · exact hg (ite_eq_left hx)
  · ext g
    by_cases hx : x.coeff g = 0 <;> simp [hx, hc]

end Semiring

section PowerSeries

variable [Semiring Γ] [PartialOrder Γ] [IsStrictOrderedRing Γ] [Semiring R] [Semiring S]

/-- Coefficientwise maps commute with the inclusion of power series into Hahn series. -/
@[simp]
theorem map_ofPowerSeries (f : R →+* S) (p : R⟦X⟧) :
    (ofPowerSeries Γ R p).map f = ofPowerSeries Γ S (PowerSeries.map f p) := by
  rw [ofPowerSeries_apply, ofPowerSeries_apply, map_embDomain]
  refine congrArg _ (HahnSeries.ext <| funext fun n ↦ ?_)
  simp

end PowerSeries

section Descent

open Polynomial

variable [PartialOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]

/-- Applying a `K`-linear functional `f : L → K` to every coefficient of `c • x`, for a series `x`
with coefficients in `K`, gives `f c • x`. -/
theorem map_smul_mapRingHom_algebraMap {K L : Type*} [CommSemiring K] [CommSemiring L]
    [Algebra K L] (f : L →ₗ[K] K) (c : L) (x : K⟦Γ⟧) :
    (c • mapRingHom (algebraMap K L) x).map f = f c • x := by
  ext g
  simp only [map_coeff, coeff_smul, coeff_mapRingHom]
  simpa [Algebra.smul_def, mul_comm] using f.map_smul (x.coeff g) c

variable {K L : Type*} [Field K] [CommRing L] [Algebra K L]

/-- **Descent of algebraic relations to the coefficient field.** Let `L` be an algebra over a field
`K`, for instance a field extension, and let `φ` and `ℓ` be series with coefficients in `K`. If
`φ Q(ℓ) = P(ℓ)` over `L` for polynomials `P, Q` over `L` with `Q ≠ 0`, then `φ Q'(ℓ) = P'(ℓ)` for
polynomials `P', Q'` over `K` with `Q' ≠ 0`. Polynomials are evaluated through the constant
series `HahnSeries.C`, which does not depend on a choice of algebra structure on the series. -/
theorem exists_mul_eval₂_C_eq_eval₂_C_of_mapRingHom {φ ℓ : K⟦Γ⟧} {P Q : L[X]} (hQ : Q ≠ 0)
    (h : mapRingHom (algebraMap K L) φ * Q.eval₂ C (mapRingHom (algebraMap K L) ℓ) =
      P.eval₂ C (mapRingHom (algebraMap K L) ℓ)) :
    ∃ P' Q' : K[X], Q' ≠ 0 ∧ φ * Q'.eval₂ C ℓ = P'.eval₂ C ℓ := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K (Polynomial.leadingCoeff_ne_zero.mpr hQ)
  let Λ : L⟦Γ⟧ →+ K⟦Γ⟧ :=
    { toFun y := y.map f
      map_zero' := by ext; simp
      map_add' _ _ := by ext; simp }
  -- apply `f` to every coefficient of a polynomial over `L`
  let lin (R : L[X]) : K[X] := ∑ i ∈ Finset.range (R.natDegree + 1), monomial i (f (R.coeff i))
  have hlin (R : L[X]) (y : K⟦Γ⟧) :
      Λ (mapRingHom (algebraMap K L) y * R.eval₂ C (mapRingHom (algebraMap K L) ℓ)) =
        y * (lin R).eval₂ C ℓ := by
    rw [eval₂_eq_sum_range, Finset.mul_sum, map_sum]
    simp only [lin, eval₂_finsetSum, eval₂_monomial, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← map_pow, mul_left_comm, ← map_mul, C_mul_eq_smul, C_mul_eq_smul, mul_smul_comm]
    exact map_smul_mapRingHom_algebraMap f _ _
  refine ⟨lin P, lin Q, fun h0 ↦ ?_, ?_⟩
  · have := Polynomial.ext_iff.mp h0 Q.natDegree
    simp [lin, finsetSum_coeff, coeff_monomial, hf] at this
  · rw [← one_mul ((lin P).eval₂ C ℓ), ← hlin, ← hlin, map_one, one_mul, h]

end Descent

end HahnSeries
