/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.HahnSeries.PowerSeries
public import TauCeti.RingTheory.HahnSeries.Multiplication
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Coefficientwise maps of Hahn series

A ring homomorphism `f : R →+* S` induces the ring homomorphism `R⟦Γ⟧ →+* S⟦Γ⟧` applying `f` to
every coefficient. Mathlib provides the underlying map `HahnSeries.map` and its compatibility with
addition, multiplication and monomials; this file bundles it as a ring homomorphism, records that
it commutes with exponent embeddings and with the inclusion of power series, and shows that a
coefficient map sending only `0` to `0`, for instance an injective one, preserves supports and
orders.

For Laurent series `R⸨X⸩ = R⟦ℤ⟧` this is the base change of the coefficients, for instance
along a field embedding `K → L`, under which formal substitution and the other coefficient-level
constructions on Laurent series are natural.

## Main definitions

* `HahnSeries.mapRingHom f`: the coefficientwise ring homomorphism `R⟦Γ⟧ →+* S⟦Γ⟧`.
* `HahnSeries.mapRingEquiv e`: the ring equivalence induced by an equivalence of coefficients.
* `HahnSeries.coefficientAlgebra Γ R A`: the algebra of `A⟦Γ⟧` over `R⟦Γ⟧` induced by `Algebra R A`.
* `HahnSeries.mapAlgHom f`: the coefficientwise algebra homomorphism `A⟦Γ⟧ →ₐ[R] B⟦Γ⟧`, for the
  coefficientwise algebra structures.
* `HahnSeries.piAlgEquiv R`: Hahn series over a finite product `∀ i, A i` are families of Hahn
  series over the factors.

## Main results

* `HahnSeries.map_embDomain`: coefficientwise maps commute with exponent embeddings.
* `HahnSeries.map_ofPowerSeries`: coefficientwise maps commute with the inclusion of power
  series, `PowerSeries.map` on the source side.
* `HahnSeries.map_aeval`: coefficientwise algebra maps commute with evaluating multivariate
  polynomials at Hahn series.
* `HahnSeries.mem_map_rangeS`: the range of a coefficientwise map consists of the series
  with all coefficients in the range of the coefficient map.
* `HahnSeries.eqLocusS_mapRingHom`: coefficientwise maps preserve equalizers; for a faithfully
  flat `R → S` this describes `R⟦Γ⟧` inside `S⟦Γ⟧` by the two maps to `(S ⊗[R] S)⟦Γ⟧`.
* `HahnSeries.coeff_mem_of_coeff_pow_mem`: if a prime ideal contains every coefficient of `yⁿ`,
  then it contains every coefficient of `y`, by reduction modulo the prime ideal.
* `HahnSeries.support_map_eq`, `HahnSeries.orderTop_map_eq`, `HahnSeries.order_map_eq`: a
  coefficient map sending only `0` to `0` preserves the support and the order; the
  `_of_injective` versions, also for `mapRingHom` and `mapAlgHom`, are the simp lemmas for
  injective coefficient maps.
* `HahnSeries.exists_mul_eval₂_C_eq_eval₂_C_of_mapRingHom_of_apply_coeff_ne_zero`: for an algebra
  `L` over a commutative semiring `K`, a relation `φ Q(ℓ) = P(ℓ)` with `P, Q` over `L` between
  series `φ, ℓ` with coefficients in `K` descends to such a relation with `P, Q` over `K` and
  `Q ≠ 0`, provided some `K`-linear functional `L → K` does not vanish at a coefficient of `Q`.
* `HahnSeries.exists_mul_eval₂_C_eq_eval₂_C_of_mapRingHom`: the descent for `Q ≠ 0` and a
  `K`-algebra `L` that is projective as a `K`-module, for instance a field extension `L/K`.

## Implementation notes

The descent applies a `K`-linear functional `f : L → K` to every coefficient. Since `φ` and `ℓ`
have coefficients in `K`, this sends `c • φ ℓⁱ` to `f c • φ ℓⁱ`, so it turns the relation over `L`
into the one whose coefficients are the images of those of `P` and `Q` under `f`. Choosing `f`
nonzero at some coefficient of `Q` keeps the new `Q` nonzero; when `L` is projective over `K`,
such an `f` exists for the leading coefficient of a nonzero `Q`.
-/

public section

open scoped PowerSeries

namespace HahnSeries

variable {Γ Γ' R S T : Type*}

section Zero

variable [Zero R] [Zero S] {F : Type*} [FunLike F R S] [ZeroHomClass F R S] [PartialOrder Γ]

/-- Coefficientwise maps commute with exponent embeddings. -/
theorem map_embDomain [PartialOrder Γ'] (f : Γ ↪o Γ') (x : R⟦Γ⟧) (g : F) :
    (embDomain f x).map g = embDomain f (x.map g) := by
  ext b
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hb
    simp
  · simp [embDomain_of_notMem_range hb]

/-- A coefficient map that sends only `0` to `0` preserves the support. Compare
`Finsupp.support_mapRange_eq`. -/
theorem support_map_eq (x : R⟦Γ⟧) {g : F} (hg : ∀ r, g r = 0 → r = 0) :
    (x.map g).support = x.support :=
  Function.support_comp_eq g (fun {_} ↦ ⟨hg _, fun h ↦ h ▸ map_zero g⟩) x.coeff

/-- An injective coefficient map preserves the support. -/
@[simp]
theorem support_map_of_injective (x : R⟦Γ⟧) {g : F} (hg : Function.Injective g) :
    (x.map g).support = x.support :=
  support_map_eq x fun _ ↦ (map_eq_zero_iff g hg).mp

/-- A coefficient map that sends only `0` to `0` preserves `orderTop`. -/
theorem orderTop_map_eq (x : R⟦Γ⟧) {g : F} (hg : ∀ r, g r = 0 → r = 0) :
    (x.map g).orderTop = x.orderTop := by
  -- `orderTop` is defined from the support alone: whether it is empty, and if not, the minimal
  -- element chosen by `Set.IsWF.min`
  simp only [orderTop, ← support_eq_empty_iff, support_map_eq x hg]

/-- An injective coefficient map preserves `orderTop`. -/
@[simp]
theorem orderTop_map_of_injective (x : R⟦Γ⟧) {g : F} (hg : Function.Injective g) :
    (x.map g).orderTop = x.orderTop :=
  orderTop_map_eq x fun _ ↦ (map_eq_zero_iff g hg).mp

/-- A coefficient map that sends only `0` to `0` preserves the order of a nonzero series, and the
junk value `0` of the order of `0`. -/
theorem order_map_eq [Zero Γ] (x : R⟦Γ⟧) {g : F} (hg : ∀ r, g r = 0 → r = 0) :
    (x.map g).order = x.order := by
  -- `order` is defined from the support alone: whether it is empty, and if not, the minimal
  -- element chosen by `Set.IsWF.min`
  simp only [order, ← support_eq_empty_iff, support_map_eq x hg]

/-- An injective coefficient map preserves the order of a nonzero series, and the junk value `0`
of the order of `0`. -/
@[simp]
theorem order_map_of_injective [Zero Γ] (x : R⟦Γ⟧) {g : F} (hg : Function.Injective g) :
    (x.map g).order = x.order :=
  order_map_eq x fun _ ↦ (map_eq_zero_iff g hg).mp

end Zero

section NonAssocSemiring

variable [PartialOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
  [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring T]

/-- The ring homomorphism `R⟦Γ⟧ →+* S⟦Γ⟧` applying a ring homomorphism `f : R →+* S` to every
coefficient. -/
def mapRingHom (f : R →+* S) : R⟦Γ⟧ →+* S⟦Γ⟧ where
  toFun x := x.map f
  map_zero' := HahnSeries.map_zero (f : ZeroHom R S)
  map_one' := by simpa using map_C (Γ := Γ) 1 f
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

/-- A ring equivalence of coefficients induces a ring equivalence of Hahn series. -/
noncomputable def mapRingEquiv (e : R ≃+* S) : R⟦Γ⟧ ≃+* S⟦Γ⟧ :=
  RingEquiv.ofRingHom (mapRingHom (e : R →+* S)) (mapRingHom (e.symm : S →+* R))
    (by rw [← mapRingHom_comp, RingEquiv.comp_symm, mapRingHom_id])
    (by rw [← mapRingHom_comp, RingEquiv.symm_comp, mapRingHom_id])

/-- The ring map underlying the induced equivalence maps coefficients by the original ring map. -/
@[simp]
theorem mapRingEquiv_toRingHom (e : R ≃+* S) :
    (mapRingEquiv (Γ := Γ) e : R⟦Γ⟧ →+* S⟦Γ⟧) = mapRingHom (e : R →+* S) :=
  (rfl)

/-- Applying the induced equivalence applies the underlying coefficientwise ring map. -/
@[simp]
theorem mapRingEquiv_apply (e : R ≃+* S) (x : R⟦Γ⟧) :
    mapRingEquiv e x = mapRingHom (e : R →+* S) x :=
  (rfl)

/-- Inverting the induced equivalence inverts the equivalence of coefficients. -/
@[simp]
theorem mapRingEquiv_symm (e : R ≃+* S) :
    (mapRingEquiv (Γ := Γ) e).symm = mapRingEquiv e.symm :=
  (rfl)

theorem mapRingHom_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (mapRingHom f : R⟦Γ⟧ →+* S⟦Γ⟧) := fun _ _ h ↦
  HahnSeries.ext <| funext fun g ↦ hf congr(($h).coeff g)

@[simp]
theorem support_mapRingHom_of_injective (x : R⟦Γ⟧) {f : R →+* S} (hf : Function.Injective f) :
    (mapRingHom f x).support = x.support :=
  support_map_of_injective x hf

@[simp]
theorem orderTop_mapRingHom_of_injective (x : R⟦Γ⟧) {f : R →+* S} (hf : Function.Injective f) :
    (mapRingHom f x).orderTop = x.orderTop :=
  orderTop_map_of_injective x hf

@[simp]
theorem order_mapRingHom_of_injective (x : R⟦Γ⟧) {f : R →+* S} (hf : Function.Injective f) :
    (mapRingHom f x).order = x.order :=
  order_map_of_injective x hf

@[simp]
theorem mapRingHom_single (f : R →+* S) (a : Γ) (r : R) :
    mapRingHom f (single a r) = single a (f r) :=
  HahnSeries.map_single (f : ZeroHom R S)

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

/-- **Coefficientwise maps preserve equalizers.** If `f : R →+* S` maps onto the equalizer of
`g₁ g₂ : S →+* T`, then `mapRingHom f` maps onto the equalizer of `mapRingHom g₁` and
`mapRingHom g₂`: a series is in the image of `R⟦Γ⟧` exactly when its two coefficientwise images
in `T⟦Γ⟧` agree. -/
theorem eqLocusS_mapRingHom {f : R →+* S} {g₁ g₂ : S →+* T} (h : g₁.eqLocusS g₂ = f.rangeS) :
    (mapRingHom g₁ : S⟦Γ⟧ →+* T⟦Γ⟧).eqLocusS (mapRingHom g₂) =
      (mapRingHom f : R⟦Γ⟧ →+* S⟦Γ⟧).rangeS := by
  ext x
  rw [mem_map_rangeS, RingHom.mem_eqLocusS, HahnSeries.ext_iff, funext_iff]
  refine forall_congr' fun n ↦ ?_
  rw [coeff_mapRingHom, coeff_mapRingHom, ← RingHom.mem_eqLocusS, h]

end NonAssocSemiring

section PrimeIdeal

variable [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]

/-- If a prime ideal `P` contains every coefficient of `y ^ n`, then it contains every coefficient
of `y`: the Hahn series over the domain `R ⧸ P` have no nonzero nilpotent elements. (For `n = 0`
the hypothesis fails, since `P` does not contain the constant coefficient `1` of `y ^ 0`.) -/
theorem coeff_mem_of_coeff_pow_mem {P : Ideal R} [hP : P.IsPrime] {y : R⟦Γ⟧} {n : ℕ}
    (h : ∀ g, (y ^ n).coeff g ∈ P) (g : Γ) : y.coeff g ∈ P := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact absurd (by simpa using h 0) hP.one_notMem
  have hy : mapRingHom (Ideal.Quotient.mk P) y = 0 := by
    refine (pow_eq_zero_iff hn).mp ?_
    rw [← map_pow (mapRingHom (Ideal.Quotient.mk P)) y n]
    ext g
    rw [coeff_mapRingHom, coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact h g
  simpa [Ideal.Quotient.eq_zero_iff_mem] using congr(($hy).coeff g)

end PrimeIdeal

section Algebra

variable [PartialOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [CommSemiring R]
  {A B D : Type*} [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring D] [Algebra R D]

/-- The algebra of Hahn series over Hahn series with the same exponents, induced by applying
the coefficient algebra map to each coefficient. -/
noncomputable abbrev coefficientAlgebra (Γ R A : Type*) [PartialOrder Γ] [AddCommMonoid Γ]
    [IsOrderedCancelAddMonoid Γ] [CommSemiring R] [Semiring A] [Algebra R A] :
    Algebra R⟦Γ⟧ A⟦Γ⟧ :=
  (mapRingHom (Γ := Γ) (algebraMap R A)).toAlgebra' fun x y ↦
    (commute_of_coeff_commute _ y fun i j ↦ by
      rw [coeff_mapRingHom]
      exact Algebra.commute_algebraMap_left _ _).eq

/-- The scalar map for the coefficientwise algebra applies the scalar map of the coefficients. -/
theorem algebraMap_coefficientAlgebra :
    letI := coefficientAlgebra Γ R A
    algebraMap R⟦Γ⟧ A⟦Γ⟧ = mapRingHom (algebraMap R A) :=
  (rfl)

/-- The `R`-algebra homomorphism `A⟦Γ⟧ →ₐ[R] B⟦Γ⟧` applying an `R`-algebra homomorphism
`f : A →ₐ[R] B` to every coefficient, for the coefficientwise algebra structures
`HahnSeries.instAlgebra`. -/
def mapAlgHom (f : A →ₐ[R] B) : A⟦Γ⟧ →ₐ[R] B⟦Γ⟧ where
  __ := mapRingHom (f : A →+* B)
  commutes' r := by
    rw [algebraMap_apply, algebraMap_apply, ← f.commutes r]
    exact map_C _ (f : A →+* B)

theorem mapAlgHom_apply (f : A →ₐ[R] B) (x : A⟦Γ⟧) : mapAlgHom f x = x.map f :=
  (rfl)

@[simp]
theorem coeff_mapAlgHom (f : A →ₐ[R] B) (x : A⟦Γ⟧) (g : Γ) :
    (mapAlgHom f x).coeff g = f (x.coeff g) :=
  (rfl)

/-- The ring homomorphism underlying `mapAlgHom f` is `mapRingHom f`. -/
@[simp]
theorem coe_mapAlgHom (f : A →ₐ[R] B) :
    ((mapAlgHom f : A⟦Γ⟧ →ₐ[R] B⟦Γ⟧) : A⟦Γ⟧ →+* B⟦Γ⟧) = mapRingHom (f : A →+* B) :=
  (rfl)

@[simp]
theorem mapAlgHom_id : mapAlgHom (AlgHom.id R A) = AlgHom.id R A⟦Γ⟧ :=
  AlgHom.ext fun _ ↦ HahnSeries.ext rfl

theorem mapAlgHom_comp (f : A →ₐ[R] B) (g : B →ₐ[R] D) :
    mapAlgHom (g.comp f) = (mapAlgHom g).comp (mapAlgHom f : A⟦Γ⟧ →ₐ[R] B⟦Γ⟧) :=
  AlgHom.ext fun _ ↦ HahnSeries.ext rfl

@[simp]
theorem mapAlgHom_single (f : A →ₐ[R] B) (a : Γ) (r : A) :
    mapAlgHom f (single a r) = single a (f r) :=
  HahnSeries.map_single (f : ZeroHom A B)

theorem mapAlgHom_injective {f : A →ₐ[R] B} (hf : Function.Injective f) :
    Function.Injective (mapAlgHom f : A⟦Γ⟧ →ₐ[R] B⟦Γ⟧) :=
  mapRingHom_injective (f := (f : A →+* B)) hf

@[simp]
theorem support_mapAlgHom_of_injective (x : A⟦Γ⟧) {f : A →ₐ[R] B} (hf : Function.Injective f) :
    (mapAlgHom f x).support = x.support :=
  support_map_of_injective x hf

@[simp]
theorem orderTop_mapAlgHom_of_injective (x : A⟦Γ⟧) {f : A →ₐ[R] B} (hf : Function.Injective f) :
    (mapAlgHom f x).orderTop = x.orderTop :=
  orderTop_map_of_injective x hf

@[simp]
theorem order_mapAlgHom_of_injective (x : A⟦Γ⟧) {f : A →ₐ[R] B} (hf : Function.Injective f) :
    (mapAlgHom f x).order = x.order :=
  order_map_of_injective x hf

end Algebra

section Pi

variable [PartialOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] (R) [CommSemiring R]
  {ι : Type*} [Finite ι] {A : ι → Type*} [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]

/-- **Hahn series over a finite product.** A Hahn series with coefficients in a finite product
`∀ i, A i` is the family of its coefficientwise projections, as an isomorphism of algebras for
the coefficientwise algebra structures `HahnSeries.instAlgebra`. Finiteness of `ι` makes the
union of the supports of a family partially well-ordered. -/
noncomputable def piAlgEquiv : (∀ i, A i)⟦Γ⟧ ≃ₐ[R] ∀ i, (A i)⟦Γ⟧ where
  toFun x i := mapRingHom (Pi.evalRingHom A i) x
  invFun y :=
    { coeff g i := (y i).coeff g
      isPWO_support' := by
        have := Fintype.ofFinite ι
        refine ((Finset.isPWO_bUnion Finset.univ).mpr fun i _ ↦ (y i).isPWO_support).mono ?_
        intro g hg
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hg
        exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_univ i)) hi }
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' x y := funext fun i ↦ map_mul (mapRingHom (Pi.evalRingHom A i)) x y
  map_add' x y := funext fun i ↦ map_add (mapRingHom (Pi.evalRingHom A i)) x y
  commutes' r := funext fun i ↦ by
    rw [algebraMap_apply, Pi.algebraMap_apply, algebraMap_apply]
    exact map_C _ (Pi.evalRingHom A i)

@[simp]
theorem piAlgEquiv_apply (x : (∀ i, A i)⟦Γ⟧) (i : ι) :
    piAlgEquiv R x i = mapRingHom (Pi.evalRingHom A i) x :=
  (rfl)

theorem coeff_piAlgEquiv_apply (x : (∀ i, A i)⟦Γ⟧) (i : ι) (g : Γ) :
    (piAlgEquiv R x i).coeff g = x.coeff g i :=
  (rfl)

@[simp]
theorem coeff_piAlgEquiv_symm_apply (y : ∀ i, (A i)⟦Γ⟧) (g : Γ) (i : ι) :
    ((piAlgEquiv R).symm y).coeff g i = (y i).coeff g :=
  (rfl)

end Pi

section Aeval

variable [PartialOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]

/-- Applying a coefficientwise `k`-algebra map `φ` to the value of a multivariate polynomial at
Hahn series gives the value of the polynomial at the mapped series: the coefficientwise form of
`MvPolynomial.comp_aeval`. -/
theorem map_aeval {k σ : Type*} [CommSemiring k] [CommSemiring R] [Algebra k R] [CommSemiring S]
    [Algebra k S] (φ : R →ₐ[k] S) (s : σ → R⟦Γ⟧) (f : MvPolynomial σ k) :
    (MvPolynomial.aeval s f).map φ = MvPolynomial.aeval (fun i ↦ (s i).map φ) f :=
  DFunLike.congr_fun (MvPolynomial.comp_aeval (R := k) s (mapAlgHom (Γ := Γ) φ)) f

end Aeval

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
theorem map_smul_mapRingHom_algebraMap {K L : Type*} [CommSemiring K] [Semiring L]
    [Algebra K L] (f : L →ₗ[K] K) (c : L) (x : K⟦Γ⟧) :
    (c • mapRingHom (algebraMap K L) x).map f = f c • x := by
  ext g
  simp only [map_coeff, coeff_smul, coeff_mapRingHom, smul_eq_mul]
  exact f.map_mul_algebraMap c (x.coeff g)

variable {K L : Type*} [CommSemiring K] [Semiring L] [Algebra K L]

/-- **Descent of algebraic relations along a linear functional.** Let `L` be an algebra over a
commutative semiring `K`, let `φ` and `ℓ` be series with coefficients in `K`, and let
`φ Q(ℓ) = P(ℓ)` over `L` for polynomials `P, Q` over `L`. If some `K`-linear functional
`f : L → K` does not vanish at some coefficient of `Q`, then `φ Q'(ℓ) = P'(ℓ)` for polynomials
`P', Q'` over `K` with `Q' ≠ 0`, namely the images of `P` and `Q` under `f` coefficientwise.
Polynomials are evaluated through the constant series `HahnSeries.C`. -/
theorem exists_mul_eval₂_C_eq_eval₂_C_of_mapRingHom_of_apply_coeff_ne_zero {φ ℓ : K⟦Γ⟧}
    {P Q : L[X]} (f : L →ₗ[K] K) {i : ℕ} (hf : f (Q.coeff i) ≠ 0)
    (h : mapRingHom (algebraMap K L) φ * Q.eval₂ C (mapRingHom (algebraMap K L) ℓ) =
      P.eval₂ C (mapRingHom (algebraMap K L) ℓ)) :
    ∃ P' Q' : K[X], Q' ≠ 0 ∧ φ * Q'.eval₂ C ℓ = P'.eval₂ C ℓ := by
  let Λ : L⟦Γ⟧ →+ K⟦Γ⟧ :=
    { toFun y := y.map f
      map_zero' := HahnSeries.map_zero (f : ZeroHom L K)
      map_add' _ _ := HahnSeries.map_add (f : L →+ K) }
  have hΛ (z : L⟦Γ⟧) : Λ z = z.map f := rfl
  -- apply `f` to every coefficient of a polynomial over `L`
  let lin (R : L[X]) : K[X] := AddMonoidAlgebra.map (f : L →+ K) R
  have hcoeff (R : L[X]) (n : ℕ) : (lin R).coeff n = f (R.coeff n) := rfl
  have hsupp (R : L[X]) : (lin R).support ⊆ R.support := fun n hn ↦
    mem_support_iff.2 fun h ↦ mem_support_iff.1 hn (by rw [hcoeff, h, map_zero])
  have hlin (R : L[X]) (y : K⟦Γ⟧) :
      Λ (mapRingHom (algebraMap K L) y * R.eval₂ C (mapRingHom (algebraMap K L) ℓ)) =
        y * (lin R).eval₂ C ℓ := by
    rw [eval₂_eq_sum, eval₂_eq_sum, sum_def,
      sum_eq_of_subset _ (fun _ ↦ by rw [map_zero, zero_mul]) (hsupp R),
      Finset.mul_sum, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    -- a series with coefficients in `K` commutes with the constants, as `K` is central in `L`
    have hy : Commute (mapRingHom (algebraMap K L) y) (C (R.coeff n)) :=
      commute_C_iff.2 fun g ↦ Algebra.commute_algebraMap_left (y.coeff g) (R.coeff n)
    rw [hy.left_comm, hcoeff]
    simpa only [hΛ, map_mul, map_pow, C_mul_eq_smul, mul_smul_comm] using
      map_smul_mapRingHom_algebraMap f (R.coeff n) (y * ℓ ^ n)
  refine ⟨lin P, lin Q, fun h0 ↦ hf ?_, ?_⟩
  · rw [← hcoeff, h0, Polynomial.coeff_zero]
  · rw [← one_mul ((lin P).eval₂ C ℓ), ← hlin, ← hlin, map_one, one_mul, h]

/-- **Descent of algebraic relations to the coefficient ring.** Let `K` be a commutative
semiring and let `L` be a `K`-algebra that is projective as a `K`-module, for instance a field
extension of `K`, and let `φ` and `ℓ` be series with coefficients in `K`. If `φ Q(ℓ) = P(ℓ)`
over `L` for polynomials `P, Q` over `L` with `Q ≠ 0`, then `φ Q'(ℓ) = P'(ℓ)` for polynomials
`P', Q'` over `K` with `Q' ≠ 0`. Polynomials are evaluated through the constant series
`HahnSeries.C`, which does not depend on a choice of algebra structure on the series. -/
theorem exists_mul_eval₂_C_eq_eval₂_C_of_mapRingHom [Module.Projective K L] {φ ℓ : K⟦Γ⟧}
    {P Q : L[X]} (hQ : Q ≠ 0)
    (h : mapRingHom (algebraMap K L) φ * Q.eval₂ C (mapRingHom (algebraMap K L) ℓ) =
      P.eval₂ C (mapRingHom (algebraMap K L) ℓ)) :
    ∃ P' Q' : K[X], Q' ≠ 0 ∧ φ * Q'.eval₂ C ℓ = P'.eval₂ C ℓ :=
  have ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero K (Polynomial.leadingCoeff_ne_zero.mpr hQ)
  exists_mul_eval₂_C_eq_eval₂_C_of_mapRingHom_of_apply_coeff_ne_zero f hf h

end Descent

end HahnSeries
