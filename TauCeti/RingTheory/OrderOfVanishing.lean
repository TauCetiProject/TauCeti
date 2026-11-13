/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.GroupWithZero.Indicator
import Mathlib.RingTheory.RingHom.Surjective
import TauCeti.RingTheory.Ideal.Quotient.Semilocal
import TauCeti.RingTheory.Length

/-!
# Invariance and vanishing of the order of vanishing

For a Noetherian domain `R` of Krull dimension at most one with fraction field `K`, Mathlib's
`Ring.ordFrac R : K →*₀ ℤᵐ⁰` extends the order of vanishing `Ring.ord R x = length (R ⧸ (x))` to the
fraction field. This file records that the order of vanishing is transported by ring isomorphisms,
that it turns finite products of non-zero-divisors into sums, and that the order of a nonzero
element of `R` is trivial exactly when that element is a unit: `R ⧸ (x)` is the zero ring exactly
when `(x)` is the unit ideal. Mathlib has the forward direction, `Ring.ordFrac_of_isUnit`; the
converse is what reads "`f` has order zero at a codimension-one point" as "`f` is a unit at that
point".

## Main results

* `TauCeti.Ring.ord_ringEquiv`, `TauCeti.Ring.ordMonoidWithZeroHom_ringEquiv` and
  `TauCeti.Ring.ordFrac_map_of_ringEquiv`: the order of vanishing is invariant under ring
  isomorphisms, also as a homomorphism to `ℤᵐ⁰` and on fraction fields;
* `TauCeti.Ring.ord_eq_zero_iff`: `Ring.ord R x = 0` exactly when `x` is a unit;
* `TauCeti.Ring.ord_prod`: the order of a finite product of non-zero-divisors is the sum of the
  orders;
* `TauCeti.Ring.isUnit_iff_ordFrac_one`: `x` is a unit exactly when `Ring.ordFrac R x = 1`; this
  extends Mathlib's `Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing` to Noetherian domains
  of dimension at most one.
-/

public section

namespace TauCeti

namespace Ring

open scoped nonZeroDivisors

section RingEquiv

section Ring

variable {R R' : Type*} [Ring R] [Ring R']

/-- The order of vanishing is invariant under ring isomorphisms: `σ : R ≃+* R'` induces a
`σ`-semilinear isomorphism `R ⧸ (x) ≃ R' ⧸ (σ x)`, so both quotients have the same length. -/
@[simp]
theorem ord_ringEquiv (σ : R ≃+* R') (x : R) : Ring.ord R' (σ x) = Ring.ord R x := by
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.symm (σ : R →+* R') σ.symm
  exact ((Submodule.Quotient.equiv (Ideal.span {x}) (Ideal.span {σ x}) σ.toSemilinearEquiv
    (by simp [← Ideal.submodule_span_eq, Submodule.map_span])).toLinearMap.length_eq_of_bijective
    (LinearEquiv.bijective _)).symm

end Ring

variable {R R' : Type*} [CommRing R] [CommRing R']

/-- The order of vanishing, as a homomorphism to `ℤᵐ⁰`, is invariant under ring isomorphisms. -/
@[simp]
theorem ordMonoidWithZeroHom_ringEquiv [Nontrivial R] [Nontrivial R'] (σ : R ≃+* R') (x : R) :
    Ring.ordMonoidWithZeroHom R' (σ x) = Ring.ordMonoidWithZeroHom R x := by
  have hmem : σ x ∈ R'⁰ ↔ x ∈ R⁰ := by
    rw [← MulEquivClass.map_nonZeroDivisors σ, Submonoid.mem_map_iff_mem σ.injective]
  by_cases hx : x ∈ R⁰ <;> simp [Ring.ordMonoidWithZeroHom_eq_ord, hx, hmem]

variable [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  [IsDomain R'] [IsNoetherianRing R'] [Ring.KrullDimLE 1 R']
  {K K' : Type*} [Field K] [Field K'] [Algebra R K] [IsFractionRing R K] [Algebra R' K']
  [IsFractionRing R' K']

/-- The order of vanishing on fraction fields is invariant under ring isomorphisms: if
`σ : R ≃+* R'` and `τ : K →+* K'` are compatible with the inclusions into the fraction fields, then
`ordFrac R' (τ k) = ordFrac R k`. -/
theorem ordFrac_map_of_ringEquiv (σ : R ≃+* R') (τ : K →+* K')
    (h : ∀ a, τ (algebraMap R K a) = algebraMap R' K' (σ a)) (k : K) :
    Ring.ordFrac R' (τ k) = Ring.ordFrac R k := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) k
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  simp [h, Ring.ordFrac_eq_ord, ha, nonZeroDivisors.ne_zero hb]

end RingEquiv

variable {R : Type*} [CommRing R]

/-- The order of vanishing of a ring element is zero exactly when the element is a unit: the
quotient `R ⧸ (x)` is trivial exactly when `(x)` is the unit ideal. -/
theorem ord_eq_zero_iff (x : R) : Ring.ord R x = 0 ↔ IsUnit x := by
  rw [Ring.ord, Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff,
    Ideal.span_singleton_eq_top]

/-- The order of vanishing of a finite product of non-zero-divisors is the sum of their orders. -/
theorem ord_prod {ι : Type*} {s : Finset ι} {d : ι → R} (hd : ∀ i ∈ s, d i ∈ R⁰) :
    Ring.ord R (∏ i ∈ s, d i) = ∑ i ∈ s, Ring.ord R (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      Ring.ord_mul' R (hd a (Finset.mem_insert_self a s)),
      ih fun i hi ↦ hd i (Finset.mem_insert_of_mem hi)]

variable [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- In a Noetherian domain of dimension at most one, an element is a unit exactly when its order
of vanishing in the fraction field is trivial. This extends Mathlib's
`Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing` from discrete valuation rings to
Noetherian domains of dimension at most one, such as the local rings at the codimension-one points
of a locally Noetherian integral scheme. -/
theorem isUnit_iff_ordFrac_one {x : R} : IsUnit x ↔ Ring.ordFrac R (algebraMap R K x) = 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hnz : x ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hx
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hnz)
  rw [Ring.ordFrac_eq_ord R hx, Ring.ordMonoidWithZeroHom_eq_coe R hnz hn.symm, ← ord_eq_zero_iff,
    ← hn]
  simp [← WithZero.coe_one]

end Ring

/-- The localization `(R ⧸ bR)_q` has length `ord_{R_m} b` over itself, where `m` is the prime
of `R` under `q`. -/
theorem length_localization_quotient_span_singleton {R : Type*} [CommRing R] (b : R)
    (q : Ideal (R ⧸ Ideal.span {b})) [q.IsPrime] :
    Module.length (Localization.AtPrime q) (Localization.AtPrime q) =
      Ring.ord (Localization.AtPrime (q.comap (Ideal.Quotient.mk (Ideal.span {b}))))
        (algebraMap R _ b) := by
  -- The localization `ψ : R_m → (R ⧸ bR)_q` of `R → R ⧸ bR` is surjective with kernel `b R_m`.
  let ψ := Localization.localRingHom _ q (Ideal.Quotient.mk (Ideal.span {b})) rfl
  have hψ : Function.Surjective ψ :=
    RingHom.surjective_localRingHom_of_surjective _ Ideal.Quotient.mk_surjective q
  have hker : RingHom.ker ψ = Ideal.span {algebraMap R _ b} := by
    have hmap : ψ = IsLocalization.map
        (M := (q.comap (Ideal.Quotient.mk (Ideal.span {b}))).primeCompl) (T := q.primeCompl)
        (Localization.AtPrime q) (Ideal.Quotient.mk (Ideal.span {b}))
        (Localization.le_comap_primeCompl_iff.mpr le_rfl) := by
      apply Localization.localRingHom_unique
      exact IsLocalization.map_eq _
    rw [hmap]
    refine (IsLocalization.ker_map (Localization.AtPrime q) (Ideal.Quotient.mk (Ideal.span {b}))
      (Ideal.map_primeCompl_comap_of_surjective _ Ideal.Quotient.mk_surjective q)).trans ?_
    rw [Ideal.mk_ker, Ideal.map_span, Set.image_singleton]
  let _ : Algebra (Localization.AtPrime (q.comap (Ideal.Quotient.mk (Ideal.span {b}))))
      (Localization.AtPrime q) := ψ.toAlgebra
  let e : (Localization.AtPrime (q.comap (Ideal.Quotient.mk (Ideal.span {b}))) ⧸ RingHom.ker ψ)
      ≃ₐ[Localization.AtPrime (q.comap (Ideal.Quotient.mk (Ideal.span {b})))]
      Localization.AtPrime q :=
    AlgEquiv.ofRingEquiv (f := RingHom.quotientKerEquivOfSurjective hψ) (by
      simp [RingHom.algebraMap_toAlgebra])
  rw [← Module.length_eq_of_surjective
      (S := Localization.AtPrime (q.comap (Ideal.Quotient.mk (Ideal.span {b})))) hψ,
    ← e.toLinearEquiv.length_eq,
    (Ideal.quotientEquivAlgOfEq _ hker).toLinearEquiv.length_eq, Ring.ord]

/-- The local order of `b` vanishes outside the maximal ideals containing `b`. -/
theorem support_ord_subset {B : Type*} [CommRing B] (b : B) :
    Function.support (fun m : MaximalSpectrum B ↦
      Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ b)) ⊆
      {m | b ∈ m.asIdeal} := by
  intro m hm
  by_contra hbm
  exact hm (Ring.ord_of_isUnit ((IsLocalization.AtPrime.isUnit_to_map_iff _ _ b).2 hbm))

section LocalLengthDecomposition

variable {A B : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]

/-- **The length of `B ⧸ bB` as a sum of local orders** (Fulton, *Intersection Theory*,
Appendix A.3). Let `A` be a local Noetherian domain of dimension at most one and `B` a domain
finite over `A`. For `b ≠ 0`,
`length_A (B ⧸ bB) = Σ_m ord_{B_m}(b) [κ(B_m) : κ(A)]`, the sum over the maximal ideals `m` of `B`
(only those containing `b` contribute), with the residue degree `[κ(B_m) : κ(A)]` read as the
`A`-length of `κ(B_m)`. -/
theorem length_quotient_span_singleton_eq_finsum_ord [IsLocalRing A] {b : B} (hb : b ≠ 0) :
    Module.length A (B ⧸ Ideal.span {b}) =
      ∑ᶠ m : MaximalSpectrum B, Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ b) *
        Module.length A (IsLocalRing.ResidueField (Localization.AtPrime m.asIdeal)) := by
  set G : MaximalSpectrum B → ℕ∞ := fun m ↦
    Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ b) *
      Module.length A (IsLocalRing.ResidueField (Localization.AtPrime m.asIdeal))
  -- The maximal ideals of `B ⧸ bB` are those of `B` containing `b`.
  let c : MaximalSpectrum (B ⧸ Ideal.span {b}) → MaximalSpectrum B := fun q ↦
    ⟨q.asIdeal.comap (Ideal.Quotient.mk _),
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective⟩
  have hc : Function.Injective c := fun q q' h ↦ MaximalSpectrum.ext
    (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
      (congrArg MaximalSpectrum.asIdeal h))
  have hsupp : Function.support G ⊆ Set.range c := by
    intro m hm
    have hbm : b ∈ m.asIdeal := support_ord_subset b (Function.support_mul_subset_left _ _ hm)
    obtain ⟨q, hq⟩ := exists_maximalSpectrum_comap_mk_eq hbm
    exact ⟨q, MaximalSpectrum.ext hq⟩
  have hG : ∑ᶠ m, G m = ∑ᶠ q, G (c q) := by
    rw [← finsum_mem_range hc, finsum_mem_def, Set.indicator_eq_self.2 hsupp]
  rw [length_quotient_span_singleton_eq_finsum hb, hG]
  refine finsum_congr fun q ↦ ?_
  rw [length_localization_quotient_span_singleton, Ideal.length_residueField_localization_quotient]

end LocalLengthDecomposition

section Localization

variable {B L : Type*} [CommRing B] [Field L] [Algebra B L] [IsFractionRing B L]
  (R : MaximalSpectrum B → Type*) [∀ m, CommRing (R m)] [∀ m, IsDomain (R m)]
  [∀ m, IsNoetherianRing (R m)] [∀ m, Ring.KrullDimLE 1 (R m)] [∀ m, Algebra B (R m)]
  [∀ m, IsLocalization.AtPrime (R m) m.asIdeal] [∀ m, Algebra (R m) L]
  [∀ m, IsScalarTower B (R m) L] [∀ m, IsFractionRing (R m) L]

/-- For nonzero `b : B`, its order in a localization `R m` of `B` at a maximal ideal `m`,
computed on the fraction field `L`, is its order in `B_m`. Here `R m` is a Noetherian domain of
Krull dimension at most one. -/
theorem ordFrac_algebraMap_eq_ofAdd_ord (m : MaximalSpectrum B) {b : B} (hb : b ≠ 0) :
    Ring.ordFrac (R m) (algebraMap B L b) = Multiplicative.ofAdd
      ((Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ b)).toNat : ℤ) := by
  let e : Localization.AtPrime m.asIdeal ≃ₐ[B] R m :=
    IsLocalization.algEquiv m.asIdeal.primeCompl _ _
  have hy : algebraMap B (R m) b ≠ 0 := fun h ↦ hb <| IsFractionRing.injective B L <| by
    rw [IsScalarTower.algebraMap_apply B (R m) L, h, map_zero, map_zero]
  have hy' := mem_nonZeroDivisors_of_ne_zero hy
  have he : Ring.ord (R m) (algebraMap B (R m) b) =
      Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ b) := by
    rw [← e.commutes]
    exact Ring.ord_ringEquiv e.toRingEquiv _
  have hn : Ring.ord (R m) (algebraMap B (R m) b) =
      ((Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ b)).toNat : ℕ∞) := by
    rw [← he, ENat.natCast_toNat (Ring.ord_ne_top hy')]
  rw [IsScalarTower.algebraMap_apply B (R m) L, Ring.ordFrac_eq_ord (R m) hy,
    Ring.ordMonoidWithZeroHom_eq_coe (R m) hy' hn]

omit [IsFractionRing B L] in
/-- The order of `b ∈ B` is trivial at every maximal ideal of `B` not containing `b`. -/
theorem mulSupport_ordFrac_pow_subset (b : B) (d : MaximalSpectrum B → ℕ) :
    Function.mulSupport (fun m ↦ Ring.ordFrac (R m) (algebraMap B L b) ^ d m) ⊆
      {m | b ∈ m.asIdeal} := by
  intro m hm
  by_contra hbm
  refine hm ?_
  dsimp only
  rw [IsScalarTower.algebraMap_apply B (R m) L, Ring.ordFrac_of_isUnit (K := L)
    ((IsLocalization.AtPrime.isUnit_to_map_iff (R m) m.asIdeal b).2 hbm), one_pow]

end Localization

end TauCeti
