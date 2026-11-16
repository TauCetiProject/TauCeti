/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Basic
public import TauCeti.RingTheory.Length.Determinant
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.GroupWithZero.Indicator
import Mathlib.Data.ENat.BigOperators
import TauCeti.RingTheory.Ideal.Quotient.Semilocal
import TauCeti.RingTheory.Localization.FiniteDimensional
import TauCeti.RingTheory.OrderOfVanishing

/-!
# The order of a norm

Let `A` be a Noetherian domain of Krull dimension at most one with fraction field `K`, and let `B`
be a domain that is a finite `A`-algebra, with fraction field `L`. For a nonzero `b : B`, this
file computes the order of the norm `N_{L/K}(b)` in two steps (Fulton, *Intersection Theory*,
Appendix A.3):

* `TauCeti.ordFrac_norm_eq_coe_of_length_eq`: the order of `N_{L/K}(b)` is the `A`-length of
  `B ⧸ bB`. The norm need not lie in `A`, since `A` need not be integrally closed, so its order is
  Mathlib's `Ring.ordFrac A` on `K`. This is Fulton's determinant lemma (Appendix A.2)
  (`LinearMap.ordFrac_det_eq_coe_of_length_eq`) for multiplication by `b` on the lattice `B ⊆ L`,
  which spans `L` over `K` because `B` is integral over `A`
  (`TauCeti.span_range_algebraMap_eq_top`).
* `TauCeti.length_quotient_span_singleton_eq_finsum_ord`: for `A` local, that length is
  `Σ_m ord_{B_m}(b) [κ(B_m) : κ(A)]` over the maximal ideals `m` of `B`.
  `TauCeti.length_quotient_span_singleton_eq_finsum` decomposes the `A`-length over the
  localizations `C_q` of `C = B ⧸ bB`, using `MaximalSpectrum.toPiLocalizationEquiv` and
  `IsLocalRing.length_restrictScalars` over `C_q`. The length identities
  `TauCeti.length_localization_quotient_span_singleton` and
  `Ideal.length_residueField_localization_quotient` rewrite these local lengths in terms of
  `B_m`, where `m` is the preimage of `q`.

Together they give `ord_A N_{L/K}(b) = Σ_m [κ(B_m) : κ(A)] ord_{B_m}(b)`, the coefficient identity
behind the pushforward of principal divisors along finite maps (Fulton, Proposition 1.4(b)).
`TauCeti.ordFrac_norm_eq_finprod` states it for every nonzero `r` in `L`, multiplicatively in
`ℤᵐ⁰`, with the orders taken in arbitrary localizations `R m` of `B` at its maximal ideals (such as
the local rings of a scheme at the points of a fibre) and the residue degree read as the `A`-length
of `B ⧸ m`. The orders are transported from `B_m` to `R m` by `TauCeti.Ring.ord_ringEquiv`.
-/

public section

namespace TauCeti

variable {A K B L : Type*} [CommRing A] [Field K] [Algebra A K] [CommRing B] [Algebra A B]
  [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [IsScalarTower A B L]

variable [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsFractionRing A K]
  [Module.Finite A B]

/-- **The order of a norm is a length** (Fulton, *Intersection Theory*, Appendix A.3, first step).
Let `A` be a Noetherian domain of dimension at most one with fraction field `K`, and let `B` be a
domain finite over `A`, with fraction field `L`. For nonzero `b : B` with `B ⧸ bB` of `A`-length
`n`, the norm `N_{L/K}(b)` has order `n`. -/
theorem ordFrac_norm_eq_coe_of_length_eq {b : B} (hb : b ≠ 0) {n : ℕ}
    (hn : Module.length A (B ⧸ Ideal.span {b}) = n) :
    Ring.ordFrac A (Algebra.norm K (algebraMap B L b)) = Multiplicative.ofAdd (n : ℤ) := by
  -- The lattice `B ⊆ L`, the image of the `A`-linear map `f`.
  let f : B →ₗ[A] L := (IsScalarTower.toAlgHom A B L).toLinearMap
  have hf : Function.Injective f := by simpa [f] using IsFractionRing.injective B L
  let M : Submodule A L := LinearMap.range f
  have hspan : Submodule.span K (M : Set L) = ⊤ := by
    rw [← span_range_algebraMap_eq_top K (A := A) (B := B), LinearMap.coe_range,
      AlgHom.coe_toLinearMap, IsScalarTower.coe_toAlgHom']
  have : Module.Finite K L := IsFractionRing.finiteDimensional_of_finite A B K L
  -- Multiplication by `b` on `L` preserves the lattice.
  let φ : L →ₗ[K] L := Algebra.lmul K L (algebraMap B L b)
  have hφM : ∀ x ∈ M, φ x ∈ M := by
    rintro _ ⟨y, rfl⟩
    exact ⟨b * y, by simp [φ, f]⟩
  have hb' : algebraMap B L b ≠ 0 := (FaithfulSMul.algebraMap_eq_zero_iff B L).not.2 hb
  have hdet : LinearMap.det φ ≠ 0 := by
    rw [← Algebra.norm_apply]
    exact (Algebra.norm_ne_zero_iff).2 hb'
  rw [Algebra.norm_apply]
  refine LinearMap.ordFrac_det_eq_coe_of_length_eq φ M ?_ hspan hφM hdet ?_
  · exact Module.Finite.iff_fg.1 (Module.Finite.range f)
  -- Under `B ≃ M`, the ideal `bB` is the image of multiplication by `b`.
  let e : B ≃ₗ[A] M := LinearEquiv.ofInjective f hf
  have he : ((Ideal.span {b}).restrictScalars A).map (e : B →ₗ[A] M) =
      LinearMap.range ((φ.restrictScalars A).restrict hφM) := by
    ext ⟨x, hx⟩
    simp only [Submodule.mem_map, Submodule.restrictScalars_mem, Ideal.mem_span_singleton',
      LinearMap.mem_range, Subtype.ext_iff, LinearEquiv.coe_coe, Subtype.exists]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨f a, ⟨a, rfl⟩, by rw [LinearEquiv.ofInjective_apply]; simp [φ, f, mul_comm]⟩
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨b * a, ⟨a, mul_comm a b⟩, by rw [LinearEquiv.ofInjective_apply]; simp [φ, f]⟩
  rw [← (Submodule.Quotient.equiv _ _ e he).length_eq,
    (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {b})).length_eq, hn]

section Fraction

variable {A K B L : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  [IsLocalRing A] [Field K] [Algebra A K] [IsFractionRing A K] [CommRing B] [IsDomain B]
  [Algebra A B] [Module.Finite A B] [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
  [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
  (R : MaximalSpectrum B → Type*) [∀ m, CommRing (R m)] [∀ m, IsDomain (R m)]
  [∀ m, IsNoetherianRing (R m)] [∀ m, Ring.KrullDimLE 1 (R m)] [∀ m, Algebra B (R m)]
  [∀ m, IsLocalization.AtPrime (R m) m.asIdeal] [∀ m, Algebra (R m) L]
  [∀ m, IsScalarTower B (R m) L] [∀ m, IsFractionRing (R m) L]

/-- **The order of a norm, multiplicative form** (Fulton, *Intersection Theory*, Appendix A.3).
Let `A` be a local Noetherian domain of dimension at most one with fraction field `K`, `B` a domain
finite over `A` with fraction field `L`, and `R m` a localization of `B` at each maximal ideal
`m`. For `b ≠ 0` in `B`, `ord_A N_{L/K}(b) = Σ_m [B ⧸ m : κ(A)] ord_{R m}(b)`, written
multiplicatively in `ℤᵐ⁰`, with the residue degree read as the `A`-length of `B ⧸ m`. -/
theorem ordFrac_norm_algebraMap_eq_finprod {b : B} (hb : b ≠ 0) :
    Ring.ordFrac A (Algebra.norm K (algebraMap B L b)) =
      ∏ᶠ m, Ring.ordFrac (R m) (algebraMap B L b) ^ (Module.length A (B ⧸ m.asIdeal)).toNat := by
  classical
  set S := (finite_setOf_mem_maximalSpectrum A hb).toFinset
  have hfin : Module.length A (B ⧸ Ideal.span {b}) ≠ ⊤ :=
    Module.length_ne_top_iff.2 (isFiniteLength_quotient_span_singleton hb)
  -- The local lengths of `B ⧸ bB` vanish away from the maximal ideals containing `b`.
  have hlen := length_quotient_span_singleton_eq_finsum_ord (A := A) hb
  rw [finsum_eq_sum_of_support_subset _ (s := S) (by
    simpa only [S, Set.Finite.coe_toFinset] using
      ((Function.support_mul_subset_left _ _).trans (support_ord_subset b)))] at hlen
  have hS : ∀ m ∈ S, Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ b) *
      Module.length A (IsLocalRing.ResidueField (Localization.AtPrime m.asIdeal)) ≠ ⊤ :=
    ENat.sum_ne_top.1 (hlen ▸ hfin)
  rw [ordFrac_norm_eq_coe_of_length_eq (K := K) (L := L) hb (ENat.natCast_toNat hfin).symm,
    finprod_eq_prod_of_mulSupport_subset _ (s := S) (by
      simp only [S, Set.Finite.coe_toFinset]; exact mulSupport_ordFrac_pow_subset R b _),
    hlen, ENat.toNat_sum hS]
  simp only [ordFrac_algebraMap_eq_ofAdd_ord R _ hb, ENat.toNat_mul,
    MaximalSpectrum.length_residueField_localization_eq, ← WithZero.coe_pow, ← ofAdd_nsmul,
    Nat.cast_sum, Nat.cast_mul, nsmul_eq_mul, mul_comm, ofAdd_sum]
  exact map_prod (WithZero.coeMonoidHom (α := Multiplicative ℤ)) _ _

/-- **The order of a norm** (Fulton, *Intersection Theory*, Appendix A.3). Let `A` be a local
Noetherian domain of dimension at most one with fraction field `K`, `B` a domain finite over `A`
with fraction field `L`, and `R m` a localization of `B` at each maximal ideal `m`. For `r ≠ 0`
in `L`, `ord_A N_{L/K}(r) = Σ_m [B ⧸ m : κ(A)] ord_{R m}(r)`, written multiplicatively in `ℤᵐ⁰`,
with the residue degree read as the `A`-length of `B ⧸ m`. This is the coefficient identity behind
the pushforward of principal divisors along finite maps (Fulton, Proposition 1.4(b)). -/
theorem ordFrac_norm_eq_finprod {r : L} (hr : r ≠ 0) :
    Ring.ordFrac A (Algebra.norm K r) =
      ∏ᶠ m, Ring.ordFrac (R m) r ^ (Module.length A (B ⧸ m.asIdeal)).toNat := by
  obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := B) r
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hb0 : b ≠ 0 := by rintro rfl; simp at hr
  set d : MaximalSpectrum B → ℕ := fun m ↦ (Module.length A (B ⧸ m.asIdeal)).toNat
  have hfin (x : B) (hx : x ≠ 0) :
      Function.HasFiniteMulSupport fun m ↦ Ring.ordFrac (R m) (algebraMap B L x) ^ d m :=
    (finite_setOf_mem_maximalSpectrum A hx).subset (mulSupport_ordFrac_pow_subset R x d)
  have : Module.Finite K L := IsFractionRing.finiteDimensional_of_finite A B K L
  simp_rw [div_eq_mul_inv, map_mul, Algebra.norm_inv, map_inv₀, mul_pow, inv_pow]
  rw [finprod_mul_distrib (hfin b hb0) ?_, finprod_inv_distrib,
    ordFrac_norm_algebraMap_eq_finprod R hb0, ordFrac_norm_algebraMap_eq_finprod R hc0]
  exact (hfin c hc0).inv

end Fraction

end TauCeti
