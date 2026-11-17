/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.PowerSeries.Expand
import TauCeti.GroupTheory.Coset.Fiber
import TauCeti.RingTheory.PowerSeries.Geometric
import TauCeti.RingTheory.PowerSeries.ProdOneSubXPow

/-!
# Products of linear factors over characters of a finite commutative group

Let `G` be a finite commutative group and `R` an integral domain with enough roots of unity for
the exponent of `G`. For any element `g : G` of order `f = orderOf g`, restricting characters
`χ : G →* Rˣ` to the cyclic subgroup `H = ⟨g⟩` is a surjective group homomorphism with
kernel of order `|G| / f`. On the cyclic subgroup `H`, the values `χ g` are precisely the `f`-th
roots of unity in `R`, each taken once, so `∏ ψ : H →* Rˣ, (1 - C (ψ g) * X) = 1 - X ^ f`
(`CommGroup.prod_one_sub_C_monoidHom_mul_X_of_zpowers_eq_top`, using Mathlib's
`X_pow_sub_C_eq_prod`). Lifting back across the restriction fiber gives
`(1 - X ^ f) ^ (|G| / f)`.

Evaluating via any ring homomorphism `R →+* S` yields the corresponding identity in `S`, including
the formal power series identity in `PowerSeries R`. Inverting both sides in `PowerSeries R`
identifies the product of the geometric series `∑ (χ g) ^ k X ^ k` with the `(|G| / f)`-th power
of `(mk 1).subst (X ^ f)`.

## Main results

* `CommGroup.prod_one_sub_C_monoidHom_mul_X_of_zpowers_eq_top`: the cyclic-group case where `g`
  generates `G`, giving `∏ χ : G →* Rˣ, (1 - C (χ g) * X) = 1 - X ^ orderOf g`.
* `CommGroup.prod_one_sub_C_monoidHom_mul_X`:
  `∏ χ : G →* Rˣ, (1 - C (χ g) * X) = (1 - X ^ orderOf g) ^ (Nat.card G / orderOf g)`.
* `CommGroup.prod_one_sub_map_monoidHom_mul`: image under any ring homomorphism `f : R →+* S`
  and evaluation at `z : S`.
* `CommGroup.prod_one_sub_monoidHom_mul`: scalar specialization at `z : R`.
* `CommGroup.prod_one_sub_C_monoidHom_mul_X_powerSeries`: the same product in `PowerSeries R`.
* `CommGroup.prod_mk_pow_monoidHom`: the inverse geometric-series product in `PowerSeries R`,
  `∏ χ : G →* Rˣ, mk (fun k ↦ (χ g : R) ^ k) =
    ((mk 1).subst (X ^ orderOf g)) ^ (|G| / orderOf g)`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 4, Theorem 4.3.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
* Built on Mathlib's `CommGroup` duality (`Mathlib.GroupTheory.FiniteAbelian.Duality`, by
  Michael Stoll) and `X_pow_sub_C_eq_prod` (`Mathlib.FieldTheory.KummerExtension`).
-/

public section

namespace CommGroup

variable {G R : Type*} [CommGroup G] [Finite G] [CommRing R] [IsDomain R]
  [hR : HasEnoughRootsOfUnity R (Monoid.exponent G)]

/-- **Cyclic case of the linear character product in `R[X]`.** If `g` generates the finite
commutative group `G` (so `orderOf g = |G|`), then the values `χ g` run bijectively over the
`orderOf g`-th roots of unity in `R`, and
`∏ χ : G →* Rˣ, (1 - C (χ g) * X) = 1 - X ^ orderOf g`. -/
theorem prod_one_sub_C_monoidHom_mul_X_of_zpowers_eq_top {g : G} (hg : Subgroup.zpowers g = ⊤) :
    ∏ χ : G →* Rˣ, (1 - Polynomial.C (χ g : R) * Polynomial.X) =
      1 - Polynomial.X ^ orderOf g := by
  classical
  let d : ℕ := orderOf g
  have hd_pos : 0 < d := orderOf_pos g
  have : NeZero d := ⟨hd_pos.ne'⟩
  have hcardG : Nat.card G = d := by
    have hd : d = Nat.card (Subgroup.zpowers g) := (Nat.card_zpowers g).symm
    rw [hd, hg]
    exact (Nat.card_congr Subgroup.topEquiv.toEquiv).symm
  have : HasEnoughRootsOfUnity R d := hR.of_dvd R (Monoid.order_dvd_exponent g)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot R d
  let ev : (G →* Rˣ) → R := fun ψ ↦ (ψ g : R)
  have hev_inj : Function.Injective ev := by
    intro ψ₁ ψ₂ h
    ext x
    have hx : x ∈ Subgroup.zpowers g := hg ▸ Subgroup.mem_top x
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h1 : ψ₁ g = ψ₂ g := Units.ext h
    rw [map_zpow, map_zpow, h1]
  have hpow_inj : Set.InjOn (ζ ^ ·) (Finset.range d : Set ℕ) := fun i hi j hj hij ↦
    hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
  have himg_sub :
      (Finset.univ : Finset (G →* Rˣ)).image ev ⊆ (Finset.range d).image (ζ ^ ·) := by
    intro r hr
    obtain ⟨ψ, -, rfl⟩ := Finset.mem_image.mp hr
    have hpow : (ev ψ) ^ d = 1 := by
      have h1 : (ψ g) ^ d = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
      simpa [ev] using congrArg (fun u : Rˣ ↦ (u : R)) h1
    obtain ⟨i, hi, heq⟩ := hζ.eq_pow_of_pow_eq_one hpow
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, heq⟩
  have hcard_ev : ((Finset.univ : Finset (G →* Rˣ)).image ev).card = d := by
    rw [Finset.card_image_of_injective _ hev_inj, Finset.card_univ, ← Nat.card_eq_fintype_card,
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G R, hcardG]
  have himg_eq : (Finset.univ : Finset (G →* Rˣ)).image ev = (Finset.range d).image (ζ ^ ·) :=
    Finset.eq_of_subset_of_card_le himg_sub <|
      (Finset.card_image_le).trans (by rw [Finset.card_range, hcard_ev])
  calc ∏ ψ : G →* Rˣ, (1 - Polynomial.C (ψ g : R) * Polynomial.X)
      = ∏ r ∈ (Finset.univ : Finset (G →* Rˣ)).image ev,
          (1 - Polynomial.C r * Polynomial.X) :=
        (Finset.prod_image (f := fun r ↦ 1 - Polynomial.C r * Polynomial.X)
          fun _ _ _ _ h ↦ hev_inj h).symm
    _ = ∏ r ∈ (Finset.range d).image (ζ ^ ·), (1 - Polynomial.C r * Polynomial.X) := by
        rw [himg_eq]
    _ = ∏ i ∈ Finset.range d, (1 - Polynomial.C (ζ ^ i) * Polynomial.X) :=
        Finset.prod_image hpow_inj
    _ = 1 - Polynomial.X ^ d := by
        have hpoly := congrArg (Polynomial.eval (1 : Polynomial R)) <|
          X_pow_sub_C_eq_prod (hζ.map_of_injective Polynomial.C_injective) hd_pos
            (α := (Polynomial.X : Polynomial R)) rfl
        simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
          Polynomial.eval_prod, one_pow, ← map_pow] at hpoly
        exact hpoly.symm

/-- **Product of linear character factors in `R[X]`.** Over all characters `χ : G →* Rˣ` of a
finite commutative group `G`, the product `∏ χ, (1 - C (χ g) * X)` equals
`(1 - X ^ f) ^ (|G| / f)`, where `f = orderOf g`. -/
theorem prod_one_sub_C_monoidHom_mul_X (g : G) :
    ∏ χ : G →* Rˣ, (1 - Polynomial.C (χ g : R) * Polynomial.X) =
      (1 - Polynomial.X ^ orderOf g) ^ (Nat.card G / orderOf g) := by
  let H : Subgroup G := Subgroup.zpowers g
  let gH : H := ⟨g, Subgroup.mem_zpowers g⟩
  have hordH : orderOf gH = orderOf g := Subgroup.orderOf_mk g (Subgroup.mem_zpowers g)
  have : HasEnoughRootsOfUnity R (Monoid.exponent H) :=
    hR.of_dvd R (Monoid.exponent_submonoid_dvd H.toSubmonoid)
  have hgen : Subgroup.zpowers gH = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ⟨k, Subtype.ext (by simp [gH])⟩
  have hker : Nat.card (MonoidHom.domRestrictHom H Rˣ).ker = Nat.card G / orderOf g := by
    rw [CommGroup.card_domRestrictHom_ker R H]
    have hlag := H.card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_zpowers g] at hlag
    rw [hlag, Nat.mul_div_cancel _ (orderOf_pos g)]
  rw [← hker]
  calc ∏ χ : G →* Rˣ, (1 - Polynomial.C (χ g : R) * Polynomial.X)
      = (∏ ψ : H →* Rˣ, (1 - Polynomial.C (ψ gH : R) * Polynomial.X)) ^
          Nat.card (MonoidHom.domRestrictHom H Rˣ).ker :=
        MonoidHom.prod_comp_of_surjective (MonoidHom.domRestrictHom H Rˣ)
          (MonoidHom.domRestrict_surjective R H)
          (fun ψ : H →* Rˣ ↦ 1 - Polynomial.C (ψ gH : R) * Polynomial.X)
    _ = (1 - Polynomial.X ^ orderOf g) ^ Nat.card (MonoidHom.domRestrictHom H Rˣ).ker := by
        rw [prod_one_sub_C_monoidHom_mul_X_of_zpowers_eq_top (R := R) hgen, hordH]

/-- **Evaluated character product along a ring homomorphism.** Applying `f : R →+* S` and
evaluating at `z : S` gives
`∏ χ, (1 - f (χ g) * z) = (1 - z ^ orderOf g) ^ (|G| / orderOf g)`. -/
theorem prod_one_sub_map_monoidHom_mul {S : Type*} [CommRing S] (f : R →+* S) (g : G) (z : S) :
    ∏ χ : G →* Rˣ, (1 - f (χ g : R) * z) =
      (1 - z ^ orderOf g) ^ (Nat.card G / orderOf g) := by
  have h := congrArg (Polynomial.eval₂RingHom f z) (prod_one_sub_C_monoidHom_mul_X (R := R) g)
  simpa only [map_prod, map_pow, map_sub, map_one, map_mul, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_C, Polynomial.eval₂_X] using h

/-- **Evaluated character product in `R`.** For any `z : R`,
`∏ χ : G →* Rˣ, (1 - (χ g : R) * z) = (1 - z ^ orderOf g) ^ (|G| / orderOf g)`. -/
theorem prod_one_sub_monoidHom_mul (g : G) (z : R) :
    ∏ χ : G →* Rˣ, (1 - (χ g : R) * z) = (1 - z ^ orderOf g) ^ (Nat.card G / orderOf g) :=
  prod_one_sub_map_monoidHom_mul (RingHom.id R) g z

/-- **Product of linear character factors in `PowerSeries R`.** -/
theorem prod_one_sub_C_monoidHom_mul_X_powerSeries (g : G) :
    ∏ χ : G →* Rˣ, (1 - PowerSeries.C (χ g : R) * PowerSeries.X) =
      (1 - PowerSeries.X ^ orderOf g) ^ (Nat.card G / orderOf g) :=
  prod_one_sub_map_monoidHom_mul (PowerSeries.C (R := R)) g PowerSeries.X

/-- **Product of geometric series over characters.** In `PowerSeries R`, the product of the
geometric series `∑ (χ g) ^ k X ^ k` over all characters `χ : G →* Rˣ` equals
`((mk 1).subst (X ^ orderOf g)) ^ (|G| / orderOf g)`. -/
theorem prod_mk_pow_monoidHom (g : G) :
    ∏ χ : G →* Rˣ, PowerSeries.mk (fun k ↦ (χ g : R) ^ k) =
      ((PowerSeries.mk 1 : PowerSeries R).subst (PowerSeries.X ^ orderOf g)) ^
        (Nat.card G / orderOf g) := by
  let A : PowerSeries R := ∏ χ : G →* Rˣ, PowerSeries.mk (fun k ↦ (χ g : R) ^ k)
  let B : PowerSeries R :=
    ((PowerSeries.mk 1 : PowerSeries R).subst (PowerSeries.X ^ orderOf g)) ^
      (Nat.card G / orderOf g)
  let C : PowerSeries R := (1 - PowerSeries.X ^ orderOf g) ^ (Nat.card G / orderOf g)
  have hAC : A * C = 1 := by
    dsimp only [A, C]
    rw [← prod_one_sub_C_monoidHom_mul_X_powerSeries (R := R) g, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun χ _ ↦ TauCeti.powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one _
  have hBC : B * C = 1 := by
    dsimp only [B, C]
    rw [← PowerSeries.expand_apply (orderOf g) (orderOf_pos g).ne', ← mul_pow,
      PowerSeries.expand_mk_one_mul_one_sub_X_pow (orderOf g) (orderOf_pos g).ne', one_pow]
  calc A = A * 1 := (mul_one A).symm
    _ = A * (B * C) := by rw [hBC]
    _ = B * (A * C) := by ring
    _ = B := by rw [hAC, mul_one]

end CommGroup
