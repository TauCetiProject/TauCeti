/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.AbsoluteValue.Place
public import TauCeti.Analysis.AbsoluteValue.ValuationSubring
public import Mathlib.FieldTheory.Galois.Basic
public import TauCeti.RingTheory.Valuation.Center

import Mathlib.NumberTheory.Padics.Complex
import TauCeti.NumberTheory.NumberField.PlacesOver.Galois
import TauCeti.NumberTheory.NumberField.PlacesOver.InfinitePlace
import TauCeti.NumberTheory.NumberField.PlacesOver.Place
import TauCeti.RingTheory.Valuation.CharZero
import TauCeti.RingTheory.Valuation.InfiniteGalois
import TauCeti.RingTheory.Valuation.ValuationSubring

/-!
# Finite places of algebraic extensions of `ℚ` as valuation subrings

Let `L` be a field algebraic over `ℚ`. A finite place `w` of `L` (an `AbsoluteValue.Place L` with
`IsNonarchimedean w.val`) has the valuation subring `A_w = {x | w x ≤ 1}`
(`AbsoluteValue.valuationSubring`). This file proves that `w ↦ A_w` is a bijection from the finite
places of `L` onto the valuation subrings of `L` other than `L`
(`AbsoluteValue.Place.finitePlaceEquivValuationSubring`), and deduces the existence and the
conjugacy of the places above a given place.

* **Injectivity** holds for any field of characteristic zero: equal valuation subrings make the
  places equivalent (`AbsoluteValue.isEquiv_iff_valuationSubring`), and equivalent places are equal
  (`AbsoluteValue.Place.eq_of_isEquiv`).
* **Surjectivity.** A valuation subring `A ≠ L` meets `ℤ` in a nonzero prime `pℤ`: if every nonzero
  integer were a unit of `A`, then `A` would contain `ℚ` and every element of `L`, since a nonzero
  integer multiple of an algebraic element is integral over `ℤ`
  (`ValuationSubring.exists_prime_natCast_mem_nonunits`). Embed `L` into `ℚ^alg` over `ℚ`
  and extend `A` to a valuation subring `A'` of `ℚ^alg` (`ValuationSubring.exists_comap_eq`). The
  norm of `PadicAlgCl p` pulled back along a `ℚ`-embedding of `ℚ^alg` is a place `w₀` above `p`
  (`AbsoluteValue.Place.exists_under_eq_padic`). Both `A'` and `A_{w₀}` meet `ℚ` in the
  localization of `ℤ` at `p` (`ValuationSubring.comap_algebraMap_rat_eq_of_natCast_mem_nonunits`),
  so they are conjugate under `Gal(ℚ^alg/ℚ)`
  (`ValuationSubring.exists_algEquiv_smul_eq_of_comap_eq_of_isGalois`); so `A'` is the valuation
  subring of a conjugate of `w₀`, and `A` that of its restriction to `L`.
* **Places above a place.** For fields `K ⊆ L` with `L` algebraic over `ℚ`, every place of `K` is
  the restriction of a place of `L` (`AbsoluteValue.Place.exists_under_eq`): over a finite place
  extend its valuation subring to `L`, over an infinite place use Tau Ceti's
  `NumberField.nonempty_setOf_liesOver_infinitePlace`. For `L / K` Galois, possibly infinite,
  `L ≃ₐ[K] L` is transitive on the places of `L` with a given restriction to `K`
  (`AbsoluteValue.Place.exists_smul_eq_of_under_eq`), with no algebraicity hypothesis over `ℚ`:
  over a finite place through the conjugacy of the valuation subrings, over an infinite place by
  Tau Ceti's `NumberField.exists_smul_eq_of_liesOver_infinitePlace`. The same holds for a group
  acting on `L` that maps onto `L ≃ₐ[K] L`
  (`AbsoluteValue.Place.exists_smul_eq_of_under_eq_of_surjective`); Mathlib's `IsGaloisGroup` is
  not enough when `L / K` is infinite, since a countable dense subgroup of `Gal(ℚ^alg/ℚ)` has
  countable orbits, while `ℚ^alg` has uncountably many places above each place of `ℚ`.

## Main results

* `AbsoluteValue.Place.eq_of_valuationSubring_eq`: a finite place is determined by its valuation
  subring.
* `AbsoluteValue.Place.exists_valuationSubring_eq`: for `L` algebraic over `ℚ`, every valuation
  subring of `L` other than `L` is that of a finite place.
* `AbsoluteValue.Place.finitePlaceEquivValuationSubring`: the bijection.
* `AbsoluteValue.Place.exists_under_eq_padic`: a place above each prime number.
* `AbsoluteValue.Place.exists_under_eq`, `AbsoluteValue.Place.exists_smul_eq_of_under_eq`,
  `AbsoluteValue.Place.exists_smul_eq_of_under_eq_of_surjective`: existence and conjugacy of
  places above a place.

## Acknowledgments

Using absolute values for the places of algebraic extensions of `ℚ`, so that finite and infinite
places are one type, follows the advice of Thomas Browning and Jz Pan on the Lean Zulip, in the
Riemann-Hypothesis channel, topic Library design discrepancies between RH/Mathlib/TauCeti:
<https://leanprover.zulipchat.com/#narrow/channel/658556-Riemann-Hypothesis/topic/Library.20design.20discrepancies.20between.20RH.2FMathlib.2FTauCeti/near/643780662>
and
<https://leanprover.zulipchat.com/#narrow/channel/658556-Riemann-Hypothesis/topic/Library.20design.20discrepancies.20between.20RH.2FMathlib.2FTauCeti/near/643806146>.

## References

* J. Neukirch, *Algebraic Number Theory*, Springer, 1999, Chapter II, §§3, 8 and 9.
* A. J. Engler and A. Prestel, *Valued Fields*, Springer Monographs in Mathematics, 2005, §3.2.
-/

public section

open scoped Pointwise

namespace AbsoluteValue.Place

/-! ### Finite places and valuation subrings -/

variable {L : Type*} [Field L] [CharZero L]

/-- **A finite place is determined by its valuation subring.** -/
theorem eq_of_valuationSubring_eq {v w : Place L} (hv : IsNonarchimedean v.val)
    (hw : IsNonarchimedean w.val) (h : v.val.valuationSubring hv = w.val.valuationSubring hw) :
    v = w :=
  eq_of_isEquiv ((isEquiv_iff_valuationSubring hv hw).mpr h)

/-- The valuation subring of a finite place is not the whole field. -/
theorem valuationSubring_ne_top (w : Place L) (hw : IsNonarchimedean w.val) :
    w.val.valuationSubring hw ≠ ⊤ :=
  fun h ↦ (valuationSubring_eq_top_iff hw).mp h w.isNontrivial

/-- The action of a group on a finite place moves its valuation subring. -/
private theorem valuationSubring_smul_eq {G : Type*} [Group G] [MulSemiringAction G L] (g : G)
    (w : Place L) (hw : IsNonarchimedean w.val) (hgw : IsNonarchimedean (g • w).val) :
    (g • w).val.valuationSubring hgw = g • w.val.valuationSubring hw := by
  ext x
  rw [mem_valuationSubring_iff, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    mem_valuationSubring_iff, val_smul, AbsoluteValue.smul_apply]

/-- **A place above each prime number.** A field algebraic over `ℚ` has a place restricting to the
`p`-adic absolute value on `ℚ`: the norm of `PadicAlgCl p` pulled back along a `ℚ`-embedding. -/
theorem exists_under_eq_padic [Algebra.IsAlgebraic ℚ L] (p : ℕ) [Fact p.Prime] :
    ∃ w : Place L, w.val.under ℚ = Rat.AbsoluteValue.padic p := by
  let φ : L →ₐ[ℚ] PadicAlgCl p := IsAlgClosed.lift
  have hu : (NormedField.toAbsoluteValue (PadicAlgCl p)).under ℚ = Rat.AbsoluteValue.padic p := by
    ext q
    rw [AbsoluteValue.under_apply, eq_ratCast (algebraMap ℚ _),
      ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)), Rat.AbsoluteValue.padic_eq_padicNorm,
      ← Padic.eq_padicNorm q]
    exact PadicAlgCl.norm_extends p q
  let w₁ : Place (PadicAlgCl p) := ⟨NormedField.toAbsoluteValue _, hu ▸ .padic p⟩
  refine ⟨w₁.comap (φ : L →+* PadicAlgCl p), ?_⟩
  rw [← val_under, under_comap, val_under]
  exact hu

/-- **Every proper valuation subring is that of a finite place.** For `L` algebraic over `ℚ`, a
valuation subring of `L` other than `L` is the valuation subring of a finite place of `L`. -/
theorem exists_valuationSubring_eq [Algebra.IsAlgebraic ℚ L] {A : ValuationSubring L}
    (hA : A ≠ ⊤) :
    ∃ (w : Place L) (hw : IsNonarchimedean w.val), w.val.valuationSubring hw = A := by
  let M := AlgebraicClosure ℚ
  let f : L →ₐ[ℚ] M := IsAlgClosed.lift
  obtain ⟨A', hA'⟩ := A.exists_comap_eq (f : L →+* M)
  have hA'top : A' ≠ ⊤ := by rintro rfl; exact hA (hA' ▸ rfl)
  obtain ⟨p, hp, hpA'⟩ := ValuationSubring.exists_prime_natCast_mem_nonunits hA'top
  have : Fact p.Prime := ⟨hp⟩
  -- a place `w₀` of `ℚ^alg` above `p`, and its valuation subring `A₀`
  obtain ⟨w₀, hw₀⟩ := exists_under_eq_padic (L := M) p
  have hw₀n : IsNonarchimedean w₀.val := w₀.isNonarchimedean_iff.mpr ⟨p, inferInstance, hw₀⟩
  have hpA₀ : (p : M) ∈ (w₀.val.valuationSubring hw₀n).nonunits := by
    rw [mem_nonunits_valuationSubring_iff]
    exact apply_natCast_lt_one_of_under_eq_padic hw₀
  -- `A₀` and `A'` meet `ℚ` in the same valuation subring, so they are conjugate
  obtain ⟨σ, hσ⟩ := ValuationSubring.exists_algEquiv_smul_eq_of_comap_eq_of_isGalois
    (ValuationSubring.comap_algebraMap_rat_eq_of_natCast_mem_nonunits hp hpA₀ hpA')
  have hσn : IsNonarchimedean (σ • w₀).val := by rwa [val_smul, isNonarchimedean_smul_iff]
  have hn : IsNonarchimedean ((σ • w₀).comap (f : L →+* M)).val := by
    rw [val_comap]
    exact isNonarchimedean_comp hσn (f : L →+* M).injective
  refine ⟨(σ • w₀).comap (f : L →+* M), hn, ?_⟩
  rw [← hA', ← hσ, ← valuationSubring_smul_eq σ w₀ hw₀n hσn,
    ← valuationSubring_comp hσn (f : L →+* M).injective]
  congr 1
  exact val_comap ..

variable (L) in
/-- **Finite places are proper valuation subrings.** For `L` algebraic over `ℚ`, `w ↦ A_w` is a
bijection from the finite places of `L` onto the valuation subrings of `L` other than `L`. -/
noncomputable def finitePlaceEquivValuationSubring [Algebra.IsAlgebraic ℚ L] :
    {w : Place L // IsNonarchimedean w.val} ≃ {A : ValuationSubring L // A ≠ ⊤} :=
  .ofBijective (fun w ↦ ⟨w.val.val.valuationSubring w.property, valuationSubring_ne_top _ _⟩)
    ⟨fun v w h ↦ Subtype.ext (eq_of_valuationSubring_eq v.property w.property
      (congrArg Subtype.val h)),
    fun A ↦ by
      obtain ⟨w, hw, h⟩ := exists_valuationSubring_eq A.property
      exact ⟨⟨w, hw⟩, Subtype.ext h⟩⟩

@[simp]
theorem coe_finitePlaceEquivValuationSubring_apply [Algebra.IsAlgebraic ℚ L]
    (w : {w : Place L // IsNonarchimedean w.val}) :
    (finitePlaceEquivValuationSubring L w : ValuationSubring L) =
      w.val.val.valuationSubring w.property :=
  (rfl)

/-- The finite place corresponding to a proper valuation subring `A` has valuation subring `A`. -/
@[simp]
theorem valuationSubring_finitePlaceEquivValuationSubring_symm_apply [Algebra.IsAlgebraic ℚ L]
    (A : {A : ValuationSubring L // A ≠ ⊤}) :
    ((finitePlaceEquivValuationSubring L).symm A).val.val.valuationSubring
        ((finitePlaceEquivValuationSubring L).symm A).property = A := by
  rw [← coe_finitePlaceEquivValuationSubring_apply, Equiv.apply_symm_apply]

/-! ### Places above a place -/

section Extension

variable {K : Type*} [Field K] [CharZero K] [Algebra K L]

/-- **Every place extends.** For fields `K ⊆ L` with `L` algebraic over `ℚ`, every place of `K` is
the restriction of a place of `L`. -/
theorem exists_under_eq [Algebra.IsAlgebraic ℚ L] (v : Place K) :
    ∃ w : Place L, w.under K = v := by
  by_cases hv : IsNonarchimedean v.val
  · obtain ⟨A, hA⟩ := (v.val.valuationSubring hv).exists_comap_eq (algebraMap K L)
    have hAtop : A ≠ ⊤ := by
      rintro rfl
      exact valuationSubring_ne_top v hv (hA ▸ rfl)
    obtain ⟨w, hw, rfl⟩ := exists_valuationSubring_eq hAtop
    have hwK' : IsNonarchimedean (w.under K).val :=
      (isNonarchimedean_iff_of_liesOver (K := K) w.val (w.under K).val).mp hw
    refine ⟨w, eq_of_valuationSubring_eq hwK' hv ?_⟩
    rw [← hA, ← valuationSubring_under (L := K) hw]
    congr 1
    exact val_under ..
  · have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.tower_top (K := ℚ) (A := L) K
    let u : NumberField.InfinitePlace K := ⟨v.val, (isInfinitePlace_iff v).mpr hv⟩
    obtain ⟨w, hw⟩ := NumberField.nonempty_setOf_liesOver_infinitePlace L u
    have hw' : w.LiesOver v.val := hw
    have hstd : Rat.AbsoluteValue.IsStandard (w.under ℚ) := by
      rw [← AbsoluteValue.under_under ℚ K, LiesOver.under_eq w v.val]
      exact v.isStandard_under
    exact ⟨⟨w, hstd⟩, (liesOver_iff_under_eq K).mp hw'⟩

/-- **Conjugacy of places above a place.** For a Galois extension `L / K`, possibly infinite,
two places of `L` with the same restriction to `K` are conjugate under `L ≃ₐ[K] L`. -/
theorem exists_smul_eq_of_under_eq [IsGalois K L] {w w' : Place L} (h : w.under K = w'.under K) :
    ∃ σ : L ≃ₐ[K] L, σ • w = w' := by
  by_cases hw : IsNonarchimedean w.val
  · have hwK : IsNonarchimedean (w.under K).val :=
      (isNonarchimedean_iff_of_liesOver (K := K) w.val (w.under K).val).mp hw
    have hw' : IsNonarchimedean w'.val :=
      (isNonarchimedean_iff_of_liesOver (K := K) w'.val (w'.under K).val).mpr (h ▸ hwK)
    obtain ⟨σ, hσ⟩ := ValuationSubring.exists_algEquiv_smul_eq_of_comap_eq_of_isGalois (K := K)
      (A := w.val.valuationSubring hw) (A' := w'.val.valuationSubring hw') <| by
        rw [← valuationSubring_under (L := K) hw, ← valuationSubring_under (L := K) hw']
        congr 1
        rw [← val_under, ← val_under, h]
    have hσw : IsNonarchimedean (σ • w).val := by rwa [val_smul, isNonarchimedean_smul_iff]
    exact ⟨σ, eq_of_valuationSubring_eq hσw hw' (by rw [valuationSubring_smul_eq σ w hw, hσ])⟩
  · have hwK : ¬ IsNonarchimedean (w.under K).val := fun h' ↦
      hw ((isNonarchimedean_iff_of_liesOver (K := K) w.val (w.under K).val).mpr h')
    let u : NumberField.InfinitePlace K := ⟨(w.under K).val, (isInfinitePlace_iff _).mpr hwK⟩
    have : w.val.LiesOver u.val := inferInstanceAs (w.val.LiesOver (w.under K).val)
    have : w'.val.LiesOver u.val := by
      rw [show u.val = (w'.under K).val by rw [← h]]
      infer_instance
    obtain ⟨σ, hσ⟩ := NumberField.exists_smul_eq_of_liesOver_infinitePlace u w.val w'.val
    exact ⟨σ, val_injective hσ⟩

/-- **Conjugacy under a group mapping onto the Galois group.** For `L / K` Galois and a group `G`
acting on `L` by automorphisms fixing `K` such that every `K`-automorphism of `L` is the action of
an element of `G`, two places of `L` with the same restriction to `K` are conjugate under `G`. -/
theorem exists_smul_eq_of_under_eq_of_surjective [IsGalois K L] {G : Type*} [Group G]
    [MulSemiringAction G L] [SMulCommClass G K L]
    (hG : Function.Surjective (MulSemiringAction.toAlgAut G K L)) {w w' : Place L}
    (h : w.under K = w'.under K) : ∃ g : G, g • w = w' := by
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_under_eq h
  obtain ⟨g, rfl⟩ := hG σ
  refine ⟨g, ext fun x ↦ ?_⟩
  rw [smul_apply, smul_apply, ← map_inv, AlgEquiv.smul_def, MulSemiringAction.toAlgAut_apply,
    MulSemiringAction.toAlgEquiv_apply]

end Extension

end AbsoluteValue.Place
