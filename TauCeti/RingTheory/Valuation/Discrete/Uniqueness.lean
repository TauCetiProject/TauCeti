/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import TauCeti.RingTheory.Henselian.Basic
import TauCeti.RingTheory.LocalRing.Basic
import TauCeti.RingTheory.Valuation.Archimedean
import TauCeti.RingTheory.Valuation.Discrete.Basic
import TauCeti.RingTheory.Valuation.Discrete.Comap
import TauCeti.RingTheory.Valuation.NontrivialComap

/-!
# Uniqueness of rank-one discrete valuations on rank-one Henselian valued fields

Let `K` be a field equipped with a nontrivial rank-one valuation `v₀` whose valuation ring is
Henselian (`HenselianRing v₀.integer (maximalIdeal v₀.integer)`), and let `v` be any rank-one
discrete valuation on `K` (not assumed Henselian). This file proves that `v` is equivalent to `v₀`.

The argument is elementary and needs neither completeness nor finiteness of the residue field.
Since `2` and `3` cannot both lie in the maximal ideal of the local ring `v₀.integer`, some
`ℓ ∈ {2, 3}` is invertible in `v₀.integer`. By Hensel's lemma, every element `1 + y` with
`v₀ y < 1` is an `ℓ ^ k`-th power in `v₀.integer` for every `k : ℕ`. Because the value group of
`v` is cyclic (hence has no nontrivial `ℓ`-divisible element), `v (1 + y) = 1` and therefore
`v y ≤ 1` whenever `v₀ y < 1`. Archimedeanity of the two value groups then upgrades this to
`v x < 1 ↔ v₀ x < 1`, which is equivalence of the two valuations.

As a consequence, every rank-one discrete valuative relation on `K`, if one exists, equals a
given nontrivial rank-one Henselian valuative relation on `K`, and every integral algebra `L / K`
into a ring carrying a rank-one discrete valuative relation is automatically a
`ValuativeExtension K L`. In particular, any finite algebra structure between nonarchimedean local
fields is automatically compatible with their valuations.

Without the rank-one hypothesis on `v₀`, the result is false: a rank-two Henselian valuation ring
such as `ℚ[[t]] + s ℚ((t))[[s]]` on `ℚ((t))((s))` admits the inequivalent rank-one discrete
`s`-adic valuation as a coarsening. Without discreteness of `v`, it is also false: a `q`-adic
valuation on `ℚ` (`q ≠ p`) extends to a non-discrete valuation on `ℚ_p`.

## Main results

* `Valuation.isEquiv_of_isRankOneDiscrete_of_henselianRing`: every rank-one discrete valuation on
  a field carrying a nontrivial rank-one Henselian valuation is equivalent to it.
* `Valuation.isEquiv_valuation_of_isRankOneDiscrete_of_henselianRing`: the `ValuativeRel` form.
* `ValuativeRel.eq_of_isRankOneDiscrete_of_henselianRing`: any rank-one discrete valuative relation
  on a field carrying a nontrivial rank-one Henselian valuative relation equals it.
* `RingHom.map_vle_map_iff_of_isRankOneDiscrete`: a ring homomorphism from a nontrivial rank-one
  Henselian valued field into a ring with a rank-one discrete valuative relation preserves and
  reflects `≤ᵥ` whenever the pullback valuation is nontrivial.
* `ValuativeExtension.of_isRankOneDiscrete`: an integral algebra from a nontrivial rank-one
  Henselian valued field to a ring with a rank-one discrete valuative relation is a
  `ValuativeExtension`.

## References

* F. K. Schmidt, *Mehrfach perfekte Körper*, Math. Ann. 108 (1933), 1–25.
* [A. J. Engler and A. Prestel, *Valued Fields*][engler2005], §4.4.
-/

public section

open ValuativeRel IsLocalRing
open scoped ValuativeRel

namespace Valuation

section Valuation

variable {K Γ₀ Γ : Type*} [Field K]
  [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ]

/-- On a field with a Henselian valuation `v₀`, every rank-one discrete valuation `v` is bounded by
`1` on the open unit ball `{y | v₀ y < 1}` of `v₀`. -/
private theorem val_le_one_of_lt_one_of_henselianRing (v : Valuation K Γ) [v.IsRankOneDiscrete]
    (v₀ : Valuation K Γ₀) [HenselianRing v₀.integer (maximalIdeal v₀.integer)]
    {y : K} (hy : v₀ y < 1) : v y ≤ 1 := by
  obtain ⟨ℓ, hℓ, hℓu⟩ := IsLocalRing.exists_one_lt_isUnit_natCast v₀.integer
  -- Every principal unit `1 + y` is an `ℓ ^ k`-th power in `v₀.integer` by Hensel's lemma, hence
  -- has `v`-valuation `1`.
  have h1y_ne : v (1 + y) ≠ 0 := by
    rw [ne_zero_iff]
    intro h0
    have h1 := v₀.map_one_add_of_lt hy
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  have h1y : v (1 + y) = 1 := by
    refine v.val_eq_one_of_forall_exists_pow_eq hℓ h1y_ne fun k ↦ ?_
    have hℓk : IsUnit ((ℓ ^ k : ℕ) : v₀.integer) := by
      simpa only [Nat.cast_pow] using hℓu.pow k
    have hy' : (⟨1 + y, (v₀.map_one_add_of_lt hy).le⟩ : v₀.integer) - 1 ∈
        maximalIdeal v₀.integer := by
      have hsub : (⟨1 + y, (v₀.map_one_add_of_lt hy).le⟩ : v₀.integer) - 1 = ⟨y, hy.le⟩ :=
        Subtype.ext (add_sub_cancel_left 1 y)
      rw [hsub]
      exact v₀.mem_maximalIdeal_iff.mpr hy
    obtain ⟨a, ha, -⟩ :=
      TauCeti.HenselianRing.exists_pow_eq_and_sub_one_mem_of_sub_one_mem le_rfl hℓk hy'
    exact ⟨(a : K), by simpa using congrArg Subtype.val ha⟩
  by_contra hlt
  rw [not_le] at hlt
  have h1lt : v 1 < v y := by rwa [map_one]
  exact hlt.ne' ((v.map_add_eq_of_lt_right h1lt).symm.trans h1y)

/-- **Uniqueness of rank-one discrete valuations on rank-one Henselian valued fields.** If `v₀` is
a nontrivial rank-one valuation on a field `K` whose valuation ring is Henselian, then every
rank-one discrete valuation `v` on `K` is equivalent to `v₀`. -/
theorem isEquiv_of_isRankOneDiscrete_of_henselianRing (v : Valuation K Γ) [v.IsRankOneDiscrete]
    (v₀ : Valuation K Γ₀) [v₀.IsNontrivial] [MulArchimedean v₀.ValueGroup₀]
    [HenselianRing v₀.integer (maximalIdeal v₀.integer)] :
    v.IsEquiv v₀ :=
  v.isEquiv_of_forall_lt_one_le_one v₀ (val_le_one_of_lt_one_of_henselianRing v v₀)

end Valuation

section ValuativeRel

variable {K Γ : Type*} [Field K] [ValuativeRel K]
  [ValuativeRel.IsNontrivial K] [ValuativeRel.IsRankLeOne K]
  [HenselianRing (valuation K).integer (maximalIdeal (valuation K).integer)]
  [LinearOrderedCommGroupWithZero Γ]

/-- **Uniqueness of rank-one discrete valuations for a `ValuativeRel`.** On a field carrying a
nontrivial rank-one Henselian valuative relation, every rank-one discrete valuation is equivalent
to `ValuativeRel.valuation K`. -/
theorem isEquiv_valuation_of_isRankOneDiscrete_of_henselianRing (v : Valuation K Γ)
    [v.IsRankOneDiscrete] : v.IsEquiv (valuation K) :=
  have : MulArchimedean (valuation K).ValueGroup₀ :=
    MulArchimedean.comap MonoidWithZeroHom.ValueGroup₀.embedding.toMonoidHom
      MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
  v.isEquiv_of_isRankOneDiscrete_of_henselianRing (valuation K)

end ValuativeRel

end Valuation

namespace ValuativeRel

/-- **Uniqueness of a rank-one discrete valuative relation.** If `r₁` and `r₂` are valuative
relations on a field `K` such that `r₁` is nontrivial, rank at most one, and Henselian, while `r₂`
has a rank-one discrete valuation, then `r₁ = r₂`. -/
theorem eq_of_isRankOneDiscrete_of_henselianRing {K : Type*} [Field K]
    (r₁ r₂ : ValuativeRel K) [@IsNontrivial K _ r₁] [@IsRankLeOne K _ r₁]
    [HenselianRing (@valuation K _ r₁).integer (maximalIdeal (@valuation K _ r₁).integer)]
    [(@valuation K _ r₂).IsRankOneDiscrete] : r₁ = r₂ := by
  have h : (@valuation K _ r₂).IsEquiv (@valuation K _ r₁) := by
    let := r₁
    exact Valuation.isEquiv_valuation_of_isRankOneDiscrete_of_henselianRing (@valuation K _ r₂)
  ext a b
  have h₁ : r₁.vle a b ↔ @valuation K _ r₁ a ≤ @valuation K _ r₁ b := by
    let := r₁
    exact (valuation K).vle_iff_le
  have h₂ : r₂.vle a b ↔ @valuation K _ r₂ a ≤ @valuation K _ r₂ b := by
    let := r₂
    exact (valuation K).vle_iff_le
  exact h₁.trans ((h a b).symm.trans h₂.symm)

end ValuativeRel

section RingHom

variable {K L : Type*} [Field K] [ValuativeRel K]
  [ValuativeRel.IsNontrivial K] [ValuativeRel.IsRankLeOne K]
  [HenselianRing (valuation K).integer (maximalIdeal (valuation K).integer)]
  [Ring L] [ValuativeRel L] [(valuation L).IsRankOneDiscrete]

/-- **A ring homomorphism into a rank-one discretely valued ring preserves and reflects `≤ᵥ`.**
If `K` carries a nontrivial rank-one Henselian valuative relation and the pullback of the rank-one
discrete valuation of `L` along `f : K →+* L` is nontrivial, then `f x ≤ᵥ f y ↔ x ≤ᵥ y`. -/
theorem RingHom.map_vle_map_iff_of_isRankOneDiscrete (f : K →+* L)
    [((valuation L).comap f).IsNontrivial] (x y : K) :
    f x ≤ᵥ f y ↔ x ≤ᵥ y := by
  have := (valuation L).isRankOneDiscrete_comap f
  have h := ((valuation L).comap f).isEquiv_valuation_of_isRankOneDiscrete_of_henselianRing
  rw [(valuation L).vle_iff_le, (valuation K).vle_iff_le]
  exact h x y

end RingHom

section Algebra

variable (K L : Type*) [Field K] [ValuativeRel K]
  [ValuativeRel.IsNontrivial K] [ValuativeRel.IsRankLeOne K]
  [HenselianRing (valuation K).integer (maximalIdeal (valuation K).integer)]
  [Ring L] [ValuativeRel L] [(valuation L).IsRankOneDiscrete]

/-- **Automatic valuation compatibility for integral extensions.** Every integral algebra from a
nontrivial rank-one Henselian valued field `K` to a ring `L` carrying a rank-one discrete valuative
relation is a `ValuativeExtension K L`. In particular, any finite algebra between nonarchimedean
local fields is automatically compatible with their valuations. -/
theorem ValuativeExtension.of_isRankOneDiscrete [Algebra K L] [Algebra.IsIntegral K L] :
    ValuativeExtension K L :=
  have : ((valuation L).comap (algebraMap K L)).IsNontrivial :=
    (valuation L).isNontrivial_comap_algebraMap
  ⟨fun {a b} ↦ (algebraMap K L).map_vle_map_iff_of_isRankOneDiscrete a b⟩

end Algebra
