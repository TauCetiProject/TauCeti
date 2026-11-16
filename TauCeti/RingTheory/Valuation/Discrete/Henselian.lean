/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Submonoid
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Valuation.DiscreteValuativeRel
import TauCeti.RingTheory.Henselian.Basic
import TauCeti.RingTheory.Valuation.NontrivialComap
import TauCeti.RingTheory.Valuation.ValuationSubring

/-!
# Rigidity of rank-one discrete valuations over Henselian rank-one valued fields

Let `K` be a field carrying a nontrivial valuation `w` whose valuation ring `𝒪 = w.valuationSubring`
is a Henselian local ring of Krull dimension at most one (in particular, any Henselian rank-one
valued field, with arbitrary finite or infinite residue field). Every nontrivial rank-one discrete
valuation `v` on `K` (valued in an arbitrary linearly ordered commutative group with zero, with no
Henselianity assumption on `v`) is automatically equivalent to `w`:

1. The value group `v.valueGroup` is cyclic and torsion-free, so Hensel's lemma forces the unit
   homomorphism `f : 𝒪ˣ →* v.valueGroup` induced by `v` to kill every principal unit `1 + z`
   (`z ∈ 𝔪`), by `MonoidHom.apply_eq_one_of_residue_eq_one`.
2. Consequently `v (z : K) ≤ 1` for every `z ∈ 𝔪` (otherwise `v (1 + z) = v z > 1`). Choosing a
   nonzero element `ϖ ∈ 𝔪` (from nontriviality of `w`) and using that `v.valueGroup` is
   archimedean shows `f u ≤ 1` for every `u : 𝒪ˣ`: if `1 < f u`, a power `u ^ (m + 1) * ϖ ∈ 𝔪`
   would have valuation strictly exceeding `1`. Applying this to `u` and `u⁻¹` gives `v x = 1`
   whenever `w x = 1`.
3. Since `v` is nontrivial and `Ring.KrullDimLE 1 𝒪`, `Valuation.isEquiv_of_val_eq_one_imp`
   concludes `v.IsEquiv w`.

Pulling back along an algebraic algebra `L / K` shows that when `K` is a nontrivial rank-one
Henselian valued field and `L` carries a nontrivial rank-one discrete `ValuativeRel`, `L / K` is
automatically a `ValuativeExtension K L`. Each hypothesis on `K` and `L` is sharp:

* without `HenselianLocalRing`: `K = L = ℚ` with the `p`-adic valuation on `K` and the `q`-adic
  valuation on `L` (`p ≠ q`);
* without `IsNontrivial K`: `K = L = ℚ_p` with the trivial valuation on `K` and the `p`-adic
  valuation on `L`;
* without `IsRankLeOne K`: `K = L = ℚ_p((t))` with the rank-two Henselian valuation `(v_t, v_p)`
  (valuation ring `ℤ_p + t ℚ_p[[t]]`) on `K` and the `t`-adic valuation `v_t` on `L`;
* without `IsDiscrete L`: `K = ℚ_p ∩ AlgebraicClosure ℚ` (the Henselization of `ℚ` at `p`) inside
  `L = AlgebraicClosure ℚ` carrying an `ℓ`-adic valuation (`ℓ ≠ p`);
* without `IsRankLeOne L`: `K = L = ℚ_p((t))` with the `t`-adic valuation `v_t` on `K` and the
  rank-two discrete valuation `(v_t, v_p)` on `L`;
* without `IsNontrivial L`: `K = L = ℚ_p` with the `p`-adic valuation on `K` and the trivial
  valuation on `L`;
* without `Algebra.IsAlgebraic K L`: `L = K(t)` with the `t`-adic valuation, which restricts
  trivially to `K`.

## Main results

* `Valuation.isEquiv_of_henselianLocalRing`: on a field `K` carrying a nontrivial valuation `w`
  whose valuation ring is Henselian of Krull dimension at most one, every rank-one discrete
  valuation `v` on `K` is equivalent to `w`.
* `ValuativeExtension.of_henselianLocalRing`: an algebraic algebra `L / K` from a nontrivial
  rank-one Henselian valued field `K` into a ring `L` carrying a nontrivial rank-one discrete
  `ValuativeRel` is automatically a `ValuativeExtension K L`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4 (for Hensel's lemma; the prolongation
  theorems there assume compatibility of the valuation extension).
* [A. J. Engler and A. Prestel, *Valued Fields*][engler2005], Section 4.4 (for F. K. Schmidt's
  counterpart theorem comparing two Henselian valuations on a non-separably-closed field, without
  discreteness).
-/

public section

open IsLocalRing ValuativeRel

namespace Valuation

/-- **Rigidity of rank-one discrete valuations over a Henselian rank-one valuation.** If `w` is a
nontrivial valuation on a field `K` whose valuation subring is a Henselian local ring of Krull
dimension at most one, then every rank-one discrete valuation `v` on `K` is equivalent to `w`. -/
theorem isEquiv_of_henselianLocalRing {K Γ₀ Γ₁ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
    (v : _root_.Valuation K Γ₀) [v.IsRankOneDiscrete]
    (w : _root_.Valuation K Γ₁) [w.IsNontrivial] [Ring.KrullDimLE 1 w.valuationSubring]
    [HenselianLocalRing w.valuationSubring] :
    v.IsEquiv w := by
  let f : w.valuationSubringˣ →* v.valueGroup :=
    (Units.map (v.comap w.valuationSubring.subtype).toMonoidHom).codRestrict v.valueGroup
      fun u ↦ v.mem_valueGroup ⟨((u : w.valuationSubring) : K), by simp [Valuation.comap_apply]⟩
  have hf_val (u : w.valuationSubringˣ) : (((f u : v.valueGroup) : Γ₀ˣ) : Γ₀) =
      v ((u : w.valuationSubring) : K) := by
    simp [f, Valuation.comap_apply]
  have hv_max {z : w.valuationSubring} (hz : z ∈ maximalIdeal w.valuationSubring) :
      v (z : K) ≤ 1 := by
    have hres : residue w.valuationSubring (1 + z) = 1 := by
      rw [map_add, map_one, (residue_eq_zero_iff z).mpr hz, add_zero]
    obtain ⟨u, hu⟩ := (residue_ne_zero_iff_isUnit (1 + z)).mp (by rw [hres]; exact one_ne_zero)
    have hfu : f u = 1 := f.apply_eq_one_of_residue_eq_one (by rw [hu, hres])
    have hv1 : v (1 + (z : K)) = 1 := by
      have hcoe : ((u : w.valuationSubring) : K) = 1 + (z : K) := by
        simpa using congrArg (Subtype.val : w.valuationSubring → K) hu
      rw [← hcoe, ← hf_val u, hfu, OneMemClass.coe_one, Units.val_one]
    by_contra hgt
    replace hgt : 1 < v (z : K) := not_le.mp hgt
    have hvmax : v (1 + (z : K)) = max (v 1) (v (z : K)) :=
      v.map_add_of_distinct_val (by rw [v.map_one]; exact hgt.ne)
    rw [v.map_one, max_eq_right hgt.le, hv1] at hvmax
    exact hgt.ne hvmax
  obtain ⟨a, ha0, ha1⟩ := IsNontrivial.exists_lt_one (v := w)
  let ϖ : w.valuationSubring := ⟨a, (w.mem_valuationSubring_iff a).mpr ha1.le⟩
  have hϖ_mem : ϖ ∈ maximalIdeal w.valuationSubring := w.mem_maximalIdeal_iff.mpr ha1
  obtain ⟨e⟩ := LinearOrderedCommGroup.isCyclic_iff_nonempty_equiv_int.mp
    (inferInstance : IsCyclic v.valueGroup)
  have : MulArchimedean v.valueGroup := MulArchimedean.comap e.toMonoidHom e.strictMono
  let γϖ : v.valueGroup :=
    ⟨Units.mk0 (v a) (v.ne_zero_iff.mpr ha0), v.mem_valueGroup ⟨a, rfl⟩⟩
  have hf_le (u : w.valuationSubringˣ) : f u ≤ 1 := by
    by_contra hgt
    replace hgt : 1 < f u := not_le.mp hgt
    obtain ⟨m, hm⟩ := MulArchimedean.arch γϖ⁻¹ hgt
    have hmul : 1 < f u ^ (m + 1) * γϖ := by
      have hlt : γϖ⁻¹ < f u ^ (m + 1) := hm.trans_lt (pow_lt_pow_right₀ hgt m.lt_succ_self)
      simpa [mul_comm] using mul_lt_mul_right hlt γϖ
    have hval : 1 < v ((((u : w.valuationSubring) ^ (m + 1) * ϖ : w.valuationSubring) : K)) := by
      simpa [hf_val u, γϖ, ϖ] using Units.val_lt_val.mpr (Subtype.coe_lt_coe.mpr hmul)
    exact hval.not_ge (hv_max (Ideal.mul_mem_left _ _ hϖ_mem))
  refine v.isEquiv_of_val_eq_one_imp w fun x hx ↦ ?_
  have hx0 : x ≠ 0 := w.ne_zero_iff.mp (by rw [hx]; exact one_ne_zero)
  let u : w.valuationSubringˣ :=
    ⟨⟨x, (w.mem_valuationSubring_iff x).mpr hx.le⟩,
      ⟨x⁻¹, (w.mem_valuationSubring_iff x⁻¹).mpr (by rw [map_inv₀, hx, inv_one])⟩,
      Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩
  have hfu : f u = 1 :=
    le_antisymm (hf_le u) (inv_le_one'.mp (by rw [← MonoidHom.map_inv]; exact hf_le u⁻¹))
  simpa [u, hfu] using (hf_val u).symm

end Valuation

/-- **Automatic valuation compatibility along algebraic extensions of nontrivial rank-one Henselian
valued fields.** Let `K` be a nontrivial rank-one valued field whose integer ring is Henselian, and
let `L / K` be an algebraic algebra carrying a nontrivial rank-one discrete `ValuativeRel`. Then
`L / K` is automatically a `ValuativeExtension K L`. -/
theorem ValuativeExtension.of_henselianLocalRing (K L : Type*) [Field K] [ValuativeRel K]
    [IsNontrivial K] [IsRankLeOne K] [HenselianLocalRing (valuation K).integer]
    [Ring L] [ValuativeRel L] [IsDiscrete L] [IsRankLeOne L] [IsNontrivial L]
    [Algebra K L] [Algebra.IsAlgebraic K L] :
    ValuativeExtension K L := by
  let v : Valuation K (ValueGroupWithZero L) := (valuation L).comap (algebraMap K L)
  obtain ⟨e⟩ := (ValueGroupWithZero.nonempty_orderMonoidIso_withZeroMulInt_iff (R := L)).mpr
    ⟨inferInstance, inferInstance, inferInstance⟩
  have : IsCyclic (ValueGroupWithZero L)ˣ :=
    (Units.mapEquiv e.toMulEquiv).isCyclic.mpr inferInstance
  have : v.IsNontrivial := (valuation L).isNontrivial_comap_algebraMap
  have : v.IsRankOneDiscrete := .mk' v
  have : Ring.KrullDimLE 1 (valuation K).valuationSubring :=
    (valuation K).krullDimLE_one_valuationSubring
  have : HenselianLocalRing (valuation K).valuationSubring :=
    inferInstanceAs (HenselianLocalRing (valuation K).integer)
  have hK : v.IsEquiv (valuation K) := v.isEquiv_of_henselianLocalRing (valuation K)
  refine ⟨fun {a b} ↦ ?_⟩
  rw [(valuation L).vle_iff_le, ← Valuation.comap_apply, ← Valuation.comap_apply, hK a b,
    ← (valuation K).vle_iff_le]
