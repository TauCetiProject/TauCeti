/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Moduli

/-!
# The Sobolev moduli of framed vortices do not depend on the Sobolev order

Framed degree-`m` plane vortex fields are modelled on the affine Sobolev spaces
`A_m^k = x_m + H^k` (`TauCeti.Vortex.framedFieldSpace`), acted on by the Sobolev gauge groups
`G_(k+1)` (`TauCeti.Vortex.sobolevGaugeGroup`). Both decrease as the order grows: for `k ≤ k'`,
`A_m^(k') ⊆ A_m^k` (`TauCeti.Vortex.framedFieldSpace_mono`) and `G_(k'+1) ≤ G_(k+1)`
(`TauCeti.Vortex.sobolevGaugeGroup_mono`), and the inclusions intertwine the two actions. This file
compares the vortices of the different orders.

* **Gauge equivalence does not depend on the order.** Two `C²` vortices of `A_m^(k')` that are
  related by an element of the larger group `G_(k+1)` are already related by an element of
  `G_(k'+1)`, for `2 ≤ k ≤ k'`
  (`TauCeti.Vortex.exists_mem_sobolevGaugeGroup_gaugeTransform_eq_iff_of_le`). Both conditions say
  that the two vortices have the same zero divisor
  (`TauCeti.Vortex.sobolevVortexDivisor_eq_sobolevVortexDivisor_iff`), and the inclusion
  `A_m^(k') ⊆ A_m^k` does not change the divisor
  (`TauCeti.Vortex.sobolevVortexDivisor_inclusion`).
* **Every orbit has a smooth representative of every order.** Every `C²` vortex `x` of `A_m^k`,
  `k ≥ 2`, is carried by a unique element of `G_(k+1)` to a smooth vortex lying in `A_m^s` for
  every real `s`, every derivative of whose difference with the reference field `x_m` is
  `O(exp (-c |z|))` at infinity for every rate `c < 1 / 2`
  (`TauCeti.Vortex.exists_sobolevGaugeGroup_smul_mem_framedFieldSpace`). The representative is a
  smooth vortex with the divisor of `x` (`TauCeti.Vortex.exists_contDiff_sobolevVortexDivisor_eq`),
  and it lies in the `G_(k+1)`-orbit of `x` by Taubes's classification on the Sobolev scale. A `C²`
  vortex of `A_m^k` need not itself lie in `A_m^(k+1)`: an element of `G_(k+1)` moves a field of
  `A_m^(k+1)` only within `A_m^k`.
* **The moduli of different orders agree.** For `4 ≤ k ≤ k'` the identifications of the Sobolev
  moduli of orders `k'` and `k` with `Sym ℂ m` compose to a bijection
  (`TauCeti.Vortex.sobolevVortexModuliEquivOfLE`), which is induced by the inclusion
  (`TauCeti.Vortex.sobolevVortexModuliEquivOfLE_mk`) and preserves the divisor
  (`TauCeti.Vortex.sobolevVortexModuliDivisor_sobolevVortexModuliEquivOfLE`). These
  bijections compose along `k ≤ k' ≤ k''` (`TauCeti.Vortex.sobolevVortexModuliEquivOfLE_trans`),
  and for `k = k'` the bijection is the identity
  (`TauCeti.Vortex.sobolevVortexModuliEquivOfLE_refl`).

So the zero set of the vortex equations modulo gauge, the space on which the smooth structure of the
moduli is to be built, is the same for every Sobolev order `k ≥ 4`.

## Main results

All in the namespace `TauCeti.Vortex`:

* `sobolevVortexDivisor_inclusion`: the inclusion `A_m^(k') ⊆ A_m^k` preserves the divisor.
* `exists_mem_sobolevGaugeGroup_gaugeTransform_eq_iff_of_le`: `G_(k+1)`-equivalence of vortices
  of `A_m^(k')` is `G_(k'+1)`-equivalence.
* `exists_sobolevGaugeGroup_smul_mem_framedFieldSpace`: every `C²` vortex of `A_m^k` is carried by
  a unique element of `G_(k+1)` to a smooth vortex of every `A_m^s`, with exponential decay.
* `sobolevVortexModuliEquivOfLE`: for `4 ≤ k ≤ k'`, the bijection between the Sobolev moduli of
  orders `k'` and `k` induced by the inclusion.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Topology Asymptotics
open scoped ContDiff

variable {f : ContDiffBump (0 : ℝ)} {m : ℕ} {k k' : ℕ}

/-! ### Vortices of different orders -/

/-- A `C²` vortex of `A_m^(k')` is a `C²` vortex of `A_m^k`, for `k ≤ k'`. -/
theorem inclusion_mem_sobolevVortices (h : k ≤ k') {x : framedFieldSpace f m k'}
    (hx : x ∈ sobolevVortices f m k') :
    Set.inclusion (framedFieldSpace_mono f m (by exact_mod_cast h)) x ∈ sobolevVortices f m k :=
  mem_sobolevVortices.2 ((mem_sobolevVortices (x := x)).1 hx)

variable [Fact (1 < k)] [Fact (1 < k')]

/-- **The inclusion `A_m^(k') ⊆ A_m^k` preserves the divisor**: a `C²` vortex of `A_m^(k')` has the
same zero divisor as a vortex of `A_m^k`. -/
@[simp]
theorem sobolevVortexDivisor_inclusion (h : k ≤ k') (x : sobolevVortices f m k') :
    sobolevVortexDivisor ⟨Set.inclusion (framedFieldSpace_mono f m (by exact_mod_cast h)) x.val,
        inclusion_mem_sobolevVortices h x.property⟩ =
      sobolevVortexDivisor x :=
  sobolevVortexDivisor_eq_iff.2 (isZeroMultiplicity_sectionValue_sobolevVortexDivisor x)

omit [Fact (1 < k')] in
/-- **Gauge equivalence of vortices does not depend on the order.** For `2 ≤ k ≤ k'`, two `C²`
vortices of `A_m^(k')` related by an element of `G_(k+1)` are related by an element of the smaller
group `G_(k'+1)`. -/
theorem exists_mem_sobolevGaugeGroup_gaugeTransform_eq_iff_of_le (h : k ≤ k')
    {hs : 1 < (k : ℝ) + 1} {hs' : 1 < (k' : ℝ) + 1} (x y : sobolevVortices f m k') :
    (∃ u ∈ sobolevGaugeGroup hs, gaugeTransform u y = x) ↔
      ∃ u ∈ sobolevGaugeGroup hs', gaugeTransform u y = x := by
  have : Fact (1 < k') := ⟨(Fact.out : 1 < k).trans_le h⟩
  have key {j : ℕ} [Fact (1 < j)] (hj : 1 < (j : ℝ) + 1) (x y : sobolevVortices f m j) :
      (∃ u ∈ sobolevGaugeGroup hj, gaugeTransform u y = x) ↔
        sobolevVortexDivisor x = sobolevVortexDivisor y := by
    rw [sobolevVortexDivisor_eq_sobolevVortexDivisor_iff (hs := hj)]
    simp only [Subtype.ext_iff, coe_sobolevGaugeGroup_smul, Subtype.exists, exists_prop]
  have hle : framedFieldSpace f m k' ≤ framedFieldSpace f m k :=
    framedFieldSpace_mono f m (by exact_mod_cast h)
  exact (key hs ⟨Set.inclusion hle x, inclusion_mem_sobolevVortices h x.property⟩
    ⟨Set.inclusion hle y, inclusion_mem_sobolevVortices h y.property⟩).trans <|
    (Eq.congr (sobolevVortexDivisor_inclusion h x) (sobolevVortexDivisor_inclusion h y)).trans
      (key hs' x y).symm

/-- **Every orbit has a smooth representative of every order.** For `k ≥ 2`, every `C²` vortex `x`
of `A_m^k` is carried by a unique element of `G_(k+1)` to a smooth vortex `y` lying in the affine
Sobolev space `A_m^s` for every real `s`, such that every derivative of its difference with the
reference field is `O(exp (-c |z|))` at infinity for every rate `c < 1 / 2`. -/
theorem exists_sobolevGaugeGroup_smul_mem_framedFieldSpace {hs : 1 < (k : ℝ) + 1}
    (x : sobolevVortices f m k) :
    ∃ y : sobolevVortices f m k,
      ContDiff ℝ ∞ (y : ℂ → EuclideanSpace ℝ (Fin 4)) ∧
      (∀ s : ℝ, (y : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ framedFieldSpace f m s) ∧
      (∀ c < 1 / 2, ∀ n : ℕ,
        iteratedFDeriv ℝ n ((y : ℂ → EuclideanSpace ℝ (Fin 4)) - referenceField f m)
          =O[cocompact ℂ] fun z ↦ Real.exp (-(c * ‖z‖))) ∧
      ∃! u : sobolevGaugeGroup hs, u • (x : framedFieldSpace f m k) = y := by
  -- The smooth vortex with the divisor of `x` is in the orbit of `x`.
  obtain ⟨y, hy, hyc, hys, hdec⟩ :=
    exists_contDiff_sobolevVortexDivisor_eq (f := f) (k := k) (sobolevVortexDivisor x)
  exact ⟨y, hyc, hys, hdec, existsUnique_sobolevGaugeGroup_smul_eq hy⟩

/-! ### The Sobolev moduli of different orders -/

/-- **The Sobolev moduli of framed vortices do not depend on the order.** For `4 ≤ k ≤ k'`, the
`G_(k'+1)`-orbits of `C²` vortices of `A_m^(k')` correspond bijectively to the `G_(k+1)`-orbits of
`C²` vortices of `A_m^k`, through their identifications with `Sym ℂ m`
(`sobolevVortexModuliEquiv`). The bijection is induced by the inclusion `A_m^(k') ⊆ A_m^k`
(`sobolevVortexModuliEquivOfLE_mk`). -/
def sobolevVortexModuliEquivOfLE {hs : 1 < (k : ℝ) + 1} {hs' : 1 < (k' : ℝ) + 1} (hk : 3 < k)
    (h : k ≤ k') :
    MulAction.orbitRel.Quotient (sobolevGaugeGroup hs')
        (sobolevVortexSubMulAction (f := f) (m := m) (hs := hs') (hk.trans_le h)) ≃
      MulAction.orbitRel.Quotient (sobolevGaugeGroup hs)
        (sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk) :=
  (sobolevVortexModuliEquiv (hk.trans_le h)).trans (sobolevVortexModuliEquiv hk).symm

/-- **The bijection of moduli preserves the divisor**: it is compatible with the identifications
of the Sobolev moduli of both orders with `Sym ℂ m` (`sobolevVortexModuliEquiv`). -/
@[simp]
theorem sobolevVortexModuliDivisor_sobolevVortexModuliEquivOfLE {hs : 1 < (k : ℝ) + 1}
    {hs' : 1 < (k' : ℝ) + 1} (hk : 3 < k) (h : k ≤ k')
    (q : MulAction.orbitRel.Quotient (sobolevGaugeGroup hs')
      (sobolevVortexSubMulAction (f := f) (m := m) (hs := hs') (hk.trans_le h))) :
    sobolevVortexModuliDivisor hk (sobolevVortexModuliEquivOfLE (hs := hs) hk h q) =
      sobolevVortexModuliDivisor (hk.trans_le h) q := by
  rw [sobolevVortexModuliEquivOfLE, Equiv.trans_apply, ← sobolevVortexModuliEquiv_apply hk,
    Equiv.apply_symm_apply, sobolevVortexModuliEquiv_apply]

/-- The inverse bijection of moduli preserves the divisor: the divisor of the order-`k'` orbit
assigned to an order-`k` orbit `q` is the divisor of `q`. -/
@[simp]
theorem sobolevVortexModuliDivisor_sobolevVortexModuliEquivOfLE_symm {hs : 1 < (k : ℝ) + 1}
    {hs' : 1 < (k' : ℝ) + 1} (hk : 3 < k) (h : k ≤ k')
    (q : MulAction.orbitRel.Quotient (sobolevGaugeGroup hs)
      (sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk)) :
    sobolevVortexModuliDivisor (hk.trans_le h)
        ((sobolevVortexModuliEquivOfLE (hs := hs) (hs' := hs') hk h).symm q) =
      sobolevVortexModuliDivisor hk q := by
  rw [← sobolevVortexModuliDivisor_sobolevVortexModuliEquivOfLE hk h, Equiv.apply_symm_apply]

/-- The bijection of moduli sends the orbit of a vortex of `A_m^(k')` to its orbit in `A_m^k`. -/
@[simp]
theorem sobolevVortexModuliEquivOfLE_mk {hs : 1 < (k : ℝ) + 1} {hs' : 1 < (k' : ℝ) + 1}
    (hk : 3 < k) (h : k ≤ k')
    (x : sobolevVortexSubMulAction (f := f) (m := m) (hs := hs') (hk.trans_le h)) :
    sobolevVortexModuliEquivOfLE (hs := hs) hk h (Quotient.mk'' x) =
      Quotient.mk'' ⟨Set.inclusion (framedFieldSpace_mono f m (by exact_mod_cast h)) x.val,
        mem_sobolevVortexSubMulAction.2
          (inclusion_mem_sobolevVortices h
            ((mem_sobolevVortexSubMulAction (x := x.val)).1 x.property))⟩ :=
  sobolevVortexModuliDivisor_injective hk <| by
    rw [sobolevVortexModuliDivisor_sobolevVortexModuliEquivOfLE, sobolevVortexModuliDivisor_mk,
      sobolevVortexModuliDivisor_mk]
    exact (sobolevVortexDivisor_inclusion h
      ⟨x.val, (mem_sobolevVortexSubMulAction (x := x.val)).1 x.property⟩).symm

/-- For `k = k'` the bijection of moduli is the identity. -/
@[simp]
theorem sobolevVortexModuliEquivOfLE_refl {hs : 1 < (k : ℝ) + 1} (hk : 3 < k) :
    sobolevVortexModuliEquivOfLE (f := f) (m := m) (hs := hs) (hs' := hs) hk le_rfl =
      Equiv.refl _ := by
  rw [sobolevVortexModuliEquivOfLE]
  exact Equiv.self_trans_symm _

/-- **The bijections of moduli compose**: for `4 ≤ k ≤ k' ≤ k''`, passing from order `k''` to `k'`
and then to `k` is passing from `k''` to `k`. -/
@[simp]
theorem sobolevVortexModuliEquivOfLE_trans {k'' : ℕ} [Fact (1 < k'')] {hs : 1 < (k : ℝ) + 1}
    {hs' : 1 < (k' : ℝ) + 1} {hs'' : 1 < (k'' : ℝ) + 1} (hk : 3 < k) (h : k ≤ k')
    (h' : k' ≤ k'') :
    (sobolevVortexModuliEquivOfLE (f := f) (m := m) (hs := hs') (hs' := hs'') (hk.trans_le h)
        h').trans (sobolevVortexModuliEquivOfLE (hs := hs) hk h) =
      sobolevVortexModuliEquivOfLE (hs' := hs'') hk (h.trans h') := by
  rw [sobolevVortexModuliEquivOfLE, sobolevVortexModuliEquivOfLE, sobolevVortexModuliEquivOfLE,
    Equiv.trans_assoc, ← Equiv.trans_assoc (sobolevVortexModuliEquiv _).symm,
    Equiv.symm_trans_self, Equiv.refl_trans]

/-- Passing from order `k''` to `k'` and then to `k` is passing from `k''` to `k`, pointwise. -/
@[simp]
theorem sobolevVortexModuliEquivOfLE_trans_apply {k'' : ℕ} [Fact (1 < k'')]
    {hs : 1 < (k : ℝ) + 1} {hs' : 1 < (k' : ℝ) + 1} {hs'' : 1 < (k'' : ℝ) + 1} (hk : 3 < k)
    (h : k ≤ k') (h' : k' ≤ k'')
    (q : MulAction.orbitRel.Quotient (sobolevGaugeGroup hs'')
      (sobolevVortexSubMulAction (f := f) (m := m) (hs := hs'') ((hk.trans_le h).trans_le h'))) :
    sobolevVortexModuliEquivOfLE (hs := hs) hk h
        (sobolevVortexModuliEquivOfLE (hs := hs') (hk.trans_le h) h' q) =
      sobolevVortexModuliEquivOfLE (hs' := hs'') hk (h.trans h') q := by
  rw [← sobolevVortexModuliEquivOfLE_trans hk h h', Equiv.trans_apply]

end TauCeti.Vortex
