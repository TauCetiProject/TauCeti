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
  `k ≥ 2`, is carried by an element of `G_(k+1)` to a smooth vortex lying in `A_m^s` for every real
  `s`, every derivative of whose difference with the reference field `x_m` is `O(exp (-c |z|))` at
  infinity for every rate `c < 1 / 2`
  (`TauCeti.Vortex.exists_sobolevGaugeGroup_smul_mem_framedFieldSpace`). The representative is the
  normalized smooth framed vortex with the divisor of `x`
  (`TauCeti.Vortex.exists_framedGaugeGroup_smul_mem_framedFieldSpace`), and it lies in the
  `G_(k+1)`-orbit of `x` by Taubes's classification on the Sobolev scale. A `C²` vortex of `A_m^k`
  need not itself lie in `A_m^(k+1)`: an element of `G_(k+1)` moves a field of `A_m^(k+1)` only
  within `A_m^k`.
* **The moduli of different orders agree.** For `4 ≤ k ≤ k'` the inclusion induces a bijection
  from the Sobolev moduli of order `k'` onto those of order `k`
  (`TauCeti.Vortex.sobolevVortexModuliEquivOfLE`), compatible with their identifications with
  `Sym ℂ m` (`TauCeti.Vortex.sobolevVortexModuliDivisor_sobolevVortexModuliEquivOfLE`). These
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
* `exists_sobolevGaugeGroup_smul_mem_framedFieldSpace`: every `C²` vortex of `A_m^k` is
  `G_(k+1)`-equivalent to a smooth vortex of every `A_m^s`, with exponential decay.
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
private theorem inclusion_mem_sobolevVortices (h : k ≤ k') {x : framedFieldSpace f m k'}
    (hx : x ∈ sobolevVortices f m k') :
    Set.inclusion (framedFieldSpace_mono f m (by exact_mod_cast h)) x ∈ sobolevVortices f m k :=
  mem_sobolevVortices.2 ((mem_sobolevVortices (x := x)).1 hx)

variable [Fact (1 < k)] [Fact (1 < k')]

/-- **The inclusion `A_m^(k') ⊆ A_m^k` preserves the divisor**: a `C²` vortex of `A_m^(k')` has the
same zero divisor as a vortex of `A_m^k`. -/
@[simp]
theorem sobolevVortexDivisor_inclusion (h : k ≤ k') (x : sobolevVortices f m k') :
    sobolevVortexDivisor (k := k)
        ⟨⟨x, framedFieldSpace_mono f m (by exact_mod_cast h) x.1.2⟩,
          mem_sobolevVortices.2 ((mem_sobolevVortices (x := x.1)).1 x.2)⟩ =
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
  exact (key hs ⟨Set.inclusion hle x, inclusion_mem_sobolevVortices h x.2⟩
    ⟨Set.inclusion hle y, inclusion_mem_sobolevVortices h y.2⟩).trans <|
    (Eq.congr (sobolevVortexDivisor_inclusion h x) (sobolevVortexDivisor_inclusion h y)).trans
      (key hs' x y).symm

/-- **Every orbit has a smooth representative of every order.** For `k ≥ 2`, every `C²` vortex `x`
of `A_m^k` is carried by an element of `G_(k+1)` to a smooth vortex lying in the affine Sobolev
space `A_m^s` for every real `s`, such that every derivative of its difference with the reference
field is `O(exp (-c |z|))` at infinity for every rate `c < 1 / 2`. -/
theorem exists_sobolevGaugeGroup_smul_mem_framedFieldSpace {hs : 1 < (k : ℝ) + 1}
    (x : sobolevVortices f m k) :
    ∃ u : sobolevGaugeGroup hs,
      ContDiff ℝ ∞ ((u • (x : framedFieldSpace f m k) : framedFieldSpace f m k) :
        ℂ → EuclideanSpace ℝ (Fin 4)) ∧
      (∀ s : ℝ, ((u • (x : framedFieldSpace f m k) : framedFieldSpace f m k) :
        ℂ → EuclideanSpace ℝ (Fin 4)) ∈ framedFieldSpace f m s) ∧
      ∀ c < 1 / 2, ∀ n : ℕ,
        iteratedFDeriv ℝ n (((u • (x : framedFieldSpace f m k) : framedFieldSpace f m k) :
          ℂ → EuclideanSpace ℝ (Fin 4)) - referenceField f m) =O[cocompact ℂ]
          fun z ↦ Real.exp (-(c * ‖z‖)) := by
  -- The smooth framed vortex with the divisor of `x`, normalized at its end.
  obtain ⟨y, hy⟩ := framedVortexDivisor_surjective m (sobolevVortexDivisor x)
  obtain ⟨hyc, hysol, hyfr⟩ := mem_framedVortexSubMulAction.1 y.2
  obtain ⟨v, hv, hdec⟩ := exists_framedGaugeGroup_smul_mem_framedFieldSpace f hyc hysol hyfr
  obtain ⟨hvc, hvsol, -⟩ := mem_framedVortexSubMulAction.1 (v • y).2
  rw [SubMulAction.val_smul] at hvc hvsol
  -- It is a `C²` vortex of `A_m^k` with the divisor of `x`, hence in the orbit of `x`.
  let y' : sobolevVortices f m k :=
    ⟨⟨v • (y : ℂ → EuclideanSpace ℝ (Fin 4)), hv k⟩,
      mem_sobolevVortices.2 ⟨hvc.of_le (by simp), hvsol⟩⟩
  have hdiv : sobolevVortexDivisor y' = sobolevVortexDivisor x := by
    rw [sobolevVortexDivisor_eq_framedVortexDivisor y' (v • y) (SubMulAction.val_smul v y).symm,
      framedVortexDivisor_smul, hy]
  obtain ⟨u, hu⟩ := sobolevVortexDivisor_eq_sobolevVortexDivisor_iff.1 hdiv
  refine ⟨u, ?_, ?_, ?_⟩ <;> rw [hu]
  · exact hvc
  · exact hv
  · exact hdec

/-! ### The Sobolev moduli of different orders -/

/-- The inclusion of the `C²` vortices of `A_m^(k')` into those of `A_m^k`, as a map of the
sub-actions of `G_(k'+1)` and `G_(k+1)`. -/
private def subMulActionOfLE {hs : 1 < (k : ℝ) + 1} {hs' : 1 < (k' : ℝ) + 1} (hk : 3 < k)
    (h : k ≤ k') (x : sobolevVortexSubMulAction (f := f) (m := m) (hs := hs')
      (hk.trans_le h)) :
    sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk :=
  ⟨Set.inclusion (framedFieldSpace_mono f m (by exact_mod_cast h)) x.1,
    mem_sobolevVortexSubMulAction.2
      (inclusion_mem_sobolevVortices h ((mem_sobolevVortexSubMulAction (x := x.1)).1 x.2))⟩

/-- The divisor of a `C²` vortex of `A_m^(k')` does not change when it is viewed in `A_m^k`. -/
private theorem sobolevVortexModuliDivisor_mk_subMulActionOfLE {hs : 1 < (k : ℝ) + 1}
    {hs' : 1 < (k' : ℝ) + 1} (hk : 3 < k) (h : k ≤ k')
    (x : sobolevVortexSubMulAction (f := f) (m := m) (hs := hs') (hk.trans_le h)) :
    sobolevVortexModuliDivisor hk (Quotient.mk'' (subMulActionOfLE (hs := hs) hk h x)) =
      sobolevVortexModuliDivisor (hk.trans_le h) (Quotient.mk'' x) := by
  rw [sobolevVortexModuliDivisor_mk, sobolevVortexModuliDivisor_mk]
  exact sobolevVortexDivisor_inclusion h ⟨x.1, (mem_sobolevVortexSubMulAction (x := x.1)).1 x.2⟩

/-- The map from the Sobolev moduli of order `k'` to those of order `k` induced by the inclusion
`A_m^(k') ⊆ A_m^k`. It is well defined because `G_(k'+1) ≤ G_(k+1)`. -/
private def sobolevVortexModuliOfLE {hs : 1 < (k : ℝ) + 1} {hs' : 1 < (k' : ℝ) + 1} (hk : 3 < k)
    (h : k ≤ k') :
    MulAction.orbitRel.Quotient (sobolevGaugeGroup hs')
        (sobolevVortexSubMulAction (f := f) (m := m) (hs := hs') (hk.trans_le h)) →
      MulAction.orbitRel.Quotient (sobolevGaugeGroup hs)
        (sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk) :=
  Quotient.map (subMulActionOfLE hk h) fun x y hxy ↦ by
    obtain ⟨u, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hxy)
    refine MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2
      ⟨⟨u, sobolevGaugeGroup_mono hs (by norm_cast; omega) u.2⟩, ?_⟩)
    exact Subtype.ext (Subtype.ext rfl)

/-- **The Sobolev moduli of framed vortices do not depend on the order.** For `4 ≤ k ≤ k'`, the
inclusion `A_m^(k') ⊆ A_m^k` induces a bijection from the `G_(k'+1)`-orbits of `C²` vortices of
`A_m^(k')` onto the `G_(k+1)`-orbits of `C²` vortices of `A_m^k`. -/
def sobolevVortexModuliEquivOfLE {hs : 1 < (k : ℝ) + 1} {hs' : 1 < (k' : ℝ) + 1} (hk : 3 < k)
    (h : k ≤ k') :
    MulAction.orbitRel.Quotient (sobolevGaugeGroup hs')
        (sobolevVortexSubMulAction (f := f) (m := m) (hs := hs') (hk.trans_le h)) ≃
      MulAction.orbitRel.Quotient (sobolevGaugeGroup hs)
        (sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk) :=
  Equiv.ofBijective (sobolevVortexModuliOfLE hk h) <| by
    have hcomp : sobolevVortexModuliDivisor (hs := hs) hk ∘ sobolevVortexModuliOfLE hk h =
        sobolevVortexModuliDivisor (f := f) (m := m) (hs := hs') (hk.trans_le h) :=
      funext fun q ↦ Quotient.inductionOn q (sobolevVortexModuliDivisor_mk_subMulActionOfLE hk h)
    refine (Function.Bijective.of_comp_iff'
      ⟨sobolevVortexModuliDivisor_injective hk, sobolevVortexModuliDivisor_surjective hk⟩ _).1 ?_
    rw [hcomp]
    exact ⟨sobolevVortexModuliDivisor_injective _, sobolevVortexModuliDivisor_surjective _⟩

/-- The bijection of moduli sends the orbit of a vortex of `A_m^(k')` to its orbit in `A_m^k`. -/
@[simp]
theorem sobolevVortexModuliEquivOfLE_mk {hs : 1 < (k : ℝ) + 1} {hs' : 1 < (k' : ℝ) + 1}
    (hk : 3 < k) (h : k ≤ k')
    (x : sobolevVortexSubMulAction (f := f) (m := m) (hs := hs') (hk.trans_le h)) :
    sobolevVortexModuliEquivOfLE (hs := hs) hk h (Quotient.mk'' x) =
      Quotient.mk'' ⟨⟨x.1, framedFieldSpace_mono f m (by exact_mod_cast h) x.1.2⟩,
        mem_sobolevVortexSubMulAction.2 (mem_sobolevVortices.2 ((mem_sobolevVortices (x := x.1)).1
          ((mem_sobolevVortexSubMulAction (x := x.1)).1 x.2)))⟩ :=
  (rfl)

/-- **The bijection of moduli preserves the divisor**: it is compatible with the identifications
of the Sobolev moduli of both orders with `Sym ℂ m` (`sobolevVortexModuliEquiv`). -/
@[simp]
theorem sobolevVortexModuliDivisor_sobolevVortexModuliEquivOfLE {hs : 1 < (k : ℝ) + 1}
    {hs' : 1 < (k' : ℝ) + 1} (hk : 3 < k) (h : k ≤ k')
    (q : MulAction.orbitRel.Quotient (sobolevGaugeGroup hs')
      (sobolevVortexSubMulAction (f := f) (m := m) (hs := hs') (hk.trans_le h))) :
    sobolevVortexModuliDivisor hk (sobolevVortexModuliEquivOfLE (hs := hs) hk h q) =
      sobolevVortexModuliDivisor (hk.trans_le h) q :=
  Quotient.inductionOn q (sobolevVortexModuliDivisor_mk_subMulActionOfLE hk h)

/-- The bijection of moduli between orders `k'` and `k` is the composite of their
identifications with `Sym ℂ m`. -/
theorem sobolevVortexModuliEquivOfLE_eq {hs : 1 < (k : ℝ) + 1} {hs' : 1 < (k' : ℝ) + 1}
    (hk : 3 < k) (h : k ≤ k') :
    sobolevVortexModuliEquivOfLE (f := f) (m := m) (hs := hs) (hs' := hs') hk h =
      (sobolevVortexModuliEquiv (hk.trans_le h)).trans (sobolevVortexModuliEquiv hk).symm :=
  Equiv.ext fun q ↦ (Equiv.eq_symm_apply _).2 <| by
    rw [sobolevVortexModuliEquiv_apply, sobolevVortexModuliEquiv_apply]
    exact sobolevVortexModuliDivisor_sobolevVortexModuliEquivOfLE hk h q

/-- For `k = k'` the bijection of moduli is the identity. -/
@[simp]
theorem sobolevVortexModuliEquivOfLE_refl {hs : 1 < (k : ℝ) + 1} (hk : 3 < k) :
    sobolevVortexModuliEquivOfLE (f := f) (m := m) (hs := hs) (hs' := hs) hk le_rfl =
      Equiv.refl _ := by
  rw [sobolevVortexModuliEquivOfLE_eq]
  exact Equiv.self_trans_symm _

/-- **The bijections of moduli compose**: for `4 ≤ k ≤ k' ≤ k''`, passing from order `k''` to `k'`
and then to `k` is passing from `k''` to `k`. -/
theorem sobolevVortexModuliEquivOfLE_trans {k'' : ℕ} [Fact (1 < k'')] {hs : 1 < (k : ℝ) + 1}
    {hs' : 1 < (k' : ℝ) + 1} {hs'' : 1 < (k'' : ℝ) + 1} (hk : 3 < k) (h : k ≤ k')
    (h' : k' ≤ k'') :
    (sobolevVortexModuliEquivOfLE (f := f) (m := m) (hs := hs') (hs' := hs'') (hk.trans_le h)
        h').trans (sobolevVortexModuliEquivOfLE (hs := hs) hk h) =
      sobolevVortexModuliEquivOfLE (hs' := hs'') hk (h.trans h') := by
  simp only [sobolevVortexModuliEquivOfLE_eq]
  ext q
  simp

end TauCeti.Vortex
