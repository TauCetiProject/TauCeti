/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Existence
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Regularity
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# The divisor classifies the Sobolev gauge orbits of framed plane vortices

Framed degree-`m` plane vortex fields form the affine Sobolev space `A_m^k`
(`TauCeti.Vortex.framedFieldSpace`), on which the Sobolev gauge group `G_(k+1)`
(`TauCeti.Vortex.sobolevGaugeGroup`) acts by `(a, α) ↦ (a - u⁻¹ du, u α)`. This file proves
Taubes's classification of the vortices of `A_m^k` modulo `G_(k+1)` by their zeros, for every
integer `k ≥ 2`, on the vortices that are `C²` as fields.

A continuous field of `A_m^k` has the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`
(`TauCeti.Vortex.tendsto_sectionValue_mul_inv_pow`), so the zeros of the section of a `C²` vortex
of `A_m^k`, counted with multiplicity, form an effective divisor of degree `m`
(`TauCeti.Vortex.sobolevVortexDivisor`), a point of `Sym ℂ m`. Elements of `G_(k+1)` are
continuous, so they do not change the divisor. Conversely, two `C²` vortices with the same zeros
differ by a `C²` gauge tending to one at infinity
(`TauCeti.Vortex.exists_contDiff_gaugeTransform_eq`, the argument of Taubes's uniqueness theorem),
and a `C²` gauge carrying one field of `A_m^k` to another lies in `G_(k+1)`
(`TauCeti.Vortex.mem_sobolevGaugeGroup_of_mem_framedFieldSpace`). Hence two `C²` vortices of
`A_m^k` lie in one `G_(k+1)`-orbit exactly when their divisors agree
(`TauCeti.Vortex.exists_mem_sobolevGaugeGroup_gaugeTransform_eq_iff`), and then the relating
element of `G_(k+1)` is unique, since the action is free. In the bundled action this reads
`TauCeti.Vortex.sobolevVortexDivisor_eq_sobolevVortexDivisor_iff`: the divisor is a complete
invariant of the `G_(k+1)`-orbit. A smooth vortex of `A_m^k` has the divisor of the smooth framed
moduli `TauCeti.Vortex.framedVortexModuliEquiv`
(`TauCeti.Vortex.sobolevVortexDivisor_eq_framedVortexDivisor`).

For `k ≥ 4` the elements of `G_(k+1)` are `C³`, so they preserve the `C²` vortices of `A_m^k`
(`TauCeti.Vortex.smul_mem_sobolevVortices`), which form a sub-action
(`TauCeti.Vortex.sobolevVortexSubMulAction`). The divisor then descends to its orbit space, the
Sobolev moduli of framed vortices, and is injective there
(`TauCeti.Vortex.sobolevVortexModuliDivisor_injective`). For `k ∈ {2, 3}` the `C²` vortices need
not be preserved by `G_(k+1)`, and the classification is the orbit statement above.

That every point of `Sym ℂ m` is the divisor of a vortex of `A_m^k` needs, beyond Taubes's
existence theorem for smooth framed vortices (`TauCeti.Vortex.framedVortexDivisor_surjective`),
a smooth framed gauge moving each smooth framed vortex into `A_m^k`; it is not proved here.

## Main definitions

* `TauCeti.Vortex.sobolevVortices f m k`: the fields of `A_m^k` that are `C²` and solve the vortex
  equations.
* `TauCeti.Vortex.sobolevVortexDivisor`: the zero divisor of such a field, in `Sym ℂ m`.
* `TauCeti.Vortex.sobolevVortexSubMulAction`: for `k ≥ 4`, the same fields as a sub-action of
  `G_(k+1)`.
* `TauCeti.Vortex.sobolevVortexModuliDivisor`: for `k ≥ 4`, the divisor on its orbit space.

## Main results

* `TauCeti.Vortex.exists_mem_sobolevGaugeGroup_gaugeTransform_eq_iff`: two `C²` vortices of
  `A_m^k`, `k ≥ 2`, with zero divisors `D` and `D'` are related by an element of `G_(k+1)` exactly
  when `D = D'`.
* `TauCeti.Vortex.sobolevVortexDivisor_eq_sobolevVortexDivisor_iff`: the same statement for the
  bundled action of `G_(k+1)` on `A_m^k`.
* `TauCeti.Vortex.existsUnique_sobolevGaugeGroup_smul_eq`: two `C²` vortices of `A_m^k` with the
  same divisor are related by exactly one element of `G_(k+1)`.
* `TauCeti.Vortex.sobolevVortexModuliDivisor_injective`: for `k ≥ 4`, the Sobolev moduli of
  framed vortices embed in `Sym ℂ m` by the divisor.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Filter Topology
open scoped ContDiff

variable {f : ContDiffBump (0 : ℝ)} {m : ℕ} {x y : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- **The divisor is a complete invariant of the Sobolev gauge orbit.** Let `x` and `y` be fields
of `A_m^k`, `k ≥ 2`, that are `C²` and solve the vortex equations, with zero divisors `D` and
`D'`. Then `y` is carried to `x` by an element of `G_(k+1)` exactly when `D = D'`. -/
theorem exists_mem_sobolevGaugeGroup_gaugeTransform_eq_iff {k : ℕ} (hk : 1 < k)
    (hx : x ∈ framedFieldSpace f m k) (hy : y ∈ framedFieldSpace f m k)
    (hxc : ContDiff ℝ 2 x) (hyc : ContDiff ℝ 2 y)
    (hxsol : ∀ z, equation x z = 0) (hysol : ∀ z, equation y z = 0) {D D' : Multiset ℂ}
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    (hD' : IsZeroMultiplicity (sectionValue y) fun z ↦ D'.count z) :
    (∃ u ∈ sobolevGaugeGroup (s := k + 1) (by norm_cast; omega), gaugeTransform u y = x) ↔
      D = D' := by
  have hk' : (1 : ℝ) < k := by exact_mod_cast hk
  refine ⟨fun ⟨u, hu, hux⟩ ↦ Multiset.ext.2 fun z ↦ ?_, fun hDD' ↦ ?_⟩
  · -- Continuous gauges do not change the zero multiplicities.
    have h := isZeroMultiplicity_sectionValue_gaugeTransform
      (continuous_subtype_val.comp ((mem_sobolevGaugeGroup _ u).1 hu).1) hD'
    rw [hux] at h
    exact congrFun (hD.unique h) z
  · subst hDD'
    obtain ⟨u, hu, -, hux⟩ := exists_contDiff_gaugeTransform_eq (k := 2) le_rfl hxc hyc hxsol
      hysol (tendsto_const_nhds.congr' ((eventually_norm_inv_phase_eq_one m).mono fun _ h ↦ h.symm))
      (tendsto_sectionValue_mul_inv_pow hk' hx hxc.continuous)
      (tendsto_sectionValue_mul_inv_pow hk' hy hyc.continuous)
      (isZeroMultiplicity_iff.1 hD) (isZeroMultiplicity_iff.1 hD')
    exact ⟨u, mem_sobolevGaugeGroup_of_mem_framedFieldSpace hk hy hu (hux ▸ hx), hux⟩

/-! ### The divisor map on the `C²` vortices of `A_m^k` -/

variable (f m) in
/-- **The `C²` framed vortices of `A_m^k`**: the fields of the affine Sobolev space `A_m^k` that are
`C²` and solve the vortex equations everywhere. -/
def sobolevVortices (k : ℕ) : Set (framedFieldSpace f m k) :=
  {x | ContDiff ℝ 2 (x : ℂ → EuclideanSpace ℝ (Fin 4)) ∧ ∀ z, equation x z = 0}

@[simp]
theorem mem_sobolevVortices {k : ℕ} {x : framedFieldSpace f m k} :
    x ∈ sobolevVortices f m k ↔
      ContDiff ℝ 2 (x : ℂ → EuclideanSpace ℝ (Fin 4)) ∧ ∀ z, equation x z = 0 :=
  Iff.rfl

variable {k : ℕ} [Fact (1 < k)]

/-- The zeros of a `C²` vortex of `A_m^k` form an effective divisor of degree `m`. -/
private theorem exists_sym_isZeroMultiplicity_of_mem_sobolevVortices
    (x : sobolevVortices f m k) :
    ∃ D : Sym ℂ m, IsZeroMultiplicity (sectionValue x) fun z ↦ (D : Multiset ℂ).count z := by
  obtain ⟨hxc, hsol⟩ := x.2
  have hxi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ (x : ℂ → EuclideanSpace ℝ (Fin 4)) w i :=
    (contDiff_piLp 2).1 hxc i
  have hd (i : Fin 4) : Differentiable ℝ fun w ↦ (x : ℂ → EuclideanSpace ℝ (Fin 4)) w i :=
    (hxi i).differentiable two_ne_zero
  exact exists_sym_isZeroMultiplicity_sectionValue (k := 2) (by norm_num) (hxi 0) (hxi 1) (hd 2)
    (hd 3) (fun w ↦ by simp [hsol w])
    (tendsto_sectionValue_mul_inv_pow (by exact_mod_cast (Fact.out : 1 < k)) x.1.2 hxc.continuous)

/-- **The zero divisor of a `C²` vortex of `A_m^k`**, the point of `Sym ℂ m` listing the zeros of
its section with multiplicity. It is characterized by `sobolevVortexDivisor_eq_iff`. -/
def sobolevVortexDivisor (x : sobolevVortices f m k) : Sym ℂ m :=
  (exists_sym_isZeroMultiplicity_of_mem_sobolevVortices x).choose

/-- The section of a `C²` vortex of `A_m^k` vanishes at the points of its divisor, to the order of
their multiplicities. -/
theorem isZeroMultiplicity_sectionValue_sobolevVortexDivisor (x : sobolevVortices f m k) :
    IsZeroMultiplicity (sectionValue x) fun z ↦ (sobolevVortexDivisor x : Multiset ℂ).count z :=
  (exists_sym_isZeroMultiplicity_of_mem_sobolevVortices x).choose_spec

/-- The divisor of a `C²` vortex of `A_m^k` is the unique `D ∈ Sym ℂ m` whose counts are the zero
multiplicities of its section. -/
theorem sobolevVortexDivisor_eq_iff {x : sobolevVortices f m k} {D : Sym ℂ m} :
    sobolevVortexDivisor x = D ↔
      IsZeroMultiplicity (sectionValue x) fun z ↦ (D : Multiset ℂ).count z := by
  refine ⟨fun h ↦ h ▸ isZeroMultiplicity_sectionValue_sobolevVortexDivisor x, fun h ↦ ?_⟩
  exact Sym.coe_injective <| Multiset.ext.2 fun z ↦
    congrFun ((isZeroMultiplicity_sectionValue_sobolevVortexDivisor x).unique h) z

/-- **Taubes's classification on the Sobolev scale.** Two `C²` vortices of `A_m^k` have the same
divisor exactly when they lie in one orbit of the action of `G_(k+1)` on `A_m^k`. -/
theorem sobolevVortexDivisor_eq_sobolevVortexDivisor_iff {hs : 1 < (k : ℝ) + 1}
    {x y : sobolevVortices f m k} :
    sobolevVortexDivisor x = sobolevVortexDivisor y ↔
      ∃ u : sobolevGaugeGroup hs, u • (y : framedFieldSpace f m k) = x := by
  rw [← Sym.coe_inj, ← exists_mem_sobolevGaugeGroup_gaugeTransform_eq_iff Fact.out x.1.2 y.1.2
    x.2.1 y.2.1 x.2.2 y.2.2 (isZeroMultiplicity_sectionValue_sobolevVortexDivisor x)
    (isZeroMultiplicity_sectionValue_sobolevVortexDivisor y)]
  simp only [Subtype.ext_iff, coe_sobolevGaugeGroup_smul, Subtype.exists, exists_prop]

/-- **Uniqueness of the relating gauge.** Two `C²` vortices of `A_m^k` with the same divisor are
related by exactly one element of `G_(k+1)`. -/
theorem existsUnique_sobolevGaugeGroup_smul_eq {hs : 1 < (k : ℝ) + 1}
    {x y : sobolevVortices f m k} (h : sobolevVortexDivisor x = sobolevVortexDivisor y) :
    ∃! u : sobolevGaugeGroup hs, u • (y : framedFieldSpace f m k) = x := by
  obtain ⟨u, hu⟩ := sobolevVortexDivisor_eq_sobolevVortexDivisor_iff.1 h
  exact ⟨u, hu, fun v hv ↦ IsCancelSMul.right_cancel v u _ (hv.trans hu.symm)⟩

/-- A `C²` vortex of `A_m^k` that is smooth has the divisor of the smooth framed vortex moduli. -/
theorem sobolevVortexDivisor_eq_framedVortexDivisor (x : sobolevVortices f m k)
    (x' : framedVortexSubMulAction m) (hx : (x : ℂ → EuclideanSpace ℝ (Fin 4)) = x') :
    sobolevVortexDivisor x = framedVortexDivisor x' := by
  rw [sobolevVortexDivisor_eq_iff, hx]
  exact isZeroMultiplicity_sectionValue_framedVortexDivisor x'

/-! ### The Sobolev moduli of framed vortices -/

/-- **`G_(k+1)` preserves the `C²` vortices of `A_m^k` for `k ≥ 4`**, since its elements are then
`C³` (`contDiff_of_mem_sobolevGaugeGroup`) and the connection loses one derivative of the gauge. -/
theorem smul_mem_sobolevVortices {hs : 1 < (k : ℝ) + 1} (hk : 3 < k) (u : sobolevGaugeGroup hs)
    {x : framedFieldSpace f m k} (hx : x ∈ sobolevVortices f m k) :
    u • x ∈ sobolevVortices f m k := by
  obtain ⟨hxc, hsol⟩ := hx
  have hu : ContDiff ℝ (2 + 1) fun z ↦ ((u : ℂ → Circle) z : ℂ) :=
    contDiff_of_mem_sobolevGaugeGroup (k := 3) (by norm_cast; omega) u.2
  refine ⟨by simpa only [coe_sobolevGaugeGroup_smul] using contDiff_gaugeTransform hu hxc,
    fun z ↦ ?_⟩
  rw [coe_sobolevGaugeGroup_smul, equation_gaugeTransform_eq_zero_iff
    (hu.of_le (by norm_num)).contDiffAt fun i ↦
      (((contDiff_piLp 2).1 hxc i).differentiable two_ne_zero).differentiableAt]
  exact hsol z

/-- For `k ≥ 4`, elements of `G_(k+1)` do not change the divisor. -/
@[simp]
theorem sobolevVortexDivisor_smul {hs : 1 < (k : ℝ) + 1} (hk : 3 < k) (u : sobolevGaugeGroup hs)
    (x : sobolevVortices f m k) :
    sobolevVortexDivisor ⟨u • x.1, smul_mem_sobolevVortices hk u x.2⟩ = sobolevVortexDivisor x :=
  sobolevVortexDivisor_eq_sobolevVortexDivisor_iff.2 ⟨u, rfl⟩

/-- **The `C²` framed vortices of `A_m^k` as a sub-action of `G_(k+1)`**, for `k ≥ 4`. -/
def sobolevVortexSubMulAction {hs : 1 < (k : ℝ) + 1} (hk : 3 < k) :
    SubMulAction (sobolevGaugeGroup hs) (framedFieldSpace f m k) where
  carrier := sobolevVortices f m k
  smul_mem' u _ hx := smul_mem_sobolevVortices hk u hx

@[simp]
theorem mem_sobolevVortexSubMulAction {hs : 1 < (k : ℝ) + 1} {hk : 3 < k}
    {x : framedFieldSpace f m k} :
    x ∈ sobolevVortexSubMulAction (hs := hs) hk ↔ x ∈ sobolevVortices f m k :=
  Iff.rfl

/-- **The divisor on the Sobolev moduli of framed vortices.** For `k ≥ 4` the zero divisor descends
to the `G_(k+1)`-orbits of `C²` vortices of `A_m^k`. -/
def sobolevVortexModuliDivisor {hs : 1 < (k : ℝ) + 1} (hk : 3 < k) :
    MulAction.orbitRel.Quotient (sobolevGaugeGroup hs)
      (sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk) → Sym ℂ m :=
  Quotient.lift (fun x ↦ sobolevVortexDivisor ⟨x.1, mem_sobolevVortexSubMulAction.1 x.2⟩)
    fun x y h ↦ by
      obtain ⟨u, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
      exact sobolevVortexDivisor_smul hk u ⟨y.1, y.2⟩

/-- The class of a `C²` vortex of `A_m^k` goes to its divisor. -/
@[simp]
theorem sobolevVortexModuliDivisor_mk {hs : 1 < (k : ℝ) + 1} {hk : 3 < k}
    (x : sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk) :
    sobolevVortexModuliDivisor hk (Quotient.mk'' x) =
      sobolevVortexDivisor ⟨x.1, mem_sobolevVortexSubMulAction.1 x.2⟩ :=
  (rfl)

/-- **The Sobolev moduli of framed vortices embed in `Sym ℂ m`** (Taubes's uniqueness theorem on
the Sobolev scale): for `k ≥ 4`, two `G_(k+1)`-orbits of `C²` vortices of `A_m^k` with the same
divisor coincide. -/
theorem sobolevVortexModuliDivisor_injective {hs : 1 < (k : ℝ) + 1} (hk : 3 < k) :
    Function.Injective (sobolevVortexModuliDivisor (f := f) (m := m) (hs := hs) hk) :=
  fun a b ↦ Quotient.inductionOn₂ a b fun x y h ↦ Quotient.sound <|
    MulAction.orbitRel_apply.2 <| MulAction.mem_orbit_iff.2 <| by
      obtain ⟨u, hu⟩ := sobolevVortexDivisor_eq_sobolevVortexDivisor_iff.1 h
      exact ⟨u, Subtype.ext hu⟩

end TauCeti.Vortex
