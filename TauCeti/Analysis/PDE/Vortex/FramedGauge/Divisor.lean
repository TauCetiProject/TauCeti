/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Existence
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Regularity
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Representative
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# The divisor classifies the Sobolev gauge orbits of framed plane vortices

Framed degree-`m` plane vortex fields form the affine Sobolev space `A_m^k`
(`TauCeti.Vortex.framedFieldSpace`), on which the Sobolev gauge group `G_(k+1)`
(`TauCeti.Vortex.sobolevGaugeGroup`) acts by `(a, α) ↦ (a - u⁻¹ du, u α)`. This file proves
Taubes's classification of the vortices of `A_m^k` modulo `G_(k+1)` by their zeros, for every
integer `k ≥ 2`, on the vortices that are `C²` as fields, compares smooth and Sobolev framed gauge
orbits, and identifies the Sobolev framed vortex moduli space with `Sym ℂ m`.

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
(`TauCeti.Vortex.sobolevVortexDivisor_eq_framedVortexDivisor`), and two smooth vortices of `A_m^k`
are related by a smooth framed gauge if and only if they are related by an element of `G_(k+1)`
(`TauCeti.Vortex.exists_framedGaugeGroup_smul_eq_iff_exists_sobolevGaugeGroup_smul_eq`).

Combining Taubes's existence theorem for smooth framed vortices
(`TauCeti.Vortex.exists_contDiff_equation_eq_zero_isZeroMultiplicity`) with the end-phase
normalization
`TauCeti.Vortex.exists_framedGaugeGroup_norm_iteratedFDeriv_smul_sub_referenceField_le_mul_exp`
shows that every `D ∈ Sym ℂ m` is the zero divisor of a smooth vortex lying in `A_m^s` for every
cutoff `f` and real order `s`, with exponential decay of all iterated derivatives
(`TauCeti.Vortex.exists_contDiff_mem_framedFieldSpace_equation_eq_zero_isZeroMultiplicity`). Thus
`TauCeti.Vortex.sobolevVortexDivisor` is surjective for every `k ≥ 2`
(`TauCeti.Vortex.sobolevVortexDivisor_surjective`), and every `G_(k+1)`-orbit of `C²` vortices of
`A_m^k` contains a smooth representative in `⋂_s A_m^s`
(`TauCeti.Vortex.exists_contDiff_sobolevGaugeGroup_smul_eq`).

For `k ≥ 4` the elements of `G_(k+1)` are `C³`, so they preserve the `C²` vortices of `A_m^k`
(`TauCeti.Vortex.smul_mem_sobolevVortices`), which form a sub-action
(`TauCeti.Vortex.sobolevVortexSubMulAction`). The divisor descends to its orbit space, the Sobolev
moduli of framed vortices, and defines a bijection onto `Sym ℂ m`
(`TauCeti.Vortex.sobolevVortexModuliEquiv`), canonically identifying the Sobolev moduli space with
the smooth framed vortex moduli space (`TauCeti.Vortex.sobolevVortexModuliEquivFramedVortexModuli`).

## Main definitions

* `TauCeti.Vortex.sobolevVortices f m k`: the fields of `A_m^k` that are `C²` and solve the vortex
  equations.
* `TauCeti.Vortex.sobolevVortexDivisor`: the zero divisor of such a field, in `Sym ℂ m`.
* `TauCeti.Vortex.sobolevVortexSubMulAction`: for `k ≥ 4`, the same fields as a sub-action of
  `G_(k+1)`.
* `TauCeti.Vortex.sobolevVortexModuliDivisor`: for `k ≥ 4`, the divisor on its orbit space.
* `TauCeti.Vortex.sobolevVortexModuliEquiv`: for `k ≥ 4`, the equivalence between the Sobolev
  framed vortex moduli space and `Sym ℂ m`.
* `TauCeti.Vortex.sobolevVortexModuliEquivFramedVortexModuli`: for `k ≥ 4`, the canonical
  equivalence between the Sobolev and smooth framed vortex moduli spaces.

## Main results

* `TauCeti.Vortex.exists_mem_sobolevGaugeGroup_gaugeTransform_eq_iff`: two `C²` vortices of
  `A_m^k`, `k ≥ 2`, with zero divisors `D` and `D'` are related by an element of `G_(k+1)` exactly
  when `D = D'`.
* `TauCeti.Vortex.exists_contDiff_mem_framedFieldSpace_equation_eq_zero_isZeroMultiplicity`: every
  `D ∈ Sym ℂ m` is the zero divisor of a smooth vortex in `⋂_s A_m^s` with all-order exponential
  derivative decay toward `referenceField f m`.
* `TauCeti.Vortex.sobolevVortexDivisor_eq_sobolevVortexDivisor_iff`: the orbit classification for
  the bundled action of `G_(k+1)` on `A_m^k`.
* `TauCeti.Vortex.existsUnique_sobolevGaugeGroup_smul_eq`: two `C²` vortices of `A_m^k` with the
  same divisor are related by exactly one element of `G_(k+1)`.
* `TauCeti.Vortex.exists_framedGaugeGroup_smul_eq_iff_exists_sobolevGaugeGroup_smul_eq`: two smooth
  vortices of `A_m^k`, `k ≥ 2`, differ by a smooth framed gauge if and only if they differ by an
  element of `G_(k+1)`.
* `TauCeti.Vortex.sobolevVortexDivisor_surjective`: for `k ≥ 2`, every point of `Sym ℂ m` is the
  divisor of a `C²` vortex of `A_m^k`.
* `TauCeti.Vortex.exists_contDiff_sobolevGaugeGroup_smul_eq`: every `C²` vortex of `A_m^k`, `k ≥ 2`,
  lies in the `G_(k+1)`-orbit of a smooth vortex belonging to `A_m^s` for all `s`.
* `TauCeti.Vortex.sobolevVortexModuliDivisor_bijective`: for `k ≥ 4`, the Sobolev moduli of framed
  vortices are in bijection with `Sym ℂ m` via the zero divisor.

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

/-- **Existence of smooth Sobolev framed vortices with prescribed zeros.** Every effective divisor
`D ∈ Sym ℂ m` is the zero divisor of a smooth plane vortex `x` whose section equals `|α|` times
`windingPhase m` outside a compact set, whose difference from `referenceField f m` has exponential
decay of all iterated derivatives at every rate `c < 1 / 2`, and which belongs to
`framedFieldSpace f m s` for every cutoff `f` and real order `s`. -/
theorem exists_contDiff_mem_framedFieldSpace_equation_eq_zero_isZeroMultiplicity (D : Sym ℂ m) :
    ∃ x : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ x ∧ (∀ z, equation x z = 0) ∧
      (∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z) ∧
      (∀ (f : ContDiffBump (0 : ℝ)) (s : ℝ), x ∈ framedFieldSpace f m s) ∧
      (∀ (f : ContDiffBump (0 : ℝ)), ∀ c < 1 / 2, ∀ n : ℕ, ∃ K, ∀ z,
        ‖iteratedFDeriv ℝ n (x - referenceField f m) z‖ ≤ K * Real.exp (-(c * ‖z‖))) ∧
      IsZeroMultiplicity (sectionValue x) fun z ↦ (D : Multiset ℂ).count z := by
  obtain ⟨y, hy, hsol, hfr, hD⟩ := exists_contDiff_equation_eq_zero_isZeroMultiplicity D
  obtain ⟨u, hphase, hdecay⟩ :=
    exists_framedGaugeGroup_norm_iteratedFDeriv_smul_sub_referenceField_le_mul_exp hy hsol hfr
  have huy : u • y ∈ framedVortexSubMulAction m :=
    (framedVortexSubMulAction m).smul_mem u (mem_framedVortexSubMulAction.2 ⟨hy, hsol, hfr⟩)
  obtain ⟨hux_cd, hux_sol, hux_fr⟩ := mem_framedVortexSubMulAction.1 huy
  have hlim := tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hux_fr
  exact ⟨u • y, hux_cd, hux_sol, hphase,
    fun f s ↦ mem_framedFieldSpace_of_sectionValue_eq_mul_windingPhase hux_cd hux_sol hlim
      hphase f s,
    hdecay, isZeroMultiplicity_sectionValue_framedGaugeGroup_smul hD u⟩

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

/-- A smooth vortex of `A_m^k`, `k ≥ 2`, belongs to `framedVortexSubMulAction m`. -/
theorem mem_framedVortexSubMulAction_of_mem_sobolevVortices (x : sobolevVortices f m k)
    (hx : ContDiff ℝ ∞ (x : ℂ → EuclideanSpace ℝ (Fin 4))) :
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ framedVortexSubMulAction m :=
  mem_framedVortexSubMulAction.2 ⟨hx, x.2.2,
    tendsto_sectionValue_mul_inv_pow (by exact_mod_cast (Fact.out : 1 < k)) x.1.2 hx.continuous⟩

/-- A smooth framed gauge carrying one field of `A_m^k`, `k ≥ 2`, to another belongs to the
Sobolev gauge group `G_(k+1)`. -/
theorem coe_mem_sobolevGaugeGroup_of_smul_eq {hs : 1 < (k : ℝ) + 1}
    {x y : framedFieldSpace f m k} {u : framedGaugeGroup}
    (hu : u • (y : ℂ → EuclideanSpace ℝ (Fin 4)) = x) :
    (u : ℂ → Circle) ∈ sobolevGaugeGroup hs := by
  have huc : ContDiff ℝ 2 fun z ↦ ((u : ℂ → Circle) z : ℂ) :=
    (((mem_framedGaugeGroup _).1 u.2).1).of_le (by simp)
  exact mem_sobolevGaugeGroup_of_mem_framedFieldSpace Fact.out y.2 huc
    (by rw [← framedGaugeGroup_smul, hu]; exact x.2)

/-- Two fields of `A_m^k`, `k ≥ 2`, related by a smooth framed gauge lie in the same
`G_(k+1)`-orbit, even though an arbitrary smooth framed gauge need not belong to `G_(k+1)`. -/
theorem exists_sobolevGaugeGroup_smul_eq_of_framedGaugeGroup_smul_eq {hs : 1 < (k : ℝ) + 1}
    {x y : framedFieldSpace f m k}
    (h : ∃ u : framedGaugeGroup, u • (y : ℂ → EuclideanSpace ℝ (Fin 4)) = x) :
    ∃ u : sobolevGaugeGroup hs, u • y = x := by
  obtain ⟨u, hu⟩ := h
  exact ⟨⟨u, coe_mem_sobolevGaugeGroup_of_smul_eq hu⟩,
    Subtype.ext (by rw [coe_sobolevGaugeGroup_smul, ← framedGaugeGroup_smul]; exact hu)⟩

/-- A Sobolev gauge in `G_(k+1)`, `k ≥ 2`, carrying one smooth vortex of `A_m^k` to another is
automatically a smooth framed gauge (`∈ framedGaugeGroup`). -/
theorem coe_mem_framedGaugeGroup_of_smul_eq {hs : 1 < (k : ℝ) + 1}
    {x y : sobolevVortices f m k}
    (hx : ContDiff ℝ ∞ (x : ℂ → EuclideanSpace ℝ (Fin 4)))
    (hy : ContDiff ℝ ∞ (y : ℂ → EuclideanSpace ℝ (Fin 4)))
    {u : sobolevGaugeGroup hs} (hu : u • (y : framedFieldSpace f m k) = x) :
    (u : ℂ → Circle) ∈ framedGaugeGroup := by
  let x' : framedVortexSubMulAction m :=
    ⟨x, mem_framedVortexSubMulAction_of_mem_sobolevVortices x hx⟩
  let y' : framedVortexSubMulAction m :=
    ⟨y, mem_framedVortexSubMulAction_of_mem_sobolevVortices y hy⟩
  have hdiv : framedVortexDivisor x' = framedVortexDivisor y' := by
    rw [← sobolevVortexDivisor_eq_framedVortexDivisor x x' rfl,
      ← sobolevVortexDivisor_eq_framedVortexDivisor y y' rfl]
    exact sobolevVortexDivisor_eq_sobolevVortexDivisor_iff.2 ⟨u, hu⟩
  obtain ⟨v, hv⟩ := framedVortexDivisor_eq_framedVortexDivisor_iff.1 hdiv
  have hv_val : v • (y : ℂ → EuclideanSpace ℝ (Fin 4)) = x := congrArg Subtype.val hv
  let v' : sobolevGaugeGroup hs := ⟨v, coe_mem_sobolevGaugeGroup_of_smul_eq hv_val⟩
  have hv'_smul : v' • (y : framedFieldSpace f m k) = x :=
    Subtype.ext (by rw [coe_sobolevGaugeGroup_smul, ← framedGaugeGroup_smul]; exact hv_val)
  have huv : u = v' :=
    IsCancelSMul.right_cancel u v' (y : framedFieldSpace f m k) (hu.trans hv'_smul.symm)
  rw [congrArg Subtype.val huv]
  exact v.2

/-- **Smooth vs. Sobolev gauge equivalence on `A_m^k`.** Two smooth vortices of `A_m^k`, `k ≥ 2`,
are related by a smooth framed gauge if and only if they are related by an element of `G_(k+1)`. -/
theorem exists_framedGaugeGroup_smul_eq_iff_exists_sobolevGaugeGroup_smul_eq
    {hs : 1 < (k : ℝ) + 1} {x y : sobolevVortices f m k}
    (hx : ContDiff ℝ ∞ (x : ℂ → EuclideanSpace ℝ (Fin 4)))
    (hy : ContDiff ℝ ∞ (y : ℂ → EuclideanSpace ℝ (Fin 4))) :
    (∃ u : framedGaugeGroup, u • (y : ℂ → EuclideanSpace ℝ (Fin 4)) = x) ↔
      ∃ u : sobolevGaugeGroup hs, u • (y : framedFieldSpace f m k) = x := by
  refine ⟨exists_sobolevGaugeGroup_smul_eq_of_framedGaugeGroup_smul_eq,
    fun ⟨u, hu⟩ ↦ ⟨⟨u, coe_mem_framedGaugeGroup_of_smul_eq hx hy hu⟩, ?_⟩⟩
  simpa only [framedGaugeGroup_smul, ← coe_sobolevGaugeGroup_smul] using congrArg Subtype.val hu

/-- **Taubes's existence theorem on the Sobolev scale.** For every integer `k ≥ 2`, every effective
divisor of degree `m` is the divisor of a `C²` (indeed smooth) vortex of `A_m^k`. -/
theorem sobolevVortexDivisor_surjective :
    Function.Surjective (sobolevVortexDivisor (f := f) (m := m) (k := k)) := fun D ↦ by
  obtain ⟨x, hx, hsol, -, hmem, -, hD⟩ :=
    exists_contDiff_mem_framedFieldSpace_equation_eq_zero_isZeroMultiplicity D
  exact ⟨⟨⟨x, hmem f k⟩, hx.of_le (by simp), hsol⟩, sobolevVortexDivisor_eq_iff.2 hD⟩

/-- **Smooth representative in every Sobolev vortex orbit.** Every `C²` vortex `x` of `A_m^k`,
`k ≥ 2`, is carried by a unique element of `G_(k+1)` from a smooth vortex `y` of `A_m^k` whose
field belongs to `framedFieldSpace f m s` for every real `s`. -/
theorem exists_contDiff_sobolevGaugeGroup_smul_eq {hs : 1 < (k : ℝ) + 1}
    (x : sobolevVortices f m k) :
    ∃ y : sobolevVortices f m k, ContDiff ℝ ∞ (y : ℂ → EuclideanSpace ℝ (Fin 4)) ∧
      (∀ s : ℝ, (y : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ framedFieldSpace f m s) ∧
      ∃! u : sobolevGaugeGroup hs, u • (y : framedFieldSpace f m k) = x := by
  obtain ⟨y, hy, hsol, -, hmem, -, hD⟩ :=
    exists_contDiff_mem_framedFieldSpace_equation_eq_zero_isZeroMultiplicity
      (sobolevVortexDivisor x)
  let y' : sobolevVortices f m k := ⟨⟨y, hmem f k⟩, hy.of_le (by simp), hsol⟩
  have hdiv : sobolevVortexDivisor x = sobolevVortexDivisor y' :=
    (sobolevVortexDivisor_eq_iff.2 hD).symm
  exact ⟨y', hy, hmem f, existsUnique_sobolevGaugeGroup_smul_eq hdiv⟩

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

/-- **Surjectivity of the divisor on the Sobolev moduli of framed vortices.** For `k ≥ 4`, every
effective divisor of degree `m` is the divisor of a `G_(k+1)`-orbit of `C²` vortices of `A_m^k`. -/
theorem sobolevVortexModuliDivisor_surjective {hs : 1 < (k : ℝ) + 1} (hk : 3 < k) :
    Function.Surjective (sobolevVortexModuliDivisor (f := f) (m := m) (hs := hs) hk) := fun D ↦ by
  obtain ⟨x, hx⟩ := sobolevVortexDivisor_surjective (f := f) (m := m) (k := k) D
  exact ⟨Quotient.mk'' ⟨x.1, x.2⟩, hx⟩

/-- For `k ≥ 4`, the divisor map on the Sobolev moduli of framed vortices is a bijection onto
`Sym ℂ m`. -/
theorem sobolevVortexModuliDivisor_bijective {hs : 1 < (k : ℝ) + 1} (hk : 3 < k) :
    Function.Bijective (sobolevVortexModuliDivisor (f := f) (m := m) (hs := hs) hk) :=
  ⟨sobolevVortexModuliDivisor_injective hk, sobolevVortexModuliDivisor_surjective hk⟩

/-- **The Sobolev moduli space of framed plane vortices is `Sym ℂ m`.** For `k ≥ 4`, the zero
divisor identifies the `G_(k+1)`-orbits of `C²` vortices of `A_m^k` with the effective divisors of
degree `m`. -/
def sobolevVortexModuliEquiv {hs : 1 < (k : ℝ) + 1} (hk : 3 < k) :
    MulAction.orbitRel.Quotient (sobolevGaugeGroup hs)
      (sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk) ≃ Sym ℂ m :=
  Equiv.ofBijective (sobolevVortexModuliDivisor hk) (sobolevVortexModuliDivisor_bijective hk)

@[simp]
theorem coe_sobolevVortexModuliEquiv {hs : 1 < (k : ℝ) + 1} (hk : 3 < k) :
    ⇑(sobolevVortexModuliEquiv (f := f) (m := m) (hs := hs) hk) = sobolevVortexModuliDivisor hk :=
  (rfl)

theorem sobolevVortexModuliEquiv_mk {hs : 1 < (k : ℝ) + 1} {hk : 3 < k}
    (x : sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk) :
    sobolevVortexModuliEquiv hk (Quotient.mk'' x) =
      sobolevVortexDivisor ⟨x.1, mem_sobolevVortexSubMulAction.1 x.2⟩ :=
  (rfl)

@[simp]
theorem sobolevVortexModuliDivisor_sobolevVortexModuliEquiv_symm {hs : 1 < (k : ℝ) + 1}
    (hk : 3 < k) (D : Sym ℂ m) :
    sobolevVortexModuliDivisor hk
      ((sobolevVortexModuliEquiv (f := f) (m := m) (hs := hs) hk).symm D) = D :=
  (sobolevVortexModuliEquiv hk).apply_symm_apply D

@[simp]
theorem sobolevVortexModuliEquiv_symm_sobolevVortexModuliDivisor {hs : 1 < (k : ℝ) + 1}
    (hk : 3 < k)
    (q : MulAction.orbitRel.Quotient (sobolevGaugeGroup hs)
      (sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk)) :
    (sobolevVortexModuliEquiv (f := f) (m := m) (hs := hs) hk).symm
      (sobolevVortexModuliDivisor hk q) = q :=
  (sobolevVortexModuliEquiv hk).symm_apply_apply q

/-- **Equivalence between the Sobolev and smooth framed vortex moduli spaces.** For `k ≥ 4`, the
orbit space of `G_(k+1)` on the `C²` vortices of `A_m^k` is canonically equivalent to the orbit
space of `framedGaugeGroup` on the smooth framed degree-`m` vortices, identifying orbits with the
same zero divisor. -/
def sobolevVortexModuliEquivFramedVortexModuli {hs : 1 < (k : ℝ) + 1} (hk : 3 < k) :
    MulAction.orbitRel.Quotient (sobolevGaugeGroup hs)
      (sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk) ≃
      MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction m) :=
  (sobolevVortexModuliEquiv hk).trans (framedVortexModuliEquiv m).symm

@[simp]
theorem framedVortexModuliEquiv_sobolevVortexModuliEquivFramedVortexModuli {hs : 1 < (k : ℝ) + 1}
    (hk : 3 < k)
    (q : MulAction.orbitRel.Quotient (sobolevGaugeGroup hs)
      (sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk)) :
    framedVortexModuliEquiv m (sobolevVortexModuliEquivFramedVortexModuli hk q) =
      sobolevVortexModuliDivisor hk q := by
  simp [sobolevVortexModuliEquivFramedVortexModuli]

@[simp]
theorem sobolevVortexModuliDivisor_sobolevVortexModuliEquivFramedVortexModuli_symm
    {hs : 1 < (k : ℝ) + 1} (hk : 3 < k)
    (q : MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction m)) :
    sobolevVortexModuliDivisor hk
      ((sobolevVortexModuliEquivFramedVortexModuli (f := f) (hs := hs) hk).symm q) =
      framedVortexModuliEquiv m q := by
  simp [sobolevVortexModuliEquivFramedVortexModuli]

/-- On the `G_(k+1)`-orbit of any smooth vortex in `A_m^k`,
`sobolevVortexModuliEquivFramedVortexModuli` agrees with taking its `framedGaugeGroup`-orbit. -/
theorem sobolevVortexModuliEquivFramedVortexModuli_mk_of_eq {hs : 1 < (k : ℝ) + 1} {hk : 3 < k}
    (x : sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk)
    (x' : framedVortexSubMulAction m) (hx : (x : ℂ → EuclideanSpace ℝ (Fin 4)) = x') :
    sobolevVortexModuliEquivFramedVortexModuli hk (Quotient.mk'' x) = Quotient.mk'' x' := by
  apply (framedVortexModuliEquiv m).injective
  simp [sobolevVortexDivisor_eq_framedVortexDivisor ⟨x.1, x.2⟩ x' hx]

/-- On the `framedGaugeGroup`-orbit of any smooth vortex lying in `A_m^k`, the inverse of
`sobolevVortexModuliEquivFramedVortexModuli` agrees with taking its `G_(k+1)`-orbit. -/
theorem sobolevVortexModuliEquivFramedVortexModuli_symm_mk_of_eq {hs : 1 < (k : ℝ) + 1} {hk : 3 < k}
    (x : sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk)
    (x' : framedVortexSubMulAction m) (hx : (x : ℂ → EuclideanSpace ℝ (Fin 4)) = x') :
    (sobolevVortexModuliEquivFramedVortexModuli hk).symm (Quotient.mk'' x') = Quotient.mk'' x :=
  (sobolevVortexModuliEquivFramedVortexModuli hk).symm_apply_eq.2
    (sobolevVortexModuliEquivFramedVortexModuli_mk_of_eq x x' hx).symm

end TauCeti.Vortex
