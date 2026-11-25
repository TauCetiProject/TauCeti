/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Existence

/-!
# Framed plane vortices at every coupling

The plane vortex equations with curvature coefficient `c / 8`,

`∂bar_a α = 0`,  `*iF_a = c (1 - |α|²) / 8`

(`TauCeti.Vortex.coupledEquation c`), arise at `c = 2 r` as the leading equations of the
large-parameter Seiberg–Witten equations on the normal plane of a pseudoholomorphic curve, where
the curvature coefficient is `r / 4`. Pulling a field back by the dilation `z ↦ t • z`
(`TauCeti.Vortex.dilateField`) changes the coupling from `c` to `t² c`
(`TauCeti.Vortex.coupledEquation_dilateField`), so for `c > 0` the dilation by `c^(-1/2)`, the
coordinate change `w = √(2 r) z`, carries vortices of coupling `c` to the normalized vortices of
coupling one. This file proves Taubes's classification of the smooth framed vortices
`TauCeti.Vortex.framedVortexSubMulAction c m` at coupling one and transports it along that
dilation to every positive coupling.

* For `t > 0` and `t² c = c'`, the dilation is a bijection `framedVortexDilate` from the
  vortices of coupling `c` to those of coupling `c'`. It intertwines the gauge actions through
  the dilation of framed gauges `dilateGauge`, and divides divisors by `t`
  (`framedVortexDivisor_framedVortexDilate`). The case `t = c^(-1/2)` is the normalization
  `framedVortexNormalize` to coupling one. Its inverse, the dilation by `c^(1/2)`, carries
  vortices of coupling one to coupling `c` and divides divisors by `c^(1/2)`
  (`framedVortexDivisor_framedVortexNormalize_symm`).
* For `c > 0`, two framed vortices of coupling `c` differ by a smooth framed gauge exactly when
  their zero divisors agree (`framedVortexDivisor_eq_framedVortexDivisor_iff`, Taubes's uniqueness
  theorem at `c = 1`), and every effective divisor of degree `m` is the zero divisor of one
  (`framedVortexDivisor_surjective`, Taubes's existence theorem at `c = 1`). Hence the framed gauge
  orbits of vortices of coupling `c` are in bijection with `Sym ℂ m` (`framedVortexModuliEquiv`).

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

open Complex Filter Topology

namespace TauCeti.Vortex

/-! ### Dilation between couplings -/

variable {c c' t : ℝ} {m : ℕ}

/-- A positive dilation carries the framed vortices of coupling `c` to those of coupling
`t² c`. -/
theorem dilateField_mem_framedVortexSubMulAction (ht : 0 < t)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedVortexSubMulAction c m) :
    dilateField t x ∈ framedVortexSubMulAction (t ^ 2 * c) m := by
  obtain ⟨hs, hsol, hfr⟩ := mem_framedVortexSubMulAction.1 hx
  exact mem_framedVortexSubMulAction.2 ⟨contDiff_dilateField hs t,
    fun z ↦ (coupledEquation_dilateField_apply_eq_zero_iff c t ht.ne' x z).2 (hsol _),
    tendsto_sectionValue_dilateField hfr ht⟩

/-- A positive dilation preserves and reflects framed vortices, changing the coupling from `c`
to `t² c`. -/
theorem dilateField_mem_framedVortexSubMulAction_iff (ht : 0 < t)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} :
    dilateField t x ∈ framedVortexSubMulAction (t ^ 2 * c) m ↔
      x ∈ framedVortexSubMulAction c m := by
  refine ⟨fun h ↦ ?_, dilateField_mem_framedVortexSubMulAction ht⟩
  have hc : t⁻¹ ^ 2 * (t ^ 2 * c) = c := by field_simp
  simpa [hc, ht.ne'] using dilateField_mem_framedVortexSubMulAction (inv_pos.2 ht) h

/-- **Dilation between couplings.** For `t > 0` with `t² c = c'`, pulling back by
`z ↦ t • z` is a bijection from the framed degree-`m` vortices of coupling `c` onto those of
coupling `c'`, with inverse the pullback by `z ↦ t⁻¹ • z`. -/
def framedVortexDilate (ht : 0 < t) (h : t ^ 2 * c = c') (m : ℕ) :
    framedVortexSubMulAction c m ≃ framedVortexSubMulAction c' m where
  toFun x := ⟨dilateField t x, h ▸ dilateField_mem_framedVortexSubMulAction ht x.property⟩
  invFun y := ⟨dilateField t⁻¹ y, by
    convert dilateField_mem_framedVortexSubMulAction (inv_pos.2 ht) y.property using 2
    rw [← h]
    field_simp⟩
  left_inv x := by
    ext1
    simp [inv_mul_cancel₀ ht.ne']
  right_inv y := by
    ext1
    simp [mul_inv_cancel₀ ht.ne']

@[simp]
theorem coe_framedVortexDilate (ht : 0 < t) (h : t ^ 2 * c = c')
    (x : framedVortexSubMulAction c m) :
    (framedVortexDilate ht h m x : ℂ → EuclideanSpace ℝ (Fin 4)) = dilateField t x :=
  (rfl)

@[simp]
theorem coe_framedVortexDilate_symm (ht : 0 < t) (h : t ^ 2 * c = c')
    (y : framedVortexSubMulAction c' m) :
    ((framedVortexDilate ht h m).symm y : ℂ → EuclideanSpace ℝ (Fin 4)) = dilateField t⁻¹ y :=
  (rfl)

/-- The dilation between couplings intertwines the framed gauge actions through
`dilateGauge`. -/
theorem framedVortexDilate_smul (ht : 0 < t) (h : t ^ 2 * c = c') (u : framedGaugeGroup)
    (x : framedVortexSubMulAction c m) :
    framedVortexDilate ht h m (u • x) = dilateGauge ht.ne' u • framedVortexDilate ht h m x :=
  Subtype.ext (dilateField_framedGaugeGroup_smul ht.ne' u x)

/-- **Dilation law for the divisor.** The dilation between couplings divides the divisor
by `t`. -/
@[simp]
theorem framedVortexDivisor_framedVortexDilate (ht : 0 < t) (h : t ^ 2 * c = c')
    (x : framedVortexSubMulAction c m) :
    framedVortexDivisor (framedVortexDilate ht h m x) =
      (framedVortexDivisor x).map ((t : ℂ)⁻¹ * ·) := by
  rw [framedVortexDivisor_eq_iff, Sym.coe_map, coe_framedVortexDilate]
  exact isZeroMultiplicity_sectionValue_dilateField
    (isZeroMultiplicity_sectionValue_framedVortexDivisor x) ht.ne'

/-- The inverse of the dilation between couplings multiplies the divisor by `t`. -/
@[simp]
theorem framedVortexDivisor_framedVortexDilate_symm (ht : 0 < t) (h : t ^ 2 * c = c')
    (y : framedVortexSubMulAction c' m) :
    framedVortexDivisor ((framedVortexDilate ht h m).symm y) =
      (framedVortexDivisor y).map ((t : ℂ) * ·) := by
  rw [framedVortexDivisor_eq_iff, Sym.coe_map, coe_framedVortexDilate_symm]
  simpa using isZeroMultiplicity_sectionValue_dilateField
    (isZeroMultiplicity_sectionValue_framedVortexDivisor y) (inv_ne_zero ht.ne')

/-! ### Normalization to coupling one -/

/-- **Normalization to coupling one.** For `c > 0`, the dilation by `c^(-1/2)` identifies the
framed degree-`m` vortices of coupling `c` with those of coupling one. -/
def framedVortexNormalize (hc : 0 < c) (m : ℕ) :
    framedVortexSubMulAction c m ≃ framedVortexSubMulAction 1 m :=
  framedVortexDilate (inv_pos.2 (Real.sqrt_pos.2 hc))
    (by rw [inv_pow, Real.sq_sqrt hc.le, inv_mul_cancel₀ hc.ne']) m

@[simp]
theorem coe_framedVortexNormalize (hc : 0 < c) (x : framedVortexSubMulAction c m) :
    (framedVortexNormalize hc m x : ℂ → EuclideanSpace ℝ (Fin 4)) = dilateField (√c)⁻¹ x :=
  (rfl)

@[simp]
theorem coe_framedVortexNormalize_symm (hc : 0 < c) (y : framedVortexSubMulAction 1 m) :
    ((framedVortexNormalize hc m).symm y : ℂ → EuclideanSpace ℝ (Fin 4)) = dilateField √c y := by
  rw [framedVortexNormalize, coe_framedVortexDilate_symm, inv_inv]

/-- The normalization intertwines the framed gauge actions through `dilateGauge`. -/
theorem framedVortexNormalize_smul (hc : 0 < c) (u : framedGaugeGroup)
    (x : framedVortexSubMulAction c m) :
    framedVortexNormalize hc m (u • x) =
      dilateGauge (inv_ne_zero (Real.sqrt_pos.2 hc).ne') u • framedVortexNormalize hc m x :=
  framedVortexDilate_smul _ _ u x

/-- The normalization to coupling one multiplies the divisor by `c^(1/2)`. -/
@[simp]
theorem framedVortexDivisor_framedVortexNormalize (hc : 0 < c)
    (x : framedVortexSubMulAction c m) :
    framedVortexDivisor (framedVortexNormalize hc m x) =
      (framedVortexDivisor x).map ((√c : ℂ) * ·) := by
  rw [framedVortexNormalize, framedVortexDivisor_framedVortexDilate, Complex.ofReal_inv, inv_inv]

/-- The inverse of the normalization to coupling one divides the divisor by `c^(1/2)`. -/
@[simp]
theorem framedVortexDivisor_framedVortexNormalize_symm (hc : 0 < c)
    (y : framedVortexSubMulAction 1 m) :
    framedVortexDivisor ((framedVortexNormalize hc m).symm y) =
      (framedVortexDivisor y).map ((√c : ℂ)⁻¹ * ·) := by
  rw [framedVortexNormalize, framedVortexDivisor_framedVortexDilate_symm, Complex.ofReal_inv]

/-- Multiplication of divisors by `c^(1/2)`, `c > 0`, is injective. -/
private theorem sym_map_sqrt_mul_injective (hc : 0 < c) :
    Function.Injective (Sym.map (n := m) ((√c : ℂ) * ·)) :=
  Sym.map_injective (mul_right_injective₀ (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hc).ne')) m

/-! ### The moduli of framed vortices -/

/-- Taubes's uniqueness theorem at coupling one, the normalized vortex equation. -/
private theorem framedVortexDivisor_eq_framedVortexDivisor_iff_of_one
    {x y : framedVortexSubMulAction 1 m} :
    framedVortexDivisor x = framedVortexDivisor y ↔ ∃ u : framedGaugeGroup, u • y = x := by
  obtain ⟨hx, hxsol, hxfr⟩ := mem_framedVortexSubMulAction.1 x.property
  obtain ⟨hy, hysol, hyfr⟩ := mem_framedVortexSubMulAction.1 y.property
  simp only [coupledEquation_one] at hxsol hysol
  rw [← Sym.coe_inj, ← exists_framedGaugeGroup_smul_eq_iff hx hy hxsol hysol
    (tendsto_norm_inv_phase m) hxfr hyfr (isZeroMultiplicity_sectionValue_framedVortexDivisor x)
    (isZeroMultiplicity_sectionValue_framedVortexDivisor y)]
  simp only [Subtype.ext_iff, SubMulAction.val_smul]

/-- **Taubes's uniqueness theorem, at every positive coupling.** Two smooth framed degree-`m`
vortices of coupling `c > 0` have the same divisor exactly when they differ by a smooth framed
gauge. -/
theorem framedVortexDivisor_eq_framedVortexDivisor_iff (hc : 0 < c)
    {x y : framedVortexSubMulAction c m} :
    framedVortexDivisor x = framedVortexDivisor y ↔ ∃ u : framedGaugeGroup, u • y = x := by
  rw [← (sym_map_sqrt_mul_injective hc).eq_iff, ← framedVortexDivisor_framedVortexNormalize hc,
    ← framedVortexDivisor_framedVortexNormalize hc,
    framedVortexDivisor_eq_framedVortexDivisor_iff_of_one]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨(dilateGauge (inv_ne_zero (Real.sqrt_pos.2 hc).ne')).symm u,
      (framedVortexNormalize hc m).injective ?_⟩
    rw [framedVortexNormalize_smul, MulEquiv.apply_symm_apply, hu]
  · rintro ⟨u, rfl⟩
    exact ⟨_, (framedVortexNormalize_smul hc u y).symm⟩

/-- **Taubes's existence theorem, at every positive coupling.** Every effective divisor of degree
`m` is the divisor of a smooth framed degree-`m` vortex of coupling `c > 0`. -/
theorem framedVortexDivisor_surjective (hc : 0 < c) (m : ℕ) :
    Function.Surjective (framedVortexDivisor (c := c) (m := m)) := fun D ↦ by
  obtain ⟨x, hx, hsol, hfr, hD⟩ :=
    exists_contDiff_equation_eq_zero_isZeroMultiplicity (D.map ((√c : ℂ) * ·))
  refine ⟨(framedVortexNormalize hc m).symm
    ⟨x, mem_framedVortexSubMulAction.2 ⟨hx, by simpa using hsol, hfr⟩⟩,
    sym_map_sqrt_mul_injective hc ?_⟩
  rw [← framedVortexDivisor_framedVortexNormalize hc, Equiv.apply_symm_apply,
    framedVortexDivisor_eq_iff]
  exact hD

/-- **The moduli space of framed plane vortices of coupling `c > 0` is `Sym ℂ m`** (Taubes). The
divisor identifies the orbits of the smooth framed gauge group on the smooth framed degree-`m`
vortices of coupling `c` with the effective divisors of degree `m`. -/
def framedVortexModuliEquiv (hc : 0 < c) (m : ℕ) :
    MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction c m) ≃ Sym ℂ m :=
  Equiv.ofBijective
    (Quotient.lift framedVortexDivisor fun x y h ↦ by
      obtain ⟨u, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
      exact framedVortexDivisor_smul u y)
    ⟨fun a b ↦ Quotient.inductionOn₂ a b fun x y h ↦ Quotient.sound <|
        MulAction.orbitRel_apply.2 <| MulAction.mem_orbit_iff.2 <|
          (framedVortexDivisor_eq_framedVortexDivisor_iff hc).1 h,
      fun D ↦ (framedVortexDivisor_surjective hc m D).elim fun x hx ↦ ⟨Quotient.mk'' x, hx⟩⟩

/-- The class of a smooth framed vortex goes to its divisor. -/
@[simp]
theorem framedVortexModuliEquiv_mk (hc : 0 < c) (x : framedVortexSubMulAction c m) :
    framedVortexModuliEquiv hc m (Quotient.mk'' x) = framedVortexDivisor x :=
  (rfl)

end TauCeti.Vortex
