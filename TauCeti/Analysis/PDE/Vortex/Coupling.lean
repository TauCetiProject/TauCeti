/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Dilation
public import TauCeti.Analysis.PDE.Vortex.Existence
public import TauCeti.Analysis.PDE.Vortex.FieldSpace
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Sobolev.BesselPotential.ChangeOfVariables

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
coupling one. This file transports Taubes's classification of framed plane vortices along that
dilation, and shows that dilations act on the affine Sobolev field space `A_m^k`.

* `coupledVortexSubMulAction c m` is the set of smooth framed degree-`m` vortices of coupling
  `c`, preserved by the smooth framed gauge group because the coupled equation is gauge covariant
  (`TauCeti.Vortex.coupledEquation_gaugeTransform_eq_zero_iff`). At `c = 1` it is
  `TauCeti.Vortex.framedVortexSubMulAction m` (`coupledVortexSubMulAction_one`), with the same
  divisor (`coupledVortexDivisor_eq_framedVortexDivisor`).
* For `t > 0` and `t² c = c'`, the dilation is a bijection `coupledVortexDilate` from the
  vortices of coupling `c` to those of coupling `c'`. It intertwines the gauge actions through
  the dilation of framed gauges `dilateGauge`, and divides divisors by `t`
  (`coupledVortexDivisor_coupledVortexDilate`).
* For `c > 0`, two framed vortices of coupling `c` differ by a smooth framed gauge exactly when
  their zero divisors agree (`coupledVortexDivisor_eq_coupledVortexDivisor_iff`), and every
  effective divisor of degree `m` is the zero divisor of one (`coupledVortexDivisor_surjective`).
  Hence the framed gauge orbits of vortices of coupling `c` are in bijection with `Sym ℂ m`
  (`coupledVortexModuliEquiv`).
* Dilations preserve the integer-order Sobolev fields (`dilateField_mem_sobolevFields_natCast`).
  A positive dilation fixes the reference field off a disc, since the winding phase is homogeneous
  of degree `0` and the angular form `dθ` is invariant under dilations, so it maps `A_m^k` to
  itself (`dilateField_mem_framedFieldSpace`).

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

open Complex Filter Topology TemperedDistribution
open scoped ContDiff

namespace TauCeti.Vortex

/-! ### Dilation of framed gauges -/

/-- Pulling a smooth framed gauge back by a nonzero dilation gives a smooth framed gauge. -/
theorem comp_smul_mem_framedGaugeGroup {u : ℂ → Circle} (hu : u ∈ framedGaugeGroup) {t : ℝ}
    (ht : t ≠ 0) : (fun w ↦ u (t • w)) ∈ framedGaugeGroup := by
  obtain ⟨hs, hlim⟩ := (mem_framedGaugeGroup u).1 hu
  exact (mem_framedGaugeGroup _).2 ⟨hs.comp (contDiff_id.const_smul t),
    hlim.comp (Homeomorph.smulOfNeZero t ht).map_cocompact.le⟩

/-- **Dilation of framed gauges**: the automorphism `u ↦ u (t • ·)` of the smooth framed gauge
group, for `t ≠ 0`. -/
def dilateGauge {t : ℝ} (ht : t ≠ 0) : framedGaugeGroup ≃* framedGaugeGroup where
  toFun u := ⟨fun w ↦ u.1 (t • w), comp_smul_mem_framedGaugeGroup u.2 ht⟩
  invFun u := ⟨fun w ↦ u.1 (t⁻¹ • w), comp_smul_mem_framedGaugeGroup u.2 (inv_ne_zero ht)⟩
  left_inv u := by
    ext w
    simp [mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.2 ht)]
  right_inv u := by
    ext w
    simp [inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.2 ht)]
  map_mul' _ _ := rfl

@[simp]
theorem coe_dilateGauge_apply {t : ℝ} (ht : t ≠ 0) (u : framedGaugeGroup) (w : ℂ) :
    (dilateGauge ht u : ℂ → Circle) w = (u : ℂ → Circle) (t • w) :=
  (rfl)

/-- Dilation intertwines the actions of the smooth framed gauge group. -/
theorem dilateField_framedGaugeGroup_smul {t : ℝ} (ht : t ≠ 0) (u : framedGaugeGroup)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    dilateField t (u • x) = dilateGauge ht u • dilateField t x := by
  simp only [framedGaugeGroup_smul]
  exact dilateField_gaugeTransform t u x

/-! ### Framed vortices of a given coupling -/

/-- **Smooth framed vortices of degree `m` and coupling `c`.** The smooth solutions `x` of
`∂bar_a α = 0`, `*iF_a = c (1 - |α|²) / 8` whose section has the degree-`m` end framing
`α(z) (z / |z|)⁻ᵐ → 1`. Smooth framed gauges preserve them. -/
def coupledVortexSubMulAction (c : ℝ) (m : ℕ) :
    SubMulAction framedGaugeGroup (ℂ → EuclideanSpace ℝ (Fin 4)) where
  carrier := {x | ContDiff ℝ ∞ x ∧ (∀ z, coupledEquation c x z = 0) ∧
    Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)}
  smul_mem' u x := by
    rintro ⟨hx, hsol, hfr⟩
    obtain ⟨hu, hu1⟩ := (mem_framedGaugeGroup _).1 u.2
    simp only [Set.mem_ofPred_eq, framedGaugeGroup_smul]
    refine ⟨contDiff_gaugeTransform (by simpa using hu) hx, fun z ↦ ?_,
      tendsto_sectionValue_gaugeTransform hu1 hfr⟩
    rw [coupledEquation_gaugeTransform_eq_zero_iff c (hu.contDiffAt.of_le (by simp)) fun i ↦
      (((contDiff_piLp 2).1 hx i).differentiable (by simp)).differentiableAt]
    exact hsol z

/-- The members of `coupledVortexSubMulAction c m` are the smooth framed degree-`m` vortices of
coupling `c`. -/
@[simp]
theorem mem_coupledVortexSubMulAction {c : ℝ} {m : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)} :
    x ∈ coupledVortexSubMulAction c m ↔ ContDiff ℝ ∞ x ∧ (∀ z, coupledEquation c x z = 0) ∧
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) :=
  Iff.rfl

/-- At coupling one, these are the smooth framed vortices of the normalized equation. -/
theorem coupledVortexSubMulAction_one (m : ℕ) :
    coupledVortexSubMulAction 1 m = framedVortexSubMulAction m := by
  ext x
  simp

variable {c c' t : ℝ} {m : ℕ}

/-- A positive dilation carries the framed vortices of coupling `c` to those of coupling
`t² c`. -/
theorem dilateField_mem_coupledVortexSubMulAction (ht : 0 < t)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ coupledVortexSubMulAction c m) :
    dilateField t x ∈ coupledVortexSubMulAction (t ^ 2 * c) m := by
  obtain ⟨hs, hsol, hfr⟩ := hx
  exact ⟨contDiff_dilateField hs t,
    fun z ↦ (coupledEquation_dilateField_eq_zero_iff c t ht.ne' x z).2 (hsol _),
    tendsto_sectionValue_dilateField hfr ht⟩

/-- A positive dilation preserves and reflects framed vortices, changing the coupling from `c`
to `t² c`. -/
theorem dilateField_mem_coupledVortexSubMulAction_iff (ht : 0 < t)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} :
    dilateField t x ∈ coupledVortexSubMulAction (t ^ 2 * c) m ↔
      x ∈ coupledVortexSubMulAction c m := by
  refine ⟨fun h ↦ ?_, dilateField_mem_coupledVortexSubMulAction ht⟩
  have h' := dilateField_mem_coupledVortexSubMulAction (inv_pos.2 ht) h
  rwa [dilateField_dilateField, inv_mul_cancel₀ ht.ne', dilateField_one, ← mul_assoc,
    ← mul_pow, inv_mul_cancel₀ ht.ne', one_pow, one_mul] at h'

/-- **Dilation between couplings.** For `t > 0` with `t² c = c'`, pulling back by
`z ↦ t • z` is a bijection from the framed degree-`m` vortices of coupling `c` onto those of
coupling `c'`, with inverse the pullback by `z ↦ t⁻¹ • z`. -/
def coupledVortexDilate (ht : 0 < t) (h : t ^ 2 * c = c') (m : ℕ) :
    coupledVortexSubMulAction c m ≃ coupledVortexSubMulAction c' m where
  toFun x := ⟨dilateField t x, h ▸ dilateField_mem_coupledVortexSubMulAction ht x.2⟩
  invFun y := ⟨dilateField t⁻¹ y, by
    have h' : t⁻¹ ^ 2 * c' = c := by
      rw [← h, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ ht.ne', one_pow, one_mul]
    exact h' ▸ dilateField_mem_coupledVortexSubMulAction (inv_pos.2 ht) y.2⟩
  left_inv x := by
    ext1
    simp [inv_mul_cancel₀ ht.ne']
  right_inv y := by
    ext1
    simp [mul_inv_cancel₀ ht.ne']

@[simp]
theorem coe_coupledVortexDilate (ht : 0 < t) (h : t ^ 2 * c = c')
    (x : coupledVortexSubMulAction c m) :
    (coupledVortexDilate ht h m x : ℂ → EuclideanSpace ℝ (Fin 4)) = dilateField t x :=
  (rfl)

@[simp]
theorem coe_coupledVortexDilate_symm (ht : 0 < t) (h : t ^ 2 * c = c')
    (y : coupledVortexSubMulAction c' m) :
    ((coupledVortexDilate ht h m).symm y : ℂ → EuclideanSpace ℝ (Fin 4)) = dilateField t⁻¹ y :=
  (rfl)

/-- The dilation between couplings intertwines the framed gauge actions through
`dilateGauge`. -/
theorem coupledVortexDilate_smul (ht : 0 < t) (h : t ^ 2 * c = c') (u : framedGaugeGroup)
    (x : coupledVortexSubMulAction c m) :
    coupledVortexDilate ht h m (u • x) = dilateGauge ht.ne' u • coupledVortexDilate ht h m x :=
  Subtype.ext (dilateField_framedGaugeGroup_smul ht.ne' u x)

/-! ### The zero divisor -/

/-- The zeros of a smooth framed degree-`m` vortex of any coupling form an effective divisor of
degree `m`; only the holomorphicity rows are used. -/
private theorem exists_sym_isZeroMultiplicity_of_mem_coupledVortexSubMulAction
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ coupledVortexSubMulAction c m) :
    ∃ D : Sym ℂ m, IsZeroMultiplicity (sectionValue x) fun z ↦ (D : Multiset ℂ).count z := by
  obtain ⟨hx, hsol, hfr⟩ := hx
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := (contDiff_piLp 2).1 hx i
  have hd (i : Fin 4) : Differentiable ℝ fun w ↦ x w i := (hxi i).differentiable (by simp)
  refine exists_sym_isZeroMultiplicity_sectionValue (k := ⊤) le_top (hxi 0) (hxi 1) (hd 2) (hd 3)
    (fun w ↦ ⟨?_, ?_⟩) hfr
  · simpa using congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 1) (hsol w)
  · simpa using congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 2) (hsol w)

/-- **The zero divisor of a framed vortex of coupling `c`**, the point of `Sym ℂ m` listing the
zeros of its section with multiplicity. It is characterized by `coupledVortexDivisor_eq_iff`. -/
def coupledVortexDivisor (x : coupledVortexSubMulAction c m) : Sym ℂ m :=
  (exists_sym_isZeroMultiplicity_of_mem_coupledVortexSubMulAction x.2).choose

/-- The section of a framed vortex vanishes at the points of its divisor, to the order of their
multiplicities. -/
theorem isZeroMultiplicity_sectionValue_coupledVortexDivisor (x : coupledVortexSubMulAction c m) :
    IsZeroMultiplicity (sectionValue x) fun z ↦ (coupledVortexDivisor x : Multiset ℂ).count z :=
  (exists_sym_isZeroMultiplicity_of_mem_coupledVortexSubMulAction x.2).choose_spec

/-- **Characterization of the divisor.** The divisor of a framed vortex of coupling `c` is the
unique `D ∈ Sym ℂ m` whose counts are the zero multiplicities of its section. -/
theorem coupledVortexDivisor_eq_iff {x : coupledVortexSubMulAction c m} {D : Sym ℂ m} :
    coupledVortexDivisor x = D ↔
      IsZeroMultiplicity (sectionValue x) fun z ↦ (D : Multiset ℂ).count z := by
  refine ⟨fun h ↦ h ▸ isZeroMultiplicity_sectionValue_coupledVortexDivisor x, fun h ↦ ?_⟩
  exact Sym.coe_injective <| Multiset.ext.2 fun z ↦
    congrFun ((isZeroMultiplicity_sectionValue_coupledVortexDivisor x).unique h) z

/-- Smooth framed gauges do not change the divisor. -/
@[simp]
theorem coupledVortexDivisor_smul (u : framedGaugeGroup) (x : coupledVortexSubMulAction c m) :
    coupledVortexDivisor (u • x) = coupledVortexDivisor x := by
  rw [coupledVortexDivisor_eq_iff, SubMulAction.val_smul]
  exact isZeroMultiplicity_sectionValue_framedGaugeGroup_smul
    (isZeroMultiplicity_sectionValue_coupledVortexDivisor x) u

/-- **Dilation law for the divisor.** The dilation between couplings divides the divisor
by `t`. -/
theorem coupledVortexDivisor_coupledVortexDilate (ht : 0 < t) (h : t ^ 2 * c = c')
    (x : coupledVortexSubMulAction c m) :
    coupledVortexDivisor (coupledVortexDilate ht h m x) =
      (coupledVortexDivisor x).map ((t : ℂ)⁻¹ * ·) := by
  rw [coupledVortexDivisor_eq_iff, Sym.coe_map, coe_coupledVortexDilate]
  exact isZeroMultiplicity_sectionValue_dilateField
    (isZeroMultiplicity_sectionValue_coupledVortexDivisor x) ht.ne'

/-- At coupling one, the divisor is that of `TauCeti.Vortex.framedVortexDivisor`. -/
theorem coupledVortexDivisor_eq_framedVortexDivisor (x : coupledVortexSubMulAction 1 m) :
    coupledVortexDivisor x =
      framedVortexDivisor ⟨x, by rw [← coupledVortexSubMulAction_one]; exact x.2⟩ :=
  coupledVortexDivisor_eq_iff.2 (isZeroMultiplicity_sectionValue_framedVortexDivisor
    ⟨x, by rw [← coupledVortexSubMulAction_one]; exact x.2⟩)

/-- **Uniqueness at every positive coupling.** Two framed degree-`m` vortices of coupling
`c > 0` have the same divisor exactly when they differ by a smooth framed gauge. -/
theorem coupledVortexDivisor_eq_coupledVortexDivisor_iff (hc : 0 < c)
    {x y : coupledVortexSubMulAction c m} :
    coupledVortexDivisor x = coupledVortexDivisor y ↔ ∃ u : framedGaugeGroup, u • y = x := by
  -- Dilate by `c^(-1/2)` to the normalized coupling.
  have ht : 0 < (√c)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hc)
  have h1 : (√c)⁻¹ ^ 2 * c = 1 := by rw [inv_pow, Real.sq_sqrt hc.le, inv_mul_cancel₀ hc.ne']
  set e := coupledVortexDilate ht h1 m
  -- The dilated fields are framed vortices of the normalized equation.
  have hmem (z : coupledVortexSubMulAction c m) : (e z : ℂ → EuclideanSpace ℝ (Fin 4)) ∈
      framedVortexSubMulAction m := coupledVortexSubMulAction_one m ▸ (e z).2
  obtain ⟨hxs, hxsol, hxfr⟩ := mem_framedVortexSubMulAction.1 (hmem x)
  obtain ⟨hys, hysol, hyfr⟩ := mem_framedVortexSubMulAction.1 (hmem y)
  have hphase : Tendsto (fun z : ℂ ↦ ‖((z / (‖z‖ : ℂ)) ^ m)⁻¹‖) (cocompact ℂ) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact] with z hz
    simp [Set.mem_compl_singleton_iff.1 hz]
  have hD (z : coupledVortexSubMulAction c m) := coupledVortexDivisor_coupledVortexDilate ht h1 z
  have hinj : Function.Injective (Sym.map (n := m) ((((√c)⁻¹ : ℝ) : ℂ)⁻¹ * ·)) :=
    Sym.map_injective (mul_right_injective₀ (inv_ne_zero (Complex.ofReal_ne_zero.2 ht.ne'))) m
  rw [← hinj.eq_iff, ← hD, ← hD, ← Sym.coe_inj,
    ← exists_framedGaugeGroup_smul_eq_iff hxs hys hxsol hysol hphase hxfr hyfr
      (isZeroMultiplicity_sectionValue_coupledVortexDivisor (e x))
      (isZeroMultiplicity_sectionValue_coupledVortexDivisor (e y))]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨(dilateGauge ht.ne').symm u, e.injective (Subtype.ext ?_)⟩
    rw [coupledVortexDilate_smul, MulEquiv.apply_symm_apply, SubMulAction.val_smul, hu]
  · rintro ⟨u, rfl⟩
    exact ⟨dilateGauge ht.ne' u, by rw [coupledVortexDilate_smul, SubMulAction.val_smul]⟩

/-- **Existence at every positive coupling.** Every effective divisor of degree `m` is the
divisor of a smooth framed degree-`m` vortex of coupling `c > 0`. -/
theorem coupledVortexDivisor_surjective (hc : 0 < c) (m : ℕ) :
    Function.Surjective (coupledVortexDivisor (c := c) (m := m)) := fun D ↦ by
  -- Dilate a normalized vortex with the divisor `c^(1/2) D` by `c^(1/2)`.
  have ht : 0 < (√c)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hc)
  have h1 : (√c)⁻¹ ^ 2 * c = 1 := by rw [inv_pow, Real.sq_sqrt hc.le, inv_mul_cancel₀ hc.ne']
  set e := coupledVortexDilate ht h1 m
  obtain ⟨y, hy⟩ := framedVortexDivisor_surjective m (D.map ((((√c)⁻¹ : ℝ) : ℂ)⁻¹ * ·))
  let y' : coupledVortexSubMulAction 1 m :=
    ⟨y, by rw [coupledVortexSubMulAction_one]; exact y.2⟩
  refine ⟨e.symm y', Sym.map_injective
    (mul_right_injective₀ (inv_ne_zero (Complex.ofReal_ne_zero.2 ht.ne'))) m ?_⟩
  rw [← coupledVortexDivisor_coupledVortexDilate ht h1, Equiv.apply_symm_apply,
    coupledVortexDivisor_eq_iff, ← hy]
  exact isZeroMultiplicity_sectionValue_framedVortexDivisor y

/-- **The moduli space of framed plane vortices of coupling `c > 0` is `Sym ℂ m`.** The divisor
identifies the orbits of the smooth framed gauge group on the smooth framed degree-`m` vortices of
coupling `c` with the effective divisors of degree `m`. -/
def coupledVortexModuliEquiv (hc : 0 < c) (m : ℕ) :
    MulAction.orbitRel.Quotient framedGaugeGroup (coupledVortexSubMulAction c m) ≃ Sym ℂ m :=
  Equiv.ofBijective
    (Quotient.lift coupledVortexDivisor fun x y h ↦ by
      obtain ⟨u, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
      exact coupledVortexDivisor_smul u y)
    ⟨fun a b ↦ Quotient.inductionOn₂ a b fun x y h ↦ Quotient.sound <|
        MulAction.orbitRel_apply.2 <| MulAction.mem_orbit_iff.2 <|
          (coupledVortexDivisor_eq_coupledVortexDivisor_iff hc).1 h,
      fun D ↦ (coupledVortexDivisor_surjective hc m D).elim fun x hx ↦ ⟨Quotient.mk'' x, hx⟩⟩

/-- The class of a smooth framed vortex of coupling `c` goes to its divisor. -/
@[simp]
theorem coupledVortexModuliEquiv_mk (hc : 0 < c) (x : coupledVortexSubMulAction c m) :
    coupledVortexModuliEquiv hc m (Quotient.mk'' x) = coupledVortexDivisor x :=
  (rfl)

/-! ### Dilations on the affine Sobolev field space -/

/-- Nonzero dilations preserve the integer-order Sobolev fields. -/
theorem dilateField_mem_sobolevFields_natCast (ht : t ≠ 0) {k : ℕ}
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields k) :
    dilateField t y ∈ sobolevFields k := by
  have h (j : Fin 4) : (fun z ↦ y (t • z) j) ∈ realSobolevFunctions ℂ k 2 := by
    simpa using comp_continuousLinearEquiv_mem_realSobolevFunctions_natCast (by norm_num)
      (by norm_num) (LinearEquiv.smulOfNeZero ℝ ℂ t ht).toContinuousLinearEquiv
      (mem_sobolevFields.1 hy j)
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · simpa [dilateField_apply, Pi.smul_def] using Submodule.smul_mem _ t (h 0)
  · simpa [dilateField_apply, Pi.smul_def] using Submodule.smul_mem _ t (h 1)
  · simpa [dilateField_apply] using h 2
  · simpa [dilateField_apply] using h 3

/-- A positive dilation fixes the reference field off a disc: the winding phase is homogeneous of
degree `0` and the angular form `dθ` is invariant. So the two differ by a compactly supported
field. -/
theorem hasCompactSupport_dilateField_referenceField_sub (f : ContDiffBump (0 : ℝ)) (m : ℕ)
    (ht : 0 < t) : HasCompactSupport (dilateField t (referenceField f m) - referenceField f m) := by
  rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact]
  have hr := f.rOut_pos
  have hst := div_nonneg (Real.sqrt_nonneg f.rOut) ht.le
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop
    (√f.rOut + √f.rOut / t + 1)] with z hz
  have hsq {s : ℝ} (hs : √f.rOut ≤ s) : f.rOut ≤ s ^ 2 :=
    (Real.sq_sqrt hr.le).symm.le.trans (pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2)
  have hnorm : ‖(t : ℂ) * z‖ = t * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have h₁ : f.rOut ≤ ‖z‖ ^ 2 := hsq (by linarith [Real.sqrt_nonneg f.rOut])
  have h₂ : f.rOut ≤ ‖(t : ℂ) * z‖ ^ 2 := hsq (by
    rw [hnorm, ← div_le_iff₀' ht]
    linarith [Real.sqrt_nonneg f.rOut])
  have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith [Real.sqrt_nonneg f.rOut])
  have hn : (‖z‖ : ℂ) ≠ 0 := by simpa using hz0
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
  have hphase : (t : ℂ) * z / ((‖(t : ℂ) * z‖ : ℝ) : ℂ) = z / (‖z‖ : ℂ) := by
    rw [hnorm, Complex.ofReal_mul]
    field_simp
  simp only [Pi.sub_apply, Pi.zero_apply, dilateField_apply, Complex.real_smul,
    referenceField_eq_of_rOut_le f m h₁, referenceField_eq_of_rOut_le f m h₂, hphase,
    sub_eq_zero]
  ext i
  fin_cases i <;> simp [abs_of_pos ht] <;> field_simp

/-- **Dilation of the affine field space.** A positive dilation maps `A_m^k` into itself, for
every natural order `k`. -/
theorem dilateField_mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)} {k : ℕ} (ht : 0 < t)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m k) :
    dilateField t x ∈ framedFieldSpace f m k := by
  rw [mem_framedFieldSpace] at hx ⊢
  have href := mem_sobolevFields_of_hasCompactSupport
    (y := dilateField t (referenceField f m) - referenceField f m)
    ((contDiff_dilateField (contDiff_referenceField f m) t).sub (contDiff_referenceField f m))
    (hasCompactSupport_dilateField_referenceField_sub f m ht) k
  have hsplit : dilateField t x - referenceField f m = dilateField t (x - referenceField f m) +
      (dilateField t (referenceField f m) - referenceField f m) := by
    rw [dilateField_sub]
    abel
  rw [hsplit]
  exact add_mem (dilateField_mem_sobolevFields_natCast ht.ne' hx) href

end TauCeti.Vortex
