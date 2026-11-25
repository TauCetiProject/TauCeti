/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.EquationMap
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.FieldTopology
public import TauCeti.Analysis.PDE.Vortex.Gauge.Sobolev
public import TauCeti.Analysis.Sobolev.BesselPotential.Real
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# The real chart of the framed vortex fields and the real vortex equation map

The continuous framed degree-`m` plane vortex fields of `A_m^s = x_m + H^s(ℂ; ℝ⁴)` form the
topological space `TauCeti.Vortex.SobolevFieldSpace f m s`, topologized by the four coordinates
of `x - x_m` in the complex Bessel-potential space `H^s(ℂ)`
(`TauCeti.Vortex.SobolevFieldSpace.subRef`). These coordinates are complexifications of real
functions, so they lie in the closed real subspace `BesselPotentialSpace.realSubmodule ℂ h` of
real elements of `H^s(ℂ)`, a real Hilbert space. This file shows that, for `s > 1`, the real
coordinates identify the field space with the real Hilbert space `(H^s_ℝ)⁴`, and that in these
coordinates the vortex equation is a real-analytic map between real Hilbert spaces.

**The real chart.** For `s > 1` every real element of `H^s(ℂ)` has a continuous representative
(`BesselPotentialSpace.continuousRep`), so real coordinates `u` define the continuous field
`continuousRepField u = (continuousRep (u j))ⱼ`, real-linear in `u`, and the field
`x_m + continuousRepField u` of `A_m^s` (`SobolevFieldSpace.ofRealSubRef`). This inverts the
real coordinates `SobolevFieldSpace.realSubRef`, and both maps are continuous, so they form a
homeomorphism `SobolevFieldSpace.realSubRefHomeomorph`. Above the threshold `s > n + 1`
every field of `A_m^s` is moreover a `Cⁿ` map (`SobolevFieldSpace.contDiff`).

**The real equation map.** The vortex equation `∂bar_a α = 0`, `*iF_a = (1 - |α|²) / 8` is
realized on complexified coordinates by the analytic map
`TauCeti.Vortex.sobolevEquation f m hk : H^(k+1)(ℂ)⁴ → H^k(ℂ)³`, which may vanish at non-real
coordinates that correspond to no field. For an integer `k ≥ 2`, the space `A_m^(k+1)` lies above
the threshold for `C¹` fields, and this file shows:

* `sobolevEquation` maps real coordinates to real values
  (`sobolevEquation_mem_realSubmodule`), and so does the linearized equation
  `sobolevLinearizedEquation` at real coordinates (`sobolevLinearizedEquation_mem_realSubmodule`),
  because on real coordinates they compute the pointwise equation and its linearization at the
  `C¹` field they represent;
* their restrictions `realSobolevEquation f m hk : (H^(k+1)_ℝ)⁴ → (H^k_ℝ)³` and
  `realSobolevLinearizedEquation f m hk u` are a real-analytic map
  (`contDiff_realSobolevEquation`) and its derivative (`hasFDerivAt_realSobolevEquation`);
* the zeros of `realSobolevEquation` in the real chart are exactly the vortices of `A_m^(k+1)`
  (`realSobolevEquation_realSubRef_eq_zero_iff`);
* the gauge-fixing row `sobolevGaugeAdjoint` also maps real coordinates to real values
  (`sobolevGaugeAdjoint_mem_realSubmodule`), with restriction
  `realSobolevGaugeAdjoint f m hk u : (H^(k+1)_ℝ)⁴ → H^k_ℝ`;
* at the real coordinates of a field `x`, the continuous representatives of the real gauge-fixing
  row and of the real linearized equation applied to `v` are `d₀*` and `d₁` at `x` of the field
  `continuousRepField v` of continuous representatives of `v`
  (`continuousRep_realSobolevGaugeAdjoint`, `continuousRep_realSobolevLinearizedEquation`).

Real-analyticity uses the bounded real-linear projection `BesselPotentialSpace.realPartCLM` of
`H^s(ℂ)` onto its real elements: the real map is this projection, applied coordinatewise
(`realPartPi`), composed with the complexified map and the inclusion `coordInclusion` of
real coordinates into complexified ones. The vortex moduli space near a vortex is the zero set of
this map in a slice of the gauge action, so these are the nonlinear smoothness statements on which
the implicit function theorem for the moduli space rests. The Coulomb slice and the implicit
function theorem are in `TauCeti.Analysis.PDE.Vortex.FramedGauge.LocalModuli`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open BesselPotentialSpace MeasureTheory Module TemperedDistribution
open scoped BesselPotentialSpace ContDiff

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ} {s : ℝ}

/-! ### Fields from real coordinates -/

/-- **The inclusion of real coordinates** `(H^s_ℝ)^ι` into complexified coordinates `H^s(ℂ)^ι`, a
bounded real-linear map. -/
def coordInclusion {ι : Type*} (h : 0 ≤ s) :
    (ι → realSubmodule ℂ h) →L[ℝ] (ι → H^{s}(ℂ)) :=
  ContinuousLinearMap.piMap fun _ ↦ (realSubmodule ℂ h).subtypeL

theorem coordInclusion_apply {ι : Type*} (h : 0 ≤ s) (u : ι → realSubmodule ℂ h) :
    coordInclusion h u = fun a ↦ (u a : H^{s}(ℂ)) :=
  (rfl)

/-- **The real part, coordinatewise**: the bounded real-linear projection `H^s(ℂ)^ι → (H^s_ℝ)^ι`
applying `BesselPotentialSpace.realPartCLM` in each coordinate. -/
def realPartPi {ι : Type*} (h : 0 ≤ s) :
    (ι → H^{s}(ℂ)) →L[ℝ] (ι → realSubmodule ℂ h) :=
  ContinuousLinearMap.piMap fun _ ↦ realPartCLM ℂ h

theorem realPartPi_apply {ι : Type*} (h : 0 ≤ s) (v : ι → H^{s}(ℂ)) (i : ι) :
    realPartPi h v i = realPartCLM ℂ h (v i) :=
  (rfl)

/-- **The field of real coordinates.** The field whose coordinates are the continuous
representatives (`BesselPotentialSpace.continuousRep`) of real coordinates `u ∈ (H^s_ℝ)⁴`, as a
real-linear map. For `s > 1` its coordinates agree almost everywhere with `u`
(`coeFn_inclusionLp_ae_eq_continuousRepField`), and `x_m + continuousRepField u` is the field of
`A_m^s` with real coordinates `u` (`SobolevFieldSpace.ofRealSubRef`). -/
def continuousRepField {h : 0 ≤ s} :
    (Fin 4 → realSubmodule ℂ h) →ₗ[ℝ] ℂ → EuclideanSpace ℝ (Fin 4) where
  toFun u z := WithLp.toLp 2 fun j ↦ continuousRep (u j) z
  map_add' u v := by
    funext z
    ext j
    simp
  map_smul' c u := by
    funext z
    ext j
    simp

@[simp]
theorem continuousRepField_apply {h : 0 ≤ s} (u : Fin 4 → realSubmodule ℂ h) (z : ℂ)
    (j : Fin 4) : continuousRepField u z j = continuousRep (u j) z :=
  (rfl)

/-- For `s > 1`, the coordinates of `continuousRepField u` are almost everywhere the `L²`
functions of the coordinates `u j`. -/
theorem coeFn_inclusionLp_ae_eq_continuousRepField (hs : 1 < s) {h : 0 ≤ s}
    (u : Fin 4 → realSubmodule ℂ h) (j : Fin 4) :
    ⇑(inclusionLp h (u j : H^{s}(ℂ))) =ᵐ[volume] fun z ↦ (continuousRepField u z j : ℂ) := by
  simpa only [continuousRepField_apply] using
    coeFn_inclusionLp_ae_eq_continuousRep (finrank_real_complex_lt_two_mul hs) (u j)

/-- Above the threshold `s > n + 1`, the continuous representatives of real `H^s` coordinates
form a `Cⁿ` field. -/
theorem contDiff_continuousRepField {n : ℕ} (hs : n + 1 < s) {h : 0 ≤ s}
    (u : Fin 4 → realSubmodule ℂ h) : ContDiff ℝ n (continuousRepField u) := by
  exact contDiff_piLp' (p := 2) fun j ↦ by
    simpa only [continuousRepField_apply] using
      contDiff_continuousRep (finrank_real_complex_add_two_mul_lt_two_mul hs) (u j)

/-- For `s > 1`, real coordinates are determined by their field of continuous representatives. -/
theorem continuousRepField_injective (hs : 1 < s) {h : 0 ≤ s} :
    Function.Injective (continuousRepField (h := h)) := by
  intro u v huv
  funext j
  refine continuousRep_injective (finrank_real_complex_lt_two_mul hs) (funext fun z ↦ ?_)
  simpa only [continuousRepField_apply] using congrArg (fun w ↦ w z j) huv

private theorem natCast_one_add_one_lt (hk : 2 ≤ k) : ((1 : ℕ) : ℝ) + 1 < k + 1 := by
  have : (2 : ℝ) ≤ k := by exact_mod_cast hk
  push_cast
  linarith

private theorem one_lt_natCast_add_one (hk : 2 ≤ k) : 1 < (k : ℝ) + 1 := by
  have : (2 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

private theorem finrank_real_complex_lt_two_mul_natCast (hk : 2 ≤ k) :
    (finrank ℝ ℂ : ℝ) < 2 * k :=
  finrank_real_complex_lt_two_mul ((Nat.one_lt_cast (α := ℝ)).2 hk)

/-- For `s > 1`, the field of real coordinates `u ∈ (H^s_ℝ)⁴` lies in `H^s`. -/
theorem continuousRepField_mem_sobolevFields (hs : 1 < s) {h : 0 ≤ s}
    (u : Fin 4 → realSubmodule ℂ h) : continuousRepField u ∈ sobolevFields s :=
  mem_sobolevFields.2 fun j ↦
    continuousRep_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul hs) (u j)

namespace SobolevFieldSpace

/-! ### The real chart -/

/-- The coordinates of `x - x_m` in `H^s(ℂ)` are real. -/
theorem subRef_mem_realSubmodule (h : 0 ≤ s) (x : SobolevFieldSpace f m s) (j : Fin 4) :
    subRef x j ∈ realSubmodule ℂ h := by
  rw [mem_realSubmodule_iff]
  filter_upwards [coeFn_toLp_inclusion_subRef h x j] with z hz
  rw [← toLp_inclusion, hz, Complex.ofReal_im]

/-- **The real coordinates of a field** `x` of `A_m^s`, `s ≥ 0`: the coordinates of `x - x_m` as
real elements of `H^s(ℂ)`. -/
def realSubRef (h : 0 ≤ s) (x : SobolevFieldSpace f m s) (j : Fin 4) : realSubmodule ℂ h :=
  ⟨subRef x j, subRef_mem_realSubmodule h x j⟩

@[simp]
theorem coe_realSubRef (h : 0 ≤ s) (x : SobolevFieldSpace f m s) (j : Fin 4) :
    (realSubRef h x j : H^{s}(ℂ)) = subRef x j :=
  (rfl)

/-- The `L²` function of a real coordinate of `x` is the complexification of the coordinate of
`x - x_m`. -/
theorem coeFn_inclusionLp_realSubRef (h : 0 ≤ s) (x : SobolevFieldSpace f m s) (j : Fin 4) :
    ⇑(inclusionLp h (realSubRef h x j : H^{s}(ℂ))) =ᵐ[volume]
      fun z ↦ ((x z j - referenceField f m z j : ℝ) : ℂ) := by
  rw [coe_realSubRef, ← toLp_inclusion]
  exact coeFn_toLp_inclusion_subRef h x j

/-- **The field with real coordinates `u`**, for `s > 1`: the continuous field
`x_m + (continuousRep (u j))ⱼ` of `A_m^s`, whose real coordinates are `u`
(`realSubRef_ofRealSubRef`). -/
def ofRealSubRef (hs : 1 < s) {h : 0 ≤ s} (u : Fin 4 → realSubmodule ℂ h) :
    SobolevFieldSpace f m s where
  toFun := referenceField f m + continuousRepField u
  mem_framedFieldSpace' := by
    rw [TauCeti.Vortex.mem_framedFieldSpace, add_sub_cancel_left]
    exact continuousRepField_mem_sobolevFields hs u
  continuous' := (contDiff_referenceField f m).continuous.add
    (contDiff_continuousRepField (n := 0) (by simpa using hs) u).continuous

/-- The field with real coordinates `u` is `x_m` plus the field of continuous representatives of
`u`. -/
theorem coe_ofRealSubRef (hs : 1 < s) {h : 0 ≤ s} (u : Fin 4 → realSubmodule ℂ h) :
    ⇑(ofRealSubRef (f := f) (m := m) hs u) = referenceField f m + continuousRepField u :=
  (rfl)

/-- The `j`-th coordinate of `ofRealSubRef hs u` at `z` is `x_m(z)ⱼ` plus the continuous
representative of `u j` at `z`. -/
@[simp]
theorem ofRealSubRef_apply (hs : 1 < s) {h : 0 ≤ s} (u : Fin 4 → realSubmodule ℂ h) (z : ℂ)
    (j : Fin 4) :
    ofRealSubRef (f := f) (m := m) hs u z j = referenceField f m z j + continuousRep (u j) z :=
  (rfl)

@[simp]
theorem realSubRef_ofRealSubRef (hs : 1 < s) {h : 0 ≤ s} (u : Fin 4 → realSubmodule ℂ h) :
    realSubRef h (ofRealSubRef (f := f) (m := m) hs u) = u := by
  funext j
  refine Subtype.ext ?_
  rw [coe_realSubRef, subRef_eq_toBesselPotentialSpace _ j (memSobolev_inclusionLp h _) ?_,
    toBesselPotentialSpace_memSobolev_inclusionLp]
  filter_upwards [coeFn_inclusionLp_ae_eq_continuousRepField hs u j] with z hz
  rw [hz, ofRealSubRef_apply, add_sub_cancel_left, continuousRepField_apply]

@[simp]
theorem ofRealSubRef_realSubRef (hs : 1 < s) {h : 0 ≤ s} (x : SobolevFieldSpace f m s) :
    ofRealSubRef hs (realSubRef h x) = x :=
  subRef_injective h <| funext fun j ↦ by
    rw [← coe_realSubRef h, realSubRef_ofRealSubRef, coe_realSubRef]

/-- The complexified coordinates of the field with real coordinates `u` are the coordinates `u`
included into `H^s(ℂ)⁴`. -/
theorem subRef_ofRealSubRef (hs : 1 < s) {h : 0 ≤ s} (u : Fin 4 → realSubmodule ℂ h) :
    subRef (ofRealSubRef (f := f) (m := m) hs u) = coordInclusion h u :=
  funext fun j ↦ by rw [← coe_realSubRef h, realSubRef_ofRealSubRef, coordInclusion_apply]

/-- The field of real coordinates of a field `x` of `A_m^s`, `s > 1`, is `x - x_m`. -/
theorem continuousRepField_realSubRef (hs : 1 < s) {h : 0 ≤ s} (x : SobolevFieldSpace f m s) :
    continuousRepField (realSubRef h x) = ⇑x - referenceField f m := by
  conv_rhs => rw [← ofRealSubRef_realSubRef hs (h := h) x, coe_ofRealSubRef]
  exact (add_sub_cancel_left _ _).symm

/-- **The real chart of `A_m^s`**, `s > 1`: the real coordinates of `x - x_m` identify the
continuous fields of `A_m^s` with the real Hilbert space `(H^s_ℝ)⁴`, as topological spaces. -/
def realSubRefHomeomorph (hs : 1 < s) {h : 0 ≤ s} :
    SobolevFieldSpace f m s ≃ₜ (Fin 4 → realSubmodule ℂ h) where
  toFun := realSubRef h
  invFun := ofRealSubRef hs
  left_inv := ofRealSubRef_realSubRef hs
  right_inv := realSubRef_ofRealSubRef hs
  continuous_toFun := continuous_pi fun j ↦
    ((continuous_apply j).comp continuous_subRef).subtype_mk _
  continuous_invFun := by
    refine (isEmbedding_subRef h).continuous_iff.2 ?_
    rw [show subRef ∘ ofRealSubRef hs = coordInclusion h from funext (subRef_ofRealSubRef hs)]
    exact (coordInclusion h).continuous

@[simp]
theorem coe_realSubRefHomeomorph (hs : 1 < s) {h : 0 ≤ s} :
    ⇑(realSubRefHomeomorph (f := f) (m := m) hs (h := h)) = realSubRef h :=
  (rfl)

@[simp]
theorem coe_realSubRefHomeomorph_symm (hs : 1 < s) {h : 0 ≤ s} :
    ⇑(realSubRefHomeomorph (f := f) (m := m) hs (h := h)).symm = ofRealSubRef hs :=
  (rfl)

/-- **Fields of `A_m^s` are `Cⁿ` above the threshold** `s > n + 1`. -/
theorem contDiff {n : ℕ} (hs : n + 1 < s) (x : SobolevFieldSpace f m s) : ContDiff ℝ n x :=
  contDiff_of_mem_framedFieldSpace hs x.continuous x.mem_framedFieldSpace

end SobolevFieldSpace

/-! ### The real vortex equation map -/

/-- For `k ≥ 2`, the complexified vortex equation map sends real coordinates to real values: on
real coordinates `u` it computes the vortex defect of the `C¹` field they represent. -/
theorem sobolevEquation_mem_realSubmodule (hk : 2 ≤ k)
    (u : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) (i : Fin 3) :
    sobolevEquation f m (one_le_two.trans hk) (fun a ↦ (u a : H^{(k : ℝ) + 1}(ℂ))) i ∈
      realSubmodule ℂ k.cast_nonneg := by
  have hs := one_lt_natCast_add_one hk
  rw [mem_realSubmodule_iff]
  filter_upwards [coeFn_inclusionLp_sobolevEquation_ae_eq (f := f) (m := m)
    (one_le_two.trans hk) (coeFn_inclusionLp_ae_eq_continuousRepField hs u)
    (contDiff_continuousRepField (natCast_one_add_one_lt hk) u) i] with z hz
  rw [hz, Complex.ofReal_im]

/-- For `k ≥ 2`, at real coordinates `u` the complexified linearized vortex equation sends real
variations to real values: it computes the pointwise linearization at the `C¹` field `u`
represents. -/
theorem sobolevLinearizedEquation_mem_realSubmodule (hk : 2 ≤ k)
    (u v : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) (i : Fin 3) :
    sobolevLinearizedEquation f m (one_le_two.trans hk) (fun a ↦ (u a : H^{(k : ℝ) + 1}(ℂ)))
      (fun a ↦ (v a : H^{(k : ℝ) + 1}(ℂ))) i ∈ realSubmodule ℂ k.cast_nonneg := by
  have hs := one_lt_natCast_add_one hk
  rw [mem_realSubmodule_iff]
  filter_upwards [coeFn_inclusionLp_sobolevLinearizedEquation_ae_eq (f := f) (m := m)
    (one_le_two.trans hk) (coeFn_inclusionLp_ae_eq_continuousRepField hs u)
    (coeFn_inclusionLp_ae_eq_continuousRepField hs v)
    (contDiff_continuousRepField (natCast_one_add_one_lt hk) v) i] with z hz
  rw [hz, Complex.ofReal_im]

variable (f m) in
/-- **The real vortex equation map.** For an integer `k ≥ 2`, the vortex equation in the real
chart of `A_m^(k+1)` centred at the reference field: the map `(H^(k+1)_ℝ)⁴ → (H^k_ℝ)³` sending
the real coordinates of `x - x_m` to the three components of the vortex defect of `x`
(`realSobolevEquation_realSubRef_eq_zero_iff`). It is the restriction of the complexified map
`sobolevEquation` to real coordinates (`coe_realSobolevEquation_apply`), and it is real-analytic
(`contDiff_realSobolevEquation`). -/
def realSobolevEquation (hk : 2 ≤ k)
    (u : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) (i : Fin 3) :
    realSubmodule ℂ (k.cast_nonneg : (0 : ℝ) ≤ k) :=
  ⟨_, sobolevEquation_mem_realSubmodule (f := f) (m := m) hk u i⟩

@[simp]
theorem coe_realSobolevEquation_apply (hk : 2 ≤ k)
    (u : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) (i : Fin 3) :
    (realSobolevEquation f m hk u i : H^{(k : ℝ)}(ℂ)) =
      sobolevEquation f m (one_le_two.trans hk) (fun a ↦ (u a : H^{(k : ℝ) + 1}(ℂ))) i :=
  (rfl)

variable (f m) in
/-- **The real linearized vortex equation.** For an integer `k ≥ 2` and real coordinates `u` of a
field `x ∈ A_m^(k+1)`, the linearized vortex equation `d₁` at `x` as a bounded real-linear
operator `(H^(k+1)_ℝ)⁴ → (H^k_ℝ)³`: the restriction of `sobolevLinearizedEquation` to real
coordinates (`coe_realSobolevLinearizedEquation_apply`). It is the derivative of
`realSobolevEquation f m hk` at `u` (`hasFDerivAt_realSobolevEquation`). -/
def realSobolevLinearizedEquation (hk : 2 ≤ k)
    (u : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) :
    (Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) →L[ℝ]
      (Fin 3 → realSubmodule ℂ (k.cast_nonneg : (0 : ℝ) ≤ k)) :=
  ContinuousLinearMap.pi fun i ↦
    ((ContinuousLinearMap.proj i).comp
      (((sobolevLinearizedEquation f m (one_le_two.trans hk)
        (fun a ↦ (u a : H^{(k : ℝ) + 1}(ℂ)))).restrictScalars ℝ).comp
        (coordInclusion _))).codRestrict
      (realSubmodule ℂ k.cast_nonneg) fun v ↦
        sobolevLinearizedEquation_mem_realSubmodule (f := f) (m := m) hk u v i

@[simp]
theorem coe_realSobolevLinearizedEquation_apply (hk : 2 ≤ k)
    (u v : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) (i : Fin 3) :
    (realSobolevLinearizedEquation f m hk u v i : H^{(k : ℝ)}(ℂ)) =
      sobolevLinearizedEquation f m (one_le_two.trans hk) (fun a ↦ (u a : H^{(k : ℝ) + 1}(ℂ)))
        (fun a ↦ (v a : H^{(k : ℝ) + 1}(ℂ))) i :=
  (rfl)

/-- For `k ≥ 2`, at real coordinates `u` the complexified gauge-fixing row sends real variations
to real values: it computes `d₀*` at the `C¹` field `u` represents. -/
theorem sobolevGaugeAdjoint_mem_realSubmodule (hk : 2 ≤ k)
    (u v : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) :
    sobolevGaugeAdjoint f m (one_le_two.trans hk) (fun a ↦ (u a : H^{(k : ℝ) + 1}(ℂ)))
      (fun a ↦ (v a : H^{(k : ℝ) + 1}(ℂ))) ∈ realSubmodule ℂ k.cast_nonneg := by
  have hs := one_lt_natCast_add_one hk
  rw [mem_realSubmodule_iff]
  filter_upwards [coeFn_inclusionLp_sobolevGaugeAdjoint_ae_eq (f := f) (m := m)
    (one_le_two.trans hk) (coeFn_inclusionLp_ae_eq_continuousRepField hs u)
    (coeFn_inclusionLp_ae_eq_continuousRepField hs v)
    (contDiff_euclidean.1 (contDiff_continuousRepField (natCast_one_add_one_lt hk) v) 0)
    (contDiff_euclidean.1 (contDiff_continuousRepField (natCast_one_add_one_lt hk) v) 1)] with z hz
  rw [hz, Complex.ofReal_im]

variable (f m) in
/-- **The real gauge-fixing row.** For an integer `k ≥ 2` and real coordinates `u` of a field
`x ∈ A_m^(k+1)`, the formal adjoint `d₀*` of the infinitesimal gauge action at `x` as a bounded
real-linear operator `(H^(k+1)_ℝ)⁴ → H^k_ℝ`: the restriction of `sobolevGaugeAdjoint` to real
coordinates (`coe_realSobolevGaugeAdjoint_apply`). -/
def realSobolevGaugeAdjoint (hk : 2 ≤ k)
    (u : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) :
    (Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) →L[ℝ]
      realSubmodule ℂ (k.cast_nonneg : (0 : ℝ) ≤ k) :=
  (((sobolevGaugeAdjoint f m (one_le_two.trans hk)
    (fun a ↦ (u a : H^{(k : ℝ) + 1}(ℂ)))).restrictScalars ℝ).comp (coordInclusion _)).codRestrict
      (realSubmodule ℂ k.cast_nonneg) fun v ↦
        sobolevGaugeAdjoint_mem_realSubmodule (f := f) (m := m) hk u v

@[simp]
theorem coe_realSobolevGaugeAdjoint_apply (hk : 2 ≤ k)
    (u v : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) :
    (realSobolevGaugeAdjoint f m hk u v : H^{(k : ℝ)}(ℂ)) =
      sobolevGaugeAdjoint f m (one_le_two.trans hk) (fun a ↦ (u a : H^{(k : ℝ) + 1}(ℂ)))
        (fun a ↦ (v a : H^{(k : ℝ) + 1}(ℂ))) :=
  (rfl)

/-- The `L²` functions of the real coordinates of `x` are almost everywhere the complexified
coordinates of the field `x - x_m`. -/
private theorem coeFn_inclusionLp_realSubRef_ae_eq_sub (h : 0 ≤ s) (x : SobolevFieldSpace f m s)
    (a : Fin 4) : ⇑(inclusionLp h (x.realSubRef h a : H^{s}(ℂ))) =ᵐ[volume]
      fun z ↦ ((⇑x - referenceField f m) z a : ℂ) :=
  (SobolevFieldSpace.coeFn_inclusionLp_realSubRef h x a).trans (.of_forall fun z ↦ by simp)

/-- **The real gauge-fixing row computes `d₀*`.** At the real coordinates of a field `x` of
`A_m^(k+1)`, `k ≥ 2`, the continuous representative of the real gauge-fixing row applied to `v` is
`d₀*` at `x` of the field of real coordinates `v`. -/
theorem continuousRep_realSobolevGaugeAdjoint (hk : 2 ≤ k)
    (x : SobolevFieldSpace f m ((k : ℝ) + 1))
    (v : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) :
    continuousRep (realSobolevGaugeAdjoint f m hk (x.realSubRef _) v) =
      gaugeAdjoint x (continuousRepField v) := by
  have hv := contDiff_continuousRepField (natCast_one_add_one_lt hk) v
  refine continuousRep_eq_of_ae_eq
    (finrank_real_complex_lt_two_mul_natCast hk)
    (continuous_gaugeAdjoint x.continuous hv) ?_
  rw [coe_realSobolevGaugeAdjoint_apply]
  simpa only [add_sub_cancel] using coeFn_inclusionLp_sobolevGaugeAdjoint_ae_eq (f := f) (m := m)
    (y := ⇑x - referenceField f m) (one_le_two.trans hk)
    (coeFn_inclusionLp_realSubRef_ae_eq_sub _ x)
    (coeFn_inclusionLp_ae_eq_continuousRepField (one_lt_natCast_add_one hk) v)
    (contDiff_euclidean.1 hv 0) (contDiff_euclidean.1 hv 1)

/-- **The real linearized equation computes `d₁`.** At the real coordinates of a field `x` of
`A_m^(k+1)`, `k ≥ 2`, the continuous representative of each row of the real linearized equation
applied to `v` is that row of `d₁` at `x` of the field of real coordinates `v`. -/
theorem continuousRep_realSobolevLinearizedEquation (hk : 2 ≤ k)
    (x : SobolevFieldSpace f m ((k : ℝ) + 1))
    (v : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) (i : Fin 3) :
    continuousRep (realSobolevLinearizedEquation f m hk (x.realSubRef _) v i) =
      fun z ↦ linearizedEquation x (continuousRepField v) z i := by
  have hv := contDiff_continuousRepField (natCast_one_add_one_lt hk) v
  have hc : Continuous fun z ↦ linearizedEquation x (continuousRepField v) z i := by
    have h (j : Fin 4) : Continuous fun z ↦ gaugeFixedOperator x (continuousRepField v) z j :=
      (EuclideanSpace.proj j).continuous.comp (continuous_gaugeFixedOperator x.continuous hv)
    simpa only [gaugeFixedOperator_apply_succ] using h i.succ
  refine continuousRep_eq_of_ae_eq
    (finrank_real_complex_lt_two_mul_natCast hk) hc ?_
  rw [coe_realSobolevLinearizedEquation_apply]
  simpa only [add_sub_cancel] using coeFn_inclusionLp_sobolevLinearizedEquation_ae_eq
    (f := f) (m := m) (y := ⇑x - referenceField f m) (one_le_two.trans hk)
    (coeFn_inclusionLp_realSubRef_ae_eq_sub _ x)
    (coeFn_inclusionLp_ae_eq_continuousRepField (one_lt_natCast_add_one hk) v) hv i

/-- The real equation map is the real part of the complexified map on real coordinates. -/
private theorem realSobolevEquation_eq_comp (hk : 2 ≤ k) :
    realSobolevEquation f m hk = realPartPi k.cast_nonneg ∘
      sobolevEquation f m (one_le_two.trans hk) ∘ coordInclusion _ := by
  funext u i
  rw [Function.comp_apply, Function.comp_apply, realPartPi_apply, coordInclusion_apply,
    ← coe_realSobolevEquation_apply hk, realPartCLM_coe]

/-- **The real vortex equation map is real-analytic.** -/
theorem contDiff_realSobolevEquation (hk : 2 ≤ k) :
    ContDiff ℝ ω (realSobolevEquation f m hk) := by
  rw [realSobolevEquation_eq_comp]
  exact (realPartPi _).contDiff.comp
    (((contDiff_sobolevEquation (one_le_two.trans hk)).restrict_scalars ℝ).comp
      (coordInclusion _).contDiff)

/-- **The derivative of the real vortex equation map** at real coordinates `u` is the real
linearized equation `realSobolevLinearizedEquation f m hk u`. -/
theorem hasFDerivAt_realSobolevEquation (hk : 2 ≤ k)
    (u : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) :
    HasFDerivAt (realSobolevEquation f m hk) (realSobolevLinearizedEquation f m hk u) u := by
  have hD := (realPartPi k.cast_nonneg).hasFDerivAt.comp u
    (((hasFDerivAt_sobolevEquation (f := f) (m := m) (one_le_two.trans hk)
      (coordInclusion _ u)).restrictScalars ℝ).comp u (coordInclusion _).hasFDerivAt)
  rw [← realSobolevEquation_eq_comp hk] at hD
  convert hD using 1
  ext v i : 2
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    realPartPi_apply, coordInclusion_apply]
  rw [← coe_realSobolevLinearizedEquation_apply hk, realPartCLM_coe]

/-- **The zeros of the real vortex equation map are the vortices.** For `k ≥ 2`, a continuous
field `x` of `A_m^(k+1)` solves the vortex equation exactly when its real coordinates are a zero
of `realSobolevEquation f m hk`. -/
theorem realSobolevEquation_realSubRef_eq_zero_iff (hk : 2 ≤ k)
    (x : SobolevFieldSpace f m ((k : ℝ) + 1)) :
    realSobolevEquation f m hk (x.realSubRef _) = 0 ↔ equation x = 0 := by
  have hx : ContDiff ℝ 1 x := x.contDiff (natCast_one_add_one_lt hk)
  rw [← sobolevEquation_eq_zero_iff (f := f) (m := m) (one_le_two.trans hk)
    (fun a ↦ SobolevFieldSpace.coeFn_inclusionLp_realSubRef _ x a) hx]
  constructor
  · intro h0
    funext i
    simpa using congrArg (fun v ↦ (v i : H^{(k : ℝ)}(ℂ))) h0
  · intro h0
    funext i
    exact Subtype.ext (by simpa using congrFun h0 i)

end TauCeti.Vortex
