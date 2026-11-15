/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion

/-!
# Real elements of the Bessel-potential spaces `H^s(E)`

Mathlib's Bessel-potential space `H^s(E) = H^{s,2}(E, ℂ)` is a complex Hilbert space of tempered
distributions. Real-valued Sobolev functions, such as the coordinates of a field of a real
nonlinear equation, are described in Tau Ceti by the submodule of functions
`TemperedDistribution.realSobolevFunctions E s 2`, which carries no norm. This file identifies
them with a closed real subspace of `H^s(E)`, so that the Banach-space machinery (the closed graph
and open mapping theorems, the implicit function theorem) applies to them.

For `s ≥ 0` every `u ∈ H^s(E)` is an `L²` function, the `L²` function of its inclusion into
`H^0(E) = L²(E)` (`BesselPotentialSpace.toTemperedDistribution_toLp_inclusion`). Its real part is
`BesselPotentialSpace.reValue u`. The **real subspace**
`BesselPotentialSpace.realSubmodule E s` consists of the `u` whose `L²` function is real almost
everywhere. Then:

* the real subspace is closed (`BesselPotentialSpace.isClosed_realSubmodule`), hence a real
  Banach space;
* for `u` in it, `reValue u` lies in `realSobolevFunctions E s 2`
  (`BesselPotentialSpace.reValue_mem_realSobolevFunctions`), and `u` is determined by it
  (`BesselPotentialSpace.eq_of_reValue_ae_eq`);
* conversely every `f ∈ realSobolevFunctions E s 2` is `reValue u` almost everywhere for the
  element `u = BesselPotentialSpace.ofRealSobolev hf` of the real subspace
  (`BesselPotentialSpace.reValue_ofRealSobolev`).

So `u ↦ reValue u` identifies the real subspace with `realSobolevFunctions E s 2` up to null
sets. Testing `reValue u` against a fixed real `L²` function is continuous on `H^s(E)`
(`BesselPotentialSpace.continuous_integral_reValue_mul`), which is how weak formulations of real
equations pass to limits in `H^s`.
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution
open scoped ENNReal BesselPotentialSpace InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace BesselPotentialSpace

variable {s : ℝ}

/-- The real part of the `L²` function of `u ∈ H^s(E)`, for `s ≥ 0` (`reValue_apply`). For
`s < 0`, where `u` need not be a function, it is `0` by convention. -/
def reValue (u : H^{s}(E)) : E → ℝ :=
  if hs : 0 ≤ s then fun x ↦ ((inclusion hs u).toLp x).re else 0

/-- For `s ≥ 0`, `reValue u` is the real part of the `L²` function of `u`. -/
theorem reValue_eq (hs : 0 ≤ s) (u : H^{s}(E)) :
    reValue u = fun x ↦ ((inclusion hs u).toLp x).re := by
  rw [reValue, dite_eq_left hs]

/-- For `s ≥ 0`, `reValue u x` is the real part of the `L²` function of `u` at `x`. -/
theorem reValue_apply (hs : 0 ≤ s) (u : H^{s}(E)) (x : E) :
    reValue u x = ((inclusion hs u).toLp x).re := by
  rw [reValue_eq hs]

/-- For `s < 0`, `reValue u` is `0` by convention. -/
theorem reValue_of_lt (hs : s < 0) (u : H^{s}(E)) : reValue u = 0 := by
  rw [reValue, dite_eq_right (fun h ↦ absurd h (not_le.2 hs))]

/-- The real part of the `L²` function of an element of `H^s(E)` is square integrable. -/
theorem memLp_reValue (u : H^{s}(E)) : MemLp (reValue u) 2 volume := by
  rcases lt_or_ge s 0 with hs | hs
  · rw [reValue_of_lt hs]
    exact MemLp.zero
  rw [reValue_eq hs]
  exact Complex.reCLM.comp_memLp' (Lp.memLp _)

/-- `reValue` is additive almost everywhere. -/
theorem reValue_add (u v : H^{s}(E)) :
    reValue (u + v) =ᵐ[volume] reValue u + reValue v := by
  rcases lt_or_ge s 0 with hs | hs
  · simp [reValue_of_lt hs]
  filter_upwards [coeFn_toLp_inclusion_add hs u v] with x hx
  rw [Pi.add_apply, reValue_apply hs, reValue_apply hs, reValue_apply hs, hx, Pi.add_apply,
    Complex.add_re]

/-- `reValue` is homogeneous for real scalars almost everywhere. -/
theorem reValue_smul (c : ℝ) (u : H^{s}(E)) :
    reValue (c • u) =ᵐ[volume] c • reValue u := by
  rcases lt_or_ge s 0 with hs | hs
  · simp [reValue_of_lt hs]
  have h : c • u = (c : ℂ) • u := (Complex.coe_smul c u).symm
  filter_upwards [coeFn_toLp_inclusion_smul hs (c : ℂ) u] with x hx
  rw [Pi.smul_apply, reValue_apply hs, reValue_apply hs, h, hx, Pi.smul_apply, smul_eq_mul,
    Complex.re_ofReal_mul, smul_eq_mul]

variable (E) in
/-- The **real subspace** of `H^s(E)`, `s ≥ 0`: the elements whose `L²` function is real almost
everywhere. It is closed (`BesselPotentialSpace.isClosed_realSubmodule`) and identified with
`realSobolevFunctions E s 2` by `BesselPotentialSpace.reValue`. -/
def realSubmodule (s : ℝ) (hs : 0 ≤ s := by positivity) : Submodule ℝ H^{s}(E) where
  carrier := {u | ∀ᵐ x ∂(volume : Measure E), ((inclusion hs u).toLp x).im = 0}
  add_mem' {u v} hu hv := by
    simp only [Set.mem_ofPred_eq] at hu hv ⊢
    filter_upwards [coeFn_toLp_inclusion_add hs u v, hu, hv] with x hx h₁ h₂
    rw [hx, Pi.add_apply, Complex.add_im, h₁, h₂, add_zero]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero, toLp_zero]
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure E)] with x hx
    rw [hx, Pi.zero_apply, Complex.zero_im]
  smul_mem' c u hu := by
    simp only [Set.mem_ofPred_eq] at hu ⊢
    -- The real scalar action on `H^s(E)` is the action of the complex number `c`.
    change ∀ᵐ x ∂volume, ((inclusion hs ((c : ℂ) • u)).toLp x).im = 0
    filter_upwards [coeFn_toLp_inclusion_smul hs (c : ℂ) u, hu] with x hx hu
    rw [hx, Pi.smul_apply, smul_eq_mul, Complex.im_ofReal_mul, hu, mul_zero]

theorem mem_realSubmodule_iff (hs : 0 ≤ s) {u : H^{s}(E)} :
    u ∈ realSubmodule E s hs ↔ ∀ᵐ x ∂(volume : Measure E), ((inclusion hs u).toLp x).im = 0 :=
  Iff.rfl

/-- The `L²` function of an element of the real subspace is its real part, almost everywhere. -/
theorem coeFn_toLp_inclusion_ae_eq_reValue (hs : 0 ≤ s) {u : H^{s}(E)}
    (hu : u ∈ realSubmodule E s hs) :
    (inclusion hs u).toLp =ᵐ[volume] fun x ↦ (reValue u x : ℂ) := by
  filter_upwards [hu] with x hx
  exact Complex.ext (by simp [reValue_apply hs]) (by simp [hx])

/-- The real part of an element of the real subspace of `H^s(E)` is a real `H^s` function. -/
theorem reValue_mem_realSobolevFunctions (hs : 0 ≤ s) {u : H^{s}(E)}
    (hu : u ∈ realSubmodule E s hs) : reValue u ∈ realSobolevFunctions E s 2 :=
  mem_realSobolevFunctions_of_ae_eq_ofReal (memSobolev_toLp_inclusion hs u)
    (coeFn_toLp_inclusion_ae_eq_reValue hs hu)

/-- An element of the real subspace is determined by its real part. -/
theorem eq_of_reValue_ae_eq (hs : 0 ≤ s) {u v : H^{s}(E)} (hu : u ∈ realSubmodule E s hs)
    (hv : v ∈ realSubmodule E s hs) (h : reValue u =ᵐ[volume] reValue v) : u = v := by
  refine toLp_inclusion_injective hs (Lp.ext ?_)
  filter_upwards [coeFn_toLp_inclusion_ae_eq_reValue hs hu,
    coeFn_toLp_inclusion_ae_eq_reValue hs hv, h] with x h₁ h₂ h₃
  simp [h₁, h₂, h₃]

/-- The element of the real subspace of `H^s(E)` defined by a real `H^s` function `f`. Its real
part is `f` almost everywhere (`BesselPotentialSpace.reValue_ofRealSobolev`). -/
def ofRealSobolev {f : E → ℝ} (hf : f ∈ realSobolevFunctions E s 2) : H^{s}(E) :=
  (mem_realSobolevFunctions.1 hf).choose_spec.2.toBesselPotentialSpace

/-- The `L²` function of `ofRealSobolev hf` is `f`, almost everywhere. -/
theorem coeFn_toLp_inclusion_ofRealSobolev (hs : 0 ≤ s) {f : E → ℝ}
    (hf : f ∈ realSobolevFunctions E s 2) :
    (inclusion hs (ofRealSobolev hf)).toLp =ᵐ[volume] fun x ↦ (f x : ℂ) := by
  have hspec := (mem_realSobolevFunctions.1 hf).choose_spec
  rw [ofRealSobolev, toLp_inclusion_toBesselPotentialSpace hs hspec.2 rfl]
  filter_upwards [Complex.ofRealCLM.coeFn_compLp (p := 2) (μ := volume)
    (mem_realSobolevFunctions.1 hf).choose, hspec.1] with x h₁ h₂
  rw [h₁, Complex.ofRealCLM_apply, h₂]

theorem ofRealSobolev_mem_realSubmodule (hs : 0 ≤ s) {f : E → ℝ}
    (hf : f ∈ realSobolevFunctions E s 2) : ofRealSobolev hf ∈ realSubmodule E s hs := by
  rw [mem_realSubmodule_iff]
  filter_upwards [coeFn_toLp_inclusion_ofRealSobolev hs hf] with x hx
  simp [hx]

/-- The real part of `ofRealSobolev hf` is `f`, almost everywhere. -/
theorem reValue_ofRealSobolev (hs : 0 ≤ s) {f : E → ℝ} (hf : f ∈ realSobolevFunctions E s 2) :
    reValue (ofRealSobolev hf) =ᵐ[volume] f := by
  filter_upwards [coeFn_toLp_inclusion_ofRealSobolev hs hf] with x hx
  simp [reValue_apply hs, hx]

/-- An element of the real subspace is recovered from its real part by `ofRealSobolev`. -/
theorem ofRealSobolev_reValue (hs : 0 ≤ s) {u : H^{s}(E)} (hu : u ∈ realSubmodule E s hs) :
    ofRealSobolev (reValue_mem_realSobolevFunctions hs hu) = u :=
  eq_of_reValue_ae_eq hs (ofRealSobolev_mem_realSubmodule hs _) hu (reValue_ofRealSobolev hs _)

/-- The `L²` function of an element of `H^s(E)`, `s ≥ 0`, depends continuously on it. -/
theorem continuous_toLp_inclusion (hs : 0 ≤ s) :
    Continuous fun u : H^{s}(E) ↦ (inclusion hs u).toLp := by
  simpa only [Function.comp_def, toLpₗᵢ_apply] using
    (toLpₗᵢ (E := E) (F := ℂ) (s := 0) (p := 2)).continuous.comp (inclusion hs).continuous

/-- Testing the real part against a fixed real `L²` function is continuous on `H^s(E)`. -/
theorem continuous_integral_reValue_mul {ψ : E → ℝ} (hψ : MemLp ψ 2 volume) :
    Continuous fun u : H^{s}(E) ↦ ∫ x, reValue u x * ψ x := by
  rcases lt_or_ge s 0 with hs | hs
  · simpa [reValue_of_lt hs] using continuous_const
  set Ψ : Lp ℂ 2 (volume : Measure E) := Complex.ofRealCLM.compLp (hψ.toLp ψ)
  have hΨ : Ψ =ᵐ[volume] fun x ↦ (ψ x : ℂ) := by
    filter_upwards [Complex.ofRealCLM.coeFn_compLp (p := 2) (μ := volume) (hψ.toLp ψ),
      hψ.coeFn_toLp] with x h₁ h₂
    rw [h₁, Complex.ofRealCLM_apply, h₂]
  -- The test is the real part of the `L²` inner product with `ψ`.
  have heq (u : H^{s}(E)) :
      ∫ x, reValue u x * ψ x = RCLike.re ⟪Ψ, (inclusion hs u).toLp⟫_ℂ := by
    rw [L2.inner_def, ← integral_re (L2.integrable_inner Ψ _)]
    refine integral_congr_ae ?_
    filter_upwards [hΨ] with x hx
    simp [reValue_apply hs, hx, mul_comm]
  simp_rw [heq]
  exact RCLike.continuous_re.comp (continuous_const.inner (continuous_toLp_inclusion hs))

/-- The real subspace of `H^s(E)` is closed. -/
theorem isClosed_realSubmodule (hs : 0 ≤ s) : IsClosed (realSubmodule E s hs : Set H^{s}(E)) := by
  -- It is the kernel of the continuous map `u ↦ Im` of the `L²` function of `u`.
  set T : H^{s}(E) → Lp ℝ 2 (volume : Measure E) :=
    fun u ↦ Complex.imCLM.compLp (inclusion hs u).toLp
  have hT : Continuous T :=
    (Complex.imCLM.compLpL 2 (volume : Measure E)).continuous.comp (continuous_toLp_inclusion hs)
  have hset : (realSubmodule E s hs : Set H^{s}(E)) = T ⁻¹' {0} := by
    ext u
    simp only [SetLike.mem_coe, mem_realSubmodule_iff, Set.mem_preimage, Set.mem_singleton_iff, T]
    rw [Lp.eq_zero_iff_ae_eq_zero]
    constructor
    · intro h
      filter_upwards [Complex.imCLM.coeFn_compLp (p := 2) (μ := volume) (inclusion hs u).toLp,
        h] with x h₁ h₂
      simp [h₁, h₂]
    · intro h
      filter_upwards [Complex.imCLM.coeFn_compLp (p := 2) (μ := volume) (inclusion hs u).toLp,
        h] with x h₁ h₂
      simpa [h₂] using h₁.symm
  rw [hset]
  exact isClosed_singleton.preimage hT

instance (hs : 0 ≤ s) : CompleteSpace (realSubmodule E s hs) :=
  (isClosed_realSubmodule hs).completeSpace_coe

end BesselPotentialSpace
