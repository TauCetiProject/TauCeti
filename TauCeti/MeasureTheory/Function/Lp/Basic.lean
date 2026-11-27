/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import TauCeti.MeasureTheory.Function.Lp.LinearIsometry

/-!
# Sums, linear combinations, semilinear compositions, and `RCLike` coordinates in `Lᵖ`

Mathlib provides `MeasureTheory.MemLp.toLp_zero`, `MeasureTheory.MemLp.toLp_add`, and
`MeasureTheory.Lp.coeFn_finsetSum`, as well as `MeasureTheory.memLp_finsetSum` and
`MeasureTheory.memLp_finsetSum'`. This file records the companion identities identifying the `Lp`
class of a finite sum of `Lᵖ` functions with the sum of their `Lp` classes, for any `MemLp`
witness on the sum, and registers `Unique (Lp E p (0 : Measure α))` on the zero measure.

Mathlib describes the representatives of sums, negatives and scalar multiples in `Lᵖ` almost
everywhere (`MeasureTheory.Lp.coeFn_add` and its siblings); this file records the forms that
transport almost-everywhere descriptions `⇑u =ᵐ[μ] g` of the summands, which compute the
representatives of linear combinations.

Mathlib composes `f : Lp E p μ` with `L : E →SL[σ] F` both as an element `L.compLp f` and through
the bundled continuous semilinear map `L.compLpL p μ`; this file records that the two agree, their
composition and identity laws, and that for `1 ≤ p` the postcomposition
`LinearIsometry.compLpₗᵢ` by a semilinear isometry underlies `ContinuousLinearMap.compLpL`.
Specializing `compLpₗᵢ` and `compLpL` to `RCLike.ofRealLI`, `RCLike.reCLM`, and `RCLike.imCLM`
defines the scalar inclusion `MeasureTheory.Lp.ofRealLI` and the real and imaginary coordinate
operators `MeasureTheory.Lp.reCLM` and `MeasureTheory.Lp.imCLM` between `Lp ℝ p μ` and `Lp 𝕜 p μ`.

## Main declarations

* `MeasureTheory.MemLp.toLp_finsetSum'`: `hsum.toLp (∑ i ∈ s, f i) = ∑ i ∈ s, (hf i).toLp (f i)`.
* `MeasureTheory.MemLp.toLp_finsetSum`:
  `hsum.toLp (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, (hf i).toLp (f i)`.
* `MeasureTheory.Lp.coeFn_add_ae_eq_of_ae_eq`, `MeasureTheory.Lp.coeFn_sub_ae_eq_of_ae_eq`,
  `MeasureTheory.Lp.coeFn_neg_ae_eq_of_ae_eq`, `MeasureTheory.Lp.coeFn_smul_ae_eq_of_ae_eq`: if
  `⇑u =ᵐ[μ] g` and `⇑v =ᵐ[μ] h`, then `⇑(u + v) =ᵐ[μ] g + h`, and similarly for `-` and `•`.
* `ContinuousLinearMap.compLp_comp_linear`, `ContinuousLinearMap.compLp_comp_toSpanSingleton`:
  simplification laws for linear composition and scalar-functional reconstruction at every
  exponent.
* `ContinuousLinearMap.compLpL_toSpanSingleton`: a scalar functional after rank-one
  reconstruction is scalar multiplication.
* `ContinuousLinearMap.compLpL_apply`: the bundled composition applied to `f` is `L.compLp f`.
* `ContinuousLinearMap.zero_compLp`: composing an `Lp` class with the zero map gives zero.
* `ContinuousLinearMap.compLp_compLp`, `ContinuousLinearMap.compLpL_comp_compLpL`,
  `ContinuousLinearMap.compLpL_compLpL`: composition laws for `compLp` and `compLpL`.
* `ContinuousLinearMap.compLpL_comp_compLpL_eq`: two composites of `compLpL` operators agree when
  the composites of the underlying maps do.
* `ContinuousLinearMap.id_compLp`, `ContinuousLinearMap.id_compLpL`: identity laws for `compLp` and
  `compLpL`.
* `LinearIsometry.toContinuousLinearMap_compLpₗᵢ`: postcomposition of `Lp` classes by a
  semilinear isometry (`LinearIsometry.compLpₗᵢ`) underlies `ContinuousLinearMap.compLpL`.
* `MeasureTheory.Lp.instUniqueZero`: `Unique (Lp E p (0 : Measure α))`.
* `MeasureTheory.Lp.ofRealLI`, `MeasureTheory.Lp.reCLM`, `MeasureTheory.Lp.imCLM`: scalar inclusion
  and real/imaginary parts on `Lp 𝕜 p μ` for an `RCLike` field `𝕜`.
-/

public section

open scoped ENNReal

namespace MeasureTheory.MemLp

variable {α E ι : Type*} {_ : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  {p : ℝ≥0∞} {s : Finset ι} {f : ι → α → E}

/-- The `Lp` class of a finite sum of `Lᵖ` functions is the sum of their `Lp` classes. -/
theorem toLp_finsetSum' (hsum : MemLp (∑ i ∈ s, f i) p μ) (hf : ∀ i, MemLp (f i) p μ) :
    hsum.toLp (∑ i ∈ s, f i) = ∑ i ∈ s, (hf i).toLp (f i) :=
  Lp.ext_iff.2 <| hsum.coeFn_toLp.trans <|
    (eventuallyEq_sum fun i _ ↦ (hf i).coeFn_toLp.symm).trans
      (Lp.coeFn_finsetSum s fun i ↦ (hf i).toLp (f i)).symm

/-- The `Lp` class of a pointwise finite sum `fun x ↦ ∑ i ∈ s, f i x` of `Lᵖ` functions is the
sum of their `Lp` classes. -/
theorem toLp_finsetSum (hsum : MemLp (fun x ↦ ∑ i ∈ s, f i x) p μ) (hf : ∀ i, MemLp (f i) p μ) :
    hsum.toLp (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, (hf i).toLp (f i) := by
  convert (memLp_finsetSum' s fun i _ ↦ hf i).toLp_finsetSum' hf using 1
  exact toLp_congr _ _ (.of_forall fun x ↦ (Finset.sum_apply x s f).symm)

end MeasureTheory.MemLp

namespace MeasureTheory.Lp

variable {α E 𝕜 : Type*} {_ : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}
  [NormedAddCommGroup E] {u v : Lp E p μ} {g h : α → E}

/-- If `u` and `v` are almost everywhere `g` and `h`, then `u + v` is almost everywhere `g + h`. -/
theorem coeFn_add_ae_eq_of_ae_eq (hu : ⇑u =ᵐ[μ] g) (hv : ⇑v =ᵐ[μ] h) : ⇑(u + v) =ᵐ[μ] g + h :=
  (coeFn_add u v).trans (hu.add hv)

/-- If `u` and `v` are almost everywhere `g` and `h`, then `u - v` is almost everywhere `g - h`. -/
theorem coeFn_sub_ae_eq_of_ae_eq (hu : ⇑u =ᵐ[μ] g) (hv : ⇑v =ᵐ[μ] h) : ⇑(u - v) =ᵐ[μ] g - h :=
  (coeFn_sub u v).trans (hu.sub hv)

/-- If `u` is almost everywhere `g`, then `-u` is almost everywhere `-g`. -/
theorem coeFn_neg_ae_eq_of_ae_eq (hu : ⇑u =ᵐ[μ] g) : ⇑(-u) =ᵐ[μ] -g :=
  (coeFn_neg u).trans hu.neg

/-- If `u` is almost everywhere `g`, then `c • u` is almost everywhere `c • g`. -/
theorem coeFn_smul_ae_eq_of_ae_eq [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (c : 𝕜)
    (hu : ⇑u =ᵐ[μ] g) : ⇑(c • u) =ᵐ[μ] c • g :=
  (coeFn_smul c u).trans (hu.const_smul c)

end MeasureTheory.Lp

namespace ContinuousLinearMap

open MeasureTheory

section Apply

variable {α E F 𝕜 𝕜' : Type*} {_ : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}
  [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] {σ : 𝕜 →+* 𝕜'} [RingHomIsometric σ]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜' F]

/-- The bundled composition `L.compLpL p μ` applied to `f` is the composition `L.compLp f`. -/
@[simp]
theorem compLpL_apply [Fact (1 ≤ p)] (L : E →SL[σ] F) (f : Lp E p μ) :
    L.compLpL p μ f = L.compLp f :=
  rfl

/-- Composing an `Lp` class with the zero map gives the zero class. -/
@[simp]
theorem zero_compLp (f : Lp E p μ) : (0 : E →SL[σ] F).compLp f = 0 := by
  ext1
  filter_upwards [(0 : E →SL[σ] F).coeFn_compLp f, Lp.coeFn_zero F p μ] with x hx h0
  rw [hx, h0, zero_apply, Pi.zero_apply]

end Apply

section Comp

variable {α E F G 𝕜₁ 𝕜₂ 𝕜₃ : Type*} {_ : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜₁ E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G]
  {σ₁₂ : 𝕜₁ →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜₁ →+* 𝕜₃}
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃]
  [RingHomIsometric σ₁₃]

/-- Composing `Lp` pushforwards of continuous semilinear maps agrees with the pushforward of their
composition. -/
theorem compLp_compLp (L : F →SL[σ₂₃] G) (M : E →SL[σ₁₂] F) (f : Lp E p μ) :
    L.compLp (M.compLp f) = (L.comp M).compLp f := by
  ext1
  filter_upwards [L.coeFn_compLp (M.compLp f), M.coeFn_compLp f, (L.comp M).coeFn_compLp f] with
    x hx1 hx2 hx3
  rw [hx1, hx2, hx3, comp_apply]

/-- Composing `compLpL` operators agrees with `compLpL` of the composed continuous semilinear
operator. -/
theorem compLpL_comp_compLpL [Fact (1 ≤ p)] (L : F →SL[σ₂₃] G) (M : E →SL[σ₁₂] F) :
    (L.compLpL p μ).comp (M.compLpL p μ) = (L.comp M).compLpL p μ := by
  ext1 f
  exact L.compLp_compLp M f

/-- Applying `compLpL` in succession agrees with `compLpL` of the composed continuous semilinear
operator. -/
theorem compLpL_compLpL [Fact (1 ≤ p)] (L : F →SL[σ₂₃] G) (M : E →SL[σ₁₂] F) (f : Lp E p μ) :
    L.compLpL p μ (M.compLpL p μ f) = (L.comp M).compLpL p μ f :=
  L.compLp_compLp M f

/-- Two composites of `compLpL` operators agree when the composites of the underlying continuous
semilinear maps do. -/
theorem compLpL_comp_compLpL_eq [Fact (1 ≤ p)] {H 𝕜₄ : Type*} [NormedAddCommGroup H]
    [NontriviallyNormedField 𝕜₄] [NormedSpace 𝕜₄ H] {σ₁₄ : 𝕜₁ →+* 𝕜₄} {σ₄₃ : 𝕜₄ →+* 𝕜₃}
    [RingHomCompTriple σ₁₄ σ₄₃ σ₁₃] [RingHomIsometric σ₁₄] [RingHomIsometric σ₄₃]
    {L : F →SL[σ₂₃] G} {M : E →SL[σ₁₂] F} {L' : H →SL[σ₄₃] G} {M' : E →SL[σ₁₄] H}
    (h : L.comp M = L'.comp M') :
    (L.compLpL p μ).comp (M.compLpL p μ) = (L'.compLpL p μ).comp (M'.compLpL p μ) := by
  rw [compLpL_comp_compLpL, compLpL_comp_compLpL, h]

end Comp

section Id

variable {α E 𝕜 : Type*} {_ : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}
  [NormedAddCommGroup E] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]

/-- Pushing an `Lp` function forward along the identity map returns it unchanged. -/
@[simp]
theorem id_compLp (f : Lp E p μ) : (ContinuousLinearMap.id 𝕜 E).compLp f = f := by
  ext1
  exact (ContinuousLinearMap.id 𝕜 E).coeFn_compLp f

/-- The `compLpL` operator of the identity map is the identity operator on `Lp`. -/
@[simp]
theorem id_compLpL [Fact (1 ≤ p)] :
    (ContinuousLinearMap.id 𝕜 E).compLpL p μ = ContinuousLinearMap.id 𝕜 (Lp E p μ) := by
  ext1 f
  exact id_compLp f

end Id

end ContinuousLinearMap

namespace ContinuousLinearMap

open MeasureTheory

variable {α 𝕜 E F G : Type*} [MeasurableSpace α] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {μ : Measure α} {p : ℝ≥0∞}

/-- Composition of continuous linear maps acts functorially on `Lp` classes. -/
@[simp]
theorem compLp_comp_linear (g : F →L[𝕜] G) (f : E →L[𝕜] F) (u : Lp E p μ) :
    g.compLp (f.compLp u) = (g.comp f).compLp u :=
  compLp_compLp g f u

end ContinuousLinearMap

namespace ContinuousLinearMap

open MeasureTheory

variable {α 𝕜 F : Type*} [MeasurableSpace α] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {μ : Measure α} {p : ENNReal} [Fact (1 ≤ p)]

/-- A scalar functional after rank-one `Lp` reconstruction is scalar multiplication. -/
theorem compLpL_toSpanSingleton (ℓ : F →L[𝕜] 𝕜) (v : F) (u : Lp 𝕜 p μ) :
    ℓ.compLpL p μ ((ContinuousLinearMap.toSpanSingleton 𝕜 v).compLpL p μ u) = ℓ v • u := by
  apply Lp.ext
  filter_upwards [ℓ.coeFn_compLpL
    ((ContinuousLinearMap.toSpanSingleton 𝕜 v).compLpL p μ u),
    (ContinuousLinearMap.toSpanSingleton 𝕜 v).coeFn_compLpL u,
    Lp.coeFn_smul (ℓ v) u] with x hℓ hv hs
  simp only [hℓ, hv, hs, ContinuousLinearMap.toSpanSingleton_apply, map_smul,
    Pi.smul_apply, smul_eq_mul, mul_comm]

omit [Fact (1 ≤ p)] in
/-- A scalar functional on rank-one reconstructed `Lp` data is scalar multiplication. -/
@[simp]
theorem compLp_comp_toSpanSingleton (ℓ : F →L[𝕜] 𝕜) (v : F) (u : Lp 𝕜 p μ) :
    (ℓ.comp (ContinuousLinearMap.toSpanSingleton 𝕜 v)).compLp u = ℓ v • u := by
  apply Lp.ext
  filter_upwards [(ℓ.comp (ContinuousLinearMap.toSpanSingleton 𝕜 v)).coeFn_compLp u,
    Lp.coeFn_smul (ℓ v) u] with x hℓ hs
  simp only [hℓ, hs, ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

end ContinuousLinearMap

noncomputable section

namespace LinearIsometry

variable {α 𝕜₁ 𝕜₂ E F : Type*} {m : MeasurableSpace α}
  [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ]
  [NormedAddCommGroup E] [NormedSpace 𝕜₁ E] [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- The continuous linear map underlying `LinearIsometry.compLpₗᵢ` is
`ContinuousLinearMap.compLpL`. -/
@[simp]
theorem toContinuousLinearMap_compLpₗᵢ (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : MeasureTheory.Measure α)
    (L : E →ₛₗᵢ[σ] F) :
    (L.compLpₗᵢ p μ).toContinuousLinearMap = L.toContinuousLinearMap.compLpL p μ := by
  ext1 f
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [L.coeFn_compLpₗᵢ (p := p) (μ := μ) f,
    L.toContinuousLinearMap.coeFn_compLpL (p := p) (μ := μ) f] with x h₁ h₂
  rw [coe_toContinuousLinearMap, h₁, h₂, coe_toContinuousLinearMap]

end LinearIsometry

namespace MeasureTheory.Lp

/-- On the zero measure, `Lp E p 0` has `0` as its unique element. -/
instance instUniqueZero {α E : Type*} {_ : MeasurableSpace α} [NormedAddCommGroup E]
    {p : ℝ≥0∞} : Unique (Lp E p (0 : Measure α)) where
  default := 0
  uniq _ := Lp.ext (by rw [Filter.EventuallyEq, ae_zero]; exact Filter.eventually_bot)

section RCLike

variable {α : Type*} {m : MeasurableSpace α} (𝕜 : Type*) [RCLike 𝕜]
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure α)

/-- Isometric scalar inclusion `Lp ℝ p μ →ₗᵢ[ℝ] Lp 𝕜 p μ` for an `RCLike` scalar field `𝕜`. -/
def ofRealLI : Lp ℝ p μ →ₗᵢ[ℝ] Lp 𝕜 p μ :=
  (RCLike.ofRealLI : ℝ →ₗᵢ[ℝ] 𝕜).compLpₗᵢ p μ

/-- Pointwise real-part operator `Lp 𝕜 p μ →L[ℝ] Lp ℝ p μ`. -/
def reCLM : Lp 𝕜 p μ →L[ℝ] Lp ℝ p μ :=
  (RCLike.reCLM : 𝕜 →L[ℝ] ℝ).compLpL p μ

/-- Pointwise imaginary-part operator `Lp 𝕜 p μ →L[ℝ] Lp ℝ p μ`. -/
def imCLM : Lp 𝕜 p μ →L[ℝ] Lp ℝ p μ :=
  (RCLike.imCLM : 𝕜 →L[ℝ] ℝ).compLpL p μ

variable {𝕜 p μ}

/-- `Lp.ofRealLI` casts representatives from `ℝ` to `𝕜` almost everywhere. -/
theorem coeFn_ofRealLI (f : Lp ℝ p μ) :
    ofRealLI 𝕜 p μ f =ᵐ[μ] fun x ↦ (f x : 𝕜) :=
  (RCLike.ofRealLI : ℝ →ₗᵢ[ℝ] 𝕜).coeFn_compLpₗᵢ f

/-- `Lp.reCLM` takes the real part almost everywhere. -/
theorem coeFn_reCLM (f : Lp 𝕜 p μ) :
    reCLM 𝕜 p μ f =ᵐ[μ] fun x ↦ RCLike.re (f x) :=
  (RCLike.reCLM : 𝕜 →L[ℝ] ℝ).coeFn_compLpL f

/-- `Lp.imCLM` takes the imaginary part almost everywhere. -/
theorem coeFn_imCLM (f : Lp 𝕜 p μ) :
    imCLM 𝕜 p μ f =ᵐ[μ] fun x ↦ RCLike.im (f x) :=
  (RCLike.imCLM : 𝕜 →L[ℝ] ℝ).coeFn_compLpL f

/-- Real part is a left inverse to `Lp.ofRealLI`. -/
@[simp]
theorem reCLM_ofRealLI (f : Lp ℝ p μ) : reCLM 𝕜 p μ (ofRealLI 𝕜 p μ f) = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_reCLM (ofRealLI 𝕜 p μ f), coeFn_ofRealLI (𝕜 := 𝕜) f] with x h₁ h₂
  rw [h₁, h₂, RCLike.ofReal_re]

/-- Imaginary part vanishes on `Lp.ofRealLI`. -/
@[simp]
theorem imCLM_ofRealLI (f : Lp ℝ p μ) : imCLM 𝕜 p μ (ofRealLI 𝕜 p μ f) = 0 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_imCLM (ofRealLI 𝕜 p μ f), coeFn_ofRealLI (𝕜 := 𝕜) f,
    coeFn_zero ℝ p μ] with x h₁ h₂ h₀
  rw [h₁, h₂, h₀, Pi.zero_apply, RCLike.ofReal_im]

/-- Over `ℝ`, `Lp.ofRealLI` is the identity linear isometry. -/
@[simp]
theorem ofRealLI_real : ofRealLI ℝ p μ = LinearIsometry.id := by
  ext f : 1
  refine Lp.ext ?_
  filter_upwards [coeFn_ofRealLI (𝕜 := ℝ) f] with x hx
  simpa using hx

/-- Over `ℝ`, `Lp.reCLM` is the identity continuous linear map. -/
@[simp]
theorem reCLM_real : reCLM ℝ p μ = ContinuousLinearMap.id ℝ (Lp ℝ p μ) := by
  ext f : 1
  refine Lp.ext ?_
  filter_upwards [coeFn_reCLM f] with x hx
  simpa using hx

/-- When `(RCLike.I : 𝕜) = 0`, `Lp.imCLM` is the zero operator. -/
theorem imCLM_eq_zero_of_I_eq_zero (hI : (RCLike.I : 𝕜) = 0) : imCLM 𝕜 p μ = 0 := by
  have him0 : (RCLike.imCLM : 𝕜 →L[ℝ] ℝ) = (0 : ℝ) • RCLike.imCLM := by
    ext z
    simp [RCLike.im_eq_zero hI]
  rw [imCLM, him0, ContinuousLinearMap.smul_compLpL]
  ext f : 1
  simp

/-- Over `ℝ`, `Lp.imCLM` is the zero operator. -/
@[simp]
theorem imCLM_real : imCLM ℝ p μ = 0 :=
  imCLM_eq_zero_of_I_eq_zero RCLike.I_to_real

/-- Multiplying by `RCLike.I` sends the real part to minus the imaginary part. -/
@[simp]
theorem reCLM_I_smul (f : Lp 𝕜 p μ) :
    reCLM 𝕜 p μ ((RCLike.I : 𝕜) • f) = -imCLM 𝕜 p μ f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_reCLM ((RCLike.I : 𝕜) • f), coeFn_smul (RCLike.I : 𝕜) f,
    coeFn_neg (imCLM 𝕜 p μ f), coeFn_imCLM f] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, Pi.smul_apply, Pi.neg_apply, h₄, smul_eq_mul, RCLike.I_mul_re]

/-- Real part vanishes on `I • ofRealLI g`. -/
theorem reCLM_I_smul_ofRealLI (g : Lp ℝ p μ) :
    reCLM 𝕜 p μ ((RCLike.I : 𝕜) • ofRealLI 𝕜 p μ g) = 0 := by
  simp

/-- Multiplying by `RCLike.I` scales the real part by `RCLike.im (RCLike.I : 𝕜)` in the imaginary
coordinate. -/
@[simp]
theorem imCLM_I_smul (f : Lp 𝕜 p μ) :
    imCLM 𝕜 p μ ((RCLike.I : 𝕜) • f) = RCLike.im (RCLike.I : 𝕜) • reCLM 𝕜 p μ f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_imCLM ((RCLike.I : 𝕜) • f), coeFn_smul (RCLike.I : 𝕜) f,
    coeFn_smul (RCLike.im (RCLike.I : 𝕜)) (reCLM 𝕜 p μ f), coeFn_reCLM f] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, Pi.smul_apply, Pi.smul_apply, h₄]
  simp [RCLike.mul_im]

/-- When `RCLike.im (RCLike.I : 𝕜) = 1`, `Lp.imCLM` recovers `g` from `I • ofRealLI g`. -/
theorem imCLM_I_smul_ofRealLI (hI : RCLike.im (RCLike.I : 𝕜) = 1) (g : Lp ℝ p μ) :
    imCLM 𝕜 p μ ((RCLike.I : 𝕜) • ofRealLI 𝕜 p μ g) = g := by
  simp [hI]

/-- Every `f : Lp 𝕜 p μ` decomposes into real and imaginary parts in `Lp ℝ p μ`. -/
theorem ofRealLI_reCLM_add_I_smul_imCLM (f : Lp 𝕜 p μ) :
    ofRealLI 𝕜 p μ (reCLM 𝕜 p μ f) + (RCLike.I : 𝕜) • ofRealLI 𝕜 p μ (imCLM 𝕜 p μ f) = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_add (ofRealLI 𝕜 p μ (reCLM 𝕜 p μ f))
      ((RCLike.I : 𝕜) • ofRealLI 𝕜 p μ (imCLM 𝕜 p μ f)),
    coeFn_ofRealLI (𝕜 := 𝕜) (reCLM 𝕜 p μ f), coeFn_reCLM f,
    coeFn_smul (RCLike.I : 𝕜) (ofRealLI 𝕜 p μ (imCLM 𝕜 p μ f)),
    coeFn_ofRealLI (𝕜 := 𝕜) (imCLM 𝕜 p μ f), coeFn_imCLM f] with x hadd hre₁ hre₂ hsmul him₁ him₂
  simp only [hadd, Pi.add_apply, hre₁, hre₂, hsmul, Pi.smul_apply, him₁, him₂, smul_eq_mul]
  rw [mul_comm, RCLike.re_add_im]

end RCLike

end MeasureTheory.Lp

end
