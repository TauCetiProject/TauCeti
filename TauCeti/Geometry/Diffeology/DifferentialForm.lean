/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Diffeology.Basic
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
public import TauCeti.Analysis.Calculus.DifferentialForm.Wedge

/-!
# Differential forms on diffeological spaces

A *differential `k`-form* on a diffeological space `X`, with values in a real normed space `F`
(`TauCeti.Diffeology.DifferentialForm X F k`), assigns to every plot `p : ℝⁿ → X` a smooth
`k`-form `ω_p` on `ℝⁿ`, compatibly with smooth reparametrization: `ω_(p ∘ f) = f^* ω_p` for every
smooth map `f : ℝᵐ → ℝⁿ`. The forms on plots are indexed by the plots only, so a form is
determined by its values on plots (`TauCeti.Diffeology.DifferentialForm.ext`).

Forms of each degree form a real vector space. The exterior derivative acts plotwise,
`(d ω)_p = d (ω_p)`, which is compatible with reparametrization because the flat exterior
derivative commutes with pullback (`extDeriv_pullback`); it satisfies `d ∘ d = 0`
(`TauCeti.Diffeology.DifferentialForm.extDeriv_extDeriv`). A smooth map `g : X → Y` pulls forms
back by `(g^* ω)_p = ω_(g ∘ p)`; pullback is functorial and commutes with the exterior derivative.
Real-valued forms have a plotwise wedge product (`TauCeti.Diffeology.DifferentialForm.wedge`),
which is bilinear, commutes with pullback and satisfies the Leibniz rule
`d (σ ∧ τ) = dσ ∧ τ + (-1) ^ k σ ∧ dτ`
(`TauCeti.Diffeology.DifferentialForm.toFun_extDeriv_wedge_apply`).

On a finite-dimensional real normed space `E` with its standard diffeology, plotwise forms are
exactly the smooth forms on `E`: a smooth form `ω` gives the plotwise form `p ↦ p^* ω`
(`TauCeti.Diffeology.DifferentialForm.ofForm`), every plotwise form arises in this way from a
unique smooth form (`TauCeti.Diffeology.DifferentialForm.toForm`), and the two exterior
derivatives agree (`TauCeti.Diffeology.DifferentialForm.extDeriv_ofForm`).

Plotwise forms are the forms on mapping spaces such as `C^∞(X, M)` with their functional
diffeology, where no manifold structure is available; fibre integration of forms on such spaces is
the basis of transgression.

## Main declarations

* `TauCeti.Diffeology.DifferentialForm`: differential forms on a diffeological space.
* `TauCeti.Diffeology.DifferentialForm.extDeriv`, `extDeriv_extDeriv`: the exterior derivative
  and `d ∘ d = 0`.
* `TauCeti.Diffeology.DifferentialForm.pullback`: pullback along a smooth map, with
  `pullback_id`, `pullback_comp` and `pullback_extDeriv`.
* `TauCeti.Diffeology.DifferentialForm.wedge`, `toFun_extDeriv_wedge_apply`: the wedge product
  of real-valued forms and the Leibniz rule.
* `TauCeti.Diffeology.DifferentialForm.ofForm`, `TauCeti.Diffeology.DifferentialForm.toForm`:
  the identification of plotwise forms on a finite-dimensional normed space with smooth forms.

## References

* P. Iglesias-Zemmour, *Diffeology*, Mathematical Surveys and Monographs **185**, American
  Mathematical Society (2013), Chapter 6 (differential forms, their pullbacks, exterior
  derivative and wedge product).
-/

public noncomputable section

open Function Set
open scoped ContDiff

namespace TauCeti.Diffeology

local macro:max "𝔼" noWs n:superscript(term) : term =>
  `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

variable (X : Type*) [DiffeologicalSpace X] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (k : ℕ)

/-- A **differential `k`-form** on a diffeological space `X` with values in a real normed space
`F`: for every plot `p : ℝⁿ → X`, a smooth `k`-form `toFun p hp` on `ℝⁿ`, such that for every
smooth map `f : ℝᵐ → ℝⁿ` the form on the plot `p ∘ f` is the pullback `f^* (toFun p hp)`. -/
structure DifferentialForm where
  /-- The form on the domain `ℝⁿ` of a plot `p : ℝⁿ → X`. -/
  toFun : ∀ {n : ℕ} (p : 𝔼ⁿ → X), _root_.Diffeology.IsPlot p → 𝔼ⁿ → 𝔼ⁿ [⋀^Fin k]→L[ℝ] F
  /-- The form on the domain of each plot is smooth. -/
  contDiff_toFun' : ∀ {n : ℕ} (p : 𝔼ⁿ → X) (hp : _root_.Diffeology.IsPlot p),
    ContDiff ℝ ∞ (toFun p hp)
  /-- The form on a reparametrized plot `p ∘ f` is the pullback along `f` of the form on `p`. -/
  toFun_comp' : ∀ {n m : ℕ} (p : 𝔼ⁿ → X) (hp : _root_.Diffeology.IsPlot p) (f : 𝔼ᵐ → 𝔼ⁿ)
    (hf : ContDiff ℝ ∞ f) (x : 𝔼ᵐ),
    toFun (p ∘ f) (_root_.Diffeology.isPlot_reparam hp hf) x =
      (toFun p hp (f x)).compContinuousLinearMap (fderiv ℝ f x)

namespace DifferentialForm

variable {X F k}

/-- The form on the domain of each plot is smooth. -/
theorem contDiff_toFun (σ : DifferentialForm X F k) {n : ℕ} (p : 𝔼ⁿ → X)
    (hp : _root_.Diffeology.IsPlot p) : ContDiff ℝ ∞ (σ.toFun p hp) :=
  σ.contDiff_toFun' p hp

/-- The form on a reparametrized plot `p ∘ f` is the pullback along `f` of the form on `p`. -/
theorem toFun_comp (σ : DifferentialForm X F k) {n m : ℕ} (p : 𝔼ⁿ → X)
    (hp : _root_.Diffeology.IsPlot p) (f : 𝔼ᵐ → 𝔼ⁿ) (hf : ContDiff ℝ ∞ f) (x : 𝔼ᵐ) :
    σ.toFun (p ∘ f) (_root_.Diffeology.isPlot_reparam hp hf) x =
      (σ.toFun p hp (f x)).compContinuousLinearMap (fderiv ℝ f x) :=
  σ.toFun_comp' p hp f hf x

/-- The forms on equal plots are equal. -/
theorem toFun_congr (σ : DifferentialForm X F k) {n : ℕ} {p q : 𝔼ⁿ → X}
    (hp : _root_.Diffeology.IsPlot p) (hq : _root_.Diffeology.IsPlot q) (h : p = q) :
    σ.toFun p hp = σ.toFun q hq := by
  subst h
  rfl

/-- Two forms are equal when they agree on every plot. -/
@[ext]
theorem ext {σ τ : DifferentialForm X F k}
    (h : ∀ {n : ℕ} (p : 𝔼ⁿ → X) (hp : _root_.Diffeology.IsPlot p), σ.toFun p hp = τ.toFun p hp) :
    σ = τ := by
  cases σ
  cases τ
  congr
  funext n p hp
  exact h p hp

/-! ### The vector space of forms -/

instance : Zero (DifferentialForm X F k) :=
  ⟨⟨fun _ _ _ ↦ 0, fun _ _ ↦ contDiff_const, fun _ _ _ _ _ ↦ by ext; simp⟩⟩

instance : Add (DifferentialForm X F k) :=
  ⟨fun σ τ ↦ ⟨fun p hp ↦ σ.toFun p hp + τ.toFun p hp,
    fun p hp ↦ (σ.contDiff_toFun p hp).add (τ.contDiff_toFun p hp),
    fun p hp f hf x ↦ by ext; simp [σ.toFun_comp p hp f hf, τ.toFun_comp p hp f hf]⟩⟩

instance : Neg (DifferentialForm X F k) :=
  ⟨fun σ ↦ ⟨fun p hp ↦ -σ.toFun p hp, fun p hp ↦ (σ.contDiff_toFun p hp).neg,
    fun p hp f hf x ↦ by ext; simp [σ.toFun_comp p hp f hf]⟩⟩

instance : Sub (DifferentialForm X F k) :=
  ⟨fun σ τ ↦ ⟨fun p hp ↦ σ.toFun p hp - τ.toFun p hp,
    fun p hp ↦ (σ.contDiff_toFun p hp).sub (τ.contDiff_toFun p hp),
    fun p hp f hf x ↦ by ext; simp [σ.toFun_comp p hp f hf, τ.toFun_comp p hp f hf]⟩⟩

section SMul

variable {R : Type*} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F]

instance : SMul R (DifferentialForm X F k) :=
  ⟨fun c σ ↦ ⟨fun p hp ↦ c • σ.toFun p hp, fun p hp ↦ (σ.contDiff_toFun p hp).const_smul c,
    fun p hp f hf x ↦ by ext; simp [σ.toFun_comp p hp f hf]⟩⟩

@[simp]
theorem toFun_smul (c : R) (σ : DifferentialForm X F k) {n : ℕ} (p : 𝔼ⁿ → X)
    (hp : _root_.Diffeology.IsPlot p) : (c • σ).toFun p hp = c • σ.toFun p hp :=
  (rfl)

end SMul

@[simp]
theorem toFun_zero {n : ℕ} (p : 𝔼ⁿ → X) (hp : _root_.Diffeology.IsPlot p) :
    (0 : DifferentialForm X F k).toFun p hp = 0 :=
  (rfl)

@[simp]
theorem toFun_add (σ τ : DifferentialForm X F k) {n : ℕ} (p : 𝔼ⁿ → X)
    (hp : _root_.Diffeology.IsPlot p) : (σ + τ).toFun p hp = σ.toFun p hp + τ.toFun p hp :=
  (rfl)

@[simp]
theorem toFun_neg (σ : DifferentialForm X F k) {n : ℕ} (p : 𝔼ⁿ → X)
    (hp : _root_.Diffeology.IsPlot p) : (-σ).toFun p hp = -σ.toFun p hp :=
  (rfl)

@[simp]
theorem toFun_sub (σ τ : DifferentialForm X F k) {n : ℕ} (p : 𝔼ⁿ → X)
    (hp : _root_.Diffeology.IsPlot p) : (σ - τ).toFun p hp = σ.toFun p hp - τ.toFun p hp :=
  (rfl)

instance : AddCommGroup (DifferentialForm X F k) where
  add_assoc _ _ _ := ext fun _ _ ↦ add_assoc _ _ _
  zero_add _ := ext fun _ _ ↦ zero_add _
  add_zero _ := ext fun _ _ ↦ add_zero _
  nsmul n σ := n • σ
  nsmul_zero _ := ext fun _ _ ↦ zero_smul ℕ _
  nsmul_succ _ _ := ext fun _ _ ↦ succ_nsmul _ _
  zsmul n σ := n • σ
  zsmul_zero' _ := ext fun _ _ ↦ zero_smul ℤ _
  zsmul_succ' _ _ := ext fun _ _ ↦ by simp [add_smul]
  zsmul_neg' _ _ := ext fun _ _ ↦ by simp [negSucc_zsmul, add_smul]
  neg_add_cancel _ := ext fun _ _ ↦ neg_add_cancel _
  add_comm _ _ := ext fun _ _ ↦ add_comm _ _
  sub_eq_add_neg _ _ := ext fun _ _ ↦ sub_eq_add_neg _ _

instance : Module ℝ (DifferentialForm X F k) where
  one_smul _ := ext fun _ _ ↦ one_smul ℝ _
  mul_smul _ _ _ := ext fun _ _ ↦ mul_smul _ _ _
  smul_zero _ := ext fun _ _ ↦ smul_zero _
  smul_add _ _ _ := ext fun _ _ ↦ smul_add _ _ _
  add_smul _ _ _ := ext fun _ _ ↦ add_smul _ _ _
  zero_smul _ := ext fun _ _ ↦ zero_smul ℝ _

/-! ### The exterior derivative -/

/-- The **exterior derivative** of a differential form on a diffeological space: on each plot, the
exterior derivative of the form on the domain of the plot. -/
def extDeriv (σ : DifferentialForm X F k) : DifferentialForm X F (k + 1) where
  toFun p hp := _root_.extDeriv (σ.toFun p hp)
  contDiff_toFun' p hp := contDiff_extDeriv (σ.contDiff_toFun p hp) (by simp)
  toFun_comp' p hp f hf x := by
    rw [funext (σ.toFun_comp p hp f hf)]
    exact extDeriv_pullback ((σ.contDiff_toFun p hp).differentiable (by simp) _) hf.contDiffAt
      (by simp)

@[simp]
theorem toFun_extDeriv (σ : DifferentialForm X F k) {n : ℕ} (p : 𝔼ⁿ → X)
    (hp : _root_.Diffeology.IsPlot p) :
    σ.extDeriv.toFun p hp = _root_.extDeriv (σ.toFun p hp) :=
  (rfl)

@[simp]
theorem extDeriv_add (σ τ : DifferentialForm X F k) :
    (σ + τ).extDeriv = σ.extDeriv + τ.extDeriv :=
  ext fun p hp ↦ funext fun x ↦ _root_.extDeriv_add
    ((σ.contDiff_toFun p hp).differentiable (by simp) x)
    ((τ.contDiff_toFun p hp).differentiable (by simp) x)

@[simp]
theorem extDeriv_smul (c : ℝ) (σ : DifferentialForm X F k) :
    (c • σ).extDeriv = c • σ.extDeriv :=
  ext fun p hp ↦ funext fun _ ↦ _root_.extDeriv_smul c (σ.toFun p hp)

/-- The exterior derivative as a linear map. -/
def extDerivₗ : DifferentialForm X F k →ₗ[ℝ] DifferentialForm X F (k + 1) where
  toFun σ := σ.extDeriv
  map_add' := extDeriv_add
  map_smul' := extDeriv_smul

@[simp]
theorem extDerivₗ_apply (σ : DifferentialForm X F k) : extDerivₗ σ = σ.extDeriv :=
  (rfl)

/-- `d ∘ d = 0` for differential forms on a diffeological space. -/
@[simp]
theorem extDeriv_extDeriv (σ : DifferentialForm X F k) : σ.extDeriv.extDeriv = 0 :=
  ext fun p hp ↦ _root_.extDeriv_extDeriv (σ.contDiff_toFun p hp) (by simp)

/-! ### Pullback -/

variable {Y Z : Type*} [DiffeologicalSpace Y] [DiffeologicalSpace Z]

/-- The **pullback** of a differential form on `Y` along a smooth map `g : X → Y`: on a plot `p`
of `X`, the form of the plot `g ∘ p` of `Y`. -/
def pullback (g : X → Y) (hg : _root_.Diffeology.DSmooth g) (σ : DifferentialForm Y F k) :
    DifferentialForm X F k where
  toFun p hp := σ.toFun (g ∘ p) (hg _ p hp)
  contDiff_toFun' p hp := σ.contDiff_toFun (g ∘ p) (hg _ p hp)
  toFun_comp' p hp f hf x := σ.toFun_comp (g ∘ p) (hg _ p hp) f hf x

@[simp]
theorem toFun_pullback (g : X → Y) (hg : _root_.Diffeology.DSmooth g)
    (σ : DifferentialForm Y F k) {n : ℕ} (p : 𝔼ⁿ → X) (hp : _root_.Diffeology.IsPlot p) :
    (σ.pullback g hg).toFun p hp = σ.toFun (g ∘ p) (hg _ p hp) :=
  (rfl)

/-- Pullback along the identity is the identity. -/
@[simp]
theorem pullback_id (σ : DifferentialForm X F k) :
    σ.pullback id _root_.Diffeology.dSmooth_id = σ :=
  (rfl)

/-- Pullback reverses composition of smooth maps. -/
theorem pullback_comp (g : X → Y) (hg : _root_.Diffeology.DSmooth g) (h : Y → Z)
    (hh : _root_.Diffeology.DSmooth h) (σ : DifferentialForm Z F k) :
    σ.pullback (h ∘ g) (hh.comp hg) = (σ.pullback h hh).pullback g hg :=
  (rfl)

@[simp]
theorem pullback_zero (g : X → Y) (hg : _root_.Diffeology.DSmooth g) :
    (0 : DifferentialForm Y F k).pullback g hg = 0 :=
  (rfl)

@[simp]
theorem pullback_add (g : X → Y) (hg : _root_.Diffeology.DSmooth g)
    (σ τ : DifferentialForm Y F k) :
    (σ + τ).pullback g hg = σ.pullback g hg + τ.pullback g hg :=
  (rfl)

@[simp]
theorem pullback_smul (g : X → Y) (hg : _root_.Diffeology.DSmooth g) (c : ℝ)
    (σ : DifferentialForm Y F k) : (c • σ).pullback g hg = c • σ.pullback g hg :=
  (rfl)

/-- Pullback commutes with the exterior derivative. -/
@[simp]
theorem pullback_extDeriv (g : X → Y) (hg : _root_.Diffeology.DSmooth g)
    (σ : DifferentialForm Y F k) : σ.extDeriv.pullback g hg = (σ.pullback g hg).extDeriv :=
  (rfl)

/-- Pullback along a smooth map, as a linear map. -/
def pullbackₗ (g : X → Y) (hg : _root_.Diffeology.DSmooth g) :
    DifferentialForm Y F k →ₗ[ℝ] DifferentialForm X F k where
  toFun σ := σ.pullback g hg
  map_add' := pullback_add g hg
  map_smul' := pullback_smul g hg

@[simp]
theorem pullbackₗ_apply (g : X → Y) (hg : _root_.Diffeology.DSmooth g)
    (σ : DifferentialForm Y F k) : pullbackₗ g hg σ = σ.pullback g hg :=
  (rfl)

/-! ### The wedge product of real-valued forms -/

section Wedge

variable {l : ℕ}

/-- The **wedge product** of real-valued differential forms on a diffeological space: on each plot,
the wedge product `ContinuousAlternatingMap.wedge` of the forms on the domain of the plot. -/
def wedge (σ : DifferentialForm X ℝ k) (τ : DifferentialForm X ℝ l) :
    DifferentialForm X ℝ (k + l) where
  toFun p hp x := (σ.toFun p hp x).wedge (τ.toFun p hp x)
  contDiff_toFun' p hp := (σ.contDiff_toFun p hp).wedge (τ.contDiff_toFun p hp)
  toFun_comp' p hp f hf x := by
    rw [σ.toFun_comp p hp f hf, τ.toFun_comp p hp f hf,
      ContinuousAlternatingMap.wedge_compContinuousLinearMap]

@[simp]
theorem toFun_wedge (σ : DifferentialForm X ℝ k) (τ : DifferentialForm X ℝ l) {n : ℕ}
    (p : 𝔼ⁿ → X) (hp : _root_.Diffeology.IsPlot p) :
    (σ.wedge τ).toFun p hp = fun x ↦ (σ.toFun p hp x).wedge (τ.toFun p hp x) :=
  (rfl)

@[simp]
theorem wedge_add_left (σ σ' : DifferentialForm X ℝ k) (τ : DifferentialForm X ℝ l) :
    (σ + σ').wedge τ = σ.wedge τ + σ'.wedge τ :=
  ext fun _ _ ↦ funext fun _ ↦ ContinuousAlternatingMap.wedge_add_left _ _ _

@[simp]
theorem wedge_add_right (σ : DifferentialForm X ℝ k) (τ τ' : DifferentialForm X ℝ l) :
    σ.wedge (τ + τ') = σ.wedge τ + σ.wedge τ' :=
  ext fun _ _ ↦ funext fun _ ↦ ContinuousAlternatingMap.wedge_add_right _ _ _

@[simp]
theorem wedge_smul_left (c : ℝ) (σ : DifferentialForm X ℝ k) (τ : DifferentialForm X ℝ l) :
    (c • σ).wedge τ = c • σ.wedge τ :=
  ext fun _ _ ↦ funext fun _ ↦ ContinuousAlternatingMap.wedge_smul_left _ _ _

@[simp]
theorem wedge_smul_right (c : ℝ) (σ : DifferentialForm X ℝ k) (τ : DifferentialForm X ℝ l) :
    σ.wedge (c • τ) = c • σ.wedge τ :=
  ext fun _ _ ↦ funext fun _ ↦ ContinuousAlternatingMap.wedge_smul_right _ _ _

/-- Pullback commutes with the wedge product. -/
@[simp]
theorem pullback_wedge {Y : Type*} [DiffeologicalSpace Y] (g : X → Y)
    (hg : _root_.Diffeology.DSmooth g) (σ : DifferentialForm Y ℝ k) (τ : DifferentialForm Y ℝ l) :
    (σ.wedge τ).pullback g hg = (σ.pullback g hg).wedge (τ.pullback g hg) :=
  (rfl)

/-- **The Leibniz rule** `d (σ ∧ τ) = dσ ∧ τ + (-1) ^ k • σ ∧ dτ` for a real-valued `k`-form `σ`,
evaluated on each plot. The degrees `k + 1 + l` and `k + (l + 1)` are identified with
`k + l + 1` by `Fin.cast`. -/
theorem toFun_extDeriv_wedge_apply (σ : DifferentialForm X ℝ k) (τ : DifferentialForm X ℝ l)
    {n : ℕ} (p : 𝔼ⁿ → X) (hp : _root_.Diffeology.IsPlot p) (x : 𝔼ⁿ)
    (v : Fin (k + l + 1) → 𝔼ⁿ) :
    (σ.wedge τ).extDeriv.toFun p hp x v =
      (σ.extDeriv.wedge τ).toFun p hp x (v ∘ Fin.cast (show k + 1 + l = k + l + 1 by omega)) +
        (-1 : ℝ) ^ k • (σ.wedge τ.extDeriv).toFun p hp x
          (v ∘ Fin.cast (show k + (l + 1) = k + l + 1 by omega)) := by
  simp only [toFun_extDeriv, toFun_wedge, ContinuousAlternatingMap.wedge_def]
  exact extDeriv_pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
    ((σ.contDiff_toFun p hp).differentiable (by simp) x)
    ((τ.contDiff_toFun p hp).differentiable (by simp) x) v

end Wedge

/-! ### Forms on a finite-dimensional normed space -/

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DiffeologicalSpace E]
  [_root_.Diffeology.IsContDiffCompatible E]

/-- The differential form on a normed space `E` with a compatible diffeology given by a smooth
flat form `σ`: on a plot `p`, the pullback `p^* σ`. -/
def ofForm (σ : E → E [⋀^Fin k]→L[ℝ] F) (hσ : ContDiff ℝ ∞ σ) : DifferentialForm E F k where
  toFun p _ x := (σ (p x)).compContinuousLinearMap (fderiv ℝ p x)
  contDiff_toFun' p hp := contDiff_iff_contDiffAt.2 fun x ↦
    ContDiffAt.differentialForm_pullback (hp.contDiff.contDiffAt.of_le (by simp)) hσ.contDiffAt
  toFun_comp' p hp f hf x := by
    rw [comp_apply, fderiv_comp x (hp.contDiff.differentiable (by simp) _)
      (hf.differentiable (by simp) _)]
    -- Composing an alternating map with `A ∘L B` is composing with `A`, then with `B`; both sides
    -- evaluate `σ (p (f x))` on the vectors `A (B vᵢ)`.
    rfl

@[simp]
theorem toFun_ofForm (σ : E → E [⋀^Fin k]→L[ℝ] F) (hσ : ContDiff ℝ ∞ σ) {n : ℕ} (p : 𝔼ⁿ → E)
    (hp : _root_.Diffeology.IsPlot p) (x : 𝔼ⁿ) :
    (ofForm σ hσ).toFun p hp x = (σ (p x)).compContinuousLinearMap (fderiv ℝ p x) :=
  (rfl)

/-- The exterior derivative of the plotwise form given by a smooth flat form `σ` is the plotwise
form given by the flat exterior derivative of `σ`. -/
theorem extDeriv_ofForm (σ : E → E [⋀^Fin k]→L[ℝ] F) (hσ : ContDiff ℝ ∞ σ) :
    (ofForm σ hσ).extDeriv = ofForm (_root_.extDeriv σ) (contDiff_extDeriv hσ (by simp)) :=
  ext fun p hp ↦ funext fun x ↦ extDeriv_pullback ((hσ.differentiable (by simp)) _)
    hp.contDiff.contDiffAt (by simp)

variable [FiniteDimensional ℝ E]

/-- The smooth flat form on a finite-dimensional normed space `E` underlying a differential form
on `E` with its standard diffeology. It is read off on the plot given by a linear
identification of `E` with a Euclidean space, and does not depend on that choice
(`TauCeti.Diffeology.DifferentialForm.ofForm_toForm`). -/
def toForm (σ : DifferentialForm E F k) : E → E [⋀^Fin k]→L[ℝ] F :=
  fun y ↦ (σ.toFun (toEuclidean (E := E)).symm
    (toEuclidean (E := E)).symm.contDiff.isPlot (toEuclidean y)).compContinuousLinearMap
      (toEuclidean (E := E) : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))

theorem toForm_apply (σ : DifferentialForm E F k) (y : E) :
    σ.toForm y = (σ.toFun (toEuclidean (E := E)).symm
      (toEuclidean (E := E)).symm.contDiff.isPlot (toEuclidean y)).compContinuousLinearMap
        (toEuclidean (E := E) : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
  (rfl)

/-- The flat form underlying a differential form on a finite-dimensional normed space is
smooth. -/
theorem contDiff_toForm (σ : DifferentialForm E F k) : ContDiff ℝ ∞ σ.toForm := by
  set e := toEuclidean (E := E)
  -- `σ.toForm` is the pullback along `e` of the form on the plot `e.symm`.
  have h : σ.toForm = fun y ↦
      (σ.toFun e.symm e.symm.contDiff.isPlot (e y)).compContinuousLinearMap (fderiv ℝ e y) := by
    funext y
    rw [e.fderiv, toForm_apply]
  rw [h]
  exact contDiff_iff_contDiffAt.2 fun y ↦ ContDiffAt.differentialForm_pullback (r := ∞)
    e.contDiff.contDiffAt (σ.contDiff_toFun _ _).contDiffAt

/-- A smooth flat form is recovered from the plotwise form it defines. -/
@[simp]
theorem toForm_ofForm (σ : E → E [⋀^Fin k]→L[ℝ] F) (hσ : ContDiff ℝ ∞ σ) :
    (ofForm σ hσ).toForm = σ := by
  funext y
  ext v
  simp [toForm_apply, ContinuousLinearEquiv.fderiv]

/-- Every differential form on a finite-dimensional normed space with its standard diffeology is
the plotwise form given by its underlying smooth flat form. -/
@[simp]
theorem ofForm_toForm (σ : DifferentialForm E F k) : ofForm σ.toForm σ.contDiff_toForm = σ := by
  ext n p hp x v
  set e := toEuclidean (E := E)
  have hp' : ContDiff ℝ ∞ (e ∘ p) := e.contDiff.comp hp.contDiff
  have key := σ.toFun_comp e.symm e.symm.contDiff.isPlot (e ∘ p) hp' x
  rw [σ.toFun_congr _ hp (by ext; simp [e])] at key
  rw [toFun_ofForm, key, fderiv_comp x e.differentiableAt (hp.contDiff.differentiable (by simp) x),
    ContinuousLinearEquiv.fderiv]
  simp [toForm_apply, e, comp_def]

/-- The flat form underlying the exterior derivative of a differential form on a
finite-dimensional normed space is the flat exterior derivative of its underlying flat form. -/
@[simp]
theorem toForm_extDeriv (σ : DifferentialForm E F k) :
    σ.extDeriv.toForm = _root_.extDeriv σ.toForm := by
  conv_lhs => rw [← σ.ofForm_toForm]
  rw [extDeriv_ofForm, toForm_ofForm]

end NormedSpace

end DifferentialForm

end TauCeti.Diffeology
