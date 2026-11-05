/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Analysis.Pseudodifferential.FrequencyCutoff

/-!
# Homogeneous symbols

A *homogeneous symbol of degree `m`* is a map `a : X × E → (V →L[ℂ] W)` of a position `x` and a
frequency `ξ` that is smooth away from `ξ = 0` and positively homogeneous of real degree `m` in
the frequency: `a (x, t • ξ) = t ^ m • a (x, ξ)` for every `t > 0`. These are the terms
`aₘ₋ⱼ` of a classical symbol `a ∼ ∑ⱼ χ(ξ) aₘ₋ⱼ(x, ξ)`; the leading one is its principal symbol.

A homogeneous term of degree `m` need not extend continuously to `ξ = 0` (think of
`ξ / ‖ξ‖`, of degree `0`), so its value there is a convention: `TauCeti.HomogeneousSymbol` fixes
it to be zero, which makes the carrier extensional on its coefficient, and `HomogeneousSymbol.mk'`
builds a homogeneous symbol from a function given only away from `ξ = 0`.

The file develops:

* the module structure on homogeneous symbols of a fixed degree, over every scalar ring acting
  on `V →L[ℂ] W` compatibly with `ℝ` (in particular `ℝ` and `ℂ`), and the pointwise
  composition `HomogeneousSymbol.comp`, which adds degrees;
* the derivatives `HomogeneousSymbol.spatialDeriv` in a position direction, which keeps the
  degree, and `HomogeneousSymbol.frequencyDeriv` in a frequency direction, which lowers it by
  one; iterating them gives every mixed partial derivative `∂ₓ^α ∂_ξ^β a`, homogeneous of degree
  `m - |β|` after transport along `HomogeneousSymbol.castDegree`, together with their product
  rule for `HomogeneousSymbol.comp`;
* the growth bound `HomogeneousSymbol.exists_norm_coefficient_le`: on a compact set of positions,
  `‖a (x, ξ)‖ ≤ C ‖ξ‖ ^ m`, for a proper (for instance finite-dimensional) frequency space;
  applied to the iterated derivatives above it bounds `‖∂ₓ^α ∂_ξ^β a (x, ξ)‖` by
  `C ‖ξ‖ ^ (m - |β|)`;
* smoothness of the cut-off term `χ(ξ) • a(x, ξ)` on the whole space, for a frequency cutoff
  `χ` (`HomogeneousSymbol.contDiff_smul_coefficient`).

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (1.17).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

open Set Filter Metric
open scoped ContDiff Topology

namespace TauCeti

/-- A homogeneous symbol of real degree `m`: a map `X × E → (V →L[ℂ] W)` of a position and a
frequency that vanishes at the zero frequency, is smooth away from it, and is positively
homogeneous of degree `m` in the frequency. -/
@[ext]
structure HomogeneousSymbol (X E V W : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (m : ℝ) where
  /-- The value at a position and a frequency. -/
  coefficient : X × E → V →L[ℂ] W
  zero_covector : ∀ x, coefficient (x, 0) = 0
  contDiffOn_coefficient : ContDiffOn ℝ ∞ coefficient {p | p.2 ≠ 0}
  homogeneous : ∀ x ξ (t : ℝ), 0 < t → coefficient (x, t • ξ) = t ^ m • coefficient (x, ξ)

attribute [simp] HomogeneousSymbol.zero_covector

namespace HomogeneousSymbol

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U] {m m' : ℝ}

/-- Homogeneous symbols are determined by their values at nonzero frequencies. -/
theorem ext_of_ne_zero {a b : HomogeneousSymbol X E V W m}
    (h : ∀ x ξ, ξ ≠ 0 → a.coefficient (x, ξ) = b.coefficient (x, ξ)) : a = b := by
  ext1
  funext ⟨x, ξ⟩
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  · exact h x ξ hξ

section Regularity

variable (a : HomogeneousSymbol X E V W m)

theorem contDiffAt_coefficient {p : X × E} (hp : p.2 ≠ 0) : ContDiffAt ℝ ∞ a.coefficient p :=
  a.contDiffOn_coefficient.contDiffAt ((isOpen_compl_singleton.preimage continuous_snd).mem_nhds hp)

theorem differentiableAt_coefficient {p : X × E} (hp : p.2 ≠ 0) :
    DifferentiableAt ℝ a.coefficient p :=
  (a.contDiffAt_coefficient hp).differentiableAt (by simp)

theorem continuousOn_coefficient : ContinuousOn a.coefficient {p | p.2 ≠ 0} :=
  a.contDiffOn_coefficient.continuousOn

end Regularity

section mk'

open Classical in
/-- The homogeneous symbol of degree `m` defined by a function `f` that is smooth and positively
homogeneous of degree `m` away from the zero frequency; its value at the zero frequency is set
to zero, whatever `f` does there. -/
noncomputable def mk' (f : X × E → V →L[ℂ] W) (hf : ContDiffOn ℝ ∞ f {p | p.2 ≠ 0})
    (hhom : ∀ x ξ, ξ ≠ 0 → ∀ t : ℝ, 0 < t → f (x, t • ξ) = t ^ m • f (x, ξ)) :
    HomogeneousSymbol X E V W m where
  coefficient p := if p.2 = 0 then 0 else f p
  zero_covector _ := by simp
  contDiffOn_coefficient := hf.congr fun _ hp ↦ by simp_all
  homogeneous x ξ t ht := by
    rcases eq_or_ne ξ 0 with rfl | hξ
    · simp
    · simp [hξ, smul_ne_zero ht.ne' hξ, hhom x ξ hξ t ht]

@[simp]
theorem coefficient_mk'_of_ne_zero (f : X × E → V →L[ℂ] W) (hf : ContDiffOn ℝ ∞ f {p | p.2 ≠ 0})
    (hhom : ∀ x ξ, ξ ≠ 0 → ∀ t : ℝ, 0 < t → f (x, t • ξ) = t ^ m • f (x, ξ)) {x : X} {ξ : E}
    (hξ : ξ ≠ 0) : (mk' f hf hhom).coefficient (x, ξ) = f (x, ξ) := by
  simp [mk', hξ]

/-- Rebuilding a homogeneous symbol from its own coefficient gives back the symbol. -/
@[simp]
theorem mk'_coefficient (a : HomogeneousSymbol X E V W m) :
    mk' a.coefficient a.contDiffOn_coefficient (fun x ξ _ t ht ↦ a.homogeneous x ξ t ht) = a :=
  ext_of_ne_zero fun _ _ hξ ↦ coefficient_mk'_of_ne_zero _ _ _ hξ

end mk'

/-! ### The vector space of homogeneous symbols of a fixed degree -/

instance : Zero (HomogeneousSymbol X E V W m) :=
  ⟨⟨0, fun _ ↦ rfl, contDiffOn_const, fun _ _ _ _ ↦ by simp⟩⟩

instance : Add (HomogeneousSymbol X E V W m) :=
  ⟨fun a b ↦ ⟨a.coefficient + b.coefficient, fun _ ↦ by simp,
    a.contDiffOn_coefficient.add b.contDiffOn_coefficient,
    fun x ξ t ht ↦ by simp [a.homogeneous x ξ t ht, b.homogeneous x ξ t ht]⟩⟩

instance : Neg (HomogeneousSymbol X E V W m) :=
  ⟨fun a ↦ ⟨-a.coefficient, fun _ ↦ by simp, a.contDiffOn_coefficient.neg,
    fun x ξ t ht ↦ by simp [a.homogeneous x ξ t ht]⟩⟩

instance : Sub (HomogeneousSymbol X E V W m) :=
  ⟨fun a b ↦ ⟨a.coefficient - b.coefficient, fun _ ↦ by simp,
    a.contDiffOn_coefficient.sub b.contDiffOn_coefficient,
    fun x ξ t ht ↦ by simp [a.homogeneous x ξ t ht, b.homogeneous x ξ t ht, smul_sub]⟩⟩

instance {R : Type*} [Semiring R] [Module R (V →L[ℂ] W)] [SMulCommClass ℝ R (V →L[ℂ] W)]
    [ContinuousConstSMul R (V →L[ℂ] W)] : SMul R (HomogeneousSymbol X E V W m) :=
  ⟨fun c a ↦ ⟨c • a.coefficient, fun _ ↦ by simp, a.contDiffOn_coefficient.const_smul c,
    fun x ξ t ht ↦ by
      simp only [Pi.smul_apply, a.homogeneous x ξ t ht]
      exact (smul_comm (t ^ m) c _).symm⟩⟩

@[simp]
theorem coefficient_zero : (0 : HomogeneousSymbol X E V W m).coefficient = 0 :=
  (rfl)

@[simp]
theorem coefficient_add (a b : HomogeneousSymbol X E V W m) :
    (a + b).coefficient = a.coefficient + b.coefficient :=
  (rfl)

@[simp]
theorem coefficient_neg (a : HomogeneousSymbol X E V W m) : (-a).coefficient = -a.coefficient :=
  (rfl)

@[simp]
theorem coefficient_sub (a b : HomogeneousSymbol X E V W m) :
    (a - b).coefficient = a.coefficient - b.coefficient :=
  (rfl)

@[simp]
theorem coefficient_smul {R : Type*} [Semiring R] [Module R (V →L[ℂ] W)]
    [SMulCommClass ℝ R (V →L[ℂ] W)] [ContinuousConstSMul R (V →L[ℂ] W)] (c : R)
    (a : HomogeneousSymbol X E V W m) : (c • a).coefficient = c • a.coefficient :=
  (rfl)

theorem coefficient_injective :
    Function.Injective (coefficient : HomogeneousSymbol X E V W m → X × E → V →L[ℂ] W) :=
  fun _ _ ↦ HomogeneousSymbol.ext

instance : AddCommGroup (HomogeneousSymbol X E V W m) :=
  coefficient_injective.addCommGroup _ coefficient_zero coefficient_add coefficient_neg
    coefficient_sub (fun _ _ ↦ coefficient_smul _ _) (fun _ _ ↦ coefficient_smul _ _)

instance {R : Type*} [Semiring R] [Module R (V →L[ℂ] W)] [SMulCommClass ℝ R (V →L[ℂ] W)]
    [ContinuousConstSMul R (V →L[ℂ] W)] : Module R (HomogeneousSymbol X E V W m) :=
  coefficient_injective.module R
    { toFun := coefficient, map_zero' := coefficient_zero, map_add' := coefficient_add }
    coefficient_smul

/-! ### Changing the degree -/

/-- Transport a homogeneous symbol along an equality of degrees, for instance to identify the
degrees `m' + m - 1` and `m' - 1 + m`, which are equal but not definitionally so. -/
def castDegree (h : m = m') (a : HomogeneousSymbol X E V W m) : HomogeneousSymbol X E V W m' where
  coefficient := a.coefficient
  zero_covector := a.zero_covector
  contDiffOn_coefficient := a.contDiffOn_coefficient
  homogeneous := h ▸ a.homogeneous

@[simp]
theorem coefficient_castDegree (h : m = m') (a : HomogeneousSymbol X E V W m) :
    (a.castDegree h).coefficient = a.coefficient :=
  (rfl)

@[simp]
theorem castDegree_rfl (a : HomogeneousSymbol X E V W m) : a.castDegree rfl = a :=
  (rfl)

@[simp]
theorem castDegree_castDegree {m'' : ℝ} (h : m = m') (h' : m' = m'')
    (a : HomogeneousSymbol X E V W m) :
    (a.castDegree h).castDegree h' = a.castDegree (h.trans h') :=
  (rfl)

/-! Transport along an equality of degrees commutes with the vector space operations. -/

@[simp]
theorem castDegree_zero (h : m = m') :
    (0 : HomogeneousSymbol X E V W m).castDegree h = 0 :=
  (rfl)

@[simp]
theorem castDegree_add (h : m = m') (a b : HomogeneousSymbol X E V W m) :
    (a + b).castDegree h = a.castDegree h + b.castDegree h :=
  (rfl)

@[simp]
theorem castDegree_neg (h : m = m') (a : HomogeneousSymbol X E V W m) :
    (-a).castDegree h = -a.castDegree h :=
  (rfl)

@[simp]
theorem castDegree_sub (h : m = m') (a b : HomogeneousSymbol X E V W m) :
    (a - b).castDegree h = a.castDegree h - b.castDegree h :=
  (rfl)

@[simp]
theorem castDegree_smul {R : Type*} [Semiring R] [Module R (V →L[ℂ] W)]
    [SMulCommClass ℝ R (V →L[ℂ] W)] [ContinuousConstSMul R (V →L[ℂ] W)] (h : m = m') (c : R)
    (a : HomogeneousSymbol X E V W m) : (c • a).castDegree h = c • a.castDegree h :=
  (rfl)

/-! ### Composition -/

/-- The pointwise composition of homogeneous symbols of degrees `m'` and `m` is a homogeneous
symbol of degree `m' + m`. -/
def comp (b : HomogeneousSymbol X E W U m') (a : HomogeneousSymbol X E V W m) :
    HomogeneousSymbol X E V U (m' + m) where
  coefficient p := (b.coefficient p).comp (a.coefficient p)
  zero_covector x := by simp
  contDiffOn_coefficient :=
    -- Composition of `ℂ`-linear maps, viewed as a continuous `ℝ`-bilinear map.
    ((((ContinuousLinearMap.compL ℂ V W U).bilinearRestrictScalars ℝ).contDiff.comp_contDiffOn
      b.contDiffOn_coefficient).clm_apply a.contDiffOn_coefficient).congr fun _ _ ↦ by simp
  homogeneous x ξ t ht := by
    ext v
    simp [b.homogeneous x ξ t ht, a.homogeneous x ξ t ht, smul_smul, Real.rpow_add ht, mul_comm]

@[simp]
theorem coefficient_comp (b : HomogeneousSymbol X E W U m') (a : HomogeneousSymbol X E V W m)
    (p : X × E) : (b.comp a).coefficient p = (b.coefficient p).comp (a.coefficient p) :=
  (rfl)

@[simp]
theorem comp_add (b : HomogeneousSymbol X E W U m') (a₁ a₂ : HomogeneousSymbol X E V W m) :
    b.comp (a₁ + a₂) = b.comp a₁ + b.comp a₂ := by
  ext1; funext p; simp [ContinuousLinearMap.comp_add]

@[simp]
theorem add_comp (b₁ b₂ : HomogeneousSymbol X E W U m') (a : HomogeneousSymbol X E V W m) :
    (b₁ + b₂).comp a = b₁.comp a + b₂.comp a := by
  ext1; funext p; simp [ContinuousLinearMap.add_comp]

@[simp]
theorem comp_zero (b : HomogeneousSymbol X E W U m') :
    b.comp (0 : HomogeneousSymbol X E V W m) = 0 := by
  ext1; funext p; simp

@[simp]
theorem zero_comp (a : HomogeneousSymbol X E V W m) :
    (0 : HomogeneousSymbol X E W U m').comp a = 0 := by
  ext1; funext p; simp

@[simp]
theorem comp_neg (b : HomogeneousSymbol X E W U m') (a : HomogeneousSymbol X E V W m) :
    b.comp (-a) = -b.comp a := by
  ext1; funext p; simp

@[simp]
theorem neg_comp (b : HomogeneousSymbol X E W U m') (a : HomogeneousSymbol X E V W m) :
    (-b).comp a = -b.comp a := by
  ext1; funext p; simp

@[simp]
theorem comp_sub (b : HomogeneousSymbol X E W U m') (a₁ a₂ : HomogeneousSymbol X E V W m) :
    b.comp (a₁ - a₂) = b.comp a₁ - b.comp a₂ := by
  ext1; funext p; simp [ContinuousLinearMap.comp_sub]

@[simp]
theorem sub_comp (b₁ b₂ : HomogeneousSymbol X E W U m') (a : HomogeneousSymbol X E V W m) :
    (b₁ - b₂).comp a = b₁.comp a - b₂.comp a := by
  ext1; funext p; simp [ContinuousLinearMap.sub_comp]

@[simp]
theorem comp_smul (c : ℂ) (b : HomogeneousSymbol X E W U m') (a : HomogeneousSymbol X E V W m) :
    b.comp (c • a) = c • b.comp a := by
  ext1; funext p; simp

@[simp]
theorem smul_comp (c : ℂ) (b : HomogeneousSymbol X E W U m') (a : HomogeneousSymbol X E V W m) :
    (c • b).comp a = c • b.comp a := by
  ext1; funext p; simp [ContinuousLinearMap.smul_comp]

/-- Composing with a transported symbol transports the composition. -/
@[simp]
theorem comp_castDegree {m'' : ℝ} (h : m = m'') (b : HomogeneousSymbol X E W U m')
    (a : HomogeneousSymbol X E V W m) :
    b.comp (a.castDegree h) = (b.comp a).castDegree (by rw [h]) :=
  (rfl)

/-- Composing a transported symbol transports the composition. -/
@[simp]
theorem castDegree_comp {m'' : ℝ} (h : m' = m'') (b : HomogeneousSymbol X E W U m')
    (a : HomogeneousSymbol X E V W m) :
    (b.castDegree h).comp a = (b.comp a).castDegree (by rw [h]) :=
  (rfl)

/-- Composition of homogeneous symbols is associative, up to transport of the degree. -/
theorem comp_assoc {U' : Type*} [NormedAddCommGroup U'] [NormedSpace ℂ U'] {m'' : ℝ}
    (c : HomogeneousSymbol X E U U' m'') (b : HomogeneousSymbol X E W U m')
    (a : HomogeneousSymbol X E V W m) :
    (c.comp b).comp a = (c.comp (b.comp a)).castDegree (add_assoc m'' m' m).symm :=
  (rfl)

/-! ### Spatial and frequency derivatives -/

section Deriv

variable (a : HomogeneousSymbol X E V W m)

/-- Differentiating the homogeneity relation: the derivative at `(x, t • ξ)` in the direction
`(u, t • w)` is `t ^ m` times the derivative at `(x, ξ)` in the direction `(u, w)`. -/
theorem fderiv_coefficient_smul {x : X} {ξ : E} (hξ : ξ ≠ 0) {t : ℝ} (ht : 0 < t) (u : X)
    (w : E) :
    fderiv ℝ a.coefficient (x, t • ξ) (u, t • w) =
      t ^ m • fderiv ℝ a.coefficient (x, ξ) (u, w) := by
  -- Differentiate `a ∘ L = t ^ m • a` for the linear map `L (x, ξ) = (x, t • ξ)`.
  set L : (X × E) →L[ℝ] (X × E) :=
    (ContinuousLinearMap.id ℝ X).prodMap (t • ContinuousLinearMap.id ℝ E)
  have hL : ∀ p, L p = (p.1, t • p.2) := fun _ ↦ by simp [L, Prod.map]
  have hcomp : a.coefficient ∘ L = t ^ m • a.coefficient := by
    funext p
    simp [hL, a.homogeneous p.1 p.2 t ht]
  have key := congrArg (fun g ↦ fderiv ℝ g (x, ξ) (u, w)) hcomp
  have hd : DifferentiableAt ℝ a.coefficient (L (x, ξ)) :=
    a.differentiableAt_coefficient (p := (x, t • ξ)) (smul_ne_zero ht.ne' hξ)
  rw [fderiv_comp _ hd L.differentiableAt, L.fderiv,
    fderiv_const_smul (a.differentiableAt_coefficient (p := (x, ξ)) hξ)] at key
  simpa [hL] using key

/-- Every directional derivative of a homogeneous symbol is smooth away from the zero
frequency. -/
theorem contDiffOn_fderiv_coefficient_apply (q : X × E) :
    ContDiffOn ℝ ∞ (fun p ↦ fderiv ℝ a.coefficient p q) {p | p.2 ≠ 0} :=
  (a.contDiffOn_coefficient.fderiv_of_isOpen (isOpen_compl_singleton.preimage continuous_snd)
    (by simp)).clm_apply contDiffOn_const

/-- The derivative of a homogeneous symbol in the spatial direction `v`; it is homogeneous of the
same degree. -/
noncomputable def spatialDeriv (v : X) : HomogeneousSymbol X E V W m :=
  mk' (fun p ↦ fderiv ℝ a.coefficient p (v, 0)) (a.contDiffOn_fderiv_coefficient_apply (v, 0))
    fun x ξ hξ t ht ↦ by simpa using a.fderiv_coefficient_smul hξ ht v 0

/-- The derivative of a homogeneous symbol of degree `m` in the frequency direction `w`; it is
homogeneous of degree `m - 1`. -/
noncomputable def frequencyDeriv (w : E) : HomogeneousSymbol X E V W (m - 1) :=
  mk' (fun p ↦ fderiv ℝ a.coefficient p (0, w)) (a.contDiffOn_fderiv_coefficient_apply (0, w))
    fun x ξ hξ t ht ↦ by
      have h := a.fderiv_coefficient_smul (x := x) hξ ht 0 w
      have h0 : ((0 : X), t • w) = t • ((0 : X), w) := by simp
      rw [h0, ContinuousLinearMap.map_smul] at h
      simp [Real.rpow_sub_one ht.ne', div_eq_inv_mul, mul_smul, ← h, ht.ne']

/-- At a nonzero frequency, the spatial derivative is the derivative of the coefficient in the
direction `(v, 0)`. -/
theorem coefficient_spatialDeriv_eq_fderiv (v : X) {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    (a.spatialDeriv v).coefficient (x, ξ) = fderiv ℝ a.coefficient (x, ξ) (v, 0) :=
  coefficient_mk'_of_ne_zero _ _ _ hξ

/-- At a nonzero frequency, the frequency derivative is the derivative of the coefficient in the
direction `(0, w)`. -/
theorem coefficient_frequencyDeriv_eq_fderiv (w : E) {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    (a.frequencyDeriv w).coefficient (x, ξ) = fderiv ℝ a.coefficient (x, ξ) (0, w) :=
  coefficient_mk'_of_ne_zero _ _ _ hξ

/-- At a nonzero frequency, the spatial derivative is the partial derivative in the position. -/
@[simp]
theorem coefficient_spatialDeriv (v : X) {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    (a.spatialDeriv v).coefficient (x, ξ) = fderiv ℝ (fun y ↦ a.coefficient (y, ξ)) x v := by
  have h : HasFDerivAt (fun y ↦ a.coefficient (y, ξ))
      ((fderiv ℝ a.coefficient (x, ξ)).comp (ContinuousLinearMap.inl ℝ X E)) x :=
    (a.differentiableAt_coefficient (p := (x, ξ)) hξ).hasFDerivAt.comp x
      (hasFDerivAt_prodMk_left x ξ)
  rw [coefficient_spatialDeriv_eq_fderiv _ _ hξ, h.fderiv]
  simp

/-- At a nonzero frequency, the frequency derivative is the partial derivative in the
frequency. -/
@[simp]
theorem coefficient_frequencyDeriv (w : E) {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    (a.frequencyDeriv w).coefficient (x, ξ) = fderiv ℝ (fun η ↦ a.coefficient (x, η)) ξ w := by
  have h : HasFDerivAt (fun η ↦ a.coefficient (x, η))
      ((fderiv ℝ a.coefficient (x, ξ)).comp (ContinuousLinearMap.inr ℝ X E)) ξ :=
    (a.differentiableAt_coefficient (p := (x, ξ)) hξ).hasFDerivAt.comp ξ
      (hasFDerivAt_prodMk_right x ξ)
  rw [coefficient_frequencyDeriv_eq_fderiv _ _ hξ, h.fderiv]
  simp

/-! The spatial and frequency derivatives are linear in the symbol and in the direction. -/

@[simp]
theorem add_spatialDeriv (b : HomogeneousSymbol X E V W m) (v : X) :
    (a + b).spatialDeriv v = a.spatialDeriv v + b.spatialDeriv v :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [coefficient_spatialDeriv_eq_fderiv _ _ hξ,
      fderiv_add (a.differentiableAt_coefficient (p := (x, ξ)) hξ)
        (b.differentiableAt_coefficient (p := (x, ξ)) hξ)]

@[simp]
theorem smul_spatialDeriv {R : Type*} [Semiring R] [Module R (V →L[ℂ] W)]
    [SMulCommClass ℝ R (V →L[ℂ] W)] [ContinuousConstSMul R (V →L[ℂ] W)] (c : R) (v : X) :
    (c • a).spatialDeriv v = c • a.spatialDeriv v :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [coefficient_spatialDeriv_eq_fderiv _ _ hξ,
      fderiv_const_smul (a.differentiableAt_coefficient (p := (x, ξ)) hξ)]

@[simp]
theorem neg_spatialDeriv (v : X) : (-a).spatialDeriv v = -a.spatialDeriv v :=
  ext_of_ne_zero fun x ξ hξ ↦ by simp [coefficient_spatialDeriv_eq_fderiv _ _ hξ, fderiv_neg]

@[simp]
theorem sub_spatialDeriv (b : HomogeneousSymbol X E V W m) (v : X) :
    (a - b).spatialDeriv v = a.spatialDeriv v - b.spatialDeriv v :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [coefficient_spatialDeriv_eq_fderiv _ _ hξ,
      fderiv_sub (a.differentiableAt_coefficient (p := (x, ξ)) hξ)
        (b.differentiableAt_coefficient (p := (x, ξ)) hξ)]

@[simp]
theorem zero_spatialDeriv (v : X) : (0 : HomogeneousSymbol X E V W m).spatialDeriv v = 0 :=
  ext_of_ne_zero fun x ξ hξ ↦ by simp [coefficient_spatialDeriv_eq_fderiv _ _ hξ]

@[simp]
theorem spatialDeriv_add (v v' : X) :
    a.spatialDeriv (v + v') = a.spatialDeriv v + a.spatialDeriv v' :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [coefficient_spatialDeriv_eq_fderiv _ _ hξ, ← map_add]

@[simp]
theorem spatialDeriv_smul (c : ℝ) (v : X) : a.spatialDeriv (c • v) = c • a.spatialDeriv v :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [coefficient_spatialDeriv_eq_fderiv _ _ hξ, ← map_smul]

@[simp]
theorem spatialDeriv_zero : a.spatialDeriv 0 = 0 :=
  ext_of_ne_zero fun x ξ hξ ↦ by simp [coefficient_spatialDeriv_eq_fderiv _ _ hξ, Prod.mk_zero_zero]

@[simp]
theorem add_frequencyDeriv (b : HomogeneousSymbol X E V W m) (w : E) :
    (a + b).frequencyDeriv w = a.frequencyDeriv w + b.frequencyDeriv w :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [coefficient_frequencyDeriv_eq_fderiv _ _ hξ,
      fderiv_add (a.differentiableAt_coefficient (p := (x, ξ)) hξ)
        (b.differentiableAt_coefficient (p := (x, ξ)) hξ)]

@[simp]
theorem smul_frequencyDeriv {R : Type*} [Semiring R] [Module R (V →L[ℂ] W)]
    [SMulCommClass ℝ R (V →L[ℂ] W)] [ContinuousConstSMul R (V →L[ℂ] W)] (c : R) (w : E) :
    (c • a).frequencyDeriv w = c • a.frequencyDeriv w :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [coefficient_frequencyDeriv_eq_fderiv _ _ hξ,
      fderiv_const_smul (a.differentiableAt_coefficient (p := (x, ξ)) hξ)]

@[simp]
theorem neg_frequencyDeriv (w : E) : (-a).frequencyDeriv w = -a.frequencyDeriv w :=
  ext_of_ne_zero fun x ξ hξ ↦ by simp [coefficient_frequencyDeriv_eq_fderiv _ _ hξ, fderiv_neg]

@[simp]
theorem sub_frequencyDeriv (b : HomogeneousSymbol X E V W m) (w : E) :
    (a - b).frequencyDeriv w = a.frequencyDeriv w - b.frequencyDeriv w :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [coefficient_frequencyDeriv_eq_fderiv _ _ hξ,
      fderiv_sub (a.differentiableAt_coefficient (p := (x, ξ)) hξ)
        (b.differentiableAt_coefficient (p := (x, ξ)) hξ)]

@[simp]
theorem zero_frequencyDeriv (w : E) :
    (0 : HomogeneousSymbol X E V W m).frequencyDeriv w = 0 :=
  ext_of_ne_zero fun x ξ hξ ↦ by simp [coefficient_frequencyDeriv_eq_fderiv _ _ hξ]

@[simp]
theorem frequencyDeriv_add (w w' : E) :
    a.frequencyDeriv (w + w') = a.frequencyDeriv w + a.frequencyDeriv w' :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [coefficient_frequencyDeriv_eq_fderiv _ _ hξ, ← map_add]

@[simp]
theorem frequencyDeriv_smul (c : ℝ) (w : E) :
    a.frequencyDeriv (c • w) = c • a.frequencyDeriv w :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [coefficient_frequencyDeriv_eq_fderiv _ _ hξ, ← map_smul]

@[simp]
theorem frequencyDeriv_zero : a.frequencyDeriv 0 = 0 :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [coefficient_frequencyDeriv_eq_fderiv _ _ hξ, Prod.mk_zero_zero]

/-! The derivatives commute with transport along an equality of degrees. -/

@[simp]
theorem spatialDeriv_castDegree (h : m = m') (v : X) :
    (a.castDegree h).spatialDeriv v = (a.spatialDeriv v).castDegree h := by
  subst h; rfl

@[simp]
theorem frequencyDeriv_castDegree (h : m = m') (w : E) :
    (a.castDegree h).frequencyDeriv w = (a.frequencyDeriv w).castDegree (by rw [h]) := by
  subst h; rfl

end Deriv

/-! ### The product rule for composition -/

section CompDeriv

variable (b : HomogeneousSymbol X E W U m') (a : HomogeneousSymbol X E V W m)

/-- The product rule: away from the zero frequency, the derivative of the composition `b ∘ a` in
the direction `q` is `b' q ∘ a + b ∘ a' q`. -/
theorem fderiv_coefficient_comp {p : X × E} (hp : p.2 ≠ 0) (q : X × E) :
    fderiv ℝ (b.comp a).coefficient p q =
      (fderiv ℝ b.coefficient p q).comp (a.coefficient p) +
        (b.coefficient p).comp (fderiv ℝ a.coefficient p q) := by
  -- Composition of `ℂ`-linear maps, viewed as a continuous `ℝ`-bilinear map.
  have h := ((ContinuousLinearMap.compL ℂ V W U).bilinearRestrictScalars ℝ).fderiv_of_bilinear
    (b.differentiableAt_coefficient hp) (a.differentiableAt_coefficient hp)
  rw [funext (coefficient_comp b a)]
  simpa [add_comm] using congrArg (fun L ↦ L q) h

/-- The product rule for the spatial derivative of a composition. -/
theorem spatialDeriv_comp (v : X) :
    (b.comp a).spatialDeriv v = (b.spatialDeriv v).comp a + b.comp (a.spatialDeriv v) :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [coefficient_spatialDeriv_eq_fderiv _ _ hξ, fderiv_coefficient_comp b a (p := (x, ξ)) hξ]

/-- The product rule for the frequency derivative of a composition. The degrees `m' - 1 + m`
and `m' + (m - 1)` of the two terms are transported to the degree `m' + m - 1` of the left side,
since they are equal but not definitionally so. -/
theorem frequencyDeriv_comp (w : E) :
    (b.comp a).frequencyDeriv w =
      ((b.frequencyDeriv w).comp a).castDegree (by ring) +
        (b.comp (a.frequencyDeriv w)).castDegree (by ring) :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [coefficient_frequencyDeriv_eq_fderiv _ _ hξ, fderiv_coefficient_comp b a (p := (x, ξ)) hξ]

end CompDeriv

/-! ### Growth bounds and the cut-off term -/

section Growth

variable (a : HomogeneousSymbol X E V W m)

/-- **Growth of a homogeneous symbol.** On a compact set of positions, a homogeneous symbol of
degree `m` on a proper (for instance finite-dimensional) frequency space satisfies
`‖a (x, ξ)‖ ≤ C ‖ξ‖ ^ m`. -/
theorem exists_norm_coefficient_le [ProperSpace E] {K : Set X} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ‖a.coefficient (x, ξ)‖ ≤ C * ‖ξ‖ ^ m := by
  -- `a` is bounded on the compact set `K × sphere 0 1`, and homogeneity rescales to it.
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_sphere (0 : E) 1)).exists_bound_of_continuousOn
    (a.continuousOn_coefficient.mono fun p hp ↦ by
      rintro h
      simpa [h] using (mem_prod.1 hp).2)
  refine ⟨max C 0, le_max_right _ _, fun x hx ξ ↦ ?_⟩
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simpa using mul_nonneg (le_max_right C 0) (Real.rpow_nonneg (norm_nonneg (0 : E)) m)
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hs : ‖ξ‖⁻¹ • ξ ∈ sphere (0 : E) 1 := by simp [norm_smul, hn.ne']
  have h1 : a.coefficient (x, ξ) = ‖ξ‖ ^ m • a.coefficient (x, ‖ξ‖⁻¹ • ξ) := by
    rw [← a.homogeneous _ _ _ hn, smul_inv_smul₀ hn.ne']
  rw [h1, norm_smul, Real.norm_of_nonneg (by positivity), mul_comm]
  exact mul_le_mul_of_nonneg_right ((hC (x, _) (mk_mem_prod hx hs)).trans (le_max_left _ _))
    (by positivity)

/-- For a frequency cutoff `χ`, the cut-off term `χ(ξ) • a(x, ξ)` is smooth on the whole space,
including the zero frequency. -/
theorem contDiff_smul_coefficient (χ : FrequencyCutoff E) :
    ContDiff ℝ ∞ fun p : X × E ↦ χ p.2 • a.coefficient p := by
  rw [contDiff_iff_contDiffAt]
  intro p
  rcases eq_or_ne p.2 0 with h | h
  · -- Near the zero frequency the cutoff, hence the product, vanishes identically.
    refine (contDiffAt_const (c := (0 : V →L[ℂ] W))).congr_of_eventuallyEq ?_
    filter_upwards [(continuous_snd.tendsto p).eventually
      (χ.eventuallyEq_zero_of_norm_lt_one (ξ := p.2) (by simp [h]))] with q hq
    rw [Pi.zero_apply] at hq
    simp [hq]
  · exact ((χ.contDiff.comp contDiff_snd).contDiffAt).smul (a.contDiffAt_coefficient h)

end Growth

end HomogeneousSymbol

end TauCeti
