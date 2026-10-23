/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.Algebra.Group.UCB.Translation

/-!
# Complex-valued bounded uniformly continuous functions

Bekka, de la Harpe and Valette define invariant means on complex-valued functions. For a
topological group `G`, `TauCeti.complexUCB G` is the complex subalgebra of `G →ᵇ ℂ` of functions
`f` satisfying the condition that defines the real space `TauCeti.UCB G`,

```text
∀ ε > 0,  ∀ᶠ u in 𝓝 1,  ∀ x,  ‖f (u * x) - f x‖ < ε.
```

A complex function satisfies this condition exactly when its real and imaginary parts do, so
`TauCeti.ComplexUCB G` is the complexification of `UCB G`: every `f` decomposes as
`f = ofReal (re f) + I • ofReal (im f)`. Left translation `(L_g f)(x) = f (g⁻¹ * x)` acts on
`ComplexUCB G` by complex linear isometries, compatibly with `re`, `im` and `ofReal`. This is
what transports means, and their left invariance, between the real and the complex function
spaces.

## Main definitions

* `TauCeti.complexUCB G`: the subalgebra of `G →ᵇ ℂ` defined by the condition above, the case
  `𝕜 = ℂ` of `TauCeti.ucbSubalgebra 𝕜 G`.
* `TauCeti.ComplexUCB G`: its carrier type, a complex normed algebra.
* `TauCeti.ComplexUCB.re`, `TauCeti.ComplexUCB.im`: the real and imaginary parts, as real linear
  maps to `UCB G`.
* `TauCeti.ComplexUCB.ofReal`: a real function regarded as a complex function, as a real algebra
  homomorphism from `UCB G`.
* `TauCeti.ComplexUCB.leftTranslation`: `g ↦ L_g`, with `L_g f = f (g⁻¹ * ·)`.

## Main results

* `TauCeti.mem_complexUCB_iff_tendsto`: the condition says that the left-multiplication orbit
  `u ↦ f (u * ·)` tends to `f` in supremum norm as `u → 1`.
* `TauCeti.mem_complexUCB_iff_re_im`: a complex function lies in `complexUCB G` exactly when its
  real and imaginary parts lie in `ucb G`.
* `TauCeti.ComplexUCB.ofReal_re_add_I_smul_ofReal_im`: `f = ofReal (re f) + I • ofReal (im f)`.
* `TauCeti.ComplexUCB.re_leftTranslation`, `TauCeti.ComplexUCB.im_leftTranslation`,
  `TauCeti.ComplexUCB.leftTranslation_ofReal`: left translation commutes with `re`, `im` and
  `ofReal`.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix A.3 and
  Definition G.1.4.
-/

public section

noncomputable section

open Filter Topology Complex
open scoped BoundedContinuousFunction

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (G) in
/-- The complex bounded continuous functions `f` on `G` such that `f (u * x)` is uniformly close
to `f x` for all `u` near `1`, as a subalgebra of `G →ᵇ ℂ`. -/
@[expose]
def complexUCB : Subalgebra ℂ (G →ᵇ ℂ) :=
  ucbSubalgebra ℂ G

variable (G) in
/-- The complex normed algebra of bounded complex functions on `G` that are uniformly continuous
under small left multiplication, with the supremum norm and algebra operations of `G →ᵇ ℂ`. -/
abbrev ComplexUCB : Type _ := complexUCB G

variable (G) in
/-- `complexUCB G` is the case `𝕜 = ℂ` of `ucbSubalgebra 𝕜 G`. -/
theorem complexUCB_eq_ucbSubalgebra : complexUCB G = ucbSubalgebra ℂ G :=
  rfl

/-- The defining condition of `complexUCB G`. -/
theorem mem_complexUCB_iff {f : G →ᵇ ℂ} :
    f ∈ complexUCB G ↔ ∀ ε > 0, ∀ᶠ u in 𝓝 (1 : G), ∀ x, ‖f (u * x) - f x‖ < ε := by
  rw [complexUCB_eq_ucbSubalgebra, mem_ucbSubalgebra_iff]

/-- Membership in `complexUCB G` says that `u ↦ f (u * ·)` tends to `f` in supremum norm as
`u → 1`. -/
theorem mem_complexUCB_iff_tendsto {f : G →ᵇ ℂ} :
    f ∈ complexUCB G ↔
      Tendsto (fun u => f.compContinuous (ContinuousMap.mulLeft u)) (𝓝 1) (𝓝 f) := by
  rw [complexUCB_eq_ucbSubalgebra, mem_ucbSubalgebra_iff_tendsto]

/-- Postcomposing a function in `complexUCB G` with a real linear map `ℂ → ℝ`, such as the real or
imaginary part, gives a function in `ucb G`. -/
theorem compLeftContinuousBounded_mem_ucb (L : ℂ →L[ℝ] ℝ) {f : G →ᵇ ℂ}
    (hf : f ∈ complexUCB G) : L.compLeftContinuousBounded G f ∈ ucb G := by
  rw [complexUCB_eq_ucbSubalgebra] at hf
  rw [ucb_eq_ucbSubalgebra]
  exact compLeftContinuousBounded_mem_ucbSubalgebra L hf

/-- Postcomposing a function in `ucb G` with a real linear map `ℝ → ℂ`, such as the inclusion
`ℝ → ℂ`, gives a function in `complexUCB G`. -/
theorem compLeftContinuousBounded_mem_complexUCB (L : ℝ →L[ℝ] ℂ) {f : G →ᵇ ℝ}
    (hf : f ∈ ucb G) : L.compLeftContinuousBounded G f ∈ complexUCB G := by
  rw [ucb_eq_ucbSubalgebra] at hf
  rw [complexUCB_eq_ucbSubalgebra]
  exact compLeftContinuousBounded_mem_ucbSubalgebra L hf

/-- A complex function lies in `complexUCB G` exactly when its real and imaginary parts lie in
`ucb G`. -/
theorem mem_complexUCB_iff_re_im {f : G →ᵇ ℂ} :
    f ∈ complexUCB G ↔
      reCLM.compLeftContinuousBounded G f ∈ ucb G ∧
        imCLM.compLeftContinuousBounded G f ∈ ucb G := by
  refine ⟨fun hf => ⟨compLeftContinuousBounded_mem_ucb _ hf,
    compLeftContinuousBounded_mem_ucb _ hf⟩, fun ⟨hre, him⟩ => ?_⟩
  have h : f = ofRealCLM.compLeftContinuousBounded G (reCLM.compLeftContinuousBounded G f) +
      I • ofRealCLM.compLeftContinuousBounded G (imCLM.compLeftContinuousBounded G f) := by
    ext x
    simp [mul_comm I]
  rw [h]
  exact add_mem (compLeftContinuousBounded_mem_complexUCB _ hre)
    (Subalgebra.smul_mem _ (compLeftContinuousBounded_mem_complexUCB _ him) _)

namespace ComplexUCB

/-- Two elements of `ComplexUCB G` are equal when they agree at every point. -/
@[ext]
theorem ext {f g : ComplexUCB G} (h : ∀ x, (f : G →ᵇ ℂ) x = (g : G →ᵇ ℂ) x) : f = g :=
  Subtype.ext (BoundedContinuousFunction.ext h)

/-! ### Real and imaginary parts -/

/-- The real part `x ↦ (f x).re` of a function in `ComplexUCB G`, as a real linear map to
`UCB G`. -/
def re : ComplexUCB G →ₗ[ℝ] UCB G where
  toFun f := ⟨reCLM.compLeftContinuousBounded G f, compLeftContinuousBounded_mem_ucb _ f.2⟩
  map_add' _ _ := UCB.ext fun _ => by simp
  map_smul' _ _ := UCB.ext fun _ => by simp

/-- The imaginary part `x ↦ (f x).im` of a function in `ComplexUCB G`, as a real linear map to
`UCB G`. -/
def im : ComplexUCB G →ₗ[ℝ] UCB G where
  toFun f := ⟨imCLM.compLeftContinuousBounded G f, compLeftContinuousBounded_mem_ucb _ f.2⟩
  map_add' _ _ := UCB.ext fun _ => by simp
  map_smul' _ _ := UCB.ext fun _ => by simp

/-- A real function in `UCB G`, regarded as a complex function, as a real algebra homomorphism to
`ComplexUCB G`. -/
def ofReal : UCB G →ₐ[ℝ] ComplexUCB G where
  toFun f := ⟨ofRealCLM.compLeftContinuousBounded G f,
    compLeftContinuousBounded_mem_complexUCB _ f.2⟩
  map_one' := ext fun _ => by simp
  map_mul' _ _ := ext fun _ => by simp
  map_zero' := ext fun _ => by simp
  map_add' _ _ := ext fun _ => by simp
  commutes' _ := ext fun _ => by simp [Algebra.algebraMap_eq_smul_one]

@[simp]
theorem re_apply (f : ComplexUCB G) (x : G) :
    (re f : G →ᵇ ℝ) x = ((f : G →ᵇ ℂ) x).re :=
  (rfl)

@[simp]
theorem im_apply (f : ComplexUCB G) (x : G) :
    (im f : G →ᵇ ℝ) x = ((f : G →ᵇ ℂ) x).im :=
  (rfl)

@[simp]
theorem ofReal_apply (f : UCB G) (x : G) :
    (ofReal f : G →ᵇ ℂ) x = ((f : G →ᵇ ℝ) x : ℂ) :=
  (rfl)

@[simp]
theorem re_ofReal (f : UCB G) : re (ofReal f) = f :=
  UCB.ext fun _ => by simp

@[simp]
theorem im_ofReal (f : UCB G) : im (ofReal f) = 0 :=
  UCB.ext fun _ => by simp

theorem ofReal_injective : Function.Injective (ofReal : UCB G → ComplexUCB G) :=
  Function.LeftInverse.injective re_ofReal

/-- The real part of `c • f` is `c.re • re f - c.im • im f`. -/
@[simp]
theorem re_smul (c : ℂ) (f : ComplexUCB G) : re (c • f) = c.re • re f - c.im • im f :=
  UCB.ext fun _ => by simp

/-- The imaginary part of `c • f` is `c.re • im f + c.im • re f`. -/
@[simp]
theorem im_smul (c : ℂ) (f : ComplexUCB G) : im (c • f) = c.re • im f + c.im • re f :=
  UCB.ext fun _ => by simp

@[simp]
theorem re_one : re (1 : ComplexUCB G) = 1 := by
  simpa using re_ofReal (1 : UCB G)

@[simp]
theorem im_one : im (1 : ComplexUCB G) = 0 := by
  simpa using im_ofReal (1 : UCB G)

/-- Every function in `ComplexUCB G` is `ofReal (re f) + I • ofReal (im f)`. -/
theorem ofReal_re_add_I_smul_ofReal_im (f : ComplexUCB G) :
    ofReal (re f) + I • ofReal (im f) = f :=
  ext fun _ => by simp [mul_comm I]

/-- Two functions in `ComplexUCB G` are equal when their real and imaginary parts are equal. -/
theorem ext_re_im {f g : ComplexUCB G} (hre : re f = re g) (him : im f = im g) : f = g := by
  rw [← ofReal_re_add_I_smul_ofReal_im f, hre, him, ofReal_re_add_I_smul_ofReal_im]

/-- The real part does not increase the supremum norm. -/
theorem norm_re_le (f : ComplexUCB G) : ‖re f‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x =>
    (abs_re_le_norm _).trans ((f : G →ᵇ ℂ).norm_coe_le_norm x)

/-- The imaginary part does not increase the supremum norm. -/
theorem norm_im_le (f : ComplexUCB G) : ‖im f‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x =>
    (abs_im_le_norm _).trans ((f : G →ᵇ ℂ).norm_coe_le_norm x)

/-- A real function has the same supremum norm when regarded as a complex function. -/
theorem norm_ofReal (f : UCB G) : ‖ofReal f‖ = ‖f‖ := by
  refine le_antisymm ((BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x => ?_) ?_
  · simpa using (f : G →ᵇ ℝ).norm_coe_le_norm x
  · simpa using norm_re_le (ofReal f)

/-! ### Left translation -/

/-- Left translation `g ↦ L_g`, where `(L_g f)(x) = f (g⁻¹ * x)`, as a group homomorphism from `G`
to the complex linear isometry equivalences of `ComplexUCB G`; the case `𝕜 = ℂ` of
`ucbSubalgebra.leftTranslation`. -/
def leftTranslation : G →* (ComplexUCB G ≃ₗᵢ[ℂ] ComplexUCB G) :=
  ucbSubalgebra.leftTranslation ℂ G

@[simp]
theorem leftTranslation_apply (g : G) (f : ComplexUCB G) (x : G) :
    (leftTranslation g f : G →ᵇ ℂ) x = (f : G →ᵇ ℂ) (g⁻¹ * x) :=
  ucbSubalgebra.leftTranslation_apply ..

/-- The real part of `L_g f` is the left translate `L_g` of the real part of `f`. -/
@[simp]
theorem re_leftTranslation (g : G) (f : ComplexUCB G) :
    re (leftTranslation g f) = UCB.leftTranslation g (re f) :=
  UCB.ext fun _ => by simp

/-- The imaginary part of `L_g f` is the left translate `L_g` of the imaginary part of `f`. -/
@[simp]
theorem im_leftTranslation (g : G) (f : ComplexUCB G) :
    im (leftTranslation g f) = UCB.leftTranslation g (im f) :=
  UCB.ext fun _ => by simp

/-- Left translation commutes with regarding a real function as a complex function. -/
@[simp]
theorem leftTranslation_ofReal (g : G) (f : UCB G) :
    leftTranslation g (ofReal f) = ofReal (UCB.leftTranslation g f) :=
  ext fun _ => by simp

end ComplexUCB

end TauCeti
