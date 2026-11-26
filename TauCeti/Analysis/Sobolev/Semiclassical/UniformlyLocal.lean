/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Semiclassical.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.Calculus.BumpFunction.Translates
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.Lp

/-!
# Uniformly local semiclassical Sobolev norms

Let `E` be a finite-dimensional real inner product space of dimension `n`, `h > 0` a length
scale and `η` a compactly supported real cutoff on `E`. Localizing a function `f` with values in a
real normed space to the ball of radius comparable to `h` about a point `x` gives
`y ↦ η (h⁻¹ • (y - x)) f(y)`, and the
**uniformly local semiclassical Sobolev norm** of `f` is the supremum over all centres `x` of the
semiclassical norms `‖·‖_{k,h}` (`TauCeti.semiclassicalSobolevNorm`) of these localizations:

`‖f‖_{k,h,η} = sup_x ‖η (h⁻¹ • (· - x)) f‖_{k,h}`

(`TauCeti.uniformlyLocalSemiclassicalSobolevNorm`). It measures the size of `f` on every ball of
radius comparable to `h`, in units of `h`, against the volume normalized by `h⁻ⁿ`, and it does
not see how many such balls `f` occupies. This is the norm of the rescaled linear and nonlinear
estimates near a pseudoholomorphic curve in Taubes's analysis of the large-parameter
Seiberg–Witten equations, at the scale `h = (2r)^(-1/2)`: there the fields are close to plane
vortices on every ball of radius comparable to `h` along the curve, while the curve has length of
order one.

The norm is invariant under negation, homogeneous and, when the localizations are bounded above,
subadditive (`TauCeti.uniformlyLocalSemiclassicalSobolevNorm_neg`,
`TauCeti.uniformlyLocalSemiclassicalSobolevNorm_const_smul`,
`TauCeti.uniformlyLocalSemiclassicalSobolevNorm_add_le`). It is invariant under translations of
`f` (`TauCeti.uniformlyLocalSemiclassicalSobolevNorm_comp_sub`), and at scale `h` it is the norm at
scale one of `f (h • ·)` (`TauCeti.uniformlyLocalSemiclassicalSobolevNorm_eq_comp_smul`). For
`2k > n` and real-valued functions it has the following properties, all with constants independent
of `h` and of the centre:

* **Evaluation.** `|η(0)| |f(x)| ≤ C ‖η (h⁻¹ • (· - x)) f‖_{k,h}`, hence
  `|η(0)| |f(x)| ≤ C ‖f‖_{k,h,η}` (`TauCeti.exists_norm_mul_norm_le_mul_semiclassicalSobolevNorm`,
  `TauCeti.exists_norm_mul_norm_le_mul_uniformlyLocalSemiclassicalSobolevNorm`).
* **Equivalence of cutoffs.** If `η ≠ 0`, then for every compactly supported `χ` of class `Cᵏ`
  the localizations by `χ` are bounded by `C` times a bound for the localizations by `η`
  (`TauCeti.exists_forall_semiclassicalSobolevNorm_le_mul`), so `‖f‖_{k,h,χ} ≤ C ‖f‖_{k,h,η}`
  (`TauCeti.exists_uniformlyLocalSemiclassicalSobolevNorm_le_mul`). Any two nonzero compactly
  supported cutoffs of class `Cᵏ` thus define equivalent norms.
* **Multiplication.** `‖η (h⁻¹ • (· - x)) f g‖_{k,h} ≤ C ‖η (h⁻¹ • (· - x)) f‖_{k,h} M` whenever
  `M` bounds all localizations of `g` by `η`
  (`TauCeti.exists_forall_semiclassicalSobolevNorm_mul_le_mul`), hence
  `‖f g‖_{k,h,η} ≤ C ‖f‖_{k,h,η} ‖g‖_{k,h,η}`
  (`TauCeti.exists_uniformlyLocalSemiclassicalSobolevNorm_mul_le`).

Multiplication by a scalar function `g` with the semiclassical bounds `hⁱ ‖Dⁱ g‖ ≤ B` for `i ≤ k`
commutes with the localizations, so it is bounded on the uniformly local norm for every `k`,
`‖g • f‖_{k,h,η} ≤ (k + 1) 2ᵏ B ‖f‖_{k,h,η}`
(`TauCeti.uniformlyLocalSemiclassicalSobolevNorm_smul_le`). A function `f` with these bounds itself
has localizations bounded independently of `h` and of the centre,
`‖f‖_{k,h,η} ≤ (k + 1) 2ᵏ B ‖η‖_{k,1}`
(`TauCeti.semiclassicalSobolevNorm_smul_le_mul_semiclassicalSobolevNorm_one`,
`TauCeti.uniformlyLocalSemiclassicalSobolevNorm_le_mul_semiclassicalSobolevNorm_one`). For a
**gauge transformation**, a function `u` with values in `ℝ` or `ℂ` and `‖u‖ = 1`, the inverse `ū`
has derivatives of the same norms, so `u` and `ū` both act boundedly and the uniformly local norms
of `f` and `u • f` are equivalent with constant `(k + 1) 2ᵏ B`
(`TauCeti.uniformlyLocalSemiclassicalSobolevNorm_le_mul_smul_of_norm_eq_one`).

The equivalence of cutoffs writes `χ` as a finite combination `∑ₐ gₐ η(· - a)` of translates of
`η` with compactly supported coefficients (`TauCeti.exists_finset_forall_eq_sum_mul_comp_sub`).
Placed at scale `h` about `x`, the translate `η(· - a)` becomes the cutoff about `x + h a`, and
each coefficient becomes a profile `gₐ (h⁻¹ • (· - x))` whose semiclassical norm is `‖gₐ‖_{k,1}`
for every `h` and `x` (`TauCeti.semiclassicalSobolevNorm_comp_inv_smul_sub`). The algebra estimate
for the semiclassical norms (`TauCeti.exists_semiclassicalSobolevNorm_mul_le`) then bounds each
product. For the multiplication estimate, `η` is the product of itself and a cutoff `χ` equal to
one on its support, so the localization of `f g` by `η` is the product of the localizations of `f`
by `η` and of `g` by `χ`.

The norms are real-valued suprema: a supremum over centres is only meaningful when the
localized norms are bounded above, which the statements about `‖·‖_{k,h,η}` assume.

## Main definitions

* `TauCeti.uniformlyLocalSemiclassicalSobolevNorm k h η f`: the norm
  `sup_x ‖η (h⁻¹ • (· - x)) f‖_{k,h}`.

## References

* M. Zworski, *Semiclassical Analysis*, Graduate Studies in Mathematics 138, American
  Mathematical Society, 2012 (semiclassical Sobolev spaces).
* T. Kato, *The Cauchy problem for quasi-linear symmetric hyperbolic systems*, Arch. Rational
  Mech. Anal. 58 (1975), 181–205 (uniformly local Sobolev spaces).
* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Module Set
open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {k : ℕ} {h : ℝ} {η : E → ℝ} {f g : E → F}

/-- The **uniformly local semiclassical Sobolev norm** of order `k` at scale `h` with cutoff `η`:
the supremum over all centres `x` of the semiclassical norms `‖η (h⁻¹ • (· - x)) • f‖_{k,h}` of the
localizations of `f` to the balls of radius comparable to `h`. It is meaningful when these norms
are bounded above, and is then their least upper bound; otherwise it is `0`. -/
def uniformlyLocalSemiclassicalSobolevNorm (k : ℕ) (h : ℝ) (η : E → ℝ) (f : E → F) : ℝ :=
  ⨆ x : E, semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • f y

theorem uniformlyLocalSemiclassicalSobolevNorm_def (k : ℕ) (h : ℝ) (η : E → ℝ) (f : E → F) :
    uniformlyLocalSemiclassicalSobolevNorm k h η f =
      ⨆ x : E, semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • f y :=
  (rfl)

theorem uniformlyLocalSemiclassicalSobolevNorm_nonneg (k : ℕ) (hh : 0 ≤ h) (η : E → ℝ)
    (f : E → F) : 0 ≤ uniformlyLocalSemiclassicalSobolevNorm k h η f :=
  Real.iSup_nonneg fun _ ↦ semiclassicalSobolevNorm_nonneg k hh _

@[simp]
theorem uniformlyLocalSemiclassicalSobolevNorm_zero (k : ℕ) (h : ℝ) (η : E → ℝ) :
    uniformlyLocalSemiclassicalSobolevNorm k h η (0 : E → F) = 0 := by
  simp only [uniformlyLocalSemiclassicalSobolevNorm, Pi.zero_apply, smul_zero]
  rw [← Pi.zero_def, semiclassicalSobolevNorm_zero, ciSup_const]

/-- The uniformly local norm is invariant under negation. -/
@[simp]
theorem uniformlyLocalSemiclassicalSobolevNorm_neg (k : ℕ) (h : ℝ) (η : E → ℝ) (f : E → F) :
    uniformlyLocalSemiclassicalSobolevNorm k h η (-f) =
      uniformlyLocalSemiclassicalSobolevNorm k h η f := by
  refine iSup_congr fun x ↦ ?_
  conv_rhs => rw [← semiclassicalSobolevNorm_neg]
  congr 1
  ext y
  simp only [Pi.neg_apply, smul_neg]

/-- **Homogeneity of the uniformly local norm.** `‖c f‖_{k,h,η} = |c| ‖f‖_{k,h,η}`. -/
@[simp]
theorem uniformlyLocalSemiclassicalSobolevNorm_const_smul (k : ℕ) (h c : ℝ) (η : E → ℝ)
    (f : E → F) :
    uniformlyLocalSemiclassicalSobolevNorm k h η (c • f) =
      |c| * uniformlyLocalSemiclassicalSobolevNorm k h η f := by
  rw [uniformlyLocalSemiclassicalSobolevNorm, uniformlyLocalSemiclassicalSobolevNorm,
    Real.mul_iSup_of_nonneg (abs_nonneg c)]
  refine iSup_congr fun x ↦ ?_
  rw [← semiclassicalSobolevNorm_const_smul]
  congr 1
  ext y
  simp only [Pi.smul_apply]
  exact smul_comm _ _ _

/-- Each localization is bounded by the uniformly local norm, when the localizations are bounded
above. -/
theorem semiclassicalSobolevNorm_le_uniformlyLocalSemiclassicalSobolevNorm
    (hb : BddAbove (range fun x ↦ semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • f y))
    (x : E) :
    semiclassicalSobolevNorm k h (fun y ↦ η (h⁻¹ • (y - x)) • f y) ≤
      uniformlyLocalSemiclassicalSobolevNorm k h η f :=
  le_ciSup hb x

/-- A common bound for all localizations bounds the uniformly local norm. -/
theorem uniformlyLocalSemiclassicalSobolevNorm_le {M : ℝ}
    (hM : ∀ x, semiclassicalSobolevNorm k h (fun y ↦ η (h⁻¹ • (y - x)) • f y) ≤ M) :
    uniformlyLocalSemiclassicalSobolevNorm k h η f ≤ M :=
  ciSup_le hM

/-- **Translation invariance.** The uniformly local norm of `f (· - a)` is that of `f`. -/
@[simp]
theorem uniformlyLocalSemiclassicalSobolevNorm_comp_sub (k : ℕ) (h : ℝ) (η : E → ℝ) (f : E → F)
    (a : E) :
    uniformlyLocalSemiclassicalSobolevNorm k h η (fun y ↦ f (y - a)) =
      uniformlyLocalSemiclassicalSobolevNorm k h η f := by
  -- The localization of `f (· - a)` about `x` is the translate of the localization of `f` about
  -- `x - a`.
  have hloc (x : E) : semiclassicalSobolevNorm k h (fun y ↦ η (h⁻¹ • (y - x)) • f (y - a)) =
      semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - (x - a))) • f y := by
    rw [← semiclassicalSobolevNorm_comp_sub k h (fun y ↦ η (h⁻¹ • (y - (x - a))) • f y) a]
    simp only [sub_sub_sub_cancel_right]
  simp only [uniformlyLocalSemiclassicalSobolevNorm, hloc]
  exact (Equiv.subRight a).iSup_comp (g := fun x ↦
    semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • f y)

/-- **The uniformly local norm at scale `h` is the norm at scale one of the dilated function.**
For `η` and `f` of class `Cᵏ` and `h > 0`, `‖f‖_{k,h,η} = ‖f (h • ·)‖_{k,1,η}`. -/
theorem uniformlyLocalSemiclassicalSobolevNorm_eq_comp_smul (hη : ContDiff ℝ k η)
    (hf : ContDiff ℝ k f) (hh : 0 < h) :
    uniformlyLocalSemiclassicalSobolevNorm k h η f =
      uniformlyLocalSemiclassicalSobolevNorm k 1 η fun z ↦ f (h • z) := by
  have hloc (x : E) : semiclassicalSobolevNorm k h (fun y ↦ η (h⁻¹ • (y - x)) • f y) =
      semiclassicalSobolevNorm k 1 fun z ↦ η ((1 : ℝ)⁻¹ • (z - h⁻¹ • x)) • f (h • z) := by
    rw [semiclassicalSobolevNorm_eq_comp_smul (f := fun y ↦ η (h⁻¹ • (y - x)) • f y)
      ((hη.comp_inv_smul_sub h x).smul hf) hh]
    congr 1
    ext z
    rw [smul_sub, inv_smul_smul₀ hh.ne', inv_one, one_smul]
  simp only [uniformlyLocalSemiclassicalSobolevNorm, hloc]
  exact Function.Surjective.iSup_comp (f := fun x : E ↦ h⁻¹ • x)
    (fun y ↦ ⟨h • y, inv_smul_smul₀ hh.ne' y⟩)
    fun y ↦ semiclassicalSobolevNorm k 1 fun z ↦ η ((1 : ℝ)⁻¹ • (z - y)) • f (h • z)

/-! ### Localizations -/

/-- A compactly supported function of class `Cᵏ` lies in the domain of the semiclassical norms:
its derivatives through order `k` are square integrable. -/
private theorem contDiff_and_memLp_of_hasCompactSupport {u : E → F} (hu : ContDiff ℝ k u)
    (hc : HasCompactSupport u) : ContDiff ℝ k u ∧ ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i u) 2 :=
  ⟨hu, fun _ hi ↦ hu.memLp_iteratedFDeriv_of_hasCompactSupport (by exact_mod_cast hi) hc⟩

/-- For a compactly supported cutoff `η` of class `Cᵏ`, `f` of class `Cᵏ` and `h ≠ 0`, each
localization `y ↦ η (h⁻¹ • (y - x)) • f y` is of class `Cᵏ` with square-integrable derivatives
through order `k`. -/
private theorem contDiff_and_memLp_localization (hη : ContDiff ℝ k η)
    (hηc : HasCompactSupport η) (hf : ContDiff ℝ k f) (hh : h ≠ 0) (x : E) :
    ContDiff ℝ k (fun y ↦ η (h⁻¹ • (y - x)) • f y) ∧
      ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i fun y ↦ η (h⁻¹ • (y - x)) • f y) 2 :=
  contDiff_and_memLp_of_hasCompactSupport ((hη.comp_inv_smul_sub h x).smul hf)
    (hηc.comp_inv_smul_sub hh x).smul_right

/-- **The triangle inequality for the uniformly local norm.** For a compactly supported cutoff `η`
of class `Cᵏ`, `h > 0` and `f`, `g` of class `Cᵏ` whose localizations are bounded above, the
localizations of `f + g` are bounded above and `‖f + g‖_{k,h,η} ≤ ‖f‖_{k,h,η} + ‖g‖_{k,h,η}`. -/
theorem uniformlyLocalSemiclassicalSobolevNorm_add_le (hη : ContDiff ℝ k η)
    (hηc : HasCompactSupport η) (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g) (hh : 0 < h)
    (hbf : BddAbove (range fun x ↦ semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • f y))
    (hbg : BddAbove (range fun x ↦ semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • g y)) :
    BddAbove (range fun x ↦
        semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • (f + g) y) ∧
      uniformlyLocalSemiclassicalSobolevNorm k h η (f + g) ≤
        uniformlyLocalSemiclassicalSobolevNorm k h η f +
          uniformlyLocalSemiclassicalSobolevNorm k h η g := by
  have hle (x : E) : semiclassicalSobolevNorm k h (fun y ↦ η (h⁻¹ • (y - x)) • (f + g) y) ≤
      uniformlyLocalSemiclassicalSobolevNorm k h η f +
        uniformlyLocalSemiclassicalSobolevNorm k h η g := by
    have hsplit : (fun y ↦ η (h⁻¹ • (y - x)) • (f + g) y) =
        (fun y ↦ η (h⁻¹ • (y - x)) • f y) + fun y ↦ η (h⁻¹ • (y - x)) • g y := by
      ext y
      simp only [Pi.add_apply, smul_add]
    obtain ⟨hlf, hmf⟩ := contDiff_and_memLp_localization hη hηc hf hh.ne' x
    rw [hsplit]
    exact (semiclassicalSobolevNorm_add_le hlf
      (contDiff_and_memLp_localization hη hηc hg hh.ne' x).1 hmf hh.le).trans
      (add_le_add (semiclassicalSobolevNorm_le_uniformlyLocalSemiclassicalSobolevNorm hbf x)
        (semiclassicalSobolevNorm_le_uniformlyLocalSemiclassicalSobolevNorm hbg x))
  exact ⟨⟨_, forall_mem_range.2 hle⟩, uniformlyLocalSemiclassicalSobolevNorm_le hle⟩

/-! ### Evaluation -/

/-- **Evaluation, uniformly in the scale.** If `2k > dim E`, there is a constant `C ≥ 0` such that
for every `h > 0`, every compactly supported cutoff `η` of class `Cᵏ`, every `f` of class `Cᵏ` and
every point `x`, `|η(0)| |f(x)| ≤ C ‖η (h⁻¹ • (· - x)) f‖_{k,h}`. -/
theorem exists_norm_mul_norm_le_mul_semiclassicalSobolevNorm (hk : finrank ℝ E < 2 * k) :
    ∃ C, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ η f : E → ℝ, ContDiff ℝ k η → HasCompactSupport η →
      ContDiff ℝ k f → ∀ x,
        ‖η 0‖ * ‖f x‖ ≤ C * semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • f y := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_le_mul_semiclassicalSobolevNorm (E := E) hk
  refine ⟨C, hC0, fun h hh η f hη hηc hf x ↦ ?_⟩
  obtain ⟨hloc, hm⟩ := contDiff_and_memLp_localization hη hηc hf hh.ne' x
  simpa [norm_mul] using hC h hh _ hloc hm x

/-- **Evaluation by the uniformly local norm.** If `2k > dim E`, there is a constant `C ≥ 0` such
that for every `h > 0`, every compactly supported cutoff `η` of class `Cᵏ` and every `f` of class
`Cᵏ` whose localizations are bounded above, `|η(0)| |f(x)| ≤ C ‖f‖_{k,h,η}` at every point. -/
theorem exists_norm_mul_norm_le_mul_uniformlyLocalSemiclassicalSobolevNorm
    (hk : finrank ℝ E < 2 * k) :
    ∃ C, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ η f : E → ℝ, ContDiff ℝ k η → HasCompactSupport η →
      ContDiff ℝ k f →
      BddAbove (range fun x ↦ semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • f y) →
        ∀ x, ‖η 0‖ * ‖f x‖ ≤ C * uniformlyLocalSemiclassicalSobolevNorm k h η f := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_mul_norm_le_mul_semiclassicalSobolevNorm (E := E) hk
  refine ⟨C, hC0, fun h hh η f hη hηc hf hb x ↦ (hC h hh η f hη hηc hf x).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (semiclassicalSobolevNorm_le_uniformlyLocalSemiclassicalSobolevNorm hb x) hC0

/-! ### Equivalence of cutoffs -/

/-- **Equivalence of cutoffs.** Let `2k > dim E`, and let `η ≠ 0` and `χ` be compactly supported
cutoffs of class `Cᵏ`. There is a constant `C ≥ 0` such that for every `h > 0` and every `f` of
class `Cᵏ`, if `M` bounds all localizations `‖η (h⁻¹ • (· - x)) f‖_{k,h}`, then `C M` bounds all
localizations `‖χ (h⁻¹ • (· - x)) f‖_{k,h}`. -/
theorem exists_forall_semiclassicalSobolevNorm_le_mul (hk : finrank ℝ E < 2 * k)
    (hη : ContDiff ℝ k η) (hηc : HasCompactSupport η) (hη0 : η ≠ 0) {χ : E → ℝ}
    (hχ : ContDiff ℝ k χ) (hχc : HasCompactSupport χ) :
    ∃ C, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ f : E → ℝ, ContDiff ℝ k f → ∀ M : ℝ,
      (∀ x, semiclassicalSobolevNorm k h (fun y ↦ η (h⁻¹ • (y - x)) • f y) ≤ M) →
        ∀ x, semiclassicalSobolevNorm k h (fun y ↦ χ (h⁻¹ • (y - x)) • f y) ≤ C * M := by
  obtain ⟨s, g, hg, hsum⟩ := exists_finset_forall_eq_sum_mul_comp_sub hη hη0 hχ hχc
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_semiclassicalSobolevNorm_mul_le (E := E) hk
  have hg0 (a : E) : 0 ≤ C₀ * semiclassicalSobolevNorm k 1 (g a) :=
    mul_nonneg hC₀0 (semiclassicalSobolevNorm_nonneg k zero_le_one _)
  refine ⟨∑ a ∈ s, C₀ * semiclassicalSobolevNorm k 1 (g a), Finset.sum_nonneg fun a _ ↦ hg0 a,
    fun h hh f hf M hM x ↦ ?_⟩
  -- The coefficient profiles `u a` about `x` and the localizations `v a` of `f` about `x + h a`.
  set u : E → E → ℝ := fun a y ↦ g a (h⁻¹ • (y - x))
  set v : E → E → ℝ := fun a y ↦ η (h⁻¹ • (y - (x + h • a))) • f y
  have hsplit : (fun y ↦ χ (h⁻¹ • (y - x)) • f y) = fun y ↦ ∑ a ∈ s, (u a * v a) y := by
    ext y
    rw [smul_eq_mul, hsum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp only [u, v, Pi.mul_apply, smul_eq_mul, sub_add_eq_sub_sub, smul_sub _ (y - x),
      inv_smul_smul₀ hh.ne']
    ring
  have hu (a) (ha : a ∈ s) : ContDiff ℝ k (u a) ∧ ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i (u a)) 2 :=
    contDiff_and_memLp_of_hasCompactSupport ((hg a ha).1.comp_inv_smul_sub h x)
      ((hg a ha).2.comp_inv_smul_sub hh.ne' x)
  have hv (a) : ContDiff ℝ k (v a) ∧ ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i (v a)) 2 :=
    contDiff_and_memLp_localization hη hηc hf hh.ne' (x + h • a)
  have hprod (a) (ha : a ∈ s) := hC₀ h hh _ _ (hu a ha).1 (hv a).1 (hu a ha).2 (hv a).2
  rw [hsplit, Finset.sum_mul]
  refine (semiclassicalSobolevNorm_sum_le s (fun a ha ↦ (hu a ha).1.mul (hv a).1)
    (fun a ha ↦ (hprod a ha).1) hh.le).trans (Finset.sum_le_sum fun a ha ↦ ?_)
  -- Each profile `u a` has the unit-scale norm of `g a`.
  have hua : semiclassicalSobolevNorm k h (u a) = semiclassicalSobolevNorm k 1 (g a) :=
    semiclassicalSobolevNorm_comp_inv_smul_sub (hg a ha).1 hh x
  calc semiclassicalSobolevNorm k h (u a * v a)
      ≤ C₀ * semiclassicalSobolevNorm k h (u a) * semiclassicalSobolevNorm k h (v a) :=
        (hprod a ha).2
    _ ≤ C₀ * semiclassicalSobolevNorm k 1 (g a) * M := by
        rw [hua]
        exact mul_le_mul_of_nonneg_left (hM (x + h • a)) (hg0 a)

/-- **Equivalence of uniformly local norms.** Let `2k > dim E`, and let `η ≠ 0` and `χ` be
compactly supported cutoffs of class `Cᵏ`. There is a constant `C ≥ 0` such that for every `h > 0`
and every `f` of class `Cᵏ` whose localizations by `η` are bounded above, the localizations by `χ`
are bounded above and `‖f‖_{k,h,χ} ≤ C ‖f‖_{k,h,η}`. -/
theorem exists_uniformlyLocalSemiclassicalSobolevNorm_le_mul (hk : finrank ℝ E < 2 * k)
    (hη : ContDiff ℝ k η) (hηc : HasCompactSupport η) (hη0 : η ≠ 0) {χ : E → ℝ}
    (hχ : ContDiff ℝ k χ) (hχc : HasCompactSupport χ) :
    ∃ C, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ f : E → ℝ, ContDiff ℝ k f →
      BddAbove (range fun x ↦ semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • f y) →
        BddAbove (range fun x ↦ semiclassicalSobolevNorm k h fun y ↦ χ (h⁻¹ • (y - x)) • f y) ∧
          uniformlyLocalSemiclassicalSobolevNorm k h χ f ≤
            C * uniformlyLocalSemiclassicalSobolevNorm k h η f := by
  obtain ⟨C, hC0, hC⟩ := exists_forall_semiclassicalSobolevNorm_le_mul hk hη hηc hη0 hχ hχc
  refine ⟨C, hC0, fun h hh f hf hb ↦ ?_⟩
  have hle := hC h hh f hf _ (semiclassicalSobolevNorm_le_uniformlyLocalSemiclassicalSobolevNorm hb)
  exact ⟨⟨_, forall_mem_range.2 hle⟩, uniformlyLocalSemiclassicalSobolevNorm_le hle⟩

/-! ### Multiplication -/

/-- **Multiplication, uniformly in the scale.** Let `2k > dim E` and let `η` be a compactly
supported cutoff of class `Cᵏ`. There is a constant `C ≥ 0` such that for every `h > 0` and all
`f` and `g` of class `Cᵏ`, if `M` bounds all localizations `‖η (h⁻¹ • (· - x)) g‖_{k,h}`, then at
every centre `x`

`‖η (h⁻¹ • (· - x)) f g‖_{k,h} ≤ C ‖η (h⁻¹ • (· - x)) f‖_{k,h} M`. -/
theorem exists_forall_semiclassicalSobolevNorm_mul_le_mul (hk : finrank ℝ E < 2 * k)
    (hη : ContDiff ℝ k η) (hηc : HasCompactSupport η) :
    ∃ C, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ f g : E → ℝ, ContDiff ℝ k f → ContDiff ℝ k g → ∀ M : ℝ,
      (∀ x, semiclassicalSobolevNorm k h (fun y ↦ η (h⁻¹ • (y - x)) • g y) ≤ M) →
        ∀ x, semiclassicalSobolevNorm k h (fun y ↦ η (h⁻¹ • (y - x)) • (f y * g y)) ≤
          C * semiclassicalSobolevNorm k h (fun y ↦ η (h⁻¹ • (y - x)) • f y) * M := by
  rcases eq_or_ne η 0 with rfl | hη0
  · exact ⟨0, le_rfl, fun h _ f g _ _ M _ x ↦ by simp [← Pi.zero_def]⟩
  -- A smooth bump `χ` equal to one on the support of `η`, so that `η χ = η`.
  obtain ⟨R, hR, hsub⟩ := hηc.isCompact.isBounded.subset_closedBall_lt 0 0
  let χ : ContDiffBump (0 : E) := ⟨R, R + 1, hR, by linarith⟩
  have hηχ (z : E) : η z * χ z = η z := by
    by_cases hz : z ∈ tsupport η
    · rw [χ.one_of_mem_closedBall (hsub hz), mul_one]
    · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
  have hχ : ContDiff ℝ k χ := χ.contDiff
  have hχc : HasCompactSupport χ := χ.hasCompactSupport
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_forall_semiclassicalSobolevNorm_le_mul hk hη hηc hη0 hχ hχc
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_semiclassicalSobolevNorm_mul_le (E := E) hk
  refine ⟨C₀ * C₁, mul_nonneg hC₀0 hC₁0, fun h hh f g hf hg M hM x ↦ ?_⟩
  -- The localization of `f g` by `η` is the product of those of `f` by `η` and of `g` by `χ`.
  have hsplit : (fun y ↦ η (h⁻¹ • (y - x)) • (f y * g y)) =
      (fun y ↦ η (h⁻¹ • (y - x)) • f y) * fun y ↦ χ (h⁻¹ • (y - x)) • g y := by
    ext y
    simp only [Pi.mul_apply, smul_eq_mul]
    linear_combination (-(f y * g y)) * hηχ (h⁻¹ • (y - x))
  obtain ⟨hlf, hmf⟩ := contDiff_and_memLp_localization hη hηc hf hh.ne' x
  obtain ⟨hlg, hmg⟩ := contDiff_and_memLp_localization hχ hχc hg hh.ne' x
  rw [hsplit]
  calc _ ≤ C₀ * semiclassicalSobolevNorm k h (fun y ↦ η (h⁻¹ • (y - x)) • f y) *
        semiclassicalSobolevNorm k h (fun y ↦ χ (h⁻¹ • (y - x)) • g y) :=
        (hC₀ h hh _ _ hlf hlg hmf hmg).2
    _ ≤ C₀ * semiclassicalSobolevNorm k h (fun y ↦ η (h⁻¹ • (y - x)) • f y) * (C₁ * M) :=
        mul_le_mul_of_nonneg_left (hC₁ h hh g hg M hM x)
          (mul_nonneg hC₀0 (semiclassicalSobolevNorm_nonneg k hh.le _))
    _ = C₀ * C₁ * semiclassicalSobolevNorm k h (fun y ↦ η (h⁻¹ • (y - x)) • f y) * M := by
        ring

/-- **The uniformly local norms form an algebra, uniformly in the scale.** Let `2k > dim E` and
let `η` be a compactly supported cutoff of class `Cᵏ`. There is a constant `C ≥ 0` such that for
every `h > 0` and all `f` and `g` of class `Cᵏ` whose localizations by `η` are bounded above, the
localizations of `f g` are bounded above and `‖f g‖_{k,h,η} ≤ C ‖f‖_{k,h,η} ‖g‖_{k,h,η}`. -/
theorem exists_uniformlyLocalSemiclassicalSobolevNorm_mul_le (hk : finrank ℝ E < 2 * k)
    (hη : ContDiff ℝ k η) (hηc : HasCompactSupport η) :
    ∃ C, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ f g : E → ℝ, ContDiff ℝ k f → ContDiff ℝ k g →
      BddAbove (range fun x ↦ semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • f y) →
      BddAbove (range fun x ↦ semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • g y) →
        BddAbove (range fun x ↦
            semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • (f y * g y)) ∧
          uniformlyLocalSemiclassicalSobolevNorm k h η (fun y ↦ f y * g y) ≤
            C * uniformlyLocalSemiclassicalSobolevNorm k h η f *
              uniformlyLocalSemiclassicalSobolevNorm k h η g := by
  obtain ⟨C, hC0, hC⟩ := exists_forall_semiclassicalSobolevNorm_mul_le_mul hk hη hηc
  refine ⟨C, hC0, fun h hh f g hf hg hbf hbg ↦ ?_⟩
  have hle (x : E) : semiclassicalSobolevNorm k h (fun y ↦ η (h⁻¹ • (y - x)) • (f y * g y)) ≤
      C * uniformlyLocalSemiclassicalSobolevNorm k h η f *
        uniformlyLocalSemiclassicalSobolevNorm k h η g :=
    (hC h hh f g hf hg _
      (semiclassicalSobolevNorm_le_uniformlyLocalSemiclassicalSobolevNorm hbg) x).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (semiclassicalSobolevNorm_le_uniformlyLocalSemiclassicalSobolevNorm hbf x) hC0)
        (uniformlyLocalSemiclassicalSobolevNorm_nonneg k hh.le η g))
  exact ⟨⟨_, forall_mem_range.2 hle⟩, uniformlyLocalSemiclassicalSobolevNorm_le hle⟩

/-! ### Multipliers and gauge equivalence -/

section Multiplier

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F]
  {B : ℝ}

/-- **Multipliers with semiclassical `Cᵏ` bounds on the uniformly local norm.** Let `η` be a
compactly supported cutoff of class `Cᵏ`, `h > 0`, and `g` a scalar function of class `Cᵏ` with
`hⁱ ‖Dⁱ g‖ ≤ B` everywhere for `i ≤ k`, such as a gauge transformation or a cutoff varying on the
scale `h`. For `f` of class `Cᵏ` whose localizations are bounded above, the localizations of
`g • f` are bounded above and

`‖g • f‖_{k,h,η} ≤ (k + 1) 2ᵏ B ‖f‖_{k,h,η}`.

The constant depends only on `k` and `B`. -/
theorem uniformlyLocalSemiclassicalSobolevNorm_smul_le {g : E → 𝕜} (hη : ContDiff ℝ k η)
    (hηc : HasCompactSupport η) (hg : ContDiff ℝ k g) (hf : ContDiff ℝ k f) (hh : 0 < h)
    (hB : ∀ i ≤ k, ∀ x, h ^ i * ‖iteratedFDeriv ℝ i g x‖ ≤ B)
    (hb : BddAbove (range fun x ↦ semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • f y)) :
    BddAbove (range fun x ↦
        semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • g y • f y) ∧
      uniformlyLocalSemiclassicalSobolevNorm k h η (fun y ↦ g y • f y) ≤
        (k + 1) * 2 ^ k * B * uniformlyLocalSemiclassicalSobolevNorm k h η f := by
  have hB0 : 0 ≤ (k + 1) * 2 ^ k * B :=
    mul_nonneg (by positivity) (nonneg_of_forall_pow_mul_norm_iteratedFDeriv_le hB 0)
  have hle (x : E) : semiclassicalSobolevNorm k h (fun y ↦ η (h⁻¹ • (y - x)) • g y • f y) ≤
      (k + 1) * 2 ^ k * B * uniformlyLocalSemiclassicalSobolevNorm k h η f := by
    -- Multiplication by `g` commutes with the localization.
    have hcomm : (fun y ↦ η (h⁻¹ • (y - x)) • g y • f y) =
        fun y ↦ g y • η (h⁻¹ • (y - x)) • f y := funext fun y ↦ smul_comm _ _ _
    obtain ⟨hloc, hm⟩ := contDiff_and_memLp_localization hη hηc hf hh.ne' x
    rw [hcomm]
    exact (semiclassicalSobolevNorm_smul_le_of_le_left hg hloc hm hh hB).2.trans
      (mul_le_mul_of_nonneg_left
        (semiclassicalSobolevNorm_le_uniformlyLocalSemiclassicalSobolevNorm hb x) hB0)
  exact ⟨⟨_, forall_mem_range.2 hle⟩, uniformlyLocalSemiclassicalSobolevNorm_le hle⟩

/-- **The localizations of a function with semiclassical `Cᵏ` bounds.** Let `η` be a compactly
supported cutoff of class `Cᵏ` and `h > 0`. If `f` is of class `Cᵏ` with `hⁱ ‖Dⁱ f‖ ≤ B`
everywhere for `i ≤ k`, then at every centre `x`

`‖η (h⁻¹ • (· - x)) f‖_{k,h} ≤ (k + 1) 2ᵏ B ‖η‖_{k,1}`,

a bound independent of `h` and of the centre. -/
theorem semiclassicalSobolevNorm_smul_le_mul_semiclassicalSobolevNorm_one (hη : ContDiff ℝ k η)
    (hηc : HasCompactSupport η) (hf : ContDiff ℝ k f) (hh : 0 < h)
    (hB : ∀ i ≤ k, ∀ x, h ^ i * ‖iteratedFDeriv ℝ i f x‖ ≤ B) (x : E) :
    semiclassicalSobolevNorm k h (fun y ↦ η (h⁻¹ • (y - x)) • f y) ≤
      (k + 1) * 2 ^ k * B * semiclassicalSobolevNorm k 1 η := by
  obtain ⟨hηx, hηm⟩ := contDiff_and_memLp_of_hasCompactSupport (hη.comp_inv_smul_sub h x)
    (hηc.comp_inv_smul_sub hh.ne' x)
  rw [← semiclassicalSobolevNorm_comp_inv_smul_sub hη hh x]
  exact (semiclassicalSobolevNorm_smul_le_of_le_right hηx hf hηm hh hB).2

/-- **The uniformly local norm of a function with semiclassical `Cᵏ` bounds.** Let `η` be a
compactly supported cutoff of class `Cᵏ` and `h > 0`. If `f` is of class `Cᵏ` with
`hⁱ ‖Dⁱ f‖ ≤ B` everywhere for `i ≤ k`, then the localizations of `f` are bounded above and
`‖f‖_{k,h,η} ≤ (k + 1) 2ᵏ B ‖η‖_{k,1}`, a bound independent of `h`. -/
theorem uniformlyLocalSemiclassicalSobolevNorm_le_mul_semiclassicalSobolevNorm_one
    (hη : ContDiff ℝ k η) (hηc : HasCompactSupport η) (hf : ContDiff ℝ k f) (hh : 0 < h)
    (hB : ∀ i ≤ k, ∀ x, h ^ i * ‖iteratedFDeriv ℝ i f x‖ ≤ B) :
    BddAbove (range fun x ↦ semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • f y) ∧
      uniformlyLocalSemiclassicalSobolevNorm k h η f ≤
        (k + 1) * 2 ^ k * B * semiclassicalSobolevNorm k 1 η := by
  have hle := semiclassicalSobolevNorm_smul_le_mul_semiclassicalSobolevNorm_one hη hηc hf hh hB
  exact ⟨⟨_, forall_mem_range.2 hle⟩, uniformlyLocalSemiclassicalSobolevNorm_le hle⟩

end Multiplier

section Gauge

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] {B : ℝ}

/-- **Gauge equivalence of the uniformly local norms.** Let `η` be a compactly supported cutoff of
class `Cᵏ`, `h > 0`, and `u` a gauge transformation of class `Cᵏ`, a function with `‖u‖ = 1`
everywhere, with `hⁱ ‖Dⁱ u‖ ≤ B` for `i ≤ k`. For `f` of class `Cᵏ` such that the localizations of
`u • f` are bounded above, the localizations of `f` are bounded above and

`‖f‖_{k,h,η} ≤ (k + 1) 2ᵏ B ‖u • f‖_{k,h,η}`.

Together with the bound `‖u • f‖_{k,h,η} ≤ (k + 1) 2ᵏ B ‖f‖_{k,h,η}`
(`TauCeti.uniformlyLocalSemiclassicalSobolevNorm_smul_le`), gauge transformations with
semiclassical `Cᵏ` bounds preserve the uniformly local norms up to a constant depending only on
`k` and `B`. -/
theorem uniformlyLocalSemiclassicalSobolevNorm_le_mul_smul_of_norm_eq_one {u : E → 𝕜}
    (hη : ContDiff ℝ k η) (hηc : HasCompactSupport η) (hu : ContDiff ℝ k u)
    (hu1 : ∀ x, ‖u x‖ = 1) (hf : ContDiff ℝ k f) (hh : 0 < h)
    (hB : ∀ i ≤ k, ∀ x, h ^ i * ‖iteratedFDeriv ℝ i u x‖ ≤ B)
    (hb : BddAbove (range fun x ↦
      semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • u y • f y)) :
    BddAbove (range fun x ↦ semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • f y) ∧
      uniformlyLocalSemiclassicalSobolevNorm k h η f ≤
        (k + 1) * 2 ^ k * B * uniformlyLocalSemiclassicalSobolevNorm k h η (fun y ↦ u y • f y) := by
  -- The inverse gauge is the conjugate `ū`, whose derivatives have the norms of those of `u`.
  have hu' : ContDiff ℝ k fun y ↦ conj (u y) := by
    simpa [Function.comp_def] using (RCLike.conjCLE (K := 𝕜)).contDiff.comp hu
  have hB' (i : ℕ) (hi : i ≤ k) (x : E) :
      h ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ conj (u y)) x‖ ≤ B := by
    have e := (RCLike.conjLIE (K := 𝕜)).norm_iteratedFDeriv_comp_left u x i
    simp only [Function.comp_def, RCLike.conjLIE_apply] at e
    rw [e]
    exact hB i hi x
  have hinv (y : E) : conj (u y) • u y • f y = f y := by
    rw [smul_smul, RCLike.conj_mul, hu1, RCLike.ofReal_one, one_pow, one_smul]
  have := uniformlyLocalSemiclassicalSobolevNorm_smul_le (f := fun y ↦ u y • f y) hη hηc hu'
    (hu.smul hf) hh hB' hb
  simpa only [hinv] using this

end Gauge

end TauCeti
