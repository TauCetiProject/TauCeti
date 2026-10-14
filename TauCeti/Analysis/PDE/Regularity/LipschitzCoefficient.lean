/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Basic
public import TauCeti.Analysis.Sobolev.W1p.CompactSupport
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Normed.Module.Lipschitz
import TauCeti.Analysis.Sobolev.W1p.DifferenceQuotient
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.LinearAlgebra.Matrix.ToQuadraticForm

/-!
# Interior `H²` regularity for Lipschitz principal coefficients

Let `a` be uniformly elliptic on an open `Ω ⊆ ℝⁿ`, with `x ↦ a(x)` locally Lipschitz on `Ω` in
the operator norm of its bilinear forms, let `b, c ∈ L∞(Ω)`, and let `u ∈ H¹(Ω)` be a weak
solution of

`-∂ⱼ(aⁱʲ ∂ᵢu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, with `f ∈ L²(Ω)`,

tested against every `v ∈ H¹₀(Ω)`, with no boundary condition on `u` and nothing assumed about
`∂Ω`. This file proves that `u ∈ H²_loc(Ω)`: on every open `V` whose closure is compact and
contained in `Ω`, the restriction of `u` is the first-order part of an element of `W^{2,2}(V)`
(`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn`). This is
the interior regularity theorem of Evans for `aⁱʲ ∈ C¹(Ω)`, whose coefficients are locally
Lipschitz.

## The proof

Moving the lower-order terms to the right-hand side gives `-div(a ∇u) = g` with
`g = f - ⟨b, ∇u⟩ - c u ∈ L²(Ω)`. For a smooth `ψ` equal to one near `closure V` and compactly
supported in `Ω`, let `w ∈ H¹(ℝⁿ)` be `ψ u` extended by zero. Testing the equation for `u` against
`ψ v` shows that for every `v ∈ H¹(ℝⁿ)`

`a(w, v) = ∫_Ω (ψ g - ⟨∇ψ, a ∇u⟩) v + ∫_Ω u ⟨∇v, a ∇ψ⟩`.

For a constant coefficient matrix `A` the last term is integrated by parts against the
classical divergence of `A ∇ψ`, which gives an `L²` forcing
(`TauCeti/Analysis/PDE/Regularity/Interior.lean`). For a Lipschitz `a` that divergence exists only
almost everywhere, and no Leibniz rule for Lipschitz multipliers is needed here: the
difference-quotient method only asks for bounds on `a(w, Dᵗ v)`. In the last term a translation
moves the difference quotient from `∇v` onto the field `u a ∇ψ`, and the product rule for
difference quotients bounds it by the `H¹` norm of `u` near `supp ψ`, the bound on `a ∇ψ` and its
Lipschitz constant. So `|a(w, Dᵗ v)| ≤ M ‖∇v‖_{L²}` uniformly in `t`, and the whole-space
difference-quotient estimate for such a functional forcing
(`TauCeti.PDE.UniformlyEllipticOn.norm_gradient_differenceQuotient_le_of_abs_energyFormH1_le`)
bounds `∇Dᵗ w` uniformly in `t`. The difference-quotient criterion then gives the second weak
derivatives of `w`, which agree with those of `u` on `V`.

Two auxiliary functions make the whole-space estimate applicable. It asks for a coefficient field
that is elliptic and Lipschitz on all of `ℝⁿ`, so `a` is glued to `λ I` by a second cutoff `χ`
equal to one near `supp ψ`: the field `χ a + (1 - χ) λ I` is uniformly elliptic everywhere with
the same constants, Lipschitz because `a` is Lipschitz on the compact set `supp χ`, and equal to
`a` where `∇w` lives. In the commutator term `u` is replaced by `χ u` extended by zero, an element
of `H¹(ℝⁿ)` whose difference quotients are controlled on the whole space.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.norm_gradient_differenceQuotient_le_of_abs_energyFormH1_le`:
  the whole-space difference-quotient estimate for a forcing functional bounded on difference
  quotients.
* `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn`:
  interior `H²` regularity for locally Lipschitz principal coefficients.

## References

* L. C. Evans, *Partial Differential Equations*, §6.3.1, Theorem 1 (interior `H²` regularity).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.8.
-/

public section

noncomputable section

open InnerProductSpace Matrix MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal NNReal Gradient InnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
  {K : ℝ≥0}

/-! ### Gluing the coefficient field to a constant one -/

variable [DecidableEq ι]

/-- The coefficient field `χ a + (1 - χ) λ I`. It agrees with `a` where `χ = 1`, and with the
constant coefficient `λ I` where `χ = 0`. -/
private def glueCoefficient (χ : EuclideanSpace ℝ ι → ℝ) (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (lam : ℝ) (x : EuclideanSpace ℝ ι) : Matrix ι ι ℝ :=
  χ x • a x + (1 - χ x) • (lam • (1 : Matrix ι ι ℝ))

/-- Gluing a uniformly elliptic field on `Ω` to `λ I` with a cutoff vanishing off `Ω` gives a
field that is uniformly elliptic on the whole space, with the same constants. -/
private theorem uniformlyEllipticOn_univ_glueCoefficient {s : Set (EuclideanSpace ℝ ι)}
    (ha : UniformlyEllipticOn s a lam Lam) {χ : EuclideanSpace ℝ ι → ℝ}
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hχs : ∀ x ∉ s, χ x = 0) :
    UniformlyEllipticOn univ (glueCoefficient χ a lam) lam Lam := by
  have hlam := ha.pos
  refine UniformlyEllipticOn.of_bounds hlam ha.le (fun x _ ξ => ?_) (fun x _ η ξ => ?_)
  · have hξ : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
    rw [glueCoefficient, toQuadraticForm'_add, Matrix.toQuadraticForm'_smul, _root_.smul_apply,
      smul_eq_mul, Matrix.toQuadraticForm'_smul, _root_.smul_apply, smul_eq_mul,
      toQuadraticForm'_smul_one]
    by_cases hx : x ∈ s
    · have := ha.lower_bound hx ξ
      nlinarith [(hχ01 x).1, (hχ01 x).2]
    · rw [hχs x hx]
      simp
  · have hη : 0 ≤ ‖η‖ * ‖ξ‖ := by positivity
    have hlam1 : |η ⬝ᵥ ((lam • (1 : Matrix ι ι ℝ)) *ᵥ ξ)| ≤ lam * ‖η‖ * ‖ξ‖ :=
      abs_dotProduct_smul_one_mulVec_le_of_abs_le (abs_of_pos hlam).le η ξ
    rw [glueCoefficient, add_mulVec, dotProduct_add, smul_mulVec, smul_mulVec, dotProduct_smul,
      dotProduct_smul, smul_eq_mul, smul_eq_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (hχ01 x).1, abs_of_nonneg (sub_nonneg.2 (hχ01 x).2)]
    have hχ0 := (hχ01 x).1
    have h1χ : 0 ≤ 1 - χ x := sub_nonneg.2 (hχ01 x).2
    have hfirst : χ x * |η ⬝ᵥ (a x *ᵥ ξ)| ≤ χ x * (Lam * ‖η‖ * ‖ξ‖) := by
      by_cases hx : x ∈ s
      · exact mul_le_mul_of_nonneg_left (ha.upper_bound hx η ξ) hχ0
      · rw [hχs x hx, zero_mul, zero_mul]
    calc χ x * |η ⬝ᵥ (a x *ᵥ ξ)| + (1 - χ x) * |η ⬝ᵥ ((lam • (1 : Matrix ι ι ℝ)) *ᵥ ξ)|
        ≤ χ x * (Lam * ‖η‖ * ‖ξ‖) + (1 - χ x) * (lam * ‖η‖ * ‖ξ‖) :=
          add_le_add hfirst (mul_le_mul_of_nonneg_left hlam1 h1χ)
      _ ≤ χ x * (Lam * ‖η‖ * ‖ξ‖) + (1 - χ x) * (Lam * ‖η‖ * ‖ξ‖) := by
          gcongr
          exact ha.le
      _ = Lam * ‖η‖ * ‖ξ‖ := by ring

omit [Fintype ι] in
/-- The glued field agrees with `a` wherever the cutoff equals one. -/
private theorem glueCoefficient_of_eq_one {χ : EuclideanSpace ℝ ι → ℝ} {x : EuclideanSpace ℝ ι}
    (hx : χ x = 1) : glueCoefficient χ a lam x = a x := by
  simp [glueCoefficient, hx]

/-- Gluing a field whose bilinear forms are bounded and Lipschitz on `s` to `λ I`, with a
Lipschitz cutoff vanishing off `s`, gives a field whose bilinear forms are Lipschitz on the
whole space. -/
private theorem exists_lipschitzWith_glueCoefficient {s : Set (EuclideanSpace ℝ ι)}
    (ha : UniformlyEllipticOn s a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) s)
    {χ : EuclideanSpace ℝ ι → ℝ} {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hχs : ∀ x ∉ s, χ x = 0) :
    ∃ K' : ℝ≥0, LipschitzWith K' fun x => matrixBilinearForm (glueCoefficient χ a lam x) := by
  set C := matrixBilinearForm (lam • (1 : Matrix ι ι ℝ))
  -- The bilinear form of the glued field is `C + χ (B(a) - C)`.
  have hform : (fun x => matrixBilinearForm (glueCoefficient χ a lam x)) =
      fun x => C + χ x • (matrixBilinearForm (a x) - C) := by
    funext x
    ext η ξ
    simp only [glueCoefficient, C, _root_.add_apply, _root_.smul_apply, _root_.sub_apply,
      matrixBilinearForm_add_apply, matrixBilinearForm_smul_apply, smul_eq_mul]
    ring
  have hR : ∀ x ∈ s, ‖matrixBilinearForm (a x) - C‖ ≤ ((Lam + ‖C‖).toNNReal : ℝ) :=
    fun x hx => by
      calc ‖matrixBilinearForm (a x) - C‖ ≤ ‖matrixBilinearForm (a x)‖ + ‖C‖ :=
          norm_sub_le (matrixBilinearForm (a x)) C
        _ ≤ Lam + ‖C‖ := add_le_add_left (ha.opNorm_matrixBilinearForm_le hx) _
        _ ≤ _ := Real.le_coe_toNNReal _
  have hsub : LipschitzOnWith K (fun x => matrixBilinearForm (a x) - C) s := by
    simpa using hK.sub (LipschitzWith.const C).lipschitzOnWith
  refine ⟨0 + (1 * K + L * (Lam + ‖C‖).toNNReal), ?_⟩
  rw [hform]
  exact (LipschitzWith.const C).add (LipschitzWith.smul_of_lipschitzOnWith hχ
    (fun x => by rw [Real.norm_of_nonneg (hχ01 x).1]; exact_mod_cast (hχ01 x).2) hχs hsub hR)

/-- **Extending a coefficient field from a neighbourhood of a compact set.** Let `a` be uniformly
elliptic on `Ω` with constants `λ, Λ`, with `x ↦ a(x)` locally Lipschitz on `Ω`, and let
`S ⊆ Ω` be compact. Then there is a coefficient field `ã`, uniformly elliptic on the whole space
with the same constants, with `x ↦ ã(x)` Lipschitz on the whole space, and equal to `a` on `S`.

One may take `ã = χ a + (1 - χ) λ I` for a smooth cutoff `χ` equal to one near `S` and compactly
supported in `Ω`. -/
private theorem exists_uniformlyEllipticOn_univ_lipschitzWith_eqOn
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LocallyLipschitzOn (Omega : Set (EuclideanSpace ℝ ι)) fun x => matrixBilinearForm (a x))
    {S : Set (EuclideanSpace ℝ ι)} (hS : IsCompact S) (hSΩ : S ⊆ Omega) :
    ∃ ã : EuclideanSpace ℝ ι → Matrix ι ι ℝ, UniformlyEllipticOn univ ã lam Lam ∧
      (∃ K' : ℝ≥0, LipschitzWith K' fun x => matrixBilinearForm (ã x)) ∧
        ∀ x ∈ S, ã x = a x := by
  obtain ⟨χ, hχ, hχr, hχ_one, hχc, hχts⟩ := hS.exists_contDiff_cutoff Omega.isOpen hSΩ
  have hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1 := fun x => hχr ⟨x, rfl⟩
  obtain ⟨Lχ, hLχ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hχc hχ (by simp)
  obtain ⟨Kχ, hKχ⟩ := (hK.mono hχts).exists_lipschitzOnWith_of_compact hχc.isCompact
  exact ⟨glueCoefficient χ a lam,
    uniformlyEllipticOn_univ_glueCoefficient ha hχ01
      fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hχts h),
    exists_lipschitzWith_glueCoefficient (ha.mono_set hχts) hKχ hLχ hχ01
      fun x hx => image_eq_zero_of_notMem_tsupport hx,
    fun x hx => glueCoefficient_of_eq_one (by simpa using interior_subset (hχ_one hx))⟩

/-! ### The difference-quotient estimate with a functional forcing -/

/-- **The difference-quotient energy estimate for a functional forcing.** Let `a` be uniformly
elliptic on the whole space with lower constant `λ`, and let `x ↦ a(x)` be `K`-Lipschitz in the
operator norm of its bilinear forms. Let `u ∈ H¹(ℝⁿ)` be such that the functional `v ↦ a(u, v)` is
bounded on the difference quotients in the direction `w`:

`|a(u, Dᵗ v)| ≤ M ‖∇v‖_{L²}` for every `v ∈ H¹(ℝⁿ)` and every step `t`.

Then `‖∇Dᵗ u‖_{L²} ≤ (M + K ‖w‖ ‖∇u‖_{L²}) / λ` for every step `t`.

For a weak solution of `-∂ⱼ(aⁱʲ ∂ᵢu) = f` with `f ∈ L²` the hypothesis holds with
`M = ‖w‖ ‖f‖_{L²}`, which is
`TauCeti.PDE.UniformlyEllipticOn.norm_gradient_differenceQuotient_le_of_lipschitzWith`. The
functional form also admits forcing terms in divergence form `-div F`, for which
`a(u, Dᵗ v) = ∫ ⟨F, ∇Dᵗ v⟩` is bounded by moving the difference quotient onto `F`. -/
theorem UniformlyEllipticOn.norm_gradient_differenceQuotient_le_of_abs_energyFormH1_le
    (ha : UniformlyEllipticOn univ a lam Lam)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x))
    {u : W1p mu ⊤ 2} (w : EuclideanSpace ℝ ι) {M : ℝ} (hM : 0 ≤ M)
    (hu : ∀ (t : ℝ) (v : W1p mu ⊤ 2), |energyFormH1 a 0 0 u
      (W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) v)|
        ≤ M * ‖W1p.gradient v‖)
    (t : ℝ) :
    ‖W1p.gradient (W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) u)‖
      ≤ (M + K * ‖w‖ * ‖W1p.gradient u‖) / lam := by
  have hlam := ha.pos
  have hbdd : Bornology.IsBounded (Set.range fun x => matrixBilinearForm (a x)) :=
    isBounded_iff_forall_norm_le.2 ⟨Lam, by
      rintro _ ⟨x, rfl⟩
      exact ha.opNorm_matrixBilinearForm_le (mem_univ x)⟩
  -- The discrete integration-by-parts estimate, with `Dᵗ u` in the second argument.
  have hDQ := abs_energyFormH1_differenceQuotient_add_le hbdd hK w t u
    (W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) u)
  obtain ⟨g, hg⟩ : ∃ g : W1p mu ⊤ 2,
      g = W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) u := ⟨_, rfl⟩
  rw [← hg] at hDQ ⊢
  -- Ellipticity bounds the Dirichlet energy of the difference quotient from below.
  have hlow : lam * ‖W1p.gradient g‖ ^ 2 ≤ energyFormH1 a 0 0 g g :=
    mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift (gamma := 0) ha
      (Continuous.aestronglyMeasurable (β := ι → ι → ℝ) <|
        continuous_of_continuous_matrixBilinearForm hK.continuous)
      aestronglyMeasurable_const (fun _ _ => rfl) (fun _ _ => by simp) (fun _ _ => le_rfl) g
  -- The hypothesis, tested against the reverse difference quotient of `Dᵗ u`.
  have hsol := hu (-t) g
  have hkey : lam * ‖W1p.gradient g‖ ^ 2
      ≤ (M + K * ‖w‖ * ‖W1p.gradient u‖) * ‖W1p.gradient g‖ := by
    have h1 := (abs_le.1 hDQ).2
    have h2 := (abs_le.1 hsol).1
    nlinarith
  rcases eq_or_lt_of_le (norm_nonneg (W1p.gradient g)) with hzero | hpos
  · rw [← hzero]
    exact div_nonneg (by positivity) hlam.le
  · rw [le_div_iff₀ hlam]
    nlinarith

/-! ### The localized equation -/

variable {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2} {ψ : EuclideanSpace ℝ ι → ℝ}

omit [DecidableEq ι] in
/-- **The weak equation tested against `ψ v`.** For a weak solution `u` of `-div(a ∇u) = f` in
`Ω`, a smooth `ψ` compactly supported in `Ω`, and `v ∈ H¹(ℝⁿ)`, the product `ψ v` is an
admissible test function with gradient `ψ ∇v + v ∇ψ`, so that

`∫_Ω ⟨∇v, a (ψ ∇u + u ∇ψ)⟩ = ∫_Ω (ψ f - ⟨∇ψ, a ∇u⟩) v + ∫_Ω u ⟨∇v, a ∇ψ⟩`. -/
private theorem setIntegral_matrixBilinearForm_cutoff_eq
    (hB : AEStronglyMeasurable (fun x => matrixBilinearForm (a x)) (mu.restrict Omega))
    (hΛ : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖matrixBilinearForm (a x)‖ ≤ Lam)
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) (v : W1p mu ⊤ 2) :
    ∫ x in Omega, matrixBilinearForm (a x) (W1p.gradient v x)
        (ψ x • W1p.gradient u x + W1p.value u x • ∇ ψ x) ∂mu =
      ∫ x in Omega, (ψ x * f x - matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x)) *
        W1p.value v x ∂mu +
      ∫ x in Omega, W1p.value u x * matrixBilinearForm (a x) (W1p.gradient v x) (∇ ψ x) ∂mu := by
  obtain ⟨M, hM, hψM, hgradM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hψc
  have hψM' : ∀ x ∈ Omega, |ψ x| ≤ M := fun x _ => hψM x
  have hgradM' : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ M := fun x _ => hgradM x
  have hle : mu.restrict (Omega : Set (EuclideanSpace ℝ ι)) ≤
      mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) :=
    Measure.restrict_mono (SetLike.coe_subset_coe.mpr le_top) le_rfl
  have hmem := ae_restrict_mem (μ := mu) Omega.isOpen.measurableSet
  -- `v` as an element of `H¹(Ω)`, and the test function `ψ v ∈ H¹₀(Ω)`.
  set vΩ := W1p.restrictL (le_top : Omega ≤ ⊤) v
  set v₀ := W1p.contDiffSMul ψ hψ hM hψM' hgradM' vΩ
  have hv₀ : v₀ ∈ w1p0Submodule mu Omega 2 :=
    W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (by norm_num) hψ hM hψM' hgradM'
      hψc hts vΩ
  have h := hu ⟨v₀, hv₀⟩
  simp only at h
  rw [energyFormH1_zero_zero_eq_setIntegral] at h
  -- The four integrands and their integrability on `Ω`.
  have hgu := Lp.memLp (W1p.gradient u)
  have huv := Lp.memLp (W1p.value u)
  have hgv : MemLp (fun x => W1p.gradient v x) 2 (mu.restrict Omega) :=
    (Lp.memLp (W1p.gradient v)).mono_measure hle
  have hvv : MemLp (fun x => W1p.value v x) 2 (mu.restrict Omega) :=
    (Lp.memLp (W1p.value v)).mono_measure hle
  have hψm : AEStronglyMeasurable ψ (mu.restrict Omega) := hψ.continuous.aestronglyMeasurable
  have hgψm : AEStronglyMeasurable (∇ ψ) (mu.restrict Omega) :=
    (ContDiff.continuous_gradient hψ).aestronglyMeasurable
  have happ : ∀ {p q : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι},
      AEStronglyMeasurable p (mu.restrict Omega) → AEStronglyMeasurable q (mu.restrict Omega) →
      AEStronglyMeasurable (fun x => matrixBilinearForm (a x) (p x) (q x)) (mu.restrict Omega) :=
    fun hp hq => ((continuous_fst.clm_apply (continuous_fst.comp continuous_snd)).clm_apply
      (continuous_snd.comp continuous_snd)).comp_aestronglyMeasurable (hB.prodMk (hp.prodMk hq))
  have hBψ : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ∀ η : EuclideanSpace ℝ ι,
      ‖matrixBilinearForm (a x) η (∇ ψ x)‖ ≤ Lam * M * ‖η‖ ∧
        ‖matrixBilinearForm (a x) (∇ ψ x) η‖ ≤ Lam * M * ‖η‖ := fun x hx η =>
    ⟨((matrixBilinearForm (a x)).le_of_opNorm₂_le_of_le (hΛ x hx) le_rfl (hgradM x)).trans_eq
      (by ring), (matrixBilinearForm (a x)).le_of_opNorm₂_le_of_le (hΛ x hx) (hgradM x) le_rfl⟩
  have hI1 : Integrable (fun x => ψ x * matrixBilinearForm (a x) (W1p.gradient v x)
      (W1p.gradient u x)) (mu.restrict Omega) :=
    ((hgv.norm.integrable_mul hgu.norm).const_mul (M * Lam)).mono'
      (hψm.mul (happ hgv.aestronglyMeasurable hgu.aestronglyMeasurable))
      (hmem.mono fun x hx => by
        rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs, mul_assoc]
        exact mul_le_mul (hψM x) (((matrixBilinearForm (a x)).le_opNorm₂ _ _).trans
          (by rw [mul_assoc]; gcongr; exact hΛ x hx)) (norm_nonneg _) hM)
  have hI2 : Integrable (fun x => W1p.value v x * matrixBilinearForm (a x) (∇ ψ x)
      (W1p.gradient u x)) (mu.restrict Omega) :=
    ((hvv.norm.integrable_mul hgu.norm).const_mul (Lam * M)).mono'
      (hvv.aestronglyMeasurable.mul (happ hgψm hgu.aestronglyMeasurable))
      (hmem.mono fun x hx => by
        rw [Pi.mul_apply, norm_mul, mul_left_comm]
        exact mul_le_mul_of_nonneg_left (hBψ x hx _).2 (norm_nonneg _))
  have hI3 : Integrable (fun x => ψ x * f x * W1p.value v x) (mu.restrict Omega) :=
    (((Lp.memLp f).norm.integrable_mul hvv.norm).const_mul M).mono'
      ((hψm.mul (Lp.aestronglyMeasurable f)).mul hvv.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        rw [Pi.mul_apply, norm_mul, norm_mul, Real.norm_eq_abs, mul_assoc]
        exact mul_le_mul_of_nonneg_right (hψM x) (by positivity))
  have hI4 : Integrable (fun x => W1p.value u x * matrixBilinearForm (a x) (W1p.gradient v x)
      (∇ ψ x)) (mu.restrict Omega) :=
    ((huv.norm.integrable_mul hgv.norm).const_mul (Lam * M)).mono'
      (huv.aestronglyMeasurable.mul (happ hgv.aestronglyMeasurable hgψm))
      (hmem.mono fun x hx => by
        rw [Pi.mul_apply, norm_mul, mul_left_comm]
        exact mul_le_mul_of_nonneg_left (hBψ x hx _).1 (norm_nonneg _))
  -- The tested equation: `∫ ψ B(∇v, ∇u) + ∫ v B(∇ψ, ∇u) = ∫ ψ f v`.
  have hlhs : ∫ x in Omega, matrixBilinearForm (a x) (W1p.gradient v₀ x) (W1p.gradient u x) ∂mu
      = ∫ x in Omega, (ψ x * matrixBilinearForm (a x) (W1p.gradient v x) (W1p.gradient u x)
        + W1p.value v x * matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x)) ∂mu := by
    refine integral_congr_ae ?_
    filter_upwards [W1p.gradient_contDiffSMul_ae hψ hM hψM' hgradM' vΩ,
      W1p.value_restrictL_ae le_top v, W1p.gradient_restrictL_ae le_top v] with x h1 h2 h3
    rw [h1, h2, h3, map_add, map_smul, map_smul, _root_.add_apply, _root_.smul_apply,
      _root_.smul_apply, smul_eq_mul, smul_eq_mul]
  have hrhs : ∫ x in Omega, f x * W1p.value v₀ x ∂mu =
      ∫ x in Omega, ψ x * f x * W1p.value v x ∂mu := by
    refine integral_congr_ae ?_
    filter_upwards [W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' vΩ,
      W1p.value_restrictL_ae le_top v] with x h1 h2
    rw [h1, h2, smul_eq_mul]
    ring
  rw [hlhs, hrhs, integral_add hI1 hI2] at h
  -- Split the left-hand side of the goal, and rearrange.
  have hsplit : ∫ x in Omega, matrixBilinearForm (a x) (W1p.gradient v x)
      (ψ x • W1p.gradient u x + W1p.value u x • ∇ ψ x) ∂mu =
        ∫ x in Omega, ψ x * matrixBilinearForm (a x) (W1p.gradient v x) (W1p.gradient u x) ∂mu +
        ∫ x in Omega, W1p.value u x * matrixBilinearForm (a x) (W1p.gradient v x) (∇ ψ x) ∂mu := by
    rw [← integral_add hI1 hI4]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [map_add, map_smul, smul_eq_mul]
  have hforce : ∫ x in Omega, (ψ x * f x - matrixBilinearForm (a x) (∇ ψ x)
      (W1p.gradient u x)) * W1p.value v x ∂mu = ∫ x in Omega, ψ x * f x * W1p.value v x ∂mu -
        ∫ x in Omega, W1p.value v x * matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x) ∂mu := by
    rw [← integral_sub hI3 hI2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  rw [hsplit, hforce]
  linarith

omit [DecidableEq ι] in
/-- **The energy of a localized weak solution.** Let `u` be a weak solution of `-div(a ∇u) = f`
in `Ω`, let `ψ` be smooth and compactly supported in `Ω`, and let `w ∈ H¹(ℝⁿ)` have gradient
`ψ ∇u + u ∇ψ` on `Ω` and zero off `Ω`, as the extension by zero of `ψ u` does. Let `ã` agree
with `a` on the support of `ψ`, and let `z ∈ H¹(ℝⁿ)` agree with `u` on `Ω ∩ supp ψ` and vanish
off `Ω`. Then for every `v ∈ H¹(ℝⁿ)`,

`ã(w, v) = ∫_Ω (ψ f - ⟨∇ψ, a ∇u⟩) v + ∫ z ⟨∇v, ã ∇ψ⟩`.

The first term is an `L²` forcing; the second is the divergence of the field `z ã ∇ψ`, whose
difference quotients are controlled by those of `z` when `ã` is Lipschitz. -/
private theorem energyFormH1_eq_setIntegral_add_integral {ã : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (hB : AEStronglyMeasurable (fun x => matrixBilinearForm (a x)) (mu.restrict Omega))
    (hΛ : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖matrixBilinearForm (a x)‖ ≤ Lam)
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι)))
    (hã : ∀ x ∈ tsupport ψ, ã x = a x) {w z : W1p mu ⊤ 2}
    (hwg : ∀ᵐ x ∂mu, W1p.gradient w x = (Omega : Set (EuclideanSpace ℝ ι)).indicator
      (fun y => ψ y • W1p.gradient u y + W1p.value u y • ∇ ψ y) x)
    (hzv : ∀ᵐ x ∂mu, x ∈ (Omega : Set (EuclideanSpace ℝ ι)) → x ∈ tsupport ψ →
      W1p.value z x = W1p.value u x)
    (hz0 : ∀ᵐ x ∂mu, x ∉ (Omega : Set (EuclideanSpace ℝ ι)) → W1p.value z x = 0)
    (v : W1p mu ⊤ 2) :
    energyFormH1 ã 0 0 w v =
      ∫ x in Omega, (ψ x * f x - matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x)) *
        W1p.value v x ∂mu +
      ∫ x, W1p.value z x * matrixBilinearForm (ã x) (W1p.gradient v x) (∇ ψ x) ∂mu := by
  have hΩ := Omega.isOpen.measurableSet
  have hint_top : ∀ F : EuclideanSpace ℝ ι → ℝ,
      ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)), F x ∂mu =
        ∫ x, F x ∂mu := fun F => by rw [Opens.coe_top, Measure.restrict_univ]
  -- Off the support of `ψ` the cutoff and its gradient vanish.
  have hψ0 : ∀ x ∉ tsupport ψ, ψ x = 0 ∧ ∇ ψ x = 0 := fun x hx =>
    ⟨image_eq_zero_of_notMem_tsupport hx, gradient_of_notMem_tsupport hx⟩
  -- The energy form of `w` is an integral over `Ω`, where `ã` may be replaced by `a`.
  have hE : energyFormH1 ã 0 0 w v = ∫ x in Omega, matrixBilinearForm (a x) (W1p.gradient v x)
      (ψ x • W1p.gradient u x + W1p.value u x • ∇ ψ x) ∂mu := by
    rw [energyFormH1_zero_zero_eq_setIntegral, hint_top, ← integral_indicator hΩ]
    refine integral_congr_ae ?_
    filter_upwards [hwg] with x hx
    rw [hx]
    by_cases hxΩ : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
    · rw [indicator_of_mem hxΩ, indicator_of_mem hxΩ]
      by_cases hxψ : x ∈ tsupport ψ
      · rw [hã x hxψ]
      · simp [(hψ0 x hxψ).1, (hψ0 x hxψ).2]
    · rw [indicator_of_notMem hxΩ, indicator_of_notMem hxΩ, map_zero]
  -- The second term, written over the whole space with `z` in place of `u`.
  have hz : ∫ x in Omega, W1p.value u x * matrixBilinearForm (a x) (W1p.gradient v x) (∇ ψ x) ∂mu
      = ∫ x, W1p.value z x * matrixBilinearForm (ã x) (W1p.gradient v x) (∇ ψ x) ∂mu := by
    rw [← integral_indicator hΩ]
    refine integral_congr_ae ?_
    filter_upwards [hzv, hz0] with x h1 h2
    by_cases hxΩ : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
    · rw [indicator_of_mem hxΩ]
      by_cases hxψ : x ∈ tsupport ψ
      · rw [h1 hxΩ hxψ, hã x hxψ]
      · simp [(hψ0 x hxψ).2]
    · rw [indicator_of_notMem hxΩ, h2 hxΩ, zero_mul]
  rw [hE, setIntegral_matrixBilinearForm_cutoff_eq hB hΛ hu hψ hψc hts v, hz]

omit [DecidableEq ι] in
/-- **The product rule for difference quotients, pointwise.** If `Φ` is a field of linear forms
bounded by `C` and `L`-Lipschitz, then for a real function `Z`, a vector `g`, a point `x`, a
direction `e` and a step `t`,

`|t⁻¹ (Z(x - t e) Φ(x - t e) g - Z(x) Φ(x) g)|`
  `≤ C |t⁻¹ (Z(x) - Z(x - t e))| ‖g‖ + L ‖e‖ |Z(x)| ‖g‖`. -/
private theorem norm_inv_mul_sub_le
    {Φ : EuclideanSpace ℝ ι → StrongDual ℝ (EuclideanSpace ℝ ι)} {C : ℝ} {L : ℝ≥0}
    (hC : ∀ x, ‖Φ x‖ ≤ C) (hL : LipschitzWith L Φ) {Z : EuclideanSpace ℝ ι → ℝ}
    {g x e : EuclideanSpace ℝ ι} {t : ℝ} :
    ‖t⁻¹ * (Z (x - t • e) * Φ (x - t • e) g - Z x * Φ x g)‖
      ≤ C * (‖t⁻¹ * (Z x - Z (x - t • e))‖ * ‖g‖) + L * ‖e‖ * (‖Z x‖ * ‖g‖) := by
  have hsplit : t⁻¹ * (Z (x - t • e) * Φ (x - t • e) g - Z x * Φ x g)
      = -(t⁻¹ * (Z x - Z (x - t • e))) * Φ (x - t • e) g
        + Z x * (t⁻¹ * (Φ (x - t • e) - Φ x) g) := by
    rw [_root_.sub_apply]
    ring
  -- The difference quotient of `Φ` is bounded by the Lipschitz constant.
  have hΦd : |t⁻¹| * ‖Φ (x - t • e) - Φ x‖ ≤ L * ‖e‖ := by
    have h1 : ‖Φ (x - t • e) - Φ x‖ ≤ L * (|t| * ‖e‖) := by
      simpa [dist_eq_norm, norm_smul] using hL.dist_le_mul (x - t • e) x
    rcases eq_or_ne t 0 with rfl | ht
    · simp only [_root_.inv_zero, abs_zero, zero_mul]
      positivity
    · calc |t⁻¹| * ‖Φ (x - t • e) - Φ x‖ ≤ |t⁻¹| * (L * (|t| * ‖e‖)) := by gcongr
        _ = L * ‖e‖ := by
            rw [abs_inv]
            field_simp
  have h2 : ‖Φ (x - t • e) g‖ ≤ C * ‖g‖ :=
    ((Φ (x - t • e)).le_opNorm g).trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
  have h3 : ‖t⁻¹ * (Φ (x - t • e) - Φ x) g‖ ≤ L * ‖e‖ * ‖g‖ := by
    rw [norm_mul, Real.norm_eq_abs]
    calc |t⁻¹| * ‖(Φ (x - t • e) - Φ x) g‖ ≤ |t⁻¹| * (‖Φ (x - t • e) - Φ x‖ * ‖g‖) := by
          gcongr
          exact (Φ (x - t • e) - Φ x).le_opNorm g
      _ = (|t⁻¹| * ‖Φ (x - t • e) - Φ x‖) * ‖g‖ := by ring
      _ ≤ L * ‖e‖ * ‖g‖ := by gcongr
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_neg]
  calc ‖t⁻¹ * (Z x - Z (x - t • e))‖ * ‖Φ (x - t • e) g‖ +
        ‖Z x‖ * ‖t⁻¹ * (Φ (x - t • e) - Φ x) g‖
      ≤ ‖t⁻¹ * (Z x - Z (x - t • e))‖ * (C * ‖g‖) + ‖Z x‖ * (L * ‖e‖ * ‖g‖) := by gcongr
    _ = C * (‖t⁻¹ * (Z x - Z (x - t • e))‖ * ‖g‖) + L * ‖e‖ * (‖Z x‖ * ‖g‖) := by ring

omit [DecidableEq ι] in
/-- **Moving a difference quotient onto a Lipschitz-weighted field.** Let `z ∈ H¹(ℝⁿ)` and let
`Φ` be a field of linear forms bounded by `C` and `L`-Lipschitz. For every `v ∈ H¹(ℝⁿ)`, every
direction `e` and every step `t`,

`|∫ z Φ(∇Dᵗ v)| ≤ ‖e‖ (C ‖∇z‖_{L²} + L ‖z‖_{L²}) ‖∇v‖_{L²}`.

A translation moves the difference quotient from `∇v` onto the field `z Φ`, and the product rule
for difference quotients splits `D⁻ᵗ(z Φ)` into `(D⁻ᵗ z) Φ(· - t e)`, bounded through
`‖D⁻ᵗ z‖_{L²} ≤ ‖e‖ ‖∇z‖_{L²}`, and `z D⁻ᵗ Φ`, bounded through the Lipschitz constant. -/
private theorem abs_integral_value_mul_gradient_differenceQuotient_le
    {Φ : EuclideanSpace ℝ ι → StrongDual ℝ (EuclideanSpace ℝ ι)} {C : ℝ} {L : ℝ≥0}
    (hC : ∀ x, ‖Φ x‖ ≤ C) (hL : LipschitzWith L Φ) (z v : W1p mu ⊤ 2)
    (e : EuclideanSpace ℝ ι) (t : ℝ) :
    |∫ x, W1p.value z x * Φ x (W1p.gradient
      (W1p.differenceQuotient le_rfl e t (Set.mapsTo_univ (· + t • e) _) v) x) ∂mu|
      ≤ ‖e‖ * (C * ‖W1p.gradient z‖ + L * ‖W1p.value z‖) * ‖W1p.gradient v‖ := by
  have hle : mu ≤ mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) := by
    rw [Opens.coe_top, Measure.restrict_univ]
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set Z : EuclideanSpace ℝ ι → ℝ := fun x => W1p.value z x
  set G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι := fun x => W1p.gradient v x
  set Dz := W1p.value (W1p.differenceQuotient le_rfl e (-t) (Set.mapsTo_univ (· + (-t) • e) _) z)
  have hZ : MemLp Z 2 mu := (Lp.memLp (W1p.value z)).mono_measure hle
  have hG : MemLp G 2 mu := (Lp.memLp (W1p.gradient v)).mono_measure hle
  have hDz : MemLp (Dz : EuclideanSpace ℝ ι → ℝ) 2 mu := (Lp.memLp Dz).mono_measure hle
  have hΦm : AEStronglyMeasurable Φ mu := hL.continuous.aestronglyMeasurable
  have happ : ∀ {p : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {q : EuclideanSpace ℝ ι →
      StrongDual ℝ (EuclideanSpace ℝ ι)}, AEStronglyMeasurable q mu →
      AEStronglyMeasurable p mu → AEStronglyMeasurable (fun x => q x (p x)) mu :=
    fun hq hp => (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hq.prodMk hp)
  -- Translates of `Z`, `G` and `Φ`.
  have hZs : MemLp (fun x => Z (x - t • e)) 2 mu := by
    have := hZ.comp_measurePreserving (measurePreserving_add_right mu (-(t • e)))
    simpa [Function.comp_def, sub_eq_add_neg] using this
  have hGs : MemLp (fun x => G (x + t • e)) 2 mu :=
    hG.comp_measurePreserving (measurePreserving_add_right mu _)
  have hΦs : AEStronglyMeasurable (fun x => Φ (x - t • e)) mu :=
    (hL.continuous.comp (continuous_sub_right _)).aestronglyMeasurable
  have hint : ∀ {P : EuclideanSpace ℝ ι → ℝ} {q : EuclideanSpace ℝ ι →
      StrongDual ℝ (EuclideanSpace ℝ ι)} {p : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι},
      MemLp P 2 mu → AEStronglyMeasurable q mu → (∀ x, ‖q x‖ ≤ C) → MemLp p 2 mu →
      Integrable (fun x => P x * q x (p x)) mu := fun {P q p} hP hq hqC hp =>
    ((hP.norm.integrable_mul hp.norm).const_mul C).mono'
      (hP.aestronglyMeasurable.mul (happ hq hp.aestronglyMeasurable))
      (Filter.Eventually.of_forall fun x => by
        rw [Pi.mul_apply, norm_mul, mul_left_comm]
        exact mul_le_mul_of_nonneg_left (((q x).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hqC x) (norm_nonneg _))) (norm_nonneg _))
  have hI1 := hint hZ hΦm hC hGs
  have hI2 := hint hZ hΦm hC hG
  have hI3 := hint hZs hΦs (fun x => hC _) hG
  -- The difference quotient, moved by a translation from `∇v` onto `z Φ`.
  have htrans : ∫ x, Z x * Φ x (G (x + t • e)) ∂mu =
      ∫ x, Z (x - t • e) * Φ (x - t • e) (G x) ∂mu := by
    rw [← integral_add_right_eq_self (fun x => Z (x - t • e) * Φ (x - t • e) (G x)) (t • e)]
    simp only [add_sub_cancel_right]
  have hrepr : ∫ x, W1p.value z x * Φ x (W1p.gradient
      (W1p.differenceQuotient le_rfl e t (Set.mapsTo_univ (· + t • e) _) v) x) ∂mu
      = ∫ x, t⁻¹ * (Z (x - t • e) * Φ (x - t • e) (G x) - Z x * Φ x (G x)) ∂mu := by
    calc _ = ∫ x, t⁻¹ * (Z x * Φ x (G (x + t • e)) - Z x * Φ x (G x)) ∂mu := by
          refine integral_congr_ae ?_
          filter_upwards [(W1p.gradient_differenceQuotient_ae le_rfl e t
            (Set.mapsTo_univ (· + t • e) _) v).filter_mono (ae_mono hle)] with x hx
          rw [hx, map_smul, map_sub, smul_eq_mul]
          ring
      _ = t⁻¹ * (∫ x, Z x * Φ x (G (x + t • e)) ∂mu - ∫ x, Z x * Φ x (G x) ∂mu) := by
          rw [integral_const_mul, integral_sub hI1 hI2]
      _ = _ := by
          rw [htrans, ← integral_sub hI3 hI2, ← integral_const_mul]
  -- The pointwise bound by the product rule for difference quotients.
  have hpt : ∀ᵐ x ∂mu, ‖t⁻¹ * (Z (x - t • e) * Φ (x - t • e) (G x) - Z x * Φ x (G x))‖
      ≤ C * (‖Dz x‖ * ‖G x‖) + L * ‖e‖ * (‖Z x‖ * ‖G x‖) := by
    filter_upwards [(W1p.value_differenceQuotient_ae le_rfl e (-t)
      (Set.mapsTo_univ (· + (-t) • e) _) z).filter_mono (ae_mono hle)] with x hx
    have hDx : Dz x = t⁻¹ * (Z x - Z (x - t • e)) := by
      rw [hx, neg_smul, ← sub_eq_add_neg, inv_neg]
      ring
    rw [hDx]
    exact norm_inv_mul_sub_le hC hL
  -- Cauchy--Schwarz, and the difference-quotient bound on `z`.
  have hDzG := Lp.integral_norm_mul_norm_le hle hle Dz (W1p.gradient v)
  have hZG := Lp.integral_norm_mul_norm_le hle hle (W1p.value z) (W1p.gradient v)
  have hDzn : ‖Dz‖ ≤ ‖e‖ * ‖W1p.gradient z‖ :=
    W1p.norm_value_differenceQuotient_le (by norm_num) e (-t) z
  have hint1 : Integrable (fun x => ‖Dz x‖ * ‖G x‖) mu := hDz.norm.integrable_mul hG.norm
  have hint2 : Integrable (fun x => ‖Z x‖ * ‖G x‖) mu := hZ.norm.integrable_mul hG.norm
  rw [hrepr]
  calc |∫ x, t⁻¹ * (Z (x - t • e) * Φ (x - t • e) (G x) - Z x * Φ x (G x)) ∂mu|
      ≤ ∫ x, ‖t⁻¹ * (Z (x - t • e) * Φ (x - t • e) (G x) - Z x * Φ x (G x))‖ ∂mu := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ x, (C * (‖Dz x‖ * ‖G x‖) + L * ‖e‖ * (‖Z x‖ * ‖G x‖)) ∂mu :=
        integral_mono_ae ((hI3.sub hI2).const_mul t⁻¹).norm
          ((hint1.const_mul C).add (hint2.const_mul _)) hpt
    _ = C * ∫ x, ‖Dz x‖ * ‖G x‖ ∂mu + L * ‖e‖ * ∫ x, ‖Z x‖ * ‖G x‖ ∂mu := by
        rw [integral_add (hint1.const_mul C) (hint2.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ C * (‖Dz‖ * ‖W1p.gradient v‖) + L * ‖e‖ * (‖W1p.value z‖ * ‖W1p.gradient v‖) := by
        gcongr
    _ ≤ C * ((‖e‖ * ‖W1p.gradient z‖) * ‖W1p.gradient v‖) +
          L * ‖e‖ * (‖W1p.value z‖ * ‖W1p.gradient v‖) := by gcongr
    _ = ‖e‖ * (C * ‖W1p.gradient z‖ + L * ‖W1p.value z‖) * ‖W1p.gradient v‖ := by ring

omit [DecidableEq ι] in
/-- **The localized forcing is bounded on difference quotients.** Let `u` be a weak solution of
`-div(a ∇u) = f` in `Ω`, with `a` bounded by `Λ` on `Ω`, let `ψ` be a smooth cutoff compactly
supported in `Ω`, and let `w`, `z` and `ã` be as in
`TauCeti.PDE.energyFormH1_eq_setIntegral_add_integral`, with `ã` bounded and Lipschitz on the
whole space. Then in every direction `e` there is `M ≥ 0` with

`|ã(w, Dᵗ v)| ≤ M ‖∇v‖_{L²}` for every `v ∈ H¹(ℝⁿ)` and every step `t`. -/
private theorem exists_abs_energyFormH1_differenceQuotient_le
    {ã : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (hB : AEStronglyMeasurable (fun x => matrixBilinearForm (a x)) (mu.restrict Omega))
    (hΛ : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖matrixBilinearForm (a x)‖ ≤ Lam)
    (hg : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι)))
    (hãa : ∀ x ∈ tsupport ψ, ã x = a x) {Λ' : ℝ}
    (hãΛ : ∀ x, ‖matrixBilinearForm (ã x)‖ ≤ Λ') {K' : ℝ≥0}
    (hK' : LipschitzWith K' fun x => matrixBilinearForm (ã x)) {w z : W1p mu ⊤ 2}
    (hwg : ∀ᵐ x ∂mu, W1p.gradient w x = (Omega : Set (EuclideanSpace ℝ ι)).indicator
      (fun y => ψ y • W1p.gradient u y + W1p.value u y • ∇ ψ y) x)
    (hzv' : ∀ᵐ x ∂mu, x ∈ (Omega : Set (EuclideanSpace ℝ ι)) → x ∈ tsupport ψ →
      W1p.value z x = W1p.value u x)
    (hz0 : ∀ᵐ x ∂mu, x ∉ (Omega : Set (EuclideanSpace ℝ ι)) → W1p.value z x = 0)
    (e : EuclideanSpace ℝ ι) :
    ∃ M, 0 ≤ M ∧ ∀ (t : ℝ) (v : W1p mu ⊤ 2), |energyFormH1 ã 0 0 w
      (W1p.differenceQuotient le_rfl e t (Set.mapsTo_univ (· + t • e) _) v)|
        ≤ M * ‖W1p.gradient v‖ := by
  have hΩ := Omega.isOpen.measurableSet
  have hleΩ : mu.restrict (Omega : Set (EuclideanSpace ℝ ι)) ≤
      mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) :=
    Measure.restrict_mono (SetLike.coe_subset_coe.mpr le_top) le_rfl
  have hΛ'0 : 0 ≤ Λ' := (norm_nonneg (matrixBilinearForm (ã 0))).trans (hãΛ 0)
  obtain ⟨M, hM, hψM, hgradM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hψc
  -- The field `Φ(x) = ⟨·, ã(x) ∇ψ(x)⟩` is bounded and Lipschitz.
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : EuclideanSpace ℝ ι → StrongDual ℝ (EuclideanSpace ℝ ι),
      ∀ x, Φ x = (matrixBilinearForm (ã x)).flip (∇ ψ x) := ⟨_, fun _ => rfl⟩
  have hΦC : ∀ x, ‖Φ x‖ ≤ Λ' * M := fun x => (hΦ x).symm ▸
    ((matrixBilinearForm (ã x)).flip.le_opNorm _).trans (by
      rw [ContinuousLinearMap.opNorm_flip]
      exact mul_le_mul (hãΛ x) (hgradM x) (norm_nonneg _) hΛ'0)
  obtain ⟨Lg, hLg⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    ((hψc.fderiv ℝ).comp_left (map_zero _)) (hψ.gradient_right (m := 1) (by simp)) one_ne_zero
  have hΦL : LipschitzWith (1 * K' * M.toNNReal + Λ'.toNNReal * Lg) Φ := by
    rw [show Φ = fun x => (matrixBilinearForm (ã x)).flip (∇ ψ x) from funext hΦ]
    exact LipschitzWith.clm_apply ((ContinuousLinearMap.flipₗᵢ ℝ _ _ _).lipschitzWith.comp hK') hLg
        (fun x => by
          rw [ContinuousLinearMap.opNorm_flip]
          exact (hãΛ x).trans (Real.le_coe_toNNReal _))
        (fun x => (hgradM x).trans (Real.le_coe_toNNReal _))
  -- The forcing of the localized equation is bounded on difference quotients.
  obtain ⟨G₀, hG₀x⟩ : ∃ G₀ : EuclideanSpace ℝ ι → ℝ,
      ∀ x, G₀ x = ψ x * f x - matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x) :=
    ⟨_, fun _ => rfl⟩
  have hG₀ : MemLp G₀ 2 (mu.restrict Omega) := by
    rw [funext hG₀x]
    have hmem := ae_restrict_mem (μ := mu) hΩ
    have hcont : Continuous fun p : (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) ×
        EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => p.1 p.2.1 p.2.2 :=
      (continuous_fst.clm_apply (continuous_fst.comp continuous_snd)).clm_apply
        (continuous_snd.comp continuous_snd)
    have hBm : AEStronglyMeasurable (fun x => matrixBilinearForm (a x) (∇ ψ x)
        (W1p.gradient u x)) (mu.restrict Omega) :=
      hcont.comp_aestronglyMeasurable (hB.prodMk
        ((ContDiff.continuous_gradient hψ).aestronglyMeasurable.prodMk
          (Lp.aestronglyMeasurable (W1p.gradient u))))
    refine MemLp.sub ((Lp.memLp f).of_le_mul (c := M)
      (hψ.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hψM x) (norm_nonneg _)))
      ((Lp.memLp (W1p.gradient u)).of_le_mul (c := Lam * M) hBm
        (hmem.mono fun x hx => (matrixBilinearForm (a x)).le_of_opNorm₂_le_of_le (hΛ x hx)
          (hgradM x) le_rfl))
  obtain ⟨G₀L, hG₀L⟩ : ∃ G₀L : Lp ℝ 2 (mu.restrict Omega), G₀L =ᵐ[mu.restrict Omega] G₀ :=
    ⟨hG₀.toLp G₀, hG₀.coeFn_toLp⟩
  refine ⟨‖e‖ * (‖G₀L‖ + (Λ' * M * ‖W1p.gradient z‖ +
    ↑(1 * K' * M.toNNReal + Λ'.toNNReal * Lg) * ‖W1p.value z‖)), by positivity, fun t v => ?_⟩
  have hsecond := abs_integral_value_mul_gradient_differenceQuotient_le hΦC hΦL z v e t
  have hv'n := W1p.norm_value_differenceQuotient_le (mu := mu) (by norm_num) e t v
  obtain ⟨v', hv'⟩ : ∃ v', v' = W1p.differenceQuotient le_rfl e t
    (Set.mapsTo_univ (· + t • e) _) v := ⟨_, rfl⟩
  rw [← hv'] at hsecond hv'n ⊢
  rw [energyFormH1_eq_setIntegral_add_integral hB hΛ hg hψ hψc hts hãa hwg hzv' hz0 v']
  simp only [← hG₀x]
  simp only [hΦ, ContinuousLinearMap.flip_apply] at hsecond
  have hfirst : |∫ x in Omega, G₀ x * W1p.value v' x ∂mu|
      ≤ ‖G₀L‖ * (‖e‖ * ‖W1p.gradient v‖) := by
    calc |∫ x in Omega, G₀ x * W1p.value v' x ∂mu|
        ≤ ∫ x in Omega, ‖G₀L x‖ * ‖W1p.value v' x‖ ∂mu := by
          rw [← Real.norm_eq_abs]
          refine (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae ?_)
          filter_upwards [hG₀L] with x hx
          rw [hx, norm_mul]
      _ ≤ ‖G₀L‖ * ‖W1p.value v'‖ := Lp.integral_norm_mul_norm_le le_rfl hleΩ _ _
      _ ≤ ‖G₀L‖ * (‖e‖ * ‖W1p.gradient v‖) := by gcongr
  refine (abs_add_le _ _).trans ?_
  calc _ ≤ ‖G₀L‖ * (‖e‖ * ‖W1p.gradient v‖) +
        ‖e‖ * (Λ' * M * ‖W1p.gradient z‖ + ↑(1 * K' * M.toNNReal + Λ'.toNNReal * Lg) *
          ‖W1p.value z‖) * ‖W1p.gradient v‖ := add_le_add hfirst hsecond
    _ = _ := by ring

/-! ### Interior `H²` regularity -/

/-- **Interior `H²` regularity for Lipschitz principal coefficients.** Let `a` be uniformly
elliptic on `Ω` with `x ↦ a(x)` Lipschitz on `Ω`, in the operator norm of its bilinear forms, let
`b, c ∈ L∞(Ω)`, and let `u ∈ H¹(Ω)` be a weak solution of

`-∂ⱼ(aⁱʲ ∂ᵢu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, with `f ∈ L²(Ω)`,

in the sense that `∫_Ω (⟨∇v, a ∇u⟩ + ⟨b, ∇u⟩ v + c u v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, with no
boundary condition on `u`. Then `u ∈ H²_loc(Ω)`: on every open `V` whose closure is compact and
contained in `Ω`, the restriction of `u` is the first-order part of an element of `W^{2,2}(V)`.

No regularity of `∂Ω`, sign of `c`, or smallness of the lower-order terms is assumed. For a
constant coefficient matrix this is
`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL`. -/
theorem UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LocallyLipschitzOn (Omega : Set (EuclideanSpace ℝ ι)) fun x => matrixBilinearForm (a x))
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {V : Opens (EuclideanSpace ℝ ι)} (hV : IsCompact (closure (V : Set (EuclideanSpace ℝ ι))))
    (hVΩ : closure (V : Set (EuclideanSpace ℝ ι)) ⊆ Omega) :
    ∃ U : Wkp mu V 2 2, Wkp.lowerOrder 1 U =
      W1p.restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hVΩ)) u := by
  have hΩ := Omega.isOpen.measurableSet
  have htop : mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) = mu := by
    rw [Opens.coe_top, Measure.restrict_univ]
  -- Measurability and boundedness of the coefficients on `Ω`; the lower-order terms are moved
  -- into the forcing.
  have hBc : ContinuousOn (fun x => matrixBilinearForm (a x)) Omega := hK.continuousOn
  have hB : AEStronglyMeasurable (fun x => matrixBilinearForm (a x)) (mu.restrict Omega) :=
    hBc.aestronglyMeasurable hΩ
  have hΛ : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖matrixBilinearForm (a x)‖ ≤ Lam :=
    fun x hx => ha.opNorm_matrixBilinearForm_le hx
  have ham : AEStronglyMeasurable a (mu.restrict Omega) :=
    ContinuousOn.aestronglyMeasurable (β := ι → ι → ℝ)
      (continuousOn_of_continuousOn_matrixBilinearForm hBc) hΩ
  have hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega) := by
    simpa using memLp_energyIntegrand_of_bounds (b := 0) (c := 0) (beta := 0) (gamma := 0)
      ha.upper_nonneg ham aestronglyMeasurable_const aestronglyMeasurable_const
      (fun x hx => ha.upper_bound hx) (fun _ _ => by simp) (fun _ _ => by simp)
  obtain ⟨g, hg⟩ := exists_forcing_energyFormH1_principal_eq hcoeff hb hc hu
  -- A cutoff `ψ` equal to one near `closure V`, and a cutoff `χ` equal to one near `supp ψ`.
  obtain ⟨ψ, hψ, -, hψ_one, hψc, hts⟩ := hV.exists_contDiff_cutoff Omega.isOpen hVΩ
  obtain ⟨χ, hχ, -, hχ_one, hχc, hχts⟩ :=
    hψc.isCompact.exists_contDiff_cutoff Omega.isOpen hts
  have hχ1 : ∀ x ∈ tsupport ψ, χ x = 1 := fun x hx => by
    simpa using interior_subset (hχ_one hx)
  -- A coefficient field elliptic and Lipschitz everywhere, equal to `a` near `supp ψ`.
  obtain ⟨ã, hã, ⟨K', hK'⟩, hãa⟩ :=
    exists_uniformlyEllipticOn_univ_lipschitzWith_eqOn ha hK hψc.isCompact hts
  -- The localized solution `w = ψ u` and the auxiliary `z = χ u`, extended by zero.
  obtain ⟨M, hM, hψM, hgradM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hψc
  obtain ⟨N, hN, hχN, hgradN⟩ := (hχ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hχc
  have hw := W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (p := 2) (by norm_num) hψ
    hM (fun x _ => hψM x) (fun x _ => hgradM x) hψc hts u
  have hz := W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (p := 2) (by norm_num) hχ
    hN (fun x _ => hχN x) (fun x _ => hgradN x) hχc hχts u
  set w : W1p mu ⊤ 2 := (W1p0.extendByZeroL le_top ⟨_, hw⟩ : W1p mu ⊤ 2)
  set z : W1p mu ⊤ 2 := (W1p0.extendByZeroL le_top ⟨_, hz⟩ : W1p mu ⊤ 2)
  have hwg := W1p.gradient_extendByZeroL_contDiffSMul_ae hψ hM (fun x _ => hψM x)
    (fun x _ => hgradM x) u hw
  have hzv := W1p.value_extendByZeroL_contDiffSMul_ae hχ hN (fun x _ => hχN x)
    (fun x _ => hgradN x) u hz
  have hzv' : ∀ᵐ x ∂mu, x ∈ (Omega : Set (EuclideanSpace ℝ ι)) → x ∈ tsupport ψ →
      W1p.value z x = W1p.value u x := hzv.mono fun x hx hxΩ hxψ => by
    rw [hx, indicator_of_mem hxΩ, hχ1 x hxψ, one_mul]
  have hz0 : ∀ᵐ x ∂mu, x ∉ (Omega : Set (EuclideanSpace ℝ ι)) → W1p.value z x = 0 :=
    hzv.mono fun x hx hxΩ => by rw [hx, indicator_of_notMem hxΩ]
  have hãΛ : ∀ x, ‖matrixBilinearForm (ã x)‖ ≤ Lam :=
    fun x => hã.opNorm_matrixBilinearForm_le (mem_univ x)
  -- The second weak derivatives of the localized solution, on the whole space.
  have hH2 : ∀ i j, ∃ G : Lp ℝ 2
      (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))),
      HasWeakLineDerivOn mu ⊤ (fun x => ⟪W1p.gradient w x, EuclideanSpace.basisFun ι ℝ j⟫_ℝ) G
        (EuclideanSpace.basisFun ι ℝ i) := fun i j => by
    obtain ⟨Mi, hMi, hforce⟩ := exists_abs_energyFormH1_differenceQuotient_le hB hΛ hg hψ hψc
      hts hãa hãΛ hK' hwg hzv' hz0 (EuclideanSpace.basisFun ι ℝ i)
    have hDQ := hã.norm_gradient_differenceQuotient_le_of_abs_energyFormH1_le hK'
      (EuclideanSpace.basisFun ι ℝ i) hMi hforce
    obtain ⟨G, -, hG⟩ := W1p.exists_norm_le_hasWeakLineDerivOn_inner_gradient_of_norm_gradient_le
      w (EuclideanSpace.basisFun ι ℝ i) hDQ (EuclideanSpace.basisFun ι ℝ j)
    exact ⟨G, hG⟩
  -- On `V`, the gradient of the localized solution is that of `u`.
  have hψ_V : ∀ x ∈ closure (V : Set (EuclideanSpace ℝ ι)), ψ x = 1 ∧ ∇ ψ x = 0 := fun x hx => by
    have hev : ψ =ᶠ[nhds x] fun _ => (1 : ℝ) := mem_interior_iff_mem_nhds.1 (hψ_one hx)
    exact ⟨hev.eq_of_nhds, hev.gradient_eq.trans (gradient_fun_const x 1)⟩
  have hgradV : ∀ᵐ x ∂mu.restrict V, W1p.gradient w x =
      W1p.gradient (W1p.restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hVΩ)) u) x := by
    filter_upwards [W1p.gradient_restrictL_ae (SetLike.coe_subset_coe.mp
        (subset_closure.trans hVΩ)) u,
      (ae_restrict_iff' V.isOpen.measurableSet).2 (hwg.mono fun x hx hxV =>
        (⟨hxV, hx⟩ : x ∈ (V : Set (EuclideanSpace ℝ ι)) ∧ W1p.gradient w x =
          (Omega : Set (EuclideanSpace ℝ ι)).indicator
            (fun y => ψ y • W1p.gradient u y + W1p.value u y • ∇ ψ y) x))]
      with x h1 h2
    obtain ⟨hxV, hx⟩ := h2
    have hxc := subset_closure hxV
    rw [h1, hx, indicator_of_mem (hVΩ hxc), (hψ_V x hxc).1, (hψ_V x hxc).2, one_smul, smul_zero,
      add_zero]
  have htopV : mu.restrict V ≤
      mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) := by
    rw [htop]
    exact Measure.restrict_le_self
  refine W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn _ (EuclideanSpace.basisFun ι ℝ)
    fun i j => ?_
  obtain ⟨G, hG⟩ := hH2 i j
  have hmem : MemLp G 2 (mu.restrict V) := (Lp.memLp G).mono_measure htopV
  refine ⟨hmem.toLp G, ((hG.mono le_top).congr_ae ?_).congr_ae_deriv hmem.coeFn_toLp.symm⟩
  filter_upwards [hgradV] with x hx
  rw [hx]

end PDE

end TauCeti
