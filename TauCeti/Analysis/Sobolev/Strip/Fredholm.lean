/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Strip.Operator
public import TauCeti.Analysis.Sobolev.Strip.Rellich

/-!
# Peetre's argument for first-order operators on the strip with boundary conditions

The linearized operators of Lagrangian Floer theory act on sections `ξ` of a trivial bundle with
fibre `V` over the strip `ℝ × [0, 1]` whose boundary values lie in two subspaces `F₀` and `F₁` of
`V`, the tangent spaces of the Lagrangians in a trivialization along the strip. Such an operator
`D ξ = M (ξ, ∂s ξ, ∂t ξ)`, with an essentially bounded coefficient field
`M : ℝ × ℝ → (V × V × V →L[ℝ] W)`, acts on `L²` jets of the strip by
`TauCeti.jetOperator 2 stripMeasure M`. That operator only involves the strip measure, so it
serves the cylinder and the strip alike, and its restriction to the Sobolev space
`TauCeti.StripSobolev.H1 F₀ F₁` is the realization `W^{1,2}_F(ℝ × [0, 1], V) → L²(ℝ × [0, 1], W)`
of `D`.

This file turns an elliptic estimate for `D` into the functional-analytic properties of that
realization, as `TauCeti.Analysis.Sobolev.Cylinder` does on the cylinder. The steps that do not
depend on the boundary conditions are proved once for every space of sections with square
integrable jets in `TauCeti.Analysis.Sobolev.Strip.Operator`
(`TauCeti.StripSobolev.norm_jetLp_le_of_setIntegral_le`,
`TauCeti.StripSobolev.finiteDimensional_ker_jetOperator_comp_subtypeL_of_forall_norm_jetLp_le`,
`TauCeti.StripSobolev.isFredholm_and_index_eq_of_isPreconnected`). This file states the
semi-Fredholm estimate for sections with boundary values in `F₀` and `F₁` as the hypothesis
`TauCeti.StripSobolev.HasSemiFredholmEstimate`, which it does not prove for any particular
operator, and combines it with Rellich's theorem on the strip
(`TauCeti.StripSobolev.isCompactOperator_restrictValue_comp_subtypeL`, from
`TauCeti.Analysis.Sobolev.Strip.Rellich`).

* **Peetre's argument.** Suppose that `D` satisfies the semi-Fredholm estimate
  (`TauCeti.StripSobolev.HasSemiFredholmEstimate`)

  `∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

  for every `C²` section `ξ` with boundary values in `F₀` and `F₁` that vanishes for `|s|` large.
  Restriction to `[-T, T] × [0, 1]` is compact on `W^{1,2}_F` by Rellich's theorem
  `TauCeti.StripSobolev.isCompactOperator_restrictValue_comp_subtypeL`, so the estimate is an a
  priori estimate with compact error on `W^{1,2}_F`, and the realization of `D` has
  finite-dimensional kernel (`TauCeti.StripSobolev.finiteDimensional_ker_jetOperator_comp_subtypeL`)
  and closed range (`TauCeti.StripSobolev.isClosed_range_jetOperator_comp_subtypeL`).
* **Families.** The realization depends continuously on `M` in `L^∞`
  (`TauCeti.continuousOn_jetOperator`). So along a family of coefficient fields,
  continuous in `L^∞` on a preconnected set and each satisfying a semi-Fredholm estimate, the
  realizations are all Fredholm with the same index as soon as one of them is Fredholm
  (`TauCeti.StripSobolev.isFredholm_and_index_eq_of_hasSemiFredholmEstimate`). This is how the
  Fredholm property and the index of a strip operator are read off from a model operator joined to
  it by such a path, without the regularity of weak solutions of the adjoint equation.
* **An estimate from below.** If `D` moreover bounds every test section in `L²` over the whole
  strip, `∫ ‖ξ‖² ≤ C' ∫ ‖D ξ‖²`, as stationary operators at nondegenerate chords do, the compact
  error disappears: `‖x‖ ≤ K ‖D x‖` on `W^{1,2}_F`
  (`TauCeti.StripSobolev.exists_forall_norm_le_mul_norm_jetOperator_comp_subtypeL`), and the
  realization is injective (`TauCeti.StripSobolev.ker_jetOperator_comp_subtypeL_eq_bot`).

The estimate is stated, as on the cylinder, for sections vanishing outside `(a, b) × ℝ`, with the
integrals of the left side and of `‖D ξ‖²` over `[a, b] × [0, 1]`. This is the form produced by
patching estimates on the two ends of the strip with an interior estimate.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., §3.1 and
  Appendix B, on the linearized operator with totally real boundary conditions and the
  semi-Fredholm estimate.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm theory of operators `∂s + J ∂t + S`.
* T. Kato, *Perturbation Theory for Linear Operators*, second edition, Chapter IV, §5.1, on the
  stability of the index.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace TauCeti.StripSobolev

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] {F₀ F₁ : Submodule ℝ V}

/-- The **semi-Fredholm estimate** with constants `C` and `T` for the first-order operator
`D ξ = M (ξ, ∂s ξ, ∂t ξ)` on the strip `ℝ × [0, 1]` with boundary conditions `F₀` and `F₁`: for
every `C²` section `ξ` with `ξ (s, 0) ∈ F₀` and `ξ (s, 1) ∈ F₁` for all `s`, vanishing for
`s ∉ (a, b)`,

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`,

the first two integrals over `[a, b] × [0, 1]`. -/
def HasSemiFredholmEstimate (F₀ F₁ : Submodule ℝ V) (M : ℝ × ℝ → V × V × V →L[ℝ] W)
    (C T : ℝ) : Prop :=
  ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s, ξ (s, 0) ∈ F₀) → (∀ s, ξ (s, 1) ∈ F₁) →
    ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
      ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z (1, 0)‖ ^ 2 +
          ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
        C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖M z (jet ξ z)‖ ^ 2) +
          ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2)

/-- The defining property of `TauCeti.StripSobolev.HasSemiFredholmEstimate`. -/
theorem hasSemiFredholmEstimate_iff {M : ℝ × ℝ → V × V × V →L[ℝ] W} {C T : ℝ} :
    HasSemiFredholmEstimate F₀ F₁ M C T ↔
      ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s, ξ (s, 0) ∈ F₀) → (∀ s, ξ (s, 1) ∈ F₁) →
        ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
          ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z (1, 0)‖ ^ 2 +
              ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
            C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖M z (jet ξ z)‖ ^ 2) +
              ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2) :=
  Iff.rfl

/-- A semi-Fredholm estimate gives `‖f‖ ≤ √C (‖D f‖ + ‖f|_{[-T, T] × [0, 1]}‖)` on the jets of
test sections. -/
private theorem norm_jetLp_le {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure)
    {C T : ℝ} (hest : HasSemiFredholmEstimate F₀ F₁ M C T) (ξ : testSection F₀ F₁) :
    ‖jetLp 2 (testSection F₀ F₁) ξ‖ ≤
      √(max C 0) * (‖jetOperator 2 stripMeasure M (jetLp 2 (testSection F₀ F₁) ξ)‖ +
        ‖restrictValue T (jetLp 2 (testSection F₀ F₁) ξ)‖) := by
  obtain ⟨hξ, hξ₀, hξ₁, R, hR⟩ := mem_testSection_iff.1 ξ.property
  have hR₀ : ∀ s t, max R 0 ≤ |s| → (ξ : ℝ × ℝ → V) (s, t) = 0 := fun s t hs ↦
    hR s t ((le_max_left R 0).trans hs)
  exact norm_jetLp_le_of_setIntegral_le hM (hξ.of_le (by norm_num)) hR₀
    (hest hξ hξ₀ hξ₁ (neg_le_self (le_max_right R 0)) fun s t hs ↦
      hR₀ s t (by rwa [mem_Ioo, ← abs_lt, not_lt] at hs))

/-- **Peetre's argument on the strip: finite-dimensional kernel.** Let `M` be an essentially
bounded coefficient field on the strip `ℝ × [0, 1]`, and suppose the first-order operator
`D ξ = M (ξ, ∂s ξ, ∂t ξ)` satisfies the semi-Fredholm estimate
(`TauCeti.StripSobolev.HasSemiFredholmEstimate`)

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

over `[a, b] × [0, 1]` for every `C²` section `ξ` with boundary values in `F₀` and `F₁` vanishing
for `s ∉ (a, b)`. Then the realization of `D` on `W^{1,2}_F(ℝ × [0, 1], V)` has
finite-dimensional kernel. -/
theorem finiteDimensional_ker_jetOperator_comp_subtypeL [FiniteDimensional ℝ V]
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure) {C T : ℝ}
    (hest : HasSemiFredholmEstimate F₀ F₁ M C T) :
    FiniteDimensional ℝ ((jetOperator 2 stripMeasure M).comp (H1 F₀ F₁).subtypeL).ker :=
  finiteDimensional_ker_jetOperator_comp_subtypeL_of_forall_norm_jetLp_le
    (isCompactOperator_restrictValue_comp_subtypeL F₀ F₁ T) (norm_jetLp_le hM hest)

/-- **Peetre's argument on the strip: closed range.** Under the semi-Fredholm estimate of
`TauCeti.StripSobolev.finiteDimensional_ker_jetOperator_comp_subtypeL`, the realization of `D` on
`W^{1,2}_F(ℝ × [0, 1], V)` has closed range in `L²(ℝ × [0, 1], W)`. -/
theorem isClosed_range_jetOperator_comp_subtypeL [FiniteDimensional ℝ V]
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure) {C T : ℝ}
    (hest : HasSemiFredholmEstimate F₀ F₁ M C T) :
    IsClosed (((jetOperator 2 stripMeasure M).comp (H1 F₀ F₁).subtypeL).range :
      Set (Lp W 2 stripMeasure)) :=
  isClosed_range_jetOperator_comp_subtypeL_of_forall_norm_jetLp_le
    (isCompactOperator_restrictValue_comp_subtypeL F₀ F₁ T) (norm_jetLp_le hM hest)

/-- **Fredholmness and the index along families of strip operators.** Let `M x` be essentially
bounded coefficient fields on the strip, depending continuously on `x` in `L^∞` on a
preconnected set `s`, whose first-order operators `D_x ξ = M x (ξ, ∂s ξ, ∂t ξ)` each satisfy a
semi-Fredholm estimate with boundary conditions `F₀` and `F₁`. If the realization
`D_{x₀} : W^{1,2}_F(ℝ × [0, 1], V) → L²(ℝ × [0, 1], W)` is Fredholm for one `x₀ ∈ s`, then every
`D_x` with `x ∈ s` is Fredholm, with the same index. -/
theorem isFredholm_and_index_eq_of_hasSemiFredholmEstimate [FiniteDimensional ℝ V]
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsPreconnected s)
    {M : X → ℝ × ℝ → V × V × V →L[ℝ] W} (hM : ∀ x ∈ s, MemLp (M x) ∞ stripMeasure)
    (hcont : ∀ x ∈ s, Tendsto (fun y ↦ eLpNorm (M y - M x) ∞ stripMeasure) (𝓝[s] x) (𝓝 0))
    (hest : ∀ x ∈ s, ∃ C T, HasSemiFredholmEstimate F₀ F₁ (M x) C T) {x₀ x : X}
    (hx₀ : x₀ ∈ s) (hx : x ∈ s)
    (h₀ : ((jetOperator 2 stripMeasure (M x₀)).comp (H1 F₀ F₁).subtypeL).IsFredholm) :
    ((jetOperator 2 stripMeasure (M x)).comp (H1 F₀ F₁).subtypeL).IsFredholm ∧
      ((jetOperator 2 stripMeasure (M x)).comp (H1 F₀ F₁).subtypeL).index =
        ((jetOperator 2 stripMeasure (M x₀)).comp (H1 F₀ F₁).subtypeL).index :=
  isFredholm_and_index_eq_of_isPreconnected hs hM hcont
    (fun z hz ↦ (hest z hz).elim fun _ ⟨_, h⟩ ↦
      finiteDimensional_ker_jetOperator_comp_subtypeL (hM z hz) h)
    (fun z hz ↦ (hest z hz).elim fun _ ⟨_, h⟩ ↦
      isClosed_range_jetOperator_comp_subtypeL (hM z hz) h) hx₀ hx h₀

/-- **An estimate from below on `W^{1,2}_F`.** Let `M` be an essentially bounded coefficient field
on the strip whose first-order operator `D ξ = M (ξ, ∂s ξ, ∂t ξ)` satisfies the semi-Fredholm
estimate (`TauCeti.StripSobolev.HasSemiFredholmEstimate`) with boundary conditions `F₀` and `F₁`,
and suppose that `D` also bounds the value of every test section in `L²` over the whole strip:
`∫ ‖ξ‖² ≤ C' ∫ ‖D ξ‖²`. Then the realization of `D` on `W^{1,2}_F(ℝ × [0, 1], V)` is bounded
below: `‖x‖ ≤ K ‖D x‖` for every `x`. The global `L²` bound removes the compact error term of the
semi-Fredholm estimate. -/
theorem exists_forall_norm_le_mul_norm_jetOperator_comp_subtypeL
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure) {C T C' : ℝ}
    (hest : HasSemiFredholmEstimate F₀ F₁ M C T)
    (hL2 : ∀ ξ : testSection F₀ F₁, ∫ z, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 ∂stripMeasure ≤
      C' * ∫ z, ‖M z (jet (ξ : ℝ × ℝ → V) z)‖ ^ 2 ∂stripMeasure) :
    ∃ K : ℝ≥0, ∀ x : H1 F₀ F₁,
      ‖x‖ ≤ K * ‖(jetOperator 2 stripMeasure M).comp (H1 F₀ F₁).subtypeL x‖ :=
  ⟨⟨√(max C 0) * (1 + √(max C' 0)), by positivity⟩,
    norm_le_mul_norm_jetOperator_comp_subtypeL_of_forall_norm_jetLp_le (Real.sqrt_nonneg _)
      (norm_jetLp_le hM hest) fun ξ ↦
        have ⟨hξ, _, _, _, hR⟩ := mem_testSection_iff.1 ξ.property
        norm_restrictValue_jetLp_le hM T hξ.continuous hR (hL2 ξ)⟩

/-- **Injectivity on `W^{1,2}_F`.** Under the hypotheses of
`TauCeti.StripSobolev.exists_forall_norm_le_mul_norm_jetOperator_comp_subtypeL`, a semi-Fredholm
estimate together with a global `L²` bound `∫ ‖ξ‖² ≤ C' ∫ ‖D ξ‖²` on test sections, the
realization of `D` on `W^{1,2}_F(ℝ × [0, 1], V)` has trivial kernel. -/
theorem ker_jetOperator_comp_subtypeL_eq_bot {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ stripMeasure) {C T C' : ℝ} (hest : HasSemiFredholmEstimate F₀ F₁ M C T)
    (hL2 : ∀ ξ : testSection F₀ F₁, ∫ z, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 ∂stripMeasure ≤
      C' * ∫ z, ‖M z (jet (ξ : ℝ × ℝ → V) z)‖ ^ 2 ∂stripMeasure) :
    ((jetOperator 2 stripMeasure M).comp (H1 F₀ F₁).subtypeL).ker = ⊥ := by
  obtain ⟨K, hK⟩ := exists_forall_norm_le_mul_norm_jetOperator_comp_subtypeL hM hest hL2
  exact LinearMap.ker_eq_bot.2 ((ContinuousLinearMap.antilipschitz_of_bound _ hK).injective)

end TauCeti.StripSobolev
