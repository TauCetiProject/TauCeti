/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.Analysis.CStarAlgebra.Trace.Basic
public import TauCeti.Analysis.CStarAlgebra.Trace.LowerSemicontinuous
import TauCeti.Algebra.Star.Polarization

/-!
# The domain ideal of a trace on a C⋆-algebra and the linear extension

For a trace `τ` on a C⋆-algebra `B` (`TauCeti.IsTrace`), the **domain** `𝔪_τ` is the complex
span of the finite part `𝔪_τ⁺ = {x ∈ B₊ : τ(x) < ∞}` (`TauCeti.domain`). Following
Dixmier 1963, Lemme 3, p. 226:

* `𝔪_τ` is the span of the products `y⋆x` with `x, y` in the square-integrable ideal
  `𝔫_τ = {x : τ(x⋆x) < ∞}` (`TauCeti.IsTrace.domain_eq_span_star_mul`). A positive
  `x ∈ 𝔪_τ⁺` is `b⋆b` with `b ∈ 𝔫_τ`, and conversely the polarization
  `4 y⋆x = Σ_{k=0}^{3} iᵏ (x + iᵏy)⋆(x + iᵏy)` writes `y⋆x` through elements of `𝔪_τ⁺`.
* Hence `𝔪_τ` is a self-adjoint two-sided ideal (`TauCeti.IsTrace.domainIdeal`), since `𝔫_τ` is
  one: `a y⋆x = (y a⋆)⋆x`.
* `𝔪_τ ∩ B₊ = 𝔪_τ⁺` (`TauCeti.IsTrace.mem_domain_iff_of_nonneg`): every element of `𝔪_τ` is
  `(p - q) + i (r - s)` with `p, q, r, s ∈ 𝔪_τ⁺`, so a positive element of `𝔪_τ`, being
  self-adjoint, equals `p - q ≤ p`, and `𝔪_τ⁺` is hereditary.
* `τ` extends uniquely to a complex-linear functional on `𝔪_τ`
  (`TauCeti.IsTrace.existsUnique_linearMap`). The self-adjoint elements of `𝔪_τ` are the
  differences `p - q`, and `p - q = p' - q'` forces `τ(p) - τ(q) = τ(p') - τ(q')` by additivity;
  this real value (`TauCeti.selfAdjointTrace`) is real-linear, and the extension is
  `z ↦ τ(ℜ z) + i τ(ℑ z)` (`TauCeti.IsTrace.linearMap`).
* The extension is tracial: `τ(xz) = τ(zx)` for `x ∈ 𝔪_τ`, `z ∈ B`
  (`TauCeti.IsTrace.linearMap_mul_comm`). Polarizing the trace identity gives
  `τ(y⋆x) = τ(xy⋆)` for `x, y ∈ 𝔫_τ`, and for `x = b⋆b ∈ 𝔪_τ⁺` (`b ∈ 𝔫_τ`) both `τ(b⋆bz)`
  and `τ(zb⋆b)` equal `τ(bzb⋆)`.
* When `τ` is densely defined (`TauCeti.IsDenselyDefined`), `𝔪_τ` is dense in `B`
  (`TauCeti.IsDenselyDefined.dense_domain`): its closure is a subspace containing `B₊`, which
  spans `B`. Since `𝔪_τ ⊆ 𝔫_τ`, so is `𝔫_τ`
  (`TauCeti.IsTrace.dense_sqIntegrable_of_isDenselyDefined`).
* A trace finite on `B₊` has `𝔪_τ = B`; for the trace of a positive tracial functional `ω` the
  extension is `ω` itself (`TauCeti.PositiveTracialFunctional.linearMap_toTrace`).

## Main definitions

* `TauCeti.domain`: the domain `𝔪_τ = span_ℂ 𝔪_τ⁺` of a trace.
* `TauCeti.IsTrace.domainIdeal`: `𝔪_τ` as a two-sided ideal.
* `TauCeti.selfAdjointTrace`: the real value `τ(p) - τ(q)` at a difference `p - q`.
* `TauCeti.IsTrace.linearMap`: the linear extension of `τ` to `𝔪_τ`.

## Main results

* `TauCeti.IsTrace.domain_eq_span_star_mul`: `𝔪_τ = span{y⋆x : x, y ∈ 𝔫_τ}`.
* `TauCeti.IsTrace.mem_domain_iff`: the elements of `𝔪_τ` are the `(p - q) + i (r - s)` with
  `p, q, r, s ∈ 𝔪_τ⁺`.
* `TauCeti.IsTrace.mul_mem_domain_left`, `TauCeti.IsTrace.mul_mem_domain_right`,
  `TauCeti.star_mem_domain`: `𝔪_τ` is a self-adjoint two-sided ideal.
* `TauCeti.IsTrace.mem_domain_iff_of_nonneg`, `TauCeti.IsTrace.domain_inter_nonneg`:
  `𝔪_τ ∩ B₊ = 𝔪_τ⁺`.
* `TauCeti.IsTrace.domain_subset_sqIntegrable`: `𝔪_τ ⊆ 𝔫_τ`.
* `TauCeti.IsTrace.existsUnique_linearMap`, `TauCeti.IsTrace.eq_linearMap`: the unique linear
  extension, which is real on self-adjoint elements
  (`TauCeti.IsTrace.linearMap_apply_of_isSelfAdjoint`) and equals `τ` on `𝔪_τ⁺`
  (`TauCeti.IsTrace.linearMap_apply_of_mem_finitePart`).
* `TauCeti.IsTrace.linearMap_star_mul_comm`, `TauCeti.IsTrace.linearMap_mul_comm`: traciality
  of the extension.
* `TauCeti.IsDenselyDefined.dense_domain`,
  `TauCeti.IsTrace.dense_sqIntegrable_of_isDenselyDefined`: `𝔪_τ` and `𝔫_τ` are dense when `τ`
  is densely defined.
* `TauCeti.domain_eq_top_of_lt_top`, `TauCeti.mem_domain_of_lt_top`,
  `TauCeti.PositiveTracialFunctional.linearMap_toTrace`: bounded traces.

## References

* Jacques Dixmier, *Traces sur les C*-algèbres*, Ann. Inst. Fourier (Grenoble) 13 (1963),
  219–262. Chapitre I: Lemme 3, p. 226.
-/

public section

open scoped ENNReal NNReal ComplexOrder ComplexStarModule

namespace TauCeti

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {τ : B → ℝ≥0∞}

variable (τ) in
/-- The **domain** `𝔪_τ = span_ℂ 𝔪_τ⁺` of a trace: the complex span of its finite part. -/
def domain : Submodule ℂ B :=
  Submodule.span ℂ (finitePart τ)

omit [StarOrderedRing B] in
/-- The domain of `τ` is the span of its finite part. -/
theorem domain_def : domain τ = Submodule.span ℂ (finitePart τ) :=
  (rfl)

omit [StarOrderedRing B] in
/-- The finite part `𝔪_τ⁺` lies in the domain `𝔪_τ`. -/
theorem finitePart_subset_domain : finitePart τ ⊆ domain τ :=
  Submodule.subset_span

namespace IsTrace

/-- A real multiple `t (p - q)` of a difference of elements of `𝔪_τ⁺` is again such a
difference. -/
private theorem exists_real_smul_sub (hτ : IsTrace τ) (t : ℝ) {p q : B} (hp : p ∈ finitePart τ)
    (hq : q ∈ finitePart τ) :
    ∃ p' ∈ finitePart τ, ∃ q' ∈ finitePart τ, t • (p - q) = p' - q' := by
  rcases le_total 0 t with ht | ht
  · lift t to ℝ≥0 using ht
    exact ⟨_, hτ.smul_mem_finitePart t hp, _, hτ.smul_mem_finitePart t hq, smul_sub _ _ _⟩
  · obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, (s : ℝ) = -t := ⟨⟨-t, neg_nonneg.2 ht⟩, rfl⟩
    refine ⟨_, hτ.smul_mem_finitePart s hq, _, hτ.smul_mem_finitePart s hp, ?_⟩
    rw [hs, neg_smul, neg_smul, smul_sub]
    abel

/-- **Decomposition of the domain.** Every element of `𝔪_τ` is `(p - q) + i (r - s)` with
`p, q, r, s ∈ 𝔪_τ⁺`. -/
theorem exists_eq_sub_add_I_smul_sub (hτ : IsTrace τ) {z : B} (hz : z ∈ domain τ) :
    ∃ p ∈ finitePart τ, ∃ q ∈ finitePart τ, ∃ r ∈ finitePart τ, ∃ s ∈ finitePart τ,
      z = (p - q) + Complex.I • (r - s) := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    exact ⟨x, hx, 0, hτ.zero_mem_finitePart, 0, hτ.zero_mem_finitePart, 0,
      hτ.zero_mem_finitePart, by simp⟩
  | zero =>
    exact ⟨0, hτ.zero_mem_finitePart, 0, hτ.zero_mem_finitePart, 0, hτ.zero_mem_finitePart, 0,
      hτ.zero_mem_finitePart, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨p, hp, q, hq, r, hr, s, hs, rfl⟩ := hx
    obtain ⟨p', hp', q', hq', r', hr', s', hs', rfl⟩ := hy
    refine ⟨p + p', hτ.add_mem_finitePart hp hp', q + q', hτ.add_mem_finitePart hq hq',
      r + r', hτ.add_mem_finitePart hr hr', s + s', hτ.add_mem_finitePart hs hs', ?_⟩
    rw [smul_sub, smul_sub, smul_sub, smul_add, smul_add]
    abel
  | smul c x _ hx =>
    obtain ⟨p, hp, q, hq, r, hr, s, hs, rfl⟩ := hx
    -- `c • ((p - q) + i (r - s)) = (a (p - q) - b (r - s)) + i (b (p - q) + a (r - s))`
    obtain ⟨p₁, hp₁, q₁, hq₁, h₁⟩ := hτ.exists_real_smul_sub c.re hp hq
    obtain ⟨p₂, hp₂, q₂, hq₂, h₂⟩ := hτ.exists_real_smul_sub (-c.im) hr hs
    obtain ⟨p₃, hp₃, q₃, hq₃, h₃⟩ := hτ.exists_real_smul_sub c.im hp hq
    obtain ⟨p₄, hp₄, q₄, hq₄, h₄⟩ := hτ.exists_real_smul_sub c.re hr hs
    refine ⟨p₁ + p₂, hτ.add_mem_finitePart hp₁ hp₂, q₁ + q₂, hτ.add_mem_finitePart hq₁ hq₂,
      p₃ + p₄, hτ.add_mem_finitePart hp₃ hp₄, q₃ + q₄, hτ.add_mem_finitePart hq₃ hq₄, ?_⟩
    have key : c • ((p - q) + Complex.I • (r - s)) =
        (c.re • (p - q) + (-c.im) • (r - s)) +
          Complex.I • (c.im • (p - q) + c.re • (r - s)) := by
      conv_lhs => rw [← Complex.re_add_im c]
      simp only [← Complex.coe_smul]
      match_scalars
      · ring
      · ring
      · linear_combination (c.im : ℂ) * Complex.I_sq
      · linear_combination -(c.im : ℂ) * Complex.I_sq
    rw [key, h₁, h₂, h₃, h₄]
    module

/-- Membership in `𝔪_τ`: the elements of the domain are exactly the `(p - q) + i (r - s)` with
`p, q, r, s ∈ 𝔪_τ⁺`. -/
theorem mem_domain_iff (hτ : IsTrace τ) {z : B} :
    z ∈ domain τ ↔ ∃ p ∈ finitePart τ, ∃ q ∈ finitePart τ, ∃ r ∈ finitePart τ,
      ∃ s ∈ finitePart τ, z = (p - q) + Complex.I • (r - s) := by
  refine ⟨hτ.exists_eq_sub_add_I_smul_sub, ?_⟩
  rintro ⟨p, hp, q, hq, r, hr, s, hs, rfl⟩
  have h (a : B) (ha : a ∈ finitePart τ) : a ∈ domain τ := finitePart_subset_domain ha
  exact Submodule.add_mem _ (Submodule.sub_mem _ (h p hp) (h q hq))
    (Submodule.smul_mem _ _ (Submodule.sub_mem _ (h r hr) (h s hs)))

/-- A self-adjoint element of `𝔪_τ` is a difference `p - q` of elements of `𝔪_τ⁺`. -/
theorem exists_eq_sub_of_isSelfAdjoint (hτ : IsTrace τ) {z : B} (hz : z ∈ domain τ)
    (hsa : IsSelfAdjoint z) : ∃ p ∈ finitePart τ, ∃ q ∈ finitePart τ, z = p - q := by
  obtain ⟨p, hp, q, hq, r, hr, s, hs, rfl⟩ := hτ.exists_eq_sub_add_I_smul_sub hz
  -- `p - q` and `r - s` are self-adjoint, so the imaginary part `r - s` vanishes.
  have hpq : IsSelfAdjoint (p - q) :=
    (mem_finitePart.1 hp).1.isSelfAdjoint.sub (mem_finitePart.1 hq).1.isSelfAdjoint
  have hrs : IsSelfAdjoint (r - s) :=
    (mem_finitePart.1 hr).1.isSelfAdjoint.sub (mem_finitePart.1 hs).1.isSelfAdjoint
  have h0 : Complex.I • (r - s) = 0 := by
    have h := hsa.star_eq
    simp only [star_add, star_smul, hpq.star_eq, hrs.star_eq, Complex.star_def,
      Complex.conj_I] at h
    have h2 : (2 : ℂ) • (Complex.I • (r - s)) = 0 := by linear_combination (norm := module) -h
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  exact ⟨p, hp, q, hq, by rw [h0, add_zero]⟩

/-- **`𝔪_τ ∩ B₊ = 𝔪_τ⁺`.** A positive element lies in the domain of a trace exactly when its trace
is finite. -/
theorem mem_domain_iff_of_nonneg (hτ : IsTrace τ) {x : B} (hx : 0 ≤ x) :
    x ∈ domain τ ↔ x ∈ finitePart τ := by
  refine ⟨fun h ↦ ?_, fun h ↦ finitePart_subset_domain h⟩
  obtain ⟨p, hp, q, hq, rfl⟩ := hτ.exists_eq_sub_of_isSelfAdjoint h hx.isSelfAdjoint
  exact hτ.mem_finitePart_of_le hp hx (sub_le_self _ (mem_finitePart.1 hq).1)

/-- **`𝔪_τ ∩ B₊ = 𝔪_τ⁺`**, as an equality of sets. -/
theorem domain_inter_nonneg (hτ : IsTrace τ) :
    (domain τ : Set B) ∩ {x | 0 ≤ x} = finitePart τ := by
  ext x
  exact ⟨fun h ↦ (hτ.mem_domain_iff_of_nonneg h.2).1 h.1,
    fun h ↦ ⟨finitePart_subset_domain h, (mem_finitePart.1 h).1⟩⟩

/-- For `x ∈ 𝔫_τ`, the product `x⋆x` lies in the domain. -/
theorem _root_.TauCeti.star_mul_self_mem_domain {x : B} (hx : x ∈ sqIntegrable τ) :
    star x * x ∈ domain τ :=
  finitePart_subset_domain (star_mul_self_mem_finitePart_iff.2 hx)

/-- For `x, y ∈ 𝔫_τ`, the product `y⋆x` lies in the domain, by polarization. -/
theorem star_mul_mem_domain (hτ : IsTrace τ) {x y : B} (hx : x ∈ sqIntegrable τ)
    (hy : y ∈ sqIntegrable τ) : star y * x ∈ domain τ := by
  have hmem (c : ℂ) : x + c • y ∈ sqIntegrable τ :=
    hτ.add_mem_sqIntegrable hx (hτ.smul_mem_sqIntegrable c hy)
  have key := star_mul_polarization y x
  have h4 : (4 : ℂ) • (star y * x) ∈ domain τ := by
    rw [key]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_
    · simpa using star_mul_self_mem_domain (hmem 1)
    · exact Submodule.smul_mem _ _ (star_mul_self_mem_domain (hmem Complex.I))
    · simpa [sub_eq_add_neg] using star_mul_self_mem_domain (hmem (-1))
    · refine Submodule.smul_mem _ _ ?_
      simpa [sub_eq_add_neg] using star_mul_self_mem_domain (hmem (-Complex.I))
  simpa [smul_smul] using Submodule.smul_mem _ (4⁻¹ : ℂ) h4

/-- For `x ∈ 𝔫_τ`, the product `xx⋆` lies in the domain. -/
theorem mul_star_self_mem_domain (hτ : IsTrace τ) {x : B} (hx : x ∈ sqIntegrable τ) :
    x * star x ∈ domain τ :=
  finitePart_subset_domain (hτ.mul_star_self_mem_finitePart_iff.2 hx)

/-- For `x, y ∈ 𝔫_τ`, the product `xy⋆` lies in the domain. -/
theorem mul_star_mem_domain (hτ : IsTrace τ) {x y : B} (hx : x ∈ sqIntegrable τ)
    (hy : y ∈ sqIntegrable τ) : x * star y ∈ domain τ := by
  simpa using hτ.star_mul_mem_domain (hτ.star_mem_sqIntegrable hy) (hτ.star_mem_sqIntegrable hx)

/-- **`𝔪_τ = span{y⋆x : x, y ∈ 𝔫_τ}`** (Dixmier 1963, Lemme 3, p. 226). -/
theorem domain_eq_span_star_mul (hτ : IsTrace τ) :
    domain τ = Submodule.span ℂ
      {z | ∃ x ∈ sqIntegrable τ, ∃ y ∈ sqIntegrable τ, z = star y * x} := by
  refine le_antisymm (Submodule.span_le.2 fun z hz ↦ ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨b, hb, rfl⟩ := exists_eq_star_mul_self_of_mem_finitePart hz
    exact Submodule.subset_span ⟨b, hb, b, hb, rfl⟩
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    exact hτ.star_mul_mem_domain hx hy

/-- `𝔪_τ` is a left ideal. -/
theorem mul_mem_domain_left (hτ : IsTrace τ) (a : B) {z : B} (hz : z ∈ domain τ) :
    a * z ∈ domain τ := by
  rw [hτ.domain_eq_span_star_mul] at hz ⊢
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    refine Submodule.subset_span ⟨x, hx, y * star a, hτ.mul_mem_sqIntegrable_right _ hy, ?_⟩
    simp [star_mul, mul_assoc]
  | zero => simp
  | add z w _ _ hz hw => rw [mul_add]; exact Submodule.add_mem _ hz hw
  | smul c z _ hz => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hz

/-- `𝔪_τ` is self-adjoint. -/
theorem _root_.TauCeti.star_mem_domain {z : B} (hz : z ∈ domain τ) : star z ∈ domain τ := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    exact finitePart_subset_domain (by rwa [(mem_finitePart.1 hz).1.isSelfAdjoint.star_eq])
  | zero => simp
  | add z w _ _ hz hw => rw [star_add]; exact Submodule.add_mem _ hz hw
  | smul c z _ hz => rw [star_smul]; exact Submodule.smul_mem _ _ hz

/-- `𝔪_τ` is a right ideal. -/
theorem mul_mem_domain_right (hτ : IsTrace τ) (a : B) {z : B} (hz : z ∈ domain τ) :
    z * a ∈ domain τ := by
  simpa using star_mem_domain (hτ.mul_mem_domain_left (star a) (star_mem_domain hz))

/-- The domain `𝔪_τ` of a trace as a two-sided ideal (Dixmier 1963, Lemme 3, p. 226). -/
def domainIdeal (hτ : IsTrace τ) : TwoSidedIdeal B :=
  .mk' (domain τ) (Submodule.zero_mem _) (Submodule.add_mem _)
    (fun hx ↦ by simpa using Submodule.neg_mem _ hx) (hτ.mul_mem_domain_left _)
    (hτ.mul_mem_domain_right _)

/-- The carrier of `hτ.domainIdeal` is `𝔪_τ`. -/
@[simp]
theorem coe_domainIdeal (hτ : IsTrace τ) : (hτ.domainIdeal : Set B) = domain τ :=
  Set.ext fun _ ↦ TwoSidedIdeal.mem_mk' ..

/-- Membership in `hτ.domainIdeal` is membership in `𝔪_τ`. -/
@[simp]
theorem mem_domainIdeal (hτ : IsTrace τ) {x : B} : x ∈ hτ.domainIdeal ↔ x ∈ domain τ :=
  TwoSidedIdeal.mem_mk' ..

/-- `𝔪_τ ⊆ 𝔫_τ`: the domain lies in the square-integrable ideal. -/
theorem domain_subset_sqIntegrable (hτ : IsTrace τ) : (domain τ : Set B) ⊆ sqIntegrable τ := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, hb, rfl⟩ := exists_eq_star_mul_self_of_mem_finitePart hz
    exact hτ.mul_mem_sqIntegrable_left _ hb
  | zero => exact hτ.zero_mem_sqIntegrable
  | add z w _ _ hz hw => exact hτ.add_mem_sqIntegrable hz hw
  | smul c z _ hz => exact hτ.smul_mem_sqIntegrable c hz

/-! ### The linear extension -/

omit [StarOrderedRing B] in
/-- The real-valued trace `x ↦ τ(x)` is additive on `𝔪_τ⁺`. -/
theorem toReal_map_add (hτ : IsTrace τ) {p q : B} (hp : p ∈ finitePart τ)
    (hq : q ∈ finitePart τ) : (τ (p + q)).toReal = (τ p).toReal + (τ q).toReal := by
  rw [mem_finitePart] at hp hq
  rw [hτ.map_add_of_nonneg hp.1 hq.1, ENNReal.toReal_add hp.2.ne hq.2.ne]

omit [StarOrderedRing B] in
/-- Differences in `𝔪_τ⁺` determine differences of traces: `p - q = p' - q'` gives
`τ(p) - τ(q) = τ(p') - τ(q')`. -/
theorem toReal_sub_eq_of_sub_eq (hτ : IsTrace τ) {p q p' q' : B} (hp : p ∈ finitePart τ)
    (hq : q ∈ finitePart τ) (hp' : p' ∈ finitePart τ) (hq' : q' ∈ finitePart τ)
    (h : p - q = p' - q') : (τ p).toReal - (τ q).toReal = (τ p').toReal - (τ q').toReal := by
  have h' := congrArg (fun x ↦ (τ x).toReal) (sub_eq_sub_iff_add_eq_add.1 h)
  simp only [hτ.toReal_map_add hp hq', hτ.toReal_map_add hp' hq] at h'
  linarith

end IsTrace

variable (τ) in
/-- The real trace `τ(p) - τ(q)` of a difference `p - q` of elements `p, q ∈ 𝔪_τ⁺`, which by
`TauCeti.IsTrace.selfAdjointTrace_sub` does not depend on the choice of `p` and `q`; it is `0` at
elements that are not such differences. The self-adjoint elements of `𝔪_τ` are such differences
(`TauCeti.IsTrace.exists_eq_sub_of_isSelfAdjoint`). -/
noncomputable def selfAdjointTrace (h : B) : ℝ :=
  open Classical in
  if hh : ∃ pq : B × B, pq.1 ∈ finitePart τ ∧ pq.2 ∈ finitePart τ ∧ h = pq.1 - pq.2 then
    (τ hh.choose.1).toReal - (τ hh.choose.2).toReal
  else 0

namespace IsTrace

omit [StarOrderedRing B] in
/-- `selfAdjointTrace τ (p - q) = τ(p) - τ(q)` for `p, q ∈ 𝔪_τ⁺`. -/
theorem selfAdjointTrace_sub (hτ : IsTrace τ) {p q : B} (hp : p ∈ finitePart τ)
    (hq : q ∈ finitePart τ) : selfAdjointTrace τ (p - q) = (τ p).toReal - (τ q).toReal := by
  have hh : ∃ pq : B × B, pq.1 ∈ finitePart τ ∧ pq.2 ∈ finitePart τ ∧ p - q = pq.1 - pq.2 :=
    ⟨(p, q), hp, hq, rfl⟩
  rw [selfAdjointTrace, dite_eq_left hh]
  obtain ⟨h₁, h₂, h₃⟩ := hh.choose_spec
  exact (hτ.toReal_sub_eq_of_sub_eq hp hq h₁ h₂ h₃).symm

omit [StarOrderedRing B] in
/-- `selfAdjointTrace τ x = τ(x)` for `x ∈ 𝔪_τ⁺`. -/
theorem selfAdjointTrace_of_mem_finitePart (hτ : IsTrace τ) {x : B} (hx : x ∈ finitePart τ) :
    selfAdjointTrace τ x = (τ x).toReal := by
  simpa [hτ.map_zero] using hτ.selfAdjointTrace_sub hx hτ.zero_mem_finitePart

/-- Nonnegative real multiples: if `r (p - q) = p₀ - q₀` with `r ≥ 0` and
`p, q, p₀, q₀ ∈ 𝔪_τ⁺`, then `τ(p₀) - τ(q₀) = r (τ(p) - τ(q))`. -/
private theorem toReal_sub_eq_nnreal_mul_of_smul_sub_eq (hτ : IsTrace τ) (r : ℝ≥0)
    {p q p₀ q₀ : B} (hp : p ∈ finitePart τ) (hq : q ∈ finitePart τ) (hp₀ : p₀ ∈ finitePart τ)
    (hq₀ : q₀ ∈ finitePart τ) (h : (r : ℝ) • (p - q) = p₀ - q₀) :
    (τ p₀).toReal - (τ q₀).toReal = r * ((τ p).toReal - (τ q).toReal) := by
  rw [smul_sub] at h
  rw [← hτ.toReal_sub_eq_of_sub_eq (hτ.smul_mem_finitePart r hp)
    (hτ.smul_mem_finitePart r hq) hp₀ hq₀ h,
    hτ.map_nnreal_smul_of_nonneg r (mem_finitePart.1 hp).1,
    hτ.map_nnreal_smul_of_nonneg r (mem_finitePart.1 hq).1, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.coe_toReal]
  ring

/-- Real multiples: if `r (p - q) = p₀ - q₀` with `p, q, p₀, q₀ ∈ 𝔪_τ⁺`, then
`τ(p₀) - τ(q₀) = r (τ(p) - τ(q))`. -/
private theorem toReal_sub_eq_mul_of_smul_sub_eq (hτ : IsTrace τ) (r : ℝ) {p q p₀ q₀ : B}
    (hp : p ∈ finitePart τ) (hq : q ∈ finitePart τ) (hp₀ : p₀ ∈ finitePart τ)
    (hq₀ : q₀ ∈ finitePart τ) (h : r • (p - q) = p₀ - q₀) :
    (τ p₀).toReal - (τ q₀).toReal = r * ((τ p).toReal - (τ q).toReal) := by
  rcases le_total 0 r with hr | hr
  · lift r to ℝ≥0 using hr
    exact hτ.toReal_sub_eq_nnreal_mul_of_smul_sub_eq r hp hq hp₀ hq₀ h
  · -- `r (p - q) = (-r) (q - p)` with `-r ≥ 0`.
    lift -r to ℝ≥0 using neg_nonneg.2 hr with u hu
    have h' : (u : ℝ) • (q - p) = p₀ - q₀ := by rw [← h, hu, neg_smul, ← smul_neg, neg_sub]
    rw [hτ.toReal_sub_eq_nnreal_mul_of_smul_sub_eq u hq hp hp₀ hq₀ h', hu]
    ring

/-- `selfAdjointTrace τ` is real-linear on the self-adjoint elements of `𝔪_τ`. -/
theorem selfAdjointTrace_smul_add_smul (hτ : IsTrace τ) (s t : ℝ) {a b : B}
    (ha : a ∈ domain τ) (ha' : IsSelfAdjoint a) (hb : b ∈ domain τ) (hb' : IsSelfAdjoint b) :
    selfAdjointTrace τ (s • a + t • b) = s * selfAdjointTrace τ a + t * selfAdjointTrace τ b := by
  obtain ⟨p, hp, q, hq, rfl⟩ := hτ.exists_eq_sub_of_isSelfAdjoint ha ha'
  obtain ⟨p', hp', q', hq', rfl⟩ := hτ.exists_eq_sub_of_isSelfAdjoint hb hb'
  obtain ⟨p₁, hp₁, q₁, hq₁, h₁⟩ := hτ.exists_real_smul_sub s hp hq
  obtain ⟨p₂, hp₂, q₂, hq₂, h₂⟩ := hτ.exists_real_smul_sub t hp' hq'
  have e₁ := hτ.toReal_sub_eq_mul_of_smul_sub_eq s hp hq hp₁ hq₁ h₁
  have e₂ := hτ.toReal_sub_eq_mul_of_smul_sub_eq t hp' hq' hp₂ hq₂ h₂
  rw [h₁, h₂, show p₁ - q₁ + (p₂ - q₂) = (p₁ + p₂) - (q₁ + q₂) by abel,
    hτ.selfAdjointTrace_sub (hτ.add_mem_finitePart hp₁ hp₂) (hτ.add_mem_finitePart hq₁ hq₂),
    hτ.selfAdjointTrace_sub hp hq, hτ.selfAdjointTrace_sub hp' hq']
  rw [hτ.toReal_map_add hp₁ hp₂, hτ.toReal_map_add hq₁ hq₂]
  linarith

/-- The real part of an element of `𝔪_τ` lies in `𝔪_τ`. -/
theorem _root_.TauCeti.realPart_mem_domain {z : B} (hz : z ∈ domain τ) :
    (ℜ z : B) ∈ domain τ := by
  rw [realPart_apply_coe]
  exact Submodule.smul_of_tower_mem _ _ (Submodule.add_mem _ hz (star_mem_domain hz))

/-- The imaginary part of an element of `𝔪_τ` lies in `𝔪_τ`. -/
theorem _root_.TauCeti.imaginaryPart_mem_domain {z : B} (hz : z ∈ domain τ) :
    (ℑ z : B) ∈ domain τ := by
  rw [imaginaryPart_apply_coe]
  exact Submodule.smul_mem _ _
    (Submodule.smul_of_tower_mem _ _ (Submodule.sub_mem _ hz (star_mem_domain hz)))

/-- The **linear extension** of a trace to its domain `𝔪_τ`: `z ↦ τ(ℜ z) + i τ(ℑ z)`, where
the trace of a self-adjoint element `p - q` of `𝔪_τ` (`p, q ∈ 𝔪_τ⁺`) is `τ(p) - τ(q)`
(Dixmier 1963, Lemme 3, p. 226). -/
noncomputable def linearMap (hτ : IsTrace τ) : domain τ →ₗ[ℂ] ℂ where
  toFun z := selfAdjointTrace τ (ℜ (z : B)) + Complex.I * selfAdjointTrace τ (ℑ (z : B))
  map_add' z w := by
    have h := hτ.selfAdjointTrace_smul_add_smul 1 1 (realPart_mem_domain z.property)
      (ℜ (z : B)).property (realPart_mem_domain w.property) (ℜ (w : B)).property
    have h' := hτ.selfAdjointTrace_smul_add_smul 1 1 (imaginaryPart_mem_domain z.property)
      (ℑ (z : B)).property (imaginaryPart_mem_domain w.property) (ℑ (w : B)).property
    simp only [one_smul, one_mul] at h h'
    simp only [Submodule.coe_add, map_add, AddSubgroup.coe_add, h, h', Complex.ofReal_add]
    ring
  map_smul' c z := by
    have h := hτ.selfAdjointTrace_smul_add_smul c.re (-c.im) (realPart_mem_domain z.property)
      (ℜ (z : B)).property (imaginaryPart_mem_domain z.property) (ℑ (z : B)).property
    have h' := hτ.selfAdjointTrace_smul_add_smul c.re c.im (imaginaryPart_mem_domain z.property)
      (ℑ (z : B)).property (realPart_mem_domain z.property) (ℜ (z : B)).property
    simp only [SetLike.val_smul, realPart_smul, imaginaryPart_smul, sub_eq_add_neg, ← neg_smul,
      AddSubgroup.coe_add, selfAdjoint.val_smul, h, h', neg_mul, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_neg, RingHom.id_apply, smul_eq_mul]
    linear_combination (selfAdjointTrace τ (ℜ (z : B)) +
        Complex.I * selfAdjointTrace τ (ℑ (z : B))) * Complex.re_add_im c -
      (c.im * selfAdjointTrace τ (ℑ (z : B))) * Complex.I_sq

/-- The value of the linear extension. -/
theorem linearMap_apply (hτ : IsTrace τ) (z : domain τ) :
    hτ.linearMap z =
      selfAdjointTrace τ (ℜ (z : B)) + Complex.I * selfAdjointTrace τ (ℑ (z : B)) :=
  (rfl)

/-- The linear extension is real on self-adjoint elements of `𝔪_τ`. -/
theorem linearMap_apply_of_isSelfAdjoint (hτ : IsTrace τ) (z : domain τ)
    (hz : IsSelfAdjoint (z : B)) : hτ.linearMap z = selfAdjointTrace τ z := by
  have h0 := hτ.selfAdjointTrace_of_mem_finitePart hτ.zero_mem_finitePart
  rw [linearMap_apply, hz.coe_realPart, hz.imaginaryPart]
  simp [h0, hτ.map_zero]

/-- The linear extension agrees with `τ` on `𝔪_τ⁺`; in particular it is nonnegative there. -/
theorem linearMap_apply_of_mem_finitePart (hτ : IsTrace τ) {x : B} (hx : x ∈ finitePart τ) :
    hτ.linearMap ⟨x, finitePart_subset_domain hx⟩ = (τ x).toReal := by
  rw [hτ.linearMap_apply_of_isSelfAdjoint _ (mem_finitePart.1 hx).1.isSelfAdjoint,
    hτ.selfAdjointTrace_of_mem_finitePart hx]

/-- Uniqueness of the linear extension: a linear functional on `𝔪_τ` that agrees with `τ` on
`𝔪_τ⁺` is `hτ.linearMap`. -/
theorem eq_linearMap (hτ : IsTrace τ) {f : domain τ →ₗ[ℂ] ℂ}
    (hf : ∀ x (hx : x ∈ finitePart τ), f ⟨x, finitePart_subset_domain hx⟩ = (τ x).toReal) :
    f = hτ.linearMap :=
  LinearMap.ext_on Submodule.span_span_coe_preimage fun _ hz ↦
    (hf _ hz).trans (hτ.linearMap_apply_of_mem_finitePart hz).symm

/-- **The linear extension of a trace.** A trace extends uniquely to a complex-linear functional
on its domain `𝔪_τ`, a two-sided ideal with `𝔪_τ ∩ B₊ = 𝔪_τ⁺` (`TauCeti.IsTrace.domainIdeal`,
`TauCeti.IsTrace.mem_domain_iff_of_nonneg`) (Dixmier 1963, Lemme 3, p. 226). -/
theorem existsUnique_linearMap (hτ : IsTrace τ) :
    ∃! φ : domain τ →ₗ[ℂ] ℂ, ∀ x (hx : x ∈ finitePart τ),
      φ ⟨x, finitePart_subset_domain hx⟩ = (τ x).toReal :=
  ⟨hτ.linearMap, fun _ hx ↦ hτ.linearMap_apply_of_mem_finitePart hx, fun _ hψ ↦ hτ.eq_linearMap hψ⟩

/-- The trace identity for the linear extension: `τ(w⋆w) = τ(ww⋆)` for `w ∈ 𝔫_τ`. -/
theorem linearMap_star_mul_self (hτ : IsTrace τ) {w : B} (hw : w ∈ sqIntegrable τ) :
    hτ.linearMap ⟨star w * w, star_mul_self_mem_domain hw⟩ =
      hτ.linearMap ⟨w * star w, hτ.mul_star_self_mem_domain hw⟩ := by
  rw [hτ.linearMap_apply_of_mem_finitePart (star_mul_self_mem_finitePart_iff.2 hw),
    hτ.linearMap_apply_of_mem_finitePart (hτ.mul_star_self_mem_finitePart_iff.2 hw),
    hτ.map_star_mul_self]

/-- `τ(y⋆x) = τ(xy⋆)` for `x, y ∈ 𝔫_τ`, by polarization of the trace identity. -/
theorem linearMap_star_mul_comm (hτ : IsTrace τ) {x y : B} (hx : x ∈ sqIntegrable τ)
    (hy : y ∈ sqIntegrable τ) :
    hτ.linearMap ⟨star y * x, hτ.star_mul_mem_domain hx hy⟩ =
      hτ.linearMap ⟨x * star y, hτ.mul_star_mem_domain hx hy⟩ := by
  have hadd (c : ℂ) : x + c • y ∈ sqIntegrable τ :=
    hτ.add_mem_sqIntegrable hx (hτ.smul_mem_sqIntegrable c hy)
  have hsub (c : ℂ) : x - c • y ∈ sqIntegrable τ := by
    simpa [sub_eq_add_neg] using hadd (-c)
  have h₁ : x + y ∈ sqIntegrable τ := by simpa using hadd 1
  have h₂ : x - y ∈ sqIntegrable τ := by simpa using hsub 1
  -- The elements `w⋆w` and `ww⋆` of `𝔪_τ`, for `w ∈ 𝔫_τ`.
  let m (w : B) (hw : w ∈ sqIntegrable τ) : domain τ := ⟨star w * w, star_mul_self_mem_domain hw⟩
  let m' (w : B) (hw : w ∈ sqIntegrable τ) : domain τ :=
    ⟨w * star w, hτ.mul_star_self_mem_domain hw⟩
  have hs (w : B) (hw : w ∈ sqIntegrable τ) : hτ.linearMap (m w hw) = hτ.linearMap (m' w hw) :=
    hτ.linearMap_star_mul_self hw
  -- The polarization identities for `y⋆x` and `xy⋆`, as identities in `𝔪_τ`.
  have p₁ : (4 : ℂ) • (⟨star y * x, hτ.star_mul_mem_domain hx hy⟩ : domain τ) =
      m _ h₁ + Complex.I • m _ (hadd Complex.I) - m _ h₂ - Complex.I • m _ (hsub Complex.I) :=
    Subtype.ext (by simpa [m] using star_mul_polarization y x)
  have p₂ : (4 : ℂ) • (⟨x * star y, hτ.mul_star_mem_domain hx hy⟩ : domain τ) =
      m' _ h₁ + Complex.I • m' _ (hadd Complex.I) - m' _ h₂ - Complex.I • m' _ (hsub Complex.I) :=
    Subtype.ext (by simpa [m'] using mul_star_polarization y x)
  have e₁ := congrArg hτ.linearMap p₁
  have e₂ := congrArg hτ.linearMap p₂
  simp only [map_add, map_sub, map_smul, smul_eq_mul] at e₁ e₂
  rw [hs _ h₁, hs _ (hadd Complex.I), hs _ h₂, hs _ (hsub Complex.I), ← e₂] at e₁
  exact mul_left_cancel₀ four_ne_zero e₁

/-- **Traciality of the linear extension**: `τ(xz) = τ(zx)` for `x ∈ 𝔪_τ` and `z ∈ B`
(Dixmier 1963, Lemme 3, p. 226). -/
theorem linearMap_mul_comm (hτ : IsTrace τ) {x : B} (hx : x ∈ domain τ) (z : B) :
    hτ.linearMap ⟨x * z, hτ.mul_mem_domain_right z hx⟩ =
      hτ.linearMap ⟨z * x, hτ.mul_mem_domain_left z hx⟩ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    -- `x = b⋆b` with `b ∈ 𝔫_τ`, and both `τ(b⋆bz)` and `τ(zb⋆b)` equal `τ(bzb⋆)`.
    obtain ⟨b, hb, rfl⟩ := exists_eq_star_mul_self_of_mem_finitePart hx
    have h₁ := hτ.linearMap_star_mul_comm (hτ.mul_mem_sqIntegrable_right z hb) hb
    have h₂ := hτ.linearMap_star_mul_comm hb (hτ.mul_mem_sqIntegrable_right (star z) hb)
    simp only [star_mul, star_star, mul_assoc] at h₁ h₂ ⊢
    exact h₁.trans h₂.symm
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [← map_add, AddMemClass.mk_add_mk, add_mul, mul_add] using congr($ihx + $ihy)
  | smul c x hx ih =>
    simpa only [← map_smul, SetLike.mk_smul_mk, smul_mul_assoc, mul_smul_comm] using
      congr(c • $ih)

end IsTrace

/-! ### Densely defined traces -/

/-- **The domain of a densely defined trace is dense.** -/
theorem IsDenselyDefined.dense_domain (hd : IsDenselyDefined τ) : Dense (domain τ : Set B) := by
  -- The closure of `𝔪_τ` is a subspace containing `B₊`, which spans `B`.
  have h : {x : B | 0 ≤ x} ⊆ (domain τ).topologicalClosure :=
    (isDenselyDefined_iff.1 hd).trans (closure_mono finitePart_subset_domain)
  have htop : (domain τ).topologicalClosure = ⊤ :=
    eq_top_iff.2 (CStarAlgebra.span_nonneg (A := B) ▸ Submodule.span_le.2 h)
  rw [← Submodule.dense_iff_topologicalClosure_eq_top] at htop
  exact htop

/-- **The square-integrable elements of a densely defined trace are dense.** -/
theorem IsTrace.dense_sqIntegrable_of_isDenselyDefined (hτ : IsTrace τ)
    (hd : IsDenselyDefined τ) : Dense (sqIntegrable τ) :=
  hd.dense_domain.mono hτ.domain_subset_sqIntegrable

/-! ### Bounded traces -/

/-- A trace that is finite on `B₊` is defined everywhere: `𝔪_τ = B`. -/
theorem domain_eq_top_of_lt_top (hfin : ∀ x : B, 0 ≤ x → τ x < ∞) : domain τ = ⊤ := by
  rw [eq_top_iff, ← CStarAlgebra.span_nonneg]
  exact Submodule.span_mono fun x hx ↦ mem_finitePart.2 ⟨hx, hfin x hx⟩

/-- Every element lies in the domain of a trace that is finite on `B₊`. -/
theorem mem_domain_of_lt_top (hfin : ∀ x : B, 0 ≤ x → τ x < ∞) (x : B) : x ∈ domain τ := by
  rw [domain_eq_top_of_lt_top hfin]
  exact Submodule.mem_top

namespace PositiveTracialFunctional

/-- The trace of a positive tracial functional is defined everywhere. -/
@[simp]
theorem domain_toTrace (ω : PositiveTracialFunctional B) : domain ω.toTrace = ⊤ :=
  domain_eq_top_of_lt_top fun x _ ↦ ω.toTrace_lt_top x

/-- The linear extension of the trace of a positive tracial functional `ω` is `ω`. -/
@[simp]
theorem linearMap_toTrace (ω : PositiveTracialFunctional B) (z : domain ω.toTrace) :
    ω.isTrace_toTrace.linearMap z = ω z := by
  let ψ : domain ω.toTrace →ₗ[ℂ] ℂ := (ω : B →ₗ[ℂ] ℂ).comp (domain ω.toTrace).subtype
  have hψ : ∀ x (hx : x ∈ finitePart ω.toTrace),
      ψ ⟨x, finitePart_subset_domain hx⟩ = (ω.toTrace x).toReal := by
    intro x hx
    exact ω.apply_eq_toReal_toTrace (mem_finitePart.1 hx).1
  simp [← ω.isTrace_toTrace.eq_linearMap hψ, ψ]

end PositiveTracialFunctional

end TauCeti
