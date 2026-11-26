/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.L1Space.HasFiniteIntegral
public import TauCeti.MeasureTheory.Group.OrbitCutoff.Discrete
public import TauCeti.MeasureTheory.Measure.Haar.Unique

/-!
# Integration in Iwasawa coordinates

Let `G` be a unimodular second countable locally compact group, `N ⊂ G` a closed subgroup, `K ⊂ G`
a compact subgroup and `i : M → G` a continuous homomorphism from a unimodular group `M`, with
`G = N · i(M) · K`, and suppose that conjugation by `i(m)` multiplies the Haar measure of `N` by
`w(m) > 0`. Then the measure `dn dm dk` in the coordinates `i(m) n k` is a multiple of the Haar
measure of `G` (`MeasureTheory.exists_lintegral_iwasawa_eq_mul`); the constant is not computed, and
may be infinite.

Combined with a discrete subgroup `Γ` with `Γ ∩ N` cocompact in `N` and `Γ = (Γ ∩ N) · i(Δ)`, the
integral over `Γ \ G` of a function `F` left invariant under `N` and `Γ` is
`c ∫_{Δ\M} ∫_K w(m) F(i(m) k) dk dm` for a constant `c ≠ 0`
(`MeasureTheory.exists_integral_cutoffMeasure_iwasawa`). Here `Δ \ M` is described by a measure `α`
on `M` whose unfolding along `Δ` is the Haar measure of `M`.

## Main results

* `MeasureTheory.exists_lintegral_iwasawa_eq_mul`: the Iwasawa integration formula, up to a
  constant.
* `MeasureTheory.exists_integral_cutoffMeasure_iwasawa`: integration over `Γ \ G` in Iwasawa
  coordinates.

The general facts these proofs use are stated in reusable form: measurable choice of rescaling
factors (`MeasureTheory.exists_measurable_mul_eq_of_scale`), division of an integral formula by a
factor `c ∈ (0, ∞]` of the measure (`MeasureTheory.exists_integral_eq_mul_of_smul_measure`), the
splitting `D × (Γ ∩ N) ≃ Γ` of a subgroup along a complement
(`Subgroup.exists_equiv_prod_subgroupOf`), and the averaged change of variables `x = b(p) y k⁻¹`
for a two-sided invariant measure (`MeasureTheory.lintegral_mul_lintegral_translate`).

## References

* A. W. Knapp, *Lie groups beyond an introduction*, second edition, Birkhäuser, 2002, Proposition
  8.43, for the Iwasawa integration formula of a reductive group.

The statements and proofs are adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache
2.0, Copyright 2026 Anthropic PBC), `src/Lib/Adelic/QuotientMeasure/IwasawaUnfolding.lean`
(`New.exists_measurable_mul_eq_of_scale`, `New.ofReal_mul_lintegral_iwasawa_translate`,
`New.lintegral_iwasawa_inv_mul_translate`, `New.lintegral_iwasawa`,
`New.exists_equiv_prod_subgroupOf`, `New.ofReal_mul_lintegral_quotMeasure_tsum`,
`New.exists_integral_eq_mul_of_smul_measure`, `New.integral_quotMeasure_iwasawa`).
-/

public section

open MeasureTheory Measure Set Function ProbabilityTheory

open scoped ENNReal Pointwise

namespace MeasureTheory

/-- **Measurable rescaling of a family of functions.** Let `J` send measurable functions
`X → ℝ≥0∞` to measurable functions, and suppose that at each point `y` every `J f y` differs from
`J f x₀` by the same finite nonzero factor `r y` (independent of `f`). Then for every measurable
`β` there is a measurable `g` with `g y * J f y = β y * J f x₀` for all `y` and measurable `f`:
the factors `y ↦ r y` can be chosen measurably. -/
theorem exists_measurable_mul_eq_of_scale {X : Type*} [MeasurableSpace X]
    {J : (X → ℝ≥0∞) → X → ℝ≥0∞} {x₀ : X} (hJ : ∀ f, Measurable f → Measurable (J f))
    (h_scale : ∀ y, ∃ r : ℝ≥0∞, r ≠ 0 ∧ r ≠ ∞ ∧ ∀ f, Measurable f → r * J f y = J f x₀)
    {β : X → ℝ≥0∞} (hβ : Measurable β) :
    ∃ g : X → ℝ≥0∞, Measurable g ∧ ∀ y f, Measurable f → g y * J f y = β y * J f x₀ := by
  by_cases! h_const : ∀ y f, Measurable f → J f y = J f x₀
  · exact ⟨β, hβ, fun y f hf ↦ by rw [h_const y f hf]⟩
  -- Otherwise some `J f` is finite and nonzero everywhere; the factor at `y` is `J f x₀ / J f y`.
  obtain ⟨y₀, f, hf, h_ne⟩ := h_const
  obtain ⟨r, hr_zero, hr_top, hr⟩ := h_scale y₀
  have h_zero : J f x₀ ≠ 0 := fun h ↦ h_ne (by simpa [h, hr_zero] using hr f hf)
  have h_top : J f x₀ ≠ ∞ := fun h ↦
    h_ne (by simpa [h, hr_zero, hr_top, ENNReal.mul_eq_top] using hr f hf)
  refine ⟨fun x ↦ β x * (J f x₀ / J f x), hβ.mul (measurable_const.div (hJ f hf)),
    fun x φ hφ ↦ ?_⟩
  obtain ⟨s, hs_zero, -, hs⟩ := h_scale x
  have hx_zero : J f x ≠ 0 := fun h ↦ h_zero (by rw [← hs f hf, h, mul_zero])
  have hx_top : J f x ≠ ∞ := fun h ↦ h_top (by rw [← hs f hf, h, ENNReal.mul_top hs_zero])
  have h_div : J f x₀ / J f x = s := by
    rw [← hs f hf, ENNReal.mul_div_cancel_right hx_zero hx_top]
  simp only [h_div, mul_assoc, hs φ hφ]

/-- **Dividing an integral formula by a factor of the measure.** For `c ∈ (0, ∞]` and finite
nonzero `V` there is a real `a ≠ 0` such that whenever `F` is integrable for `c • q` with
`∫ F ∂(c • q) = V • I`, then `F` is integrable for `q` with `∫ F ∂q = a • I`. For `c = ∞` this
uses that a function integrable for `∞ • q` vanishes `q`-almost everywhere. -/
theorem exists_integral_eq_mul_of_smul_measure {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (q : Measure X) {c V : ℝ≥0∞} (hc : c ≠ 0)
    (hV_zero : V ≠ 0) (hV_top : V ≠ ∞) :
    ∃ a ≠ (0 : ℝ), ∀ (F : X → E) (I : E), Integrable F (c • q) →
      ∫ x, F x ∂(c • q) = V.toReal • I → Integrable F q ∧ ∫ x, F x ∂q = a • I := by
  have hV : V.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hV_zero, hV_top⟩
  rcases eq_or_ne c ∞ with rfl | hc_top
  · -- for `c = ∞` integrability forces `F = 0` almost everywhere
    refine ⟨1, one_ne_zero, fun F I h_int h_eq ↦ ?_⟩
    have hF_zero : F =ᵐ[q] 0 := TauCeti.MeasureTheory.ae_eq_zero_of_hasFiniteIntegral_top_smul
      (h_int.aestronglyMeasurable.mono_ac (absolutelyContinuous_smul ENNReal.top_ne_zero))
      h_int.hasFiniteIntegral
    obtain rfl : I = 0 := by
      rw [integral_smul_measure, ENNReal.toReal_top, zero_smul, eq_comm, smul_eq_zero] at h_eq
      exact h_eq.resolve_left hV
    exact ⟨(integrable_zero X E q).congr hF_zero.symm, by simp [integral_eq_zero_of_ae hF_zero]⟩
  · have hc_real : c.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hc, hc_top⟩
    refine ⟨V.toReal / c.toReal, div_ne_zero hV hc_real,
      fun F I h_int h_eq ↦ ⟨(integrable_smul_measure hc hc_top).1 h_int, ?_⟩⟩
    rw [integral_smul_measure] at h_eq
    rw [div_eq_inv_mul, mul_smul, ← h_eq, smul_smul, inv_mul_cancel₀ hc_real, one_smul]

/-- **Splitting a subgroup along a complement.** Let `i : M →* G` meet the subgroup `N` only in
`i(1)`, and let `δ : D → M` be injective. If the subgroup `Γ` contains every `i(δ d)` and every
`g ∈ Γ` has some `g i(δ d) ∈ N`, then `(d, γ) ↦ i(δ d) γ` is a bijection
`D × (Γ ∩ N) ≃ Γ`. -/
theorem _root_.Subgroup.exists_equiv_prod_subgroupOf {G M D : Type*} [Group G] [Group M]
    {N Γ : Subgroup G} {i : M →* G}
    (h_triv : ∀ a : M, i a ∈ N → a = 1) {δ : D → M} (hδ : δ.Injective)
    (hδ_mem : ∀ d, i (δ d) ∈ Γ) (hΓ : ∀ g ∈ Γ, ∃ d, g * i (δ d) ∈ N) :
    ∃ e : D × Γ.subgroupOf N ≃ Γ, ∀ d (γ : Γ.subgroupOf N), (e (d, γ) : G) = i (δ d) * (γ : N) := by
  let φ (p : D × Γ.subgroupOf N) : Γ :=
    ⟨i (δ p.1) * (p.2 : N), mul_mem (hδ_mem p.1) (Subgroup.mem_subgroupOf.1 p.2.property)⟩
  refine ⟨.ofBijective φ ⟨?_, fun g ↦ ?_⟩, fun d γ ↦ rfl⟩
  · rintro ⟨d, γ⟩ ⟨d', γ'⟩ h
    have h_eq : i (δ d) * (γ : N) = i (δ d') * (γ' : N) := congrArg Subtype.val h
    have h_mem : i ((δ d)⁻¹ * δ d') ∈ N := by
      simpa [QuotientGroup.eq] using congrArg (QuotientGroup.mk : G → G ⧸ N) h_eq
    obtain rfl : d = d' := hδ (inv_mul_eq_one.1 (h_triv _ h_mem))
    simpa using h_eq
  · obtain ⟨d, h_mem⟩ : ∃ d, (g : G)⁻¹ * i (δ d) ∈ N := hΓ _ (inv_mem g.property)
    let γ : Γ.subgroupOf N :=
      ⟨⟨(g : G)⁻¹ * i (δ d), h_mem⟩, mul_mem (inv_mem g.property) (hδ_mem d)⟩
    exact ⟨(d, γ⁻¹), by simp [φ, γ]⟩

variable {G M : Type*} [Group G] [Group M] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [TopologicalSpace M] [IsTopologicalGroup M]
  [MeasurableSpace M] [BorelSpace M] {w : M → ℝ}
  {ν : Measure M} [ν.IsMulRightInvariant] {N K : Subgroup G} [CompactSpace K]
  {κ : Measure K} [κ.IsHaarMeasure] {lam : Measure N} {i : M →* G}

omit [CompactSpace K] [κ.IsHaarMeasure] in
/-- Moving `n i(m) k` through the Iwasawa coordinates multiplies the integral by `w(m)`. -/
private theorem ofReal_mul_lintegral_iwasawa_translate [lam.IsMulRightInvariant]
    [κ.IsMulRightInvariant]
    (h_conj : ∀ m (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ n : N, f (i m * n * (i m)⁻¹) ∂lam = .ofReal (w m) * ∫⁻ n : N, f n ∂lam)
    {f : G → ℝ≥0∞} (hf : Measurable f) (n : N) (m : M) (k : K) :
    .ofReal (w m) * ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, f (i a * u * (n * i m * k) * l⁻¹) ∂lam ∂ν ∂κ =
      ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, f (i a * u * l⁻¹) ∂lam ∂ν ∂κ := by
  -- Absorb `n` into `u`, move `i(m)` past `u`, then absorb `m` into `a` and `k` into `l`.
  have h_move (x z : G) : .ofReal (w m) * ∫⁻ u : N, f (x * u * (n * i m * k) * z) ∂lam =
      ∫⁻ u : N, f (x * i m * u * (k * z)) ∂lam :=
    calc .ofReal (w m) * ∫⁻ u : N, f (x * u * (n * i m * k) * z) ∂lam
      _ = .ofReal (w m) * ∫⁻ u : N, f (x * u * i m * (k * z)) ∂lam := by
        rw [← lintegral_mul_right_eq_self (fun u : N ↦ f (x * u * i m * (k * z))) n]
        simp [mul_assoc]
      _ = ∫⁻ u : N, f (x * (i m * u * (i m)⁻¹) * i m * (k * z)) ∂lam :=
        (h_conj m (fun y ↦ f (x * y * i m * (k * z))) (by fun_prop)).symm
      _ = ∫⁻ u : N, f (x * i m * u * (k * z)) ∂lam := by simp [mul_assoc]
  calc
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, f (i (a * m) * u * (k * l⁻¹)) ∂lam ∂ν ∂κ := by
      simp only [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, map_mul, ← h_move]
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, f (i a * u * (k * l⁻¹)) ∂lam ∂ν ∂κ :=
      lintegral_congr fun l ↦
        lintegral_mul_right_eq_self (fun a : M ↦ ∫⁻ u : N, f (i a * u * (k * l⁻¹)) ∂lam) m
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, f (i a * u * l⁻¹) ∂lam ∂ν ∂κ := by
      rw [← lintegral_mul_right_eq_self _ k]
      simp

omit [ν.IsMulRightInvariant] [CompactSpace K] [κ.IsHaarMeasure] in
/-- Translating the argument by `n i(m) k` does not change the integral of `g ((i(a) u)⁻¹ x l)` in
the Iwasawa coordinates. -/
private theorem lintegral_iwasawa_inv_mul_translate [ν.IsMulLeftInvariant]
    [κ.IsMulLeftInvariant] [lam.IsMulLeftInvariant]
    (h_conj : ∀ m (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ n : N, f (i m * n * (i m)⁻¹) ∂lam = .ofReal (w m) * ∫⁻ n : N, f n ∂lam)
    {g : G → ℝ≥0∞} (hg : Measurable g) (n : N) (m : M) (k : K) :
    ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * (n * i m * k * l)) ∂lam ∂ν ∂κ =
      ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * l) ∂lam ∂ν ∂κ := by
  -- Move `(i a)⁻¹` past `u⁻¹` to absorb `n` into `u`; then absorb `m` into `a` and `k` into `l`.
  have h_absorb (a : M) (z : G) :
      ∫⁻ u : N, g ((i a * u)⁻¹ * (n * z)) ∂lam = ∫⁻ u : N, g ((i a * u)⁻¹ * z) ∂lam := by
    have h_move (y : G) : ∫⁻ u : N, g ((i a * u)⁻¹ * y) ∂lam =
        .ofReal (w a) * ∫⁻ u : N, g ((i a)⁻¹ * ((u : G)⁻¹ * y)) ∂lam := by
      simpa [mul_assoc] using h_conj a (fun x ↦ g ((i a)⁻¹ * (x⁻¹ * y))) (by fun_prop)
    rw [h_move, h_move, ← lintegral_mul_left_eq_self _ n]
    simp [mul_assoc]
  calc
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * (i m * (k * l))) ∂lam ∂ν ∂κ := by
      simp only [mul_assoc, h_absorb]
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * (k * l)) ∂lam ∂ν ∂κ := by
      refine lintegral_congr fun l ↦ ?_
      rw [← lintegral_mul_left_eq_self _ m]
      simp [mul_assoc]
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * l) ∂lam ∂ν ∂κ :=
      lintegral_mul_left_eq_self (fun l : K ↦ ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * l) ∂lam ∂ν) k

variable [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [LocallyCompactSpace M]
  [SecondCountableTopology M] [ν.IsHaarMeasure] [lam.IsHaarMeasure]

omit [LocallyCompactSpace G] [T2Space G] [CompactSpace K] in
/-- **Change of variables `x = b(p) y k⁻¹`, averaged over a measure on the translations.** For a
left and right invariant s-finite measure `μ` on `G`, a measurable `b : P → G`, a subgroup `K` and
an s-finite measure `π` on `P × K`,
`∫ g(y) ∫ f(b(p) y k⁻¹) dπ(p, k) dμ(y) = ∫ (∫ g(b(p)⁻¹ x k) dπ(p, k)) f(x) dμ(x)`. -/
theorem lintegral_mul_lintegral_translate {P : Type*} [MeasurableSpace P] (μ : Measure G)
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [SFinite μ] {π : Measure (P × K)} [SFinite π]
    {b : P → G} (hb : Measurable b) {g f : G → ℝ≥0∞} (hg : Measurable g) (hf : Measurable f) :
    ∫⁻ y, g y * ∫⁻ h, f (b h.1 * y * h.2⁻¹) ∂π ∂μ =
      ∫⁻ x, (∫⁻ h, g ((b h.1)⁻¹ * (x * h.2)) ∂π) * f x ∂μ := by
  calc ∫⁻ y, g y * ∫⁻ h, f (b h.1 * y * h.2⁻¹) ∂π ∂μ
    _ = ∫⁻ h, ∫⁻ y, g y * f (b h.1 * y * h.2⁻¹) ∂μ ∂π := by
      simp (disch := fun_prop) only [← lintegral_const_mul]
      exact lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ h, ∫⁻ x, g ((b h.1)⁻¹ * (x * h.2)) * f x ∂μ ∂π := by
      congr with ⟨p, k⟩
      rw [← lintegral_mul_left_eq_self _ (b p)⁻¹, ← lintegral_mul_right_eq_self _ (k : G)]
      simp [mul_assoc]
    _ = ∫⁻ x, ∫⁻ h, g ((b h.1)⁻¹ * (x * h.2)) * f x ∂π ∂μ :=
      lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ x, (∫⁻ h, g ((b h.1)⁻¹ * (x * h.2)) ∂π) * f x ∂μ :=
      lintegral_congr fun x ↦ lintegral_mul_const _ (by fun_prop)

/-- **The Iwasawa integration formula**, up to a constant. Let `G` and `M` be unimodular, `N ⊂ G`
closed and unimodular, `K ⊂ G` compact, `i : M → G` a continuous homomorphism with `G = N i(M) K`,
and let conjugation by `i(m)` multiply integrals over `N` by `w(m) > 0`. Then there is
`d ∈ [0, ∞]` with `∫_K ∫_M ∫_N f(i(m) n k) dn dm dk = d ∫_G f dμ` for every measurable `f ≥ 0`. -/
theorem exists_lintegral_iwasawa_eq_mul (μ : Measure G) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] [lam.IsMulRightInvariant] (hN : IsClosed (N : Set G))
    (hw_pos : ∀ m, 0 < w m) (hi : Continuous i)
    (h_dec : ∀ g : G, ∃ (n : N) (m : M) (k : K), g = n * i m * k)
    (h_conj : ∀ m (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ n : N, f (i m * n * (i m)⁻¹) ∂lam = .ofReal (w m) * ∫⁻ n : N, f n ∂lam) :
    ∃ d : ℝ≥0∞, ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ k : K, ∫⁻ m : M, ∫⁻ n : N, f (i m * n * k) ∂lam ∂ν ∂κ = d * ∫⁻ g, f g ∂μ := by
  -- Let `J f y` be the integral of `f (i(m) n y k⁻¹)`; the left side is `J f 1`. Moving `y` only
  -- divides `J f y` by `w`, so `J f 1 = ∫ g(y) J f y dμ(y)` for a suitable weight `g`. After
  -- Fubini and a translation of `y`, this is `∫ d(x) f(x) dμ(x)`, and `d` is constant.
  have : LocallyCompactSpace N := hN.locallyCompactSpace
  have : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set G)
  have : κ.IsMulRightInvariant := isMulRightInvariant_of_isHaarMeasure_of_isFiniteMeasure κ
  have : κ.IsInvInvariant := isInvInvariant_of_isHaarMeasure_of_isFiniteMeasure κ
  obtain ⟨β, hβ⟩ := (inferInstance : HasOrbitCutoff μ G).exists_isOrbitCutoff
  have hβ_one : ∫⁻ x, β x ∂μ = 1 := by simpa using hβ.lintegral_smul 1
  let π : Measure ((M × N) × K) := (ν.prod lam).prod κ
  let b (p : M × N) : G := i p.1 * p.2
  have hπ (φ : G → K → ℝ≥0∞) (hφ : Measurable (uncurry φ)) :
      ∫⁻ h, φ (b h.1) h.2 ∂π = ∫⁻ k : K, ∫⁻ m : M, ∫⁻ n : N, φ (i m * n) k ∂lam ∂ν ∂κ := by
    rw [lintegral_prod_symm _ (by fun_prop)]
    exact lintegral_congr fun k ↦ lintegral_prod _ (by fun_prop)
  let J (f : G → ℝ≥0∞) (y : G) : ℝ≥0∞ := ∫⁻ h, f (b h.1 * y * h.2⁻¹) ∂π
  have hJ (f : G → ℝ≥0∞) (hf : Measurable f) (y : G) :
      J f y = ∫⁻ k : K, ∫⁻ m : M, ∫⁻ n : N, f (i m * n * y * k⁻¹) ∂lam ∂ν ∂κ :=
    hπ (fun x k ↦ f (x * y * k⁻¹)) (by fun_prop)
  have h_scale (y : G) : ∃ r : ℝ≥0∞, r ≠ 0 ∧ r ≠ ∞ ∧
      ∀ f : G → ℝ≥0∞, Measurable f → r * J f y = J f 1 := by
    obtain ⟨n, m, k, rfl⟩ := h_dec y
    refine ⟨.ofReal (w m), (ENNReal.ofReal_pos.2 (hw_pos m)).ne', ENNReal.ofReal_ne_top,
      fun f hf ↦ ?_⟩
    simpa only [hJ f hf, mul_one] using
      ofReal_mul_lintegral_iwasawa_translate (ν := ν) (κ := κ) h_conj hf n m k
  have hJ_meas (f : G → ℝ≥0∞) (hf : Measurable f) : Measurable (J f) :=
    Measurable.lintegral_prod_right (f := fun (y : G) (h : (M × N) × K) ↦ f (b h.1 * y * h.2⁻¹))
      (by fun_prop)
  obtain ⟨g, hg, hgJ⟩ := exists_measurable_mul_eq_of_scale hJ_meas h_scale hβ.measurable
  let d (x : G) : ℝ≥0∞ := ∫⁻ h, g ((b h.1)⁻¹ * (x * h.2)) ∂π
  have hd (x : G) : d x = d 1 := by
    obtain ⟨n, m, k, rfl⟩ := h_dec x
    have hd_eq (z : G) := hπ (fun y l ↦ g (y⁻¹ * (z * l))) (by fun_prop)
    simpa only [d, hd_eq, one_mul] using
      lintegral_iwasawa_inv_mul_translate (ν := ν) (κ := κ) h_conj hg n m k
  refine ⟨d 1, fun f hf ↦ ?_⟩
  calc ∫⁻ k : K, ∫⁻ m : M, ∫⁻ n : N, f (i m * n * k) ∂lam ∂ν ∂κ
    _ = J f 1 := by
      rw [hJ f hf, ← lintegral_inv_eq_self]
      simp
    _ = ∫⁻ y, g y * J f y ∂μ := by simp [hgJ _ f hf, lintegral_mul_const _ hβ.measurable, hβ_one]
    _ = ∫⁻ x, d x * f x ∂μ :=
      lintegral_mul_lintegral_translate μ (b := b) (by fun_prop) hg hf
    _ = d 1 * ∫⁻ x, f x ∂μ := by simp_rw [hd, lintegral_const_mul _ hf]

omit [TopologicalSpace M] [IsTopologicalGroup M] [MeasurableSpace M] [BorelSpace M]
  [LocallyCompactSpace M] [SecondCountableTopology M] [ν.IsHaarMeasure] in
/-- `w(m)` times the integral over `(Γ ∩ N) \ N` of a sum over `Γ` unfolds to a sum over `d` of
integrals over `N`. -/
private theorem ofReal_mul_lintegral_cutoffMeasure_tsum {Γ : Subgroup G} [DiscreteTopology Γ]
    (hN : IsClosed (N : Set G)) [lam.IsMulRightInvariant]
    (h_conj : ∀ m (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ n : N, f (i m * n * (i m)⁻¹) ∂lam = .ofReal (w m) * ∫⁻ n : N, f n ∂lam)
    (h_triv : ∀ a : M, i a ∈ N → a = 1) {D : Type*} [Countable D] {δ : D → M} (hδ : δ.Injective)
    (hδ_mem : ∀ d, i (δ d) ∈ Γ) (hΓ : ∀ g ∈ Γ, ∃ d, g * i (δ d) ∈ N) {f : G → ℝ≥0∞}
    (hf : Measurable f) (m : M) (k : G) :
    .ofReal (w m) *
        ∫⁻ n : N, ∑' γ : Γ, f (γ * (n * (i m * k))) ∂(Γ.subgroupOf N).cutoffMeasure lam =
      ∑' d, ∫⁻ n : N, f (i (δ d * m) * n * k) ∂lam := by
  -- Write `Γ = {i(δ d) γ}` with `γ ∈ Γ ∩ N`, unfold over `Γ ∩ N`, and move `i(m)` past `n`.
  have : LocallyCompactSpace N := hN.locallyCompactSpace
  have : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set G)
  have : lam.IsInvInvariant := isInvInvariant_of_isMulRightInvariant lam
  obtain ⟨e, he⟩ := Subgroup.exists_equiv_prod_subgroupOf h_triv hδ hδ_mem hΓ
  simp only [← e.tsum_eq, tsum_prod', he]
  have : Countable (Γ.subgroupOf N) := countable_of_Lindelof_of_discrete
  rw [lintegral_tsum fun d ↦ (Measurable.tsum fun γ ↦ by fun_prop).aemeasurable,
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun d ↦ ?_
  calc ENNReal.ofReal (w m) * ∫⁻ n : N, ∑' γ : Γ.subgroupOf N,
        f (i (δ d) * (γ : N) * (n * (i m * k))) ∂(Γ.subgroupOf N).cutoffMeasure lam
    _ = ENNReal.ofReal (w m) * ∫⁻ n : N, f (i (δ d) * n * i m * k) ∂lam := by
      rw [← lintegral_cutoffMeasure_lintegral (ν := (count : Measure (Γ.subgroupOf N)))
        (f := fun n : N ↦ f (i (δ d) * n * i m * k)) (by fun_prop)]
      simp [lintegral_count, Subgroup.smul_def, mul_assoc]
    _ = ∫⁻ n : N, f (i (δ d) * (i m * n * (i m)⁻¹) * i m * k) ∂lam :=
      (h_conj m (fun y ↦ f (i (δ d) * y * i m * k)) (by fun_prop)).symm
    _ = ∫⁻ n : N, f (i (δ d * m) * n * k) ∂lam := by simp [mul_assoc]

/-- **Unfolding in Iwasawa coordinates.** In the setting of
`MeasureTheory.exists_lintegral_iwasawa_eq_mul`, let moreover `i(a) ∈ N` only for `a = 1`, and let
`Γ ⊂ G` be discrete with `Γ ∩ N` cocompact in `N` and `Γ = (Γ ∩ N) · i(δ(D))` for an injective
`δ : D → M` from a countable set. Let `α` be a measure on `M` that unfolds to `ν` along `δ`,
standing for the quotient `δ(D) \ M`. Let `w` be measurable. There is `c ≠ 0` such that for every
measurable `F` from `G` to a real normed space, left invariant under `N` and under `Γ`, with
`(m, k) ↦ w(m) F(i(m) k)` integrable for `α × κ`, `F` is integrable over `Γ \ G` and
`∫_{Γ\G} F = c ∫∫ w(m) F(i(m) k) dα(m) dκ(k)`. -/
theorem exists_integral_cutoffMeasure_iwasawa {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure G) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] {Γ : Subgroup G} [DiscreteTopology Γ] (hN : IsClosed (N : Set G))
    (hw : Measurable w) (hw_pos : ∀ m, 0 < w m) (hi : Continuous i)
    (h_dec : ∀ g : G, ∃ (n : N) (m : M) (k : K), g = n * i m * k)
    (h_conj : ∀ m (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ n : N, f (i m * n * (i m)⁻¹) ∂lam = .ofReal (w m) * ∫⁻ n : N, f n ∂lam)
    (h_triv : ∀ a : M, i a ∈ N → a = 1) {D : Type*} [Countable D] {δ : D → M} (hδ : δ.Injective)
    (α : Measure M) [SFinite α]
    (hα : ∀ f : M → ℝ≥0∞, Measurable f → ∫⁻ m, f m ∂ν = ∫⁻ m, ∑' d, f (δ d * m) ∂α)
    (hδ_mem : ∀ d, i (δ d) ∈ Γ) (hΓ : ∀ g ∈ Γ, ∃ d, g * i (δ d) ∈ N)
    {C : Set N} (hC : IsCompact C) (hΓC : ((Γ.subgroupOf N : Set N)) * C = univ) :
    ∃ c ≠ (0 : ℝ), ∀ F : G → E, Measurable F → (∀ n ∈ N, ∀ g, F (n * g) = F g) →
      (∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) →
      Integrable (fun p : M × K ↦ w p.1 • F (i p.1 * p.2)) (α.prod κ) →
      Integrable F (Γ.cutoffMeasure μ) ∧
        ∫ g, F g ∂Γ.cutoffMeasure μ = c • ∫ p : M × K, w p.1 • F (i p.1 * p.2) ∂α.prod κ := by
  -- By the Iwasawa formula, `w (α × κ) × (Γ ∩ N) \ N` in the coordinates `n i(m) k` unfolds to
  -- `r • μ` along `Γ`; `(Γ ∩ N) \ N` has finite volume, so `N` is unimodular.
  have : LocallyCompactSpace N := hN.locallyCompactSpace
  have : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set G)
  let lam' : Measure N := (Γ.subgroupOf N).cutoffMeasure lam
  have : IsFiniteMeasure lam' := Subgroup.isFiniteMeasure_cutoffMeasure_of_isCompact _ hC hΓC
  have : lam.IsMulRightInvariant := Subgroup.isMulRightInvariant_of_isFiniteMeasure_cutoffMeasure
    (Γ.subgroupOf N)
  obtain ⟨r, h_iwa⟩ := exists_lintegral_iwasawa_eq_mul (ν := ν) (κ := κ) (lam := lam) μ hN hw_pos hi
    h_dec h_conj
  have hr : r ≠ 0 := fun h ↦ by simpa [h, NeZero.ne] using h_iwa 1 measurable_one
  have hw_meas : Measurable fun p : M × K ↦ ENNReal.ofReal (w p.1) := by fun_prop
  let ρ : Measure (M × K) := (α.prod κ).withDensity fun p ↦ .ofReal (w p.1)
  let σ (p : M × K) : G := i p.1 * p.2
  let τ (p : (M × K) × N) : G := p.2 * σ p.1
  have : Countable Γ := countable_of_Lindelof_of_discrete
  have h_unfold : MeasurePreserving (fun p : ((M × K) × N) × Γ ↦ p.2 • τ p.1)
      ((ρ.prod lam').prod count) (r • μ) := by
    refine ⟨by fun_prop, ext_of_lintegral _ fun f hf ↦ ?_⟩
    calc
      _ = ∫⁻ p : M × K, ∫⁻ n : N, ∑' γ : Γ, f (γ * (n * (i p.1 * p.2))) ∂lam' ∂ρ := by
        simp (disch := fun_prop) only [lintegral_map, lintegral_prod, lintegral_count,
          Subgroup.smul_def, smul_eq_mul, τ, σ]
      _ = ∫⁻ k : K, ∫⁻ m : M, ∑' d, ∫⁻ n : N, f (i (δ d * m) * n * k) ∂lam ∂α ∂κ := by
        rw [lintegral_withDensity_eq_lintegral_mul _ hw_meas (by fun_prop),
          lintegral_prod_symm _ (by fun_prop)]
        simp only [Pi.mul_apply, lam',
          ofReal_mul_lintegral_cutoffMeasure_tsum hN h_conj h_triv hδ hδ_mem hΓ hf]
      _ = ∫⁻ k : K, ∫⁻ m : M, ∫⁻ n : N, f (i m * n * k) ∂lam ∂ν ∂κ :=
        lintegral_congr fun k ↦ (hα (fun m ↦ ∫⁻ n : N, f (i m * n * k) ∂lam) (by fun_prop)).symm
      _ = ∫⁻ g, f g ∂(r • μ) := by rw [h_iwa f hf, lintegral_smul_measure, smul_eq_mul]
  obtain ⟨c, hc, h_div⟩ := exists_integral_eq_mul_of_smul_measure (E := E) (Γ.cutoffMeasure μ) hr
    (NeZero.ne (lam' univ)) (measure_ne_top lam' univ)
  refine ⟨c, hc, fun F hF hFN hFΓ h_weighted ↦ ?_⟩
  -- By `h_unfold`, `F` on `Γ \ G` has the law of `F ∘ τ`, which does not depend on `n`.
  have hFτ (p : (M × K) × N) : F (τ p) = F (σ p.1) := hFN p.2 p.2.property (σ p.1)
  have h_law : IdentDistrib F (fun p : M × K ↦ F (σ p)) (r • Γ.cutoffMeasure μ)
      (lam' univ • ρ) := by
    rw [Subgroup.cutoffMeasure, cutoffMeasure_def, ← withDensity_smul_measure]
    refine ((isOrbitCutoff_orbitCutoff _).identDistrib_withDensity_of_measurePreserving (T := τ)
      (.id (count : Measure Γ)) h_unfold hF (by fun_prop)
      fun γ x ↦ hFΓ γ γ.property x).trans ⟨by fun_prop, by fun_prop, ?_⟩
    simp (disch := fun_prop) only [hFτ, ← map_fst_prod, map_map, comp_def]
  have h_int : Integrable (fun p : M × K ↦ F (σ p)) ρ := by
    simpa [ρ, σ, integrable_withDensity_iff_integrable_smul' hw_meas, hw_pos, le_of_lt]
      using h_weighted
  refine h_div F _ (h_law.integrable_iff.2 (h_int.smul_measure (measure_ne_top lam' univ))) ?_
  rw [h_law.integral_eq, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hw_meas (by simp)]
  simp [σ, hw_pos, le_of_lt]

end MeasureTheory
