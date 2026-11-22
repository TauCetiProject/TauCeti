/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Normalize
public import TauCeti.Analysis.Pseudodifferential.Composition.Expansion
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Normed.Module.Cone
import TauCeti.Analysis.Normed.Module.Normalize
import TauCeti.Topology.Constructions.SumProd

/-!
# Microlocal cutoffs

A *microlocal cutoff* localizes a pseudodifferential operator near a set of positions and a cone
of frequency directions. For smooth real functions `φ` of the position and `ψ` of the frequency,
`TauCeti.HomogeneousSymbol.microlocalCutoff` is the homogeneous symbol of degree `0`

`(x, ξ) ↦ φ(x) ψ(ξ / ‖ξ‖) • id`,

which depends on the frequency only through its direction. Multiplied by a frequency cutoff `χ` it
becomes the classical symbol of order `0` `χ(ξ) φ(x) ψ(ξ / ‖ξ‖) • id`
(`TauCeti.ClassicalSymbol.ofHomogeneous`), whose principal symbol is `φ(x) ψ(ξ / ‖ξ‖) • id`.

Microlocal cutoffs exist for every microlocal region
(`TauCeti.ClassicalSymbol.exists_microlocalCutoff`): given a compact set `K` inside an open set
`U` of positions and a closed cone `F` inside an open cone `Γ` of frequencies, there is a
classical symbol `c` of order `0` that is the identity near every point of `K × F` at frequencies
of norm greater than `2`, whose principal symbol is the identity on `K × (F \ {0})`, and which
vanishes outside `L × G` for a compact `L ⊆ U` and a closed cone `G` with `G \ {0} ⊆ Γ`. Since
`L × G` is again a compact set of positions times a closed cone, cutoffs can be nested: a second
cutoff can be chosen to be the identity near every point of `L × G` at frequencies of norm greater
than `2`. Composed with a dilated frequency cutoff, a microlocal cutoff also vanishes below any
given frequency radius (`TauCeti.Symbol.exists_microlocalCutoff_of_mem`).

A cutoff that is the identity near the region where a symbol `b` lives does not change `b` at the
level of operators, up to smoothing operators: `Op(c) Op(b)` and `Op(b) Op(c)` are `Op(b)` modulo
an operator with smoothing symbol (`TauCeti.Symbol.isSmoothing_sharp_sub_of_eventuallyEq_id_left`,
`TauCeti.Symbol.isSmoothing_sharp_sub_of_eventuallyEq_id_right`). Both rest on the microlocality of
the composition symbol, `TauCeti.Symbol.isSmoothing_sharp_sub_comp_of_eventuallyEq`: wherever one
of the factors is locally constant, all correction terms of the composition expansion vanish.
These are the cutoffs and the cutoff identities with which a microlocal parametrix is turned into
microlocal elliptic regularity, `WF(u) ⊆ WF(P u) ∪ Char(P)`.

## Main declarations

* `TauCeti.HomogeneousSymbol.microlocalCutoff`: the homogeneous symbol `φ(x) ψ(ξ / ‖ξ‖) • id`.
* `TauCeti.ClassicalSymbol.exists_microlocalCutoff`: existence of microlocal cutoffs, and
  `TauCeti.Symbol.exists_microlocalCutoff`: cutoffs that also vanish below a given frequency radius.
* `TauCeti.Symbol.exists_microlocalCutoff_of_mem`: microlocal cutoffs with compact spatial support
  around a point that vanish below a given frequency radius.
* `TauCeti.Symbol.isSmoothing_sharp_sub_of_eventuallyEq_id_left`,
  `TauCeti.Symbol.isSmoothing_sharp_sub_of_eventuallyEq_id_right`: `c # b` and `b # c` agree with
  `b` modulo smoothing symbols when, at every large frequency, `b` vanishes or `c` is the identity
  near the point.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §7.
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace TauCeti

namespace HomogeneousSymbol

variable {X E V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℂ V] {φ : X → ℝ} {ψ : E → ℝ}

variable (V) in
/-- The **microlocal cutoff** `φ(x) ψ(ξ / ‖ξ‖) • id`: the homogeneous symbol of degree `0` that
localizes in the position by `φ` and in the direction of the frequency by `ψ`. -/
def microlocalCutoff (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) : HomogeneousSymbol X E V V 0 :=
  mk' (fun p ↦ (φ p.1 * ψ (NormedSpace.normalize p.2)) • ContinuousLinearMap.id ℂ V)
    (fun _ hp ↦ (((hφ.comp contDiff_fst).contDiffAt.mul
      (hψ.contDiffAt.comp _ ((NormedSpace.contDiffAt_normalize hp).comp _ contDiffAt_snd))).smul
        contDiffAt_const).contDiffWithinAt)
    fun x ξ _ t ht ↦ by simp [NormedSpace.normalize_smul_of_pos ht]

@[simp]
theorem coefficient_microlocalCutoff (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) (x : X)
    {ξ : E} (hξ : ξ ≠ 0) :
    (microlocalCutoff V hφ hψ).coefficient (x, ξ) =
      (φ x * ψ (NormedSpace.normalize ξ)) • ContinuousLinearMap.id ℂ V :=
  coefficient_mk'_of_ne_zero _ _ _ hξ

variable {n : ℕ}

/-- The cut-off term of a microlocal cutoff is `χ(ξ) φ(x) ψ(ξ / ‖ξ‖) • id` at every frequency,
including `ξ = 0`, where both sides vanish. -/
theorem coefficient_cutoffSymbol_microlocalCutoff (χ : FrequencyCutoff (CoordinateSpace n))
    {φ ψ : CoordinateSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (cutoffSymbol χ (microlocalCutoff V hφ hψ)).coefficient p =
      (χ p.2 * φ p.1 * ψ (NormedSpace.normalize p.2)) • ContinuousLinearMap.id ℂ V := by
  obtain ⟨x, ξ⟩ := p
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  · simp [coefficient_microlocalCutoff _ _ _ hξ, smul_smul, mul_assoc]

/-- The cut-off term of a microlocal cutoff with compactly supported `φ` has compact spatial
support. -/
theorem hasCompactSpatialSupport_cutoffSymbol_microlocalCutoff
    (χ : FrequencyCutoff (CoordinateSpace n)) {φ ψ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) (hφc : HasCompactSupport φ) :
    (cutoffSymbol χ (microlocalCutoff V hφ hψ)).HasCompactSpatialSupport :=
  Symbol.hasCompactSpatialSupport_iff.2 ⟨tsupport φ, hφc, fun x hx ξ ↦ by
    rw [coefficient_cutoffSymbol_microlocalCutoff]
    simp [image_eq_zero_of_notMem_tsupport hx]⟩

end HomogeneousSymbol

open HomogeneousSymbol

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

namespace Symbol

variable {m : ℝ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- **A cutoff equal to the identity where `b` lives is a left identity for `b`.** Let `b` have
compact spatial support, and let `c` be a symbol of order `0` such that at every `(x, ξ)` with
`‖ξ‖ ≥ R` either `b` vanishes near `(x, ξ)` or `c` is the identity near `(x, ξ)`. Then
`c # b - b` is smoothing: `Op(c) Op(b) = Op(b)` modulo a smoothing operator. -/
theorem isSmoothing_sharp_sub_of_eventuallyEq_id_left [CompleteSpace W] {c : Symbol n W W 0}
    {b : Symbol n V W m} (hb : b.HasCompactSpatialSupport) (R : ℝ)
    (h : ∀ x ξ, R ≤ ‖ξ‖ → b.coefficient =ᶠ[𝓝 (x, ξ)] (fun _ ↦ 0) ∨
      c.coefficient =ᶠ[𝓝 (x, ξ)] fun _ ↦ ContinuousLinearMap.id ℂ W) :
    (c.sharp b hb - inclusion (zero_add m).ge b).IsSmoothing := by
  have h₁ := isSmoothing_sharp_sub_comp_of_eventuallyEq hb R fun x ξ hξ ↦
    (h x ξ hξ).elim (fun hb ↦ Or.inr hb.prodMk_left_nhds) fun hc ↦ Or.inl hc.prodMk_right_nhds
  have h₂ : (c.comp b - inclusion (zero_add m).ge b).IsSmoothing :=
    isSmoothing_of_coefficient_eq_zero R fun x ξ hξ ↦ by
      rcases h x ξ hξ with hb | hc
      · simp [hb.self_of_nhds]
      · simp [hc.self_of_nhds]
  simpa using h₁.add h₂

/-- **A cutoff equal to the identity where `b` lives is a right identity for `b`.** Let `c` be a
symbol of order `0` with compact spatial support such that at every `(x, ξ)` with `‖ξ‖ ≥ R` either
`b` vanishes near `(x, ξ)` or `c` is the identity near `(x, ξ)`. Then `b # c - b` is smoothing:
`Op(b) Op(c) = Op(b)` modulo a smoothing operator. -/
theorem isSmoothing_sharp_sub_of_eventuallyEq_id_right [CompleteSpace V] [CompleteSpace W]
    {c : Symbol n V V 0} {b : Symbol n V W m} (hc : c.HasCompactSpatialSupport) (R : ℝ)
    (h : ∀ x ξ, R ≤ ‖ξ‖ → b.coefficient =ᶠ[𝓝 (x, ξ)] (fun _ ↦ 0) ∨
      c.coefficient =ᶠ[𝓝 (x, ξ)] fun _ ↦ ContinuousLinearMap.id ℂ V) :
    (b.sharp c hc - inclusion (add_zero m).ge b).IsSmoothing := by
  have h₁ := isSmoothing_sharp_sub_comp_of_eventuallyEq hc R fun x ξ hξ ↦
    (h x ξ hξ).elim (fun hb ↦ Or.inl hb.prodMk_right_nhds) fun hc ↦ Or.inr hc.prodMk_left_nhds
  have h₂ : (b.comp c - inclusion (add_zero m).ge b).IsSmoothing :=
    isSmoothing_of_coefficient_eq_zero R fun x ξ hξ ↦ by
      rcases h x ξ hξ with hb | hc
      · simp [hb.self_of_nhds]
      · simp [hc.self_of_nhds]
  simpa using h₁.add h₂

end Symbol

namespace ClassicalSymbol

/-- **Existence of microlocal cutoffs.** Let `K` be a compact set inside an open set `U` of
positions, and `F` a closed cone inside an open cone `Γ` of frequencies, in the sense that every
nonzero `ξ ∈ F` lies in `Γ`. There is a classical symbol `c` of order `0` such that

* `c` is the identity near every `(x, ξ) ∈ K × F` with `‖ξ‖ > 2`;
* its principal symbol is the identity at every `(x, ξ) ∈ K × F` with `ξ ≠ 0`;
* `c` has compact spatial support and vanishes unless `x ∈ L`, `ξ ∈ G` and `‖ξ‖ > 1`, for a
  compact set `L ⊆ U` and a closed cone `G` whose nonzero elements lie in `Γ`. -/
theorem exists_microlocalCutoff {K U F Γ : Set (CoordinateSpace n)} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hF : IsClosed F) (hFcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ F, t • ξ ∈ F)
    (hΓ : IsOpen Γ) (hΓcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ Γ, t • ξ ∈ Γ)
    (hFΓ : ∀ ξ ∈ F, ξ ≠ 0 → ξ ∈ Γ) :
    ∃ c : ClassicalSymbol n V V 0,
      (∀ x ∈ K, ∀ ξ ∈ F, 2 < ‖ξ‖ →
        c.toSymbol.coefficient =ᶠ[𝓝 (x, ξ)] fun _ ↦ ContinuousLinearMap.id ℂ V) ∧
      (∀ x ∈ K, ∀ ξ ∈ F, ξ ≠ 0 → c.principal.coefficient (x, ξ) = ContinuousLinearMap.id ℂ V) ∧
      c.toSymbol.HasCompactSpatialSupport ∧
      ∃ L G : Set (CoordinateSpace n), IsCompact L ∧ L ⊆ U ∧ IsClosed G ∧
        (∀ t : ℝ, 0 < t → ∀ ξ ∈ G, t • ξ ∈ G) ∧ (∀ ξ ∈ G, ξ ≠ 0 → ξ ∈ Γ) ∧
        ∀ x ξ, c.toSymbol.coefficient (x, ξ) ≠ 0 → x ∈ L ∧ ξ ∈ G ∧ 1 < ‖ξ‖ := by
  -- A spatial cutoff `φ`, equal to `1` near `K` with compact support in `U`, and an angular
  -- cutoff `ψ`, equal to `1` near the set `A` of directions of `F` with compact support in `Γ`.
  obtain ⟨φ, hφ, -, hφ1, hφc, hφU⟩ := hK.exists_contDiff_cutoff_eventuallyEq_one hU hKU
  set A := F ∩ Metric.sphere (0 : CoordinateSpace n) 1
  have hAΓ : A ⊆ Γ := fun ξ hξ ↦ hFΓ ξ hξ.1 (by rintro rfl; simpa using hξ.2)
  obtain ⟨ψ, hψ, -, hψ1, -, hψΓ⟩ :=
    ((isCompact_sphere 0 1).inter_left hF).exists_contDiff_cutoff_eventuallyEq_one hΓ hAΓ
  have hdir : ∀ ξ ∈ F, ξ ≠ 0 → NormedSpace.normalize ξ ∈ A := fun ξ hξ hξ0 ↦
    ⟨hFcone _ (inv_pos.2 (norm_pos_iff.2 hξ0)) ξ hξ, by simp [hξ0]⟩
  set c := ofHomogeneous (default : FrequencyCutoff (CoordinateSpace n))
    (microlocalCutoff V hφ hψ)
  have hc (p : CoordinateSpace n × CoordinateSpace n) : c.toSymbol.coefficient p =
      ((default : FrequencyCutoff (CoordinateSpace n)) p.2 * φ p.1 *
        ψ (NormedSpace.normalize p.2)) • ContinuousLinearMap.id ℂ V := by
    rw [toSymbol_ofHomogeneous, coefficient_cutoffSymbol_microlocalCutoff]
  -- `c` vanishes unless `x ∈ tsupport φ`, the direction of `ξ` lies in `tsupport ψ` and
  -- `‖ξ‖ > 1`, where the frequency cutoff is nonzero.
  set G := {ξ : CoordinateSpace n | ξ = 0 ∨ NormedSpace.normalize ξ ∈ tsupport ψ}
  have hsupp : ∀ x ξ, c.toSymbol.coefficient (x, ξ) ≠ 0 →
      x ∈ tsupport φ ∧ ξ ∈ G ∧ 1 < ‖ξ‖ := by
    intro x ξ h
    have h' : (default : FrequencyCutoff (CoordinateSpace n)) ξ * φ x *
        ψ (NormedSpace.normalize ξ) ≠ 0 := fun h0 ↦ h (by simp [hc, h0])
    simp only [mul_ne_zero_iff] at h'
    obtain ⟨⟨hχ, hφx⟩, hψξ⟩ := h'
    refine ⟨subset_tsupport _ hφx, Or.inr (subset_tsupport _ hψξ), not_le.1 fun hξ ↦ ?_⟩
    exact hχ (FrequencyCutoff.apply_eq_zero_of_norm_le_one _ hξ)
  refine ⟨c, fun x hx ξ hξF hξ ↦ ?_, fun x hx ξ hξF hξ0 ↦ ?_,
    ?_, tsupport φ, G, hφc, hφU, ?_, fun t ht ξ hξ ↦ ?_, fun ξ hξ hξ0 ↦ ?_, hsupp⟩
  · -- Near `(x, ξ)` all three factors equal `1`.
    have hξ0 : ξ ≠ 0 := norm_pos_iff.1 (by linarith)
    have hnorm : Tendsto (fun p : CoordinateSpace n × CoordinateSpace n ↦
        NormedSpace.normalize p.2) (𝓝 (x, ξ)) (𝓝 (NormedSpace.normalize ξ)) :=
      (continuous_snd.tendsto (x, ξ)).normalize hξ0
    filter_upwards [continuous_fst.tendsto (x, ξ) |>.eventually (hφ1 x hx),
      hnorm.eventually (hψ1 _ (hdir ξ hξF hξ0)),
      (isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).mem_nhds hξ]
      with p hφp hψp hp
    rw [hc, FrequencyCutoff.apply_eq_one_of_two_le_norm _ (le_of_lt hp), hφp, hψp]
    simp
  · rw [principal_ofHomogeneous, coefficient_microlocalCutoff _ _ _ hξ0,
      (hφ1 x hx).self_of_nhds, (hψ1 _ (hdir ξ hξF hξ0)).self_of_nhds, one_mul, one_smul]
  · rw [toSymbol_ofHomogeneous]
    exact hasCompactSpatialSupport_cutoffSymbol_microlocalCutoff _ _ _ hφc
  · exact NormedSpace.isClosed_setOf_eq_zero_or_normalize_mem (isClosed_tsupport ψ)
  · rcases hξ with rfl | hξ
    · simp [G]
    · exact Or.inr (by rwa [NormedSpace.normalize_smul_of_pos ht])
  · simpa using hΓcone _ (norm_pos_iff.2 hξ0) _ (hψΓ (hξ.resolve_left hξ0))

end ClassicalSymbol

namespace Symbol

/-- **Microlocal cutoffs vanishing at small frequencies.** Let `K` be a compact set inside an open
set `U` of positions, `F` a closed cone inside an open cone `Γ` of frequencies, and `R` a radius.
There is a symbol `c` of order `0` that is the identity at every `(x, ξ) ∈ K × F` of large
frequency, and vanishes unless `x ∈ U`, `ξ ∈ Γ` and `‖ξ‖ ≥ R`. It is the cutoff of
`TauCeti.ClassicalSymbol.exists_microlocalCutoff`, cut off below the radius `R` by a frequency
cutoff `χ(ξ / R)`; this makes it vanish outside a set `{x ∈ U, ξ ∈ Γ, ‖ξ‖ ≥ R}` on which a symbol
is elliptic, as microlocal parametrix symbols require
(`TauCeti.Symbol.IsEllipticOn.exists_isAsymptoticSum_sharpTerm_left`). -/
theorem exists_microlocalCutoff {K U F Γ : Set (CoordinateSpace n)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (hF : IsClosed F)
    (hFcone : ∀ r : ℝ, 0 < r → ∀ ξ ∈ F, r • ξ ∈ F) (hΓ : IsOpen Γ)
    (hΓcone : ∀ r : ℝ, 0 < r → ∀ ξ ∈ Γ, r • ξ ∈ Γ) (hFΓ : ∀ ξ ∈ F, ξ ≠ 0 → ξ ∈ Γ) (R : ℝ) :
    ∃ c : Symbol n V V 0, (∀ p, c.coefficient p ≠ 0 → p.1 ∈ U ∧ p.2 ∈ Γ ∧ R ≤ ‖p.2‖) ∧
      ∃ R', ∀ x ∈ K, ∀ ξ ∈ F, R' ≤ ‖ξ‖ → c.coefficient (x, ξ) = ContinuousLinearMap.id ℂ V := by
  obtain ⟨c₀, hc₀, -, -, L, G, -, hLU, -, -, hGΓ, hc₀0⟩ :=
    ClassicalSymbol.exists_microlocalCutoff (V := V) hK hU hKU hF hFcone hΓ hΓcone hFΓ
  -- Cut `c₀` off below the radius `R₁ = max R 1` by the frequency cutoff `χ(ξ / R₁)`.
  set R₁ := max R 1
  have hR₁ : 0 < R₁ := lt_max_of_lt_right one_pos
  set χ : FrequencyCutoff (CoordinateSpace n) := default
  have hR₁1 : 1 ≤ R₁ := le_max_right R 1
  have hd := coefficient_dilatedCutoff_comp χ hR₁1 c₀.toSymbol
  refine ⟨inclusion (by norm_num) ((dilatedCutoff χ hR₁1).comp c₀.toSymbol), fun p hp ↦ ?_,
    2 * R₁ + 2, fun x hx ξ hξ hR ↦ ?_⟩
  · simp only [coefficient_inclusion, hd, ne_eq, smul_eq_zero, not_or] at hp
    obtain ⟨hχ, hc⟩ := hp
    obtain ⟨hL, hG, h1⟩ := hc₀0 p.1 p.2 hc
    refine ⟨hLU hL, hGΓ _ hG (norm_pos_iff.1 (one_pos.trans h1)), ?_⟩
    by_contra hlt
    exact hχ (χ.apply_inv_smul_eq_zero hR₁ ((not_le.1 hlt).le.trans (le_max_left _ _)))
  · simp only [coefficient_inclusion, hd]
    rw [χ.apply_inv_smul_eq_one hR₁ (by linarith), one_smul]
    exact (hc₀ x hx ξ hξ (by linarith)).self_of_nhds

open Metric

/-- **Microlocal cutoffs with compact spatial support vanishing at small frequencies.** For an
open set `U` containing `x₀`, an open cone `Γ` containing `ξ₀` and a radius `R`, there is a symbol
`c` of order `0` with compact spatial support that vanishes outside the points `(x, ξ)` with
`x ∈ U`, `ξ ∈ Γ` and `‖ξ‖ ≥ R`, and is the identity at large frequencies over a neighbourhood of
`x₀` and an open cone containing `ξ₀`. -/
theorem exists_microlocalCutoff_of_mem {U Γ : Set (CoordinateSpace n)} {x₀ ξ₀ : CoordinateSpace n}
    (hU : IsOpen U) (hx₀ : x₀ ∈ U) (hΓ : IsOpen Γ) (hξ₀ : ξ₀ ∈ Γ)
    (hcone : ∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) (R : ℝ) :
    ∃ c : Symbol n V V 0, c.HasCompactSpatialSupport ∧
      (∀ p ∉ {q : CoordinateSpace n × CoordinateSpace n | q.1 ∈ U ∧ q.2 ∈ Γ ∧ R ≤ ‖q.2‖},
        c.coefficient p = 0) ∧
      ∃ U' Γ' : Set (CoordinateSpace n), IsOpen U' ∧ x₀ ∈ U' ∧ IsOpen Γ' ∧ ξ₀ ∈ Γ' ∧
        (∀ t : ℝ, 0 < t → ∀ η ∈ Γ', t • η ∈ Γ') ∧ ∃ R' : ℝ, ∀ x ∈ U', ∀ ξ ∈ Γ', R' ≤ ‖ξ‖ →
          c.coefficient (x, ξ) = ContinuousLinearMap.id ℂ V := by
  -- A closed ball of positions around `x₀` inside `U`, and an open cone `Γ'` around `ξ₀` inside a
  -- closed cone `F` whose nonzero elements lie in `Γ`.
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  obtain ⟨F, Γ', hF, hFcone, hFΓ, hΓ', hξ₀', hcone', hΓ'F⟩ :=
    hΓ.exists_isOpen_cone_subset_isClosed_cone hcone hξ₀
  obtain ⟨c₀, hc₀1, -, hc₀c, L', G, -, hLU, -, -, hGΓ, hc₀0⟩ :=
    ClassicalSymbol.exists_microlocalCutoff (V := V) (isCompact_closedBall x₀ (δ / 2)) hU
      ((closedBall_subset_ball (half_lt_self hδ)).trans hδU) hF hFcone hΓ hcone hFΓ
  obtain ⟨K, hK, hKc₀⟩ := hasCompactSpatialSupport_iff.1 hc₀c
  -- Cut `c₀` off below the radius `t = max R 1`: `c = χ(ξ / t) c₀`.
  have ht : 1 ≤ max R 1 := le_max_right R 1
  have ht0 : 0 < max R 1 := one_pos.trans_le ht
  obtain ⟨χ⟩ : Nonempty (FrequencyCutoff (CoordinateSpace n)) := ⟨default⟩
  set c := inclusion (add_zero 0).le ((dilatedCutoff χ ht).comp c₀.toSymbol)
  have hc (p : CoordinateSpace n × CoordinateSpace n) :
      c.coefficient p = χ ((max R 1)⁻¹ • p.2) • c₀.toSymbol.coefficient p := by
    rw [coefficient_inclusion, coefficient_dilatedCutoff_comp]
  refine ⟨c, hasCompactSpatialSupport_iff.2
    ⟨K, hK, fun x hx ξ ↦ by rw [hc, hKc₀ x hx ξ, smul_zero]⟩, fun p hp ↦ ?_,
    ball x₀ (δ / 2), Γ', isOpen_ball, mem_ball_self (half_pos hδ), hΓ', hξ₀', hcone',
    2 * max R 1 + 1, fun x hx ξ hξ hR ↦ ?_⟩
  · -- `c` vanishes unless `‖ξ‖ > max R 1` and `c₀(x, ξ) ≠ 0`.
    by_contra hne
    rw [hc, smul_eq_zero, not_or] at hne
    obtain ⟨hp₁, hp₂, -⟩ := hc₀0 p.1 p.2 hne.2
    have hR : max R 1 < ‖p.2‖ := not_le.1 fun h ↦ hne.1 (χ.apply_inv_smul_eq_zero ht0 h)
    have hp0 : p.2 ≠ 0 := norm_pos_iff.1 (ht0.trans hR)
    exact hp ⟨hLU hp₁, hGΓ _ hp₂ hp0, (le_max_left R 1).trans hR.le⟩
  · -- At large frequencies over `U' × Γ'` both factors are the identity.
    rw [hc, χ.apply_inv_smul_eq_one ht0 (by linarith), one_smul]
    exact (hc₀1 x (ball_subset_closedBall hx) ξ (hΓ'F hξ) (by linarith)).self_of_nhds

end Symbol

end TauCeti
