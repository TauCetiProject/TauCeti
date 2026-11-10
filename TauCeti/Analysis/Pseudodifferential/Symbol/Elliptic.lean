/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Frequency.Cutoff
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Frequency
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Elliptic symbols and their inverse symbols

A symbol `a ∈ S^m_{1,0}` with values in `V →L[ℂ] W` is *elliptic above the radius `R`*
(`TauCeti.Symbol.IsEllipticAbove`) if at every frequency `ξ` with `R ≤ ‖ξ‖` the value `a(x, ξ)`
is invertible, with

`‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)`

for `x` in each compact set, where `⟨ξ⟩ = (1 + ‖ξ‖²)^(1/2)`. It is *uniformly elliptic above `R`*
(`TauCeti.Symbol.IsUniformlyEllipticAbove`) if one constant `C` works for all positions `x`. In
both notions the radius `R` is the same for all positions.

The main result is that the inverse of an elliptic symbol, cut off at large frequencies, is a
symbol of order `-m`. For a frequency cutoff `χ` and a radius `t ≥ 1` with `2 R < t`,

`TauCeti.Symbol.cutoffInverse χ a ha ht hRt (x, ξ) = χ(ξ / t) a(x, ξ)⁻¹`

is a symbol of order `-m`, which equals `a(x, ξ)⁻¹` for `‖ξ‖ ≥ 2 t`. Its pointwise products with
`a` in either order are therefore the identity up to a smoothing symbol
(`TauCeti.Symbol.isSmoothing_cutoffInverse_comp_sub` and
`TauCeti.Symbol.isSmoothing_comp_cutoffInverse_sub`). This is the first step in the construction of
a parametrix of an elliptic pseudodifferential operator. For a uniform symbol that is uniformly
elliptic, the inverse symbol is uniform (`TauCeti.Symbol.isUniform_cutoffInverse`).

The derivative estimates of `a⁻¹` come from the formula `∂(a⁻¹) = -a⁻¹ (∂a) a⁻¹`: by induction on
the total length of `α` and `β`, the mixed derivative `∂_x^α ∂_ξ^β (a⁻¹)` is controlled through
the Leibniz rule by mixed derivatives of `a⁻¹` of smaller length and by those of `a`, and each of
these products has the weight `⟨ξ⟩^(-m - |β|)`. Only the values at large frequencies matter,
since the cutoff vanishes for `‖ξ‖ ≤ t`.

Conversely, a symbol that a symbol of order `-m` inverts at all large frequencies is elliptic
(`TauCeti.Symbol.isEllipticAbove_of_comp_eq_id`), so a symbol is elliptic above some radius
exactly when it has such an inverse (`TauCeti.Symbol.exists_isEllipticAbove_iff`), and similarly
for uniform ellipticity (`TauCeti.Symbol.exists_isUniformlyEllipticAbove_iff`). For example the
Bessel weight `⟨ξ / 2π⟩^s` is uniformly elliptic of order `s`
(`TauCeti.Symbol.isUniformlyEllipticAbove_besselPotential`).

## Main declarations

* `TauCeti.Symbol.IsEllipticAbove`, `TauCeti.Symbol.IsUniformlyEllipticAbove`: ellipticity of a
  symbol above a radius, with locally uniform and uniform constants.
* `TauCeti.Symbol.cutoffInverse`: the cut-off inverse `χ(ξ / t) a(x, ξ)⁻¹`, a symbol of
  order `-m`.
* `TauCeti.Symbol.isSmoothing_cutoffInverse_comp_sub`,
  `TauCeti.Symbol.isSmoothing_comp_cutoffInverse_sub`: it is a pointwise two-sided inverse of `a`
  modulo smoothing symbols, and `TauCeti.Symbol.isSmoothing_cutoffInverse_sub_cutoffInverse`: it
  does not depend on the cutoff and the radius modulo smoothing symbols.
* `TauCeti.Symbol.IsEllipticAbove.comp`, `TauCeti.Symbol.IsUniformlyEllipticAbove.comp`: pointwise
  products of elliptic symbols are elliptic.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.1)–(4.6).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace TauCeti

variable {n : ℕ}

/-! ### Symbol estimates at large frequencies -/

section Estimates

variable {A F G H : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H]
  [NormedSpace ℝ H] {K : Set (CoordinateSpace n)} {ρ μ ν κ : ℝ} {N : ℕ}

/-- `f` satisfies the symbol estimates of order `μ` for its mixed derivatives of total length at
most `N`, at the positions in `K` and the frequencies of norm greater than `ρ`. -/
private def EstimatesUpTo (K : Set (CoordinateSpace n)) (ρ μ : ℝ) (N : ℕ)
    (f : CoordinateSpace n × CoordinateSpace n → A) : Prop :=
  ∀ α β : List (Fin n), α.length + β.length ≤ N → ∃ C : ℝ, ∀ x ∈ K, ∀ ξ, ρ < ‖ξ‖ →
    ‖mixedDeriv α β f x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((μ - β.length) / 2)

/-- Estimates for all mixed derivatives give estimates up to every length. -/
private theorem estimatesUpTo_of_forall {f : CoordinateSpace n × CoordinateSpace n → A}
    (h : ∀ α β : List (Fin n), ∃ C : ℝ, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β f x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((μ - β.length) / 2)) :
    EstimatesUpTo K ρ μ N f :=
  fun α β _ => (h α β).imp fun _ hC x hx ξ _ => hC x hx ξ

/-- Estimates are local in the frequency region: they transfer along functions with the same
germs at every point of the region. -/
private theorem EstimatesUpTo.congr {f g : CoordinateSpace n × CoordinateSpace n → A}
    (hg : EstimatesUpTo K ρ μ N g) (h : ∀ p : CoordinateSpace n × CoordinateSpace n,
      ρ < ‖p.2‖ → f =ᶠ[𝓝 p] g) :
    EstimatesUpTo K ρ μ N f :=
  fun α β hαβ => (hg α β hαβ).imp fun _ hC x hx ξ hξ => by
    rw [(h (x, ξ) hξ).mixedDeriv_eq]
    exact hC x hx ξ hξ

private theorem EstimatesUpTo.neg {f : CoordinateSpace n × CoordinateSpace n → A}
    (hf : EstimatesUpTo K ρ μ N f) : EstimatesUpTo K ρ μ N fun p => -f p :=
  fun α β hαβ => (hf α β hαβ).imp fun _ hC x hx ξ hξ => by
    rw [← Pi.neg_def, mixedDeriv_neg, norm_neg]
    exact hC x hx ξ hξ

/-- The **Leibniz rule** for the estimates: if `f` and `g` satisfy the estimates of orders `μ`
and `ν`, then `p ↦ B (f p) (g p)` satisfies those of order `μ + ν`, for every continuous bilinear
map `B`. -/
private theorem EstimatesUpTo.bilinear (B : F →L[ℝ] G →L[ℝ] H)
    {f : CoordinateSpace n × CoordinateSpace n → F} {g : CoordinateSpace n × CoordinateSpace n → G}
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g) (hκ : μ + ν = κ)
    (hf : EstimatesUpTo K ρ μ N f) (hg : EstimatesUpTo K ρ ν N g) :
    EstimatesUpTo K ρ κ N fun p => B (f p) (g p) := by
  classical
  intro α β hαβ
  choose C hC using hf
  choose D hD using hg
  -- The constants, extended by `0` to words that are too long.
  let C' : List (Fin n) → List (Fin n) → ℝ := fun s t =>
    if h : s.length + t.length ≤ N then C s t h else 0
  let D' : List (Fin n) → List (Fin n) → ℝ := fun s t =>
    if h : s.length + t.length ≤ N then D s t h else 0
  refine ⟨‖B‖ * (β.sublists'.revzip.map fun t => (α.sublists'.revzip.map fun s =>
    C' s.1 t.1 * D' s.2 t.2).sum).sum, fun x hx ξ hξ => ?_⟩
  rw [← hκ]
  refine B.norm_mixedDeriv_le_of_bilinear hfs hgs α β (fun s t hst => ?_) fun s t hst => ?_
  · have h : s.length + t.length ≤ N := hst.trans hαβ
    simpa only [C', h, ↓reduceDIte] using hC s t h x hx ξ hξ
  · have h : s.length + t.length ≤ N := hst.trans hαβ
    simpa only [D', h, ↓reduceDIte] using hD s t h x hx ξ hξ

/-- Estimates for the first-order derivatives give estimates of one more length: the mixed
derivatives of `f` of length `N + 1` are mixed derivatives of length `N` of its first-order
derivatives. -/
private theorem estimatesUpTo_succ {f : CoordinateSpace n × CoordinateSpace n → A}
    (hfs : ContDiff ℝ ∞ f) (h₀ : EstimatesUpTo K ρ μ 0 f)
    (hfreq : ∀ j : Fin n, EstimatesUpTo K ρ (μ - 1) N
      fun p => coordinateDeriv [j] (fun η => f (p.1, η)) p.2)
    (hpos : ∀ j : Fin n, EstimatesUpTo K ρ μ N
      fun p => coordinateDeriv [j] (fun y => f (y, p.2)) p.1) :
    EstimatesUpTo K ρ μ (N + 1) f := by
  intro α β hαβ
  rcases β.eq_nil_or_concat with rfl | ⟨β, j, rfl⟩ <;> try simp only [List.concat_eq_append] at *
  · rcases α.eq_nil_or_concat with rfl | ⟨α, j, rfl⟩ <;> try simp only [List.concat_eq_append] at *
    · exact h₀ [] [] le_rfl
    · obtain ⟨C, hC⟩ := hpos j α [] (by simp at hαβ; omega)
      exact ⟨C, fun x hx ξ hξ => by
        rw [← mixedDeriv_coordinateDeriv_fst hfs]
        exact hC x hx ξ hξ⟩
  · obtain ⟨C, hC⟩ := hfreq j α β (by simp at hαβ; omega)
    exact ⟨C, fun x hx ξ hξ => by
      rw [← mixedDeriv_coordinateDeriv_snd, ← Symbol.order_sub_one_sub_length]
      exact hC x hx ξ hξ⟩

/-- The dilated cutoffs `χ(ξ / t)`, `t ≥ 1`, satisfy the estimates of order `0` at all positions
and frequencies. -/
private theorem estimatesUpTo_cutoff (χ : FrequencyCutoff (CoordinateSpace n)) {t : ℝ}
    (ht : 1 ≤ t) : EstimatesUpTo K ρ 0 N fun p => χ (t⁻¹ • p.2) := by
  refine estimatesUpTo_of_forall fun α β => ?_
  rcases eq_or_ne α [] with rfl | hα
  · obtain ⟨C, -, hC⟩ := χ.exists_norm_iteratedFDeriv_comp_inv_smul_le β.length
    refine ⟨C, fun x _ ξ => ?_⟩
    rw [mixedDeriv_nil_comp_snd fun η => χ (t⁻¹ • η), zero_sub]
    exact (norm_coordinateDeriv_le β (f := fun η => χ (t⁻¹ • η))
      (((χ.contDiff (n := ⊤)).comp (contDiff_const_smul t⁻¹)).of_le (by exact_mod_cast le_top))
      ξ).trans (hC t ht ξ)
  · exact ⟨0, fun x _ ξ => by
      rw [mixedDeriv_comp_snd (fun η => χ (t⁻¹ • η)) hα, norm_zero, zero_mul]⟩

end Estimates

/-! ### The derivatives of an inverse -/

section Inverse

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-- The estimates of a pointwise composition of families of `ℂ`-linear maps. -/
private theorem EstimatesUpTo.comp {E₁ E₂ E₃ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [NormedAddCommGroup E₃] [NormedSpace ℂ E₃]
    {K : Set (CoordinateSpace n)} {ρ μ ν κ : ℝ} {N : ℕ}
    {f : CoordinateSpace n × CoordinateSpace n → E₂ →L[ℂ] E₃}
    {g : CoordinateSpace n × CoordinateSpace n → E₁ →L[ℂ] E₂}
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g) (hκ : μ + ν = κ)
    (hf : EstimatesUpTo K ρ μ N f) (hg : EstimatesUpTo K ρ ν N g) :
    EstimatesUpTo K ρ κ N fun p => (f p).comp (g p) :=
  EstimatesUpTo.bilinear ((ContinuousLinearMap.compL ℂ E₁ E₂ E₃).bilinearRestrictScalars ℝ)
    hfs hgs hκ hf hg

/-- At the frequencies of norm at least `2 s`, `χ(ξ / s) a(x, ξ)⁻¹` is a two-sided inverse of
`a(x, ξ)`, for `R < s`. -/
private theorem cutoff_smul_inverse_comp_eq_id (χ : FrequencyCutoff (CoordinateSpace n))
    {a : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W} {R s : ℝ}
    (hinv : ∀ x ξ, R ≤ ‖ξ‖ → (a (x, ξ)).IsInvertible) (hs : 0 < s) (hRs : R < s)
    {q : CoordinateSpace n × CoordinateSpace n} (hq : 2 * s ≤ ‖q.2‖) :
    (χ (s⁻¹ • q.2) • (a q).inverse) ∘L a q = .id ℂ V ∧
      a q ∘L (χ (s⁻¹ • q.2) • (a q).inverse) = .id ℂ W := by
  rw [χ.apply_inv_smul_eq_one hs hq, one_smul]
  exact ⟨(hinv q.1 q.2 (by linarith)).inverse_comp_self,
    (hinv q.1 q.2 (by linarith)).self_comp_inverse⟩

variable [CompleteSpace V]

/-- The product `χ(ξ / t) a(x, ξ)⁻¹` is smooth when `a(x, ξ)` is invertible at all frequencies
with `R ≤ ‖ξ‖`, for `R < t`: near smaller frequencies the cutoff vanishes. -/
private theorem contDiff_cutoff_smul_inverse (χ : FrequencyCutoff (CoordinateSpace n))
    {a : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W} (ha : ContDiff ℝ ∞ a) {R t : ℝ}
    (hinv : ∀ x ξ, R ≤ ‖ξ‖ → (a (x, ξ)).IsInvertible) (ht : 0 < t) (hRt : R < t) :
    ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n =>
      χ (t⁻¹ • p.2) • (a p).inverse := by
  refine contDiff_iff_contDiffAt.2 fun p => ?_
  rcases le_or_gt R ‖p.2‖ with hp | hp
  · have h1 : ContDiffAt ℝ ∞ (fun q => (a q).inverse) p :=
      (((hinv p.1 p.2 hp).contDiffAt_map_inverse (𝕜 := ℂ)).restrict_scalars ℝ).comp p
        ha.contDiffAt
    exact (((χ.contDiff (n := ⊤)).comp (contDiff_snd.const_smul t⁻¹)).contDiffAt).smul h1
  · refine (contDiffAt_const (c := (0 : W →L[ℂ] V))).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt continuous_snd.norm continuous_const).mem_nhds (hp.trans hRt)]
      with q hq
    rw [χ.apply_inv_smul_eq_zero ht hq.le, zero_smul]

/-- At the frequencies of norm greater than `2 s`, the frequency derivatives of the inverse
`G = χ(ξ / s) a⁻¹` are `∂_{ξ_j} G = -G (∂_{ξ_j} a) G`. -/
private theorem eventuallyEq_coordinateDeriv_snd_cutoff_smul_inverse
    (χ : FrequencyCutoff (CoordinateSpace n)) {a : Symbol n V W m} {R s : ℝ}
    (hinv : ∀ x ξ, R ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible) (hs : 0 < s) (hRs : R < s)
    (j : Fin n) {p : CoordinateSpace n × CoordinateSpace n} (hp : 2 * s < ‖p.2‖) :
    (fun q => coordinateDeriv [j]
        (fun η => χ (s⁻¹ • η) • (a.coefficient (q.1, η)).inverse) q.2) =ᶠ[𝓝 p]
      fun q => -((χ (s⁻¹ • q.2) • (a.coefficient q).inverse) ∘L
        ((Symbol.frequencyDeriv j a).coefficient q ∘L
          (χ (s⁻¹ • q.2) • (a.coefficient q).inverse))) := by
  have hGs := contDiff_cutoff_smul_inverse χ a.contDiff_coefficient hinv hs hRs
  filter_upwards [(isOpen_lt continuous_const continuous_snd.norm).mem_nhds hp] with ⟨x, ξ⟩ hq
  have hη : ∀ᶠ η in 𝓝 ξ, 2 * s < ‖η‖ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hq
  rw [Symbol.coefficient_frequencyDeriv]
  exact coordinateDeriv_eq_neg_comp_of_comp_eq_id
    (φ := fun η => χ (s⁻¹ • η) • (a.coefficient (x, η)).inverse)
    (ψ := fun η => a.coefficient (x, η))
    ((hGs.comp (contDiff_prodMk_right x)).differentiable (by simp) ξ)
    ((a.contDiff_coefficient.comp (contDiff_prodMk_right x)).differentiable (by simp) ξ)
    (hη.mono fun η hη => (cutoff_smul_inverse_comp_eq_id χ hinv hs hRs
      (q := (x, η)) hη.le).1)
    (cutoff_smul_inverse_comp_eq_id χ hinv hs hRs (q := (x, ξ)) hq.le).2 j

/-- At the frequencies of norm greater than `2 s`, the position derivatives of the inverse
`G = χ(ξ / s) a⁻¹` are `∂_{x_j} G = -G (∂_{x_j} a) G`. -/
private theorem eventuallyEq_coordinateDeriv_fst_cutoff_smul_inverse
    (χ : FrequencyCutoff (CoordinateSpace n)) {a : Symbol n V W m} {R s : ℝ}
    (hinv : ∀ x ξ, R ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible) (hs : 0 < s) (hRs : R < s)
    (j : Fin n) {p : CoordinateSpace n × CoordinateSpace n} (hp : 2 * s < ‖p.2‖) :
    (fun q => coordinateDeriv [j]
        (fun y => χ (s⁻¹ • q.2) • (a.coefficient (y, q.2)).inverse) q.1) =ᶠ[𝓝 p]
      fun q => -((χ (s⁻¹ • q.2) • (a.coefficient q).inverse) ∘L
        ((Symbol.spatialDeriv j a).coefficient q ∘L
          (χ (s⁻¹ • q.2) • (a.coefficient q).inverse))) := by
  have hGs := contDiff_cutoff_smul_inverse χ a.contDiff_coefficient hinv hs hRs
  filter_upwards [(isOpen_lt continuous_const continuous_snd.norm).mem_nhds hp] with ⟨x, ξ⟩ hq
  rw [Symbol.coefficient_spatialDeriv]
  exact coordinateDeriv_eq_neg_comp_of_comp_eq_id
    (φ := fun y => χ (s⁻¹ • ξ) • (a.coefficient (y, ξ)).inverse)
    (ψ := fun y => a.coefficient (y, ξ))
    ((hGs.comp (contDiff_prodMk_left ξ)).differentiable (by simp) x)
    ((a.contDiff_coefficient.comp (contDiff_prodMk_left ξ)).differentiable (by simp) x)
    (Eventually.of_forall fun y => (cutoff_smul_inverse_comp_eq_id χ hinv hs hRs
      (q := (y, ξ)) hq.le).1)
    (cutoff_smul_inverse_comp_eq_id χ hinv hs hRs (q := (x, ξ)) hq.le).2 j

/-- **The estimates of an inverse symbol.** Let `a` satisfy the symbol estimates of order `m` at
the positions in `K`, and let `a(x, ξ)` be invertible for `R ≤ ‖ξ‖` with
`‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)` for `x ∈ K`. For `R < s`, the smooth function `G = χ(ξ / s) a(x, ξ)⁻¹`,
which is `a⁻¹` for `‖ξ‖ ≥ 2 s`, satisfies the estimates of order `-m` there. By induction on the
length, using `∂G = -G (∂a) G` and the Leibniz rule. -/
private theorem estimatesUpTo_cutoff_smul_inverse (χ : FrequencyCutoff (CoordinateSpace n))
    {a : Symbol n V W m} {K : Set (CoordinateSpace n)} {R s : ℝ}
    (hA : ∀ α β : List (Fin n), ∃ C : ℝ, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2))
    (hinv : ∀ x ξ, R ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible)
    (hbound : ∃ C : ℝ, ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ →
      ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2))
    (hs : 0 < s) (hRs : R < s) (N : ℕ) :
    EstimatesUpTo K (2 * s) (-m) N fun p => χ (s⁻¹ • p.2) • (a.coefficient p).inverse := by
  have hGs := contDiff_cutoff_smul_inverse χ a.contDiff_coefficient hinv hs hRs
  -- The estimates of the first-order derivatives of `a`.
  have hAfreq : ∀ j : Fin n, ∀ N, EstimatesUpTo K (2 * s) (m - 1) N
      (Symbol.frequencyDeriv j a).coefficient := fun j N =>
    estimatesUpTo_of_forall fun α β => (hA α (β ++ [j])).imp fun C hC x hx ξ => by
      rw [Symbol.mixedDeriv_frequencyDeriv, Symbol.order_sub_one_sub_length]
      exact hC x hx ξ
  have hApos : ∀ j : Fin n, ∀ N, EstimatesUpTo K (2 * s) m N
      (Symbol.spatialDeriv j a).coefficient := fun j N =>
    estimatesUpTo_of_forall fun α β => (hA (α ++ [j]) β).imp fun C hC x hx ξ => by
      rw [Symbol.mixedDeriv_spatialDeriv]
      exact hC x hx ξ
  -- Length zero: the bound on the inverse.
  have h₀ : EstimatesUpTo K (2 * s) (-m) 0
      fun p => χ (s⁻¹ • p.2) • (a.coefficient p).inverse := by
    intro α β hαβ
    obtain ⟨C, hC⟩ := hbound
    obtain ⟨rfl, rfl⟩ : α = [] ∧ β = [] := by
      simpa only [Nat.le_zero, Nat.add_eq_zero_iff, List.length_eq_zero_iff] using hαβ
    refine ⟨C, fun x hx ξ hξ => ?_⟩
    rw [mixedDeriv_nil_nil, χ.apply_inv_smul_eq_one hs hξ.le, one_smul, List.length_nil,
      Nat.cast_zero, sub_zero]
    exact hC x hx ξ (by linarith)
  -- The products `G (∂a) G` with the first-order derivatives `∂a` of order `μ`.
  have hprod : ∀ {N : ℕ} {μ : ℝ} {b : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W},
      ContDiff ℝ ∞ b → EstimatesUpTo K (2 * s) μ N b →
      EstimatesUpTo K (2 * s) (-m) N (fun p => χ (s⁻¹ • p.2) • (a.coefficient p).inverse) →
      EstimatesUpTo K (2 * s) (-m + (μ + -m)) N fun q =>
        -((χ (s⁻¹ • q.2) • (a.coefficient q).inverse) ∘L
          (b q ∘L (χ (s⁻¹ • q.2) • (a.coefficient q).inverse))) := fun hb hbN hG =>
    (EstimatesUpTo.comp hGs (((ContinuousLinearMap.compL ℂ W V W).bilinearRestrictScalars
      ℝ).isBoundedBilinearMap.contDiff.comp (hb.prodMk hGs)) rfl hG
      (EstimatesUpTo.comp hb hGs rfl hbN hG)).neg
  induction N with
  | zero => exact h₀
  | succ N ih =>
    refine estimatesUpTo_succ hGs h₀ (fun j => ?_) (fun j => ?_)
    · refine EstimatesUpTo.congr ?_ fun p hp =>
        eventuallyEq_coordinateDeriv_snd_cutoff_smul_inverse χ hinv hs hRs j hp
      convert hprod (Symbol.frequencyDeriv j a).contDiff_coefficient (hAfreq j N) ih using 1
      ring
    · refine EstimatesUpTo.congr ?_ fun p hp =>
        eventuallyEq_coordinateDeriv_fst_cutoff_smul_inverse χ hinv hs hRs j hp
      convert hprod (Symbol.spatialDeriv j a).contDiff_coefficient (hApos j N) ih using 1
      ring

/-- The estimates of the cut-off inverse `χ(ξ / t) a(x, ξ)⁻¹`, for `t ≥ 1` and `2 R < t`, at the
positions in `K`: it vanishes for `‖ξ‖ < t`, and for `‖ξ‖ ≥ t` it is the product of the
dilated cutoff with the function of `estimatesUpTo_cutoff_smul_inverse` for a radius `s` with
`R < s` and `2 s < t`. -/
private theorem exists_bound_cutoff_smul_inverse (χ : FrequencyCutoff (CoordinateSpace n))
    {a : Symbol n V W m} {K : Set (CoordinateSpace n)} {R t : ℝ}
    (hA : ∀ α β : List (Fin n), ∃ C : ℝ, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2))
    (hinv : ∀ x ξ, R ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible)
    (hbound : ∃ C : ℝ, ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ →
      ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2))
    (ht : 1 ≤ t) (hRt : 2 * R < t) (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • (a.coefficient p).inverse) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((-m - β.length) / 2) := by
  set s := (max R 0 + t / 2) / 2 with hs_def
  have hR0 := le_max_left R 0
  have h00 := le_max_right R 0
  have hmax : max R 0 < t / 2 := max_lt (by linarith) (by linarith)
  have hs : 0 < s := by linarith
  have hRs : R < s := by linarith
  have hst : 2 * s < t := by linarith
  set G : CoordinateSpace n × CoordinateSpace n → W →L[ℂ] V :=
    fun p => χ (s⁻¹ • p.2) • (a.coefficient p).inverse with hG
  have hGs : ContDiff ℝ ∞ G := contDiff_cutoff_smul_inverse χ a.contDiff_coefficient hinv hs hRs
  have hχs : ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n => χ (t⁻¹ • p.2) :=
    (χ.contDiff (n := ⊤)).comp (contDiff_snd.const_smul t⁻¹)
  -- Where the dilated cutoff `χ(ξ / t)` is nonzero, `G` is the inverse of `a`.
  have heq : (fun p : CoordinateSpace n × CoordinateSpace n =>
      χ (t⁻¹ • p.2) • (a.coefficient p).inverse) =
      fun p => ContinuousLinearMap.lsmul ℝ ℝ (χ (t⁻¹ • p.2)) (G p) := by
    funext p
    rw [ContinuousLinearMap.lsmul_apply]
    rcases le_or_gt ‖p.2‖ t with hp | hp
    · rw [χ.apply_inv_smul_eq_zero (by linarith) hp, zero_smul, zero_smul]
    · simp only [G, χ.apply_inv_smul_eq_one hs (by linarith : 2 * s ≤ ‖p.2‖), one_smul]
  have hprod := EstimatesUpTo.bilinear (ContinuousLinearMap.lsmul ℝ ℝ) hχs hGs (zero_add _)
    (estimatesUpTo_cutoff (K := K) (ρ := 2 * s) (N := α.length + β.length) χ ht)
    (estimatesUpTo_cutoff_smul_inverse χ hA hinv hbound hs hRs _)
  obtain ⟨C, hC⟩ := hprod α β le_rfl
  refine ⟨max C 0, le_max_right _ _, fun x hx ξ => ?_⟩
  rcases lt_or_ge ‖ξ‖ t with hξ | hξ
  · -- Below radius `t` the cut-off inverse vanishes near `(x, ξ)`.
    have hzero : (fun p : CoordinateSpace n × CoordinateSpace n =>
        χ (t⁻¹ • p.2) • (a.coefficient p).inverse) =ᶠ[𝓝 (x, ξ)] 0 := by
      filter_upwards [(isOpen_lt continuous_snd.norm continuous_const).mem_nhds
        (show ‖(x, ξ).2‖ < t from hξ)] with q hq
      rw [χ.apply_inv_smul_eq_zero (by linarith) hq.le, zero_smul, Pi.zero_apply]
    rw [hzero.mixedDeriv_eq, mixedDeriv_zero, norm_zero]
    positivity
  · rw [heq]
    exact (hC x hx ξ (by linarith)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

end Inverse

namespace Symbol

variable {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U] {m m' R R' : ℝ}

/-! ### Elliptic symbols -/

/-- A symbol `a` of order `m` is *elliptic above the radius `R`* if at every frequency `ξ` with
`R ≤ ‖ξ‖` its value `a(x, ξ)` is an invertible continuous linear map, with
`‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)` for all positions `x` in each compact set, where
`⟨ξ⟩ = (1 + ‖ξ‖²)^(1/2)`. -/
def IsEllipticAbove (a : Symbol n V W m) (R : ℝ) : Prop :=
  ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ →
    (a.coefficient (x, ξ)).IsInvertible ∧
      ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)

/-- A symbol `a` of order `m` is *uniformly elliptic above the radius `R`* if at every frequency
`ξ` with `R ≤ ‖ξ‖` its value `a(x, ξ)` is an invertible continuous linear map, with
`‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)` for one constant `C` and all positions `x`. -/
def IsUniformlyEllipticAbove (a : Symbol n V W m) (R : ℝ) : Prop :=
  ∃ C : ℝ, ∀ x ξ, R ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible ∧
    ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)

theorem isEllipticAbove_iff {a : Symbol n V W m} :
    a.IsEllipticAbove R ↔ ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ ξ,
      R ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible ∧
        ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2) :=
  Iff.rfl

theorem isUniformlyEllipticAbove_iff {a : Symbol n V W m} :
    a.IsUniformlyEllipticAbove R ↔ ∃ C : ℝ, ∀ x ξ, R ≤ ‖ξ‖ →
      (a.coefficient (x, ξ)).IsInvertible ∧
        ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2) :=
  Iff.rfl

/-- The value of a symbol elliptic above `R` is invertible at every frequency of norm at least
`R`. -/
theorem IsEllipticAbove.isInvertible {a : Symbol n V W m} (ha : a.IsEllipticAbove R)
    (x : CoordinateSpace n) {ξ : CoordinateSpace n} (hξ : R ≤ ‖ξ‖) :
    (a.coefficient (x, ξ)).IsInvertible := by
  obtain ⟨C, hC⟩ := ha {x} isCompact_singleton
  exact (hC x rfl ξ hξ).1

/-- Ellipticity above a radius implies ellipticity above every larger radius. -/
theorem IsEllipticAbove.mono {a : Symbol n V W m} (ha : a.IsEllipticAbove R) (h : R ≤ R') :
    a.IsEllipticAbove R' :=
  fun K hK => (ha K hK).imp fun _ hC x hx ξ hξ => hC x hx ξ (h.trans hξ)

/-- Uniform ellipticity above a radius implies uniform ellipticity above every larger radius. -/
theorem IsUniformlyEllipticAbove.mono {a : Symbol n V W m} (ha : a.IsUniformlyEllipticAbove R)
    (h : R ≤ R') : a.IsUniformlyEllipticAbove R' :=
  ha.imp fun _ hC x ξ hξ => hC x ξ (h.trans hξ)

/-- A uniformly elliptic symbol is elliptic. -/
theorem IsUniformlyEllipticAbove.isEllipticAbove {a : Symbol n V W m}
    (ha : a.IsUniformlyEllipticAbove R) : a.IsEllipticAbove R :=
  fun _ _ => ha.imp fun _ hC x _ ξ hξ => hC x ξ hξ

/-- An invertible constant symbol is uniformly elliptic above every radius. -/
theorem isUniformlyEllipticAbove_const {T : V →L[ℂ] W} (hT : T.IsInvertible) (R : ℝ) :
    (const T : Symbol n V W 0).IsUniformlyEllipticAbove R :=
  ⟨‖T.inverse‖, fun x ξ _ => ⟨by rw [coefficient_const]; exact hT, by simp⟩⟩

/-- The pointwise estimate behind the products of elliptic symbols: if `b(x, ξ)` and `a(x, ξ)` are
invertible with inverses bounded by `C ⟨ξ⟩^(-m')` and `D ⟨ξ⟩^(-m)`, then `b(x, ξ) ∘ a(x, ξ)` is
invertible with inverse bounded by `D C ⟨ξ⟩^(-(m' + m))`. -/
private theorem isInvertible_comp_and_norm_inverse_le {b : W →L[ℂ] U} {a : V →L[ℂ] W}
    {C D : ℝ} {ξ : CoordinateSpace n}
    (hb : b.IsInvertible ∧ ‖b.inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m' / 2))
    (ha : a.IsInvertible ∧ ‖a.inverse‖ ≤ D * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)) :
    (b ∘L a).IsInvertible ∧
      ‖(b ∘L a).inverse‖ ≤ D * C * (1 + ‖ξ‖ ^ 2) ^ (-(m' + m) / 2) := by
  refine ⟨hb.1.comp ha.1, ?_⟩
  rw [hb.1.inverse_comp_of_left]
  calc ‖a.inverse ∘L b.inverse‖ ≤ ‖a.inverse‖ * ‖b.inverse‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (D * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)) * (C * (1 + ‖ξ‖ ^ 2) ^ (-m' / 2)) :=
        mul_le_mul ha.2 hb.2 (norm_nonneg _) ((norm_nonneg _).trans ha.2)
    _ = D * C * (1 + ‖ξ‖ ^ 2) ^ (-(m' + m) / 2) := by
        rw [show -(m' + m) / 2 = -m / 2 + -m' / 2 by ring, Real.rpow_add (by positivity)]
        ring

/-- The pointwise composition of elliptic symbols is elliptic. -/
theorem IsEllipticAbove.comp {b : Symbol n W U m'} {a : Symbol n V W m}
    (hb : b.IsEllipticAbove R') (ha : a.IsEllipticAbove R) :
    (b.comp a).IsEllipticAbove (max R' R) := by
  intro K hK
  obtain ⟨C, hC⟩ := hb K hK
  obtain ⟨D, hD⟩ := ha K hK
  refine ⟨D * C, fun x hx ξ hξ => ?_⟩
  rw [coefficient_comp]
  exact isInvertible_comp_and_norm_inverse_le (hC x hx ξ ((le_max_left _ _).trans hξ))
    (hD x hx ξ ((le_max_right _ _).trans hξ))

/-- The pointwise composition of uniformly elliptic symbols is uniformly elliptic. -/
theorem IsUniformlyEllipticAbove.comp {b : Symbol n W U m'} {a : Symbol n V W m}
    (hb : b.IsUniformlyEllipticAbove R') (ha : a.IsUniformlyEllipticAbove R) :
    (b.comp a).IsUniformlyEllipticAbove (max R' R) := by
  obtain ⟨C, hC⟩ := hb
  obtain ⟨D, hD⟩ := ha
  refine ⟨D * C, fun x ξ hξ => ?_⟩
  rw [coefficient_comp]
  exact isInvertible_comp_and_norm_inverse_le (hC x ξ ((le_max_left _ _).trans hξ))
    (hD x ξ ((le_max_right _ _).trans hξ))

/-! ### The inverse symbol -/

section CutoffInverse

variable [CompleteSpace V] (χ : FrequencyCutoff (CoordinateSpace n)) (a : Symbol n V W m)
  (ha : a.IsEllipticAbove R) {t : ℝ} (ht : 1 ≤ t) (hRt : 2 * R < t)

/-- The **inverse symbol** of a symbol `a` of order `m` that is elliptic above the radius `R`: for
a frequency cutoff `χ` and a radius `t ≥ 1` with `2 R < t`, the symbol
`(x, ξ) ↦ χ(ξ / t) a(x, ξ)⁻¹` of order `-m`. It vanishes for `‖ξ‖ ≤ t`
(`Symbol.coefficient_cutoffInverse_of_norm_le`) and is the inverse of `a(x, ξ)` for
`‖ξ‖ ≥ 2 t` (`Symbol.coefficient_cutoffInverse_of_two_mul_le_norm`). -/
def cutoffInverse : Symbol n W V (-m) where
  coefficient p := χ (t⁻¹ • p.2) • (a.coefficient p).inverse
  contDiff_coefficient := contDiff_cutoff_smul_inverse χ a.contDiff_coefficient
    (fun x _ hξ => ha.isInvertible x hξ) (by linarith) (by linarith)
  exists_bound K hK α β := exists_bound_cutoff_smul_inverse χ
    (fun α β => (a.exists_bound K hK α β).imp fun _ hC => hC.2)
    (fun x _ hξ => ha.isInvertible x hξ) ((ha K hK).imp fun _ hC x hx ξ hξ => (hC x hx ξ hξ).2)
    ht hRt α β

@[simp]
theorem coefficient_cutoffInverse (p : CoordinateSpace n × CoordinateSpace n) :
    (cutoffInverse χ a ha ht hRt).coefficient p = χ (t⁻¹ • p.2) • (a.coefficient p).inverse :=
  (rfl)

/-- The inverse symbol vanishes at the frequencies of norm at most `t`. -/
theorem coefficient_cutoffInverse_of_norm_le (x : CoordinateSpace n) {ξ : CoordinateSpace n}
    (hξ : ‖ξ‖ ≤ t) : (cutoffInverse χ a ha ht hRt).coefficient (x, ξ) = 0 := by
  rw [coefficient_cutoffInverse, χ.apply_inv_smul_eq_zero (by linarith) hξ, zero_smul]

/-- At the frequencies of norm at least `2 t`, the inverse symbol is the inverse of `a`. -/
theorem coefficient_cutoffInverse_of_two_mul_le_norm (x : CoordinateSpace n)
    {ξ : CoordinateSpace n} (hξ : 2 * t ≤ ‖ξ‖) :
    (cutoffInverse χ a ha ht hRt).coefficient (x, ξ) = (a.coefficient (x, ξ)).inverse := by
  rw [coefficient_cutoffInverse, χ.apply_inv_smul_eq_one (by linarith) hξ, one_smul]

/-- At the frequencies of norm at least `2 t`, the inverse symbol is a left inverse of `a`. -/
theorem coefficient_cutoffInverse_comp_coefficient (x : CoordinateSpace n)
    {ξ : CoordinateSpace n} (hξ : 2 * t ≤ ‖ξ‖) :
    (cutoffInverse χ a ha ht hRt).coefficient (x, ξ) ∘L a.coefficient (x, ξ) = .id ℂ V := by
  rw [coefficient_cutoffInverse_of_two_mul_le_norm χ a ha ht hRt x hξ]
  exact (ha.isInvertible x (by linarith)).inverse_comp_self

/-- At the frequencies of norm at least `2 t`, the inverse symbol is a right inverse of `a`. -/
theorem coefficient_comp_coefficient_cutoffInverse (x : CoordinateSpace n)
    {ξ : CoordinateSpace n} (hξ : 2 * t ≤ ‖ξ‖) :
    a.coefficient (x, ξ) ∘L (cutoffInverse χ a ha ht hRt).coefficient (x, ξ) = .id ℂ W := by
  rw [coefficient_cutoffInverse_of_two_mul_le_norm χ a ha ht hRt x hξ]
  exact (ha.isInvertible x (by linarith)).self_comp_inverse

/-- **The inverse symbol is a pointwise left inverse modulo smoothing symbols**: the pointwise
product `χ(ξ / t) a⁻¹ ∘ a` is the identity up to a smoothing symbol. For symbols depending on the
position this is not the symbol of the composed operators; the inverse symbol is only the leading
term of a parametrix. -/
theorem isSmoothing_cutoffInverse_comp_sub :
    ((cutoffInverse χ a ha ht hRt).comp a -
      inclusion (neg_add_cancel m).ge (const (.id ℂ V))).IsSmoothing :=
  isSmoothing_of_coefficient_eq_zero (2 * t) fun x ξ hξ => by
    simp only [coefficient_sub, Pi.sub_apply, coefficient_comp, coefficient_inclusion,
      coefficient_const]
    rw [coefficient_cutoffInverse_comp_coefficient χ a ha ht hRt x hξ, sub_self]

/-- **The inverse symbol is a pointwise right inverse modulo smoothing symbols**: the pointwise
product `a ∘ χ(ξ / t) a⁻¹` is the identity up to a smoothing symbol. -/
theorem isSmoothing_comp_cutoffInverse_sub :
    (a.comp (cutoffInverse χ a ha ht hRt) -
      inclusion (add_neg_cancel m).ge (const (.id ℂ W))).IsSmoothing :=
  isSmoothing_of_coefficient_eq_zero (2 * t) fun x ξ hξ => by
    simp only [coefficient_sub, Pi.sub_apply, coefficient_comp, coefficient_inclusion,
      coefficient_const]
    rw [coefficient_comp_coefficient_cutoffInverse χ a ha ht hRt x hξ, sub_self]

/-- **Independence of the choices.** Changing the frequency cutoff and the radius changes the
inverse symbol by a smoothing symbol. -/
theorem isSmoothing_cutoffInverse_sub_cutoffInverse (χ' : FrequencyCutoff (CoordinateSpace n))
    (ha' : a.IsEllipticAbove R') {t' : ℝ} (ht' : 1 ≤ t') (hRt' : 2 * R' < t') :
    (cutoffInverse χ a ha ht hRt - cutoffInverse χ' a ha' ht' hRt').IsSmoothing :=
  isSmoothing_of_coefficient_eq_zero (2 * max t t') fun x ξ hξ => by
    rw [coefficient_sub, Pi.sub_apply,
      coefficient_cutoffInverse_of_two_mul_le_norm χ a ha ht hRt x
        ((mul_le_mul_of_nonneg_left (le_max_left t t') zero_le_two).trans hξ),
      coefficient_cutoffInverse_of_two_mul_le_norm χ' a ha' ht' hRt' x
        ((mul_le_mul_of_nonneg_left (le_max_right t t') zero_le_two).trans hξ), sub_self]

/-- The inverse symbol of a uniform symbol that is uniformly elliptic is uniform. -/
theorem isUniform_cutoffInverse (hau : a.IsUniform) (hu : a.IsUniformlyEllipticAbove R) :
    (cutoffInverse χ a ha ht hRt).IsUniform := by
  refine isUniform_iff.2 fun α β => ?_
  obtain ⟨C, hC, hCb⟩ := exists_bound_cutoff_smul_inverse (K := univ) χ
    (fun α β => (isUniform_iff.1 hau α β).imp fun _ hC x _ ξ => hC.2 x ξ)
    (fun x _ hξ => ha.isInvertible x hξ) (hu.imp fun _ hC x _ ξ hξ => (hC x ξ hξ).2)
    ht hRt α β
  exact ⟨C, hC, fun x ξ => hCb x (mem_univ x) ξ⟩

end CutoffInverse

/-! ### Characterizations -/

/-- A symbol of order `m` that a symbol of order `-m` inverts at all frequencies of norm at least
`R` is elliptic above `R`. -/
theorem isEllipticAbove_of_comp_eq_id {a : Symbol n V W m} {b : Symbol n W V (-m)}
    (h : ∀ x ξ, R ≤ ‖ξ‖ → b.coefficient (x, ξ) ∘L a.coefficient (x, ξ) = .id ℂ V ∧
      a.coefficient (x, ξ) ∘L b.coefficient (x, ξ) = .id ℂ W) :
    a.IsEllipticAbove R := by
  refine fun K hK => (b.exists_norm_coefficient_le K hK).imp fun C hC x hx ξ hξ => ?_
  obtain ⟨h₁, h₂⟩ := h x ξ hξ
  refine ⟨.of_inverse h₂ h₁, ?_⟩
  rw [ContinuousLinearMap.inverse_eq h₂ h₁]
  exact hC x hx ξ

/-- A symbol of order `m` that a uniform symbol of order `-m` inverts at all frequencies of norm
at least `R` is uniformly elliptic above `R`. -/
theorem isUniformlyEllipticAbove_of_comp_eq_id {a : Symbol n V W m} {b : Symbol n W V (-m)}
    (hb : b.IsUniform)
    (h : ∀ x ξ, R ≤ ‖ξ‖ → b.coefficient (x, ξ) ∘L a.coefficient (x, ξ) = .id ℂ V ∧
      a.coefficient (x, ξ) ∘L b.coefficient (x, ξ) = .id ℂ W) :
    a.IsUniformlyEllipticAbove R := by
  obtain ⟨C, -, hC⟩ := isUniform_iff.1 hb [] []
  refine ⟨C, fun x ξ hξ => ?_⟩
  obtain ⟨h₁, h₂⟩ := h x ξ hξ
  refine ⟨.of_inverse h₂ h₁, ?_⟩
  rw [ContinuousLinearMap.inverse_eq h₂ h₁]
  simpa using hC x ξ

/-- A symbol of order `m` is elliptic above some radius exactly when a symbol of order `-m`
inverts it at all large frequencies. -/
theorem exists_isEllipticAbove_iff [CompleteSpace V] {a : Symbol n V W m} :
    (∃ R, a.IsEllipticAbove R) ↔ ∃ b : Symbol n W V (-m), ∃ R, ∀ x ξ, R ≤ ‖ξ‖ →
      b.coefficient (x, ξ) ∘L a.coefficient (x, ξ) = .id ℂ V ∧
        a.coefficient (x, ξ) ∘L b.coefficient (x, ξ) = .id ℂ W := by
  refine ⟨fun ⟨R, ha⟩ => ?_, fun ⟨_, R, h⟩ => ⟨R, isEllipticAbove_of_comp_eq_id h⟩⟩
  have ht : 1 ≤ max 1 (2 * R + 1) := le_max_left _ _
  have hRt : 2 * R < max 1 (2 * R + 1) := (lt_add_one _).trans_le (le_max_right _ _)
  exact ⟨cutoffInverse default a ha ht hRt, 2 * max 1 (2 * R + 1), fun x ξ hξ =>
    ⟨coefficient_cutoffInverse_comp_coefficient default a ha ht hRt x hξ,
      coefficient_comp_coefficient_cutoffInverse default a ha ht hRt x hξ⟩⟩

/-- A uniform symbol of order `m` is uniformly elliptic above some radius exactly when a uniform
symbol of order `-m` inverts it at all large frequencies. -/
theorem exists_isUniformlyEllipticAbove_iff [CompleteSpace V] {a : Symbol n V W m}
    (hau : a.IsUniform) :
    (∃ R, a.IsUniformlyEllipticAbove R) ↔ ∃ b : Symbol n W V (-m), b.IsUniform ∧ ∃ R, ∀ x ξ,
      R ≤ ‖ξ‖ → b.coefficient (x, ξ) ∘L a.coefficient (x, ξ) = .id ℂ V ∧
        a.coefficient (x, ξ) ∘L b.coefficient (x, ξ) = .id ℂ W := by
  refine ⟨fun ⟨R, hu⟩ => ?_, fun ⟨_, hb, R, h⟩ => ⟨R, isUniformlyEllipticAbove_of_comp_eq_id hb h⟩⟩
  have ha := hu.isEllipticAbove
  have ht : 1 ≤ max 1 (2 * R + 1) := le_max_left _ _
  have hRt : 2 * R < max 1 (2 * R + 1) := (lt_add_one _).trans_le (le_max_right _ _)
  exact ⟨cutoffInverse default a ha ht hRt, isUniform_cutoffInverse default a ha ht hRt hau hu,
    2 * max 1 (2 * R + 1), fun x ξ hξ =>
      ⟨coefficient_cutoffInverse_comp_coefficient default a ha ht hRt x hξ,
        coefficient_comp_coefficient_cutoffInverse default a ha ht hRt x hξ⟩⟩

/-- The Bessel weight `⟨ξ / 2π⟩^s` is uniformly elliptic of order `s` above every radius: its
inverse is the Bessel weight of order `-s`. -/
theorem isUniformlyEllipticAbove_besselPotential (s R : ℝ) :
    (besselPotential s : Symbol n V V s).IsUniformlyEllipticAbove R := by
  refine isUniformlyEllipticAbove_of_comp_eq_id (isUniform_besselPotential (-s)) fun x ξ _ => ?_
  have hw : (0 : ℝ) < 1 + ‖(2 * Real.pi)⁻¹ • ξ‖ ^ 2 := by positivity
  have h₁ : (1 + ‖(2 * Real.pi)⁻¹ • ξ‖ ^ 2) ^ (-s / 2) * (1 + ‖(2 * Real.pi)⁻¹ • ξ‖ ^ 2) ^ (s / 2) =
      1 := by
    rw [← Real.rpow_add hw, neg_div, neg_add_cancel, Real.rpow_zero]
  have h₂ : (1 + ‖(2 * Real.pi)⁻¹ • ξ‖ ^ 2) ^ (s / 2) * (1 + ‖(2 * Real.pi)⁻¹ • ξ‖ ^ 2) ^ (-s / 2) =
      1 := by
    rw [mul_comm, h₁]
  simp only [coefficient_besselPotential, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.comp_id, smul_smul, ← Complex.ofReal_mul,
    h₁, h₂, Complex.ofReal_one, one_smul, and_self]

end Symbol

end TauCeti
