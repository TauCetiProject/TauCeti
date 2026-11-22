/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Microlocality
public import TauCeti.Analysis.Pseudodifferential.Symbol.Elliptic
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Pseudodifferential.Composition.Parametrix
import TauCeti.Analysis.Pseudodifferential.MicrolocalCutoff
import TauCeti.Analysis.Pseudodifferential.Symbol.Map

/-!
# The characteristic set and microlocal elliptic regularity

A point `(x₀, ξ₀)` with `ξ₀ ≠ 0` is *noncharacteristic* for a symbol `a` of order `m` if `a` is
elliptic in a conic neighbourhood of it at large frequencies: for a neighbourhood `U` of `x₀`, an
open cone `Γ` containing `ξ₀` and a radius `R`, the value `a(x, ξ)` is invertible with
`‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)` whenever `x ∈ U`, `ξ ∈ Γ` and `‖ξ‖ ≥ R`, with `C` uniform for `x` in
compact sets (`TauCeti.Symbol.IsEllipticOn`). The other points `(x₀, ξ₀)` with `ξ₀ ≠ 0` form the
**characteristic set** `Char(a)` (`TauCeti.Symbol.characteristicSet`). It is conic, and empty for a
symbol elliptic above some radius.

This file proves **microlocal elliptic regularity** for a scalar symbol `a` with compact spatial
support acting on a Bessel-potential space `H^t`: the operator `Op(a)` recovers every singularity of
`v ∈ H^t` away from its characteristic set,

`WF(v) ⊆ WF(Op(a) v) ∪ Char(a)`

(`TauCeti.Symbol.waveFrontSet_toDistribution_subset_quantizeSobolev_union_characteristicSet`).
Together with the microlocality `WF(Op(a) v) ⊆ WF(v)`
(`TauCeti.Symbol.waveFrontSet_toDistribution_quantizeSobolev_subset`), the two wave front sets agree
off `Char(a)`, and the singular supports agree over the points above which `a` has no
characteristic covector.

## Proof

Let `a` be elliptic on the points `(x, ξ)` with `x ∈ U`, `ξ ∈ Γ` and `‖ξ‖ ≥ R`, and let
`(x₀, ξ₀) ∈ U × Γ`. A microlocal cutoff, multiplied by the dilated frequency cutoff `χ(ξ / t)`,
gives a symbol `c` of order `0` with compact spatial support which vanishes outside that set and is
the identity at large frequencies over a neighbourhood `U'` of `x₀` and an open cone `Γ'` containing
`ξ₀` (`TauCeti.Symbol.exists_microlocalCutoff_of_mem`). A microlocal left parametrix symbol `b` of
order `-m` has `c ∼ ∑ₖ sharpTerm b a k`
(`TauCeti.Symbol.IsEllipticOn.exists_isAsymptoticSum_sharpTerm_left`). Since `b # a` is an
asymptotic sum of the same terms, `b # a - c` is smoothing; multiplying `b` by a cutoff `ψ(x)` equal
to `1` where `c` lives gives a symbol `q` with compact spatial support and

`Op(c) v = Op(q) (Op(a) v) - Op(e) v`, `e` smoothing
(`TauCeti.Symbol.exists_toDistr_quantizeSobolev_eq_sub`).

Now `Op(c)` is microlocally the identity on `U' × Γ'`
(`TauCeti.Symbol.waveFrontSet_toDistribution_inter_subset_quantizeSobolev`), `Op(q)` does not
enlarge wave front sets, and `Op(e) v` lies in every `H^s`, so its wave front set is empty.

## Main results

* `TauCeti.Symbol.characteristicSet`: the characteristic set of a symbol.
* `TauCeti.Symbol.exists_toDistr_quantizeSobolev_eq_sub`: the microlocal parametrix identity
  `Op(c) v = Op(q) (Op(a) v) - Op(e) v` on `H^t`, with `e` smoothing.
* `TauCeti.Symbol.waveFrontSet_toDistribution_inter_subset_quantizeSobolev_of_isEllipticOn`:
  if `a` is elliptic on `U × Γ` at large frequencies, then `WF(v) ∩ (U × Γ) ⊆ WF(Op(a) v)`.
* `TauCeti.Symbol.waveFrontSet_toDistribution_subset_quantizeSobolev_union_characteristicSet`:
  **microlocal elliptic regularity**, `WF(v) ⊆ WF(Op(a) v) ∪ Char(a)`.
* `TauCeti.Symbol.waveFrontSet_toDistribution_quantizeSobolev_sdiff_characteristicSet_eq`:
  `WF(Op(a) v) \ Char(a) = WF(v) \ Char(a)`.
* `TauCeti.Symbol.singularSupport_toDistribution_subset_singularSupport_quantizeSobolev_union`:
  the singular support of `v` lies in that of `Op(a) v` together with the positions of `Char(a)`.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §7
  (microlocal parametrices and `WF(u) ⊆ WF(Pu) ∪ Char(P)`).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  §18.1, Theorem 18.1.28.
-/

public section

noncomputable section

open Filter Metric Set TemperedDistribution Distribution
open scoped BesselPotentialSpace Topology ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-! ### The characteristic set -/

section CharacteristicSet

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

/-- The **characteristic set** `Char(a)` of a symbol `a` of order `m`: the points `(x, ξ)` with
`ξ ≠ 0` such that `a` is not elliptic (`TauCeti.Symbol.IsEllipticOn`) on the points `(y, η)` with
`y ∈ U`, `η ∈ Γ` and `‖η‖ ≥ R` for any neighbourhood `U` of `x`, open cone `Γ` containing `ξ` and
radius `R`. -/
def characteristicSet (a : Symbol n V W m) : Set (CoordinateSpace n × CoordinateSpace n) :=
  {p | p.2 ≠ 0 ∧ ¬ ∃ U ∈ 𝓝 p.1, ∃ Γ : Set (CoordinateSpace n), IsOpen Γ ∧ p.2 ∈ Γ ∧
    (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∃ R : ℝ, a.IsEllipticOn {q | q.1 ∈ U ∧ q.2 ∈ Γ ∧ R ≤ ‖q.2‖}}

theorem mem_characteristicSet_iff {a : Symbol n V W m} {x ξ : CoordinateSpace n} :
    (x, ξ) ∈ a.characteristicSet ↔ ξ ≠ 0 ∧ ¬ ∃ U ∈ 𝓝 x, ∃ Γ : Set (CoordinateSpace n),
      IsOpen Γ ∧ ξ ∈ Γ ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
        ∃ R : ℝ, a.IsEllipticOn {q | q.1 ∈ U ∧ q.2 ∈ Γ ∧ R ≤ ‖q.2‖} :=
  Iff.rfl

/-- The characteristic set is conic: it depends on the frequency only through its ray. -/
theorem smul_mem_characteristicSet_iff {a : Symbol n V W m} {x ξ : CoordinateSpace n} {t : ℝ}
    (ht : 0 < t) : (x, t • ξ) ∈ a.characteristicSet ↔ (x, ξ) ∈ a.characteristicSet := by
  have key {Γ : Set (CoordinateSpace n)} (hΓ : ∀ s : ℝ, 0 < s → ∀ η ∈ Γ, s • η ∈ Γ) :
      t • ξ ∈ Γ ↔ ξ ∈ Γ :=
    ⟨fun h ↦ by simpa [smul_smul, ht.ne'] using hΓ t⁻¹ (inv_pos.2 ht) _ h, hΓ t ht ξ⟩
  refine and_congr (by simp [ht.ne']) (not_congr (exists_congr fun U ↦
    and_congr_right fun _ ↦ exists_congr fun Γ ↦ ?_))
  exact ⟨fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨h₁, (key h₃).1 h₂, h₃, h₄⟩,
    fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨h₁, (key h₃).2 h₂, h₃, h₄⟩⟩

/-- A symbol elliptic above some radius has no characteristic points. -/
theorem IsEllipticAbove.characteristicSet_eq_empty {a : Symbol n V W m} {R : ℝ}
    (ha : a.IsEllipticAbove R) : a.characteristicSet = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ hp ↦ hp.2 ⟨univ, univ_mem, univ, isOpen_univ, mem_univ _,
    fun _ _ _ _ ↦ mem_univ _, R, (isEllipticAbove_iff_isEllipticOn.1 ha).mono fun _ hq ↦ hq.2.2⟩

end CharacteristicSet

/-! ### Microlocal elliptic regularity -/

section EllipticRegularity

/-- **The microlocal parametrix identity on Sobolev spaces.** Let `a` have compact spatial support
and be elliptic on a set `S`, and let `c` of order `0` have compact spatial support and vanish
outside `S`. Then there are a symbol `q` of order `-m` and a smoothing symbol `e`, both with compact
spatial support, such that `Op(c) v = Op(q) (Op(a) v) - Op(e) v` for every `v ∈ H^t`. -/
theorem exists_toDistr_quantizeSobolev_eq_sub {a : Symbol n ℂ ℂ m}
    (ha : a.HasCompactSpatialSupport) {S : Set (CoordinateSpace n × CoordinateSpace n)}
    (hell : a.IsEllipticOn S) {c : Symbol n ℂ ℂ 0} (hc : c.HasCompactSpatialSupport)
    (hcS : ∀ p ∉ S, c.coefficient p = 0) :
    ∃ (q : Symbol n ℂ ℂ (-m)) (hq : q.HasCompactSpatialSupport) (e : Symbol n ℂ ℂ (-m + m))
      (he : e.HasCompactSpatialSupport), e.IsSmoothing ∧
      ∀ (t : ℝ) (v : H^{t}(CoordinateSpace n, ℂ)), (c.quantizeSobolev hc t v).toDistr =
        (q.quantizeSobolev hq (t - m) (a.quantizeSobolev ha t v)).toDistr -
          (e.quantizeSobolev he t v).toDistr := by
  obtain ⟨b, hb⟩ := hell.exists_isAsymptoticSum_sharpTerm_left hcS
  -- `b # a` and `c` are asymptotic sums of the same terms, so `b # a - c` is smoothing.
  have hm' : Tendsto (fun k : ℕ ↦ -m + m - k) atTop atBot :=
    tendsto_atBot_add_const_left atTop _ <|
      tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  have hsm : (b.sharp a ha - inclusion (neg_add_cancel m).ge c).IsSmoothing :=
    ((isAsymptoticSum_sharp ha).isAsymptoticSum_inclusion_iff_isSmoothing_sub hm' (by simp)
      (by simp) (neg_add_cancel m).ge).1 hb
  -- A cutoff `ψ` equal to `1` on the spatial support `K` of `c`, and `q = ψ b`.
  obtain ⟨K, hK, hKc⟩ := hasCompactSpatialSupport_iff.1 hc
  obtain ⟨φ, hφ, -, hφ1, hφc, -⟩ := hK.exists_contDiff_cutoff_eventuallyEq_one isOpen_univ
    (subset_univ K)
  have hψ : ContDiff ℝ ∞ fun x ↦ (φ x : ℂ) := Complex.ofRealCLM.contDiff.comp hφ
  have hq := hasCompactSpatialSupport_smulLeft hψ (hφc.comp_left Complex.ofReal_zero) b
  have hcψ (x ξ : CoordinateSpace n) : (φ x : ℂ) • c.coefficient (x, ξ) = c.coefficient (x, ξ) := by
    by_cases hx : x ∈ K
    · simp [(hφ1 x hx).self_of_nhds]
    · simp [hKc x hx ξ]
  -- `q # a - c = ψ (b # a - c)` is smoothing.
  have he : (((smulLeft hψ b).sharp a ha) - inclusion (neg_add_cancel m).ge c).IsSmoothing := by
    convert hsm.smulLeft hψ using 1
    refine Symbol.ext (funext fun ⟨x, ξ⟩ ↦ ?_)
    simp only [coefficient_sub, coefficient_inclusion, coefficient_smulLeft, Pi.sub_apply,
      coefficient_sharp_of_coefficient_eq_smul (a := b) (a' := smulLeft hψ b) ha (x := x)
        (t := (φ x : ℂ)) (fun η ↦ coefficient_smulLeft hψ b (x, η)), smul_sub, hcψ]
  have hsub := (hq.sharp ha).sub (hc.inclusion (neg_add_cancel m).ge)
  refine ⟨_, hq, _, hsub, he, fun t v ↦ ?_⟩
  rw [← toDistr_quantizeSobolev_sharp hq ha, toDistr_quantizeSobolev_sub_apply (hq.sharp ha)
    (hc.inclusion _) hsub, sub_sub_cancel]
  exact toDistr_quantizeSobolev_congr (coefficient_inclusion _ _).symm hc _ rfl

/-- **Microlocal elliptic regularity on a conic region.** Let the scalar symbol `a` with compact
spatial support be elliptic on the points `(x, ξ)` with `x ∈ U`, `ξ ∈ Γ` and `‖ξ‖ ≥ R`, for an open
set `U` and an open cone `Γ`. Then `Op(a)` keeps every singularity of `v ∈ H^t` in `U × Γ`:
`WF(v) ∩ (U × Γ) ⊆ WF(Op(a) v)`. -/
theorem waveFrontSet_toDistribution_inter_subset_quantizeSobolev_of_isEllipticOn
    {a : Symbol n ℂ ℂ m} (ha : a.HasCompactSpatialSupport) (t : ℝ)
    (v : H^{t}(CoordinateSpace n, ℂ)) {U Γ : Set (CoordinateSpace n)} (hU : IsOpen U)
    (hΓ : IsOpen Γ) (hcone : ∀ s : ℝ, 0 < s → ∀ η ∈ Γ, s • η ∈ Γ) {R : ℝ}
    (hell : a.IsEllipticOn {p | p.1 ∈ U ∧ p.2 ∈ Γ ∧ R ≤ ‖p.2‖}) :
    (toDistribution ⊤ v.toDistr).waveFrontSet ∩ U ×ˢ Γ ⊆
      (toDistribution ⊤ (a.quantizeSobolev ha t v).toDistr).waveFrontSet := by
  rintro ⟨x₀, ξ₀⟩ ⟨hp, hx₀, hξ₀⟩
  obtain ⟨c, hc, hcS, U', Γ', hU', hx₀', hΓ', hξ₀', hcone', R', hc1⟩ :=
    exists_microlocalCutoff_of_mem (V := ℂ) hU hx₀ hΓ hξ₀ hcone R
  obtain ⟨q, hq, e, he, hes, hid⟩ := exists_toDistr_quantizeSobolev_eq_sub ha hell hc hcS
  -- `(x₀, ξ₀) ∈ WF(Op(c) v)`, and `Op(c) v = Op(q) (Op(a) v) - Op(e) v`.
  have h := waveFrontSet_toDistribution_inter_subset_quantizeSobolev hc t v hU' hΓ' hcone' hc1
    ⟨hp, hx₀', hξ₀'⟩
  rw [hid t v, map_sub] at h
  rcases waveFrontSet_sub_subset _ _ h with h | h
  · exact waveFrontSet_toDistribution_quantizeSobolev_subset hq (t - m) _ h
  · rw [waveFrontSet_toDistribution_eq_empty fun s ↦
      hes.memSobolev_toDistr_quantizeSobolev he t s v] at h
    exact h.elim

/-- **Microlocal elliptic regularity.** For a scalar symbol `a` with compact spatial support and
every `v ∈ H^t`, every singularity of `v` is a singularity of `Op(a) v` or a characteristic point
of `a`: `WF(v) ⊆ WF(Op(a) v) ∪ Char(a)`. -/
theorem waveFrontSet_toDistribution_subset_quantizeSobolev_union_characteristicSet
    {a : Symbol n ℂ ℂ m} (ha : a.HasCompactSpatialSupport) (t : ℝ)
    (v : H^{t}(CoordinateSpace n, ℂ)) :
    (toDistribution ⊤ v.toDistr).waveFrontSet ⊆
      (toDistribution ⊤ (a.quantizeSobolev ha t v).toDistr).waveFrontSet ∪
        a.characteristicSet := by
  rintro ⟨x, ξ⟩ hp
  by_contra h
  rw [mem_union, not_or] at h
  obtain ⟨U, hU, Γ, hΓ, hξ, hcone, R, hell⟩ :=
    not_not.1 (not_and.1 h.2 (mem_waveFrontSet_iff.1 hp).2.1)
  exact h.1 (waveFrontSet_toDistribution_inter_subset_quantizeSobolev_of_isEllipticOn ha t v
    isOpen_interior hΓ hcone (hell.mono fun _ hq ↦ ⟨interior_subset hq.1, hq.2⟩)
    ⟨hp, mem_interior_iff_mem_nhds.2 hU, hξ⟩)

/-- Off the characteristic set of a scalar symbol `a` with compact spatial support, `Op(a)` neither
creates nor removes singularities: `WF(Op(a) v) \ Char(a) = WF(v) \ Char(a)` for every
`v ∈ H^t`. -/
theorem waveFrontSet_toDistribution_quantizeSobolev_sdiff_characteristicSet_eq
    {a : Symbol n ℂ ℂ m} (ha : a.HasCompactSpatialSupport) (t : ℝ)
    (v : H^{t}(CoordinateSpace n, ℂ)) :
    (toDistribution ⊤ (a.quantizeSobolev ha t v).toDistr).waveFrontSet \ a.characteristicSet =
      (toDistribution ⊤ v.toDistr).waveFrontSet \ a.characteristicSet :=
  (sdiff_subset_sdiff_left (waveFrontSet_toDistribution_quantizeSobolev_subset ha t v)).antisymm
    fun _ hp ↦ ⟨((waveFrontSet_toDistribution_subset_quantizeSobolev_union_characteristicSet
      ha t v) hp.1).resolve_right hp.2, hp.2⟩

/-- **Elliptic regularity for singular supports.** For a scalar symbol `a` with compact spatial
support and every `v ∈ H^t`, the singular support of `v` lies in that of `Op(a) v` together with
the positions of the characteristic points of `a`. -/
theorem singularSupport_toDistribution_subset_singularSupport_quantizeSobolev_union
    {a : Symbol n ℂ ℂ m} (ha : a.HasCompactSpatialSupport) (t : ℝ)
    (v : H^{t}(CoordinateSpace n, ℂ)) :
    (toDistribution ⊤ v.toDistr).singularSupport ⊆
      (toDistribution ⊤ (a.quantizeSobolev ha t v).toDistr).singularSupport ∪
        Prod.fst '' a.characteristicSet := by
  rw [← fst_image_waveFrontSet, ← fst_image_waveFrontSet, ← image_union]
  exact image_mono
    (waveFrontSet_toDistribution_subset_quantizeSobolev_union_characteristicSet ha t v)

end EllipticRegularity

end Symbol

end TauCeti
