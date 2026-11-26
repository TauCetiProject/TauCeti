/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Microlocality
public import TauCeti.Analysis.Pseudodifferential.Symbol.Elliptic
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Distribution.WaveFrontSet.SingularSupport
import TauCeti.Analysis.Normed.Module.Cone
import TauCeti.Analysis.Pseudodifferential.Composition.Parametrix
import TauCeti.Analysis.Pseudodifferential.MicrolocalCutoff
import TauCeti.Analysis.Pseudodifferential.Symbol.Map
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Bounds

/-!
# The characteristic set and microlocal elliptic regularity

A point `(x₀, ξ₀)` with `ξ₀ ≠ 0` is *noncharacteristic* for a symbol `a` of order `m` if `a` is
elliptic in a conic neighbourhood of it at large frequencies: for a neighbourhood `U` of `x₀`, an
open cone `Γ` containing `ξ₀` and a radius `R`, the value `a(x, ξ)` is invertible with
`‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)` whenever `x ∈ U`, `ξ ∈ Γ` and `‖ξ‖ ≥ R`, with `C` uniform for `x` in
compact sets (`TauCeti.Symbol.IsEllipticOn`). The other points `(x₀, ξ₀)` with `ξ₀ ≠ 0` form the
**characteristic set** `Char(a)` (`TauCeti.Symbol.characteristicSet`). It is conic, and empty for a
symbol elliptic above some radius.

For a classical symbol `a` the characteristic set is read off the principal symbol: it consists of
the points `(x, ξ)`, `ξ ≠ 0`, at which `a_m(x, ξ)` is not invertible
(`TauCeti.ClassicalSymbol.mem_characteristicSet_toSymbol_iff`). Both inclusions come from the
high-frequency limit `t^(-m) a(y, t ζ) → a_m(x, ξ)` as `t → ∞` and `(y, ζ) → (x, ξ)`
(`TauCeti.ClassicalSymbol.tendsto_rpow_neg_smul_coefficient_smul`). If `a_m(x₀, ξ₀)` is invertible,
the limit is uniform near `(x₀, ξ₀)`, which makes `a` elliptic on the cone over a neighbourhood of
`ξ₀` at large frequencies
(`TauCeti.ClassicalSymbol.exists_isEllipticOn_of_isInvertible_coefficient_principal`). Conversely,
if `a` is elliptic along the ray of `ξ`, the rescaled values `t^(-m) a(x, t ξ)` have uniformly
bounded inverses and converge to `a_m(x, ξ)`, which is therefore invertible
(`TauCeti.ClassicalSymbol.isInvertible_coefficient_principal_of_eventually`). In particular a
classical symbol has empty characteristic set exactly when it is elliptic
(`TauCeti.ClassicalSymbol.characteristicSet_toSymbol_eq_empty_iff`).

This file proves **microlocal elliptic regularity** for a scalar symbol `a` with compact spatial
support acting on a Bessel-potential space `H^t`: the operator `Op(a)` recovers every singularity of
`v ∈ H^t` away from its characteristic set,

`WF(v) ⊆ WF(Op(a) v) ∪ Char(a)`

(`TauCeti.Symbol.waveFrontSet_toDistribution_subset_quantizeSobolev_union_characteristicSet`).
Together with the microlocality `WF(Op(a) v) ⊆ WF(v)`
(`TauCeti.Symbol.waveFrontSet_toDistribution_quantizeSobolev_subset`), the two wave front sets agree
off `Char(a)`, and the singular supports agree over the points above which `a` has no
characteristic covector.

Conversely, elliptic operators of order `0` detect the covectors at which `v` is smooth. If
`(x₀, ξ₀) ∉ WF(v)`, a microlocal cutoff `c` living in a small conic neighbourhood of `(x₀, ξ₀)` on
which `v` is microlocally smooth is the identity near `(x₀, ξ₀)`, so not characteristic there, and
`Op(c) v` has empty wave front set
(`Symbol.exists_notMem_characteristicSet_and_waveFrontSet_toDistribution_quantizeSobolev_eq_empty`).
An empty wave front set means that `Op(c) v` is a smooth function
(`Distribution.singularSupport_eq_empty_iff_waveFrontSet_eq_empty`,
`Distribution.singularSupport_eq_empty_iff`). With microlocal elliptic regularity this identifies
the Fourier-decay definition of the wave front set with the definition by elliptic test operators:

`WF(v) = ⋂ {Char(c) | c of order 0, Op(c) v smooth}`

(`TauCeti.Symbol.waveFrontSet_toDistribution_eq_iInter_characteristicSet`), the intersection being
over symbols `c` with compact spatial support.

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
* `TauCeti.Symbol.notMem_waveFrontSet_toDistribution_iff_exists`: `(x₀, ξ₀) ∉ WF(v)` if and only if
  some `c` of order `0`, not characteristic at `(x₀, ξ₀)`, gives `WF(Op(c) v) = ∅`.
* `TauCeti.Symbol.waveFrontSet_toDistribution_eq_iInter_characteristicSet`: the wave front set is
  the intersection of the characteristic sets of the test operators `c` with `WF(Op(c) v) = ∅`.
* `TauCeti.ClassicalSymbol.mem_characteristicSet_toSymbol_iff`,
  `TauCeti.ClassicalSymbol.characteristicSet_toSymbol`: the characteristic set of a classical
  symbol is the set of points at which its principal symbol is not invertible, and
  `TauCeti.ClassicalSymbol.characteristicSet_toSymbol_eq_empty_iff`: it is empty exactly when the
  symbol is elliptic.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §7
  (microlocal parametrices, `WF(u) ⊆ WF(Pu) ∪ Char(P)`, and the wave front set as the
  intersection of the characteristic sets of the operators of order `0` smoothing `u`).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  §18.1, Theorem 18.1.28 (elliptic regularity) and the description of `WF(u)` by the operators of
  order `0` mapping `u` to a smooth function, in the same section.
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

/-- A symbol of order `0` that is the identity at large frequencies over a neighbourhood of `x₀`
and an open cone containing `ξ₀` is not characteristic at `(x₀, ξ₀)`. -/
theorem notMem_characteristicSet_of_eq_id {c : Symbol n V V 0} {x₀ ξ₀ : CoordinateSpace n}
    {U Γ : Set (CoordinateSpace n)} (hU : U ∈ 𝓝 x₀) (hΓ : IsOpen Γ) (hξ₀ : ξ₀ ∈ Γ)
    (hcone : ∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) {R : ℝ}
    (hcΓ : ∀ x ∈ U, ∀ ξ ∈ Γ, R ≤ ‖ξ‖ → c.coefficient (x, ξ) = ContinuousLinearMap.id ℂ V) :
    (x₀, ξ₀) ∉ c.characteristicSet := fun h ↦
  h.2 ⟨U, hU, Γ, hΓ, hξ₀, hcone, R, isEllipticOn_iff.2 fun _ _ ↦ ⟨1, fun p hp _ ↦ by
    rw [hcΓ p.1 hp.1 p.2 hp.2.1 hp.2.2, ContinuousLinearMap.inverse_id]
    exact ⟨⟨ContinuousLinearEquiv.refl ℂ V, rfl⟩, by
      simpa using ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := V)⟩⟩⟩

end CharacteristicSet

/-! ### Microlocal elliptic regularity -/

section ParametrixIdentity

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- **The microlocal parametrix identity on Sobolev spaces.** Let `a` have compact spatial support
and be elliptic on a set `S`, and let `c` of order `0` have compact spatial support and vanish
outside `S`. Then there are a symbol `q` of order `-m` and a smoothing symbol `e`, both with compact
spatial support, such that `Op(c) v = Op(q) (Op(a) v) - Op(e) v` for every `v ∈ H^t`. -/
theorem exists_toDistr_quantizeSobolev_eq_sub {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) {S : Set (CoordinateSpace n × CoordinateSpace n)}
    (hell : a.IsEllipticOn S) {c : Symbol n V V 0} (hc : c.HasCompactSpatialSupport)
    (hcS : ∀ p ∉ S, c.coefficient p = 0) :
    ∃ (q : Symbol n W V (-m)) (hq : q.HasCompactSpatialSupport) (e : Symbol n V V (-m + m))
      (he : e.HasCompactSpatialSupport), e.IsSmoothing ∧
      ∀ (t : ℝ) (v : H^{t}(CoordinateSpace n, V)), (c.quantizeSobolev hc t v).toDistr =
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

end ParametrixIdentity

section EllipticRegularity

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

/-! ### Elliptic test operators

A covector `(x₀, ξ₀)` lies outside the wave front set of `v` exactly when some operator of
order `0`, elliptic at `(x₀, ξ₀)`, maps `v` to a smooth function. -/

section TestOperators

/-- **Elliptic test operators detect regular covectors.** If `v ∈ H^t` is microlocally smooth at
`(x₀, ξ₀)`, there is a symbol `c` of order `0` with compact spatial support, not characteristic at
`(x₀, ξ₀)`, such that `Op(c) v` has empty wave front set. -/
theorem exists_notMem_characteristicSet_and_waveFrontSet_toDistribution_quantizeSobolev_eq_empty
    (t : ℝ) (v : H^{t}(CoordinateSpace n, ℂ)) {x₀ ξ₀ : CoordinateSpace n}
    (hv : (x₀, ξ₀) ∉ (toDistribution ⊤ v.toDistr).waveFrontSet) :
    ∃ (c : Symbol n ℂ ℂ 0) (hc : c.HasCompactSpatialSupport), (x₀, ξ₀) ∉ c.characteristicSet ∧
      (toDistribution ⊤ (c.quantizeSobolev hc t v).toDistr).waveFrontSet = ∅ := by
  -- At the zero frequency every symbol is noncharacteristic, and the zero symbol will do.
  rcases eq_or_ne ξ₀ 0 with rfl | hξ₀
  · exact ⟨0, hasCompactSpatialSupport_zero, fun h ↦ h.1 rfl, by simp⟩
  set T := toDistribution ⊤ v.toDistr
  have hs : T.IsMicrolocallySmoothAt x₀ ξ₀ := by simpa [hξ₀] using hv
  -- The witnesses of microlocal smoothness at `(x₀, ξ₀)`, a cutoff `φ` and an open cone `Γ`,
  -- witness it at every `(x, η)` with `φ x ≠ 0` and `η ∈ Γ`.
  obtain ⟨φ, hφ, Γ, hΓ, hξ₀Γ, hcone, hdecay⟩ := isMicrolocallySmoothAt_iff.1 hs
  have hsm (x : CoordinateSpace n) (hx : φ x ≠ 0) (η : CoordinateSpace n) (hη : η ∈ Γ) :
      T.IsMicrolocallySmoothAt x η :=
    isMicrolocallySmoothAt_iff.2 ⟨φ, hx, Γ, hΓ, hη, hcone, hdecay⟩
  obtain ⟨δ, hδ, hδφ⟩ := Metric.isOpen_iff.1 (isOpen_ne_fun φ.continuous continuous_const) x₀ hφ
  -- A closed cone `F` with `Γ' ⊆ F` and `F \ {0} ⊆ Γ`, and a cutoff `c` living in
  -- `ball x₀ (δ / 2) × Γ'` which is the identity near `(x₀, ξ₀)`.
  obtain ⟨F, Γ', hF, hFcone, hFΓ, hΓ', hξ₀Γ', hcone', hΓ'F⟩ :=
    hΓ.exists_isOpen_cone_subset_isClosed_cone hcone hξ₀Γ
  obtain ⟨c, hc, hc0, U', Γ'', hU', hx₀U', hΓ'', hξ₀Γ'', hcone'', R', hc1⟩ :=
    exists_microlocalCutoff_of_mem (V := ℂ) isOpen_ball (mem_ball_self (half_pos hδ)) hΓ'
      hξ₀Γ' hcone' 0
  refine ⟨c, hc, notMem_characteristicSet_of_eq_id (hU'.mem_nhds hx₀U') hΓ'' hξ₀Γ'' hcone'' hc1,
    eq_empty_iff_forall_notMem.2 fun ⟨x, ξ⟩ hp ↦ ?_⟩
  -- A covector of `WF(Op(c) v)` lies in `WF(v)`, so outside `closedBall x₀ (δ / 2) × F`, where
  -- `c` vanishes conically.
  obtain ⟨-, hξ0, hns⟩ := mem_waveFrontSet_iff.1
    (waveFrontSet_toDistribution_quantizeSobolev_subset hc t v hp)
  by_cases hx : x ∈ closedBall x₀ (δ / 2)
  · by_cases hξ : ξ ∈ F
    · exact hns (hsm x (hδφ (closedBall_subset_ball (half_lt_self hδ) hx)) ξ (hFΓ ξ hξ hξ0))
    · exact notMem_waveFrontSet_toDistribution_quantizeSobolev_of_eq_zero hc t v univ_mem
        hF.isOpen_compl hξ (forall_smul_mem_compl hFcone) (R := 0)
        (fun _ _ _ hξ' _ ↦ hc0 _ fun hq ↦ hξ' (hΓ'F hq.2.1)) hp
  · exact notMem_waveFrontSet_toDistribution_quantizeSobolev_of_eq_zero hc t v
      (isClosed_closedBall.isOpen_compl.mem_nhds hx) isOpen_univ (mem_univ ξ)
      (fun _ _ _ _ ↦ mem_univ _) (R := 0)
      (fun _ hx' _ _ _ ↦ hc0 _ fun hq ↦ hx' (ball_subset_closedBall hq.1)) hp

/-- **The wave front set by elliptic test operators.** For `v ∈ H^t`, the covector `(x₀, ξ₀)` lies
outside `WF(v)` if and only if some symbol `c` of order `0` with compact spatial support, not
characteristic at `(x₀, ξ₀)`, gives `Op(c) v` empty wave front set. -/
theorem notMem_waveFrontSet_toDistribution_iff_exists (t : ℝ) (v : H^{t}(CoordinateSpace n, ℂ))
    {x₀ ξ₀ : CoordinateSpace n} :
    (x₀, ξ₀) ∉ (toDistribution ⊤ v.toDistr).waveFrontSet ↔
      ∃ (c : Symbol n ℂ ℂ 0) (hc : c.HasCompactSpatialSupport), (x₀, ξ₀) ∉ c.characteristicSet ∧
        (toDistribution ⊤ (c.quantizeSobolev hc t v).toDistr).waveFrontSet = ∅ := by
  refine
    ⟨exists_notMem_characteristicSet_and_waveFrontSet_toDistribution_quantizeSobolev_eq_empty t v,
      fun ⟨c, hc, hchar, hWF⟩ hp ↦ hchar ?_⟩
  simpa [hWF] using waveFrontSet_toDistribution_subset_quantizeSobolev_union_characteristicSet hc t
    v hp

/-- **The wave front set as an intersection of characteristic sets.** For `v ∈ H^t`, `WF(v)` is the
intersection of the characteristic sets of the symbols `c` of order `0` with compact spatial
support for which `Op(c) v` has empty wave front set. -/
theorem waveFrontSet_toDistribution_eq_iInter_characteristicSet (t : ℝ)
    (v : H^{t}(CoordinateSpace n, ℂ)) :
    (toDistribution ⊤ v.toDistr).waveFrontSet =
      ⋂ (c : Symbol n ℂ ℂ 0) (hc : c.HasCompactSpatialSupport)
        (_ : (toDistribution ⊤ (c.quantizeSobolev hc t v).toDistr).waveFrontSet = ∅),
        c.characteristicSet := by
  ext ⟨x, ξ⟩
  simp only [mem_iInter]
  refine ⟨fun hp c hc hWF ↦ ?_, fun h ↦ ?_⟩
  · simpa [hWF] using
      waveFrontSet_toDistribution_subset_quantizeSobolev_union_characteristicSet hc t v hp
  · by_contra hp
    obtain ⟨c, hc, hchar, hWF⟩ :=
      exists_notMem_characteristicSet_and_waveFrontSet_toDistribution_quantizeSobolev_eq_empty t v
        hp
    exact hchar (h c hc hWF)

end TestOperators

end Symbol

/-! ### The characteristic set of a classical symbol -/

namespace ClassicalSymbol

variable {n : ℕ} {m : ℝ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {a : ClassicalSymbol n V W m}

/-- **The principal symbol where the full symbol is elliptic.** Let `ξ ≠ 0`. If the full symbol of
a classical symbol of order `m` is invertible at `(x, t ξ)` for all large `t`, with
`‖a(x, t ξ)⁻¹‖ ≤ C ⟨t ξ⟩^(-m)`, then its principal symbol `a_m(x, ξ)` is invertible. -/
theorem isInvertible_coefficient_principal_of_eventually {x ξ : CoordinateSpace n} (hξ : ξ ≠ 0)
    {C : ℝ}
    (h : ∀ᶠ t : ℝ in atTop, (a.toSymbol.coefficient (x, t • ξ)).IsInvertible ∧
      ‖(a.toSymbol.coefficient (x, t • ξ)).inverse‖ ≤ C * (1 + ‖t • ξ‖ ^ 2) ^ (-m / 2)) :
    (a.principal.coefficient (x, ξ)).IsInvertible := by
  -- `B t = t^(-m) a(x, t ξ)` tends to `a_m(x, ξ)` and has inverses bounded by
  -- `L = C 2^(|m| / 2) ‖ξ‖^(-m)`, so it is invertible for large `t` and close to `a_m(x, ξ)`.
  have hlim : Tendsto (fun t : ℝ ↦ t ^ (-m) • a.toSymbol.coefficient (x, t • ξ)) atTop
      (𝓝 (a.principal.coefficient (x, ξ))) :=
    (a.tendsto_rpow_neg_smul_coefficient_smul hξ).comp
      ((tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop).prodMk tendsto_const_nhds)
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  set L := |C| * 2 ^ (|-m| / 2) * ‖ξ‖ ^ (-m) + 1
  have hL : 0 < L := by positivity
  obtain ⟨t, ⟨hinv, hle⟩, ht, ht1, hclose⟩ := (h.and ((eventually_gt_atTop (0 : ℝ)).and
    ((eventually_ge_atTop ‖ξ‖⁻¹).and (hlim.eventually (ball_mem_nhds _ (inv_pos.2 hL)))))).exists
  have htξ : ‖t • ξ‖ = t * ‖ξ‖ := by rw [norm_smul, Real.norm_of_nonneg ht.le]
  have htξ1 : 1 ≤ ‖t • ξ‖ := by
    rw [htξ, ← inv_mul_cancel₀ hn.ne']
    gcongr
  -- The bound on the inverse of `B t = t^(-m) a(x, t ξ)`.
  have hw := Real.one_add_sq_rpow_le_two_rpow_mul_abs_rpow (t := ‖t • ξ‖) (by
    rwa [abs_norm]) (-m)
  rw [abs_norm] at hw
  have htm : 0 < t ^ (-m) := Real.rpow_pos_of_pos ht _
  have hB : ((t ^ (-m) : ℝ) • a.toSymbol.coefficient (x, t • ξ)).IsInvertible := by
    rwa [← Complex.coe_smul, ContinuousLinearMap.isInvertible_smul_iff
      (Complex.ofReal_ne_zero.2 htm.ne')]
  have hBinv : ‖((t ^ (-m) : ℝ) • a.toSymbol.coefficient (x, t • ξ)).inverse‖ ≤ L := by
    rw [← Complex.coe_smul, ContinuousLinearMap.inverse_smul, norm_smul, norm_inv,
      Complex.norm_real, Real.norm_of_nonneg htm.le, ← Real.rpow_neg ht.le, neg_neg]
    calc t ^ m * ‖(a.toSymbol.coefficient (x, t • ξ)).inverse‖
        ≤ t ^ m * (|C| * (2 ^ (|-m| / 2) * ‖t • ξ‖ ^ (-m))) := by
          gcongr
          exact hle.trans (mul_le_mul (le_abs_self C) hw (by positivity) (abs_nonneg C))
      _ = |C| * 2 ^ (|-m| / 2) * ‖ξ‖ ^ (-m) := by
          rw [htξ, Real.mul_rpow ht.le hn.le, Real.rpow_neg ht.le]
          field_simp
      _ ≤ L := le_add_of_nonneg_right zero_le_one
  rw [dist_comm, dist_eq_norm] at hclose
  exact hB.of_mul_norm_sub_lt hBinv (by
    calc L * ‖a.principal.coefficient (x, ξ) - _‖ < L * L⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hL.ne')

/-- Near a covector `(x₀, ξ₀)`, `ξ₀ ≠ 0`, at which the principal symbol is invertible, the full
symbol `a(y, t ζ)` is invertible for all large `t`, uniformly for `(y, ζ)` near `(x₀, ξ₀)`, with
`‖a(y, t ζ)⁻¹‖ ≤ C t^(-m)`: the rescaled symbol `t^(-m) a(y, t ζ)` tends to `a_m(x₀, ξ₀)`. -/
private theorem exists_isInvertible_coefficient_smul {x₀ ξ₀ : CoordinateSpace n} (hξ₀ : ξ₀ ≠ 0)
    (h : (a.principal.coefficient (x₀, ξ₀)).IsInvertible) :
    ∃ U ∈ 𝓝 x₀, ∃ V ∈ 𝓝 ξ₀, ∃ T C : ℝ, 0 < T ∧ ∀ t, T ≤ t → ∀ y ∈ U, ∀ ζ ∈ V,
      (a.toSymbol.coefficient (y, t • ζ)).IsInvertible ∧
        ‖(a.toSymbol.coefficient (y, t • ζ)).inverse‖ ≤ C * t ^ (-m) := by
  set A := a.principal.coefficient (x₀, ξ₀)
  set M := ‖A.inverse‖ + 1
  have hM : 0 < M := by positivity
  -- Eventually `t^(-m) a(y, t ζ)` is within `1 / (2 M)` of `A`, hence invertible with inverse
  -- bounded by `2 M`.
  have hev : ∀ᶠ p in (atTop : Filter ℝ) ×ˢ 𝓝 (x₀, ξ₀),
      M * ‖p.1 ^ (-m) • a.toSymbol.coefficient (p.2.1, p.1 • p.2.2) - A‖ ≤ 1 / 2 := by
    filter_upwards [(a.tendsto_rpow_neg_smul_coefficient_smul hξ₀).eventually
      (closedBall_mem_nhds A (by positivity : 0 < 1 / (2 * M)))] with p hp
    rw [dist_eq_norm] at hp
    calc M * _ ≤ M * (1 / (2 * M)) := by gcongr
      _ = 1 / 2 := by field_simp
  obtain ⟨T, hT, N, hN, hTN⟩ := eventually_prod_iff.1 hev
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hT
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 hN
  refine ⟨U, hU, V, hV, max T₀ 1, 2 * M, by positivity, fun t ht y hy ζ hζ ↦ ?_⟩
  have ht0 : 0 < t := one_pos.trans_le ((le_max_right _ _).trans ht)
  have htm : 0 < t ^ (-m) := Real.rpow_pos_of_pos ht0 _
  have hc : ((t ^ (-m) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 htm.ne'
  have hkey := hTN (hT₀ t ((le_max_left _ _).trans ht)) (hUV (mk_mem_prod hy hζ))
  dsimp only at hkey
  rw [← Complex.coe_smul] at hkey
  have hlt := hkey.trans_lt (by norm_num : (1 / 2 : ℝ) < 1)
  have hinv := h.of_mul_norm_sub_lt (le_add_of_nonneg_right zero_le_one) hlt
  have hnorm := (h.norm_inverse_le_of_mul_norm_sub_lt (le_add_of_nonneg_right zero_le_one)
    hlt).trans (div_le_div_of_nonneg_left hM.le (by norm_num : (0 : ℝ) < 1 / 2) (by linarith))
  rw [ContinuousLinearMap.isInvertible_smul_iff hc] at hinv
  rw [ContinuousLinearMap.inverse_smul, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg htm.le] at hnorm
  refine ⟨hinv, ?_⟩
  calc ‖(a.toSymbol.coefficient (y, t • ζ)).inverse‖
      = t ^ (-m) * ((t ^ (-m))⁻¹ * ‖(a.toSymbol.coefficient (y, t • ζ)).inverse‖) := by
        field_simp
    _ ≤ t ^ (-m) * (M / (1 / 2)) := by gcongr
    _ = 2 * M * t ^ (-m) := by ring

omit [CompleteSpace V] in
/-- If `r < s ‖η‖ < 3 r` with `r, s > 0` and `‖η‖ ≥ 1`, then
`s^m = (s ‖η‖)^m ‖η‖^(-m) ≤ (r^m + (3 r)^m) 2^(|m| / 2) ⟨η⟩^(-m)`. -/
private theorem rpow_le_mul_one_add_norm_sq_rpow {r s : ℝ} {η : CoordinateSpace n} (hs : 0 < s)
    (hη1 : 1 ≤ ‖η‖) (hsη : r < s * ‖η‖ ∧ s * ‖η‖ < 3 * r) :
    s ^ m ≤ (r ^ m + (3 * r) ^ m) * (2 ^ (|-m| / 2) * (1 + ‖η‖ ^ 2) ^ (-m / 2)) := by
  have hη0 : 0 < ‖η‖ := one_pos.trans_le hη1
  have hr : 0 < r := by
    by_contra! hr
    linarith [mul_pos hs hη0, hsη.1, hsη.2]
  have hpow : (s * ‖η‖) ^ m ≤ r ^ m + (3 * r) ^ m := by
    rcases le_total 0 m with hm | hm
    · exact (Real.rpow_le_rpow (by positivity) hsη.2.le hm).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg hr.le m))
    · exact (Real.rpow_le_rpow_of_nonpos hr hsη.1.le hm).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) m))
  have hw := Real.abs_rpow_le_two_rpow_mul_one_add_sq_rpow (t := ‖η‖) (by rwa [abs_norm]) (-m)
  rw [abs_norm] at hw
  have hsm : s ^ m = (s * ‖η‖) ^ m * ‖η‖ ^ (-m) := by
    rw [Real.mul_rpow hs.le hη0.le, Real.rpow_neg hη0.le, mul_assoc,
      mul_inv_cancel₀ (Real.rpow_pos_of_pos hη0 m).ne', mul_one]
  rw [hsm]
  gcongr

/-- **Ellipticity near a noncharacteristic covector.** If the principal symbol `a_m(x₀, ξ₀)` of a
classical symbol of order `m` is invertible at a nonzero frequency `ξ₀`, then the full symbol is
elliptic at large frequencies over a neighbourhood `U` of `x₀` and an open cone `Γ` containing
`ξ₀` (`TauCeti.Symbol.IsEllipticOn`): it is invertible at the points `(x, ξ)` with `x ∈ U`,
`ξ ∈ Γ` and `‖ξ‖ ≥ R`, with `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)`. -/
theorem exists_isEllipticOn_of_isInvertible_coefficient_principal {x₀ ξ₀ : CoordinateSpace n}
    (hξ₀ : ξ₀ ≠ 0) (h : (a.principal.coefficient (x₀, ξ₀)).IsInvertible) :
    ∃ U ∈ 𝓝 x₀, ∃ Γ : Set (CoordinateSpace n), IsOpen Γ ∧ ξ₀ ∈ Γ ∧
      (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
        ∃ R : ℝ, a.toSymbol.IsEllipticOn {q | q.1 ∈ U ∧ q.2 ∈ Γ ∧ R ≤ ‖q.2‖} := by
  obtain ⟨U, hU, V, hV, T, C, hT, hTC⟩ := exists_isInvertible_coefficient_smul hξ₀ h
  set r := ‖ξ₀‖ / 2 with hr_def
  have hr : 0 < r := half_pos (norm_pos_iff.2 hξ₀)
  -- The frequencies `η` of `Γ` are `t ζ` with `ζ ∈ V ∩ ball ξ₀ r`, so `‖ζ‖ ∈ (r, 3 r)`, and
  -- `t ≥ T` once `‖η‖ ≥ 3 r T + 1`.
  obtain ⟨Γ, hΓo, hξΓ, hcone, hΓ⟩ := (isOpen_interior.inter (isOpen_ball (x := ξ₀) (ε := r)))
    |>.exists_cone_exists_smul_mem ⟨mem_interior_iff_mem_nhds.2 hV, mem_ball_self hr⟩
  -- `‖a(y, η)⁻¹‖ ≤ C (r^m + (3 r)^m) 2^(|m| / 2) ⟨η⟩^(-m)`.
  refine ⟨U, hU, Γ, hΓo, hξΓ, hcone, 3 * r * T + 1, Symbol.isEllipticOn_iff.2 fun _ _ ↦
    ⟨C * (r ^ m + (3 * r) ^ m) * 2 ^ (|-m| / 2), fun ⟨y, η⟩ ⟨hy, hη, hR⟩ _ ↦ ?_⟩⟩
  dsimp only at hy hη hR ⊢
  obtain ⟨s, hs, hsV, hsB⟩ := hΓ η hη
  have hη1 : 1 ≤ ‖η‖ := (le_add_of_nonneg_left (by positivity)).trans hR
  -- `s ‖η‖ = ‖s η‖ ∈ (r, 3 r)`.
  have hsη : r < s * ‖η‖ ∧ s * ‖η‖ < 3 * r := by
    rw [mem_ball, dist_eq_norm] at hsB
    have h₁ := norm_sub_norm_le ξ₀ (s • η)
    have h₂ := norm_sub_norm_le (s • η) ξ₀
    rw [norm_sub_rev] at h₁
    rw [norm_smul, Real.norm_of_nonneg hs.le] at h₁ h₂
    constructor <;> linarith
  -- `η = s⁻¹ • (s • η)` with `s⁻¹ ≥ T`.
  have ht : T ≤ s⁻¹ := by
    have h₁ : 3 * r * T < 3 * r * s⁻¹ :=
      calc 3 * r * T < ‖η‖ := by linarith
        _ = s⁻¹ * (s * ‖η‖) := by field_simp
        _ < s⁻¹ * (3 * r) := mul_lt_mul_of_pos_left hsη.2 (inv_pos.2 hs)
        _ = 3 * r * s⁻¹ := mul_comm _ _
    exact (lt_of_mul_lt_mul_left h₁ (by positivity)).le
  obtain ⟨hinv, hle⟩ := hTC s⁻¹ ht y hy (s • η) (interior_subset hsV)
  rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul, Real.rpow_neg (inv_nonneg.2 hs.le),
    Real.inv_rpow hs.le, inv_inv] at hle
  rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul] at hinv
  refine ⟨hinv, hle.trans ?_⟩
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hle)
    (Real.rpow_pos_of_pos hs m)
  calc C * s ^ m
      ≤ C * ((r ^ m + (3 * r) ^ m) * (2 ^ (|-m| / 2) * (1 + ‖η‖ ^ 2) ^ (-m / 2))) :=
        mul_le_mul_of_nonneg_left (rpow_le_mul_one_add_norm_sq_rpow hs hη1 hsη) hC
    _ = _ := by ring

/-- **The characteristic set of a classical symbol** consists of the points `(x, ξ)`, `ξ ≠ 0`, at
which its principal symbol `a_m(x, ξ)` is not invertible. -/
@[simp]
theorem mem_characteristicSet_toSymbol_iff {p : CoordinateSpace n × CoordinateSpace n} :
    p ∈ a.toSymbol.characteristicSet ↔
      p.2 ≠ 0 ∧ ¬ (a.principal.coefficient p).IsInvertible := by
  obtain ⟨x, ξ⟩ := p
  refine and_congr_right fun hξ ↦ not_congr ⟨fun ⟨U, hU, Γ, _, hξΓ, hcone, R, hR⟩ ↦ ?_,
    exists_isEllipticOn_of_isInvertible_coefficient_principal hξ⟩
  -- Along the ray of `ξ`, the points `(x, t ξ)` with `‖t ξ‖ ≥ R` lie in the elliptic region.
  obtain ⟨C, hC⟩ := Symbol.isEllipticOn_iff.1 hR {x} isCompact_singleton
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  refine isInvertible_coefficient_principal_of_eventually hξ (C := C) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (R / ‖ξ‖)] with t ht htR
  refine hC (x, t • ξ) ⟨mem_of_mem_nhds hU, hcone t ht ξ hξΓ, ?_⟩ rfl
  rw [norm_smul, Real.norm_of_nonneg ht.le]
  exact (div_le_iff₀ hn).1 htR

/-- The characteristic set of a classical symbol is the set of points `(x, ξ)`, `ξ ≠ 0`, at which
its principal symbol is not invertible. -/
theorem characteristicSet_toSymbol :
    a.toSymbol.characteristicSet = {p | p.2 ≠ 0 ∧ ¬ (a.principal.coefficient p).IsInvertible} :=
  Set.ext fun _ ↦ mem_characteristicSet_toSymbol_iff

/-- A classical symbol has no characteristic points exactly when it is elliptic. -/
@[simp]
theorem characteristicSet_toSymbol_eq_empty_iff :
    a.toSymbol.characteristicSet = ∅ ↔ a.IsElliptic := by
  simp [eq_empty_iff_forall_notMem, isElliptic_iff]

end ClassicalSymbol

end TauCeti
