/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Microlocality
public import TauCeti.Analysis.Pseudodifferential.Symbol.Elliptic
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.WaveFrontSet.SingularSupport
import TauCeti.Analysis.Normed.Module.Cone
import TauCeti.Analysis.Pseudodifferential.Composition.Parametrix
import TauCeti.Analysis.Pseudodifferential.MicrolocalCutoff
import TauCeti.Analysis.Pseudodifferential.Symbol.Classical.Elliptic
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

For a classical symbol `a` the characteristic set is read off the principal symbol: it consists of
the points `(x, ξ)`, `ξ ≠ 0`, at which `a_m(x, ξ)` is not invertible
(`TauCeti.ClassicalSymbol.mem_characteristicSet_toSymbol_iff`). If `a_m(x₀, ξ₀)` is invertible,
then `a` is elliptic on the cone over a neighbourhood of `ξ₀` at large frequencies
(`TauCeti.ClassicalSymbol.exists_isEllipticOn_of_isInvertible_coefficient_principal`). Conversely,
if `a` is elliptic along the ray of `ξ`, then `a_m(x, ξ)` is invertible
(`TauCeti.ClassicalSymbol.isInvertible_coefficient_principal_of_isEllipticOn`). In particular a
classical symbol has empty characteristic set exactly when it is elliptic
(`TauCeti.ClassicalSymbol.characteristicSet_toSymbol_eq_empty_iff`).

This file proves **microlocal elliptic regularity** for a symbol `a` with compact spatial support
acting on a Bessel-potential space `H^t`: the operator `Op(a)` recovers every singularity of
`v ∈ H^t` away from its characteristic set,

`WF(v) ⊆ WF(Op(a) v) ∪ Char(a)`.

It holds for **systems**, symbols with values in `V →L[ℂ] W` for finite-dimensional `W`, acting on
`v ∈ H^t(ℝⁿ; V)`, with the wave front set of vector-valued distributions, the union of the wave
front sets of the components (`Distribution.vectorWaveFrontSet`)
(`TauCeti.Symbol.vectorWaveFrontSet_toDistribution_subset_quantizeSobolev_union_characteristicSet`).
In a local frame an operator between vector bundles has such a symbol, and ellipticity of a system
is invertibility of the matrix `a(x, ξ)`, not of its entries. For a scalar symbol the wave front set
of a scalar distribution as a vector-valued one is its wave front set, and this is
`TauCeti.Symbol.waveFrontSet_toDistribution_subset_quantizeSobolev_union_characteristicSet`.
Together with the microlocality `WF(Op(a) v) ⊆ WF(v)`
(`TauCeti.Symbol.vectorWaveFrontSet_toDistribution_quantizeSobolev_subset`), the two wave front sets
agree off `Char(a)`, and the singular supports agree over the points above which `a` has no
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

For a system the parametrix `b` has values in `W →L[ℂ] V`, but the cutoff `c` can be taken scalar,
`c = c₁ Id_V` for a scalar microlocal cutoff `c₁`. Then `Op(c)` acts on each component separately,
`ℓ (Op(c) v) = Op(c₁) (ℓ v)` for every functional `ℓ` on `V`
(`TauCeti.Symbol.postcomp_comp_quantizeSobolev_map_smulRight_id`), so it is microlocally the
identity on every component, and the argument above runs on the component `ℓ v` singular at
`(x₀, ξ₀)`.

## Main results

* `TauCeti.Symbol.characteristicSet`: the characteristic set of a symbol.
* `TauCeti.Symbol.subset_union_characteristicSet`,
  `TauCeti.Symbol.sdiff_characteristicSet_eq_of_subset`: from inclusions `S ∩ (U × Γ) ⊆ S'` on the
  conic regions where `a` is elliptic to `S ⊆ S' ∪ Char(a)`, and to `S' \ Char(a) = S \ Char(a)`
  when also `S' ⊆ S`.
* `TauCeti.Symbol.exists_toDistr_quantizeSobolev_eq_sub`: the microlocal parametrix identity
  `Op(c) v = Op(q) (Op(a) v) - Op(e) v` on `H^t`, with `e` smoothing.
* `TauCeti.Symbol.vectorWaveFrontSet_toDistribution_inter_subset_quantizeSobolev_of_isEllipticOn`:
  if the system `a` is elliptic on `U × Γ` at large frequencies, then
  `WF(v) ∩ (U × Γ) ⊆ WF(Op(a) v)`.
* `TauCeti.Symbol.vectorWaveFrontSet_toDistribution_subset_quantizeSobolev_union_characteristicSet`:
  **microlocal elliptic regularity for systems**, `WF(v) ⊆ WF(Op(a) v) ∪ Char(a)`.
* `TauCeti.Symbol.vectorWaveFrontSet_toDistribution_quantizeSobolev_sdiff_characteristicSet_eq`:
  `WF(Op(a) v) \ Char(a) = WF(v) \ Char(a)`.
* `TauCeti.Symbol.singularSupport_toDistribution_subset_singularSupport_quantizeSobolev_union`:
  the singular support of `v` lies in that of `Op(a) v` together with the positions of `Char(a)`.
* `TauCeti.Symbol.waveFrontSet_toDistribution_inter_subset_quantizeSobolev_of_isEllipticOn`,
  `TauCeti.Symbol.waveFrontSet_toDistribution_subset_quantizeSobolev_union_characteristicSet`,
  `TauCeti.Symbol.waveFrontSet_toDistribution_quantizeSobolev_sdiff_characteristicSet_eq`: the
  same for scalar symbols, with the wave front set of scalar distributions.
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

/-- **Elliptic regularity from its conic form.** Let `S` be a set of points `(x, ξ)` with `ξ ≠ 0`,
such as a wave front set, with `S ∩ (U × Γ) ⊆ S'` whenever `a` is elliptic on the points `(x, ξ)`
with `x ∈ U`, `ξ ∈ Γ` and `‖ξ‖ ≥ R`, for an open set `U` and an open cone `Γ`. Then
`S ⊆ S' ∪ Char(a)`. -/
theorem subset_union_characteristicSet {a : Symbol n V W m}
    {S S' : Set (CoordinateSpace n × CoordinateSpace n)} (hS : ∀ p ∈ S, p.2 ≠ 0)
    (h : ∀ {U Γ : Set (CoordinateSpace n)}, IsOpen U → IsOpen Γ →
      (∀ s : ℝ, 0 < s → ∀ η ∈ Γ, s • η ∈ Γ) → ∀ {R : ℝ},
        a.IsEllipticOn {p | p.1 ∈ U ∧ p.2 ∈ Γ ∧ R ≤ ‖p.2‖} → S ∩ U ×ˢ Γ ⊆ S') :
    S ⊆ S' ∪ a.characteristicSet := by
  rintro ⟨x, ξ⟩ hp
  by_contra h'
  rw [mem_union, not_or, mem_characteristicSet_iff, not_and, not_not] at h'
  obtain ⟨U, hU, Γ, hΓ, hξ, hcone, R, hell⟩ := h'.2 (hS _ hp)
  exact h'.1 (h isOpen_interior hΓ hcone (hell.mono fun _ hq ↦ ⟨interior_subset hq.1, hq.2⟩)
    ⟨hp, mem_interior_iff_mem_nhds.2 hU, hξ⟩)

/-- If `S' ⊆ S ⊆ S' ∪ Char(a)`, as for the wave front sets of `Op(a) v` and `v`, then `S` and `S'`
agree off the characteristic set: `S' \ Char(a) = S \ Char(a)`. -/
theorem sdiff_characteristicSet_eq_of_subset {a : Symbol n V W m}
    {S S' : Set (CoordinateSpace n × CoordinateSpace n)} (h₁ : S' ⊆ S)
    (h₂ : S ⊆ S' ∪ a.characteristicSet) :
    S' \ a.characteristicSet = S \ a.characteristicSet :=
  (sdiff_subset_sdiff_left h₁).antisymm ((sdiff_subset_sdiff_left h₂).trans_eq union_sdiff_right)

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

/-! ### Microlocal elliptic regularity for systems

A symbol with values in `V →L[ℂ] W` is a system of pseudodifferential operators, the form in which
an operator between vector bundles appears in local frames. Its action on `V`-valued
distributions is measured by the wave front set of vector-valued distributions, the union of the
wave front sets of the components (`Distribution.vectorWaveFrontSet`). Ellipticity of the system
is invertibility of the matrix `a(x, ξ)`, which says nothing about its entries, so microlocal
elliptic regularity does not reduce to the scalar case entry by entry. The microlocal left
parametrix `b` is built for the system, but the microlocal cutoff `c ∼ b # a` can be taken scalar,
`c = c₁ Id_V`. Such a cutoff acts on each component separately
(`TauCeti.Symbol.postcomp_comp_quantizeSobolev_map_smulRight_id`), and so it is microlocally the
identity on every component. -/

section EllipticRegularity

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

/-- **Microlocal elliptic regularity for systems on a conic region.** Let the symbol `a` with values
in `V →L[ℂ] W` and compact spatial support be elliptic on the points `(x, ξ)` with `x ∈ U`, `ξ ∈ Γ`
and `‖ξ‖ ≥ R`, for an open set `U` and an open cone `Γ`. Then `Op(a)` keeps every singularity of
`v ∈ H^t(ℝⁿ; V)` in `U × Γ`: `WF(v) ∩ (U × Γ) ⊆ WF(Op(a) v)`, for the wave front sets of
vector-valued distributions. -/
theorem vectorWaveFrontSet_toDistribution_inter_subset_quantizeSobolev_of_isEllipticOn
    {a : Symbol n V W m} (ha : a.HasCompactSpatialSupport) (t : ℝ) :
    haveI : CompleteSpace W := FiniteDimensional.completeSpace ℂ W
    ∀ (v : H^{t}(CoordinateSpace n, V)) {U Γ : Set (CoordinateSpace n)}, IsOpen U → IsOpen Γ →
      (∀ s : ℝ, 0 < s → ∀ η ∈ Γ, s • η ∈ Γ) → ∀ {R : ℝ},
        a.IsEllipticOn {p | p.1 ∈ U ∧ p.2 ∈ Γ ∧ R ≤ ‖p.2‖} →
        (toDistribution ⊤ v.toDistr).vectorWaveFrontSet ∩ U ×ˢ Γ ⊆
          (toDistribution ⊤ (a.quantizeSobolev ha t v).toDistr).vectorWaveFrontSet := by
  have : CompleteSpace W := FiniteDimensional.completeSpace ℂ W
  intro v U Γ hU hΓ hcone R hell
  rintro ⟨x₀, ξ₀⟩ ⟨hp, hx₀, hξ₀⟩
  -- A scalar microlocal cutoff `c₁`, the identity near `(x₀, ξ₀)` and supported where `a` is
  -- elliptic, and the microlocal parametrix identity `Op(c) v = Op(q) (Op(a) v) - Op(e) v` for
  -- `c = c₁ Id_V`.
  obtain ⟨c₁, hc₁, hc₁S, U', Γ', hU', hx₀', hΓ', hξ₀', hcone', R', hc₁1⟩ :=
    exists_microlocalCutoff_of_mem (V := ℂ) hU hx₀ hΓ hξ₀ hcone R
  set Ψ := ((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).smulRight
    (ContinuousLinearMap.id ℂ V)).restrictScalars ℝ
  obtain ⟨q, hq, e, he, hes, hid⟩ := exists_toDistr_quantizeSobolev_eq_sub ha hell
    (hc₁.map Ψ) (c := c₁.map Ψ) fun p hp ↦ by simp [Ψ, hc₁S p hp]
  -- A component `ℓ v` of `v` is singular at `(x₀, ξ₀)`, and so is `Op(c₁) (ℓ v) = ℓ (Op(c) v)`.
  obtain ⟨ℓ, hℓ⟩ := mem_vectorWaveFrontSet_iff.1 hp
  have hw := BesselPotentialSpace.toDistribution_toDistr_postcomp (Ω := ⊤) ℓ v
  have h := waveFrontSet_toDistribution_inter_subset_quantizeSobolev hc₁ t
    (BesselPotentialSpace.postcomp _ t 2 ℓ v) hU' hΓ' hcone' hc₁1 ⟨hw ▸ hℓ, hx₀', hξ₀'⟩
  rw [← postcomp_quantizeSobolev_map_smulRight_id hc₁ ℓ t v,
    BesselPotentialSpace.toDistribution_toDistr_postcomp, hid t v, map_sub, map_sub] at h
  rcases waveFrontSet_sub_subset _ _ h with h | h
  · -- The component of `Op(q) (Op(a) v)` is singular only where `Op(a) v` is.
    exact vectorWaveFrontSet_toDistribution_quantizeSobolev_subset hq (t - m) _
      (waveFrontSet_mapCLM_subset_vectorWaveFrontSet ℓ _ h)
  · -- The component of `Op(e) v` lies in every `H^s`, since `e` is smoothing.
    rw [← BesselPotentialSpace.toDistribution_toDistr_postcomp,
      waveFrontSet_toDistribution_eq_empty fun s ↦ by
        rw [BesselPotentialSpace.toDistr_postcomp]
        exact (hes.memSobolev_toDistr_quantizeSobolev he t s v).postcomp ℓ] at h
    exact h.elim

/-- **Microlocal elliptic regularity for systems.** For a symbol `a` with values in `V →L[ℂ] W`
and compact spatial support, and every `v ∈ H^t(ℝⁿ; V)`, every singularity of `v` is a singularity
of `Op(a) v` or a characteristic point of `a`: `WF(v) ⊆ WF(Op(a) v) ∪ Char(a)`, for the wave front
sets of vector-valued distributions. -/
theorem vectorWaveFrontSet_toDistribution_subset_quantizeSobolev_union_characteristicSet
    {a : Symbol n V W m} (ha : a.HasCompactSpatialSupport) (t : ℝ) :
    haveI : CompleteSpace W := FiniteDimensional.completeSpace ℂ W
    ∀ v : H^{t}(CoordinateSpace n, V),
      (toDistribution ⊤ v.toDistr).vectorWaveFrontSet ⊆
        (toDistribution ⊤ (a.quantizeSobolev ha t v).toDistr).vectorWaveFrontSet ∪
          a.characteristicSet := by
  intro v
  exact subset_union_characteristicSet (fun _ hp ↦ (vectorWaveFrontSet_subset _ hp).2)
    (vectorWaveFrontSet_toDistribution_inter_subset_quantizeSobolev_of_isEllipticOn ha t v)

end EllipticRegularity

section FiniteDimensionalValues

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

/-- Off the characteristic set of a symbol `a` with values in `V →L[ℂ] W` and compact spatial
support, `Op(a)` neither creates nor removes singularities: `WF(Op(a) v) \ Char(a) =
WF(v) \ Char(a)` for every `v ∈ H^t(ℝⁿ; V)`, for the wave front sets of vector-valued
distributions. -/
theorem vectorWaveFrontSet_toDistribution_quantizeSobolev_sdiff_characteristicSet_eq
    {a : Symbol n V W m} (ha : a.HasCompactSpatialSupport) (t : ℝ) :
    haveI : CompleteSpace V := FiniteDimensional.completeSpace ℂ V
    haveI : CompleteSpace W := FiniteDimensional.completeSpace ℂ W
    ∀ v : H^{t}(CoordinateSpace n, V),
      (toDistribution ⊤ (a.quantizeSobolev ha t v).toDistr).vectorWaveFrontSet \
          a.characteristicSet =
        (toDistribution ⊤ v.toDistr).vectorWaveFrontSet \ a.characteristicSet := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℂ V
  have : CompleteSpace W := FiniteDimensional.completeSpace ℂ W
  intro v
  exact sdiff_characteristicSet_eq_of_subset
    (vectorWaveFrontSet_toDistribution_quantizeSobolev_subset ha t v)
    (vectorWaveFrontSet_toDistribution_subset_quantizeSobolev_union_characteristicSet ha t v)

/-- **Elliptic regularity for singular supports.** For a symbol `a` with values in `V →L[ℂ] W` and
compact spatial support, and every `v ∈ H^t(ℝⁿ; V)`, the singular support of `v` lies in that of
`Op(a) v` together with the positions of the characteristic points of `a`. -/
theorem singularSupport_toDistribution_subset_singularSupport_quantizeSobolev_union
    {a : Symbol n V W m} (ha : a.HasCompactSpatialSupport) (t : ℝ) :
    haveI : CompleteSpace V := FiniteDimensional.completeSpace ℂ V
    haveI : CompleteSpace W := FiniteDimensional.completeSpace ℂ W
    ∀ v : H^{t}(CoordinateSpace n, V),
      (toDistribution ⊤ v.toDistr).singularSupport ⊆
        (toDistribution ⊤ (a.quantizeSobolev ha t v).toDistr).singularSupport ∪
          Prod.fst '' a.characteristicSet := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℂ V
  intro v
  rw [← fst_image_vectorWaveFrontSet, ← fst_image_vectorWaveFrontSet, ← image_union]
  exact image_mono
    (vectorWaveFrontSet_toDistribution_subset_quantizeSobolev_union_characteristicSet ha t v)

end FiniteDimensionalValues

/-! ### Scalar symbols

For a scalar symbol the wave front set of the vector-valued distribution `Op(a) v` is its wave
front set (`Distribution.vectorWaveFrontSet_eq_waveFrontSet`), so the statements above specialize
to the following. -/

section Scalar

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
  simpa only [vectorWaveFrontSet_eq_waveFrontSet] using
    vectorWaveFrontSet_toDistribution_inter_subset_quantizeSobolev_of_isEllipticOn ha t v hU hΓ
      hcone hell

/-- **Microlocal elliptic regularity.** For a scalar symbol `a` with compact spatial support and
every `v ∈ H^t`, every singularity of `v` is a singularity of `Op(a) v` or a characteristic point
of `a`: `WF(v) ⊆ WF(Op(a) v) ∪ Char(a)`. -/
theorem waveFrontSet_toDistribution_subset_quantizeSobolev_union_characteristicSet
    {a : Symbol n ℂ ℂ m} (ha : a.HasCompactSpatialSupport) (t : ℝ)
    (v : H^{t}(CoordinateSpace n, ℂ)) :
    (toDistribution ⊤ v.toDistr).waveFrontSet ⊆
      (toDistribution ⊤ (a.quantizeSobolev ha t v).toDistr).waveFrontSet ∪
        a.characteristicSet := by
  simpa only [vectorWaveFrontSet_eq_waveFrontSet] using
    vectorWaveFrontSet_toDistribution_subset_quantizeSobolev_union_characteristicSet ha t v

/-- Off the characteristic set of a scalar symbol `a` with compact spatial support, `Op(a)` neither
creates nor removes singularities: `WF(Op(a) v) \ Char(a) = WF(v) \ Char(a)` for every
`v ∈ H^t`. -/
theorem waveFrontSet_toDistribution_quantizeSobolev_sdiff_characteristicSet_eq
    {a : Symbol n ℂ ℂ m} (ha : a.HasCompactSpatialSupport) (t : ℝ)
    (v : H^{t}(CoordinateSpace n, ℂ)) :
    (toDistribution ⊤ (a.quantizeSobolev ha t v).toDistr).waveFrontSet \ a.characteristicSet =
      (toDistribution ⊤ v.toDistr).waveFrontSet \ a.characteristicSet := by
  simpa only [vectorWaveFrontSet_eq_waveFrontSet] using
    vectorWaveFrontSet_toDistribution_quantizeSobolev_sdiff_characteristicSet_eq ha t v

end Scalar

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

/-- **The characteristic set of a classical symbol** consists of the points `(x, ξ)`, `ξ ≠ 0`, at
which its principal symbol `a_m(x, ξ)` is not invertible. -/
@[simp]
theorem mem_characteristicSet_toSymbol_iff {p : CoordinateSpace n × CoordinateSpace n} :
    p ∈ a.toSymbol.characteristicSet ↔
      p.2 ≠ 0 ∧ ¬ (a.principal.coefficient p).IsInvertible := by
  obtain ⟨x, ξ⟩ := p
  exact and_congr_right fun hξ ↦ not_congr ⟨fun ⟨_, hU, _, _, hξΓ, hcone, _, hR⟩ ↦
    isInvertible_coefficient_principal_of_isEllipticOn hξ (mem_of_mem_nhds hU)
      (fun t ht ↦ hcone t ht ξ hξΓ) hR,
    exists_isEllipticOn_of_isInvertible_coefficient_principal hξ⟩

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
