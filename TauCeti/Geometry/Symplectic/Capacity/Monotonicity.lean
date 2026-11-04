/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Geometry.Symplectic.Capacity.Relative
public import TauCeti.Geometry.Symplectic.Hamiltonian.AlmostExistence
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Topology.Homotopy.AddCircle

/-!
# The Hofer–Zehnder monotonicity argument

Let `σ` be a nondegenerate two-form on a finite-dimensional manifold `M`, let `F : M → ℝ` be smooth
with compact sublevel sets `{F ≤ s}`, and let `Z ⊆ {F ≤ a}`. The relative `π₁`-sensitive
Hofer–Zehnder capacities `c(s) = c°_HZ({F < s}, Z)` of the open sublevel sets increase with `s`
(`TauCeti.SmoothTwoForm.relContractibleHZCapacity_mono`). This file proves the two steps of the
argument of Hofer, Zehnder and Struwe which turn finiteness of `c(b)` into closed characteristics on
the levels of `F` in `(a, b)`.

**The monotonicity step.** Let `G` be `({F < s₁}, Z)`-admissible, and let `f : ℝ → ℝ` be a smooth
function with `0 ≤ f ≤ A`, equal to `A` on `(-∞, s₁]` and to `0` on `[s₂, ∞)`. Then
`H = G + f ∘ F` is a candidate for `c(s₃)`, `s₃ > s₂`, with maximum `max G + A`. The integral
curves of `X_H` either stay in `{F < s₁}`, where `X_H = X_G`, or lie in a level `F⁻¹(c)`, `c ≥ s₁`,
where `X_H = f'(c) X_F` (`TauCeti.SmoothTwoForm.IsNondegenerate.isMIntegralCurve_add_comp`). The
first kind are constant when they are fast and contractible, because `G` is admissible. So if
`max G + A > c(s₃)`, then `H` is not admissible, and some level `F⁻¹(c)` with `s₁ ≤ c ≤ s₂` carries
a closed characteristic, contractible in `M`, of period at most `sup |f'|`
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_hasContractibleClosedCharacteristicOfPeriodLE`).

**Almost every level.** A monotone function is differentiable almost everywhere. At a point `s`
where `c` is differentiable with derivative `L`, `c(s + η) < c(s) + (|L| + 1) η` for small `η > 0`,
so the monotonicity step applies with `A = (|L| + 2) η` and a cutoff `f` of slope at most a
constant times `A / η`. Hence for almost every `s ∈ (a, b)` there is a bound `K` such that every
interval `[s, s + δ]`, `δ > 0`, contains a level carrying a closed characteristic contractible in
`M` of period at most `K`
(`IsNondegenerate.ae_forall_exists_hasContractibleClosedCharacteristicOfPeriodLE`).
The bound `K` does not depend on `δ`, which is what allows passing to the limit `δ → 0` to obtain a
closed characteristic on the level `F⁻¹(s)` itself; that limit is not treated here.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.isMIntegralCurve_add_comp`: the dichotomy for the
  integral curves of `X_{G + f ∘ F}`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.exists_hasContractibleClosedCharacteristicOfPeriodLE`:
  the monotonicity step.
* `IsNondegenerate.ae_forall_exists_hasContractibleClosedCharacteristicOfPeriodLE`: closed
  characteristics of bounded period on levels arbitrarily close above almost every level.

## References

* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Section 4.2.
* M. Struwe, *Existence of periodic solutions of Hamiltonian systems on almost every energy
  surface*, Bol. Soc. Brasil. Mat. 20 (1990), 49–58.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.3.
-/

public section

noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ContDiff ENNReal Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E] {σ : SmoothTwoForm I M} {Z : Set M} {F G : M → ℝ} {f : ℝ → ℝ}

namespace IsNondegenerate

/-- **Orbits of a Hamiltonian enlarged along the levels of `F`.** Let `G` be supported in
`{F < s}`, let `f` be constant on `(-∞, s]`, and let `γ` be an integral curve of the Hamiltonian
vector field of `G + f ∘ F`. Either `γ` stays in `{F < s}` and is an integral curve of `X_G`, or it
lies in a level `F⁻¹(c)` with `c ≥ s`, along which `X_G` vanishes, and is an integral curve of
`f'(c) X_F`. -/
theorem isMIntegralCurve_add_comp (hσ : σ.IsNondegenerate) (hG : MDifferentiable I 𝓘(ℝ) G)
    (hF : MDifferentiable I 𝓘(ℝ) F) (hf : Differentiable ℝ f) {s : ℝ}
    (hGs : tsupport G ⊆ {x | F x < s}) (hfs : ∀ r ≤ s, f r = f s) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ (σ.hamiltonianVectorField (G + f ∘ F))) :
    ((∀ t, F (γ t) < s) ∧ IsMIntegralCurve γ (σ.hamiltonianVectorField G)) ∨
      ∃ c, s ≤ c ∧ (∀ t, F (γ t) = c) ∧ (∀ t, σ.hamiltonianVectorField G (γ t) = 0) ∧
        IsMIntegralCurve γ (deriv f c • σ.hamiltonianVectorField F) := by
  have hXH (x : M) : σ.hamiltonianVectorField (G + f ∘ F) x =
      σ.hamiltonianVectorField G x + deriv f (F x) • σ.hamiltonianVectorField F x := by
    rw [hamiltonianVectorField_add (hG x) ((hf _).comp_mdifferentiableAt (hF x)),
      hamiltonianVectorField_comp (hf _) (hF x)]
  -- `X_G` vanishes off the support of `G`, and `X_{f ∘ F}` vanishes on `{F < s}`.
  have hXG (x : M) (hx : x ∉ tsupport G) : σ.hamiltonianVectorField G x = 0 :=
    hamiltonianVectorField_eq_zero_of_eventuallyEq (c := 0)
      (notMem_tsupport_iff_eventuallyEq.1 hx)
  have hXf (x : M) (hx : F x < s) : deriv f (F x) • σ.hamiltonianVectorField F x = 0 := by
    rw [← hamiltonianVectorField_comp (hf _) (hF x)]
    refine hamiltonianVectorField_eq_zero_of_eventuallyEq (c := f s) ?_
    filter_upwards [(isOpen_lt hF.continuous continuous_const).mem_nhds hx] with y hy
    exact hfs _ (le_of_lt hy)
  by_cases hlt : ∀ t, F (γ t) < s
  · refine Or.inl ⟨hlt, fun t ↦ ?_⟩
    have h := hγ t
    rwa [hXH, hXf _ (hlt t), add_zero] at h
  push Not at hlt
  obtain ⟨t₀, ht₀⟩ := hlt
  -- Off the support of `G`, the field is `f'(F) X_F`, which is tangent to the levels of `F`. So
  -- the set of times at which `γ` lies in the level of `γ t₀`, which is off the support, is open.
  have hconst : ∀ t, F (γ t) = F (γ t₀) := by
    have hγc := hγ.continuous
    have hopen : IsOpen {t | F (γ t) = F (γ t₀)} := by
      refine isOpen_iff_mem_nhds.2 fun t ht ↦ ?_
      have hmem : γ t ∈ (tsupport G)ᶜ := fun h ↦ (hGs h).not_ge (ht.symm ▸ ht₀)
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1
        ((isClosed_tsupport G).isOpen_compl.preimage hγc) t hmem
      refine Filter.mem_of_superset (Metric.ball_mem_nhds t hε) fun u hu ↦ ?_
      have h := (hγ.isMIntegralCurveOn (Metric.ball t ε)).apply_eq_of_mvfderiv_apply_eq_zero
        Metric.isOpen_ball (convex_ball t ε).isPreconnected (fun v _ ↦ hF _) (fun v hv ↦ ?_)
        (Metric.mem_ball_self hε) hu
      · exact h.trans ht
      rw [hXH, hXG _ (hball hv), zero_add, map_smul,
        (hσ.isHamiltonianVectorField_hamiltonianVectorField F).mvfderiv_apply_self, smul_zero]
    have hclosed : IsClosed {t | F (γ t) = F (γ t₀)} :=
      isClosed_eq (hF.continuous.comp hγc) continuous_const
    have huniv := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨t₀, rfl⟩
    exact fun t ↦ (Set.ext_iff.1 huniv t).2 trivial
  have hXG' (t : ℝ) : σ.hamiltonianVectorField G (γ t) = 0 :=
    hXG _ fun h ↦ (hGs h).not_ge ((hconst t).symm ▸ ht₀)
  refine Or.inr ⟨F (γ t₀), ht₀, hconst, hXG', fun t ↦ ?_⟩
  have h : σ.hamiltonianVectorField (G + f ∘ F) (γ t) =
      (deriv f (F (γ t₀)) • σ.hamiltonianVectorField F) (γ t) := by
    rw [hXH, hXG', zero_add, hconst, Pi.smul_apply]
  rw [← h]
  exact hγ t

/-- If no level `F⁻¹(c)`, `s₁ ≤ c ≤ s₂`, carries a closed characteristic contractible in `M` of
period at most `K`, then `G + f ∘ F` is `({F < s₃}, Z)`-admissible, under the hypotheses of the
monotonicity step. -/
private theorem isRelContractibleHZAdmissible_add_comp (hσ : σ.IsNondegenerate)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) {s₁ s₂ s₃ A K : ℝ} (hs₁₂ : s₁ ≤ s₂) (hs₂₃ : s₂ < s₃)
    (hcpt : IsCompact {x | F x ≤ s₂}) (hint : {x | F x ≤ s₂} ⊆ I.interior M)
    (hne : ∃ x, s₂ < F x ∧ F x < s₃) (hZ : Z ⊆ {x | F x ≤ s₁})
    (hG : σ.IsRelContractibleHZAdmissible {x | F x < s₁} Z G) (hf : ContDiff ℝ ∞ f)
    (hf_nonneg : ∀ r, 0 ≤ f r) (hf_le : ∀ r, f r ≤ A) (hfA : ∀ r ≤ s₁, f r = A)
    (hf0 : ∀ r, s₂ ≤ r → f r = 0) (hK : ∀ r, |deriv f r| ≤ K)
    (hno : ∀ c ∈ Icc s₁ s₂, ¬σ.HasContractibleClosedCharacteristicOfPeriodLE univ F c K) :
    σ.IsRelContractibleHZAdmissible {x | F x < s₃} Z (G + f ∘ F) := by
  have hGs : tsupport G ⊆ {x | F x < s₁} :=
    hG.tsupport_subset_interior.trans interior_subset
  have hFc : Continuous F := hF.continuous
  -- The support of `H = G + f ∘ F` lies in `{F ≤ s₂}`.
  have hsupp : tsupport (G + f ∘ F) ⊆ {x | F x ≤ s₂} := by
    refine (tsupport_add G (f ∘ F)).trans (union_subset ?_ ?_)
    · exact hGs.trans fun x hx ↦ (le_of_lt hx).trans hs₁₂
    · refine closure_minimal (fun x hx ↦ ?_) (isClosed_le hFc continuous_const)
      by_contra h
      exact hx (hf0 _ (le_of_lt (not_le.1 h)))
  exact {
    contMDiff := hG.contMDiff.add (hf.comp_contMDiff hF)
    isCompact_tsupport := hcpt.of_isClosed_subset (isClosed_tsupport _) hsupp
    tsupport_subset_interior := by
      rw [(isOpen_lt hFc continuous_const).interior_eq]
      exact hsupp.trans fun x hx ↦ lt_of_le_of_lt hx hs₂₃
    tsupport_subset_interior_manifold := hsupp.trans hint
    nonneg := fun x ↦ add_nonneg (hG.nonneg x) (hf_nonneg _)
    exists_isOpen_eqOn_zero := by
      obtain ⟨x, hx₂, hx₃⟩ := hne
      refine ⟨{x | s₂ < F x ∧ F x < s₃}, (isOpen_lt continuous_const hFc).inter
        (isOpen_lt hFc continuous_const), ⟨x, hx₂, hx₃⟩, fun y hy ↦ hy.2, fun y hy ↦ ?_⟩
      have hy₁ : y ∉ tsupport G := fun h ↦ (hGs h).not_ge (hs₁₂.trans (le_of_lt hy.1))
      simp [image_eq_zero_of_notMem_tsupport hy₁, hf0 _ (le_of_lt hy.1)]
    isMaxOn := fun z hz ↦ isMaxOn_iff.2 fun y _ ↦ by
      simp only [Pi.add_apply, comp_apply, hfA _ (hZ hz)]
      exact add_le_add (isMaxOn_iff.1 (hG.isMaxOn z hz) y trivial) (hf_le _)
    eq_of_isMIntegralCurve := by
      intro T γ hT hT1 hγ hper hcontr t
      rcases hσ.isMIntegralCurve_add_comp (ContMDiff.mdifferentiable hG.contMDiff (by simp))
        (ContMDiff.mdifferentiable hF (by simp)) (hf.differentiable (by simp)) hGs
        (fun r hr ↦ (hfA r hr).trans (hfA s₁ le_rfl).symm) hγ with ⟨-, hγG⟩ | ⟨c, hc₁, hlev, -, hγc⟩
      · exact hG.eq_of_isMIntegralCurve T γ hT hT1 hγG hper hcontr t
      by_cases hd : deriv f c = 0
      · exact IsMIntegralCurve.apply_eq_of_forall_eq_zero hγc (fun u ↦ by simp [hd]) 0 t
      -- A nonconstant orbit on the level `c` is a closed characteristic of `F` of period
      -- `T |f'(c)| ≤ K`, which is excluded.
      by_contra hne_t
      have hc₂ : c ≤ s₂ := by
        by_contra h
        refine hd ((Filter.EventuallyEq.deriv_eq (f₁ := f) (f := fun _ ↦ (0 : ℝ)) ?_).trans
          (deriv_const c 0))
        filter_upwards [Ioi_mem_nhds (not_le.1 h)] with r hr using hf0 r (le_of_lt hr)
      obtain ⟨g, hg, hgγ⟩ := hcontr
      have ha : (deriv f c)⁻¹ ≠ 0 := inv_ne_zero hd
      obtain ⟨g', hg', hgg'⟩ := hg.exists_addCircle_comp_mul hT.ne' ha
      have hgγ' (u : ℝ) : g' u = γ (u * (deriv f c)⁻¹) := by rw [hgg', hgγ]
      have hγF : IsMIntegralCurve (γ ∘ (· * (deriv f c)⁻¹)) (σ.hamiltonianVectorField F) := by
        have h := IsMIntegralCurve.comp_mul hγc (deriv f c)⁻¹
        rwa [smul_smul, inv_mul_cancel₀ hd, one_smul] at h
      refine hno c ⟨hc₁, hc₂⟩ (hasContractibleClosedCharacteristicOfPeriodLE_iff.2
        ⟨T / |(deriv f c)⁻¹|, γ ∘ (· * (deriv f c)⁻¹),
        div_pos hT (abs_pos.2 ha), ?_, hγF, fun u ↦ ?_, ⟨t * deriv f c, ?_⟩,
        fun u ↦ hlev _,
        (⟨fun p ↦ ⟨g' p, trivial⟩, by fun_prop⟩ : C(AddCircle (T / |(deriv f c)⁻¹|), univ)),
        ?_, fun u ↦ hgγ' u⟩)
      · rw [abs_inv, div_inv_eq_mul]
        calc T * |deriv f c| ≤ 1 * K := mul_le_mul hT1 (hK c) (abs_nonneg _) zero_le_one
          _ = K := one_mul K
      · simp only [comp_apply, ← hgγ', AddCircle.coe_add_period]
      · simpa [mul_inv_cancel_right₀ hd] using hne_t
      · exact hg'.comp_right (⟨fun p ↦ ⟨p, trivial⟩, by fun_prop⟩ : C(M, (univ : Set M))) }

omit [FiniteDimensional ℝ E] in
/-- The maximum of `G + f ∘ F` is `max G + A`, when `G` is `({F < s₁}, Z)`-admissible and `f ≤ A`
with equality on `(-∞, s₁]`: the maximum of `G` is attained in `{F < s₁}`. -/
private theorem iSup_add_comp {s₁ A : ℝ}
    (hG : σ.IsRelContractibleHZAdmissible {x | F x < s₁} Z G)
    (hf_le : ∀ r, f r ≤ A) (hfA : ∀ r ≤ s₁, f r = A) :
    (⨆ x, (G + f ∘ F) x) = (⨆ x, G x) + A := by
  have hGc : Continuous G := hG.contMDiff.continuous
  have hGbdd : BddAbove (range G) := hGc.bddAbove_range_of_hasCompactSupport hG.isCompact_tsupport
  have hGs : tsupport G ⊆ {x | F x < s₁} :=
    hG.tsupport_subset_interior.trans interior_subset
  -- The maximum of `G` is attained at a point of `{F < s₁}`, where `G + f ∘ F = G + A`.
  have hHle (x : M) : (G + f ∘ F) x ≤ (⨆ x, G x) + A :=
    add_le_add (le_ciSup hGbdd x) (hf_le _)
  obtain ⟨U, -, ⟨u, hu⟩, hUs, hU0⟩ := hG.exists_isOpen_eqOn_zero
  have : Nonempty M := ⟨u⟩
  obtain ⟨x₀, hx₀⟩ := hGc.exists_forall_ge_of_hasCompactSupport hG.isCompact_tsupport
  have hsup : (⨆ x, G x) = G x₀ := le_antisymm (ciSup_le hx₀) (le_ciSup hGbdd x₀)
  obtain ⟨y, hy, hFy⟩ : ∃ y, G y = G x₀ ∧ F y < s₁ := by
    by_cases h0 : G x₀ = 0
    · exact ⟨u, (hU0 hu).trans h0.symm, hUs hu⟩
    · exact ⟨x₀, rfl, hGs (subset_tsupport G h0)⟩
  have hHy : (G + f ∘ F) y = (⨆ x, G x) + A := by
    simp only [Pi.add_apply, comp_apply, hy, hsup, hfA _ (le_of_lt hFy)]
  have hHsup : (⨆ x, (G + f ∘ F) x) = (⨆ x, G x) + A :=
    le_antisymm (ciSup_le hHle) (hHy ▸ le_ciSup ⟨_, forall_mem_range.2 hHle⟩ y)
  exact hHsup


/-- **The Hofer–Zehnder monotonicity step.** Let `G` be `({F < s₁}, Z)`-admissible, with
`Z ⊆ {F ≤ s₁}`, and let `f` be a smooth function with `0 ≤ f ≤ A`, equal to `A` on `(-∞, s₁]` and
to `0` on `[s₂, ∞)`, with `|f'| ≤ K`. Suppose that `{F ≤ s₂}` is compact and lies in the interior
of `M`, that some value of `F` lies in `(s₂, s₃)`, and that `c°_HZ({F < s₃}, Z) < max G + A`.
Then some level `F⁻¹(c)` with `s₁ ≤ c ≤ s₂` carries a closed characteristic, contractible in `M`,
of period at most `K`. -/
theorem exists_hasContractibleClosedCharacteristicOfPeriodLE (hσ : σ.IsNondegenerate)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) {s₁ s₂ s₃ A K : ℝ} (hs₁₂ : s₁ ≤ s₂) (hs₂₃ : s₂ < s₃)
    (hcpt : IsCompact {x | F x ≤ s₂}) (hint : {x | F x ≤ s₂} ⊆ I.interior M)
    (hne : ∃ x, s₂ < F x ∧ F x < s₃) (hZ : Z ⊆ {x | F x ≤ s₁})
    (hG : σ.IsRelContractibleHZAdmissible {x | F x < s₁} Z G) (hf : ContDiff ℝ ∞ f)
    (hf_nonneg : ∀ r, 0 ≤ f r) (hf_le : ∀ r, f r ≤ A) (hfA : ∀ r ≤ s₁, f r = A)
    (hf0 : ∀ r, s₂ ≤ r → f r = 0) (hK : ∀ r, |deriv f r| ≤ K)
    (hcap : σ.relContractibleHZCapacity {x | F x < s₃} Z < ENNReal.ofReal ((⨆ x, G x) + A)) :
    ∃ c ∈ Icc s₁ s₂, σ.HasContractibleClosedCharacteristicOfPeriodLE univ F c K := by
  by_contra hno
  push Not at hno
  exact ((iSup_add_comp hG hf_le hfA ▸ (isRelContractibleHZAdmissible_add_comp hσ hF hs₁₂ hs₂₃
    hcpt hint hne hZ hG hf hf_nonneg hf_le hfA hf0 hK hno).ofReal_iSup_le_relContractibleHZCapacity)
    ).not_gt hcap

/-- **Closed characteristics near almost every level.** Let `F` be smooth, with `{F < b}` in the
interior of `M` and compact sublevel sets `{F ≤ s}` for `s < b`, let every value in `(a, b)` be
attained by `F`, and let `Z ⊆ {F ≤ a}`. If the relative capacity
`c°_HZ({F < b}, Z)` is finite, then for almost every `s ∈ (a, b)` there is a bound `K` such that
every interval `[s, s + δ]`, `δ > 0`, contains a level of `F` carrying a closed characteristic,
contractible in `M`, of period at most `K`. -/
theorem ae_forall_exists_hasContractibleClosedCharacteristicOfPeriodLE (hσ : σ.IsNondegenerate)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) {a b : ℝ} (hcpt : ∀ s < b, IsCompact {x | F x ≤ s})
    (hint : {x | F x < b} ⊆ I.interior M) (hrange : Ioo a b ⊆ range F)
    (hZ : Z ⊆ {x | F x ≤ a}) (hcap : σ.relContractibleHZCapacity {x | F x < b} Z ≠ (∞ : ℝ≥0∞)) :
    ∀ᵐ s, s ∈ Ioo a b → ∃ K, ∀ δ > 0, ∃ c ∈ Icc s (s + δ),
      σ.HasContractibleClosedCharacteristicOfPeriodLE univ F c K := by
  have hFc : Continuous F := hF.continuous
  have hfin (u : ℝ) : σ.relContractibleHZCapacity {x | F x < min u b} Z ≠ (∞ : ℝ≥0∞) :=
    ne_top_of_le_ne_top hcap (relContractibleHZCapacity_mono
      (ofPred_subset_ofPred.2 fun x hx ↦ lt_of_lt_of_le hx (min_le_right u b)) subset_rfl)
  -- The capacities of the sublevel sets, a monotone function of the level.
  set φ : ℝ → ℝ := fun u ↦ (σ.relContractibleHZCapacity {x | F x < min u b} Z).toReal with hφ
  have hmono : Monotone φ := fun u v huv ↦ ENNReal.toReal_mono (hfin v)
    (relContractibleHZCapacity_mono
      (ofPred_subset_ofPred.2 fun x hx ↦ lt_of_lt_of_le hx (min_le_min_right b huv)) subset_rfl)
  have hφeq {u : ℝ} (hu : u ≤ b) :
      σ.relContractibleHZCapacity {x | F x < u} Z = ENNReal.ofReal (φ u) := by
    have h := ENNReal.ofReal_toReal (hfin u)
    rw [min_eq_left hu] at h
    rw [hφ]
    simp only [min_eq_left hu]
    exact h.symm
  obtain ⟨Mρ, hMρ⟩ := Continuous.bounded_above_of_compact_support
    ((Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl)
    Real.smoothTransition.hasCompactSupport_deriv
  filter_upwards [hmono.ae_differentiableAt] with s hs hsI
  -- The right difference quotients of `φ` at `s` are eventually below `|φ'(s)| + 1`.
  set L := deriv φ s
  have hslope : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (φ (s + t) - φ s) < |L| + 1 :=
    ((hasDerivAt_iff_tendsto_slope_zero.1 hs.hasDerivAt).mono_left
      (nhdsWithin_mono _ fun t ht ↦ mem_compl_singleton_iff.2 (ne_of_gt ht))).eventually
      (gt_mem_nhds (by linarith [le_abs_self L]))
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 hslope
  refine ⟨2 * Mρ * (|L| + 2), fun δ hδ ↦ ?_⟩
  -- Work at a scale `η ≤ δ` below `δ₀` and with `s + η < b`.
  set η := min δ (min (δ₀ / 2) ((b - s) / 2)) with hη
  have hη0 : 0 < η := lt_min hδ (lt_min (by linarith) (by linarith [hsI.2]))
  have hηδ : η ≤ δ := min_le_left _ _
  have hηδ₀ : η < δ₀ := (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (by linarith))
  have hηb : s + η < b := by
    have : η ≤ (b - s) / 2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith [hsI.2]
  have hη2 : 0 < η / 2 := by linarith
  -- A level of `F` in each nonempty subinterval of `(a, b)`.
  have hval {r : ℝ} (hr : r ∈ Ioo a b) : ∃ x, F x = r := hrange hr
  -- An admissible `G` for `{F < s}` with `max G > c(s) - η`.
  obtain ⟨x₁, hx₁⟩ := hval (r := (a + s) / 2) ⟨by linarith [hsI.1], by linarith [hsI.1, hsI.2]⟩
  obtain ⟨G, hG, hGsup⟩ := exists_isRelContractibleHZAdmissible_lt_iSup (σ := σ)
    (V := {x | F x < s}) (Z := Z)
    ⟨{x | F x < s}, isOpen_lt hFc continuous_const,
      ⟨x₁, show F x₁ < s by rw [hx₁]; linarith [hsI.1]⟩, subset_rfl⟩
    (by rw [hφeq hsI.2.le]; exact ENNReal.ofReal_ne_top) hη0
  rw [hφeq hsI.2.le, ENNReal.toReal_ofReal (by positivity)] at hGsup
  -- The cutoff `f`, stepping down from `A = (|L| + 2) η` to `0` across `[s, s + η / 2]`.
  set A := (|L| + 2) * η with hA
  have hA0 : 0 ≤ A := by positivity
  set f : ℝ → ℝ := fun r ↦ A * (1 - Real.smoothTransition ((r - s) / (η / 2))) with hf
  have hfderiv (r : ℝ) : HasDerivAt f
      (A * -(deriv Real.smoothTransition ((r - s) / (η / 2)) * (1 / (η / 2)))) r :=
    ((((hasDerivAt_id r).sub_const s).div_const (η / 2)).smoothTransition.const_sub 1).const_mul A
  obtain ⟨c, hc, hcc⟩ := hσ.exists_hasContractibleClosedCharacteristicOfPeriodLE hF
    (s₁ := s) (s₂ := s + η / 2) (s₃ := s + η) (A := A) (K := 2 * Mρ * (|L| + 2)) (f := f)
    (by linarith) (by linarith) (hcpt _ (by linarith)) (fun x (hx : F x ≤ s + η / 2) ↦
      hint (show F x < b by linarith))
    (by
      obtain ⟨x, hx⟩ := hval (r := s + 3 * η / 4) ⟨by linarith [hsI.1], by linarith⟩
      exact ⟨x, by rw [hx]; linarith, by rw [hx]; linarith⟩)
    (fun z hz ↦ show F z ≤ s from (show F z ≤ a from hZ hz).trans hsI.1.le) hG
    (contDiff_const.mul (contDiff_const.sub (Real.smoothTransition.contDiff.comp
      (by fun_prop))))
    (fun r ↦ mul_nonneg hA0 (sub_nonneg.2 (Real.smoothTransition.le_one _)))
    (fun r ↦ mul_le_of_le_one_right hA0 (sub_le_self _ (Real.smoothTransition.nonneg _)))
    (fun r hr ↦ by
      simp only [hf]
      rw [Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hr) hη2.le), sub_zero, mul_one])
    (fun r hr ↦ by
      simp only [hf]
      rw [Real.smoothTransition.one_of_one_le
        ((one_le_div hη2).2 (by linarith : η / 2 ≤ r - s)), sub_self, mul_zero])
    (fun r ↦ by
      rw [(hfderiv r).deriv, abs_mul, abs_of_nonneg hA0, abs_neg, abs_mul,
        abs_of_pos (one_div_pos.2 hη2)]
      calc A * (|deriv Real.smoothTransition ((r - s) / (η / 2))| * (1 / (η / 2)))
          ≤ A * (Mρ * (1 / (η / 2))) := by
            gcongr
            exact hMρ _
        _ = 2 * Mρ * (|L| + 2) := by rw [hA]; field_simp)
    (by
      -- `c(s + η) < c(s) + (|L| + 1) η < max G + A`.
      have h := hδ₀' ⟨hη0, hηδ₀⟩
      rw [smul_eq_mul, inv_mul_lt_iff₀ hη0] at h
      rw [hφeq hηb.le]
      have hφ0 : 0 ≤ φ (s + η) := ENNReal.toReal_nonneg
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by rw [hA]; linarith))
  exact ⟨c, ⟨hc.1, by linarith [hc.2]⟩, hcc⟩

end IsNondegenerate

end SmoothTwoForm

end TauCeti
