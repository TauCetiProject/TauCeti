/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.SmoothTransition
public import TauCeti.Geometry.Symplectic.Liouville.ClosedCharacteristic
public import TauCeti.Geometry.Symplectic.Liouville.Graph.Level
public import TauCeti.Geometry.Symplectic.Liouville.Graph.Region
import TauCeti.Geometry.Manifold.ContMDiff.Log

/-!
# A smooth defining function of a Liouville graph

Let `M` be a completion of the Liouville domain `W ⊆ M` (`TauCeti.IsLiouvilleCompletion`), with
Liouville field `Z`, Liouville flow `ψ` and radial coordinate `r`, let `ι : S → M` be a smooth
injective immersion of a compact manifold of one dimension less onto the frontier `∂W`, and let
`f > 1` be smooth on `S`. The Liouville graph `Σ_f = {ψ_{log f(s)}(ι s)}`
(`TauCeti.liouvilleGraph`) is the level `1` of its defining function `F`
(`TauCeti.liouvilleGraphFunction`), which is `r / f(s)` at the point `ψ_t(ι s)` of the cylindrical
end. But `F` is only smooth outside `W`, and on `W` its values are not meaningful. An almost
existence theorem, such as Theorem A of Barraud, Damian, Humilière and Oancea, applies to a smooth
function on all of `M` with compact sublevel sets and a regular level.

This file constructs such a function. Fix levels `a < b < 0` with `e^{-a} < f`. The function
`TauCeti.smoothLogLiouvilleGraphFunction Z W ι f a b` is `log F` cut off below at `a`:

`G = a + τ((log F - a) / (b - a)) (log F - a)`,

for the smooth transition `τ` from `0` to `1` (`Real.smoothTransition`), that is, the smooth lower
truncation `TauCeti.smoothLowerTruncation a b` applied to `log F`. Since `log F < a` on a
neighbourhood of `W`, where `G` is the constant `a`, and `log F` is smooth outside `W`, the function
`G` is smooth on all of `M`
(`TauCeti.IsLiouvilleCompletion.contMDiff_smoothLogLiouvilleGraphFunction`). It agrees with `log F`
where `log F ≥ b` (`TauCeti.smoothLogLiouvilleGraphFunction_eq_of_right_le`), a neighbourhood of
the graph, and it has:

* **compact sublevel sets**
  (`TauCeti.IsLiouvilleCompletion.isCompact_setOf_smoothLogLiouvilleGraphFunction_le`);
* **the graph as its level `0`**
  (`TauCeti.IsLiouvilleCompletion.setOf_smoothLogLiouvilleGraphFunction_eq_zero`);
* **the region bounded by the graph as its sublevel set `{G < 0}`**
  (`TauCeti.IsLiouvilleCompletion.setOf_smoothLogLiouvilleGraphFunction_lt_zero`), the open set
  `W ∪ {ψ_t(ι s) | t < log f(s)}` (`TauCeti.liouvilleGraphRegion`), which contains `W` and
  deformation retracts onto it;
* **the Liouville flow as a translation** above `b`, `G(ψ_t x) = G(x) + t`
  (`TauCeti.IsLiouvilleCompletion.smoothLogLiouvilleGraphFunction_flowOf`), so that every value
  above `b`, `0` in particular, is regular
  (`TauCeti.IsLiouvilleCompletion.isRegularValue_smoothLogLiouvilleGraphFunction`).

So `e^G` is a smooth function with compact sublevel sets whose regular level `1` is `Σ_f`, which
bounds `{e^G < 1}`, and which equals `r / f` near `Σ_f`: the function `F_α` of the graph
construction in the proof of Corollary E of Barraud, Damian, Humilière and Oancea.

Since the Liouville flow translates `G` near its level `0`, the almost existence property of that
level gives a closed characteristic on the graph
(`IsLiouvilleCompletion.hasContractibleClosedCharacteristic_univ_smoothLogLiouvilleGraphFunction`
in `TauCeti`), and that closed characteristic comes from a closed Reeb orbit of the contact form
`f ι^* α` whose loop on `∂W` is contractible in `M`
(`IsLiouvilleCompletion.exists_isMIntegralCurve_reebVectorField_of_hasContractibleAlmostExistence`
in `TauCeti`).
This is the step of Corollary E from almost existence to closed Reeb orbits, for the contact forms
`f ι^* α`.

## Main definitions

* `TauCeti.smoothLogLiouvilleGraphFunction Z W ι f a b`: the logarithm of the defining function of
  the Liouville graph of `f`, cut off below at `a`.

## Main results

In the namespace `TauCeti.IsLiouvilleCompletion`:

* `contMDiff_smoothLogLiouvilleGraphFunction`: it is smooth.
* `isCompact_setOf_smoothLogLiouvilleGraphFunction_le`: its sublevel sets are compact.
* `setOf_smoothLogLiouvilleGraphFunction_eq_zero`: its level `0` is the Liouville graph.
* `setOf_smoothLogLiouvilleGraphFunction_lt_zero`: its sublevel set `{G < 0}` is the region
  bounded by the graph.
* `isRegularValue_smoothLogLiouvilleGraphFunction`: its values above `b` are regular.
* `exists_isMIntegralCurve_reebVectorField_of_hasContractibleAlmostExistence`: if its level `0`
  has the contractible almost existence property in `M`, the contact form `f ι^* α` has a closed
  Reeb orbit `γ` whose loop `ι ∘ γ` is contractible in `M`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Corollary E and its proof (the hypersurface
  `Σ_α` as the regular level of a smooth function with compact sublevel sets).
* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Section 4.2 (existence of closed characteristics on hypersurfaces of contact type from the
  almost existence theorem).
-/

public section

open Function Module Set
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {S : Type*}
  {Z : (x : M) → TangentSpace I x} {W : Set M} {ι : S → M} {f : S → ℝ} {a b c : ℝ} {x : M}

/-! ### The smoothed logarithm of the defining function -/

variable (Z W ι f) in
/-- **A smooth defining function of the Liouville graph** of `f` over `ι`, on a completion of the
Liouville domain `W`: the logarithm of the defining function `F` of the graph
(`TauCeti.liouvilleGraphFunction`), cut off below at the level `a` by the smooth lower truncation
`TauCeti.smoothLowerTruncation a b`, `a + τ((log F - a) / (b - a)) (log F - a)` for the smooth
transition `τ` from `0` to `1`. It is `log F` where `log F ≥ b`, the constant `a` where
`log F ≤ a`, and below `b` where `log F < b`. For levels `a < b < 0` with
`e^{-a} < f`, it is smooth with compact sublevel sets
(`TauCeti.IsLiouvilleCompletion.contMDiff_smoothLogLiouvilleGraphFunction`,
`TauCeti.IsLiouvilleCompletion.isCompact_setOf_smoothLogLiouvilleGraphFunction_le`), and its
regular level `0` is the Liouville graph
(`TauCeti.IsLiouvilleCompletion.setOf_smoothLogLiouvilleGraphFunction_eq_zero`). -/
noncomputable def smoothLogLiouvilleGraphFunction [Nonempty S] (a b : ℝ) (x : M) : ℝ :=
  smoothLowerTruncation a b (Real.log (liouvilleGraphFunction Z W ι f x))

theorem smoothLogLiouvilleGraphFunction_def [Nonempty S] (a b : ℝ) (x : M) :
    smoothLogLiouvilleGraphFunction Z W ι f a b x =
      smoothLowerTruncation a b (Real.log (liouvilleGraphFunction Z W ι f x)) :=
  (rfl)

private theorem pos_of_exp_neg_lt (ha : ∀ s, Real.exp (-a) < f s) (s : S) : 0 < f s :=
  (Real.exp_pos _).trans (ha s)

private theorem one_lt_of_exp_neg_lt (ha : ∀ s, Real.exp (-a) < f s) (ha₀ : a < 0) (s : S) :
    1 < f s :=
  (Real.one_lt_exp_iff.2 (neg_pos.2 ha₀)).trans (ha s)

variable [Nonempty S]

/-- Where `log F ≥ b`, the smoothed logarithm of the defining function `F` of the Liouville graph
is `log F`. -/
theorem smoothLogLiouvilleGraphFunction_eq_of_right_le (hab : a < b)
    (hx : b ≤ Real.log (liouvilleGraphFunction Z W ι f x)) :
    smoothLogLiouvilleGraphFunction Z W ι f a b x =
      Real.log (liouvilleGraphFunction Z W ι f x) :=
  smoothLowerTruncation_of_right_le hab hx

/-- Where `log F ≤ a`, the smoothed logarithm of the defining function `F` of the Liouville graph is
the constant `a`. -/
theorem smoothLogLiouvilleGraphFunction_eq_of_le_left (hab : a ≤ b)
    (hx : Real.log (liouvilleGraphFunction Z W ι f x) ≤ a) :
    smoothLogLiouvilleGraphFunction Z W ι f a b x = a :=
  smoothLowerTruncation_of_le_left hab hx

/-- The smoothed logarithm of the defining function of the Liouville graph is at least `a`. -/
theorem le_smoothLogLiouvilleGraphFunction (hab : a ≤ b) (x : M) :
    a ≤ smoothLogLiouvilleGraphFunction Z W ι f a b x :=
  le_smoothLowerTruncation hab _

/-- Where `log F < b`, the smoothed logarithm of the defining function `F` of the Liouville graph is
below `b`. -/
theorem smoothLogLiouvilleGraphFunction_lt_of_lt (hab : a < b)
    (hx : Real.log (liouvilleGraphFunction Z W ι f x) < b) :
    smoothLogLiouvilleGraphFunction Z W ι f a b x < b :=
  smoothLowerTruncation_lt_of_lt hab hx

/-- Where the smoothed logarithm of the defining function `F` of the Liouville graph exceeds `b`,
it is `log F`. -/
theorem smoothLogLiouvilleGraphFunction_eq_of_lt (hab : a < b)
    (hx : b < smoothLogLiouvilleGraphFunction Z W ι f a b x) :
    smoothLogLiouvilleGraphFunction Z W ι f a b x = Real.log (liouvilleGraphFunction Z W ι f x) :=
  smoothLogLiouvilleGraphFunction_eq_of_right_le hab
    (not_lt.1 fun hlt ↦ (smoothLogLiouvilleGraphFunction_lt_of_lt hab hlt).not_gt hx)

/-- Above `b`, the sublevel sets of the smoothed logarithm of the defining function `F` of the
Liouville graph are those of `log F`. -/
theorem smoothLogLiouvilleGraphFunction_lt_iff (hab : a < b) (hc : b ≤ c) :
    smoothLogLiouvilleGraphFunction Z W ι f a b x < c ↔
      Real.log (liouvilleGraphFunction Z W ι f x) < c :=
  smoothLowerTruncation_lt_iff hab hc

/-- Above `b`, the levels of the smoothed logarithm of the defining function `F` of the Liouville
graph are those of `log F`. -/
theorem smoothLogLiouvilleGraphFunction_eq_iff (hab : a < b) (hc : b ≤ c) :
    smoothLogLiouvilleGraphFunction Z W ι f a b x = c ↔
      Real.log (liouvilleGraphFunction Z W ι f x) = c :=
  smoothLowerTruncation_eq_iff hab hc

namespace IsLiouvilleCompletion

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
  {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1}

section Domain

variable (h : IsLiouvilleCompletion ω α W) (hZ : RoughForm.interior Z ω.val = α.val)
  (ha : ∀ s, Real.exp (-a) < f s)
include h hZ ha

/-- **On the Liouville domain, the smoothed logarithm of the defining function of the Liouville
graph is the constant `a`**, when `e^{-a} < f`. -/
theorem smoothLogLiouvilleGraphFunction_of_mem (hab : a ≤ b) (hx : x ∈ W) :
    smoothLogLiouvilleGraphFunction Z W ι f a b x = a := by
  refine smoothLogLiouvilleGraphFunction_eq_of_le_left hab ?_
  obtain ⟨s, hs⟩ := exists_liouvilleGraphFunction_eq_div Z W ι f x
  rw [hs, (h.liouvilleRadialCoordinate_eq_one_iff hZ).2 hx, one_div, Real.log_inv]
  linarith [(Real.lt_log_iff_exp_lt (pos_of_exp_neg_lt ha s)).2 (ha s)]

variable (hinj : Injective ι) (hιW : range ι = frontier W)
include hinj hιW

/-- **The Liouville flow translates the smoothed logarithm of the defining function of the
Liouville graph above `b`**: if `b < G(x)` and `b < G(x) + t`, then `G(ψ_t x) = G(x) + t`, when
`e^{-a} < f` and `a < b`. -/
theorem smoothLogLiouvilleGraphFunction_flowOf (hab : a < b) {t : ℝ}
    (hx : b < smoothLogLiouvilleGraphFunction Z W ι f a b x)
    (hxt : b < smoothLogLiouvilleGraphFunction Z W ι f a b x + t) :
    smoothLogLiouvilleGraphFunction Z W ι f a b (flowOf Z t x) =
      smoothLogLiouvilleGraphFunction Z W ι f a b x + t := by
  have hf₀ := pos_of_exp_neg_lt ha
  have hιW' : ∀ s, ι s ∈ frontier W := range_subset_iff.1 hιW.le
  -- The point lies outside `W`, where the function is the constant `a < b`.
  have hxW : x ∈ Wᶜ := fun hxW ↦ by
    rw [h.smoothLogLiouvilleGraphFunction_of_mem hZ ha hab.le hxW] at hx
    exact hab.not_gt hx
  rw [smoothLogLiouvilleGraphFunction_eq_of_lt hab hx] at hxt ⊢
  obtain ⟨t₀, ht₀, s, rfl⟩ := h.exists_flowOf_eq_of_notMem hZ hιW.ge hxW
  -- On the end, `log F (ψ_τ (ι s)) = τ - log f(s)` for `τ > 0`.
  have hlog {τ : ℝ} (hτ : 0 < τ) :
      Real.log (liouvilleGraphFunction Z W ι f (flowOf Z τ (ι s))) = τ - Real.log (f s) := by
    rw [h.liouvilleGraphFunction_flowOf hZ hιW' hinj hτ, Real.log_div (Real.exp_pos τ).ne'
      (hf₀ s).ne', Real.log_exp]
  rw [hlog ht₀] at hxt ⊢
  have hfs : -a < Real.log (f s) := (Real.lt_log_iff_exp_lt (hf₀ s)).2 (ha s)
  have htt : 0 < t + t₀ := by linarith
  rw [h.flowOf_flowOf hZ,
    smoothLogLiouvilleGraphFunction_eq_of_right_le hab (by rw [hlog htt]; linarith), hlog htt]
  ring

omit ha in
/-- **The level `0` of the smoothed logarithm of the defining function is the Liouville graph**,
for levels `a < b ≤ 0` and `1 < f`. -/
theorem setOf_smoothLogLiouvilleGraphFunction_eq_zero (hf1 : ∀ s, 1 < f s) (hab : a < b)
    (hb : b ≤ 0) :
    {x | smoothLogLiouvilleGraphFunction Z W ι f a b x = 0} = range (liouvilleGraph Z ι f) := by
  have hf₀ (s : S) : 0 < f s := one_pos.trans (hf1 s)
  ext x
  rw [mem_ofPred_eq, smoothLogLiouvilleGraphFunction_eq_iff hab hb,
    ← h.liouvilleGraphFunction_eq_one_iff hZ hinj hιW hf1]
  exact ⟨Real.eq_one_of_pos_of_log_eq_zero (liouvilleGraphFunction_pos hf₀ _),
    fun h1 ↦ by rw [h1, Real.log_one]⟩

omit ha in
/-- **The sublevel set `{G < 0}` of the smoothed logarithm of the defining function is the region
bounded by the Liouville graph**, `W ∪ {ψ_t(ι s) | t < log f(s)}`, for levels `a < b ≤ 0` and
`1 < f`. -/
theorem setOf_smoothLogLiouvilleGraphFunction_lt_zero (hf1 : ∀ s, 1 < f s) (hab : a < b)
    (hb : b ≤ 0) :
    {x | smoothLogLiouvilleGraphFunction Z W ι f a b x < 0} = liouvilleGraphRegion Z W ι f := by
  have hf₀ (s : S) : 0 < f s := one_pos.trans (hf1 s)
  have hιW' : ∀ s, ι s ∈ frontier W := range_subset_iff.1 hιW.le
  ext x
  rw [mem_ofPred_eq, smoothLogLiouvilleGraphFunction_lt_iff hab hb,
    Real.log_neg_iff (liouvilleGraphFunction_pos hf₀ _), mem_liouvilleGraphRegion]
  by_cases hxW : x ∈ W
  · simp [hxW, h.liouvilleGraphFunction_lt_one_of_mem hZ hf1 hxW]
  obtain ⟨t₀, ht₀, s, rfl⟩ := h.exists_flowOf_eq_of_notMem hZ hιW.ge hxW
  simp only [hxW, false_or]
  rw [h.liouvilleGraphFunction_flowOf hZ hιW' hinj ht₀, div_lt_one (hf₀ s)]
  refine ⟨fun hlt ↦ ⟨t₀, s, (Real.lt_log_iff_exp_lt (hf₀ s)).2 hlt, rfl⟩, ?_⟩
  rintro ⟨t, s', hts', heq⟩
  -- The flow-out map is injective, so `(t, s') = (t₀, s)`.
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj
    (h.injective_flowOf_comp hZ (h.isCompleteVectorField hZ) hinj hιW' heq)
  exact (Real.lt_log_iff_exp_lt (hf₀ _)).1 hts'

end Domain

section Smooth

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [J.Boundaryless] [TopologicalSpace S] [ChartedSpace H' S]
  [IsManifold J (⊤ : ℕ∞) S] [CompactSpace S]
  (h : IsLiouvilleCompletion ω α W) (hZ : RoughForm.interior Z ω.val = α.val)
  (hι : ContMDiff J I (⊤ : ℕ∞) ι) (hιs : ∀ s, Injective (mfderiv J I ι s)) (hinj : Injective ι)
  (hιW : range ι = frontier W) (hdim : finrank ℝ E' + 1 = finrank ℝ E)
  (hf : ContMDiff J 𝓘(ℝ) (⊤ : ℕ∞) f) (ha : ∀ s, Real.exp (-a) < f s)
include h hZ hι hιs hinj hιW hdim hf ha

/-- **The smoothed logarithm of the defining function of the Liouville graph is smooth.** Let `ι`
be a smooth injective immersion of a compact manifold of one dimension less onto the frontier of
the Liouville domain, `f` smooth and `e^{-a} < f`. Then the logarithm of the defining function `F`
of the Liouville graph of `f`, cut off below at `a`, is smooth on `M`. -/
theorem contMDiff_smoothLogLiouvilleGraphFunction (hab : a ≤ b) :
    ContMDiff I 𝓘(ℝ) (⊤ : ℕ∞) (smoothLogLiouvilleGraphFunction Z W ι f a b) := by
  have hf₀ := pos_of_exp_neg_lt ha
  -- A uniform bound `e^{-a} < m ≤ f` on the compact `S`.
  obtain ⟨m, hm, hmf⟩ := isCompact_univ.exists_forall_le' hf.continuous.continuousOn
    fun s (_ : s ∈ univ) ↦ ha s
  have hma : 1 < m * Real.exp a := by
    calc (1 : ℝ) = Real.exp (-a) * Real.exp a := by
          rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      _ < m * Real.exp a := mul_lt_mul_of_pos_right hm (Real.exp_pos a)
  intro x
  by_cases hx : liouvilleRadialCoordinate Z W x < m * Real.exp a
  · -- Near `x`, `F ≤ r / m < e^a`, so the function is the constant `a`.
    have hev : smoothLogLiouvilleGraphFunction Z W ι f a b =ᶠ[𝓝 x] fun _ ↦ a := by
      filter_upwards [(isOpen_lt (h.continuous_liouvilleRadialCoordinate hZ)
        continuous_const).mem_nhds hx] with y (hy : _ < _)
      refine smoothLogLiouvilleGraphFunction_eq_of_le_left hab
        ((Real.log_le_iff_le_exp (liouvilleGraphFunction_pos hf₀ _)).2 ?_)
      obtain ⟨s, hs⟩ := exists_liouvilleGraphFunction_eq_div Z W ι f y
      rw [hs, div_le_iff₀ (hf₀ s)]
      have := hmf s (mem_univ _)
      nlinarith [Real.exp_pos a]
    exact contMDiffAt_const.congr_of_eventuallyEq hev
  · -- Outside `W`, `F` is smooth and positive.
    have hxW : x ∉ W := (h.one_lt_liouvilleRadialCoordinate_iff hZ).1 (hma.trans_le (not_lt.1 hx))
    exact (contDiff_smoothLowerTruncation a b).contDiffAt.comp_contMDiffAt
      ((h.contMDiffAt_liouvilleGraphFunction hZ hι hιs hinj hιW hdim hf (fun s ↦ (hf₀ s).ne')
        hxW).log (liouvilleGraphFunction_pos hf₀ _).ne')

/-- **The sublevel sets of the smoothed logarithm of the defining function of the Liouville graph
are compact**, for levels `a < b` with `e^{-a} < f`. -/
theorem isCompact_setOf_smoothLogLiouvilleGraphFunction_le (hab : a < b) (c : ℝ) :
    IsCompact {x | smoothLogLiouvilleGraphFunction Z W ι f a b x ≤ c} := by
  have hf₀ := pos_of_exp_neg_lt ha
  obtain ⟨B, hB⟩ := (isCompact_range hf.continuous).bddAbove
  have hG := h.contMDiff_smoothLogLiouvilleGraphFunction hZ hι hιs hinj hιW hdim hf ha hab.le
  refine (h.isCompact_setOf_liouvilleRadialCoordinate_le hZ
    (Real.exp (max c b) * B)).of_isClosed_subset (isClosed_le hG.continuous continuous_const)
    fun x (hx : _ ≤ c) ↦ ?_
  -- `log F(x) ≤ max c b`, so `r(x) = F(x) f(s) ≤ e^{max c b} max f`.
  have hL : Real.log (liouvilleGraphFunction Z W ι f x) ≤ max c b := by
    refine not_lt.1 fun hlt ↦ ?_
    rw [smoothLogLiouvilleGraphFunction_eq_of_right_le hab ((le_max_right c b).trans hlt.le)] at hx
    exact ((le_max_left c b).trans_lt hlt).not_ge hx
  have hFx := (Real.log_le_iff_le_exp (liouvilleGraphFunction_pos hf₀ _)).1 hL
  obtain ⟨s, hs⟩ := exists_liouvilleGraphFunction_eq_div Z W ι f x
  rw [hs, div_le_iff₀ (hf₀ s)] at hFx
  exact hFx.trans (mul_le_mul_of_nonneg_left (hB (mem_range_self _)) (Real.exp_pos _).le)

/-- **The values above `b` of the smoothed logarithm of the defining function of the Liouville graph
are regular**, for levels `a < b` with `e^{-a} < f`. In particular, for `b < 0` the level `0`,
the Liouville graph, is regular. -/
theorem isRegularValue_smoothLogLiouvilleGraphFunction (hab : a < b) (hc : b < c) :
    IsRegularValue I 𝓘(ℝ) (smoothLogLiouvilleGraphFunction Z W ι f a b) c := by
  have hZ1 : ContMDiff I I.tangent 1 (T% Z) := (h.contMDiff_of_interior_eq hZ).of_le (by simp)
  have hG := h.contMDiff_smoothLogLiouvilleGraphFunction hZ hι hιs hinj hιW hdim hf ha hab.le
  refine isRegularValue_of_apply_flowOf_eq_add hZ1 (a := b) (b := c + 1)
    (fun x _ ↦ (hG x).mdifferentiableAt (by simp)) (fun x t hx hxt ↦ ?_) ⟨hc, by linarith⟩
  exact h.smoothLogLiouvilleGraphFunction_flowOf hZ ha hinj hιW hab hx.1 hxt.1

/-- **Almost existence gives existence on a Liouville graph**, for contractibility in the
completion: for levels `a < b < 0` with `e^{-a} < f`, if the level `0` of the smoothed logarithm of
the defining function of the Liouville graph has the contractible almost existence property in
`M`, then the graph carries a closed characteristic contractible in `M`. -/
theorem hasContractibleClosedCharacteristic_univ_smoothLogLiouvilleGraphFunction (hab : a < b)
    (hb : b < 0)
    (hae : ω.HasContractibleAlmostExistence univ (smoothLogLiouvilleGraphFunction Z W ι f a b) 0) :
    ω.HasContractibleClosedCharacteristic univ (smoothLogLiouvilleGraphFunction Z W ι f a b) 0 := by
  have hG := h.contMDiff_smoothLogLiouvilleGraphFunction hZ hι hιs hinj hιW hdim hf ha hab.le
  exact (h.isLiouvilleVectorField hZ).hasContractibleClosedCharacteristic_univ h.isNondegenerate
    (h.isCompleteVectorField hZ) ((h.contMDiff_of_interior_eq hZ).of_le (by simp)) (neg_pos.2 hb)
    (fun x _ ↦ (hG x).mdifferentiableAt (by simp))
    (fun x t hx hxt ↦ h.smoothLogLiouvilleGraphFunction_flowOf hZ ha hinj hιW hab
      (by linarith [hx.1]) (by linarith [hxt.1])) hae

/-- **Almost existence on a Liouville graph gives a contractible closed Reeb orbit**, the step
from almost existence to closed Reeb orbits in Corollary E of Barraud–Damian–Humilière–Oancea.
Let `M` be a completion of the Liouville domain `W` with primitive `α`, let `ι` be a smooth
injective immersion of a compact manifold of one dimension less onto the frontier of `W`, and let
`f` be smooth with `e^{-a} < f`, for levels `a < b < 0`. If the level `0` of the smoothed
logarithm of the defining function of the Liouville graph of `f` has the contractible almost
existence property in `M`, then the contact form `j^* α = f ι^* α` of the graph `j`
(`TauCeti.mpullback_liouvilleGraph_apply`) has a closed Reeb orbit `γ` whose loop `ι ∘ γ` on the
boundary of `W`, run at another speed, is contractible in `M`. -/
theorem exists_isMIntegralCurve_reebVectorField_of_hasContractibleAlmostExistence (hab : a < b)
    (hb : b < 0)
    (hae : ω.HasContractibleAlmostExistence univ (smoothLogLiouvilleGraphFunction Z W ι f a b) 0) :
    ∃ γ : ℝ → S, IsMIntegralCurve γ (SmoothForm.mpullback (liouvilleGraph Z ι f)
        (h.contMDiff_liouvilleGraph hZ hι hf fun s ↦ ((Real.exp_pos _).trans (ha s)).ne')
        α).reebVectorField ∧ (∃ τ, τ ≠ 0 ∧ Periodic γ τ) ∧
      ∃ (T : ℝ) (ψ : ℝ ≃ₜ ℝ), 0 < T ∧
        ∃ g : C(AddCircle T, M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = ι (γ (ψ t)) :=
  IsLiouvilleDomain.exists_isMIntegralCurve_reebVectorField_of_hasContractibleClosedCharacteristic
    h.toIsLiouvilleDomain hZ (h.isCompleteVectorField hZ) hι hinj hιs (range_subset_iff.1 hιW.le) hf
    (pos_of_exp_neg_lt ha) hdim
    ((h.contMDiff_smoothLogLiouvilleGraphFunction hZ hι hιs hinj hιW hdim hf ha hab.le).of_le
      (by simp))
    (h.isRegularValue_smoothLogLiouvilleGraphFunction hZ hι hιs hinj hιW hdim hf ha hab hb)
    (h.setOf_smoothLogLiouvilleGraphFunction_eq_zero hZ hinj hιW
      (one_lt_of_exp_neg_lt ha (hab.trans hb)) hab hb.le)
    (h.hasContractibleClosedCharacteristic_univ_smoothLogLiouvilleGraphFunction hZ hι hιs hinj hιW
      hdim hf ha hab hb hae)

end Smooth

end IsLiouvilleCompletion

end TauCeti
