/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.FaaDiBruno
public import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
public import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# `C^n` convergence of families of maps

A family `f i` of maps converges to `f₀` in `C^n` near `x₀`, along a filter `l` on the
indices, when every derivative of order at most `n` converges *continuously*: `D^k f i x` tends
to `D^k f₀ x₀` as `i → l` and `x → x₀` jointly (`TauCeti.TendstoContDiffAt`). On an open set
on which the derivatives of the limit are continuous, continuous convergence at every point is
the same as locally uniform convergence of each derivative of order at most `n`
(`TauCeti.tendstoContDiffAt_iff_tendstoLocallyUniformlyOn`), which in finite dimensions is
uniform convergence on compact sets: this is the usual meaning of "`f i → f₀` in `C^n`".

The continuous form composes well. Through the Faà di Bruno formula, `C^n` convergence is
preserved by composition of two converging families (`TauCeti.TendstoContDiffAt.comp`), and it
holds componentwise for pairs (`TauCeti.TendstoContDiffAt.prodMk`).

## Main declarations

* `TauCeti.TendstoContDiffAt`: continuous convergence of all derivatives of order at most `n`,
  characterized by `TauCeti.tendstoContDiffAt_iff`.
* `TauCeti.TendstoContDiffAt.tendsto`, `TauCeti.TendstoContDiffAt.tendsto_fderiv`: convergence
  of the values and of the first derivatives.
* `ContDiffAt.tendstoContDiffAt_const`: a constant family converges to its value.
* `TauCeti.TendstoContDiffAt.comp`, `TauCeti.TendstoContDiffAt.prodMk`: stability under
  composition and pairing.
* `TauCeti.tendstoContDiffAt_iff_tendstoLocallyUniformlyOn`: the comparison with locally uniform
  convergence of the derivatives.
-/

public section

open Set Filter Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {ι : Type*} {l : Filter ι} {n m : ℕ}

variable (𝕜) in
/-- **`C^n` convergence of a family of maps at a point.** `f i → f₀` in `C^n` at `x₀` along `l`
when, for every order `k ≤ n`, the derivative `D^k f i x` tends to `D^k f₀ x₀` as `i → l` and
`x → x₀` jointly. Holding at every point of an open set on which the derivatives of `f₀` of order
at most `n` are continuous, this is locally uniform convergence of the derivatives of order at
most `n` there (`TauCeti.tendstoContDiffAt_iff_tendstoLocallyUniformlyOn`). -/
def TendstoContDiffAt (n : ℕ) (f : ι → E → F) (f₀ : E → F) (l : Filter ι) (x₀ : E) :
    Prop :=
  ∀ k ≤ n, Tendsto (fun p : ι × E ↦ iteratedFDeriv 𝕜 k (f p.1) p.2) (l ×ˢ 𝓝 x₀)
    (𝓝 (iteratedFDeriv 𝕜 k f₀ x₀))

namespace TendstoContDiffAt

variable {f : ι → E → F} {f₀ : E → F} {x₀ : E}

/-- Unfolding `TendstoContDiffAt`: every derivative of order at most `n` converges continuously. -/
theorem _root_.TauCeti.tendstoContDiffAt_iff :
    TendstoContDiffAt 𝕜 n f f₀ l x₀ ↔ ∀ k ≤ n, Tendsto
      (fun p : ι × E ↦ iteratedFDeriv 𝕜 k (f p.1) p.2) (l ×ˢ 𝓝 x₀)
      (𝓝 (iteratedFDeriv 𝕜 k f₀ x₀)) :=
  Iff.rfl

/-- The derivatives of order `k ≤ n` converge continuously. -/
theorem tendsto_iteratedFDeriv (h : TendstoContDiffAt 𝕜 n f f₀ l x₀) {k : ℕ}
    (hk : k ≤ n) : Tendsto (fun p : ι × E ↦ iteratedFDeriv 𝕜 k (f p.1) p.2) (l ×ˢ 𝓝 x₀)
      (𝓝 (iteratedFDeriv 𝕜 k f₀ x₀)) :=
  h k hk

/-- `C^n` convergence implies `C^m` convergence for `m ≤ n`. -/
theorem of_le (h : TendstoContDiffAt 𝕜 n f f₀ l x₀) (hmn : m ≤ n) :
    TendstoContDiffAt 𝕜 m f f₀ l x₀ :=
  fun k hk ↦ h k (hk.trans hmn)

/-- `C^n` convergence depends only on the members of the family eventually along `l`. -/
theorem congr (h : TendstoContDiffAt 𝕜 n f f₀ l x₀) {g : ι → E → F}
    (hfg : ∀ᶠ i in l, f i = g i) : TendstoContDiffAt 𝕜 n g f₀ l x₀ := by
  refine fun k hk ↦ (h k hk).congr' ?_
  filter_upwards [tendsto_fst.eventually hfg] with p hp
  rw [hp]

/-- The values converge continuously. -/
theorem tendsto (h : TendstoContDiffAt 𝕜 n f f₀ l x₀) :
    Tendsto (fun p : ι × E ↦ f p.1 p.2) (l ×ˢ 𝓝 x₀) (𝓝 (f₀ x₀)) := by
  simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
    LinearIsometryEquiv.apply_symm_apply] using
    ((continuousMultilinearCurryFin0 𝕜 E F).continuous.tendsto _).comp (h 0 (Nat.zero_le n))

/-- `C^0` convergence is continuous convergence of the values. -/
theorem _root_.TauCeti.tendstoContDiffAt_zero_iff :
    TendstoContDiffAt 𝕜 0 f f₀ l x₀ ↔
      Tendsto (fun p : ι × E ↦ f p.1 p.2) (l ×ˢ 𝓝 x₀) (𝓝 (f₀ x₀)) := by
  refine ⟨tendsto, fun h k hk ↦ ?_⟩
  obtain rfl := Nat.le_zero.mp hk
  simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
    ((continuousMultilinearCurryFin0 𝕜 E F).symm.continuous.tendsto _).comp h

/-- For `1 ≤ n`, the first derivatives converge continuously. -/
theorem tendsto_fderiv (h : TendstoContDiffAt 𝕜 n f f₀ l x₀) (hn : 1 ≤ n) :
    Tendsto (fun p : ι × E ↦ fderiv 𝕜 (f p.1) p.2) (l ×ˢ 𝓝 x₀) (𝓝 (fderiv 𝕜 f₀ x₀)) := by
  simpa only [Function.comp_def, continuousMultilinearCurryFin1_iteratedFDeriv_one] using
    ((continuousMultilinearCurryFin1 𝕜 E F).continuous.tendsto _).comp (h 1 hn)

end TendstoContDiffAt

/-- **A constant family converges in `C^n`** at every point where it is `C^n`. -/
theorem _root_.ContDiffAt.tendstoContDiffAt_const {f₀ : E → F} {x₀ : E}
    (hf : ContDiffAt 𝕜 n f₀ x₀) :
    TendstoContDiffAt 𝕜 n (fun _ : ι ↦ f₀) f₀ l x₀ :=
  fun k hk ↦ ((hf.continuousAt_iteratedFDeriv (by exact_mod_cast hk)).tendsto).comp tendsto_snd

/-- **`C^n` convergence is preserved by composition.** If `g i → g₀` in `C^n` at `f₀ x₀` and
`f i → f₀` in `C^n` at `x₀`, all of them `C^n` near the relevant points, then
`g i ∘ f i → g₀ ∘ f₀` in `C^n` at `x₀`. This is the Faà di Bruno formula: the `k`-th derivative
of a composite is a fixed continuous expression in the derivatives of order at most `k`. -/
theorem TendstoContDiffAt.comp {g : ι → F → G} {g₀ : F → G} {f : ι → E → F} {f₀ : E → F}
    {x₀ : E} (hg : TendstoContDiffAt 𝕜 n g g₀ l (f₀ x₀)) (hf : TendstoContDiffAt 𝕜 n f f₀ l x₀)
    (hgd : ∀ᶠ p in l ×ˢ 𝓝 x₀, ContDiffAt 𝕜 n (g p.1) (f p.1 p.2))
    (hfd : ∀ᶠ p in l ×ˢ 𝓝 x₀, ContDiffAt 𝕜 n (f p.1) p.2)
    (hg₀ : ContDiffAt 𝕜 n g₀ (f₀ x₀)) (hf₀ : ContDiffAt 𝕜 n f₀ x₀) :
    TendstoContDiffAt 𝕜 n (fun i ↦ g i ∘ f i) (g₀ ∘ f₀) l x₀ := by
  intro k hk
  have hk' : ((k : ℕ) : WithTop ℕ∞) ≤ n := by exact_mod_cast hk
  have hlim : Tendsto (fun p : ι × E ↦ (p.1, f p.1 p.2)) (l ×ˢ 𝓝 x₀) (l ×ˢ 𝓝 (f₀ x₀)) :=
    tendsto_fst.prodMk hf.tendsto
  rw [iteratedFDeriv_comp hg₀ hf₀ hk']
  refine (Filter.Tendsto.taylorComp (m := k)
    (q := fun p : ι × E ↦ ftaylorSeries 𝕜 (g p.1) (f p.1 p.2))
    (p := fun p : ι × E ↦ ftaylorSeries 𝕜 (f p.1) p.2)
    (fun j hj ↦ (hg j (hj.trans hk)).comp hlim) (fun j _ hj ↦ hf j (hj.trans hk))).congr' ?_
  filter_upwards [hgd, hfd] with p hgp hfp
  exact (iteratedFDeriv_comp hgp hfp hk').symm

/-- **`C^n` convergence of pairs.** Two families converging in `C^n` at `x₀` give a converging
family of pairs. -/
theorem TendstoContDiffAt.prodMk {f : ι → E → F} {f₀ : E → F} {g : ι → E → G} {g₀ : E → G}
    {x₀ : E} (hf : TendstoContDiffAt 𝕜 n f f₀ l x₀) (hg : TendstoContDiffAt 𝕜 n g g₀ l x₀)
    (hfd : ∀ᶠ p in l ×ˢ 𝓝 x₀, ContDiffAt 𝕜 n (f p.1) p.2)
    (hgd : ∀ᶠ p in l ×ˢ 𝓝 x₀, ContDiffAt 𝕜 n (g p.1) p.2)
    (hf₀ : ContDiffAt 𝕜 n f₀ x₀) (hg₀ : ContDiffAt 𝕜 n g₀ x₀) :
    TendstoContDiffAt 𝕜 n (fun i x ↦ (f i x, g i x)) (fun x ↦ (f₀ x, g₀ x)) l x₀ := by
  intro k hk
  have hk' : ((k : ℕ) : WithTop ℕ∞) ≤ n := by exact_mod_cast hk
  rw [iteratedFDeriv_prodMk hf₀ hg₀ hk']
  refine ((ContinuousMultilinearMap.prodL 𝕜 (fun _ : Fin k ↦ E) F G).continuous.tendsto _ |>.comp
    ((hf k hk).prodMk_nhds (hg k hk))).congr' ?_
  filter_upwards [hfd, hgd] with p hfp hgp
  exact (iteratedFDeriv_prodMk hfp hgp hk').symm

/-- **`C^n` convergence on an open set is locally uniform convergence of the derivatives.** If
the derivatives of order at most `n` of `f₀` are continuous on an open set `s`, then `f i → f₀`
in `C^n` at every point of `s` exactly when each of these derivatives of `f i` converges locally
uniformly on `s` to that of `f₀`. -/
theorem tendstoContDiffAt_iff_tendstoLocallyUniformlyOn {f : ι → E → F} {f₀ : E → F} {s : Set E}
    (hs : IsOpen s) (hf₀ : ∀ k ≤ n, ContinuousOn (iteratedFDeriv 𝕜 k f₀) s) :
    (∀ x ∈ s, TendstoContDiffAt 𝕜 n f f₀ l x) ↔
      ∀ k ≤ n, TendstoLocallyUniformlyOn (fun i ↦ iteratedFDeriv 𝕜 k (f i))
        (iteratedFDeriv 𝕜 k f₀) l s := by
  refine ⟨fun h k hk ↦ ?_, fun h x hx k hk ↦ ?_⟩
  · exact (hs.tendstoLocallyUniformlyOn_iff_forall_tendsto_of_continuousOn (hf₀ k hk)).2
      fun x hx ↦ h x hx k hk
  · exact (hs.tendstoLocallyUniformlyOn_iff_forall_tendsto_of_continuousOn (hf₀ k hk)).1
      (h k hk) x hx

end TauCeti
