/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Morrey
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.Normed.Module.Multilinear.Basic
import TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.Planar
import TauCeti.Analysis.Sobolev.Local.Wkp
import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Sobolev.WeakDeriv.ContinuousRepresentative

/-!
# Higher-order Morrey embedding for local Sobolev maps on planar domains

Let `Ω ⊆ ℂ` be open, let `F` be a finite-dimensional real normed space, let `2 < p ≤ ∞` and let
`k ≥ 0`. This file proves that a map `u ∈ W^{k+1,p}_loc(Ω, F)`, in the sense of
`TauCeti.MemWkpLoc p Ω (k + 1)`, agrees almost everywhere on `Ω` with a map `g` of class `Cᵏ` on
`Ω`, whose first derivative is a weak derivative of `u` (for `k ≥ 1`) and whose `k`-th derivative
lies in `W^{1,p}_loc` and is Hölder continuous with exponent `α = 1 - 2 / p` on compact subsets of
`Ω`, with the local bound

`‖Dᵏg(x) - Dᵏg(y)‖ ≤ C ‖D(Dᵏg)‖_{Lᵖ(B(x, 2|x - y|))} |x - y|^α`
whenever `closedBall x (2|x - y|) ⊆ Ω`.

Here `Dᵏg = iteratedFDeriv ℝ k g` and `D(Dᵏg)` is any weak derivative of it on `Ω`. The constant
`C` depends only on `p`, `k` and `F`. Equivalently, `W^{k,p}_loc` maps have `C^{k-1, 1-2/p}`
representatives for `k ≥ 1`.

## Proof

The order-one case is `TauCeti.MemWkpLoc.continuousOn_preciseRepresentative` together with the
local Morrey inequality `TauCeti.MemWkpLoc.exists_dist_preciseRepresentative_le`. Higher orders
follow by induction on `k`: a weak derivative of `u ∈ W^{k+2,p}_loc` lies in `W^{k+1,p}_loc`, so
it has a `Cᵏ` representative by induction, and a function whose weak derivative is `Cᵏ` has a
`Cᵏ⁺¹` representative (`TauCeti.HasWeakFDerivOn.exists_contDiffOn_succ_ae_eq`).

For the Hölder bound, the classical derivative of a `C¹` representative `g` of `u` is a weak
derivative of `u` lying in the preceding local Sobolev class
(`TauCeti.MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn`), so by induction `iteratedFDeriv ℝ k g`
lies in `W^{1,p}_loc` (`TauCeti.MemWkpLoc.iteratedFDeriv_of_contDiffOn`). The order-one
estimates then apply to it. These two derivative results hold for every `p` and live in
`TauCeti.Analysis.Sobolev.Local.Basic`. The finite-dimensionality of the space of `k`-multilinear
maps needed by the order-one estimates is `ContinuousMultilinearMap.instModuleFinite`.

## Main declarations

* `TauCeti.MemWkpLoc.exists_contDiffOn_ae_eq`: `W^{k+1,p}_loc ⊆ Cᵏ` for `p > 2`, and
  `TauCeti.MemWkpLoc.contDiffOn_of_continuousOn`: every continuous representative is `Cᵏ`.
* `TauCeti.MemWkpLoc.memLpLoc_top`: `W^{1,p}_loc ⊆ L^∞_loc` for `p > 2`.
* `TauCeti.MemWkpLoc.exists_dist_iteratedFDeriv_le`: the local Morrey inequality for the top
  derivative.
* `TauCeti.MemWkpLoc.exists_holderOnWith_iteratedFDeriv_of_isCompact`: Hölder continuity of the
  top derivative on compact subsets of `Ω`.
* `TauCeti.MemWkpLoc.exists_contDiffOn_holderOnWith_iteratedFDeriv_ball`: for real-valued maps and
  `2 < p < ∞`, the local `C^{j,1-2/p}` bound on a disc whose closure lies in `Ω`, by the norm in
  `W^{j+1,p}` of the disc.
* `TauCeti.MemWkpLoc.exists_contDiffOn_holderOnWith_iteratedFDeriv_ball_finBasis`: the same bound
  for values in a finite-dimensional space, by the norms in `W^{j+1,p}` of the disc of the
  coordinates in `Module.finBasis`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Morrey's embedding for local Sobolev spaces).
* L. C. Evans, *Partial Differential Equations*, §5.6.2, Theorem 5 and §5.6.3.
-/

public section

noncomputable section

open Metric Set MeasureTheory Module TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {Ω : Opens ℂ}
  {k : ℕ} {u g : ℂ → F}

/-! ### Morrey's embedding at higher order -/

variable [FiniteDimensional ℝ F]

/-- **Morrey's embedding `W^{k+1,p}_loc ⊆ Cᵏ` for `p > 2`.** A map `u ∈ MemWkpLoc p Ω (k + 1)`
agrees almost everywhere on `Ω` with a map `g` that is `Cᵏ` on `Ω`. For `k ≥ 1` the classical
derivative of `g` is a weak derivative of `u`
(`TauCeti.MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn`), and the `k`-th derivative of `g` is
Hölder continuous with exponent `1 - 2 / p` on compact subsets of `Ω`
(`TauCeti.MemWkpLoc.exists_holderOnWith_iteratedFDeriv_of_isCompact`). -/
theorem MemWkpLoc.exists_contDiffOn_ae_eq (hp : 2 < p) (hu : MemWkpLoc p Ω (k + 1) u) :
    ∃ g : ℂ → F, ContDiffOn ℝ k g Ω ∧ u =ᵐ[volume.restrict Ω] g := by
  induction k generalizing F with
  | zero =>
    refine ⟨preciseRepresentative volume u, ?_, ?_⟩
    · simpa using hu.continuousOn_preciseRepresentative hp
    · exact hu.memLpLoc.ae_eq_preciseRepresentative (one_le_two.trans hp.le)
  | succ k ih =>
    obtain ⟨D, hD, hDk⟩ := hu.exists_weakFDeriv_of_isOpen
    obtain ⟨h, hh, hDh⟩ := ih hDk
    obtain ⟨g, hg, hug, -⟩ := (hD.congr_ae_deriv hDh).exists_contDiffOn_succ_ae_eq (n := k) hh
    exact ⟨g, by exact_mod_cast hg, hug⟩

/-- **Continuous representatives are `Cᵏ`.** For `p > 2`, every representative of
`u ∈ MemWkpLoc p Ω (k + 1)` that is continuous on `Ω` is `Cᵏ` on `Ω`: it agrees on `Ω` with the
`Cᵏ` representative of `TauCeti.MemWkpLoc.exists_contDiffOn_ae_eq`. -/
theorem MemWkpLoc.contDiffOn_of_continuousOn (hp : 2 < p) (hu : MemWkpLoc p Ω (k + 1) u)
    (hg : ContinuousOn g Ω) (hug : u =ᵐ[volume.restrict Ω] g) : ContDiffOn ℝ k g Ω := by
  obtain ⟨g', hg', hug'⟩ := hu.exists_contDiffOn_ae_eq hp
  exact hg'.congr (Measure.eqOn_open_of_ae_eq (hug.symm.trans hug') Ω.isOpen hg hg'.continuousOn)

/-- **`W^{1,p}_loc` is locally bounded for `p > 2`.** A map `u ∈ MemWkpLoc p Ω 1` agrees almost
everywhere on `Ω` with a continuous map, by Morrey's embedding, so it is locally `L^∞` on `Ω`. -/
theorem MemWkpLoc.memLpLoc_top (hp : 2 < p) (hu : MemWkpLoc p Ω 1 u) : MemLpLoc ⊤ Ω u := by
  obtain ⟨g, hg, hug⟩ := (hu : MemWkpLoc p Ω (0 + 1) u).exists_contDiffOn_ae_eq hp
  exact hg.continuousOn.memLpLoc.congr_ae hug.symm

/-- The `k`-th derivative of a `Cᵏ` representative of `u ∈ MemWkpLoc p Ω (k + 1)` lies in
`MemWkpLoc p Ω 1`, is continuous on `Ω`, and therefore equals its precise representative there. -/
private theorem iteratedFDeriv_memWkpLoc_one_and_eqOn (hu : MemWkpLoc p Ω (k + 1) u)
    (hg : ContDiffOn ℝ k g Ω) (hug : u =ᵐ[volume.restrict Ω] g) :
    MemWkpLoc p Ω 1 (iteratedFDeriv ℝ k g) ∧
      EqOn (preciseRepresentative volume (iteratedFDeriv ℝ k g)) (iteratedFDeriv ℝ k g) Ω := by
  have h1 := hu.iteratedFDeriv_of_contDiffOn (by rw [Opens.interior_coe])
    (by rwa [Opens.interior_coe]) hug
  have hcont : ContinuousOn (iteratedFDeriv ℝ k g) Ω :=
    ContinuousOn.continuousOn_iteratedFDeriv hg Ω.isOpen le_rfl
  exact ⟨h1, eqOn_preciseRepresentative_of_continuousOn Ω.isOpen
    (hcont.locallyIntegrableOn Ω.isOpen.measurableSet) (Filter.EventuallyEq.refl _ _) hcont⟩

/-- **The local Morrey inequality at higher order.** Let `2 < p ≤ ∞`, `α = 1 - 2 / p` and
`k ≥ 0`. There is a constant `C > 0`, depending only on `p`, `k` and `F`, such that the following
holds. Let `u ∈ MemWkpLoc p Ω (k + 1)`, let `g` be `Cᵏ` on `Ω` and equal to `u` almost everywhere
on `Ω`, and let `E` be a weak derivative of `Dᵏg = iteratedFDeriv ℝ k g` on `Ω`, which exists
since `Dᵏg ∈ MemWkpLoc p Ω 1` (`TauCeti.MemWkpLoc.iteratedFDeriv_of_contDiffOn`).
If `closedBall x (2 |x - y|) ⊆ Ω`, then

`‖Dᵏg(x) - Dᵏg(y)‖ ≤ C ‖E‖_{Lᵖ(B(x, 2 |x - y|))} |x - y|^α`. -/
theorem MemWkpLoc.exists_dist_iteratedFDeriv_le (hp : 2 < p) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Opens ℂ} {u g : ℂ → F}
      {E : ℂ → ℂ →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => ℂ) F},
      MemWkpLoc p Ω (k + 1) u → ContDiffOn ℝ k g Ω → u =ᵐ[volume.restrict Ω] g →
      HasWeakFDerivOn volume Ω (iteratedFDeriv ℝ k g) E →
      ∀ {x y : ℂ}, closedBall x (2 * dist x y) ⊆ Ω →
        dist (iteratedFDeriv ℝ k g x) (iteratedFDeriv ℝ k g y) ≤
          C * (eLpNorm E p (volume.restrict (ball x (2 * dist x y)))).toReal *
            dist x y ^ (((1 : ℝ≥0∞) - 2 / p).toNNReal : ℝ) := by
  obtain ⟨C, hC, hdist⟩ := MemWkpLoc.exists_dist_preciseRepresentative_le
    (F := ContinuousMultilinearMap ℝ (fun _ : Fin k => ℂ) F) hp
  refine ⟨C, hC, fun {Ω u g E} hu hg hug hE x y hxy => ?_⟩
  obtain ⟨h1, heq⟩ := iteratedFDeriv_memWkpLoc_one_and_eqOn hu hg hug
  have hx : x ∈ (Ω : Set ℂ) := hxy (mem_closedBall_self (by positivity))
  have hy : y ∈ (Ω : Set ℂ) := hxy (by
    rw [mem_closedBall, dist_comm]
    linarith [dist_nonneg (x := x) (y := y)])
  rw [← heq hx, ← heq hy]
  exact hdist h1 hE hxy

/-- **Morrey's embedding at higher order on compact sets.** If `2 < p ≤ ∞`, `g` is `Cᵏ` on `Ω`
and agrees almost everywhere on `Ω` with `u ∈ MemWkpLoc p Ω (k + 1)`, then
`iteratedFDeriv ℝ k g` is Hölder continuous with exponent `1 - 2 / p` on every compact subset of
`Ω`: `g` is a `C^{k, 1 - 2/p}` representative of `u`. -/
theorem MemWkpLoc.exists_holderOnWith_iteratedFDeriv_of_isCompact (hp : 2 < p)
    (hu : MemWkpLoc p Ω (k + 1) u) (hg : ContDiffOn ℝ k g Ω) (hug : u =ᵐ[volume.restrict Ω] g)
    {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0, HolderOnWith C ((1 : ℝ≥0∞) - 2 / p).toNNReal (iteratedFDeriv ℝ k g) K := by
  obtain ⟨h1, heq⟩ := iteratedFDeriv_memWkpLoc_one_and_eqOn hu hg hug
  obtain ⟨C, hC⟩ := h1.exists_holderOnWith_preciseRepresentative_of_isCompact hp hK hKΩ
  refine ⟨C, fun x hx y hy => ?_⟩
  rw [← heq (hKΩ hx), ← heq (hKΩ hy)]
  exact hC x hx y hy

/-- **Local `C^{j,1-2/q}` bounds on a disc.** For `2 < q < ∞`, a centre `c` and a radius `s`
there is a constant `K` such that, for every open `Ω` containing the closure of `ball c s`, every
real `u ∈ MemWkpLoc q Ω (j + 1)` is represented on `ball c s` by some
`v ∈ W^{j+1,q}(ball c s)` and agrees almost everywhere there with a map `g` that is `Cʲ` on
`ball c s`, whose derivatives of order `i ≤ j` are bounded by `K ‖v‖` and Hölder of exponent
`1 - 2 / q` with constant `K ‖v‖` on `ball c s`. -/
theorem MemWkpLoc.exists_contDiffOn_holderOnWith_iteratedFDeriv_ball {q : ℝ≥0}
    [Fact (1 ≤ (q : ℝ≥0∞))] (hq : 2 < q) (c : ℂ) (s : ℝ) (j : ℕ) :
    ∃ K : ℝ≥0, ∀ {Ω : Opens ℂ} (u : ℂ → ℝ), closure (ball c s) ⊆ Ω →
      MemWkpLoc q Ω (j + 1) u →
      ∃ v : Wkp volume (⟨ball c s, isOpen_ball⟩ : Opens ℂ) q (j + 1),
        Wkp.value (j + 1) v =ᵐ[volume.restrict (ball c s)] u ∧
        ∃ g : ℂ → ℝ, ContDiffOn ℝ j g (ball c s) ∧ u =ᵐ[volume.restrict (ball c s)] g ∧
          ∀ i ≤ j, (∀ z ∈ ball c s, ‖iteratedFDeriv ℝ i g z‖ ≤ K * ‖v‖) ∧
            HolderOnWith (K * ‖v‖₊) (1 - 2 / q) (iteratedFDeriv ℝ i g) (ball c s) := by
  obtain ⟨K, hK⟩ := Wkp.exists_contDiffOn_holderOnWith_iteratedFDeriv_complexBall c s hq j
  refine ⟨K, fun u hsub hu => ?_⟩
  obtain ⟨v, hv⟩ := hu.exists_wkp (W := ⟨ball c s, isOpen_ball⟩)
    ((isCompact_closedBall c s).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall)
    hsub
  obtain ⟨g, hg, hvg, hb⟩ := hK v
  exact ⟨v, hv, g, hg, hv.symm.trans hvg, hb⟩


omit [FiniteDimensional ℝ F] in
/-- Derivative bounds pass to finite sums `∑ₗ A l ∘ g l` with continuous linear `A l`: if each
`g l` is `Cʲ` on the open set `V` and its derivatives of order `i ≤ j` are bounded by `M l` and
`r`-Hölder with constant `M l` on `S ⊆ V`, then the derivatives of the sum are bounded by
`∑ₗ ‖A l‖ M l` and `r`-Hölder with that constant on `S`. -/
private theorem iteratedFDeriv_sum_clm_comp_le_and_holderOnWith {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {V S : Set ℂ} (hV : IsOpen V) (hSV : S ⊆ V)
    {j : ℕ} {r : ℝ≥0} (A : ι → E →L[ℝ] F) {g : ι → ℂ → E} (hg : ∀ l, ContDiffOn ℝ j (g l) V)
    (M : ι → ℝ≥0) (hb : ∀ l, ∀ i ≤ j, (∀ z ∈ S, ‖iteratedFDeriv ℝ i (g l) z‖ ≤ M l) ∧
      HolderOnWith (M l) r (iteratedFDeriv ℝ i (g l)) S) {i : ℕ} (hi : i ≤ j) :
    (∀ z ∈ S, ‖iteratedFDeriv ℝ i (fun z => ∑ l, A l (g l z)) z‖ ≤ ∑ l, ‖A l‖₊ * M l) ∧
      HolderOnWith (∑ l, ‖A l‖₊ * M l) r (iteratedFDeriv ℝ i (fun z => ∑ l, A l (g l z))) S := by
  set L : ι → ContinuousMultilinearMap ℝ (fun _ : Fin i => ℂ) E →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin i => ℂ) F :=
    fun l => ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin i => ℂ) E F (A l)
  have hL (l : ι) : ‖L l‖ ≤ ‖A l‖ := ContinuousLinearMap.norm_compContinuousMultilinearMapL_le _
  -- On `S`, the derivatives of the sum are the sums of the images of those of the terms.
  have hD (z : ℂ) (hz : z ∈ S) : iteratedFDeriv ℝ i (fun z => ∑ l, A l (g l z)) z =
      ∑ l, L l (iteratedFDeriv ℝ i (g l) z) := by
    have hza (l : ι) : ContDiffAt ℝ j (g l) z := (hg l).contDiffAt (hV.mem_nhds (hSV hz))
    have hza' (l : ι) : ContDiffAt ℝ i (fun z => A l (g l z)) z :=
      ((A l).contDiff.contDiffAt.comp z (hza l)).of_le (by exact_mod_cast hi)
    rw [iteratedFDeriv_fun_sum_apply fun l _ => hza' l]
    exact Finset.sum_congr rfl fun l _ =>
      (A l).iteratedFDeriv_comp_left (hza l) (by exact_mod_cast hi)
  refine ⟨fun z hz => ?_, ?_⟩
  · rw [hD z hz]
    refine (norm_sum_le _ _).trans ?_
    push_cast
    refine Finset.sum_le_sum fun l _ => ?_
    exact ((L l).le_opNorm _).trans (mul_le_mul (hL l) ((hb l i hi).1 z hz) (norm_nonneg _)
      (norm_nonneg _))
  · refine (HolderOnWith.sum (s := Finset.univ) fun l _ =>
      HolderOnWith.of_dist_le fun x hx y hy => ?_).congr fun z hz => (hD z hz).symm
    refine (((L l).lipschitzWith.comp_holderOnWith (hb l i hi).2).dist_le hx hy).trans ?_
    simp only [NNReal.coe_mul, coe_nnNorm]
    gcongr
    exact hL l

/-- **Local `C^{j,1-2/q}` bounds on a disc, for finite-dimensional values.** For `2 < q < ∞`, a
centre `c` and a radius `s` there is a constant `K` such that, for every open `Ω` containing the
closure of `ball c s`, every `u ∈ MemWkpLoc q Ω (j + 1)` with values in `F` has coordinates in the
basis `Module.finBasis ℝ F` represented on `ball c s` by elements `v l` of `W^{j+1,q}(ball c s)`,
and agrees almost everywhere on `ball c s` with a map `g` that is `Cʲ` on `ball c s`, whose
derivatives of order `i ≤ j` are bounded by `K ∑ₗ ‖v l‖` and Hölder of exponent `1 - 2 / q` with
constant `K ∑ₗ ‖v l‖` on `ball c s`. This is
`TauCeti.MemWkpLoc.exists_contDiffOn_holderOnWith_iteratedFDeriv_ball` applied to each
coordinate. -/
theorem MemWkpLoc.exists_contDiffOn_holderOnWith_iteratedFDeriv_ball_finBasis {q : ℝ≥0}
    [Fact (1 ≤ (q : ℝ≥0∞))] (hq : 2 < q) (c : ℂ) (s : ℝ) (j : ℕ) :
    ∃ K : ℝ≥0, ∀ {Ω : Opens ℂ} (u : ℂ → F), closure (ball c s) ⊆ Ω →
      MemWkpLoc q Ω (j + 1) u →
      ∃ v : Fin (finrank ℝ F) → Wkp volume (⟨ball c s, isOpen_ball⟩ : Opens ℂ) q (j + 1),
        (∀ l, Wkp.value (j + 1) (v l) =ᵐ[volume.restrict (ball c s)]
          fun z => Module.finBasis ℝ F |>.coord l (u z)) ∧
        ∃ g : ℂ → F, ContDiffOn ℝ j g (ball c s) ∧ u =ᵐ[volume.restrict (ball c s)] g ∧
          ∀ i ≤ j, (∀ z ∈ ball c s, ‖iteratedFDeriv ℝ i g z‖ ≤ K * ∑ l, ‖v l‖) ∧
            HolderOnWith (K * ∑ l, ‖v l‖₊) (1 - 2 / q) (iteratedFDeriv ℝ i g) (ball c s) := by
  obtain ⟨K, hK⟩ := exists_contDiffOn_holderOnWith_iteratedFDeriv_ball (j := j) hq c s
  set b := Module.finBasis ℝ F
  -- Coordinates `ℓ l` and the inverse maps `A l : t ↦ t • b l`.
  set ℓ : Fin (finrank ℝ F) → F →L[ℝ] ℝ := fun l => (b.coord l).toContinuousLinearMap
  set A : Fin (finrank ℝ F) → ℝ →L[ℝ] F :=
    fun l => (ContinuousLinearMap.id ℝ ℝ).smulRight (b l)
  refine ⟨(∑ l, ‖A l‖₊) * K, fun {Ω} u hsub hu => ?_⟩
  choose v hv g hg hug hb using fun l =>
    hK (Ω := Ω) (fun z => ℓ l (u z)) hsub (hu.clm_comp (ℓ l))
  have hsum (x : F) : x = ∑ l, A l (ℓ l x) := by
    simp only [A, ℓ, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      LinearMap.coe_toContinuousLinearMap', Basis.coord_apply]
    exact (b.sum_repr x).symm
  -- The bounds `K ‖v l‖` of the coordinates are at most `K ∑ ‖v‖`.
  have hb' (l : Fin (finrank ℝ F)) (i : ℕ) (hi : i ≤ j) :
      (∀ z ∈ ball c s, ‖iteratedFDeriv ℝ i (g l) z‖ ≤ K * ∑ l', ‖v l'‖₊) ∧
        HolderOnWith (K * ∑ l', ‖v l'‖₊) (1 - 2 / q) (iteratedFDeriv ℝ i (g l)) (ball c s) := by
    have hvl : ‖v l‖₊ ≤ ∑ l', ‖v l'‖₊ :=
      Finset.single_le_sum (f := fun l' => ‖v l'‖₊) (fun _ _ => zero_le) (Finset.mem_univ l)
    refine ⟨fun z hz => ((hb l i hi).1 z hz).trans ?_, HolderOnWith.of_dist_le fun x hx y hy =>
      ((hb l i hi).2.dist_le hx hy).trans ?_⟩
    · push_cast
      gcongr
      exact Finset.single_le_sum (f := fun l' => ‖v l'‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ l)
    · gcongr
  have hC : ∑ l, ‖A l‖₊ * (K * ∑ l', ‖v l'‖₊) = (∑ l, ‖A l‖₊) * K * ∑ l, ‖v l‖₊ := by
    rw [← Finset.sum_mul]
    ring
  refine ⟨v, hv, fun z => ∑ l, A l (g l z),
    ContDiffOn.sum fun l _ => (A l).contDiff.comp_contDiffOn (hg l), ?_, fun i hi => ?_⟩
  · filter_upwards [ae_all_iff.2 hug] with z hz
    rw [hsum (u z)]
    exact Finset.sum_congr rfl fun l _ => by rw [hz l]
  · obtain ⟨h1, h2⟩ := iteratedFDeriv_sum_clm_comp_le_and_holderOnWith isOpen_ball subset_rfl A
      hg (fun _ => K * ∑ l', ‖v l'‖₊) (fun l i hi => hb' l i hi) hi
    rw [hC] at h1 h2
    exact ⟨fun z hz => by simpa using h1 z hz, h2⟩

end TauCeti
