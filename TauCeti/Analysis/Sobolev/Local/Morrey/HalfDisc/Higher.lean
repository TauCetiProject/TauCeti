/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ReImTopology
public import TauCeti.Analysis.Sobolev.Local.Morrey.Higher
import TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.Planar
import TauCeti.Analysis.Sobolev.Local.Reflection
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Analysis.Sobolev.Local.Wkp.HalfDisc
import TauCeti.Topology.MetricSpace.Holder

/-!
# Higher-order Morrey embedding on half-discs

Let `Ω ⊆ ℂ` be open, let `S = Ω ∩ {0 ≤ im}` be the corresponding relatively open subset of the
closed upper half-plane, and let `F` be a finite-dimensional real normed space. The local Sobolev
class `TauCeti.MemWkpLoc p S k` tests weak derivatives on the interior `Ω ∩ {0 < im}` and imposes
`Lᵖ` bounds on compact subsets of `S`, which may reach the real axis. This file proves Morrey's
embedding up to the real axis at every order:

* for `2 < p ≤ ∞`, a map `u ∈ MemWkpLoc p S (k + 1)` agrees almost everywhere on `S` with a map `g`
  that is `Cᵏ` on an open neighbourhood of `S` in `Ω`, and `iteratedFDeriv ℝ k g` is Hölder
  continuous with exponent `1 - 2 / p` on compact subsets of `S`, including those meeting the
  real axis;
* for `1 ≤ p ≤ ∞` and `2 < k p`, a map `u ∈ MemWkpLoc p S k` agrees almost everywhere on `S` with a
  map continuous on `S`.

The derivatives of such a `g` up to order `k` do not depend on the choice of `g` on `S`
(`TauCeti.eqOn_iteratedFDeriv_of_ae_eq_inter_setOf_im_nonneg`). For real-valued maps and
`2 < q < ∞`, the local `C^{j,1-2/q}` bound on a half-disc `ball x s ∩ {0 ≤ im}` with real centre
`x`, whose disc has closure in `Ω`, bounds the derivatives of order at most `j` of such a
representative, and their Hölder constants up to the real axis, by a multiple of the
`W^{j+1,q}` norm on the open half-disc.

## Proof

The order-`k` higher reflection of `u` across the real axis lies in `W^{k,p}_loc` of an open set
`V` with `S ⊆ V ⊆ Ω` (`TauCeti.MemWkpLoc.exists_opens_memWkpLoc_planarReflection`). It agrees
with `u` on `S`, so the interior results of `TauCeti.Analysis.Sobolev.Local.Morrey.Higher` and
`TauCeti.Analysis.Sobolev.Local.SobolevEmbedding` on `V` apply to it. For the local bounds, `u`
restricts to an element of `W^{j+1,q}` of the open half-disc
(`TauCeti.MemWkpLoc.exists_wkp_upperHalf`), which is a Lipschitz domain, and
`TauCeti.Wkp.exists_contDiffOn_holderOnWith_iteratedFDeriv_complexBall_upperHalf` bounds a
representative there; it agrees with the reflected representative on the open half-disc, and the
bounds reach the real axis by continuity.

## Main declarations

* `TauCeti.MemWkpLoc.exists_opens_contDiffOn_ae_eq_inter_setOf_im_nonneg`: `Cᵏ` representatives
  of `W^{k+1,p}` maps up to the real axis, for `p > 2`.
* `TauCeti.MemWkpLoc.exists_holderOnWith_iteratedFDeriv_of_isCompact_inter_setOf_im_nonneg`:
  Hölder continuity of the top derivative on compact subsets of `S`.
* `TauCeti.MemWkpLoc.exists_continuousOn_ae_eq_of_two_lt_mul_inter_setOf_im_nonneg`: continuous
  representatives up to the real axis for `k p > 2`.
* `TauCeti.MemWkpLoc.exists_contDiffOn_holderOnWith_iteratedFDeriv_ball_inter_setOf_im_nonneg`:
  the local `C^{j,1-2/q}` bound on half-discs up to the real axis. The bound on discs is
  `TauCeti.MemWkpLoc.exists_contDiffOn_holderOnWith_iteratedFDeriv_ball`, and the classical
  derivatives of a representative on `Ω ∩ {0 < im}` are weak derivatives in the classes of `S`
  (`TauCeti.MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn_inter_setOf_im_nonneg`,
  `TauCeti.MemWkpLoc.iteratedFDeriv_of_contDiffOn_inter_setOf_im_nonneg`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Sobolev spaces on half-discs).
* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 5.19 (extension by
  reflection).
-/

public section

noncomputable section

open Metric Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {Ω : Opens ℂ}
  {k : ℕ} {u g : ℂ → F}

/-- The higher reflection agrees with `u` on `Ω ∩ {0 ≤ im}`, so a representative of the
reflection on a larger set is a representative of `u` there. -/
private theorem ae_eq_of_planarReflection_ae_eq {V : Set ℂ}
    (hSV : (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ V)
    (h : TauCeti.planarReflection (higherReflectionCoeff k) u =ᵐ[volume.restrict V] g) :
    u =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] g := by
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hSV h,
    ae_restrict_mem (Ω.isOpen.measurableSet.inter (measurableSet_le measurable_const
      Complex.measurable_im))] with z hz hzS
  rw [← hz, planarReflection_of_nonneg _ _ hzS.2]

/-- **Uniqueness of derivatives up to the real axis.** Let `g₁` and `g₂` be `Cᵏ` on open sets
containing `Ω ∩ {0 ≤ im}` and agree almost everywhere on `Ω ∩ {0 ≤ im}`. Then their derivatives
of every order `i ≤ k` agree on `Ω ∩ {0 ≤ im}`, including at the points of the real axis. -/
theorem eqOn_iteratedFDeriv_of_ae_eq_inter_setOf_im_nonneg {V₁ V₂ : Opens ℂ}
    (hS₁ : (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ V₁) (hS₂ : (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ V₂)
    {g₁ g₂ : ℂ → F} (hg₁ : ContDiffOn ℝ k g₁ V₁) (hg₂ : ContDiffOn ℝ k g₂ V₂)
    (h : g₁ =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] g₂) {i : ℕ} (hi : i ≤ k) :
    EqOn (iteratedFDeriv ℝ i g₁) (iteratedFDeriv ℝ i g₂) ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  set S : Set ℂ := (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}
  have hint : IsOpen (interior S) := isOpen_interior
  have hc₁ := (hg₁.continuousOn).mono (interior_subset.trans hS₁)
  have hc₂ := (hg₂.continuousOn).mono (interior_subset.trans hS₂)
  have heq : EqOn g₁ g₂ (interior S) :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset interior_subset h) hint
      hc₁ hc₂
  have heqi : EqOn (iteratedFDeriv ℝ i g₁) (iteratedFDeriv ℝ i g₂) (interior S) := fun z hz =>
    ((Filter.eventuallyEq_of_mem (hint.mem_nhds hz) heq).iteratedFDeriv ℝ i).eq_of_nhds
  exact heqi.of_subset_closure
    ((ContinuousOn.continuousOn_iteratedFDeriv hg₁ V₁.isOpen (by exact_mod_cast hi)).mono hS₁)
    ((ContinuousOn.continuousOn_iteratedFDeriv hg₂ V₂.isOpen (by exact_mod_cast hi)).mono hS₂)
    interior_subset (by simpa only [inter_comm] using
      subset_closure_interior_setOfPred_le_im_inter Ω.isOpen)

variable [FiniteDimensional ℝ F]

/-- **Morrey's embedding `W^{k+1,p}_loc ⊆ Cᵏ` up to the real axis, for `p > 2`.** A map
`u ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) (k + 1)` agrees almost everywhere on `Ω ∩ {0 ≤ im}` with a map `g`
that is `Cᵏ` on an open set `V` with `Ω ∩ {0 ≤ im} ⊆ V ⊆ Ω`. The derivatives of `g` of order at
most `k` on `Ω ∩ {0 ≤ im}` do not depend on the choice of `g`
(`TauCeti.eqOn_iteratedFDeriv_of_ae_eq_inter_setOf_im_nonneg`), and the `k`-th one is Hölder
continuous with exponent `1 - 2 / p` on compact subsets of `Ω ∩ {0 ≤ im}`
(`TauCeti.MemWkpLoc.exists_holderOnWith_iteratedFDeriv_of_isCompact_inter_setOf_im_nonneg`). -/
theorem MemWkpLoc.exists_opens_contDiffOn_ae_eq_inter_setOf_im_nonneg (hp : 2 < p)
    (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) u) :
    ∃ V : Opens ℂ, (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ V ∧ (V : Set ℂ) ⊆ Ω ∧
      ∃ g : ℂ → F, ContDiffOn ℝ k g V ∧ u =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] g := by
  obtain ⟨V, hSV, hVΩ, hV⟩ := hu.exists_opens_memWkpLoc_planarReflection (one_le_two.trans hp.le)
  obtain ⟨g, hg, hrg⟩ := hV.exists_contDiffOn_ae_eq hp
  exact ⟨V, hSV, hVΩ, g, hg, ae_eq_of_planarReflection_ae_eq hSV hrg⟩

/-- **Morrey's embedding at higher order on compact sets up to the real axis.** Let `2 < p ≤ ∞`,
`u ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) (k + 1)`, and let `g` be `Cᵏ` on an open set `V` and agree with `u`
almost everywhere on `Ω ∩ {0 ≤ im}`. Then `iteratedFDeriv ℝ k g` is Hölder continuous with
exponent `1 - 2 / p` on every compact subset of `(Ω ∩ {0 ≤ im}) ∩ V`, including compact sets
meeting the real axis. -/
theorem MemWkpLoc.exists_holderOnWith_iteratedFDeriv_of_isCompact_inter_setOf_im_nonneg
    (hp : 2 < p) (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) u) {V : Opens ℂ}
    (hg : ContDiffOn ℝ k g V) (hug : u =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] g)
    {K : Set ℂ} (hK : IsCompact K) (hKS : K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (hKV : K ⊆ V) :
    ∃ C : ℝ≥0, HolderOnWith C ((1 : ℝ≥0∞) - 2 / p).toNNReal (iteratedFDeriv ℝ k g) K := by
  obtain ⟨W, hSW, -, hW⟩ := hu.exists_opens_memWkpLoc_planarReflection (one_le_two.trans hp.le)
  obtain ⟨h, hh, hrh⟩ := hW.exists_contDiffOn_ae_eq hp
  obtain ⟨C, hC⟩ := hW.exists_holderOnWith_iteratedFDeriv_of_isCompact hp hh hrh hK
    (hKS.trans hSW)
  -- On `(Ω ⊓ V) ∩ {0 ≤ im}` the derivatives of `g` and of `h` agree.
  have hsub : ((Ω ⊓ V : Opens ℂ) : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} :=
    fun z hz => ⟨hz.1.1, hz.2⟩
  have hug' : u =ᵐ[volume.restrict (((Ω ⊓ V : Opens ℂ) : Set ℂ) ∩ {z | 0 ≤ z.im})] g :=
    ae_restrict_of_ae_restrict_of_subset hsub hug
  have huh : u =ᵐ[volume.restrict (((Ω ⊓ V : Opens ℂ) : Set ℂ) ∩ {z | 0 ≤ z.im})] h :=
    ae_restrict_of_ae_restrict_of_subset hsub (ae_eq_of_planarReflection_ae_eq hSW hrh)
  have hgh := hug'.symm.trans huh
  have heq := eqOn_iteratedFDeriv_of_ae_eq_inter_setOf_im_nonneg (Ω := Ω ⊓ V)
    (V₁ := V) (V₂ := W) (fun z hz => hz.1.2) (fun z hz => hSW (hsub hz)) hg hh hgh le_rfl
  refine ⟨C, fun x hx y hy => ?_⟩
  rw [heq ⟨⟨(hKS hx).1, hKV hx⟩, (hKS hx).2⟩, heq ⟨⟨(hKS hy).1, hKV hy⟩, (hKS hy).2⟩]
  exact hC x hx y hy

/-- **Morrey for `kp > 2` up to the real axis: continuous representatives.** If `1 ≤ p ≤ ∞` and
`2 < k p`, every `u ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) k` agrees almost everywhere on `Ω ∩ {0 ≤ im}` with
a map continuous on `Ω ∩ {0 ≤ im}`. For `p ≤ 2` this needs `k ≥ 2`. -/
theorem MemWkpLoc.exists_continuousOn_ae_eq_of_two_lt_mul_inter_setOf_im_nonneg (hp : 1 ≤ p)
    (hkp : 2 < (k : ℝ≥0∞) * p) (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k u) :
    ∃ g : ℂ → F, ContinuousOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ∧
      u =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] g := by
  obtain ⟨V, hSV, -, hV⟩ := hu.exists_opens_memWkpLoc_planarReflection hp
  obtain ⟨g, hg, hrg⟩ := hV.exists_continuousOn_ae_eq_of_two_lt_mul hp hkp
  exact ⟨g, hg.mono hSV, ae_eq_of_planarReflection_ae_eq hSV hrg⟩

/-! ### Local bounds -/

variable {q : ℝ≥0} [Fact (1 ≤ (q : ℝ≥0∞))]

/-- **Local `C^{j,1-2/q}` bounds on a half-disc, up to the real axis.** For `2 < q < ∞`, a real
centre `x` and a radius `s` there is a constant `K` such that, for every open `Ω` containing the
closure of `ball x s`, every real `u ∈ MemWkpLoc q (Ω ∩ {0 ≤ im}) (j + 1)` is represented on the
open half-disc `ball x s ∩ {0 < im}` by some `v` in `W^{j+1,q}` of it, and agrees almost everywhere
on the half-disc `ball x s ∩ {0 ≤ im}` with a map `g` that is `Cʲ` on an open neighbourhood of it,
whose derivatives of order `i ≤ j` are bounded by `K ‖v‖` and Hölder of exponent `1 - 2 / q` with
constant `K ‖v‖` on `ball x s ∩ {0 ≤ im}`, including its segment of the real axis. -/
theorem MemWkpLoc.exists_contDiffOn_holderOnWith_iteratedFDeriv_ball_inter_setOf_im_nonneg
    (hq : 2 < q) (x s : ℝ) (j : ℕ) :
    ∃ K : ℝ≥0, ∀ {Ω : Opens ℂ} (u : ℂ → ℝ), closure (ball (x : ℂ) s) ⊆ Ω →
      MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (j + 1) u →
      ∃ v : Wkp volume (Opens.upperHalf ⟨ball (x : ℂ) s, isOpen_ball⟩) q (j + 1),
        Wkp.value (j + 1) v =ᵐ[volume.restrict (ball (x : ℂ) s ∩ {z | 0 < z.im})] u ∧
        ∃ V : Opens ℂ, ball (x : ℂ) s ∩ {z | 0 ≤ z.im} ⊆ V ∧ ∃ g : ℂ → ℝ, ContDiffOn ℝ j g V ∧
          u =ᵐ[volume.restrict (ball (x : ℂ) s ∩ {z | 0 ≤ z.im})] g ∧ ∀ i ≤ j,
            (∀ z ∈ ball (x : ℂ) s ∩ {z | 0 ≤ z.im}, ‖iteratedFDeriv ℝ i g z‖ ≤ K * ‖v‖) ∧
              HolderOnWith (K * ‖v‖₊) (1 - 2 / q) (iteratedFDeriv ℝ i g)
                (ball (x : ℂ) s ∩ {z | 0 ≤ z.im}) := by
  obtain ⟨K, hK⟩ := Wkp.exists_contDiffOn_holderOnWith_iteratedFDeriv_complexBall_upperHalf x s hq j
  refine ⟨K, fun {Ω} u hsub hu => ?_⟩
  set B := ball (x : ℂ) s
  set O := B ∩ {z | 0 < z.im}
  -- The bounds hold for the representative `g₁` of the Sobolev space of the open half-disc `O`.
  obtain ⟨v, hv⟩ := hu.exists_wkp_upperHalf (W := ⟨B, isOpen_ball⟩)
    ((isCompact_closedBall _ s).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall)
    hsub
  simp only [Opens.coe_upperHalf, Opens.coe_mk] at hv
  obtain ⟨g₁, hg₁, hvg₁, hb⟩ := hK v
  -- A representative `g` that is `Cʲ` across the real axis agrees with `g₁` on `O`, with all its
  -- derivatives, and the bounds pass to the closure of `O` by continuity.
  obtain ⟨V, hSV, -, g, hg, hug⟩ :=
    hu.exists_opens_contDiffOn_ae_eq_inter_setOf_im_nonneg (by exact_mod_cast hq)
  have hTS : B ∩ {z | 0 ≤ z.im} ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} :=
    inter_subset_inter_left _ (subset_closure.trans hsub)
  have hOT : O ⊆ B ∩ {z | 0 ≤ z.im} := fun z hz => ⟨hz.1, (mem_ofPred.1 hz.2).le⟩
  have hO : IsOpen O := isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
  have hOV : O ⊆ V := (hOT.trans hTS).trans hSV
  have hug₁ : u =ᵐ[volume.restrict O] g₁ := hv.symm.trans hvg₁
  have hug' : u =ᵐ[volume.restrict O] g := ae_restrict_of_ae_restrict_of_subset (hOT.trans hTS) hug
  have hgg₁ : EqOn g g₁ O := Measure.eqOn_open_of_ae_eq (hug'.symm.trans hug₁) hO
    (hg.continuousOn.mono hOV) hg₁.continuousOn
  have heq (i : ℕ) : EqOn (iteratedFDeriv ℝ i g) (iteratedFDeriv ℝ i g₁) O := fun z hz =>
    ((Filter.eventuallyEq_of_mem (hO.mem_nhds hz) hgg₁).iteratedFDeriv ℝ i).eq_of_nhds
  have hcl : B ∩ {z | 0 ≤ z.im} ⊆ closure O := fun z hz => by
    have h := subset_closure_interior_setOfPred_le_im_inter isOpen_ball ⟨hz.2, hz.1⟩
    rwa [interior_inter, isOpen_ball.interior_eq, Complex.interior_setOfPred_le_im,
      inter_comm] at h
  have hcont {i : ℕ} (hi : i ≤ j) (z : ℂ) (hz : z ∈ B ∩ {z | 0 ≤ z.im}) :
      ContinuousAt (iteratedFDeriv ℝ i g) z :=
    (ContinuousOn.continuousOn_iteratedFDeriv hg V.isOpen (by exact_mod_cast hi)).continuousAt
      (V.isOpen.mem_nhds (hSV (hTS hz)))
  refine ⟨v, hv, V, hTS.trans hSV, g, hg, ae_restrict_of_ae_restrict_of_subset hTS hug,
    fun i hi => ⟨fun z hz => ?_, ?_⟩⟩
  · exact ContinuousWithinAt.closure_le (hcl hz) (hcont hi z hz).norm.continuousWithinAt
      continuousWithinAt_const fun y hy => heq i hy ▸ (hb i hi).1 y hy
  · refine HolderOnWith.of_subset_closure (fun a ha b hb' => ?_) hcl (hcont hi)
    rw [heq i ha, heq i hb']
    exact (hb i hi).2 a ha b hb'

end TauCeti
