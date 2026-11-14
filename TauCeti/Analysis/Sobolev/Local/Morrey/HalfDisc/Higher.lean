/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Morrey.Higher
public import TauCeti.Analysis.Sobolev.Local.Reflection
public import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
public import TauCeti.Analysis.Complex.ReImTopology
public import TauCeti.Analysis.Sobolev.Local.Wkp.HalfDisc
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.Planar
import TauCeti.Analysis.Complex.EvenReflection
import TauCeti.Analysis.Sobolev.Local.Locality
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

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
(`TauCeti.eqOn_iteratedFDeriv_of_ae_eq_inter_setOf_im_nonneg`), and for `k ≥ 1` the classical
derivative of `g` is a weak derivative of `u` on `Ω ∩ {0 < im}` lying in `MemWkpLoc p S k`
(`TauCeti.MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn_inter_setOf_im_nonneg`).

## Proof

The order-`k` higher reflection of `u` across the real axis lies in `W^{k,p}_loc` of an open set
`V` between `S` and `Ω`: the union of `Ω ∩ {0 < im}` and of discs in `Ω` centred on the real axis
(`TauCeti.MemWkpLoc.planarReflection_higherReflectionCoeff_ball`, glued by
`TauCeti.memWkpLoc_iSup_iff`). It agrees with `u` on `S`, so the interior results of
`TauCeti.Analysis.Sobolev.Local.Morrey.Higher` and `TauCeti.Analysis.Sobolev.Local.SobolevEmbedding`
on `V` apply to it.

## Main declarations

* `TauCeti.MemWkpLoc.exists_opens_contDiffOn_ae_eq_inter_setOf_im_nonneg`: `Cᵏ` representatives
  of `W^{k+1,p}` maps up to the real axis, for `p > 2`.
* `TauCeti.MemWkpLoc.exists_holderOnWith_iteratedFDeriv_of_isCompact_inter_setOf_im_nonneg`:
  Hölder continuity of the top derivative on compact subsets of `S`.
* `TauCeti.MemWkpLoc.exists_continuousOn_ae_eq_of_two_lt_mul_inter_setOf_im_nonneg`: continuous
  representatives up to the real axis for `k p > 2`.

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

/-- The order-`k` higher reflection of `u ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) k` is in `MemWkpLoc p V k`
on an open set `V` between `Ω ∩ {0 ≤ im}` and `Ω`: the union of the open upper part of `Ω` and of
discs in `Ω` centred on the real axis. -/
private theorem exists_opens_memWkpLoc_planarReflection_aux [CompleteSpace F] (hp : 1 ≤ p)
    (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k u) :
    ∃ V : Opens ℂ, (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ V ∧ (V : Set ℂ) ⊆ Ω ∧
      MemWkpLoc p V k (TauCeti.planarReflection (higherReflectionCoeff k) u) := by
  choose r hr0 hrΩ using fun x : {x : ℝ // (x : ℂ) ∈ Ω} => Metric.isOpen_iff.1 Ω.isOpen _ x.2
  let O : Option {x : ℝ // (x : ℂ) ∈ Ω} → Opens ℂ := fun i =>
    i.elim Ω.upperHalf fun x => ⟨ball (x : ℂ) (r x), isOpen_ball⟩
  refine ⟨⨆ i, O i, fun z hz => ?_, ?_, (memWkpLoc_iSup_iff O).2 ?_⟩
  · rw [Opens.coe_iSup, mem_iUnion]
    rcases (show 0 ≤ z.im from hz.2).lt_or_eq with h | h
    · exact ⟨none, Opens.mem_upperHalf.2 ⟨hz.1, h⟩⟩
    · have hz' : ((z.re : ℝ) : ℂ) = z := Complex.ext rfl (by simpa using h)
      exact ⟨some ⟨z.re, hz' ▸ hz.1⟩, mem_ball.2 ((dist_eq_zero.2 hz'.symm).trans_lt (hr0 _))⟩
  · rw [Opens.coe_iSup]
    refine iUnion_subset fun i => ?_
    cases i with
    | none => exact fun z hz => (Opens.mem_upperHalf.1 hz).1
    | some x => exact hrΩ x
  · rintro (_ | x)
    · refine (hu.mono fun z hz => ⟨(Opens.mem_upperHalf.1 hz).1,
        (Opens.mem_upperHalf.1 hz).2.le⟩).congr_ae ?_
      exact ae_restrict_of_forall_mem Ω.upperHalf.isOpen.measurableSet fun z hz =>
        (planarReflection_of_nonneg _ _ (Opens.mem_upperHalf.1 hz).2.le).symm
    · exact (hu.mono (inter_subset_inter_left _ (hrΩ x)))
        |>.planarReflection_higherReflectionCoeff_ball hp x (r x)

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

/-- **The derivative of a `C¹` representative is a weak derivative, on half-discs.** If `g` is
`C¹` on `Ω ∩ {0 < im}` and agrees almost everywhere on `Ω ∩ {0 ≤ im}` with
`u ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) (k + 1)`, then `fderiv ℝ g` is a weak derivative of `u` on
`Ω ∩ {0 < im}` and lies in `MemWkpLoc p (Ω ∩ {0 ≤ im}) k`, with `Lᵖ` bounds up to the real axis.
-/
theorem MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn_inter_setOf_im_nonneg
    (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) u)
    (hg : ContDiffOn ℝ 1 g Ω.upperHalf)
    (hug : u =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] g) :
    HasWeakFDerivOn volume Ω.upperHalf u (fderiv ℝ g) ∧
      MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k (fderiv ℝ g) := by
  have := hu.completeSpace
  obtain ⟨D, hD, hDk⟩ := hu.exists_weakFDeriv
  rw [Opens.interior_inter_setOf_im_nonneg_eq_upperHalf] at hD
  have hsub : (Ω.upperHalf : Set ℂ) ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} := fun z hz =>
    ⟨(Opens.mem_upperHalf.1 hz).1, (Opens.mem_upperHalf.1 hz).2.le⟩
  have hug' : u =ᵐ[volume.restrict Ω.upperHalf] g := ae_restrict_of_ae_restrict_of_subset hsub hug
  have hg' : HasWeakFDerivOn volume Ω.upperHalf g (fderiv ℝ g) := hg.hasWeakFDerivOn_fderiv
  refine ⟨hg'.congr_ae hug'.symm, hDk.congr_ae ?_⟩
  have hDg := (hD.congr_ae hug').ae_eq hg'
  rw [Opens.coe_upperHalf] at hDg
  refine (ae_restrict_congr_set ?_).1 hDg
  exact Filter.EventuallyEqSet.rfl.inter (Complex.setOf_le_im_ae_eq 0).symm

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
  obtain ⟨V, hSV, hVΩ, hV⟩ := exists_opens_memWkpLoc_planarReflection_aux
    (one_le_two.trans hp.le) hu
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
  obtain ⟨W, hSW, -, hW⟩ := exists_opens_memWkpLoc_planarReflection_aux
    (one_le_two.trans hp.le) hu
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
  obtain ⟨V, hSV, -, hV⟩ := exists_opens_memWkpLoc_planarReflection_aux hp hu
  obtain ⟨g, hg, hrg⟩ := hV.exists_continuousOn_ae_eq_of_two_lt_mul hp hkp
  exact ⟨g, hg.mono hSV, ae_eq_of_planarReflection_ae_eq hSV hrg⟩

/-! ### Local bounds -/

/-- The half-disc of the Lipschitz-domain library, read in the coordinates `z ↦ (im z, re z)`, is
the upper half `ball 0 r ∩ {0 < im}` of the disc of radius `r` in `ℂ`. -/
theorem preimage_equivRealProdL2Swap_halfDisc (r : ℝ) :
    Complex.equivRealProdL2Swap ⁻¹' (halfDisc r : Set (WithLp 2 (ℝ × ℝ))) =
      ball (0 : ℂ) r ∩ {z | 0 < z.im} := by
  ext z
  rw [mem_preimage, SetLike.mem_coe, mem_halfDisc, Complex.equivRealProdL2Swap.norm_map]
  simp

variable {q : ℝ≥0} [Fact (1 ≤ (q : ℝ≥0∞))]

/-- **Local `C^{j,1-2/q}` bounds on a disc.** For `2 < q < ∞` there is a constant `K` such that
every real `u ∈ MemWkpLoc q (ball c r) (j + 1)` is represented on `ball c (r / 2)` by some
`v ∈ W^{j+1,q}(ball c (r / 2))` and agrees almost everywhere there with a map `g` that is `Cʲ` on
`ball c (r / 2)`, whose derivatives of order `i ≤ j` are bounded by `K ‖v‖` and Hölder of
exponent `1 - 2 / q` with constant `K ‖v‖` on `ball c (r / 2)`. -/
theorem MemWkpLoc.exists_contDiffOn_holderOnWith_iteratedFDeriv_ball (hq : 2 < q) (c : ℂ)
    (r : ℝ) (j : ℕ) :
    ∃ K : ℝ≥0, ∀ u : ℂ → ℝ, MemWkpLoc q (ball c r) (j + 1) u →
      ∃ v : Wkp volume (⟨ball c (r / 2), isOpen_ball⟩ : Opens ℂ) q (j + 1),
        Wkp.value (j + 1) v =ᵐ[volume.restrict (ball c (r / 2))] u ∧
        ∃ g : ℂ → ℝ, ContDiffOn ℝ j g (ball c (r / 2)) ∧
          u =ᵐ[volume.restrict (ball c (r / 2))] g ∧ ∀ i ≤ j,
            (∀ z ∈ ball c (r / 2), ‖iteratedFDeriv ℝ i g z‖ ≤ K * ‖v‖) ∧
              HolderOnWith (K * ‖v‖₊) (1 - 2 / q) (iteratedFDeriv ℝ i g) (ball c (r / 2)) := by
  obtain ⟨K, hK⟩ := Wkp.exists_contDiffOn_holderOnWith_iteratedFDeriv_complexBall c (r / 2) hq j
  refine ⟨K, fun u hu => ?_⟩
  have hsub : closure (ball c (r / 2)) ⊆ ball c r := by
    rcases le_or_gt r 0 with hr | hr
    · rw [ball_eq_empty.2 (by linarith), closure_empty]
      exact empty_subset _
    · exact closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith))
  obtain ⟨v, hv⟩ := hu.exists_wkp (Ω := ⟨ball c r, isOpen_ball⟩)
    (W := ⟨ball c (r / 2), isOpen_ball⟩)
    ((isCompact_closedBall c (r / 2)).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall) hsub
  obtain ⟨g, hg, hvg, hb⟩ := hK v
  exact ⟨v, hv, g, hg, hv.symm.trans hvg, hb⟩

/-- **Local `C^{j,1-2/q}` bounds on a half-disc, up to the real axis.** For `2 < q < ∞` there is a
constant `K` such that every real `u ∈ MemWkpLoc q (ball 0 r ∩ {0 ≤ im}) (j + 1)` is represented
on the upper half-disc `ball 0 (r / 2) ∩ {0 < im}` by some `v` in `W^{j+1,q}` of it and agrees
almost everywhere there with a map `g` that is `Cʲ` on it, whose derivatives of order `i ≤ j` are
bounded by `K ‖v‖` and Hölder of exponent `1 - 2 / q` with constant `K ‖v‖` on it. The Hölder
bound is uniform up to the segment of the real axis. -/
theorem MemWkpLoc.exists_contDiffOn_holderOnWith_iteratedFDeriv_ball_inter_setOf_im_nonneg
    (hq : 2 < q) (r : ℝ) (j : ℕ) :
    ∃ K : ℝ≥0, ∀ u : ℂ → ℝ, MemWkpLoc q (ball 0 r ∩ {z | 0 ≤ z.im}) (j + 1) u →
      ∃ v : Wkp volume (Opens.upperHalf ⟨ball 0 (r / 2), isOpen_ball⟩) q (j + 1),
        Wkp.value (j + 1) v =ᵐ[volume.restrict (ball 0 (r / 2) ∩ {z | 0 < z.im})] u ∧
        ∃ g : ℂ → ℝ, ContDiffOn ℝ j g (ball 0 (r / 2) ∩ {z | 0 < z.im}) ∧
          u =ᵐ[volume.restrict (ball 0 (r / 2) ∩ {z | 0 < z.im})] g ∧ ∀ i ≤ j,
            (∀ z ∈ ball 0 (r / 2) ∩ {z | 0 < z.im}, ‖iteratedFDeriv ℝ i g z‖ ≤ K * ‖v‖) ∧
              HolderOnWith (K * ‖v‖₊) (1 - 2 / q) (iteratedFDeriv ℝ i g)
                (ball 0 (r / 2) ∩ {z | 0 < z.im}) := by
  have hO : (⟨Complex.equivRealProdL2Swap ⁻¹' halfDisc (r / 2),
      (halfDisc (r / 2)).isOpen.preimage Complex.equivRealProdL2Swap.continuous⟩ : Opens ℂ) =
      Opens.upperHalf ⟨ball 0 (r / 2), isOpen_ball⟩ :=
    Opens.ext ((preimage_equivRealProdL2Swap_halfDisc _).trans
      (Opens.coe_upperHalf ⟨ball 0 (r / 2), isOpen_ball⟩).symm)
  have h := Wkp.exists_contDiffOn_holderOnWith_iteratedFDeriv_complexHalfDisc (p := q) (r / 2) hq j
  rw [hO, preimage_equivRealProdL2Swap_halfDisc] at h
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun u hu => ?_⟩
  obtain ⟨v, hv⟩ : ∃ v : Wkp volume (Opens.upperHalf ⟨ball 0 (r / 2), isOpen_ball⟩) q (j + 1),
      Wkp.value (j + 1) v =ᵐ[volume.restrict (ball 0 (r / 2) ∩ {z | 0 < z.im})] u := by
    rcases lt_or_ge 0 r with hr | hr
    · exact hu.exists_wkp_ball_half_inter_setOf_im_pos hr
    · have h0 : volume.restrict (ball (0 : ℂ) (r / 2) ∩ {z | 0 < z.im}) = 0 := by
        rw [ball_eq_empty.2 (by linarith), empty_inter, Measure.restrict_empty]
      refine ⟨0, ?_⟩
      rw [h0, ae_zero]
      exact Filter.eventually_bot
  obtain ⟨g, hg, hvg, hb⟩ := hK v
  exact ⟨v, hv, g, hg, hv.symm.trans hvg, hb⟩

end TauCeti
