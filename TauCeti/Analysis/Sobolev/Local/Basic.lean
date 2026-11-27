/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.Analysis.Complex.ReImTopology
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import TauCeti.MeasureTheory.Function.MemLpLoc
public import TauCeti.MeasureTheory.Function.LocallyIntegrable
public import TauCeti.Topology.Sets.Opens
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Local vector-valued Sobolev classes on planar domains

`TauCeti.MemWkpLoc p U k f` requires iterated weak derivatives through order `k` on
`interior U`, with `Lᵖ` bounds on every compact subset of `U` itself, in the sense of the local
`Lᵖ` class `TauCeti.MemLpLoc` for Lebesgue measure on the plane. For half-discs these
bounds reach the real axis, while test functions stay in the interior. On open sets this is
the usual local Sobolev class. Derivatives take values in iterated continuous linear maps,
rather than scalar jets.
These predicates concern actual functions; almost-everywhere changes do not affect membership.
They impose no global integrability condition on the possibly unbounded domain.

This file supplies restriction to arbitrary subsets (also combined with a change of the function
off the subset), linearity, continuous-linear composition, pairing, pointwise product maps of
operator fields, decreasing the integrability exponent, and decreasing the derivative order.
Smoothness on an open neighbourhood gives membership, without requiring a global smooth extension,
and so does smoothness up to the boundary on a set of unique differentiability, such as a
half-disc (`ContDiffOn.memWkpLoc_of_uniqueDiffOn`). Smooth maps on the whole plane are in every
class on every set.
Conversely, let `U` agree almost everywhere with its interior, as open sets and half-discs do.
If `g` is `Cᵏ` on the interior of `U` and agrees almost everywhere on `U` with
`u ∈ MemWkpLoc p U (k + m)`, then `fderiv ℝ g` is a weak derivative of `u`
(`TauCeti.MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn`, for `k ≥ 1`) and
`iteratedFDeriv ℝ k g ∈ MemWkpLoc p U m` (`TauCeti.MemWkpLoc.iteratedFDeriv_of_contDiffOn`).
On a relatively open subset `Ω ∩ {0 ≤ im}` of the closed upper half-plane the interior is
`Ω ∩ {0 < im}` (`TauCeti.interior_inter_setOf_im_nonneg`), and since the real axis is null, local
`Lᵖ` membership there is detected on the upper halves `W ∩ {0 < im}`
(`TopologicalSpace.Opens.upperHalf`) of the open `W` with compact closure inside `Ω`
(`TauCeti.memLpLoc_inter_setOf_im_nonneg_iff`). No boundary trace is asserted here;
extension across the real axis is in `TauCeti.Analysis.Sobolev.Local.Reflection`. On open
domains, every weak derivative of a member of `MemWkpLoc p Ω (k + 1)` is in
`MemWkpLoc p Ω k`; at order one, it is locally `Lᵖ`.
`TauCeti.WeakDerivChainLe` compares the `Lᵖ` norms of two maps and, recursively, of every pair of
their weak derivatives through a given order.
In positive order, completeness is inherited from the native weak-derivative predicate; the
definitions admit every real normed codomain without an additional typeclass assumption.
The continuous-linear composition result requires a complete target, as does the native
weak-derivative result it uses.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (local Sobolev spaces and their elementary operations).
-/

public noncomputable section

open MeasureTheory TopologicalSpace

namespace TauCeti

variable {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
  {p q : ENNReal} {U V : Set ℂ} {f g : ℂ → F}

/-- **Local `Lᵖ` on a half-disc through upper halves.** A function is locally `Lᵖ` on
`Ω ∩ {0 ≤ im}`, up to the real axis, exactly when it is `Lᵖ` on the upper half `W ∩ {0 < im}` of
every open `W` whose closure is compact and contained in `Ω`. The real axis is null, so the
compact sets reaching it see no more than these upper halves. -/
theorem memLpLoc_inter_setOf_im_nonneg_iff {Ω : Opens ℂ} :
    MemLpLoc p ((Ω : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) f ↔
      ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
        MemLp f p (volume.restrict (W.upperHalf : Set ℂ)) := by
  refine ⟨fun hf W hWc hWΩ => ?_, fun h => memLpLoc_iff.2 fun K hKU hK => ?_⟩
  · have hK : IsCompact (closure (W : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) :=
      hWc.inter_right (isClosed_le continuous_const Complex.continuous_im)
    refine (memLpLoc_iff.1 hf _ (Set.inter_subset_inter_left _ hWΩ) hK).mono_measure
      (Measure.restrict_mono ?_ le_rfl)
    intro z hz
    obtain ⟨hzW, hz0⟩ := Opens.mem_upperHalf.1 hz
    exact ⟨subset_closure hzW, hz0.le⟩
  · obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen
      (hKU.trans Set.inter_subset_left)
    refine (h ⟨W, hWo⟩ hWc hWΩ).mono_measure (Measure.restrict_mono_ae ?_)
    filter_upwards [(Complex.setOf_le_im_ae_eq 0).subset] with z hz hzK
    exact Opens.mem_upperHalf.2 ⟨hKW hzK, hz (hKU hzK).2⟩

variable [NormedSpace ℝ F] [NormedSpace ℝ G]

/-- The iterated weak derivatives through order `k` exist on `interior U` and are `Lᵖ` on
every compact subset of `U`, including compact sets reaching its boundary.
The first derivative takes values in `ℂ →L[ℝ] F`; higher derivatives iterate this construction.
No integrability at infinity or boundary trace is required. -/
def MemWkpLoc (p : ENNReal) (U : Set ℂ) :
    (k : ℕ) → {F : Type*} → [NormedAddCommGroup F] → [NormedSpace ℝ F] → (ℂ → F) → Prop
  | 0, _, _, _, f => MemLpLoc p U f
  | k + 1, F, _, _, f => MemLpLoc p U f ∧
      ∃ D : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D ∧ MemWkpLoc p U k D

variable {Ω : Opens ℂ} {k l : ℕ}

/-- At order zero the local Sobolev class is exactly the local `Lᵖ` class. -/
@[simp]
theorem memWkpLoc_zero_iff : MemWkpLoc p U 0 f ↔ MemLpLoc p U f := Iff.rfl

/-- The successor-order characterization supplies a weak derivative in the preceding class. -/
theorem memWkpLoc_succ_iff : MemWkpLoc p U (k + 1) f ↔ MemLpLoc p U f ∧
    ∃ D : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D ∧
      MemWkpLoc p U k D := Iff.rfl

/-- On an open domain, the successor-order weak derivative is tested on the domain itself. -/
theorem memWkpLoc_succ_iff_of_isOpen : MemWkpLoc p Ω (k + 1) f ↔ MemLpLoc p Ω f ∧
    ∃ D : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume Ω f D ∧ MemWkpLoc p Ω k D := by
  simp only [memWkpLoc_succ_iff, Opens.interior_coe]

/-- Every local Sobolev function is locally `Lᵖ`. -/
theorem MemWkpLoc.memLpLoc (hf : MemWkpLoc p U k f) : MemLpLoc p U f := by
  cases k with
  | zero => exact hf
  | succ k => exact hf.1

/-- A positive-order local Sobolev function has a weak derivative of the preceding order. -/
theorem MemWkpLoc.exists_weakFDeriv (hf : MemWkpLoc p U (k + 1) f) :
    ∃ D : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D ∧
      MemWkpLoc p U k D := hf.2

/-- On an open domain, positive-order membership gives a weak derivative on that domain. -/
theorem MemWkpLoc.exists_weakFDeriv_of_isOpen (hf : MemWkpLoc p Ω (k + 1) f) :
    ∃ D : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume Ω f D ∧ MemWkpLoc p Ω k D :=
  (memWkpLoc_succ_iff_of_isOpen.mp hf).2

/-- Positive-order membership retains the completeness required by weak derivatives. -/
theorem MemWkpLoc.completeSpace (hf : MemWkpLoc p U (k + 1) f) : CompleteSpace F := by
  obtain ⟨D, hD, _⟩ := hf.exists_weakFDeriv
  exact hD.completeSpace

/-- Restriction preserves the interior weak derivatives and the bounds on compact subsets. -/
theorem MemWkpLoc.mono (hf : MemWkpLoc p U k f) (hVU : V ⊆ U) :
    MemWkpLoc p V k f := by
  induction k generalizing F with
  | zero => exact hf.mono_set hVU
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    exact ⟨hp.mono_set hVU, D, hD.mono (interior_mono hVU), ih hk⟩

/-- Almost-everywhere changes of the function preserve its local Sobolev class. -/
theorem MemWkpLoc.congr_ae (hf : MemWkpLoc p U k f)
    (hfg : f =ᵐ[volume.restrict U] g) : MemWkpLoc p U k g := by
  cases k with
  | zero => exact hf.congr_ae hfg
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    exact ⟨hp.congr_ae hfg, D,
      hD.congr_ae (ae_mono (Measure.restrict_mono_set volume interior_subset) hfg), hk⟩

/-- Restricting to a subset preserves the local Sobolev class of any function agreeing with the
original one on that subset. -/
theorem MemWkpLoc.congr_mono (hf : MemWkpLoc p U k f) (hgf : Set.EqOn g f V) (hVU : V ⊆ U) :
    MemWkpLoc p V k g := by
  cases k with
  | zero => exact MemLpLoc.congr_mono hf hgf hVU
  | succ k =>
    obtain ⟨-, D, hD, hk⟩ := hf.mono hVU
    exact ⟨hf.memLpLoc.congr_mono hgf hVU, D, hD.congr_ae <| by
      filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with z hz using
        (hgf (interior_subset hz)).symm, hk⟩

/-- The local Sobolev class only depends on the values on the set. -/
theorem MemWkpLoc.congr (hf : MemWkpLoc p U k f) (hgf : Set.EqOn g f U) : MemWkpLoc p U k g :=
  hf.congr_mono hgf subset_rfl

/-- Every weak derivative of a member of `MemWkpLoc p Ω (k + 1)` is in `MemWkpLoc p Ω k`, not only
the one supplied by the definition: weak derivatives are unique almost everywhere. -/
theorem MemWkpLoc.memWkpLoc_of_hasWeakFDerivOn (hf : MemWkpLoc p Ω (k + 1) f)
    {D : ℂ → ℂ →L[ℝ] F} (hD : HasWeakFDerivOn volume Ω f D) : MemWkpLoc p Ω k D := by
  obtain ⟨D', hD', hD'k⟩ := hf.exists_weakFDeriv_of_isOpen
  exact hD'k.congr_ae (hD'.ae_eq hD)

/-- Every weak derivative of a member of `MemWkpLoc p Ω 1` is locally `Lᵖ` on `Ω`, not only the
one supplied by the definition: weak derivatives are unique almost everywhere. -/
theorem MemWkpLoc.memLpLoc_of_hasWeakFDerivOn (hf : MemWkpLoc p Ω 1 f)
    {D : ℂ → ℂ →L[ℝ] F} (hD : HasWeakFDerivOn volume Ω f D) : MemLpLoc p Ω D :=
  memWkpLoc_zero_iff.1 (hf.memWkpLoc_of_hasWeakFDerivOn hD)

/-- Decreasing the integrability exponent preserves each local derivative order. -/
theorem MemWkpLoc.mono_exponent (hf : MemWkpLoc p U k f) (hqp : q ≤ p) :
    MemWkpLoc q U k f := by
  induction k generalizing F with
  | zero => exact hf.mono_exponent hqp
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    exact ⟨hp.mono_exponent hqp, D, hD, ih hk⟩

/-- Dropping the top derivative preserves local Sobolev membership. -/
theorem MemWkpLoc.of_succ (hf : MemWkpLoc p U (k + 1) f) : MemWkpLoc p U k f := by
  induction k generalizing F with
  | zero => exact hf.1
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    exact ⟨hp, D, hD, ih hk⟩

/-- Membership at any smaller derivative order follows from membership at a larger one. -/
theorem MemWkpLoc.of_le (hf : MemWkpLoc p U k f) (hlk : l ≤ k) : MemWkpLoc p U l f := by
  induction hlk with
  | refl => exact hf
  | step _ ih => exact ih hf.of_succ

/-- The zero function lies in every local Sobolev class with complete codomain. -/
@[simp]
theorem memWkpLoc_zero_fun [CompleteSpace F] : MemWkpLoc p U k (0 : ℂ → F) := by
  induction k generalizing F with
  | zero => exact memLpLoc_zero
  | succ k ih => exact ⟨memLpLoc_zero, 0, hasWeakFDerivOn_zero, ih⟩

/-- Local Sobolev membership is closed under addition. -/
theorem MemWkpLoc.add (hf : MemWkpLoc p U k f) (hg : MemWkpLoc p U k g) :
    MemWkpLoc p U k (f + g) := by
  induction k generalizing F with
  | zero => exact hf.add hg
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    obtain ⟨hq, D', hD', hk'⟩ := hg
    exact ⟨hp.add hq, D + D', hD.add hD', ih hk hk'⟩

/-- Local Sobolev membership is closed under negation. -/
theorem MemWkpLoc.neg (hf : MemWkpLoc p U k f) : MemWkpLoc p U k (-f) := by
  induction k generalizing F with
  | zero => exact hf.neg
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    exact ⟨hp.neg, -D, hD.neg, ih hk⟩

/-- Local Sobolev membership is closed under subtraction. -/
theorem MemWkpLoc.sub (hf : MemWkpLoc p U k f) (hg : MemWkpLoc p U k g) :
    MemWkpLoc p U k (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Real scalar multiplication preserves local Sobolev membership. -/
theorem MemWkpLoc.const_smul (hf : MemWkpLoc p U k f) (c : ℝ) :
    MemWkpLoc p U k (c • f) := by
  induction k generalizing F with
  | zero => exact hf.const_smul c
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    exact ⟨hp.const_smul c, c • D, hD.const_smul c, ih hk⟩

/-- Continuous linear maps of the codomain preserve all local weak derivative orders. -/
theorem MemWkpLoc.clm_comp [CompleteSpace G] (hf : MemWkpLoc p U k f)
    (A : F →L[ℝ] G) : MemWkpLoc p U k (fun z => A (f z)) := by
  induction k generalizing F G with
  | zero => exact hf.clm_comp A
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    exact ⟨hp.clm_comp A, fun z => A.comp (D z), hD.clm_comp A,
      ih hk ((ContinuousLinearMap.compL ℝ ℂ F G) A)⟩

/-- **Pairs of local Sobolev maps.** Two maps in the local Sobolev class of order `k` pair to a map
in the same class, with values in the product. -/
theorem MemWkpLoc.prodMk [CompleteSpace F] [CompleteSpace G] {g : ℂ → G}
    (hf : MemWkpLoc p U k f) (hg : MemWkpLoc p U k g) :
    MemWkpLoc p U k (fun z => (f z, g z)) := by
  have h := (hf.clm_comp (ContinuousLinearMap.inl ℝ F G)).add
    (hg.clm_comp (ContinuousLinearMap.inr ℝ F G))
  convert h using 1
  ext z <;> simp

/-- **Products of operator fields.** If two fields of continuous linear maps are in the local
Sobolev class of order `k`, so is their pointwise product map `(A z).prodMap (B z)`. -/
theorem MemWkpLoc.prodMap {E₁ E₂ E₃ E₄ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂] [NormedAddCommGroup E₃]
    [NormedSpace ℝ E₃] [NormedAddCommGroup E₄] [NormedSpace ℝ E₄] [CompleteSpace E₄]
    {A : ℂ → E₁ →L[ℝ] E₂} {B : ℂ → E₃ →L[ℝ] E₄} (hA : MemWkpLoc p U k A)
    (hB : MemWkpLoc p U k B) : MemWkpLoc p U k (fun z => (A z).prodMap (B z)) := by
  simpa using (hA.prodMk hB).clm_comp (ContinuousLinearMap.prodMapL ℝ E₁ E₂ E₃ E₄)

/-- A continuous linear change of codomain preserves and reflects every local weak
Sobolev order. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.comp_memWkpLoc_iff (e : F ≃L[ℝ] G) :
    MemWkpLoc p U k (fun z => e (f z)) ↔ MemWkpLoc p U k f := by
  cases k with
  | zero =>
    simpa only [memWkpLoc_zero_iff] using
      (e.comp_memLpLoc_iff (p := p) (U := U) (f := f))
  | succ k =>
    constructor
    · intro h
      have : CompleteSpace G := h.completeSpace
      have : CompleteSpace F :=
        (e.isUniformEmbedding.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance
      simpa only [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] using
        h.clm_comp e.symm.toContinuousLinearMap
    · intro h
      have : CompleteSpace F := h.completeSpace
      have : CompleteSpace G :=
        (e.isUniformEmbedding.isUniformInducing.completeSpace_congr e.surjective).mp inferInstance
      exact h.clm_comp e.toContinuousLinearMap

/-- Constant functions belong to every local Sobolev class. -/
@[simp]
theorem memWkpLoc_const [CompleteSpace F] (c : F) : MemWkpLoc p U k (fun _ => c) := by
  cases k with
  | zero => exact memLpLoc_const c
  | succ k =>
    refine ⟨memLpLoc_const c, 0, ?_, memWkpLoc_zero_fun⟩
    apply hasWeakFDerivOn_iff.mpr
    exact fun v => hasWeakLineDerivOn_const (μ := volume) (Ω := Opens.interior U) (v := v) c

/-- Finite sums of local Sobolev functions remain in the same class. -/
theorem MemWkpLoc.sum {ι : Type*} [CompleteSpace F] (s : Finset ι)
    {f : ι → ℂ → F} (hf : ∀ i ∈ s, MemWkpLoc p U k (f i)) :
    MemWkpLoc p U k (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, Pi.zero_def] using
      (memWkpLoc_zero_fun (p := p) (U := U) (k := k) (F := F))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi, Pi.add_def] using
      (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- A map that is `Cᵏ` on an open neighbourhood of `U` has locally `Lᵖ` weak derivatives
through order `k` on `U`, with bounds reaching its boundary, for every exponent. -/
theorem _root_.ContDiffOn.memWkpLoc [CompleteSpace F]
    (hf : ContDiffOn ℝ k f (Ω : Set ℂ)) (hU : U ⊆ Ω) : MemWkpLoc p U k f := by
  induction k generalizing F with
  | zero => exact (hf.continuousOn.mono hU).memLpLoc
  | succ k ih =>
    have hD : ContDiffOn ℝ k (fderiv ℝ f) (Ω : Set ℂ) :=
      hf.fderiv_of_isOpen Ω.isOpen (by simp)
    refine ⟨(hf.continuousOn.mono hU).memLpLoc, fderiv ℝ f, ?_, ih hD⟩
    exact (hf.of_le (by simp)).hasWeakFDerivOn_fderiv.mono (interior_subset.trans hU)

/-- **`Cᵏ` up to the boundary.** A map that is `Cᵏ` on a set `U` of unique differentiability, such
as a half-disc `Ω ∩ {0 ≤ im}`, has locally `Lᵖ` weak derivatives through order `k` on `U`, with
bounds reaching its boundary, for every exponent. The first weak derivative is the derivative
within `U`, which is continuous up to the boundary of `U`. -/
theorem _root_.ContDiffOn.memWkpLoc_of_uniqueDiffOn [CompleteSpace F]
    (hf : ContDiffOn ℝ k f U) (hU : UniqueDiffOn ℝ U) : MemWkpLoc p U k f := by
  induction k generalizing F with
  | zero => exact hf.continuousOn.memLpLoc
  | succ k ih =>
    refine ⟨hf.continuousOn.memLpLoc, fderivWithin ℝ f U, ?_, ih (hf.fderivWithin hU le_rfl)⟩
    -- on the interior of `U` the derivative within `U` is the classical derivative
    refine ((hf.of_le (by simp)).mono interior_subset).hasWeakFDerivOn_fderiv.congr_ae_deriv
      ((ae_restrict_iff' (Opens.interior U).isOpen.measurableSet).2
        (Filter.Eventually.of_forall fun z hz ↦ ?_))
    exact (fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.1 hz)).symm

/-- A `Cᵏ` map on the whole plane is in the local class `W^{k,p}` on every set, for every
exponent. -/
theorem _root_.ContDiff.memWkpLoc [CompleteSpace F] (hf : ContDiff ℝ k f) :
    MemWkpLoc p U k f :=
  hf.contDiffOn.memWkpLoc (Ω := ⊤) ((Set.subset_univ U).trans_eq Opens.coe_top.symm)

/-! ### Bounds for chains of weak derivatives -/

section WeakDerivChainLe

/-- `WeakDerivChainLe p S T C m f g` bounds the iterated weak derivatives of `f` through order `m`
by those of `g`: the `Lᵖ(S)` norm of `f` is at most `C` times the `Lᵖ(T)` norm of `g`, and for
every weak derivative `Df` of `f` on the interior of `S` and every weak derivative `Dg` of `g` on
the interior of `T`, the pair `Df`, `Dg` satisfies the same through order `m - 1`. Since the
quantification is over all weak derivatives, the bound holds for every choice of the iterated
derivatives `D^i f` and `D^i g`, `i ≤ m`. -/
def WeakDerivChainLe (p : ENNReal) (S T : Set ℂ) (C : ENNReal) :
    (m : ℕ) → {F : Type*} → [NormedAddCommGroup F] → [NormedSpace ℝ F] → (ℂ → F) → (ℂ → F) →
      Prop
  | 0, _, _, _, f, g => eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T)
  | m + 1, F, _, _, f, g =>
      eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T) ∧
        ∀ Df Dg : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior S) f Df →
          HasWeakFDerivOn volume (Opens.interior T) g Dg → WeakDerivChainLe p S T C m Df Dg

variable {C : ENNReal} {S T : Set ℂ} {m : ℕ}

/-- At order zero the chain bound is the `Lᵖ` bound. -/
@[simp]
theorem weakDerivChainLe_zero_iff :
    WeakDerivChainLe p S T C 0 f g ↔
      eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T) :=
  Iff.rfl

/-- At a successor order the chain bound is the `Lᵖ` bound together with the chain bound for
every pair of weak derivatives. -/
theorem weakDerivChainLe_succ_iff :
    WeakDerivChainLe p S T C (m + 1) f g ↔
      eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T) ∧
        ∀ Df Dg : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior S) f Df →
          HasWeakFDerivOn volume (Opens.interior T) g Dg → WeakDerivChainLe p S T C m Df Dg :=
  Iff.rfl

/-- A chain bound gives the `Lᵖ` bound at order zero. -/
theorem WeakDerivChainLe.eLpNorm_le (h : WeakDerivChainLe p S T C m f g) :
    eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T) := by
  cases m with
  | zero => exact h
  | succ m => exact h.1

/-- A chain bound passes to every pair of weak derivatives, one order lower. -/
theorem WeakDerivChainLe.weakFDeriv (h : WeakDerivChainLe p S T C (m + 1) f g)
    {Df Dg : ℂ → ℂ →L[ℝ] F} (hf : HasWeakFDerivOn volume (Opens.interior S) f Df)
    (hg : HasWeakFDerivOn volume (Opens.interior T) g Dg) : WeakDerivChainLe p S T C m Df Dg :=
  h.2 Df Dg hf hg

end WeakDerivChainLe

/-! ### Classical derivatives of `Cᵏ` representatives -/

variable {m : ℕ} {u : ℂ → F}

/-- **The derivative of a `C¹` representative is a weak derivative.** Let `U` agree almost
everywhere with its interior, as an open set does and as a half-disc `Ω ∩ {0 ≤ im}` does
(`TauCeti.inter_setOf_im_nonneg_ae_eq_interior`). If `g` is `C¹` on the interior of `U` and
agrees almost everywhere on `U` with `u ∈ MemWkpLoc p U (k + 1)`, then `fderiv ℝ g` is a weak
derivative of `u` on the interior of `U` and lies in `MemWkpLoc p U k`. By uniqueness of weak
derivatives (`TauCeti.HasWeakFDerivOn.ae_eq`), every weak derivative of `u` on the interior of `U`
agrees with `fderiv ℝ g` almost everywhere on `U`. -/
theorem MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn (hu : MemWkpLoc p U (k + 1) u)
    (hU : U =ᵐ[volume] (Opens.interior U : Set ℂ)) (hg : ContDiffOn ℝ 1 g (Opens.interior U))
    (hug : u =ᵐ[volume.restrict U] g) :
    HasWeakFDerivOn volume (Opens.interior U) u (fderiv ℝ g) ∧ MemWkpLoc p U k (fderiv ℝ g) := by
  have := hu.completeSpace
  rw [Measure.restrict_congr_set hU] at hug
  have hg' : HasWeakFDerivOn volume (Opens.interior U) g (fderiv ℝ g) := hg.hasWeakFDerivOn_fderiv
  obtain ⟨D, hD, hDk⟩ := hu.exists_weakFDeriv
  refine ⟨hg'.congr_ae hug.symm, hDk.congr_ae ?_⟩
  rw [Measure.restrict_congr_set hU]
  exact (hD.congr_ae hug).ae_eq hg'

/-- **Iterated derivatives of a `Cᵏ` representative.** Let `U` agree almost everywhere with its
interior, as an open set does and as a half-disc `Ω ∩ {0 ≤ im}` does
(`TauCeti.inter_setOf_im_nonneg_ae_eq_interior`). If `g` is `Cᵏ` on the interior of `U` and agrees
almost everywhere on `U` with `u ∈ MemWkpLoc p U (k + m)`, then `iteratedFDeriv ℝ k g` lies in
`MemWkpLoc p U m`. No restriction on `p` is needed. -/
theorem MemWkpLoc.iteratedFDeriv_of_contDiffOn (hu : MemWkpLoc p U (k + m) u)
    (hU : U =ᵐ[volume] (Opens.interior U : Set ℂ)) (hg : ContDiffOn ℝ k g (Opens.interior U))
    (hug : u =ᵐ[volume.restrict U] g) :
    MemWkpLoc p U m (iteratedFDeriv ℝ k g) := by
  induction k generalizing F with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ ℂ F).symm.toContinuousLinearEquiv.comp_memWkpLoc_iff.2
      ((Nat.zero_add m ▸ hu).congr_ae hug)
  | succ k ih =>
    rw [Nat.add_right_comm] at hu
    obtain ⟨-, hDk⟩ := hu.hasWeakFDerivOn_fderiv_of_contDiffOn hU
      (hg.of_le (by exact_mod_cast Nat.le_add_left 1 k)) hug
    have hgk : ContDiffOn ℝ k (fderiv ℝ g) (Opens.interior U) :=
      hg.fderiv_of_isOpen isOpen_interior (by push_cast; rfl)
    have h := ih hDk hgk (Filter.EventuallyEq.refl _ _)
    have heq : iteratedFDeriv ℝ (k + 1) g =
        fun z => (continuousMultilinearCurryRightEquiv' ℝ k ℂ F).symm
          (iteratedFDeriv ℝ k (fderiv ℝ g) z) := by
      ext1 z
      exact iteratedFDeriv_succ_eq_comp_right
    rw [heq]
    exact (continuousMultilinearCurryRightEquiv' ℝ k ℂ F).symm.toContinuousLinearEquiv
      |>.comp_memWkpLoc_iff.2 h

end TauCeti
