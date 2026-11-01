/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import TauCeti.Analysis.Normed.Operator.WeaklyCompact
import Mathlib.Analysis.Normed.Module.Completion
import TauCeti.Analysis.Normed.Lp.Schur
import TauCeti.Analysis.Normed.Module.WeakSpace.Bounded
import TauCeti.Analysis.Normed.Module.WeakSpace.SeqCompact
import TauCeti.Analysis.Normed.Operator.WeaklyCompact.ZeroAtInfty
import TauCeti.Topology.Algebra.Module.WeakSpace
import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic

/-!
# Dunford–Pettis operators and the Dunford–Pettis property

A bounded operator `T : E →L[𝕜] F` between normed spaces over a normed field is *Dunford–Pettis*
(`ContinuousLinearMap.IsDunfordPettis`) if it maps weakly convergent sequences to norm-convergent
sequences. In Banach space theory these operators are also called *completely continuous*; the
name `ContinuousLinearMap.IsCompletelyContinuous` is already used in Tau Ceti for Serre's notion
of uniform approximability by operators of finite rank, which is a different property.

Dunford–Pettis operators are closed under sums, scalar multiples and composition on either side
with bounded operators. Between real or complex normed spaces they are exactly the operators taking
weakly compact sets to norm-compact sets, and every compact operator is Dunford–Pettis.

A normed space `E` has the *Dunford–Pettis property* (`TauCeti.HasDunfordPettisProperty`) if
every weakly compact operator from `E` into a Banach space is Dunford–Pettis. The main result is
the sequence criterion: `E` has the Dunford–Pettis property iff `f n (x n) → 0` whenever `x` is
weakly null in `E` and `f` is weakly null in the dual `StrongDual 𝕜 E`. The forward direction
tests the property on the weakly compact operator `E → c₀` sending `y` to `n ↦ f n y`, using the
duality `c₀* = ℓ¹`; the converse uses Gantmacher's theorem and Šmulian's theorem in the dual. The
criterion shows that the Dunford–Pettis property does not depend on the universe of the targets.
By Schur's theorem every bounded operator out of `ℓ¹` is Dunford–Pettis, so `ℓ¹` has the
Dunford–Pettis property.

## Main definitions

* `ContinuousLinearMap.IsDunfordPettis`: weakly convergent sequences are mapped to norm-convergent
  sequences.
* `TauCeti.HasDunfordPettisProperty`: every weakly compact operator into a Banach space is
  Dunford–Pettis.

## Main results

* `ContinuousLinearMap.isDunfordPettis_iff_tendsto_zero`: it suffices to test weakly null
  sequences.
* `ContinuousLinearMap.isDunfordPettis_iff_forall_isCompact_image`: an operator is Dunford–Pettis
  iff it maps weakly compact sets to norm-compact sets.
* `IsCompactOperator.isDunfordPettis`: compact operators are Dunford–Pettis.
* `TauCeti.hasDunfordPettisProperty_iff`: the sequence criterion for the Dunford–Pettis property.
* `TauCeti.HasDunfordPettisProperty.isDunfordPettis`: under the Dunford–Pettis property, weakly
  compact operators into normed spaces in any universe are Dunford–Pettis.
* `lp.hasDunfordPettisProperty_one`: `ℓ¹` has the Dunford–Pettis property.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §5.4.
-/

public section

open Filter Function Metric NormedSpace Set Topology
open scoped ZeroAtInfty

namespace ContinuousLinearMap

section Ideal

variable {𝕜 D E F G : Type*} [NormedField 𝕜]
  [SeminormedAddCommGroup D] [NormedSpace 𝕜 D]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A bounded operator is *Dunford–Pettis*, or *completely continuous* in the sense of Banach
space theory, if it maps weakly convergent sequences to norm-convergent sequences. -/
def IsDunfordPettis (T : E →L[𝕜] F) : Prop :=
  ∀ ⦃x : ℕ → E⦄ ⦃a : E⦄,
    Tendsto (fun n ↦ toWeakSpace 𝕜 E (x n)) atTop (𝓝 (toWeakSpace 𝕜 E a)) →
      Tendsto (fun n ↦ T (x n)) atTop (𝓝 (T a))

/-- Unfolding lemma for `ContinuousLinearMap.IsDunfordPettis`. -/
theorem isDunfordPettis_def {T : E →L[𝕜] F} :
    T.IsDunfordPettis ↔ ∀ ⦃x : ℕ → E⦄ ⦃a : E⦄,
      Tendsto (fun n ↦ toWeakSpace 𝕜 E (x n)) atTop (𝓝 (toWeakSpace 𝕜 E a)) →
        Tendsto (fun n ↦ T (x n)) atTop (𝓝 (T a)) :=
  Iff.rfl

/-- An operator is Dunford–Pettis iff it maps weakly null sequences to norm-null sequences. -/
theorem isDunfordPettis_iff_tendsto_zero {T : E →L[𝕜] F} :
    T.IsDunfordPettis ↔ ∀ ⦃x : ℕ → E⦄,
      Tendsto (fun n ↦ toWeakSpace 𝕜 E (x n)) atTop (𝓝 0) →
        Tendsto (fun n ↦ T (x n)) atTop (𝓝 0) := by
  refine ⟨fun hT x hx ↦ ?_, fun h x a hx ↦ ?_⟩
  · simpa using hT (a := 0) (by simpa using hx)
  · have := h (x := fun n ↦ x n - a) (by simpa using hx.sub_const (toWeakSpace 𝕜 E a))
    simpa [tendsto_sub_nhds_zero_iff] using this

/-- The zero operator is Dunford–Pettis. -/
theorem isDunfordPettis_zero : (0 : E →L[𝕜] F).IsDunfordPettis := fun _ _ _ ↦ by
  simpa using tendsto_const_nhds

/-- A sum of Dunford–Pettis operators is Dunford–Pettis. -/
theorem IsDunfordPettis.add {T S : E →L[𝕜] F} (hT : T.IsDunfordPettis)
    (hS : S.IsDunfordPettis) : (T + S).IsDunfordPettis := fun _ _ hx ↦ by
  simpa using (hT hx).add (hS hx)

/-- A scalar multiple of a Dunford–Pettis operator is Dunford–Pettis. -/
theorem IsDunfordPettis.smul {S : Type*} [DistribSMul S F] [SMulCommClass 𝕜 S F]
    [ContinuousConstSMul S F] {T : E →L[𝕜] F} (hT : T.IsDunfordPettis) (c : S) :
    (c • T).IsDunfordPettis := fun _ _ hx ↦ by
  simpa using (hT hx).const_smul c

/-- The negative of a Dunford–Pettis operator is Dunford–Pettis. -/
theorem IsDunfordPettis.neg {T : E →L[𝕜] F} (hT : T.IsDunfordPettis) :
    (-T).IsDunfordPettis := fun _ _ hx ↦ by
  simpa using (hT hx).neg

/-- A difference of Dunford–Pettis operators is Dunford–Pettis. -/
theorem IsDunfordPettis.sub {T S : E →L[𝕜] F} (hT : T.IsDunfordPettis)
    (hS : S.IsDunfordPettis) : (T - S).IsDunfordPettis := by
  simpa [sub_eq_add_neg] using hT.add hS.neg

/-- Dunford–Pettis operators form a right ideal: precomposing with a bounded operator preserves
the Dunford–Pettis property. -/
theorem IsDunfordPettis.comp_clm {T : E →L[𝕜] F} (hT : T.IsDunfordPettis) (S : D →L[𝕜] E) :
    (T.comp S).IsDunfordPettis := fun _ _ hx ↦
  hT (((WeakSpace.map S).continuous.tendsto _).comp hx)

/-- Dunford–Pettis operators form a left ideal: postcomposing with a bounded operator preserves
the Dunford–Pettis property. -/
theorem IsDunfordPettis.clm_comp {T : E →L[𝕜] F} (hT : T.IsDunfordPettis) (S : F →L[𝕜] G) :
    (S.comp T).IsDunfordPettis := fun _ _ hx ↦
  (S.continuous.tendsto _).comp (hT hx)

end Ideal

section CompactOperator

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Compact operators are Dunford–Pettis. -/
theorem _root_.IsCompactOperator.isDunfordPettis {T : E →L[𝕜] F} (hT : IsCompactOperator T) :
    T.IsDunfordPettis := fun x _ hx ↦ by
  -- A weakly convergent sequence is bounded, so its image lies in a norm-compact set, on which
  -- weak convergence is norm convergence.
  obtain ⟨K, hK, hTK⟩ := hT.image_subset_compact_of_bounded hx.isBounded_range_of_toWeakSpace
  exact TauCeti.tendsto_of_tendsto_toWeakSpace_of_isCompact (𝕜 := 𝕜) hK
    (Eventually.of_forall fun n ↦ hTK (mem_image_of_mem T (mem_range_self n)))
    (((WeakSpace.map T).continuous.tendsto _).comp hx)

end CompactOperator

section Compact

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- An operator is Dunford–Pettis iff it maps weakly compact sets to norm-compact sets. -/
theorem isDunfordPettis_iff_forall_isCompact_image {T : E →L[𝕜] F} :
    T.IsDunfordPettis ↔ ∀ K : Set E, IsCompact (toWeakSpace 𝕜 E '' K) → IsCompact (T '' K) := by
  constructor
  · -- By Šmulian's theorem a weakly compact set is weakly sequentially compact.
    intro hT K hK
    refine IsSeqCompact.isCompact fun y hy ↦ ?_
    choose x hxK hxy using hy
    obtain rfl : y = T ∘ x := funext fun n ↦ (hxy n).symm
    obtain ⟨-, ⟨a, ha, rfl⟩, φ, hφ, hlim⟩ := TauCeti.isSeqCompact_toWeakSpace_of_isCompact hK
      (x := fun n ↦ toWeakSpace 𝕜 E (x n)) fun n ↦ mem_image_of_mem _ (hxK n)
    exact ⟨T a, mem_image_of_mem T ha, φ, hφ, hT (x := x ∘ φ) hlim⟩
  · -- A weakly convergent sequence together with its limit is weakly compact.
    intro h x a hx
    have hK := h (insert a (range x)) <| by
      rw [image_insert_eq, ← range_comp]
      exact hx.isCompact_insert_range
    refine TauCeti.tendsto_of_tendsto_toWeakSpace_of_isCompact (𝕜 := 𝕜) hK
      (Eventually.of_forall fun n ↦ mem_image_of_mem T (mem_insert_of_mem _ (mem_range_self n)))
      ?_
    exact ((WeakSpace.map T).continuous.tendsto _).comp hx

/-- If `f n (x n) → 0` whenever `x` is weakly null in `E` and `f` is weakly null in the dual,
then every weakly compact operator from `E` is Dunford–Pettis. The codomain need not be complete.
-/
theorem IsWeaklyCompact.isDunfordPettis_of_tendsto_apply {T : E →L[𝕜] F}
    (hT : T.IsWeaklyCompact)
    (h : ∀ ⦃x : ℕ → E⦄ ⦃f : ℕ → StrongDual 𝕜 E⦄,
      Tendsto (fun n ↦ toWeakSpace 𝕜 E (x n)) atTop (𝓝 0) →
        Tendsto (fun n ↦ toWeakSpace 𝕜 (StrongDual 𝕜 E) (f n)) atTop (𝓝 0) →
          Tendsto (fun n ↦ f n (x n)) atTop (𝓝 0)) :
    T.IsDunfordPettis := by
  refine isDunfordPettis_iff_tendsto_zero.2 fun x hx ↦ ?_
  -- Otherwise `ε ≤ ‖T (x (ψ n))‖` along a subsequence `ψ`.
  by_contra hnot
  obtain ⟨s, hs, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.1 hnot
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs
  have hlarge : ∃ᶠ n in atTop, ε ≤ ‖T (x n)‖ := hfreq.mono fun n hn ↦ by
    by_contra h
    exact hn (hball (by simpa using h))
  obtain ⟨ψ, hψ, hψε⟩ := extraction_of_frequently_atTop hlarge
  -- Norming functionals `g n` of `T (x (ψ n))` pull back to the image of the unit ball under the
  -- weakly compact adjoint, so a further subsequence `φ` converges weakly to some `h₀`.
  choose g hg hgx using fun n ↦ exists_dual_vector'' 𝕜 (T (x (ψ n)))
  obtain ⟨h₀, φ, hφ, hlim⟩ := TauCeti.tendsto_subseq_toWeakSpace_of_isCompact_closure
    (isWeaklyCompact_def.1 hT.precomp) (u := fun n ↦ ContinuousLinearMap.precomp 𝕜 T (g n))
    fun n ↦ mem_image_of_mem _ (mem_closedBall_zero_iff.2 (hg n))
  -- Apply the criterion to the weakly null sequences `x ∘ ψ ∘ φ` and `g ∘ φ ∘ T - h₀`.
  have hx' : Tendsto (fun n ↦ toWeakSpace 𝕜 E (x (ψ (φ n)))) atTop (𝓝 0) :=
    hx.comp (hψ.comp hφ).tendsto_atTop
  have h₁ := h hx' (f := fun n ↦ ContinuousLinearMap.precomp 𝕜 T (g (φ n)) - h₀)
    (by simpa using hlim.sub_const (toWeakSpace 𝕜 (StrongDual 𝕜 E) h₀))
  have h₂ : Tendsto (fun n ↦ h₀ (x (ψ (φ n)))) atTop (𝓝 0) := by
    simpa using (TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto (x := (0 : E)).1
      (by rwa [map_zero])) h₀
  have h₃ : Tendsto (fun n ↦ ‖T (x (ψ (φ n)))‖) atTop (𝓝 0) := by
    simpa [hgx] using (h₁.add h₂).norm
  obtain ⟨n, hn⟩ := (h₃.eventually (gt_mem_nhds hε)).exists
  exact (hψε (φ n)).not_gt hn

end Compact

end ContinuousLinearMap

namespace TauCeti

universe u

section DunfordPettisProperty

variable (𝕜 : Type*) (E : Type u) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A normed space `E` has the *Dunford–Pettis property* if every weakly compact operator from
`E` into a Banach space is Dunford–Pettis. The definition quantifies over Banach spaces in the
universe of `E`; by `TauCeti.HasDunfordPettisProperty.isDunfordPettis` the conclusion then holds
for weakly compact operators into normed spaces in every universe. -/
def HasDunfordPettisProperty : Prop :=
  ∀ (F : Type u) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] (T : E →L[𝕜] F),
    T.IsWeaklyCompact → T.IsDunfordPettis

variable {𝕜 E}

open ZeroAtInftyContinuousMap UniformSpace in
/-- **The Dunford–Pettis property, sequence criterion**, forward direction: if `E` has the
Dunford–Pettis property, `x` is weakly null in `E` and `f` is weakly null in the dual, then
`f n (x n) → 0`. -/
theorem HasDunfordPettisProperty.tendsto_apply (h : HasDunfordPettisProperty 𝕜 E)
    {x : ℕ → E} {f : ℕ → StrongDual 𝕜 E}
    (hx : Tendsto (fun n ↦ toWeakSpace 𝕜 E (x n)) atTop (𝓝 0))
    (hf : Tendsto (fun n ↦ toWeakSpace 𝕜 (StrongDual 𝕜 E) (f n)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ f n (x n)) atTop (𝓝 0) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp [Subsingleton.elim (x _) 0]
  obtain ⟨T₀, hT₀, hT₀f⟩ := exists_isWeaklyCompact_apply_eq hf
  -- Move the values to the Banach space `C₀(ℕ, Completion E)`, in the universe of `E`, along a
  -- unit vector `e`.
  obtain ⟨e₀, he₀⟩ := exists_ne (0 : E)
  set e : E := (‖e₀‖⁻¹ : 𝕜) • e₀
  have he : ‖e‖ = 1 := norm_smul_inv_norm he₀
  let ι : 𝕜 →L[𝕜] Completion E := (1 : 𝕜 →L[𝕜] 𝕜).smulRight (e : Completion E)
  let T : E →L[𝕜] C₀(ℕ, Completion E) := (compLeft ι ⟨‖ι‖, ι.le_opNorm⟩).comp T₀
  have hT : Tendsto (fun n ↦ T (x n)) atTop (𝓝 0) :=
    ContinuousLinearMap.isDunfordPettis_iff_tendsto_zero.1
      (h _ T (hT₀.clm_comp _)) hx
  refine squeeze_zero_norm (fun n ↦ ?_) (by simpa using hT.norm)
  calc ‖f n (x n)‖ = ‖T (x n) n‖ := by simp [T, ι, hT₀f, norm_smul, he]
    _ ≤ ‖T (x n)‖ := norm_coe_le_norm _ _

/-- Under the Dunford–Pettis property, every weakly compact operator from `E` into a normed space,
in any universe, is Dunford–Pettis. -/
theorem HasDunfordPettisProperty.isDunfordPettis (h : HasDunfordPettisProperty 𝕜 E)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {T : E →L[𝕜] F}
    (hT : T.IsWeaklyCompact) : T.IsDunfordPettis :=
  hT.isDunfordPettis_of_tendsto_apply fun _ _ ↦ h.tendsto_apply

/-- **The Dunford–Pettis property, sequence criterion.** A normed space `E` has the
Dunford–Pettis property iff `f n (x n) → 0` whenever `x` is weakly null in `E` and `f` is weakly
null in the dual of `E`. -/
theorem hasDunfordPettisProperty_iff :
    HasDunfordPettisProperty 𝕜 E ↔
      ∀ ⦃x : ℕ → E⦄ ⦃f : ℕ → StrongDual 𝕜 E⦄,
        Tendsto (fun n ↦ toWeakSpace 𝕜 E (x n)) atTop (𝓝 0) →
          Tendsto (fun n ↦ toWeakSpace 𝕜 (StrongDual 𝕜 E) (f n)) atTop (𝓝 0) →
            Tendsto (fun n ↦ f n (x n)) atTop (𝓝 0) :=
  ⟨fun h _ _ ↦ h.tendsto_apply, fun h _ _ _ _ _ hT ↦ hT.isDunfordPettis_of_tendsto_apply h⟩

end DunfordPettisProperty

end TauCeti

namespace lp

variable {𝕜 ι F : Type*} [RCLike 𝕜] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- By Schur's theorem, every bounded operator out of `ℓ¹` is Dunford–Pettis. -/
theorem isDunfordPettis_one (T : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] F) : T.IsDunfordPettis :=
  fun _ _ hx ↦ (T.continuous.tendsto _).comp (tendsto_of_tendsto_toWeakSpace_one hx)

variable (𝕜 ι) in
/-- `ℓ¹` has the Dunford–Pettis property. -/
theorem hasDunfordPettisProperty_one :
    TauCeti.HasDunfordPettisProperty 𝕜 (lp (fun _ : ι ↦ 𝕜) 1) :=
  fun _ _ _ _ T _ ↦ isDunfordPettis_one T

end lp
