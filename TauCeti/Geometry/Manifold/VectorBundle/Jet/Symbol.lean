/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Jet.Basic
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.IteratedFDeriv.LeibnizJet
import TauCeti.Analysis.Calculus.IteratedFDeriv.Mul
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# The top-order jets of a vector bundle

Let `V` be a vector bundle over a manifold `M` and `JᵣV` its bundle of `r`-jets. Forgetting the
derivatives of order `r` is the truncation `JᵣV → Jᵣ₋₁V`. Its kernel at `x` consists of the jets
of sections all of whose derivatives of order below `r` vanish at `x`, and such a jet is
determined by the derivative of order `r`, a symmetric multilinear map on the tangent space with
values in the fibre. This is the exact sequence

`0 → Sym^r T*ₓM ⊗ Vₓ → (JᵣV)ₓ → (Jᵣ₋₁V)ₓ → 0`

through which the top-order coefficient of a differential operator of order `r` becomes its
principal symbol.

This file constructs the map `TauCeti.JetBundle.ofTop I F V r x` from the continuous
`r`-multilinear maps `TₓM × ⋯ × TₓM → Vₓ` to the fibre of `JᵣV` at `x`: in the chart and the
trivialization at `x`, `ofTop A` is the jet whose components of order below `r` vanish and whose
component of order `r` is the symmetrization of `A`. Its range is exactly the kernel of the
truncation (`TauCeti.JetBundle.range_ofTop`), the truncation is onto
(`TauCeti.JetBundle.truncate_surjective`), and `ofTop A` vanishes exactly when the symmetrization
of `A`, read in the trivialization at `x`, does (`TauCeti.JetBundle.ofTop_eq_zero_iff`). These
are the three parts of the exact sequence above, with `Sym^r T*ₓM ⊗ Vₓ` represented by the
multilinear maps modulo those whose symmetrization vanishes.

On a real manifold without boundary the map has an intrinsic description by products of
functions vanishing at `x`: if `f₁, …, fᵣ` are smooth functions with `fᵢ(x) = 0` and `s` is a
smooth section, then

`jʳ(f₁ ⋯ fᵣ s)(x) = ofTop (r! • (dₓf₁ ⊗ ⋯ ⊗ dₓfᵣ ⊗ s(x)))`

(`TauCeti.JetBundle.jet_prod_smul`), where `dₓf₁ ⊗ ⋯ ⊗ dₓfᵣ ⊗ s(x)` is the multilinear map
`(v₁, …, vᵣ) ↦ dₓf₁(v₁) ⋯ dₓfᵣ(vᵣ) s(x)`. The proof reads the product in the chart at `x` and
uses the Leibniz rule: the derivative of order `r` at `x` of a product of `r` functions vanishing
at `x` with a function `u` is `r! • (∏ᵢ Dfᵢ h) • u` on the diagonal `(h, …, h)`
(`TauCeti.iteratedFDeriv_prod_smul_apply_const`), and a symmetric jet is determined by its values
on the diagonals.

## Main definitions and results

* `TauCeti.JetBundle.ofTop`: the inclusion of the top-order multilinear maps into the fibre of the
  jet bundle, with its components `TauCeti.JetBundle.toJets_ofTop_last` and
  `TauCeti.JetBundle.toJets_ofTop_of_ne_last`.
* `TauCeti.JetBundle.ofTop_eq_zero_iff`, `TauCeti.JetBundle.truncate_ofTop`,
  `TauCeti.JetBundle.range_ofTop`, `TauCeti.JetBundle.truncate_surjective`: the exact sequence
  above.
* `TauCeti.JetBundle.jet_prod_smul`: the jet of `f₁ ⋯ fᵣ s` for functions `fᵢ` vanishing at `x`.

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  §§12.2–12.5 and 12.16–12.17 (the exact sequence of jet bundles of a vector bundle).
-/

public section

noncomputable section

open Bundle Filter Set
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace JetBundle

section General

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V] {r r' : ℕ}

variable (I F V r) in
/-- The **inclusion of the top-order jets**: a continuous multilinear map
`A : TₓM × ⋯ × TₓM → Vₓ` of `r` variables is sent to the `r`-jet at `x` whose components of order
below `r` vanish and whose component of order `r` is the symmetrization of `A`, both read in the
chart and the trivialization at `x`. Its range is the kernel of the truncation to order `r - 1`
(`TauCeti.JetBundle.range_ofTop`), and it is the jet of `f₁ ⋯ fᵣ s` for functions `fᵢ`
vanishing at `x` (`TauCeti.JetBundle.jet_prod_smul`). -/
def ofTop [IsManifold I r M] [ContMDiffVectorBundle r F V I] (x : M) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r ↦ TangentSpace I x) (V x) →ₗ[𝕜]
      JetBundle I F V r x :=
  (SymmetricJet.ofTop 𝕜 E F r).toLinearMap ∘ₗ
    (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜 _ _ _
      ((trivializationAt F V x).continuousLinearMapAt 𝕜 x)).toLinearMap

section Order

variable [IsManifold I r M] [ContMDiffVectorBundle r F V I]

theorem ofTop_apply (x : M)
    (A : ContinuousMultilinearMap 𝕜 (fun _ : Fin r ↦ TangentSpace I x) (V x)) :
    ofTop I F V r x A = SymmetricJet.ofTop 𝕜 E F r
      (((trivializationAt F V x).continuousLinearMapAt 𝕜 x).compContinuousMultilinearMap A) :=
  (rfl)

/-- The top component of `ofTop A`, read in the trivialization at `x`, is the symmetrization of
`A`. -/
@[simp]
theorem toJets_ofTop_last (x : M)
    (A : ContinuousMultilinearMap 𝕜 (fun _ : Fin r ↦ TangentSpace I x) (V x)) :
    SymmetricJet.toJets 𝕜 E F r (ofTop I F V r x A) (Fin.last r) =
      ContinuousMultilinearMap.symmetrize 𝕜 (Fin r) E F
        (((trivializationAt F V x).continuousLinearMapAt 𝕜 x).compContinuousMultilinearMap A) :=
  SymmetricJet.toJets_ofTop_last _

/-- The components of `ofTop A` below the top order vanish. -/
theorem toJets_ofTop_of_ne_last (x : M)
    (A : ContinuousMultilinearMap 𝕜 (fun _ : Fin r ↦ TangentSpace I x) (V x))
    {i : Fin (r + 1)} (hi : i ≠ Fin.last r) :
    SymmetricJet.toJets 𝕜 E F r (ofTop I F V r x A) i = 0 :=
  SymmetricJet.toJets_ofTop_of_ne_last _ hi

/-- `ofTop A` vanishes exactly when the symmetrization of `A`, read in the trivialization at `x`,
does. -/
theorem ofTop_eq_zero_iff (x : M)
    (A : ContinuousMultilinearMap 𝕜 (fun _ : Fin r ↦ TangentSpace I x) (V x)) :
    ofTop I F V r x A = 0 ↔ ContinuousMultilinearMap.symmetrize 𝕜 (Fin r) E F
      (((trivializationAt F V x).continuousLinearMapAt 𝕜 x).compContinuousMultilinearMap A) = 0 :=
  SymmetricJet.ofTop_eq_zero_iff _

end Order

/-- Jets with only a top component truncate to zero. -/
@[simp]
theorem truncate_ofTop [IsManifold I r M] [ContMDiffVectorBundle r F V I]
    [IsManifold I r' M] [ContMDiffVectorBundle r' F V I] (hr : r' < r) (x : M)
    (A : ContinuousMultilinearMap 𝕜 (fun _ : Fin r ↦ TangentSpace I x) (V x)) :
    truncate (I := I) (F := F) (V := V) hr.le x (ofTop I F V r x A) = 0 := by
  rw [truncate_apply, ofTop_apply]
  exact SymmetricJet.truncate_ofTop hr _

/-- **The kernel of the truncation.** An `(r + 1)`-jet at `x` truncates to zero in order `r` exactly
when it is `ofTop A` for a continuous multilinear map `A` of `r + 1` tangent vectors with values in
the fibre `Vₓ`. -/
theorem range_ofTop [IsManifold I (r + 1 : ℕ) M] [ContMDiffVectorBundle (r + 1 : ℕ) F V I]
    [IsManifold I r M] [ContMDiffVectorBundle r F V I] (x : M) :
    LinearMap.range (ofTop I F V (r + 1) x) =
      (truncate (I := I) (F := F) (V := V) (Nat.le_add_right r 1) x).ker := by
  ext j
  refine ⟨?_, fun hj ↦ ?_⟩
  · rintro ⟨A, rfl⟩
    exact truncate_ofTop (Nat.lt_succ_self r) x A
  -- In the trivialization at `x`, the jet is `SymmetricJet.ofTop` of a multilinear map `B` with
  -- values in the model fibre; read `B` back in the fibre through the inverse trivialization.
  let j' : SymmetricJet 𝕜 E F (r + 1) := j
  have hj' : j' ∈ (SymmetricJet.truncate 𝕜 E F (Nat.le_add_right r 1)).ker :=
    LinearMap.mem_ker.2 ((truncate_apply _ x j).symm.trans (LinearMap.mem_ker.1 hj))
  rw [SymmetricJet.ker_truncate] at hj'
  obtain ⟨B, hB⟩ := hj'
  refine ⟨((trivializationAt F V x).symmL 𝕜 x).compContinuousMultilinearMap B,
    (congrArg (SymmetricJet.ofTop 𝕜 E F (r + 1)) ?_).trans hB⟩
  ext v
  exact (trivializationAt F V x).continuousLinearMapAt_symmL
    (mem_baseSet_trivializationAt F V x) _

end General

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I] {r : ℕ}

/-- **The jet of a product of functions vanishing at a point.** If `f₁, …, fᵣ` are smooth functions
vanishing at `x` and `t` is a smooth section, the `r`-jet of `f₁ ⋯ fᵣ t` at `x` only has a top
component: it is `ofTop (r! • (dₓf₁ ⊗ ⋯ ⊗ dₓfᵣ ⊗ t(x)))`, where the multilinear map
`dₓf₁ ⊗ ⋯ ⊗ dₓfᵣ ⊗ t(x)` sends `(v₁, …, vᵣ)` to `dₓf₁(v₁) ⋯ dₓfᵣ(vᵣ) t(x)`. -/
theorem jet_prod_smul {x : M} (f : Fin r → C^∞⟮I, M; ℝ⟯) (hf : ∀ i, f i x = 0)
    (t : Cₛ^∞⟮I; F, V⟯) :
    jet I F r (fun y ↦ (∏ i, f i y) • t y) x = ofTop I F V r x (r.factorial •
      (ContinuousMultilinearMap.mkPiRing ℝ (Fin r) (t x)).compContinuousLinearMap
        fun i ↦ mvfderiv I (f i) x) := by
  have hx := FirstJetBundle.mem_baseSet_self (H := H) F V x
  have hxI : I.IsInteriorPoint x := BoundarylessManifold.isInteriorPoint
  -- Global `C^r` representatives of the chart expressions of the `fᵢ` and of `t` near `x`.
  choose g hg _ hgf using fun i ↦
    ((f i).contMDiff.contMDiffAt.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint hxI).of_le
      (by exact_mod_cast le_top : ((r : ℕ∞) : WithTop ℕ∞) ≤ ∞)
      |>.exists_contDiff_eventuallyEq_of_finiteDimensional r
  obtain ⟨w, hw, -, hwt⟩ := ((FirstJetBundle.contDiffAt_localRep I F (t.contMDiff x) hx).of_le
      (by exact_mod_cast le_top : ((r : ℕ∞) : WithTop ℕ∞) ≤ ∞)
      |>.exists_contDiff_eventuallyEq_of_finiteDimensional r)
  -- Near the image of `x`, the local representative of the product is `(∏ᵢ gᵢ) • w`.
  have hloc : FirstJetBundle.localRep I F (fun y ↦ (∏ i, f i y) • t y) x =ᶠ[𝓝 (extChartAt I x x)]
      fun z ↦ (∏ i, g i z) • w z := by
    filter_upwards [FirstJetBundle.localRep_smul_eventuallyEq I F (fun y ↦ ∏ i, f i y) t hx,
      eventually_all.2 hgf, hwt] with z hz hgz hwz
    rw [hz, hwz]
    congr 1
    exact Finset.prod_congr rfl fun i _ ↦ (hgz i).symm
  have hg0 : ∀ i, g i (extChartAt I x x) = 0 := fun i ↦ by
    rw [(hgf i).eq_of_nhds, Function.comp_apply, extChartAt_to_inv, hf i]
  have hdg : ∀ i, fderiv ℝ (g i) (extChartAt I x x) = mvfderiv I (f i) x := fun i ↦ by
    rw [(hgf i).fderiv_eq, mvfderiv_eq_fderiv_comp_extChartAt_symm]
  have hw0 : w (extChartAt I x x) = (trivializationAt F V x).continuousLinearMapAt ℝ x (t x) := by
    rw [hwt.eq_of_nhds, FirstJetBundle.localRep_extChartAt I F t (mem_chart_source H x),
      Trivialization.continuousLinearMapAt_apply,
      (trivializationAt F V x).coe_linearMapAt_of_mem (mem_baseSet_trivializationAt F V x)]
  -- Both jets are symmetrizations, so it suffices to compare their tuples on the diagonals.
  rw [jet_eq_symmetrizeJets_of_eventuallyEq hloc, ofTop_apply, SymmetricJet.ofTop_apply]
  refine symmetrizeJets_eq_of_forall_apply_const_eq fun k h ↦ ?_
  by_cases hk : k = Fin.last r
  · subst hk
    rw [Pi.single_eq_same]
    refine (iteratedFDeriv_prod_smul_apply_const hg hw hg0 h).trans ?_
    -- Both sides are the trivialization at `x` applied to `r! • (∏ᵢ dₓfᵢ h) • t x`.
    have htop : ∀ v : TangentSpace I x,
        ((trivializationAt F V x).continuousLinearMapAt ℝ x).compContinuousMultilinearMap
          (r.factorial • (ContinuousMultilinearMap.mkPiRing ℝ (Fin r) (t x)).compContinuousLinearMap
            fun i ↦ mvfderiv I (f i) x) (fun _ ↦ v) =
        r.factorial • (∏ i, mvfderiv I (f i) x v) •
          (trivializationAt F V x).continuousLinearMapAt ℝ x (t x) := fun v ↦ by
      simp
    simp only [hdg, hw0]
    -- The goal evaluates on `Fin (Fin.last r).val → E`, which is `Fin r → E` by definition; the
    -- dependent type of `Pi.single (Fin.last r) _ k` blocks rewriting `Fin.val_last` there.
    exact (htop h).symm
  · rw [Pi.single_eq_of_ne hk, iteratedFDeriv_prod_smul_eq_zero_of_lt
      (fun i ↦ (hg i).contDiffAt) hw.contDiffAt hg0 (Fin.val_lt_last hk)]

end Real

end JetBundle

end TauCeti
