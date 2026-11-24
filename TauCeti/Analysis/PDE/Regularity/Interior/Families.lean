/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Interior.Basic
import TauCeti.Analysis.Normed.Operator.Banach
import TauCeti.Topology.Instances.Matrix

/-!
# Interior `H²` regularity for families of weak solutions

Let `a` be uniformly elliptic on `Ω` with `x ↦ a(x)` locally Lipschitz on `Ω`, and let
`b, c ∈ L∞(Ω)`. Interior `H²` regularity
(`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn`) puts the
restriction to `V` of every weak solution `u ∈ H¹(Ω)` of `L u = f` in `W^{2,2}(V)`, for every open
`V` whose closure is compact and contained in `Ω`. This file shows that the passage from `(u, f)`
to that element of `W^{2,2}(V)` is a bounded linear operator, and deduces the statement for
families of weak solutions in `Lq` over any measure space, including the strong measurability of
the resulting family. For a time interval this is `u ∈ Lq(t₀, t₁; H²_loc(Ω))`.

On the closed subspace `TauCeti.PDE.weakEquationGraph` of the pairs `(u, f) ∈ H¹(Ω) × L²(Ω)` with
`L u = f`, the map `(u, f) ↦ U` is the lift of `(u, f) ↦ u|_V` through the injective first-order
part `W^{2,2}(V) → H¹(V)`, which is continuous by the closed graph theorem
(`ContinuousLinearMap.exists_comp_eq_of_range_le_range`).

## Main declarations

* `UniformlyEllipticOn.exists_continuousLinearMap_lowerOrder_eq_restrictL_of_locallyLipschitzOn`:
  the passage from a solution pair `(u, f)` of `TauCeti.PDE.weakEquationGraph` to the element of
  `W^{2,2}(V)` extending `u|_V` is a bounded linear operator, by the closed graph theorem.
* `TauCeti.PDE.UniformlyEllipticOn.exists_memLp_lowerOrder_eq_restrictL_of_locallyLipschitzOn`:
  a family `t ↦ u(t)` of weak solutions of `L u(t) = f(t)` in `Lq` over a measure space, with
  `f ∈ Lq`, has its restrictions to `V` given by a family in `Lq` with values in `W^{2,2}(V)`.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal NNReal InnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}

section Families

variable [DecidableEq ι] {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
  {lam Lam : ℝ}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace
-- The shortcut instances of the energy-form file, so that the normed structure of the subspace
-- of `W^{1,2}(Ω) × L²(Ω)` below and of its operators is found by instance search.
attribute [local instance] instSeminormedAddCommGroupW1p instNormedSpaceW1p

/-- **Interior `H²` regularity as a bounded operator.** Under the hypotheses of
`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn`, there is a
continuous linear map from the pairs `(u, f)` with `L u = f`
(`TauCeti.PDE.weakEquationGraph`) to `W^{2,2}(V)` whose value has first-order part `u|_V`. It is
linear because the first-order part determines an element of `W^{2,2}(V)`, and continuous by the
closed graph theorem; its norm bounds the `W^{2,2}(V)` norm by the `H¹(Ω)` norm of `u` and the
`L²(Ω)` norm of `f`. -/
theorem UniformlyEllipticOn.exists_continuousLinearMap_lowerOrder_eq_restrictL_of_locallyLipschitzOn
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LocallyLipschitzOn (Omega : Set (EuclideanSpace ℝ ι)) fun x => matrixBilinearForm (a x))
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    {V : Opens (EuclideanSpace ℝ ι)} (hV : IsCompact (closure (V : Set (EuclideanSpace ℝ ι))))
    (hVΩ : closure (V : Set (EuclideanSpace ℝ ι)) ⊆ Omega) :
    ∃ T : weakEquationGraph hcoeff →L[ℝ] Wkp mu V 2 2, ∀ p, Wkp.lowerOrder 1 (T p) =
      W1p.restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hVΩ))
        (p : W1p mu Omega 2 × Lp ℝ 2 (mu.restrict Omega)).1 := by
  set hVle : V ≤ Omega := SetLike.coe_subset_coe.mp (subset_closure.trans hVΩ)
  have : CompleteSpace (weakEquationGraph hcoeff) :=
    (isClosed_weakEquationGraph hcoeff).completeSpace_coe
  -- Lift `(u, f) ↦ u|_V` through the first-order part, which is injective.
  let R : weakEquationGraph hcoeff →L[ℝ] W1p mu V 2 := (W1p.restrictL hVle).comp
    ((ContinuousLinearMap.fst ℝ _ _).comp (weakEquationGraph hcoeff).subtypeL)
  have hR : R.range ≤ (Wkp.lowerOrderL 1 : Wkp mu V 2 2 →L[ℝ] W1p mu V 2).range := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨U, hU⟩ := ha.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn hK hb hc
      (fun v => ((mem_weakEquationGraph_iff hcoeff).1 p.property v).trans
        (dirichletForcing_apply_eq_setIntegral _ v)) hV hVΩ
    exact ⟨U, (Wkp.lowerOrderL_apply 1 U).trans hU⟩
  obtain ⟨T, hT⟩ := ContinuousLinearMap.exists_comp_eq_of_range_le_range R _
    (fun U U' h => Wkp.ext_lowerOrder 1 <| by
      rw [← Wkp.lowerOrderL_apply, ← Wkp.lowerOrderL_apply]
      exact h) hR
  exact ⟨T, fun p => (Wkp.lowerOrderL_apply 1 (T p)).symm.trans (DFunLike.congr_fun hT p)⟩

/-- **Interior `H²` regularity for families of weak solutions.** Let `a` be uniformly elliptic on
`Ω`, with `x ↦ a(x)` locally Lipschitz on `Ω` in the operator norm of its bilinear forms, and let
`b, c ∈ L∞(Ω)`. Let `t ↦ u(t) ∈ H¹(Ω)` and `t ↦ f(t) ∈ L²(Ω)` be families in `Lq`, indexed by a
measure space, such that for almost every `t`, `u(t)` is a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu(t)) + ⟨b, ∇u(t)⟩ + c u(t) = f(t)` in `Ω`,

tested against `H¹₀(Ω)`, with no boundary condition on `u(t)`. Then on every open `V` whose
closure is compact and contained in `Ω` there is a family `t ↦ U(t) ∈ W^{2,2}(V)` in `Lq`, in
particular almost everywhere strongly measurable, whose first-order part is the restriction of
`u(t)` to `V` for almost every `t`. For a time interval this is the statement
`u ∈ Lq(t₀, t₁; H²_loc(Ω))`. -/
theorem UniformlyEllipticOn.exists_memLp_lowerOrder_eq_restrictL_of_locallyLipschitzOn
    {α : Type*} [MeasurableSpace α] {ν : Measure α} {q : ℝ≥0∞}
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LocallyLipschitzOn (Omega : Set (EuclideanSpace ℝ ι)) fun x => matrixBilinearForm (a x))
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    {u : α → W1p mu Omega 2} {f : α → Lp ℝ 2 (mu.restrict Omega)}
    (hu : MemLp u q ν) (hf : MemLp f q ν)
    (heq : ∀ᵐ t ∂ν, ∀ v : W1p0 mu Omega 2, energyFormH1 a b c (u t) (v : W1p mu Omega 2) =
      ∫ x in Omega, f t x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {V : Opens (EuclideanSpace ℝ ι)} (hV : IsCompact (closure (V : Set (EuclideanSpace ℝ ι))))
    (hVΩ : closure (V : Set (EuclideanSpace ℝ ι)) ⊆ Omega) :
    ∃ U : α → Wkp mu V 2 2, MemLp U q ν ∧ ∀ᵐ t ∂ν, Wkp.lowerOrder 1 (U t) =
      W1p.restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hVΩ)) (u t) := by
  have hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega) :=
    memLp_energyIntegrand_of_memLp_top ha.upper_nonneg
      ((continuousOn_of_continuousOn_matrixBilinearForm hK.continuousOn).aestronglyMeasurable
        Omega.isOpen.measurableSet)
      (fun _x hx eta xi => ha.upper_bound hx eta xi) hb hc
  obtain ⟨T, hT⟩ :=
    ha.exists_continuousLinearMap_lowerOrder_eq_restrictL_of_locallyLipschitzOn hK hb hc hcoeff
      hV hVΩ
  -- The pairs `(u(t), f(t))`, replaced by `0` at the times where they are not solution pairs.
  classical
  let S := weakEquationGraph hcoeff
  let P : α → W1p mu Omega 2 × Lp ℝ 2 (mu.restrict Omega) := fun t => (u t, f t)
  let Q : α → S := fun t => if h : P t ∈ S then ⟨P t, h⟩ else 0
  have hPQ : ∀ᵐ t ∂ν, ((Q t : S) : W1p mu Omega 2 × Lp ℝ 2 (mu.restrict Omega)) = P t := by
    filter_upwards [heq] with t ht
    have h : P t ∈ S := (mem_weakEquationGraph_iff hcoeff (p := P t)).2 fun v =>
      (ht v).trans (dirichletForcing_apply_eq_setIntegral _ v).symm
    simp only [Q, h, ↓reduceDIte]
  have hQ : AEStronglyMeasurable Q ν :=
    Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff.1
      ((hu.aestronglyMeasurable.prodMk hf.aestronglyMeasurable).congr (hPQ.mono fun _ h => h.symm))
  refine ⟨fun t => T (Q t), ?_, ?_⟩
  · refine MemLp.of_le ((hu.norm.add hf.norm).const_mul ‖T‖)
      (T.continuous.comp_aestronglyMeasurable hQ) ?_
    filter_upwards [hPQ] with t ht
    calc ‖T (Q t)‖ ≤ ‖T‖ * ‖Q t‖ := T.le_opNorm _
      _ = ‖T‖ * ‖P t‖ := by rw [← ht, Submodule.norm_coe]
      _ ≤ ‖T‖ * (‖u t‖ + ‖f t‖) := by
        gcongr
        simp only [P, Prod.norm_mk]
        exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
      _ ≤ ‖‖T‖ * (‖u t‖ + ‖f t‖)‖ := Real.le_norm_self _
  · filter_upwards [hPQ] with t ht
    rw [hT, ht]

end Families

end PDE

end TauCeti
