/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.DirichletProblem
public import TauCeti.Analysis.PDE.Regularity.Interior
import Mathlib.Analysis.Normed.Operator.Banach
import TauCeti.Topology.Instances.Matrix

/-!
# Interior `H²` regularity in space for parabolic weak solutions

Let `Ω ⊆ ℝⁿ` be open and let `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` have a uniformly elliptic
principal coefficient `a` that is locally Lipschitz on `Ω`, and bounded measurable `b` and `c`.
This file proves that a weak solution `u` of the parabolic equation `∂ₜu + L u = F` with
`F ∈ L²(t₀, t₁; L²(Ω))` and `∂ₜu ∈ L²(t₀, t₁; L²(Ω))` lies in `L²(t₀, t₁; H²_loc(Ω))`: on every
open `V` whose closure is compact and contained in `Ω`, the restrictions `u(t)|_V` are the
first-order parts of a square-integrable family of elements of `W^{2,2}(V)`. With the time
regularity of `TauCeti.PDE.exists_memLp_hasWeakLineDerivOn_valueL_energyFormH1_of_isSymm`, this is
the interior form of the improved regularity of Evans, §7.1.3, Theorem 5: for time-independent
coefficients with symmetric principal part, an initial value in `H¹₀(Ω)` gives a solution in
`L^∞(t₀, t₁; H¹₀(Ω)) ∩ L²(t₀, t₁; H²_loc(Ω))` with `∂ₜu ∈ L²(t₀, t₁; L²(Ω))`.

At almost every time `t`, the function `u(t) ∈ H¹(Ω)` is a weak solution of the elliptic equation
`L u(t) = F(t) - ∂ₜu(t)`, whose right-hand side lies in `L²(Ω)`, so interior elliptic regularity
(`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn`) puts
`u(t)` in `H²(V)`. What remains is that the resulting family is square integrable in time,
including its strong measurability. Both come from the observation that the passage from a weak
solution to its `H²(V)` extension is a bounded linear operator: on the closed subspace of the pairs
`(u, f) ∈ H¹(Ω) × L²(Ω)` with `L u = f`, the map `(u, f) ↦ U`, where `U ∈ W^{2,2}(V)` is the unique
element with first-order part `u|_V`, is linear, and its graph is closed because the first-order
part is continuous and injective. The closed graph theorem makes it continuous. Applying it to the
pairs `(u(t), F(t) - ∂ₜu(t))` gives the family, and the theorem
`TauCeti.PDE.UniformlyEllipticOn.exists_memLp_lowerOrder_eq_restrictL_of_locallyLipschitzOn` is
stated for any such family of weak solutions, indexed by an arbitrary measure space.

The Lipschitz hypothesis on `a` cannot be dropped: a time-independent weak solution of the
elliptic equation is a weak solution of the parabolic one with `∂ₜu = 0`, and for the coefficient
with a jump of `TauCeti.Analysis.PDE.Regularity.JumpCoefficient` such solutions need not lie in
`H²` near the jump.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.exists_memLp_lowerOrder_eq_restrictL_of_locallyLipschitzOn`:
  a family `t ↦ u(t)` of weak solutions of `L u(t) = f(t)` in `Lq` over a measure space, with
  `f ∈ Lq`, has its restrictions to `V` given by a family in `Lq` with values in `W^{2,2}(V)`.
* `TauCeti.PDE.exists_memLp_lowerOrder_eq_restrictL_of_isSymm`: a weak solution of the parabolic
  Dirichlet problem with time-independent, locally Lipschitz, symmetric principal coefficients,
  forcing in `L²(t₀, t₁; L²(Ω))` and initial value in `H¹₀(Ω)` lies in `L²(t₀, t₁; H²(V))`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §7.1.3, Theorem 5, which proves the
  global `H²` regularity for smooth coefficients and a smooth boundary.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory Set TopologicalSpace Filter
open scoped InnerProductSpace Topology ENNReal

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace
-- The shortcut instances of the energy-form file, so that the normed structure of the subspaces
-- of `W^{1,2}(Ω) × L²(Ω)` below and of their operators is found by instance search.
attribute [local instance] instSeminormedAddCommGroupW1p instNormedSpaceW1p

/-! ### The solution operator into `W^{2,2}(V)` -/

/-- The pairs `(u, f) ∈ H¹(Ω) × L²(Ω)` for which `u` is a weak solution of `L u = f`, tested
against `H¹₀(Ω)`, with no boundary condition on `u`. Its intersection with the boundary condition
`u ∈ H¹₀(Ω)` is `TauCeti.PDE.dirichletGraph`. -/
private def interiorGraph
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega)) :
    Submodule ℝ (W1p mu Omega 2 × Lp ℝ 2 (mu.restrict Omega)) where
  carrier := ⋂ v : W1p0 mu Omega 2,
    {p | energyFormH1L hcoeff p.1 v = dirichletForcing p.2 v}
  add_mem' {p q} hp hq := mem_iInter.2 fun v => by
    simp only [mem_iInter, mem_ofPred_eq] at hp hq
    simp only [mem_ofPred_eq, Prod.fst_add, Prod.snd_add, map_add, add_apply, hp v, hq v,
      dirichletForcing_apply, inner_add_left]
  zero_mem' := mem_iInter.2 fun v => by simp
  smul_mem' r p hp := mem_iInter.2 fun v => by
    simp only [mem_iInter, mem_ofPred_eq] at hp
    simp only [mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, map_smul, smul_apply, hp v,
      dirichletForcing_apply, real_inner_smul_left, smul_eq_mul]

private theorem mem_interiorGraph_iff
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    {p : W1p mu Omega 2 × Lp ℝ 2 (mu.restrict Omega)} :
    p ∈ interiorGraph hcoeff ↔ ∀ v : W1p0 mu Omega 2,
      energyFormH1 a b c p.1 (v : W1p mu Omega 2) =
        ∫ x in Omega, p.2 x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  simp only [← dirichletForcing_apply_eq_setIntegral, ← energyFormH1L_apply hcoeff]
  exact mem_iInter

private theorem isClosed_interiorGraph
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega)) :
    IsClosed (interiorGraph hcoeff : Set (W1p mu Omega 2 × Lp ℝ 2 (mu.restrict Omega))) := by
  refine isClosed_iInter fun v => isClosed_eq ?_ ?_
  · exact ((energyFormH1L hcoeff).continuous.comp continuous_fst).clm_apply continuous_const
  · simp only [dirichletForcing_apply]
    exact continuous_snd.inner continuous_const

variable [DecidableEq ι] {lam Lam : ℝ}

/-- Interior `H²` regularity as a bounded operator: under the hypotheses of
`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn`, there is a
continuous linear map from the pairs `(u, f)` with `L u = f` to `W^{2,2}(V)` whose value has
first-order part `u|_V`. It is linear because the first-order part determines an element of
`W^{2,2}(V)`, and continuous by the closed graph theorem. -/
private theorem exists_continuousLinearMap_lowerOrder_eq_restrictL
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LocallyLipschitzOn (Omega : Set (EuclideanSpace ℝ ι)) fun x => matrixBilinearForm (a x))
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    {V : Opens (EuclideanSpace ℝ ι)} (hV : IsCompact (closure (V : Set (EuclideanSpace ℝ ι))))
    (hVΩ : closure (V : Set (EuclideanSpace ℝ ι)) ⊆ Omega) :
    ∃ T : interiorGraph hcoeff →L[ℝ] Wkp mu V 2 2, ∀ p, Wkp.lowerOrder 1 (T p) =
      W1p.restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hVΩ))
        (p : W1p mu Omega 2 × Lp ℝ 2 (mu.restrict Omega)).1 := by
  set hVle : V ≤ Omega := SetLike.coe_subset_coe.mp (subset_closure.trans hVΩ)
  have hex (p : interiorGraph hcoeff) : ∃ U : Wkp mu V 2 2, Wkp.lowerOrder 1 U =
      W1p.restrictL hVle (p : W1p mu Omega 2 × Lp ℝ 2 (mu.restrict Omega)).1 :=
    ha.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn hK hb hc
      ((mem_interiorGraph_iff hcoeff).1 p.property) hV hVΩ
  choose T hT using hex
  -- The first-order part, a continuous linear map into `W^{1,2}(V)`, which is injective.
  let low : Wkp mu V 2 2 →L[ℝ] W1p mu V 2 := Wkp.lowerOrderL 1
  have hlow (U : Wkp mu V 2 2) : low U = Wkp.lowerOrder 1 U := Wkp.lowerOrderL_apply 1 U
  have hlowT (p : interiorGraph hcoeff) : low (T p) =
      W1p.restrictL hVle (p : W1p mu Omega 2 × Lp ℝ 2 (mu.restrict Omega)).1 :=
    (hlow _).trans (hT p)
  have hinj (U U' : Wkp mu V 2 2) (h : low U = low U') : U = U' :=
    Wkp.ext_lowerOrder 1 (by rw [← hlow, ← hlow, h])
  let T₀ : interiorGraph hcoeff →ₗ[ℝ] Wkp mu V 2 2 :=
    { toFun := T
      map_add' := fun p p' => hinj _ _ <| by
        rw [map_add, hlowT, hlowT, hlowT, Submodule.coe_add, Prod.fst_add, map_add]
      map_smul' := fun r p => hinj _ _ <| by
        rw [map_smul, hlowT, hlowT, RingHom.id_apply, Submodule.coe_smul, Prod.smul_fst,
          map_smul] }
  have : CompleteSpace (interiorGraph hcoeff) :=
    (isClosed_interiorGraph hcoeff).completeSpace_coe
  -- The graph is closed: the first-order part of a limit is the limit of the first-order parts.
  refine ⟨ContinuousLinearMap.ofSeqClosedGraph (g := T₀) fun p p₀ U hp hU => hinj _ _ ?_, hT⟩
  refine tendsto_nhds_unique ((low.continuous.tendsto U).comp hU) ?_
  have hlim : Tendsto (fun n => W1p.restrictL hVle
      ((p n : interiorGraph hcoeff) : W1p mu Omega 2 × Lp ℝ 2 (mu.restrict Omega)).1) atTop
      (𝓝 (W1p.restrictL hVle (p₀ : W1p mu Omega 2 × Lp ℝ 2 (mu.restrict Omega)).1)) :=
    ((W1p.restrictL hVle).continuous.comp (continuous_fst.comp continuous_subtypeVal)
      |>.tendsto p₀).comp hp
  exact (hlowT p₀).symm ▸ hlim.congr fun n => (hlowT (p n)).symm

/-! ### Families of weak solutions -/

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
  obtain ⟨T, hT⟩ := exists_continuousLinearMap_lowerOrder_eq_restrictL ha hK hb hc hcoeff hV hVΩ
  -- The pairs `(u(t), f(t))`, replaced by `0` at the times where they are not solution pairs.
  classical
  let S := interiorGraph hcoeff
  let P : α → W1p mu Omega 2 × Lp ℝ 2 (mu.restrict Omega) := fun t => (u t, f t)
  let Q : α → S := fun t => if h : P t ∈ S then ⟨P t, h⟩ else 0
  have hPQ : ∀ᵐ t ∂ν, ((Q t : S) : W1p mu Omega 2 × Lp ℝ 2 (mu.restrict Omega)) = P t := by
    filter_upwards [heq] with t ht
    have h : P t ∈ S := (mem_interiorGraph_iff hcoeff (p := P t)).2 ht
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
        exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
      _ ≤ ‖‖T‖ * (‖u t‖ + ‖f t‖)‖ := Real.le_norm_self _
  · filter_upwards [hPQ] with t ht
    rw [hT, ht]

/-! ### The parabolic Dirichlet problem -/

/-- **Interior `H²` regularity in space for the parabolic Dirichlet problem** (Evans, §7.1.3,
Theorem 5, in its interior form). Let the coefficients of `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` be
independent of time, with `a` uniformly elliptic on `Ω`, symmetric almost everywhere and locally
Lipschitz on `Ω` in the operator norm of its bilinear forms, and `b`, `c` bounded and measurable.
Let `u` be a weak solution of `∂ₜu + L u = F` in `(t₀, t₁) × Ω`, `u = 0` on `(t₀, t₁) × ∂Ω`, with
forcing `F ∈ L²(t₀, t₁; L²(Ω))`, whose continuous `L²(Ω)`-valued representative starts at
`u₀ ∈ H¹₀(Ω)`. Then `u ∈ L²(t₀, t₁; H²_loc(Ω))`: on every open `V` whose closure is compact and
contained in `Ω` there is a family `t ↦ U(t) ∈ W^{2,2}(V)` in `L²(t₀, t₁)` whose first-order part
is the restriction of `u(t)` to `V` for almost every `t`. No regularity of `∂Ω`, no boundedness
of `Ω` and no sign condition on `c` is needed. -/
theorem exists_memLp_lowerOrder_eq_restrictL_of_isSymm {t₀ t₁ beta gamma : ℝ}
    (hell : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LocallyLipschitzOn (Omega : Set (EuclideanSpace ℝ ι)) fun x => matrixBilinearForm (a x))
    (hsymm : ∀ᵐ x ∂mu.restrict Omega, (a x).IsSymm)
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    {F : ℝ → Lp ℝ 2 (mu.restrict Omega)} (hF : MemLp F 2 (volume.restrict (Ioo t₀ t₁)))
    {u₀ : W1p0 mu Omega 2} {u : ℝ → W1p0 mu Omega 2} {u' : ℝ → StrongDual ℝ (W1p0 mu Omega 2)}
    {w : ℝ → Lp ℝ 2 (mu.restrict Omega)}
    (h : HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
        (W1p0.valueL (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo t₀ t₁)))
    (hu' : MemLp u' 2 (volume.restrict (Ioo t₀ t₁)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2,
      u' t v + energyFormH1 a b c (u t : W1p mu Omega 2) (v : W1p mu Omega 2) =
        ⟪F t, W1p0.valueL v⟫_ℝ)
    (hw : ContinuousOn w (Icc t₀ t₁))
    (hae : (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo t₀ t₁)] w)
    (h₀ : w t₀ = W1p0.valueL u₀)
    {V : Opens (EuclideanSpace ℝ ι)} (hV : IsCompact (closure (V : Set (EuclideanSpace ℝ ι))))
    (hVΩ : closure (V : Set (EuclideanSpace ℝ ι)) ⊆ Omega) :
    ∃ U : ℝ → Wkp mu V 2 2, MemLp U 2 (volume.restrict (Ioo t₀ t₁)) ∧
      ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), Wkp.lowerOrder 1 (U t) =
        W1p.restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hVΩ))
          (u t : W1p mu Omega 2) := by
  have ha : AEStronglyMeasurable a (mu.restrict Omega) :=
    (continuousOn_of_continuousOn_matrixBilinearForm hK.continuousOn).aestronglyMeasurable
      Omega.isOpen.measurableSet
  -- The time derivative `d ∈ L²(t₀, t₁; L²(Ω))`; then `L u(t) = F(t) - d(t)` at almost every time.
  obtain ⟨d, hd, -, hu'd, -⟩ := exists_memLp_hasWeakLineDerivOn_valueL_energyFormH1_of_isSymm ha hb
    hc hell hsymm hb_bound hc_bound hF h hu hu' heq hw hae h₀
  have hbm : MemLp b ⊤ (mu.restrict Omega) := memLp_top_of_bound hb beta
    (ae_restrict_of_forall_mem Omega.isOpen.measurableSet hb_bound)
  have hcm : MemLp c ⊤ (mu.restrict Omega) := memLp_top_of_bound hc gamma
    (ae_restrict_of_forall_mem Omega.isOpen.measurableSet hc_bound)
  refine hell.exists_memLp_lowerOrder_eq_restrictL_of_locallyLipschitzOn hK hbm hcm
    (((w1p0Submodule mu Omega 2).toSubmodule.subtypeL).comp_memLp' hu) (hF.sub hd) ?_ hV hVΩ
  filter_upwards [heq, hu'd] with t ht ht' v
  rw [Function.comp_apply, Submodule.subtypeL_apply, Pi.sub_apply,
    ← dirichletForcing_apply_eq_setIntegral, dirichletForcing_apply,
    inner_sub_left, ← W1p0.valueL_apply, ← ht v, ht' v]
  ring

end PDE

end TauCeti
