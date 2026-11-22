/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.DirichletProblem
public import TauCeti.Analysis.PDE.Regularity.Interior.Basic
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
pairs `(u(t), F(t) - ∂ₜu(t))` gives the family. The operator and the statement for any family of
weak solutions indexed by a measure space,
`TauCeti.PDE.UniformlyEllipticOn.exists_memLp_lowerOrder_eq_restrictL_of_locallyLipschitzOn`, are
elliptic results proved in `TauCeti.Analysis.PDE.Regularity.Interior`.

The Lipschitz hypothesis on `a` cannot be dropped: a time-independent weak solution of the
elliptic equation is a weak solution of the parabolic one with `∂ₜu = 0`, and for the coefficient
with a jump of `TauCeti.Analysis.PDE.Regularity.JumpCoefficient` such solutions need not lie in
`H²` near the jump.

## Main declarations

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
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ} [DecidableEq ι]
  {lam Lam : ℝ}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

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
  rw [← dirichletForcing_apply_eq_setIntegral]
  simp only [Function.comp_apply, Submodule.subtypeL_apply, Pi.sub_apply, dirichletForcing_apply,
    inner_sub_left, W1p0.valueL_apply] at ht ht' ⊢
  linarith [ht v, ht' v]

end PDE

end TauCeti
