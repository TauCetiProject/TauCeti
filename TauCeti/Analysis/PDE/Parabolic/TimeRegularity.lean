/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.EnergyEstimate.Basic
import TauCeti.Analysis.InnerProductSpace.LaxMilgram
import TauCeti.Analysis.InnerProductSpace.Positive.MetricChange.Basic
import TauCeti.Analysis.PDE.Parabolic.Existence
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Time regularity of weak solutions of parabolic equations

Let `V ↪ H ↪ V*` be a Gelfand triple of real Hilbert spaces, given by an injective
`ι : V →L[ℝ] H` (`ContinuousLinearMap.gelfandDual`), and let `A : V →L[ℝ] V*` be a bounded,
**time-independent, symmetric and coercive** operator: `A v w = A w v` and `α ‖v‖² ≤ A v v` with
`α > 0`. A weak solution of

`u' + A u = f`, `u(a) = u₀`,

with `f ∈ L²(a, b; V*)` and `u₀ ∈ H` only has `u' ∈ L²(a, b; V*)`. This file proves that the
solution gains regularity when the data do: if `f = ι* g` with `g ∈ L²(a, b; H)` and `u₀ = ι v₀`
with `v₀ ∈ V`, then

* `ι ∘ u` has a weak time derivative `d ∈ L²(a, b; H)`, with `u' = ι* d`;
* `u` has a representative `v` continuous on `[a, b]` with values in `V`, with `v a = v₀`;
* the **second energy identity** `A v(t) v(t) - A v(s) v(s) = 2 ∫ₛᵗ ⟪g - d, d⟫` holds for all
  `s, t ∈ [a, b]`, where `g - d` is the element of `H` representing `A u`, and with it the bound
  `A v(t) v(t) + ∫ₐᵗ ‖d‖² ≤ A v₀ v₀ + ∫ₐᵗ ‖g‖²`

(`TauCeti.HasWeakLineDerivOn.exists_memLp_hasWeakLineDerivOn_of_gelfandDual_of_symm`).
For a parabolic equation `∂ₜu - div(a ∇u) + … = f` this says `∂ₜu ∈ L²(0, T; L²(Ω))` and
`u ∈ C([0, T]; H¹₀(Ω))` when `f ∈ L²(0, T; L²(Ω))` and `u(0) ∈ H¹₀(Ω)`. Lower-order terms `M u`
with `M : V →L[ℝ] H`, and a Gårding shift, are absorbed into `g`, since `M ∘ u ∈ L²(a, b; H)`.
The energy identity is exact, not only an estimate, so it can be added up over the pieces of a
partition of `[a, b]` on which the operator is frozen, as for coefficients depending on time.

## The argument

Formally the estimate comes from testing the equation with `u'`: since `A` is symmetric and
constant, `A u u' = ½ (A u u)'`, so `‖u'‖² + ½ (A u u)' = ⟪g, u'⟫`. Instead of justifying this
for a weak solution, the solution is constructed a second time in a **shifted Gelfand triple**, in
which `H` plays the role of `V` and `V`, with the inner product `A v w`, that of `H`.

Write `A v w = ⟪Q v, Q w⟫` for the automorphism `Q`, the square root of the Riesz operator of `A`
(`ContinuousLinearMap.metricChangeEquiv`), and let `R : H →L[ℝ] V` be the solution operator of the
stationary problem, `A (R h) = ι* h` (`IsCoercive.solutionOfFunctional`). The shifted embedding is
`J = Q ∘ R : H → V`; it has dense range because `ι` is injective, and
`⟪J x, J y⟫ = A (R x) (R y) = ⟪ι (R x), y⟫`. In the shifted triple the problem

`z' + z = g`, `z(a) = Q v₀`

is coercive, and the abstract existence theorem
(`TauCeti.exists_hasWeakLineDerivOn_gelfandDual`) produces `z ∈ L²(a, b; H)`. Read in `H`, its
equation says that `ι (R z)` has weak derivative `g - z ∈ L²(a, b; H)`, and read in `V*` it says
that `R z` is a weak solution of the original problem with the original initial value; by
uniqueness (`TauCeti.HasWeakLineDerivOn.ae_eq_of_gelfandDual`) it is `u`. In the shifted triple
the continuous pivot representative of `z` is that of `Q (R z) = Q u`, so `Q⁻¹` of it is a
representative of `u` continuous into `V`, and the energy identity of the shifted triple
(`TauCeti.HasWeakLineDerivOn.norm_sq_sub_norm_sq_eq_of_gelfandDual`) is the second energy identity
above, with `‖Q u‖² = A u u` and `z = g - d`.

## Main declarations

* `TauCeti.HasWeakLineDerivOn.exists_memLp_hasWeakLineDerivOn_of_gelfandDual_of_symm`: the weak
  time derivative in `L²(a, b; H)`, the continuous representative in `V` and the second energy
  identity.

The parabolic Dirichlet problem with time-independent symmetric principal coefficients is the
instance `TauCeti.PDE.exists_memLp_hasWeakLineDerivOn_valueL_energyFormH1_of_isSymm`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §7.1.3, Theorem 5, which proves the
  bounds on `∂ₜu` and `sup_t ‖u(t)‖_{H¹₀}` for second-order parabolic equations by Galerkin
  approximation.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped InnerProductSpace

namespace TauCeti

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {ι : V →L[ℝ] H} {A : V →L[ℝ] StrongDual ℝ V} {a b α : ℝ}

omit [CompleteSpace H] in
/-- **The shifted embedding.** For an injective `ι` and a symmetric coercive `A`, there are an
automorphism `Q` of `V` with `A v w = ⟪Q v, Q w⟫` and the solution operator `R : H →L[ℝ] V` of the
stationary problem, `A (R x) = ι* x` (Lax–Milgram), such that `Q ∘ R` has dense range. -/
private theorem exists_shiftedEmbedding (hι : Function.Injective ι)
    (hsymm : ∀ v w, A v w = A w v) (hα : 0 < α) (hA : ∀ v, α * ‖v‖ ^ 2 ≤ A v v) :
    ∃ (Q : V ≃L[ℝ] V) (R : H →L[ℝ] V), (∀ v w, ⟪Q v, Q w⟫_ℝ = A v w) ∧
      (∀ x v, A (R x) v = ⟪x, ι v⟫_ℝ) ∧ DenseRange ((Q : V →L[ℝ] V) ∘L R) := by
  have hcoer : IsCoercive A := ⟨α, hα, fun v ↦ by rw [mul_assoc, ← sq]; exact hA v⟩
  have hH := hcoer.isStrictlyPositive_continuousLinearMapOfBilin hsymm
  set Q := (A.metricChangeEquiv hH).symm
  have hQ (v w : V) : ⟪Q v, Q w⟫_ℝ = A v w := by
    rw [ContinuousLinearMap.metricChangeEquiv_symm_apply,
      ContinuousLinearMap.metricChangeEquiv_symm_apply,
      ContinuousLinearMap.inner_sqrt_apply_sqrt_apply hH.nonneg]
  set R : H →L[ℝ] V := hcoer.solutionOfFunctional ∘L ι.gelfandDual
  have hR (x : H) (v : V) : A (R x) v = ⟪x, ι v⟫_ℝ := by
    rw [ContinuousLinearMap.comp_apply, hcoer.apply_solutionOfFunctional_eq,
      ContinuousLinearMap.gelfandDual_apply]
  refine ⟨Q, R, hQ, hR, ?_⟩
  -- Dense range: if `Q y ⊥ Q (R x)` for all `x`, then `ι y ⊥ H`, so `y = 0`.
  set J : H →L[ℝ] V := (Q : V →L[ℝ] V) ∘L R
  have hperp : (LinearMap.range (J : H →ₗ[ℝ] V))ᗮ = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun z hz ↦ ?_
    obtain ⟨y, rfl⟩ : ∃ y, z = Q y := ⟨Q.symm z, (Q.apply_symm_apply z).symm⟩
    have h0 := Submodule.inner_right_of_mem_orthogonal
      (LinearMap.mem_range_self (J : H →ₗ[ℝ] V) (ι y)) hz
    simp only [ContinuousLinearMap.coe_coe, J, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, hQ, hR, inner_self_eq_zero] at h0
    rw [hι (h0.trans (map_zero ι).symm), map_zero]
  have hrange : (LinearMap.range (J : H →ₗ[ℝ] V) : Set V) = Set.range J :=
    LinearMap.coe_range _
  rw [DenseRange, ← hrange]
  exact Submodule.dense_iff_topologicalClosure_eq_top.2
    (Submodule.topologicalClosure_eq_top_iff.2 hperp)

/-- **The shifted problem.** Let `J : H →L[ℝ] V` have dense range, with
`⟪J x, J y⟫ = ⟪ι (R x), y⟫` for some `R : H →L[ℝ] V`. Then for `g ∈ L²(a, b; H)` and `y₀ ∈ V`
the problem `z' + z = g`, `z(a) = y₀` in the Gelfand triple `H ↪ V ↪ H*` given by `J` has a
solution `z ∈ L²(a, b; H)`. Read in `H`, its equation says that `ι ∘ R ∘ z` has weak derivative
`g - z`; the continuous representative `w₁` of `J ∘ z` starts at `y₀` and satisfies the energy
identity `‖w₁ t‖² - ‖w₁ s‖² = 2 ∫ₛᵗ ⟪g - z, z⟫`. -/
private theorem exists_shiftedSolution [TopologicalSpace.SeparableSpace H] (hab : a ≤ b)
    {J R : H →L[ℝ] V} (hJd : DenseRange J) (hJ : ∀ x y, ⟪J x, J y⟫_ℝ = ⟪ι (R x), y⟫_ℝ)
    {g : ℝ → H} (hg : MemLp g 2 (volume.restrict (Ioo a b))) (y₀ : V) :
    ∃ (z : ℝ → H) (w₁ : ℝ → V), MemLp z 2 (volume.restrict (Ioo a b)) ∧
      HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι (R (z t)))
        (fun t ↦ g t - z t) 1 ∧
      ContinuousOn w₁ (Icc a b) ∧ (fun t ↦ J (z t)) =ᵐ[volume.restrict (Ioo a b)] w₁ ∧
      w₁ a = y₀ ∧ ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        ‖w₁ t‖ ^ 2 - ‖w₁ s‖ ^ 2 = 2 * ∫ r in s..t, ⟪g r - z r, z r⟫_ℝ := by
  -- In the shifted triple the operator is the inner product of `H`, coercive with constant `1`.
  have hA₁ : ∀ x y : H, AEStronglyMeasurable (fun _ : ℝ ↦ innerSL ℝ x y)
      (volume.restrict (Ioo a b)) := fun _ _ ↦ aestronglyMeasurable_const
  have hA₁_bound : ∀ᵐ _ : ℝ ∂volume.restrict (Ioo a b), ‖innerSL ℝ (E := H)‖ ≤ 1 :=
    Eventually.of_forall fun _ ↦ norm_innerSL_le ℝ
  have hA₁_coer : ∀ᵐ _ : ℝ ∂volume.restrict (Ioo a b), ∀ x : H,
      1 * ‖x‖ ^ 2 - 0 * ‖J x‖ ^ 2 ≤ innerSL ℝ x x :=
    Eventually.of_forall fun _ x ↦ by simp
  have hf₁ : MemLp (fun t ↦ innerSL ℝ (g t)) 2 (volume.restrict (Ioo a b)) :=
    (innerSL ℝ).comp_memLp' hg
  obtain ⟨z, w₁, hz, hz', hzd, hw₁, hae₁, hw₁a⟩ :=
    exists_hasWeakLineDerivOn_gelfandDual (A := fun _ ↦ innerSL ℝ) hJd hab hA₁ hA₁_bound one_pos
      hA₁_coer hf₁ y₀
  -- Read in `H` through the Riesz isomorphism, `J* J = ι ∘ R` and the equation is `z' = g - z`.
  set T : StrongDual ℝ H →L[ℝ] H :=
    (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hT₁ (x : H) : T (J.gelfandDual (J x)) = ι (R x) := by
    refine ext_inner_right ℝ fun y ↦ ?_
    simp [T, InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.gelfandDual_apply, hJ]
  have hT₂ (x : H) : T (innerSL ℝ x) = x := by
    refine ext_inner_right ℝ fun y ↦ ?_
    simp [T]
  refine ⟨z, w₁, hz, by simpa only [map_sub, hT₁, hT₂] using hzd.clm_comp T, hw₁, hae₁, hw₁a,
    fun s hs t ht ↦ ?_⟩
  -- The energy identity of the shifted triple, whose pairing is the inner product of `H`.
  rw [hzd.norm_sq_sub_norm_sq_eq_of_gelfandDual hz hz' hw₁ hae₁ hs ht]
  simp only [sub_apply, innerSL_apply_apply, inner_sub_left]
  -- `simp` rewrites only the first pairing. In the second, `innerSL ℝ` is the operator family of
  -- the existence theorem, used as an `ℝ`-linear map `H →L[ℝ] H*`, while `innerSL_apply_apply` is
  -- stated for the conjugate-linear `H →L⋆[ℝ] H*`; over `ℝ` the two agree by definition.
  rfl

/-- `TauCeti.HasWeakLineDerivOn.exists_memLp_hasWeakLineDerivOn_of_gelfandDual_of_symm` for
`a ≤ b`, where the shifted problem can be solved, without the energy bound. -/
private theorem exists_memLp_hasWeakLineDerivOn_of_gelfandDual_of_symm_of_le
    [TopologicalSpace.SeparableSpace H] (hab : a ≤ b) (hι : Function.Injective ι)
    (hsymm : ∀ v w, A v w = A w v) (hα : 0 < α) (hA : ∀ v, α * ‖v‖ ^ 2 ≤ A v v)
    {g : ℝ → H} (hg : MemLp g 2 (volume.restrict (Ioo a b))) {v₀ : V} {u : ℝ → V}
    {u' : ℝ → StrongDual ℝ V} {w : ℝ → H}
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι.gelfandDual (ι (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo a b))) (hu' : MemLp u' 2 (volume.restrict (Ioo a b)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo a b), u' t + A (u t) = ι.gelfandDual (g t))
    (hw : ContinuousOn w (Icc a b)) (hae : (fun t ↦ ι (u t)) =ᵐ[volume.restrict (Ioo a b)] w)
    (h₀ : w a = ι v₀) :
    ∃ (d : ℝ → H) (v : ℝ → V), MemLp d 2 (volume.restrict (Ioo a b)) ∧
      HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι (u t)) d 1 ∧
      (∀ᵐ t ∂volume.restrict (Ioo a b), u' t = ι.gelfandDual (d t)) ∧
      ContinuousOn v (Icc a b) ∧ u =ᵐ[volume.restrict (Ioo a b)] v ∧ v a = v₀ ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        A (v t) (v t) - A (v s) (v s) = 2 * ∫ r in s..t, ⟪g r - d r, d r⟫_ℝ := by
  -- Solve the shifted problem `z' + z = g`, `z(a) = Q v₀`; `z` will be `A u = g - u'`.
  obtain ⟨Q, R, hQ, hR, hJd⟩ := exists_shiftedEmbedding hι hsymm hα hA
  have hRι (x : H) : A (R x) = ι.gelfandDual x := by
    ext v
    rw [hR, ContinuousLinearMap.gelfandDual_apply]
  obtain ⟨z, w₁, hz, hH, hw₁, hae₁, hw₁a, hen⟩ := exists_shiftedSolution (ι := ι) (R := R) hab
    hJd (fun x y ↦ by simp [hQ, hsymm (R x), hR, real_inner_comm]) hg (Q v₀)
  -- Read in `V*`, the shifted equation says that `R z` solves the original problem, with the same
  -- initial value, so by uniqueness `u = R z`.
  have hd : MemLp (fun t ↦ g t - z t) 2 (volume.restrict (Ioo a b)) := hg.sub hz
  have huu : u =ᵐ[volume.restrict (Ioo a b)] fun t ↦ R (z t) :=
    HasWeakLineDerivOn.ae_eq_of_gelfandDual (A := fun _ ↦ A) (β := 0) h
      (hH.clm_comp ι.gelfandDual) hu hu' (R.comp_memLp' hz) (ι.gelfandDual.comp_memLp' hd) hα
      le_rfl (Eventually.of_forall fun _ v ↦ by simpa using hA v) heq
      (Eventually.of_forall fun t ↦ by simp [hRι, map_sub])
      hw hae ((ι.continuous.comp Q.symm.continuous).comp_continuousOn hw₁)
      (by filter_upwards [hae₁] with t ht; simp [← ht])
      (by simp only [Function.comp_apply, hw₁a, Q.symm_apply_apply, h₀])
  -- The continuous representative of `J z = Q (R z)` gives the one of `u = R z` in `V`, and the
  -- energy identity of the shifted problem is the one of `A u u`, since `A v v = ‖Q v‖²`.
  have hAw (t : ℝ) : A (Q.symm (w₁ t)) (Q.symm (w₁ t)) = ‖w₁ t‖ ^ 2 := by
    rw [← hQ, Q.apply_symm_apply, real_inner_self_eq_norm_sq]
  refine ⟨fun t ↦ g t - z t, fun t ↦ Q.symm (w₁ t), hd,
    hH.congr_ae (huu.mono fun t ht ↦ by simp only [ht]), ?_,
    Q.symm.continuous.comp_continuousOn hw₁, ?_, by simp only [hw₁a, Q.symm_apply_apply],
    fun s hs t ht ↦ ?_⟩
  · filter_upwards [heq, huu] with t ht hut
    rw [map_sub, ← ht, ← hRι, hut, add_sub_cancel_right]
  · filter_upwards [huu, hae₁] with t hut ht₁
    rw [hut, ← ht₁, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      Q.symm_apply_apply]
  · rw [hAw, hAw, hen s hs t ht]
    congr 2
    ext r
    rw [sub_sub_cancel, real_inner_comm]

/-- **Time regularity of weak solutions.** Let `ι : V →L[ℝ] H` be an injective map of real
Hilbert spaces, `H` separable, and let `A : V →L[ℝ] V*` be symmetric and coercive,
`α ‖v‖² ≤ A v v` with `α > 0`. Let `u ∈ L²(a, b; V)` be a weak solution of `u' + A u = ι* g` with
`g ∈ L²(a, b; H)`, whose continuous `H`-valued representative `w` takes the value `w a = ι v₀`
for some `v₀ ∈ V`. Then `ι ∘ u` has a weak time derivative `d ∈ L²(a, b; H)` on `(a, b)`, with
`u' = ι* d` almost everywhere, and `u` has a representative `v` continuous on `[a, b]` with
values in `V` and `v a = v₀`. It satisfies the **second energy identity**

`A v(t) v(t) - A v(s) v(s) = 2 ∫ₛᵗ ⟪g - d, d⟫` for all `s, t ∈ [a, b]`,

the integrated form of `(A u u)' = 2 A u u'`, in which `g - d` represents `A u` in `H`, and the
energy bound `A v(t) v(t) + ∫ₐᵗ ‖d‖² ≤ A v₀ v₀ + ∫ₐᵗ ‖g‖²` for every `t ∈ [a, b]`. -/
theorem HasWeakLineDerivOn.exists_memLp_hasWeakLineDerivOn_of_gelfandDual_of_symm
    [TopologicalSpace.SeparableSpace H] (hι : Function.Injective ι)
    (hsymm : ∀ v w, A v w = A w v) (hα : 0 < α) (hA : ∀ v, α * ‖v‖ ^ 2 ≤ A v v)
    {g : ℝ → H} (hg : MemLp g 2 (volume.restrict (Ioo a b))) {v₀ : V} {u : ℝ → V}
    {u' : ℝ → StrongDual ℝ V} {w : ℝ → H}
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι.gelfandDual (ι (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo a b))) (hu' : MemLp u' 2 (volume.restrict (Ioo a b)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo a b), u' t + A (u t) = ι.gelfandDual (g t))
    (hw : ContinuousOn w (Icc a b)) (hae : (fun t ↦ ι (u t)) =ᵐ[volume.restrict (Ioo a b)] w)
    (h₀ : w a = ι v₀) :
    ∃ (d : ℝ → H) (v : ℝ → V), MemLp d 2 (volume.restrict (Ioo a b)) ∧
      HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι (u t)) d 1 ∧
      (∀ᵐ t ∂volume.restrict (Ioo a b), u' t = ι.gelfandDual (d t)) ∧
      ContinuousOn v (Icc a b) ∧ u =ᵐ[volume.restrict (Ioo a b)] v ∧ v a = v₀ ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        A (v t) (v t) - A (v s) (v s) = 2 * ∫ r in s..t, ⟪g r - d r, d r⟫_ℝ) ∧
      ∀ t ∈ Icc a b, A (v t) (v t) + ∫ r in a..t, ‖d r‖ ^ 2 ≤ A v₀ v₀ + ∫ r in a..t, ‖g r‖ ^ 2 := by
  rcases lt_or_ge b a with hba | hab
  · -- On an empty interval there is nothing to prove.
    have hI : Ioo a b = ∅ := Ioo_eq_empty_of_le hba.le
    have hJ : Icc a b = ∅ := Icc_eq_empty_of_lt hba
    refine ⟨0, fun _ ↦ v₀, MemLp.zero, hasWeakLineDerivOn_iff_locally.2 fun x hx ↦ ?_,
      by simp [hI], by simp [hJ],
      by rw [hI, Measure.restrict_empty, ae_zero]; exact Filter.eventually_bot, rfl, by simp [hJ],
      by simp [hJ]⟩
    simp [hI] at hx
  obtain ⟨d, v, hd, hdd, hu'd, hv, huv, hva, hid⟩ :=
    exists_memLp_hasWeakLineDerivOn_of_gelfandDual_of_symm_of_le hab hι hsymm hα hA hg h hu hu'
      heq hw hae h₀
  refine ⟨d, v, hd, hdd, hu'd, hv, huv, hva, hid, fun t ht ↦ ?_⟩
  -- The bound follows from the identity on `[a, t]` and `2 ⟪g - d, d⟫ ≤ ‖g‖² - ‖d‖²`.
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab
  have hgd : IntegrableOn (fun r ↦ ⟪g r - d r, d r⟫_ℝ) (Ioo a b) :=
    memLp_one_iff_integrable.1 ((innerSL ℝ (E := H)).memLp_of_bilin 1 (hg.sub hd) hd)
  have hg2 : IntegrableOn (fun r ↦ ‖g r‖ ^ 2) (Ioo a b) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  have hd2 : IntegrableOn (fun r ↦ ‖d r‖ ^ 2) (Ioo a b) :=
    (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).1 hd
  have hg2t := hg2.intervalIntegrable_of_mem_Icc ha ht
  have hd2t := hd2.intervalIntegrable_of_mem_Icc ha ht
  have hle : ∫ r in a..t, 2 * ⟪g r - d r, d r⟫_ℝ ≤ ∫ r in a..t, (‖g r‖ ^ 2 - ‖d r‖ ^ 2) :=
    intervalIntegral.integral_mono_on ht.1 ((hgd.intervalIntegrable_of_mem_Icc ha ht).const_mul 2)
      (hg2t.sub hd2t) fun r _ ↦ by
        rw [inner_sub_left, real_inner_self_eq_norm_sq]
        nlinarith [norm_sub_sq_real (g r) (d r), sq_nonneg ‖g r - d r‖]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hg2t hd2t] at hle
  have := hid a ha t ht
  rw [hva] at this
  linarith

end TauCeti
