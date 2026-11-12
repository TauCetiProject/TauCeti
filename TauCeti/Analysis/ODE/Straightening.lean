/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
public import TauCeti.Analysis.ODE.InitialCondition
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem
public import TauCeti.Dynamics.Flow.LieBracket
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# The straightening theorem for vector fields on a normed space

Near a point where a `C^n` vector field `w` on a finite-dimensional real normed space `E` does not
vanish, some `C^n` change of coordinates carries `w` to a constant field. Precisely, there is an
open partial homeomorphism `φ` of `E`, `C^n` with `C^n` inverse, whose domain contains the point
`a` and whose derivative sends `w y` to `w a` at every point `y` of its domain
(`TauCeti.exists_openPartialHomeomorph_fderiv_eq_const`). This is the flow-box theorem: in the
coordinates `φ`, the integral curves of `w` become parallel straight lines traversed with constant
velocity `w a`.

Cut `w` off to a globally Lipschitz `C^n` field `g` that agrees with it near `a`, and let `Φ` be the
global flow of `g`, which is `C^n` jointly in the initial condition and time. Choose a continuous
linear functional `ℓ` with `ℓ (w a) = 1` and set

`ψ z = Φ (a + (z - ℓ z • w a)) (ℓ z)`.

The flow law gives `ψ (z + s • w a) = Φ (ψ z) s`, so differentiating in `s` shows that `dψ z`
sends `w a` to `g (ψ z)`. At `z = 0` the derivative of `ψ` is the identity, so by the inverse
function theorem with `C^n` inverse
(`ContDiffOn.exists_openPartialHomeomorph_fderiv_symm_apply_eq`) `ψ` is a local
diffeomorphism near `0` whose inverse sends `g` to `w a`; restricted to where `g = w`, that inverse
is the required `φ`.

Finitely many fields `w i` with linearly independent values at `a` and pairwise vanishing Lie
brackets near `a` are straightened simultaneously: one `C^n` change of coordinates `φ` sends every
`w i y` to `w i a` (`TauCeti.exists_openPartialHomeomorph_fderiv_eq_const_of_lieBracket_eq_zero`).
Cut each field off to a globally Lipschitz `g i` with flow `Φ i`, choose continuous linear
functionals `ℓ i` with `ℓ i (w j a) = δ i j`, and compose the flows,

`ψ z = Φ i₁ (ℓ i₁ z) (⋯ (Φ iₖ (ℓ iₖ z) (a + (z - ∑ i, ℓ i z • w i a))))`.

The brackets of the `g i` vanish near `a`, so their flows commute for short times near `a`
(`TauCeti.flowOfLipschitz_comm_of_lieBracket_eq_zero_on`). Each flow can therefore be moved to the
outside of the composite, so that `ψ (z + s • w i a) = Φ i s (ψ z)` and `dψ z` sends `w i a` to
`g i (ψ z)` for `z` near `0`. Again `dψ 0` is the identity, and the local inverse of `ψ` is the
required `φ`.

## Main results

* `TauCeti.exists_openPartialHomeomorph_fderiv_eq_const`: a nonvanishing `C^n` vector field is
  constant in suitable `C^n` local coordinates.
* `TauCeti.exists_openPartialHomeomorph_fderiv_eq_const_of_lieBracket_eq_zero`: finitely many
  `C^n` vector fields with linearly independent values and vanishing brackets are simultaneously
  constant in suitable `C^n` local coordinates.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 9.22 (canonical form near a regular point) and Theorem 9.46 (canonical
  form for commuting vector fields).
-/

public section

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The coordinates `ψ z = Φ (a + (z - ℓ z • u)) (ℓ z)` built from a flow `Φ`: flow for time
`ℓ z` from the point of the hyperplane through `a` with direction `ker ℓ` reached by `z`. -/
private def flowBoxMap (Φ : E → ℝ → E) (a u : E) (ℓ : E →L[ℝ] ℝ) (z : E) : E :=
  Φ (a + (z - ℓ z • u)) (ℓ z)

/-- The flow-box coordinates of a flow intertwine translation along `u` with the flow. -/
private theorem flowBoxMap_add_smul {Φ : E → ℝ → E} (hΦ : ∀ x t s, Φ x (t + s) = Φ (Φ x t) s)
    {a u : E} {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ u = 1) (z : E) (s : ℝ) :
    flowBoxMap Φ a u ℓ (z + s • u) = Φ (flowBoxMap Φ a u ℓ z) s := by
  have hz : z + s • u - (ℓ z + s) • u = z - ℓ z • u := by
    rw [add_smul]
    abel
  simp only [flowBoxMap, map_add, map_smul, hℓ, smul_eq_mul, mul_one, hz, hΦ]

/-- The affine map `z ↦ (a + (z - ℓ z • u), ℓ z)` feeding the flow in the flow-box coordinates. -/
private theorem hasFDerivAt_flowBoxArg (a u : E) (ℓ : E →L[ℝ] ℝ) (z : E) :
    HasFDerivAt (fun z : E ↦ (a + (z - ℓ z • u), ℓ z))
      (((ContinuousLinearMap.id ℝ E) - ℓ.smulRight u).prod ℓ) z :=
  (((hasFDerivAt_id z).sub (ℓ.hasFDerivAt.smul_const u)).const_add a).prodMk ℓ.hasFDerivAt

section Flow

variable [CompleteSpace E] {g : E → E} {K : NNReal} (hg : LipschitzWith K g) {a u : E}
  {ℓ : E →L[ℝ] ℝ}
include hg

/-- The derivative of the flow-box coordinates of the flow of `g` in the direction `u` is `g`. -/
private theorem fderiv_flowBoxMap_apply (hℓ : ℓ u = 1) {z : E}
    (hd : DifferentiableAt ℝ (flowBoxMap (ODE.globalSolution g hg) a u ℓ) z) :
    fderiv ℝ (flowBoxMap (ODE.globalSolution g hg) a u ℓ) z u =
      g (flowBoxMap (ODE.globalSolution g hg) a u ℓ z) := by
  set ψ := flowBoxMap (ODE.globalSolution g hg) a u ℓ
  -- Differentiate `s ↦ ψ (z + s • u) = Φ (ψ z) s` at `s = 0` in two ways.
  have h₁ : HasDerivAt (fun s : ℝ ↦ ψ (z + s • u)) (fderiv ℝ ψ z u) 0 := by
    have hline : HasDerivAt (fun s : ℝ ↦ z + s • u) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add z
    have hdiff : HasFDerivAt ψ (fderiv ℝ ψ z) (z + (0 : ℝ) • u) := by
      simpa using hd.hasFDerivAt
    exact hdiff.comp_hasDerivAt (0 : ℝ) hline
  have h₂ : HasDerivAt (fun s : ℝ ↦ ψ (z + s • u)) (g (ψ z)) 0 := by
    have h := ODE.hasDerivAt_globalSolution g hg (ψ z) 0
    rw [ODE.globalSolution_zero] at h
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)
    exact flowBoxMap_add_smul (ODE.globalSolution_add g hg) hℓ z s
  exact h₁.unique h₂

/-- The flow-box coordinates of the flow of `g` at the base point `a`, with `g a = u`, have the
identity as derivative at `0`. -/
private theorem hasFDerivAt_flowBoxMap_zero (hga : g a = u)
    (hd : DifferentiableAt ℝ (fun p : E × ℝ ↦ ODE.globalSolution g hg p.1 p.2) (a, 0)) :
    HasFDerivAt (flowBoxMap (ODE.globalSolution g hg) a u ℓ) (ContinuousLinearMap.id ℝ E) 0 := by
  set Φ := ODE.globalSolution g hg
  set D := fderiv ℝ (fun p : E × ℝ ↦ Φ p.1 p.2) (a, 0)
  -- `D` restricted to the space directions is the identity, since `Φ x 0 = x`.
  have hDx (h : E) : D (h, 0) = h := by
    have h₁ := hd.hasFDerivAt.comp a (hasFDerivAt_prodMk_left (𝕜 := ℝ) a (0 : ℝ))
    have h₂ : HasFDerivAt (fun x : E ↦ Φ x 0) (ContinuousLinearMap.id ℝ E) a := by
      rw [show (fun x : E ↦ Φ x 0) = id from funext (ODE.globalSolution_zero g hg)]
      exact hasFDerivAt_id a
    simpa using congrArg (fun L : E →L[ℝ] E ↦ L h) (h₁.unique h₂)
  -- `D` in the time direction is `g a`, the velocity of the flow line through `a`.
  have hDt : D (0, 1) = u := by
    have h₁ := hd.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_const (0 : ℝ) a).prodMk (hasDerivAt_id (0 : ℝ)))
    have h₂ := ODE.hasDerivAt_globalSolution g hg a 0
    rw [ODE.globalSolution_zero, hga] at h₂
    exact h₁.unique h₂
  have hd' : HasFDerivAt (fun p : E × ℝ ↦ Φ p.1 p.2) D (a + (0 - ℓ 0 • u), ℓ 0) := by
    simpa using hd.hasFDerivAt
  unfold flowBoxMap
  refine (hd'.comp (0 : E) (hasFDerivAt_flowBoxArg a u ℓ 0)).congr_fderiv ?_
  ext h
  have hsplit : ((h - ℓ h • u, ℓ h) : E × ℝ) = (h - ℓ h • u, 0) + ℓ h • ((0 : E), (1 : ℝ)) := by
    simp
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.prod_apply, sub_apply, ContinuousLinearMap.smulRight_apply]
  rw [hsplit, map_add, map_smul, hDx, hDt]
  simp

end Flow

/-! ### Commuting vector fields -/

section CommutingFlows

variable {ι X : Type*} [TopologicalSpace X]

/-- The composite `Φ_{i₁}^{t i₁} ∘ ⋯ ∘ Φ_{iₖ}^{t iₖ}` of the time maps of a family of flows, along
the list of indices `[i₁, …, iₖ]`. -/
private def flowComp (Φ : ι → Flow ℝ X) : List ι → (ι → ℝ) → X → X
  | [], _, x => x
  | i :: l, t, x => Φ i (t i) (flowComp Φ l t x)

private theorem flowComp_zero (Φ : ι → Flow ℝ X) (l : List ι) (x : X) : flowComp Φ l 0 x = x := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [flowComp, ih]

private theorem continuous_flowComp (Φ : ι → Flow ℝ X) (l : List ι) :
    Continuous fun p : (ι → ℝ) × X ↦ flowComp Φ l p.1 p.2 := by
  induction l with
  | nil => exact continuous_snd
  | cons i l ih => exact (Φ i).continuous ((continuous_apply i).comp continuous_fst) ih

private theorem contDiff_flowComp [Fintype ι] {n : WithTop ℕ∞} (Φ : ι → Flow ℝ E)
    (hΦ : ∀ i, ContDiff ℝ n fun p : E × ℝ ↦ Φ i p.2 p.1) (l : List ι) :
    ContDiff ℝ n fun p : (ι → ℝ) × E ↦ flowComp Φ l p.1 p.2 := by
  induction l with
  | nil => exact contDiff_snd
  | cons i l ih => exact (hΦ i).comp (ih.prodMk (contDiff_pi.1 contDiff_fst i))

variable [DecidableEq ι]

/-- Moving the time of an index outside the list does not change the composite. -/
private theorem flowComp_add_smul_single_of_notMem (Φ : ι → Flow ℝ X) {i : ι} {l : List ι}
    (hi : i ∉ l) (t : ι → ℝ) (s : ℝ) (x : X) :
    flowComp Φ l (t + s • Pi.single i 1) x = flowComp Φ l t x := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [List.mem_cons, not_or] at hi
    obtain ⟨hij, hil⟩ := hi
    simp [flowComp, ih hil, Ne.symm hij]

/-- If the flow of `i` commutes near `a` with every other flow of the family, then moving the
time of `i` in the composite along a list containing `i` once is flowing along `Φ i`, near
`(0, 0, a)`. -/
private theorem eventually_flowComp_add_smul_single (Φ : ι → Flow ℝ X) {a : X} {i : ι}
    (hcomm : ∀ j, j ≠ i → ∀ᶠ q : ℝ × ℝ × X in 𝓝 (0, 0, a),
      Φ j q.1 (Φ i q.2.1 q.2.2) = Φ i q.2.1 (Φ j q.1 q.2.2))
    {l : List ι} (hl : l.Nodup) (hi : i ∈ l) :
    ∀ᶠ p : (ι → ℝ) × ℝ × X in 𝓝 (0, 0, a),
      flowComp Φ l (p.1 + p.2.1 • Pi.single i 1) p.2.2 = Φ i p.2.1 (flowComp Φ l p.1 p.2.2) := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    obtain ⟨hjl, hl⟩ := List.nodup_cons.1 hl
    by_cases hji : j = i
    · subst hji
      refine Eventually.of_forall fun p ↦ ?_
      simp only [flowComp, flowComp_add_smul_single_of_notMem Φ hjl, Pi.add_apply,
        Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, add_comm (p.1 j), Flow.map_add]
    · have hil : i ∈ l := (List.mem_cons.1 hi).resolve_left (Ne.symm hji)
      -- Commute `Φ i` past `Φ j` at the point reached by the rest of the list.
      have hcont : ContinuousAt (fun p : (ι → ℝ) × ℝ × X ↦
          (p.1 j, p.2.1, flowComp Φ l p.1 p.2.2)) (0, 0, a) :=
        (((continuous_apply j).comp continuous_fst).prodMk
          ((continuous_fst.comp continuous_snd).prodMk ((continuous_flowComp Φ l).comp
            (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))).continuousAt
      have h0 : ((0 : ι → ℝ) j, (0 : ℝ), flowComp Φ l 0 a) = (0, 0, a) := by
        simp [flowComp_zero]
      have hj := (h0 ▸ hcont.tendsto).eventually (hcomm j hji)
      filter_upwards [ih hl hil, hj] with p hp hpj
      simp only [flowComp, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hji, smul_zero,
        add_zero, hp]
      exact hpj

end CommutingFlows

variable [FiniteDimensional ℝ E]

/-- **The straightening theorem** (flow-box theorem). A `C^n` vector field `w`, `1 ≤ n`, defined
near a point `a` of a finite-dimensional real normed space, with `w a ≠ 0`, is constant in suitable
`C^n` coordinates: there is an open partial homeomorphism `φ`, `C^n` on its source with `C^n`
inverse on its target, such that `a ∈ φ.source` and `dφ_y (w y) = w a` for every `y ∈ φ.source`. -/
theorem exists_openPartialHomeomorph_fderiv_eq_const {n : ℕ∞} (hn : 1 ≤ n) {w : E → E}
    {s : Set E} {a : E} (hw : ContDiffOn ℝ n w s) (hs : s ∈ 𝓝 a) (ha : w a ≠ 0) :
    ∃ φ : OpenPartialHomeomorph E E, a ∈ φ.source ∧ (∀ y ∈ φ.source, ContDiffAt ℝ n φ y) ∧
      (∀ z ∈ φ.target, ContDiffAt ℝ n φ.symm z) ∧ ∀ y ∈ φ.source, fderiv ℝ φ y (w y) = w a := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  set u := w a
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by
    have : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
    exact (lt_of_lt_of_le zero_lt_one this).ne'
  -- A globally Lipschitz `C^n` field `g` agreeing with `w` on an open set `S ∋ a`.
  obtain ⟨k, hk⟩ : ∃ k : ℕ∞, n = k + 1 := ⟨n - 1, (tsub_add_cancel_of_le hn).symm⟩
  have hw' : ContDiffOn ℝ ((k : WithTop ℕ∞) + 1) w s := by
    rw [hk] at hw
    exact_mod_cast hw
  obtain ⟨g, K, hg, hgK, hgw⟩ :=
    hw'.exists_lipschitzWith_contDiff_eventuallyEq_of_finiteDimensional hs
  obtain ⟨S, hSo, haS, hSg⟩ : ∃ S : Set E, IsOpen S ∧ a ∈ S ∧ ∀ y ∈ S, g y = w y := by
    obtain ⟨S, hS, hSo, haS⟩ := mem_nhds_iff.1 hgw
    exact ⟨S, hSo, haS, hS⟩
  -- The flow `Φ` of `g` and the flow-box coordinates `ψ`.
  set Φ := ODE.globalSolution g hgK with hΦ
  have hΦs : ContDiff ℝ n fun p : E × ℝ ↦ Φ p.1 p.2 := by
    rw [hk]
    exact_mod_cast ODE.contDiff_globalSolution g hgK hg
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_eq_one (R := ℝ) ha
  set ψ := flowBoxMap Φ a u ℓ with hψ
  have hψs : ContDiff ℝ n ψ :=
    hΦs.comp ((contDiff_const.add (contDiff_id.sub (ℓ.contDiff.smul contDiff_const))).prodMk
      ℓ.contDiff)
  have hψ0 : ψ 0 = a := by
    simp [hψ, flowBoxMap, hΦ, ODE.globalSolution_zero]
  have hψu (z : E) : fderiv ℝ ψ z u = g (ψ z) :=
    fderiv_flowBoxMap_apply hgK hℓ (hψs.differentiable hn0 z)
  have hψ0' : HasFDerivAt ψ (ContinuousLinearMap.id ℝ E) 0 :=
    hasFDerivAt_flowBoxMap_zero hgK (hSg a haS) (hΦs.differentiable hn0 _)
  -- Invert `ψ` near `0`, on the open set where `ψ` lands in `S`, where `g = w`.
  obtain ⟨Θ, hΘ, h0Θ, hΘS, hΘs, hΘg⟩ :=
    ContDiffOn.exists_openPartialHomeomorph_fderiv_symm_apply_eq hψs.contDiffOn
      (hSo.preimage hψs.continuous) (show ψ 0 ∈ S from hψ0 ▸ haS) (by exact_mod_cast hn)
      (e := ContinuousLinearEquiv.refl ℝ E) (by rw [ContinuousLinearEquiv.coe_refl, hψ0'.fderiv])
      (v := fun _ : Unit ↦ g) (u := fun _ ↦ u) fun z _ _ ↦ hψu z
  refine ⟨Θ.symm, hψ0 ▸ hΘ ▸ Θ.map_source h0Θ,
    fun y hy ↦ hΘs.contDiffAt (Θ.open_target.mem_nhds hy), fun z _ ↦ ?_, fun y hy ↦ ?_⟩
  · rw [OpenPartialHomeomorph.symm_symm, hΘ]
    exact hψs.contDiffAt
  · have hyS : y ∈ S := by
      rw [← Θ.right_inv hy, hΘ]
      exact hΘS (Θ.map_target hy)
    rw [← hSg y hyS]
    exact hΘg y hy ()

section Commuting

variable {ι : Type*} [Finite ι]

/-- **The canonical form for commuting vector fields** (simultaneous flow-box theorem). Let
`w i`, for `i` in a finite index set, be `C^n` vector fields, `1 ≤ n`, defined near a point `a` of
a finite-dimensional real normed space, with linearly independent values `w i a`, and whose
pairwise Lie brackets vanish near `a`. Then the fields are simultaneously constant in suitable
`C^n` coordinates: there is an open partial homeomorphism `φ`, `C^n` on its source with `C^n`
inverse on its target, such that `a ∈ φ.source` and `dφ_y (w i y) = w i a` for every
`y ∈ φ.source` and every `i`. -/
theorem exists_openPartialHomeomorph_fderiv_eq_const_of_lieBracket_eq_zero {n : ℕ∞} (hn : 1 ≤ n)
    {w : ι → E → E} {s : Set E} {a : E} (hw : ∀ i, ContDiffOn ℝ n (w i) s) (hs : s ∈ 𝓝 a)
    (hli : LinearIndependent ℝ fun i ↦ w i a)
    (hbr : Pairwise fun i j ↦ VectorField.lieBracket ℝ (w i) (w j) =ᶠ[𝓝 a] 0) :
    ∃ φ : OpenPartialHomeomorph E E, a ∈ φ.source ∧ (∀ y ∈ φ.source, ContDiffAt ℝ n φ y) ∧
      (∀ z ∈ φ.target, ContDiffAt ℝ n φ.symm z) ∧
        ∀ y ∈ φ.source, ∀ i, fderiv ℝ φ y (w i y) = w i a := by
  -- Cut the fields off to globally Lipschitz fields `g i`, whose flows `Φ i` commute near `a`.
  -- With functionals `P` dual to the vectors `u i = w i a`, the composite `ψ` of the flows for the
  -- times `P z`, started on the affine complement of the `u i` through `a`, satisfies
  -- `dψ_z (u i) = g i (ψ z)` near `0` and `dψ_0 = id`; its local inverse is the required chart.
  classical
  have := Fintype.ofFinite ι
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  set u : ι → E := fun i ↦ w i a
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by
    have : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
    exact (lt_of_lt_of_le zero_lt_one this).ne'
  -- Globally Lipschitz `C^n` fields `g i` agreeing with `w i` near `a`.
  obtain ⟨k, hk⟩ : ∃ k : ℕ∞, n = k + 1 := ⟨n - 1, (tsub_add_cancel_of_le hn).symm⟩
  have hcut (i : ι) : ∃ (g : E → E) (K : NNReal), ContDiff ℝ ((k : WithTop ℕ∞) + 1) g ∧
      LipschitzWith K g ∧ g =ᶠ[𝓝 a] w i := by
    have hwi : ContDiffOn ℝ ((k : WithTop ℕ∞) + 1) (w i) s := by
      have := hw i
      rw [hk] at this
      exact_mod_cast this
    exact hwi.exists_lipschitzWith_contDiff_eventuallyEq_of_finiteDimensional hs
  choose g K hg hgK hgw using hcut
  have hg1 (i : ι) : ContDiff ℝ 1 (g i) := (hg i).of_le (by simp)
  -- An open set `S ∋ a` on which `g = w`.
  obtain ⟨S, hSg, hSo, haS⟩ := eventually_nhds_iff.1 (eventually_all.2 hgw)
  -- The flows of the `g i` commute for short times near `a`.
  set Φ : ι → Flow ℝ E := fun i ↦ flowOfLipschitz (g i) (hgK i) with hΦ
  have hΦs (i : ι) : ContDiff ℝ n fun p : E × ℝ ↦ Φ i p.2 p.1 := by
    rw [hk]
    simpa [hΦ] using ODE.contDiff_globalSolution (g i) (hgK i) (hg i)
  have hcomm (i j : ι) (hji : j ≠ i) : ∀ᶠ q : ℝ × ℝ × E in 𝓝 (0, 0, a),
      Φ j q.1 (Φ i q.2.1 q.2.2) = Φ i q.2.1 (Φ j q.1 q.2.2) :=
    eventually_flowOfLipschitz_comm (hgK j) (hg1 j) (hgK i) ((hg i).differentiable (by simp))
      (((hgw j).lieBracket_vectorField (hgw i)).trans (hbr hji))
  -- Functionals `P` dual to the `u i`, and the flow-box coordinates `ψ`.
  set Lc : (ι → ℝ) →L[ℝ] E := LinearMap.toContinuousLinearMap (Fintype.linearCombination ℝ u)
  obtain ⟨P₀, hP₀⟩ := (Fintype.linearCombination ℝ u).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hli.fintypeLinearCombination_injective)
  set P : E →L[ℝ] (ι → ℝ) := LinearMap.toContinuousLinearMap P₀
  have hPL (c : ι → ℝ) : P (Lc c) = c := LinearMap.congr_fun hP₀ c
  have hLc (c : ι → ℝ) : Lc c = ∑ i, c i • u i := Fintype.linearCombination_apply ℝ u c
  have hLs (i : ι) : Lc (Pi.single i 1) = u i := by simp [hLc, Pi.single_apply]
  have hPu (i : ι) (z : E) (r : ℝ) : P (z + r • u i) = P z + r • Pi.single i 1 := by
    rw [map_add, map_smul, ← hLs, hPL]
  set l := (Finset.univ : Finset ι).toList
  set ψ : E → E := fun z ↦ flowComp Φ l (P z) (a + (z - Lc (P z))) with hψ
  have hψs : ContDiff ℝ n ψ :=
    (contDiff_flowComp Φ hΦs l).comp (P.contDiff.prodMk
      (contDiff_const.add (contDiff_id.sub (Lc.contDiff.comp P.contDiff))))
  have hψ0 : ψ 0 = a := by simp [hψ, flowComp_zero]
  -- Translating `z` along `u i` flows `ψ z` along `g i`, for `(z, r)` near `(0, 0)`.
  have hψtr (i : ι) : ∀ᶠ z in 𝓝 (0 : E), ∀ᶠ r in 𝓝 (0 : ℝ), ψ (z + r • u i) = Φ i r (ψ z) := by
    have hcont : ContinuousAt (fun q : E × ℝ ↦ (P q.1, q.2, a + (q.1 - Lc (P q.1))))
        ((0 : E), (0 : ℝ)) :=
      ((P.continuous.comp continuous_fst).prodMk (continuous_snd.prodMk (continuous_const.add
        (continuous_fst.sub (Lc.continuous.comp (P.continuous.comp continuous_fst)))))).continuousAt
    have h0 : (P 0, (0 : ℝ), a + ((0 : E) - Lc (P 0))) = (0, 0, a) := by simp
    have h := (h0 ▸ hcont.tendsto).eventually (eventually_flowComp_add_smul_single Φ
      (fun j hji ↦ hcomm i j hji) (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ i)))
    rw [nhds_prod_eq] at h
    filter_upwards [h.curry] with z hz
    filter_upwards [hz] with r hr
    have hbase : z + r • u i - Lc (P (z + r • u i)) = z - Lc (P z) := by
      rw [hPu, map_add, map_smul, hLs]
      abel
    simp only [hψ]
    rw [hbase, hPu i z r]
    exact hr
  -- Hence the derivative of `ψ` sends `u i` to `g i ∘ ψ` near `0`.
  have hψu : ∀ᶠ z in 𝓝 (0 : E), ∀ i, fderiv ℝ ψ z (u i) = g i (ψ z) := by
    refine eventually_all.2 fun i ↦ ?_
    filter_upwards [hψtr i] with z hz
    have h₁ : HasDerivAt (fun r : ℝ ↦ ψ (z + r • u i)) (fderiv ℝ ψ z (u i)) 0 := by
      have hline : HasDerivAt (fun r : ℝ ↦ z + r • u i) (u i) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (u i)).const_add z
      have hdiff : HasFDerivAt ψ (fderiv ℝ ψ z) (z + (0 : ℝ) • u i) := by
        simpa using (hψs.differentiable hn0 z).hasFDerivAt
      exact hdiff.comp_hasDerivAt (0 : ℝ) hline
    have h₂ : HasDerivAt (fun r : ℝ ↦ ψ (z + r • u i)) (g i (ψ z)) 0 := by
      have h := hasDerivAt_flowOfLipschitz (hgK i) (ψ z) 0
      rw [Flow.map_zero_apply] at h
      exact h.congr_of_eventuallyEq (hz.mono fun r hr ↦ hr)
    exact h₁.unique h₂
  -- The derivative of `ψ` at `0` is the identity.
  have hD (h : E) : fderiv ℝ ψ 0 h = h := by
    have hk₀ : fderiv ℝ ψ 0 (h - Lc (P h)) = h - Lc (P h) := by
      set k := h - Lc (P h)
      have hPk : P k = 0 := by simp [k, hPL]
      have hline : (fun r : ℝ ↦ ψ (r • k)) = fun r ↦ a + r • k := by
        funext r
        simp [hψ, hPk, flowComp_zero]
      have h₁ : HasDerivAt (fun r : ℝ ↦ ψ (r • k)) (fderiv ℝ ψ 0 k) 0 := by
        have hdiff : HasFDerivAt ψ (fderiv ℝ ψ 0) ((0 : ℝ) • k) := by
          simpa using (hψs.differentiable hn0 0).hasFDerivAt
        simpa [Function.comp_def] using
          hdiff.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).smul_const k)
      have h₂ : HasDerivAt (fun r : ℝ ↦ ψ (r • k)) k 0 := by
        rw [hline]
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const k).const_add a
      exact h₁.unique h₂
    have hu₀ (i : ι) : fderiv ℝ ψ 0 (u i) = u i := by
      rw [hψu.self_of_nhds i, hψ0, hSg a haS i]
    calc fderiv ℝ ψ 0 h = fderiv ℝ ψ 0 (h - Lc (P h)) + fderiv ℝ ψ 0 (Lc (P h)) := by
          rw [← map_add, sub_add_cancel]
      _ = h - Lc (P h) + Lc (P h) := by
          rw [hk₀, hLc, map_sum]
          simp only [map_smul, hu₀]
      _ = h := sub_add_cancel _ _
  -- Invert `ψ` near `0`, on an open set where the identities hold and `ψ` lands in `S`.
  obtain ⟨U, hU, hUo, h0U⟩ := eventually_nhds_iff.1 hψu
  obtain ⟨Θ, hΘ, h0Θ, -, hΘs, hΘw⟩ :=
    ContDiffOn.exists_openPartialHomeomorph_fderiv_symm_apply_eq hψs.contDiffOn
      (hUo.inter (hSo.preimage hψs.continuous)) ⟨h0U, show ψ 0 ∈ S from hψ0 ▸ haS⟩
      (by exact_mod_cast hn) (e := ContinuousLinearEquiv.refl ℝ E)
      (by ext h; simp [hD]) (v := w) (u := u)
      fun z hz i ↦ by rw [hU z hz.1 i, hSg _ hz.2 i]
  refine ⟨Θ.symm, hψ0 ▸ hΘ ▸ Θ.map_source h0Θ,
    fun y hy ↦ hΘs.contDiffAt (Θ.open_target.mem_nhds hy), fun z _ ↦ ?_, fun y hy i ↦ ?_⟩
  · rw [OpenPartialHomeomorph.symm_symm, hΘ]
    exact hψs.contDiffAt
  · exact hΘw y hy i

end Commuting

end TauCeti
