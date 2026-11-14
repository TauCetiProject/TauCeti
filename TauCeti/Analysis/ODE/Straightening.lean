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
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# The straightening theorem for vector fields on a normed space

Near a point where a `C^n` vector field `w` on a finite-dimensional real normed space `E` does not
vanish, some `C^n` change of coordinates carries `w` to a constant field. Precisely, there is an
open partial homeomorphism `φ` of `E`, `C^n` with `C^n` inverse, whose domain contains the point
`a` and whose derivative sends `w y` to `w a` at every point `y` of its domain
(`TauCeti.exists_openPartialHomeomorph_fderiv_eq_const`). This is the flow-box theorem: in the
coordinates `φ`, the integral curves of `w` become parallel straight lines traversed with constant
velocity `w a`.

More generally, finitely many fields `w i` with linearly independent values at `a` and pairwise
vanishing Lie brackets near `a` are straightened simultaneously: one `C^n` change of coordinates
`φ` sends every `w i y` to `w i a`
(`TauCeti.exists_openPartialHomeomorph_fderiv_eq_const_of_lieBracket_eventuallyEq_zero`); a
single nonvanishing field is the case of a one-element index set.

Cut each field off to a globally Lipschitz `C^n` field `g i` that agrees with `w i` near `a`, and
let `Φ i` be the global flow of `g i`, which is `C^n` jointly in the initial condition and time.
Choose continuous linear functionals `ℓ i` with `ℓ i (w j a) = δ i j` and compose the flows,

`ψ z = Φ i₁ (ℓ i₁ z) (⋯ (Φ iₖ (ℓ iₖ z) (a + (z - ∑ i, ℓ i z • w i a))))`.

The brackets of the `g i` vanish near `a`, so their flows commute for short times near `a`
(`TauCeti.eventually_flowOfLipschitz_comm_of_lieBracket_eventuallyEq_zero`). Each flow can
therefore be moved to the outside of the composite, so that `ψ (z + s • w i a) = Φ i s (ψ z)`, and
differentiating in `s` shows that `dψ z` sends `w i a` to `g i (ψ z)` for `z` near `0`. At `z = 0`
the derivative of `ψ` is the identity, so by the inverse function theorem with `C^n` inverse
(`ContDiffOn.exists_openPartialHomeomorph_fderiv_symm_apply_eq`) `ψ` is a local diffeomorphism
near `0` whose inverse sends each `g i` to `w i a`; restricted to where `g i = w i`, that inverse
is the required `φ`.

## Main results

* `TauCeti.exists_openPartialHomeomorph_fderiv_eq_const`: a nonvanishing `C^n` vector field is
  constant in suitable `C^n` local coordinates.
* `TauCeti.exists_openPartialHomeomorph_fderiv_eq_const_of_lieBracket_eventuallyEq_zero`:
  finitely many `C^n` vector fields with linearly independent values and vanishing brackets are
  simultaneously constant in suitable `C^n` local coordinates.

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

/-- A map whose translates along `u` follow the flow of `g` for short times, at `z`, has
derivative `g (ψ z)` in the direction `u` at `z`. -/
private theorem fderiv_apply_eq_of_eventually_add_smul_eq [CompleteSpace E] {g : E → E}
    {K : NNReal} (hg : LipschitzWith K g) {ψ : E → E} {z u : E} (hd : DifferentiableAt ℝ ψ z)
    (h : ∀ᶠ r in 𝓝 (0 : ℝ), ψ (z + r • u) = flowOfLipschitz g hg r (ψ z)) :
    fderiv ℝ ψ z u = g (ψ z) := by
  have hΦ := hasDerivAt_flowOfLipschitz hg (ψ z) 0
  rw [Flow.map_zero_apply] at hΦ
  rw [← hd.lineDeriv_eq_fderiv]
  exact HasLineDerivAt.lineDeriv (hΦ.congr_of_eventuallyEq h)

section FlowBox

variable {ι : Type*} [Fintype ι]

/-- The flow-box coordinates of a finite family of flows `Φ i` at `a`, along vectors `u i` with
dual coordinates `P`: flow for the times `P z` from the point `a + (z - ∑ i, P z i • u i)` of the
affine complement of the `u i` through `a`. -/
private def flowBox (Φ : ι → Flow ℝ E) (a : E) (u : ι → E) (P : E →L[ℝ] ι → ℝ) (z : E) : E :=
  flowComp Φ (Finset.univ : Finset ι).toList (P z) (a + (z - ∑ i, P z i • u i))

private theorem flowBox_of_apply_eq_zero (Φ : ι → Flow ℝ E) (a : E) (u : ι → E)
    {P : E →L[ℝ] ι → ℝ} {z : E} (hz : P z = 0) : flowBox Φ a u P z = a + z := by
  simp [flowBox, hz, flowComp_zero]

private theorem contDiff_flowBox {n : WithTop ℕ∞} (Φ : ι → Flow ℝ E)
    (hΦ : ∀ i, ContDiff ℝ n fun p : E × ℝ ↦ Φ i p.2 p.1) (a : E) (u : ι → E)
    (P : E →L[ℝ] ι → ℝ) : ContDiff ℝ n (flowBox Φ a u P) :=
  (contDiff_flowComp Φ hΦ _).comp (P.contDiff.prodMk (contDiff_const.add (contDiff_id.sub
    (ContDiff.sum fun i _ ↦ (contDiff_pi.1 P.contDiff i).smul contDiff_const))))

variable [DecidableEq ι] {Φ : ι → Flow ℝ E} {a : E} {u : ι → E} {P : E →L[ℝ] ι → ℝ}

/-- If `P` is dual to the `u i` and the flow of `i` commutes near `a` with the other flows, then
translating `z` along `u i` flows the flow-box coordinates along `Φ i`, for `(z, r)` near
`(0, 0)`. -/
private theorem eventually_flowBox_add_smul (hP : ∀ i, P (u i) = Pi.single i 1) {i : ι}
    (hcomm : ∀ j, j ≠ i → ∀ᶠ q : ℝ × ℝ × E in 𝓝 (0, 0, a),
      Φ j q.1 (Φ i q.2.1 q.2.2) = Φ i q.2.1 (Φ j q.1 q.2.2)) :
    ∀ᶠ z in 𝓝 (0 : E), ∀ᶠ r in 𝓝 (0 : ℝ),
      flowBox Φ a u P (z + r • u i) = Φ i r (flowBox Φ a u P z) := by
  have hcont : ContinuousAt (fun q : E × ℝ ↦ (P q.1, q.2, a + (q.1 - ∑ j, P q.1 j • u j)))
      ((0 : E), (0 : ℝ)) :=
    ((P.continuous.comp continuous_fst).prodMk (continuous_snd.prodMk (continuous_const.add
      (continuous_fst.sub (continuous_finsetSum _ fun j _ ↦
        ((continuous_apply j).comp (P.continuous.comp continuous_fst)).smul
          continuous_const))))).continuousAt
  have h0 : (P 0, (0 : ℝ), a + ((0 : E) - ∑ j, P 0 j • u j)) = (0, 0, a) := by simp
  have h := (h0 ▸ hcont.tendsto).eventually (eventually_flowComp_add_smul_single Φ hcomm
    (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ i)))
  rw [nhds_prod_eq] at h
  filter_upwards [h.curry] with z hz
  filter_upwards [hz] with r hr
  have hPu : P (z + r • u i) = P z + r • Pi.single i 1 := by rw [map_add, map_smul, hP]
  have hbase :
      z + r • u i - ∑ j, (P z + r • Pi.single i 1 : ι → ℝ) j • u j = z - ∑ j, P z j • u j := by
    simp only [Pi.add_apply, Pi.smul_apply, add_smul, Finset.sum_add_distrib, smul_eq_mul,
      Pi.single_apply, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    abel
  simp only [flowBox]
  rw [hPu, hbase]
  exact hr

/-- If `P` is dual to the `u i`, and the derivative of the flow-box coordinates at `0` fixes
each `u i`, then it is the identity. -/
private theorem fderiv_flowBox_zero (hP : ∀ i, P (u i) = Pi.single i 1)
    (hd : DifferentiableAt ℝ (flowBox Φ a u P) 0)
    (hu : ∀ i, fderiv ℝ (flowBox Φ a u P) 0 (u i) = u i) :
    fderiv ℝ (flowBox Φ a u P) 0 = ContinuousLinearMap.id ℝ E := by
  ext h
  -- Split `h` into its part `k` in the kernel of `P`, where the coordinates are a translation,
  -- and a combination of the `u i`.
  set k := h - ∑ i, P h i • u i
  have hPk : P k = 0 := by
    ext j
    simp [k, hP, Pi.single_apply]
  have hk : fderiv ℝ (flowBox Φ a u P) 0 k = k := by
    have hline : HasLineDerivAt ℝ (flowBox Φ a u P) k 0 k := by
      have h' : HasDerivAt (fun r : ℝ ↦ a + r • k) k 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const k).const_add a
      refine h'.congr_of_eventuallyEq (Eventually.of_forall fun r ↦ ?_)
      dsimp only
      rw [zero_add, flowBox_of_apply_eq_zero Φ a u (by rw [map_smul, hPk, smul_zero])]
    rw [← hd.lineDeriv_eq_fderiv, hline.lineDeriv]
  rw [ContinuousLinearMap.id_apply]
  calc fderiv ℝ (flowBox Φ a u P) 0 h = fderiv ℝ (flowBox Φ a u P) 0 (k + ∑ i, P h i • u i) := by
        simp only [k, sub_add_cancel]
    _ = h := by
        rw [map_add, map_sum, hk]
        simp only [map_smul, hu, k, sub_add_cancel]

end FlowBox

variable [FiniteDimensional ℝ E]

section Commuting

variable {ι : Type*}

/-- **The canonical form for commuting vector fields** (simultaneous flow-box theorem). Let
`w i` be `C^n` vector fields, `1 ≤ n`, defined near a point `a` of a finite-dimensional real
normed space, with linearly independent values `w i a` (so the index type is finite), and whose
pairwise Lie brackets vanish near `a`. Then the fields are simultaneously constant in suitable
`C^n` coordinates: there is an open partial homeomorphism `φ`, `C^n` on its source with `C^n`
inverse on its target, such that `a ∈ φ.source` and `dφ_y (w i y) = w i a` for every
`y ∈ φ.source` and every `i`. -/
theorem exists_openPartialHomeomorph_fderiv_eq_const_of_lieBracket_eventuallyEq_zero {n : ℕ∞}
    (hn : 1 ≤ n) {w : ι → E → E} {s : Set E} {a : E} (hw : ∀ i, ContDiffOn ℝ n (w i) s)
    (hs : s ∈ 𝓝 a)
    (hli : LinearIndependent ℝ fun i ↦ w i a)
    (hbr : Pairwise fun i j ↦ VectorField.lieBracket ℝ (w i) (w j) =ᶠ[𝓝 a] 0) :
    ∃ φ : OpenPartialHomeomorph E E, a ∈ φ.source ∧ (∀ y ∈ φ.source, ContDiffAt ℝ n φ y) ∧
      (∀ z ∈ φ.target, ContDiffAt ℝ n φ.symm z) ∧
        ∀ y ∈ φ.source, ∀ i, fderiv ℝ φ y (w i y) = w i a := by
  -- Cut the fields off to globally Lipschitz fields `g i`, whose flows `Φ i` commute near `a`.
  -- With functionals `P` dual to the vectors `u i = w i a`, the flow-box coordinates `ψ`
  -- satisfy `dψ_z (u i) = g i (ψ z)` near `0` and `dψ_0 = id`; their local inverse is the
  -- required chart.
  classical
  have := hli.finite
  have := Fintype.ofFinite ι
  let _ : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
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
    eventually_flowOfLipschitz_comm_of_lieBracket_eventuallyEq_zero (hgK j) (hg1 j) (hgK i)
      (.of_forall ((hg i).differentiable (by simp)))
      (((hgw j).lieBracket_vectorField (hgw i)).trans (hbr hji))
  -- Functionals `P` dual to the `u i`, and the flow-box coordinates `ψ`.
  obtain ⟨P₀, hP₀⟩ := (Fintype.linearCombination ℝ u).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hli.fintypeLinearCombination_injective)
  set P : E →L[ℝ] (ι → ℝ) := LinearMap.toContinuousLinearMap P₀
  have hP (i : ι) : P (u i) = Pi.single i 1 := by
    have h := LinearMap.congr_fun hP₀ (Pi.single i 1)
    rwa [LinearMap.comp_apply, Fintype.linearCombination_apply_single, one_smul] at h
  set ψ := flowBox Φ a u P
  have hψs : ContDiff ℝ n ψ := contDiff_flowBox Φ hΦs a u P
  have hψ0 : ψ 0 = a := by simpa using flowBox_of_apply_eq_zero Φ a u (P := P) (map_zero P)
  -- The derivative of `ψ` sends `u i` to `g i ∘ ψ` near `0`, and is the identity at `0`.
  have hψu : ∀ᶠ z in 𝓝 (0 : E), ∀ i, fderiv ℝ ψ z (u i) = g i (ψ z) :=
    eventually_all.2 fun i ↦ (eventually_flowBox_add_smul hP (hcomm i)).mono fun z hz ↦
      fderiv_apply_eq_of_eventually_add_smul_eq (hgK i) (hψs.differentiable hn0 z) hz
  have hD : fderiv ℝ ψ 0 = ContinuousLinearMap.id ℝ E :=
    fderiv_flowBox_zero hP (hψs.differentiable hn0 0) fun i ↦ by
      rw [hψu.self_of_nhds i, hψ0, hSg a haS i]
  -- Invert `ψ` near `0`, on an open set where the identities hold and `ψ` lands in `S`.
  obtain ⟨U, hU, hUo, h0U⟩ := eventually_nhds_iff.1 hψu
  obtain ⟨Θ, hΘ, h0Θ, -, hΘs, hΘw⟩ :=
    ContDiffOn.exists_openPartialHomeomorph_fderiv_symm_apply_eq hψs.contDiffOn
      (hUo.inter (hSo.preimage hψs.continuous)) ⟨h0U, mem_preimage.2 (by rwa [hψ0])⟩
      (by exact_mod_cast hn) (e := ContinuousLinearEquiv.refl ℝ E)
      (by rw [ContinuousLinearEquiv.coe_refl, hD]) (v := w) (u := u)
      fun z hz i ↦ by rw [hU z hz.1 i, hSg _ hz.2 i]
  refine ⟨Θ.symm, hψ0 ▸ hΘ ▸ Θ.map_source h0Θ,
    fun y hy ↦ hΘs.contDiffAt (Θ.open_target.mem_nhds hy), fun z _ ↦ ?_, fun y hy i ↦ ?_⟩
  · rw [OpenPartialHomeomorph.symm_symm, hΘ]
    exact hψs.contDiffAt
  · exact hΘw y hy i

end Commuting

/-- **The straightening theorem** (flow-box theorem). A `C^n` vector field `w`, `1 ≤ n`, defined
near a point `a` of a finite-dimensional real normed space, with `w a ≠ 0`, is constant in suitable
`C^n` coordinates: there is an open partial homeomorphism `φ`, `C^n` on its source with `C^n`
inverse on its target, such that `a ∈ φ.source` and `dφ_y (w y) = w a` for every `y ∈ φ.source`.
This is the case of a single field in
`TauCeti.exists_openPartialHomeomorph_fderiv_eq_const_of_lieBracket_eventuallyEq_zero`. -/
theorem exists_openPartialHomeomorph_fderiv_eq_const {n : ℕ∞} (hn : 1 ≤ n) {w : E → E}
    {s : Set E} {a : E} (hw : ContDiffOn ℝ n w s) (hs : s ∈ 𝓝 a) (ha : w a ≠ 0) :
    ∃ φ : OpenPartialHomeomorph E E, a ∈ φ.source ∧ (∀ y ∈ φ.source, ContDiffAt ℝ n φ y) ∧
      (∀ z ∈ φ.target, ContDiffAt ℝ n φ.symm z) ∧ ∀ y ∈ φ.source, fderiv ℝ φ y (w y) = w a := by
  obtain ⟨φ, haφ, hφ, hφs, hφw⟩ :=
    exists_openPartialHomeomorph_fderiv_eq_const_of_lieBracket_eventuallyEq_zero hn
      (w := fun _ : Unit ↦ w)
      (fun _ ↦ hw) hs (linearIndependent_unique_iff.2 ha)
      fun i j h ↦ (h (Subsingleton.elim i j)).elim
  exact ⟨φ, haφ, hφ, hφs, fun y hy ↦ hφw y hy ()⟩

end TauCeti
