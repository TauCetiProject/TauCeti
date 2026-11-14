/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod

/-!
# Holomorphy and the conjugate Wirtinger derivative

For a real-differentiable map between complex normed spaces, vanishing of the conjugate
Wirtinger derivative characterizes complex differentiability. The real-differentiability
hypothesis is essential because the totalized real derivative vanishes at nondifferentiable
points. In one variable the real differential has coefficients `wirtingerDeriv f x 1` and
`conjWirtingerDeriv f x 1` in the basis `dz`, `dbar z`; testing the latter coefficient alone
detects its vanishing.

On the coordinate space `ι → ℂ` the conjugate Wirtinger derivative is conjugate-linear, so it
vanishes as soon as it vanishes on the coordinate vectors: a real-differentiable map is holomorphic
exactly when all its partial derivatives `∂g/∂(conj z_j)` vanish
(`TauCeti.differentiableAt_iff_forall_conjWirtingerDeriv_apply_single_eq_zero`).

Adding a holomorphic function does not change the conjugate Wirtinger derivative, so a function
that is locally a `Cⁿ` function plus a holomorphic one is `Cⁿ` with the same conjugate Wirtinger
derivatives (`TauCeti.contDiffOn_and_conjWirtingerDeriv_eq_of_locally_eq_add`). This glues the
local solutions in exhaustion proofs of the `\bar∂`-lemma.

For a jointly sufficiently smooth family `H : P → V → W` over an open set `s ×ˢ U` whose slices
`H p` are holomorphic on `U`, symmetry of mixed second derivatives implies that every parameter
Fréchet derivative `z ↦ fderiv ℝ (fun q ↦ H q z) p` and, by induction, every iterated parameter
Fréchet derivative `z ↦ iteratedFDeriv ℝ k (fun q ↦ H q z) p` remains holomorphic on `U`
(`TauCeti.differentiableOn_fderiv_partial`, `TauCeti.differentiableOn_iteratedFDeriv_partial`).

These statements connect the real differential and its type decomposition with holomorphy.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, Chapter II.
-/

public noncomputable section

open Complex Filter Set Topology
open scoped ComplexConjugate ContDiff

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- A real-differentiable map between complex normed spaces is complex differentiable
exactly when its conjugate Wirtinger derivative vanishes. -/
theorem differentiableAt_iff_conjWirtingerDeriv_eq_zero {g : V → W} {x : V}
    (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℂ g x ↔ conjWirtingerDeriv g x = 0 := by
  constructor
  · exact fun h ↦ h.conjWirtingerDeriv_eq_zero
  · intro h
    apply (differentiableAt_iff_restrictScalars ℝ hg).mpr
    refine ⟨wirtingerDeriv g x, ?_⟩
    ext v
    simpa only [ContinuousLinearMap.coe_restrictScalars', h, zero_apply, add_zero] using
      wirtingerDeriv_add_conjWirtingerDeriv g x v

/-- For a real-differentiable function of one complex variable, the single equation
`conjWirtingerDeriv f x 1 = 0` characterizes complex differentiability. -/
theorem differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero {f : ℂ → W} {x : ℂ}
    (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℂ f x ↔ conjWirtingerDeriv f x 1 = 0 := by
  rw [differentiableAt_iff_conjWirtingerDeriv_eq_zero hf,
    conjWirtingerDeriv_eq_zero_iff_apply_one_eq_zero]

/-- On `ι → ℂ`, a real-differentiable map is complex differentiable exactly when its conjugate
Wirtinger derivatives `∂g/∂(conj z_j)` in the coordinate directions all vanish. -/
theorem differentiableAt_iff_forall_conjWirtingerDeriv_apply_single_eq_zero {ι : Type*}
    [Fintype ι] [DecidableEq ι] {g : (ι → ℂ) → W} {x : ι → ℂ} (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℂ g x ↔ ∀ j, conjWirtingerDeriv g x (Pi.single j 1) = 0 := by
  rw [differentiableAt_iff_conjWirtingerDeriv_eq_zero hg]
  refine ⟨fun h j ↦ by simp [h], fun h ↦ ContinuousLinearMap.ext fun v ↦ ?_⟩
  have hv : v = ∑ j, v j • Pi.single j (1 : ℂ) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    simp [← Pi.single_smul]
  rw [hv, map_sum]
  simp [h]

/-- **Gluing modulo holomorphic functions.** If near each point of `U` the function `G` is a
`Cⁿ` function `a`, `n ≥ 1`, plus a holomorphic `Cⁿ` function, and the conjugate Wirtinger
derivatives of `a` in the directions `v j` are `f j`, then `G` is `Cⁿ` on `U` with the same
conjugate Wirtinger derivatives. -/
theorem contDiffOn_and_conjWirtingerDeriv_eq_of_locally_eq_add {ι : Type*} {n : WithTop ℕ∞}
    {G : V → W} {v : ι → V} {f : ι → V → W} {U : Set V} (hn : 1 ≤ n)
    (hG : ∀ z ∈ U, ∃ O : Set V, IsOpen O ∧ z ∈ O ∧ ∃ a K : V → W, ContDiffOn ℝ n a O ∧
      (∀ w ∈ O, ∀ j, conjWirtingerDeriv a w (v j) = f j w) ∧ ContDiffOn ℂ n K O ∧
        EqOn G (a + K) O) :
    ContDiffOn ℝ n G U ∧ ∀ z ∈ U, ∀ j, conjWirtingerDeriv G z (v j) = f j z := by
  refine ⟨contDiffOn_of_locally_contDiffOn fun z hz ↦ ?_, fun z hz j ↦ ?_⟩
  · obtain ⟨O, hO, hzO, a, K, ha, -, hK, hGK⟩ := hG z hz
    exact ⟨O, hO, hzO, ((ha.add (hK.restrict_scalars ℝ)).congr hGK).mono inter_subset_right⟩
  · obtain ⟨O, hO, hzO, a, K, ha, haf, hK, hGK⟩ := hG z hz
    have hn0 : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
    have hKz := (hK.contDiffAt (hO.mem_nhds hzO)).differentiableAt hn0
    rw [(hGK.eventuallyEq_of_mem (hO.mem_nhds hzO)).conjWirtingerDeriv_eq,
      conjWirtingerDeriv_add ((ha.contDiffAt (hO.mem_nhds hzO)).differentiableAt hn0)
        (hKz.restrictScalars ℝ), add_apply, hKz.conjWirtingerDeriv_eq_zero, zero_apply,
      add_zero, haf z hzO j]

end TauCeti

section ParameterDerivatives

universe u v

namespace TauCeti

/-- **Parameter Fréchet derivatives preserve spatial holomorphy (first order).** If `H : P → V → W`
is jointly `C²` over `ℝ` on `s ×ˢ U`, for open sets `s ⊆ P` and `U ⊆ V`, and `H p` is holomorphic
on `U` for every `p ∈ s`, then `z ↦ fderiv ℝ (fun q ↦ H q z) p` is holomorphic on `U` for every
`p ∈ s`. -/
theorem differentiableOn_fderiv_partial {P V W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    {H : P → V → W} {s : Set P} {U : Set V} (hs : IsOpen s) (hU : IsOpen U)
    (hH : ContDiffOn ℝ 2 ↿H (s ×ˢ U)) (hHol : ∀ p ∈ s, DifferentiableOn ℂ (H p) U)
    {p : P} (hp : p ∈ s) :
    DifferentiableOn ℂ (fun z ↦ fderiv ℝ (fun q ↦ H q z) p) U := by
  intro z₀ hz₀
  refine DifferentiableAt.differentiableWithinAt ?_
  set ψ : V → P →L[ℝ] W := fun z ↦ fderiv ℝ (fun q ↦ H q z) p
  have hHat : ContDiffAt ℝ 2 ↿H (p, z₀) := hH.contDiffAt ((hs.prod hU).mem_nhds ⟨hp, hz₀⟩)
  have hD2 : DifferentiableAt ℝ (fderiv ℝ ↿H) (p, z₀) :=
    (hHat.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  let R : (P × V →L[ℝ] W) →L[ℝ] P →L[ℝ] W :=
    (ContinuousLinearMap.compL ℝ P (P × V) W).flip (ContinuousLinearMap.inl ℝ P V)
  have hψeq : ψ =ᶠ[𝓝 z₀] fun z ↦ R (fderiv ℝ ↿H (p, z)) := by
    filter_upwards [hU.mem_nhds hz₀] with z hz
    exact fderiv_slice_left
      ((hH.differentiableOn (by norm_num)).differentiableAt ((hs.prod hU).mem_nhds ⟨hp, hz⟩))
  have hψ : HasFDerivAt ψ
      (R.comp ((fderiv ℝ (fderiv ℝ ↿H) (p, z₀)).comp (ContinuousLinearMap.inr ℝ P V))) z₀ :=
    (R.hasFDerivAt.comp z₀ (hD2.hasFDerivAt.comp z₀
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) p z₀))).congr_of_eventuallyEq hψeq
  have hθ (w' : V) : HasFDerivAt (fun q ↦ fderiv ℝ ↿H (q, z₀) (0, w'))
      ((ContinuousLinearMap.apply ℝ W (0, w')).comp
        ((fderiv ℝ (fderiv ℝ ↿H) (p, z₀)).comp (ContinuousLinearMap.inl ℝ P V))) p := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
      (ContinuousLinearMap.apply ℝ W (0, w')).hasFDerivAt.comp p
        (hD2.hasFDerivAt.comp p (hasFDerivAt_prodMk_left (𝕜 := ℝ) p z₀))
  have hmixed (w : V) (u : P) :
      fderiv ℝ ψ z₀ w u = fderiv ℝ (fun q ↦ fderiv ℝ ↿H (q, z₀) (0, w)) p u := by
    rw [hψ.fderiv, (hθ w).fderiv]
    simpa [R] using (hHat.isSymmSndFDerivAt (by simp)).eq (0, w) (u, 0)
  rw [differentiableAt_iff_conjWirtingerDeriv_eq_zero hψ.differentiableAt]
  ext w u
  have hθeq : (fun q ↦ fderiv ℝ ↿H (q, z₀) (0, I • w)) =ᶠ[𝓝 p]
      (I • fun q ↦ fderiv ℝ ↿H (q, z₀) (0, w)) := by
    filter_upwards [hs.mem_nhds hp] with q hq
    have hqH : DifferentiableAt ℝ ↿H (q, z₀) :=
      (hH.differentiableOn (by norm_num)).differentiableAt ((hs.prod hU).mem_nhds ⟨hq, hz₀⟩)
    have hqC : DifferentiableAt ℂ (H q) z₀ := (hHol q hq z₀ hz₀).differentiableAt (hU.mem_nhds hz₀)
    have hunc : (fun y ↦ ↿H (q, y)) = H q := rfl
    have hsr (w' : V) : fderiv ℝ (H q) z₀ w' = fderiv ℝ ↿H (q, z₀) (0, w') := by
      simpa [hunc] using congrArg (· w') (fderiv_slice_right hqH)
    simp only [Pi.smul_apply, ← hsr (I • w), ← hsr w, hqC.fderiv_restrictScalars ℝ,
      ContinuousLinearMap.coe_restrictScalars', map_smul]
  have hI : fderiv ℝ ψ z₀ (I • w) u = I • fderiv ℝ ψ z₀ w u := by
    rw [hmixed (I • w) u, hmixed w u, hθeq.fderiv_eq, ((hθ w).const_smul I).fderiv, (hθ w).fderiv]
    rfl
  simp only [conjWirtingerDeriv_apply, zero_apply, add_apply, smul_apply, hI, smul_smul, I_mul_I,
    neg_one_smul, add_neg_cancel, smul_zero]

private def curryFin0SymmCLM (P W : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup W] [NormedSpace ℂ W] :
    W →L[ℂ] ContinuousMultilinearMap ℝ (fun _ : Fin 0 ↦ P) W :=
  LinearMap.mkContinuous
    { toFun := (continuousMultilinearCurryFin0 ℝ P W).symm
      map_add' := map_add _
      map_smul' c x := by ext m; simp }
    1 fun x ↦ by simp

private def curryRightSymmCLM (P W : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (k : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ P) (P →L[ℝ] W) →L[ℂ]
      ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) ↦ P) W :=
  LinearMap.mkContinuous
    { toFun := (continuousMultilinearCurryRightEquiv' ℝ k P W).symm
      map_add' := map_add _
      map_smul' c Φ := by ext m; simp }
    1 fun Φ ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      exact le_of_eq ((continuousMultilinearCurryRightEquiv' ℝ k P W).symm.norm_map Φ)

private theorem differentiableOn_iteratedFDeriv_partial_aux {P : Type u} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {W : Type (max u v)} [NormedAddCommGroup W] [NormedSpace ℂ W] (k : ℕ)
    {s : Set P} {U : Set V} (hs : IsOpen s) (hU : IsOpen U) {p : P} (hp : p ∈ s)
    {H : P → V → W} (hH : ContDiffOn ℝ (k + 1 : ℕ) ↿H (s ×ˢ U))
    (hHol : ∀ p ∈ s, DifferentiableOn ℂ (H p) U) :
    DifferentiableOn ℂ (fun z ↦ iteratedFDeriv ℝ k (fun q ↦ H q z) p) U := by
  induction k generalizing W with
  | zero =>
    refine ((curryFin0SymmCLM P W).differentiable.comp_differentiableOn (hHol p hp)).congr
      fun z _ ↦ ?_
    ext _
    simp [curryFin0SymmCLM]
  | succ k ih =>
    let H' : P → V → P →L[ℝ] W := fun q z ↦ fderiv ℝ (fun r ↦ H r z) q
    have hk' : (((k + 1 : ℕ) : WithTop ℕ∞) + 1) ≤ ((k + 1 + 1 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast le_rfl
    have hH' : ContDiffOn ℝ (k + 1 : ℕ) ↿H' (s ×ˢ U) :=
      (hH.of_le hk').fderiv_partial_of_isOpen (hs.prod hU)
    have h2_nat : 2 ≤ k + 1 + 1 := by omega
    have h2 : (2 : WithTop ℕ∞) ≤ ((k + 1 + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast h2_nat
    have hHol' : ∀ q ∈ s, DifferentiableOn ℂ (H' q) U := fun q hq ↦
      differentiableOn_fderiv_partial hs hU (hH.of_le h2) hHol hq
    refine (Differentiable.comp_differentiableOn (F := P [×k]→L[ℝ] P →L[ℝ] W)
      (curryRightSymmCLM P W k).differentiable (ih hH' hHol')).congr fun z _ ↦ ?_
    simp [H', curryRightSymmCLM, iteratedFDeriv_succ_eq_comp_right]

/-- **Iterated parameter Fréchet derivatives preserve spatial holomorphy.** If `H : P → V → W` is
jointly `C^n` over `ℝ` on `s ×ˢ U`, for open sets `s ⊆ P` and `U ⊆ V`, with `(k + 1 : ℕ) ≤ n`
(in particular for `n = ∞` and every `k : ℕ`), and `H p` is holomorphic on `U` for every `p ∈ s`,
then `z ↦ iteratedFDeriv ℝ k (fun q ↦ H q z) p` is holomorphic on `U` for every `p ∈ s`. -/
theorem differentiableOn_iteratedFDeriv_partial {P : Type u} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {W : Type v} [NormedAddCommGroup W] [NormedSpace ℂ W] (k : ℕ)
    {n : WithTop ℕ∞} {H : P → V → W} {s : Set P} {U : Set V}
    (hs : IsOpen s) (hU : IsOpen U) (hk : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ n)
    (hH : ContDiffOn ℝ n ↿H (s ×ˢ U)) (hHol : ∀ p ∈ s, DifferentiableOn ℂ (H p) U)
    {p : P} (hp : p ∈ s) :
    DifferentiableOn ℂ (fun z ↦ iteratedFDeriv ℝ k (fun q ↦ H q z) p) U := by
  let eW : Type (max u v) := ULift.{u} W
  let isoW : eW ≃L[ℂ] W := ContinuousLinearEquiv.ulift
  let L_ℝ : eW →L[ℝ] W := isoW.toContinuousLinearMap.restrictScalars ℝ
  let M_ℂ : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ P) eW →L[ℂ]
      ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ P) W :=
    LinearMap.mkContinuous
      { toFun Φ := L_ℝ.compContinuousMultilinearMap Φ
        map_add' Φ Ψ := by ext m; simp
        map_smul' c Φ := by ext m; simp [L_ℝ] }
      ‖L_ℝ‖ fun Φ ↦ L_ℝ.norm_compContinuousMultilinearMap_le Φ
  have hH' : ContDiffOn ℝ (k + 1 : ℕ) ↿(fun q z ↦ isoW.symm (H q z)) (s ×ˢ U) :=
    (isoW.symm.contDiff.restrict_scalars ℝ).comp_contDiffOn (hH.of_le hk)
  have hHol' : ∀ q ∈ s, DifferentiableOn ℂ (fun z ↦ isoW.symm (H q z)) U :=
    fun q hq ↦ isoW.symm.differentiable.comp_differentiableOn (hHol q hq)
  refine (M_ℂ.differentiable.comp_differentiableOn
    (differentiableOn_iteratedFDeriv_partial_aux k hs hU hp hH' hHol')).congr fun z hz ↦ ?_
  have hk0 : (k : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast Nat.le_succ k
  have hkp : ContDiffAt ℝ k (fun q ↦ isoW.symm (H q z)) p :=
    ((hH'.of_le hk0).contDiffAt ((hs.prod hU).mem_nhds ⟨hp, hz⟩)).comp p
      (contDiffAt_id.prodMk contDiffAt_const)
  have hcomp : (isoW ∘ fun q ↦ isoW.symm (H q z)) = fun q ↦ H q z := by
    ext q; exact isoW.apply_symm_apply _
  simpa [M_ℂ, L_ℝ, hcomp] using L_ℝ.iteratedFDeriv_comp_left hkp le_rfl

end TauCeti

end ParameterDerivatives
