/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Distribution.Distribution
public import TauCeti.Analysis.Distribution.TestFunction.Translation
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Analysis.Calculus.ContDiff.Convolution
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.Distribution.Order
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Topology.Algebra.Monoid
import TauCeti.Topology.Algebra.Support

/-!
# Regularization of distributions

For a distribution `T` on an open set `Ω` and a test function `ρ`, the **regularization**
`T.translatePairing ρ` is the function `x ↦ T (ρ (· - x))`, defined at every `x` for which the
translate `ρ (· - x)` is supported in `Ω`; it is the convolution of `T` with the reflection
`ρ (- ·)` of `ρ`. This file shows that it is smooth on the open set of such `x`, with derivatives
given by the distributional derivatives of `T`:

`∂_v (x ↦ T (ρ (· - x))) = x ↦ (∂_v T) (ρ (· - x))`.

Consequently, if every distributional derivative of `T` vanishes, the regularization is constant
on each preconnected open set of admissible translations. This is the regularization step in the
classical proof that a distribution whose derivatives all vanish on a connected open set is a
constant multiple of Lebesgue measure. The admissible translations form an open set by
`IsCompact.isOpen_setOf_mapsTo_add`, since `ρ` has compact support.

Integrating the regularization against an integrable compactly supported function `f` gives `T`
applied to the convolution `f ⋆ ρ`, so regularizations recover `T` as the kernel `ρ` shrinks. This
commutes `T` with an integral of test functions. On tests supported in a fixed compact set, `T` is
bounded by finitely many derivatives, hence by the sup norm of a jet with values in a Banach space;
by Hahn–Banach each scalar functional of `T` extends continuously to that space, where it commutes
with the Bochner integral.

Differentiability rests on the finite order of a distribution on each compact set,
`Distribution.exists_norm_apply_le` from `TauCeti.Analysis.Distribution.Order`: the first-order
Taylor remainder of `x ↦ ρ (· - x)` is supported in a fixed compact set and all of its
derivatives are `o(‖h‖)` uniformly, so its image under `T` is `o(‖h‖)` as well.

## Main declarations

* `Distribution.translatePairing`: the regularization `x ↦ T (ρ (· - x))`.
* `Distribution.fderiv_translatePairing_apply`: the derivative identity.
* `Distribution.contDiffOn_translatePairing`: the regularization is smooth.
* `Distribution.translatePairing_eq_of_lineDerivOp_eq_zero`: if all derivatives of `T` vanish,
  the regularization is constant on preconnected open sets of admissible translations.
* `Distribution.apply_eq_integral_smul_translatePairing`: pairing the regularization with an
  integrable compactly supported `f` is `T` applied to the convolution `f ⋆ ρ`,
  `T (f ⋆ ρ) = ∫ f y • T (ρ (· - y)) dy`.

## References

* [L. Hörmander, *The Analysis of Linear Partial Differential Operators I*][hormander2003],
  §2.1 for the local order estimate and Theorem 4.1.1 for the smoothness of regularizations and
  their derivatives.
-/

public section

noncomputable section

open Set Filter Topology TopologicalSpace TestFunction LineDeriv Metric
open scoped Distributions ContDiff

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω V : Opens E}

/-- The translate `ρ (· - x)` of a test function, as a test function on `Ω` when it is supported
there. -/
private def translateOfMapsTo (ρ : 𝓓(V, ℝ)) {x : E} (h : MapsTo (· + x) (tsupport ρ) Ω) :
    𝓓(Ω, ℝ) :=
  TauCeti.translateTestFunction
    (V := ⟨(· + x) ⁻¹' Ω, Ω.isOpen.preimage (continuous_add_const x)⟩) (mapsTo_preimage _ _)
    ⟨ρ, ρ.contDiff, ρ.hasCompactSupport, h⟩

private theorem translateOfMapsTo_apply (ρ : 𝓓(V, ℝ)) {x : E}
    (h : MapsTo (· + x) (tsupport ρ) Ω) (y : E) : translateOfMapsTo ρ h y = ρ (y - x) := by
  rw [translateOfMapsTo, TauCeti.translateTestFunction_apply]
  exact congrFun coe_mk (y - x)

/-- The regularization of a distribution `T` by a test function `ρ`: the function
`x ↦ T (ρ (· - x))`. Its value at `x` is `T` applied to the translate of `ρ` by `x` when this
translate is supported in `Ω`, and `0` otherwise. It is the convolution of `T` with the
reflection `ρ (- ·)` of `ρ`. -/
def translatePairing (T : 𝓓'(Ω, F)) (ρ : 𝓓(V, ℝ)) (x : E) : F :=
  open Classical in
  if h : MapsTo (· + x) (tsupport ρ) Ω then T (translateOfMapsTo ρ h) else 0

/-- The regularization at `x` is `T` applied to any test function on `Ω` which is the translate
of `ρ` by `x`. -/
theorem translatePairing_eq (T : 𝓓'(Ω, F)) {ρ : 𝓓(V, ℝ)} {x : E} {φ : 𝓓(Ω, ℝ)}
    (hφ : ∀ y, φ y = ρ (y - x)) : T.translatePairing ρ x = T φ := by
  have h : MapsTo (· + x) (tsupport ρ) Ω := by
    intro z hz
    apply φ.tsupport_subset
    rw [show (φ : E → ℝ) = fun y => ρ (y - x) from funext hφ, TauCeti.tsupport_comp_sub_right]
    simpa using hz
  simp only [translatePairing, h, ↓reduceDIte]
  congr 1
  ext y
  rw [translateOfMapsTo_apply, hφ]

/-- The regularization vanishes where the translate of `ρ` is not supported in `Ω`. -/
theorem translatePairing_eq_zero_of_not_mapsTo (T : 𝓓'(Ω, F)) {ρ : 𝓓(V, ℝ)} {x : E}
    (h : ¬MapsTo (· + x) (tsupport ρ) Ω) : T.translatePairing ρ x = 0 := by
  simp [translatePairing, h]

/-- The regularization of the zero distribution vanishes. -/
@[simp]
theorem translatePairing_zero (ρ : 𝓓(V, ℝ)) :
    (0 : 𝓓'(Ω, F)).translatePairing ρ = 0 := by
  ext x
  simp [translatePairing]

/-- Regularization is additive in the distribution. -/
@[simp]
theorem translatePairing_add (T S : 𝓓'(Ω, F)) (ρ : 𝓓(V, ℝ)) :
    (T + S).translatePairing ρ = T.translatePairing ρ + S.translatePairing ρ := by
  ext x
  by_cases h : MapsTo (· + x) (tsupport ρ) Ω <;> simp [translatePairing, h]

/-- Regularization commutes with scalar multiplication of the distribution. -/
@[simp]
theorem translatePairing_smul {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass ℝ M F]
    [ContinuousConstSMul M F] (c : M) (T : 𝓓'(Ω, F)) (ρ : 𝓓(V, ℝ)) :
    (c • T).translatePairing ρ = c • T.translatePairing ρ := by
  ext x
  by_cases h : MapsTo (· + x) (tsupport ρ) Ω <;> simp [translatePairing, h]

/-- The translate `ρ (· - x)` has the translated topological support. -/
private theorem tsupport_translateOfMapsTo (ρ : 𝓓(V, ℝ)) {x : E}
    (h : MapsTo (· + x) (tsupport ρ) Ω) :
    tsupport (translateOfMapsTo ρ h) = (· - x) ⁻¹' tsupport ρ := by
  rw [show (translateOfMapsTo ρ h : E → ℝ) = fun y => ρ (y - x) from
    funext (translateOfMapsTo_apply ρ h), TauCeti.tsupport_comp_sub_right]

/-- Around an admissible translation `x`, a closed thickening of the support of `ρ (· - x)`
still lies in `Ω`, so all nearby translations are admissible. -/
private theorem exists_cthickening_tsupport_translateOfMapsTo_subset (ρ : 𝓓(V, ℝ)) {x : E}
    (hx : MapsTo (· + x) (tsupport ρ) Ω) :
    ∃ δ > 0, cthickening δ (tsupport (translateOfMapsTo ρ hx)) ⊆ Ω ∧
      ∀ h : E, ‖h‖ ≤ δ → MapsTo (· + (x + h)) (tsupport ρ) Ω := by
  obtain ⟨δ, hδ, hδΩ⟩ := (translateOfMapsTo ρ hx).hasCompactSupport.isCompact
    |>.exists_cthickening_subset_open Ω.isOpen (translateOfMapsTo ρ hx).tsupport_subset
  refine ⟨δ, hδ, hδΩ, fun h hh z hz => hδΩ ?_⟩
  refine mem_cthickening_of_dist_le _ (z + x) δ _ ?_ ?_
  · rw [tsupport_translateOfMapsTo]
    simpa using hz
  · simpa [dist_eq_norm, ← add_assoc] using hh

/-- The first-order Taylor remainder of the regularization at `x` in the direction `h` is `T`
applied to the first-order Taylor remainder of the translates of `ρ`. -/
private theorem translatePairing_add_sub_sub_eq (T : 𝓓'(Ω, F)) (ρ : 𝓓(V, ℝ)) {x h : E}
    (hx : MapsTo (· + x) (tsupport ρ) Ω) (hxh : MapsTo (· + (x + h)) (tsupport ρ) Ω) :
    T.translatePairing ρ (x + h) - T.translatePairing ρ x - (∂_{h} T).translatePairing ρ x =
      T (translateOfMapsTo ρ hxh - translateOfMapsTo ρ hx + ∂_{h} (translateOfMapsTo ρ hx)) := by
  rw [translatePairing_eq T (translateOfMapsTo_apply ρ hxh),
    translatePairing_eq T (translateOfMapsTo_apply ρ hx),
    translatePairing_eq _ (translateOfMapsTo_apply ρ hx), lineDerivOp_apply_apply]
  simp [sub_eq_add_neg]

variable [FiniteDimensional ℝ E]

/-- The regularization is differentiable at every admissible translation, with derivative given
by the regularizations of the distributional derivatives of `T`. -/
private theorem exists_hasFDerivAt_translatePairing (T : 𝓓'(Ω, F)) (ρ : 𝓓(V, ℝ)) {x : E}
    (hx : MapsTo (· + x) (tsupport ρ) Ω) :
    ∃ L : E →L[ℝ] F, HasFDerivAt (T.translatePairing ρ) L x ∧
      ∀ v, L v = (∂_{v} T).translatePairing ρ x := by
  let L : E →L[ℝ] F := LinearMap.toContinuousLinearMap
    { toFun := fun v => (∂_{v} T).translatePairing ρ x
      map_add' := fun v w => by simp [lineDerivOp_left_add]
      map_smul' := fun c v => by simp [lineDerivOp_left_smul] }
  refine ⟨L, ?_, fun v => rfl⟩
  -- The translate of `ρ` by `x` and a compact neighbourhood `K` of its support inside `Ω`.
  let φ₀ : 𝓓(Ω, ℝ) := translateOfMapsTo ρ hx
  have hφ₀ : ∀ y, φ₀ y = ρ (y - x) := translateOfMapsTo_apply ρ hx
  obtain ⟨δ, hδ, hδΩ, hδx⟩ := exists_cthickening_tsupport_translateOfMapsTo_subset ρ hx
  let K : Compacts E := ⟨cthickening δ (tsupport φ₀), φ₀.hasCompactSupport.isCompact.cthickening⟩
  obtain ⟨N, C, hC, hT⟩ := T.exists_norm_apply_le (K := K) hδΩ
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  -- Choose a radius on which all derivatives of order at most `N` of the Taylor remainder are
  -- bounded by `c / (C + 1) * ‖h‖`.
  have hε : 0 < c / (C + 1) := div_pos hc (by linarith)
  have hrem := fun i => φ₀.hasCompactSupport.exists_norm_iteratedFDeriv_sub_sub_add_fderiv_le
    φ₀.contDiff (n := ∞) (i := i) (by exact_mod_cast le_top) hε
  choose r hr hrem using hrem
  let r₀ := min δ ((Finset.range (N + 1)).inf' (by simp) r)
  have hr₀ : 0 < r₀ := lt_min hδ ((Finset.lt_inf'_iff _).2 fun i _ => hr i)
  filter_upwards [ball_mem_nhds (0 : E) hr₀] with h hh
  rw [mem_ball_zero_iff] at hh
  have hhδ : ‖h‖ ≤ δ := hh.le.trans (min_le_left _ _)
  -- The translate of `ρ` by `x + h`, and the Taylor remainder as a test function on `Ω`.
  let φh : 𝓓(Ω, ℝ) := translateOfMapsTo ρ (hδx h hhδ)
  let R : 𝓓(Ω, ℝ) := φh - φ₀ + ∂_{h} φ₀
  have hR : (R : E → ℝ) = fun y => φ₀ (y - h) - φ₀ y + fderiv ℝ φ₀ y h := by
    ext y
    have hd := φ₀.contDiff.differentiable (by simp) y
    simp [R, φh, hφ₀, translateOfMapsTo_apply, hd.lineDeriv_eq_fderiv, sub_sub, add_comm h x]
  have hRK : tsupport R ⊆ K := by
    rw [hR]
    exact TauCeti.tsupport_sub_sub_add_fderiv_subset _ hhδ
  have hRbound : ∀ i ≤ N, ∀ y, ‖iteratedFDeriv ℝ i R y‖ ≤ c / (C + 1) * ‖h‖ := by
    intro i hi y
    have hri : ‖h‖ < r i := hh.trans_le ((min_le_right _ _).trans
      (Finset.inf'_le _ (Finset.mem_range.2 (Nat.lt_succ_of_le hi))))
    rw [hR]
    exact hrem i h hri y
  rw [show L h = (∂_{h} T).translatePairing ρ x from rfl,
    translatePairing_add_sub_sub_eq T ρ hx (hδx h hhδ)]
  calc ‖T R‖ ≤ C * (c / (C + 1) * ‖h‖) :=
        hT R hRK _ (by positivity) hRbound
    _ = C / (C + 1) * (c * ‖h‖) := by ring
    _ ≤ c * ‖h‖ :=
      mul_le_of_le_one_left (by positivity) ((div_le_one (by linarith)).2 (by linarith))

/-- The regularization is differentiable at every admissible translation. -/
theorem differentiableAt_translatePairing (T : 𝓓'(Ω, F)) (ρ : 𝓓(V, ℝ)) {x : E}
    (hx : MapsTo (· + x) (tsupport ρ) Ω) : DifferentiableAt ℝ (T.translatePairing ρ) x :=
  let ⟨_, hL, _⟩ := exists_hasFDerivAt_translatePairing T ρ hx
  hL.differentiableAt

/-- **The derivative of a regularization.** At every admissible translation, the derivative of
`x ↦ T (ρ (· - x))` in the direction `v` is the regularization of the distributional derivative
`∂_{v} T`. -/
theorem fderiv_translatePairing_apply (T : 𝓓'(Ω, F)) (ρ : 𝓓(V, ℝ)) {x : E}
    (hx : MapsTo (· + x) (tsupport ρ) Ω) (v : E) :
    fderiv ℝ (T.translatePairing ρ) x v = (∂_{v} T).translatePairing ρ x := by
  obtain ⟨L, hL, hLv⟩ := exists_hasFDerivAt_translatePairing T ρ hx
  rw [hL.fderiv, hLv]

/-- **Regularizations are smooth.** The regularization `x ↦ T (ρ (· - x))` is smooth on the open
set of translations for which `ρ (· - x)` is supported in `Ω`. -/
theorem contDiffOn_translatePairing (T : 𝓓'(Ω, F)) (ρ : 𝓓(V, ℝ)) :
    ContDiffOn ℝ ∞ (T.translatePairing ρ) {x | MapsTo (· + x) (tsupport ρ) Ω} := by
  have hU := ρ.hasCompactSupport.isCompact.isOpen_setOf_mapsTo_add Ω.isOpen
  rw [contDiffOn_infty]
  intro n
  induction n generalizing T with
  | zero =>
    exact contDiffOn_zero.2 fun x hx =>
      (differentiableAt_translatePairing T ρ hx).continuousAt.continuousWithinAt
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (differentiableAt_translatePairing T ρ hx).differentiableWithinAt,
      by simp, ?_⟩
    refine contDiffOn_clm_apply.2 fun v => (ih (∂_{v} T)).congr fun x hx => ?_
    exact fderiv_translatePairing_apply T ρ hx v

/-- **Distributions with vanishing derivatives have locally constant regularizations.** If every
directional derivative of `T` vanishes, then `x ↦ T (ρ (· - x))` is constant on every
preconnected open set of translations for which `ρ (· - x)` is supported in `Ω`. -/
theorem translatePairing_eq_of_lineDerivOp_eq_zero {T : 𝓓'(Ω, F)}
    (hT : ∀ v : E, ∂_{v} T = 0) (ρ : 𝓓(V, ℝ)) {U : Set E} (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hU : ∀ x ∈ U, MapsTo (· + x) (tsupport ρ) Ω) {x y : E}
    (hx : x ∈ U) (hy : y ∈ U) : T.translatePairing ρ x = T.translatePairing ρ y := by
  refine hUo.is_const_of_fderiv_eq_zero hUc
    (fun z hz => (differentiableAt_translatePairing T ρ (hU z hz)).differentiableWithinAt)
    (fun z hz => ?_) hx hy
  ext v
  simp [fderiv_translatePairing_apply T ρ (hU z hz), hT]

section Convolution

open MeasureTheory Function
open ContinuousLinearMap (lsmul)
open scoped Convolution BoundedContinuousFunction Pointwise NNReal

variable (E) in
/-- Indices `(i, j)` of the values of an `i`-th derivative, `i ≤ N`, on the tuple of vectors of
`Module.finBasis ℝ E` indexed by `j`. -/
private abbrev JetIndex (N : ℕ) := Σ i : Fin (N + 1), Fin i → Fin (Module.finrank ℝ E)

/-- The values of a family of multilinear maps of orders at most `N` on tuples of basis
vectors. -/
private noncomputable def basisEvalCLM (N : ℕ) :
    (Π i : Fin (N + 1), E [×i]→L[ℝ] ℝ) →L[ℝ] JetIndex E N → ℝ :=
  ContinuousLinearMap.pi fun k =>
    ContinuousMultilinearMap.apply ℝ _ ℝ (fun l => Module.finBasis ℝ E (k.2 l)) ∘L
      ContinuousLinearMap.proj k.1

/-- A multilinear map is determined by its values on tuples of basis vectors. -/
private theorem basisEvalCLM_injective (N : ℕ) : Injective (basisEvalCLM (E := E) N) :=
  fun _ _ h => funext fun i => ContinuousMultilinearMap.toMultilinearMap_injective <|
    Module.Basis.ext_multilinear (fun _ => Module.finBasis ℝ E) fun v => congrFun h ⟨i, v⟩

/-- On these finite-dimensional families, the norm is controlled by the values on tuples of basis
vectors. -/
private theorem exists_norm_le_mul_norm_basisEvalCLM (N : ℕ) :
    ∃ C : ℝ≥0, ∀ A : Π i : Fin (N + 1), E [×i]→L[ℝ] ℝ, ‖A‖ ≤ C * ‖basisEvalCLM N A‖ := by
  have _ (i : Fin (N + 1)) : FiniteDimensional ℝ (E [×i]→L[ℝ] ℝ) :=
    Module.Finite.of_injective ContinuousMultilinearMap.toMultilinearMapLinear
      ContinuousMultilinearMap.toMultilinearMap_injective
  obtain ⟨C, -, hC⟩ := (basisEvalCLM (E := E) N).toLinearMap.exists_antilipschitzWith
    (LinearMap.ker_eq_bot.2 (basisEvalCLM_injective N))
  exact ⟨C, ZeroHomClass.bound_of_antilipschitz _ hC⟩

/-- The values on tuples of basis vectors of the derivatives of order at most `N` of a smooth
function supported in `K`, as one bounded continuous real-valued jet. -/
private noncomputable def basisJetCLM (K : Compacts E) (N : ℕ) :
    𝓓_{K}(E, ℝ) →L[ℝ] E →ᵇ (JetIndex E N → ℝ) :=
  (basisEvalCLM N).compLeftContinuousBounded E ∘L
    ∑ i, (ContinuousLinearMap.single ℝ (fun i : Fin (N + 1) => E [×i]→L[ℝ] ℝ) i
      ).compLeftContinuousBounded E ∘L ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i

private theorem basisJetCLM_apply (K : Compacts E) (N : ℕ) (χ : 𝓓_{K}(E, ℝ)) (x : E) :
    basisJetCLM K N χ x = basisEvalCLM N fun i => iteratedFDeriv ℝ i χ x := by
  simp only [basisJetCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compLeftContinuousBounded_apply]
  congr 1
  ext1 i
  simp

private theorem basisJetCLM_apply_apply (K : Compacts E) (N : ℕ) (χ : 𝓓_{K}(E, ℝ)) (x : E)
    (k : JetIndex E N) :
    basisJetCLM K N χ x k = iteratedFDeriv ℝ k.1 χ x (fun l => Module.finBasis ℝ E (k.2 l)) := by
  rw [basisJetCLM_apply]
  rfl

/-- The derivatives of order at most `N` of a smooth function supported in `K` are bounded by the
norm of its jet. -/
private theorem exists_norm_iteratedFDeriv_le_mul_norm_basisJetCLM (K : Compacts E) (N : ℕ) :
    ∃ C : ℝ≥0, ∀ (χ : 𝓓_{K}(E, ℝ)), ∀ i ≤ N, ∀ x,
      ‖iteratedFDeriv ℝ i χ x‖ ≤ C * ‖basisJetCLM K N χ‖ := by
  obtain ⟨C, hC⟩ := exists_norm_le_mul_norm_basisEvalCLM (E := E) N
  refine ⟨C, fun χ i hi x => ?_⟩
  calc ‖iteratedFDeriv ℝ i χ x‖
      ≤ ‖fun i : Fin (N + 1) => iteratedFDeriv ℝ i χ x‖ :=
        norm_le_pi_norm (fun i : Fin (N + 1) => iteratedFDeriv ℝ i χ x) ⟨i, Nat.lt_succ_of_le hi⟩
    _ ≤ C * ‖basisJetCLM K N χ x‖ := by rw [basisJetCLM_apply]; exact hC _
    _ ≤ C * ‖basisJetCLM K N χ‖ := by gcongr; exact (basisJetCLM K N χ).norm_coe_le_norm x

/-- The translates of the jet of a smooth function supported in `K` depend continuously on the
translation. -/
private theorem continuous_basisJetCLM_compContinuous (K : Compacts E) (N : ℕ)
    (χ : 𝓓_{K}(E, ℝ)) :
    Continuous fun y : E =>
      (basisJetCLM K N χ).compContinuous ⟨(· - y), continuous_sub_right y⟩ := by
  have hc : HasCompactSupport (basisJetCLM K N χ) := by
    refine HasCompactSupport.intro K.isCompact fun x hx => ?_
    have h0 (i : Fin (N + 1)) : iteratedFDeriv ℝ i χ x = 0 :=
      notMem_support.1 fun h => hx (χ.tsupport_subset (support_iteratedFDeriv_subset _ h))
    rw [basisJetCLM_apply, show (fun i : Fin (N + 1) => iteratedFDeriv ℝ i χ x) = 0 from
      funext h0, map_zero]
  refine Metric.continuous_iff.2 fun y ε hε => ?_
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuous_iff.1
    (hc.uniformContinuous_of_continuous (basisJetCLM K N χ).continuous) (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun y' hy' => lt_of_le_of_lt ?_ (half_lt_self hε)⟩
  refine (BoundedContinuousFunction.dist_le (half_pos hε).le).2 fun x => ?_
  exact (hδε (show dist (x - y') (x - y) < δ by rwa [dist_sub_left])).le

variable [CompleteSpace F] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [SFinite μ]
  [μ.IsAddLeftInvariant]

/-- **A distribution passes under a convolution integral.** Let `ψ` be a test function which is
the convolution `f ⋆ ρ`, `ψ x = ∫ f y * ρ (x - y) ∂μ(y)`, of an integrable compactly supported
`f` with a test function `ρ` whose translates by the points of `tsupport f` are supported in `Ω`.
Then `T ψ` is the integral of the regularization against `f`:

`T ψ = ∫ f y • T (ρ (· - y)) ∂μ(y)`.

Pairing the regularization of `T` with a test function is therefore pairing `T` with a
convolution, which is how regularizations recover a distribution as the kernel shrinks. -/
theorem apply_eq_integral_smul_translatePairing (T : 𝓓'(Ω, F)) (ρ : 𝓓(V, ℝ)) {f : E → ℝ}
    (hf : Integrable f μ) (hfc : HasCompactSupport f)
    (hfρ : ∀ y ∈ tsupport f, MapsTo (· + y) (tsupport ρ) Ω) {ψ : 𝓓(Ω, ℝ)}
    (hψ : ⇑ψ = f ⋆[lsmul ℝ ℝ, μ] ρ) :
    T ψ = ∫ y, f y • T.translatePairing ρ y ∂μ := by
  classical
  -- Strategy: on tests supported in a compact `K`, `T` is bounded by the sup norm of a jet of
  -- finite order, valued in a Banach space. After applying a functional `ℓ` on `F`, Hahn–Banach
  -- extends `ℓ ∘ T` to a continuous functional `g` on that space, and `g` commutes with the
  -- Bochner integral of the jets of the translates of `ρ`, which is the jet of `ψ`.
  -- The translates of `ρ` and the test function `ψ` are supported in one compact `K ⊆ Ω`, on
  -- which `T` is bounded by the norm of the jets of order `N`.
  let K : Compacts E :=
    ⟨tsupport f + tsupport ρ, hfc.isCompact.add ρ.hasCompactSupport.isCompact⟩
  have hKΩ : (K : Set E) ⊆ Ω := by
    rintro _ ⟨y, hy, z, hz, rfl⟩
    simpa [add_comm] using hfρ y hy hz
  obtain ⟨N, C, hC0, hC⟩ := T.exists_norm_apply_le hKΩ
  obtain ⟨C₀, hC₀⟩ := exists_norm_iteratedFDeriv_le_mul_norm_basisJetCLM K N
  have hbound (χ : 𝓓_{K}(E, ℝ)) :
      ‖T (ofSupportedInCLM ℝ hKΩ χ)‖ ≤ C * C₀ * ‖basisJetCLM K N χ‖ := by
    rw [mul_assoc]
    exact hC _ (by simpa using χ.tsupport_subset) _ (by positivity) fun i hi x => by
      simpa using hC₀ χ i hi x
  -- The translates of the jet of `ρ` form a bounded continuous path `Θ`.
  let Kρ : Compacts E := ⟨tsupport ρ, ρ.hasCompactSupport.isCompact⟩
  let ρK : 𝓓_{Kρ}(E, ℝ) := .of_support_subset ρ.contDiff (subset_tsupport _)
  have hρK : ⇑ρK = ρ := funext <| ContDiffMapSupportedIn.coe_of_support_subset _ _
  let Θ (y : E) : E →ᵇ (JetIndex E N → ℝ) :=
    (basisJetCLM Kρ N ρK).compContinuous ⟨(· - y), continuous_sub_right y⟩
  have hΘ (y x : E) (k : JetIndex E N) :
      Θ y x k = iteratedFDeriv ℝ k.1 ρ (x - y) (fun l => Module.finBasis ℝ E (k.2 l)) := by
    simp [Θ, basisJetCLM_apply_apply, hρK]
  have hΘb (y : E) : ‖Θ y‖ ≤ ‖basisJetCLM Kρ N ρK‖ :=
    (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x =>
      (basisJetCLM Kρ N ρK).norm_coe_le_norm (x - y)
  have hfΘ : Integrable (fun y => f y • Θ y) μ :=
    hf.smul_bdd _ (continuous_basisJetCLM_compContinuous Kρ N ρK).aestronglyMeasurable
      (ae_of_all _ hΘb)
  -- The translate of `ρ` by a point of `tsupport f` is a test supported in `K` whose jet is the
  -- corresponding point of the path.
  have htrans (y : E) (hy : y ∈ tsupport f) : ∃ χ : 𝓓_{K}(E, ℝ),
      basisJetCLM K N χ = Θ y ∧ T (ofSupportedInCLM ℝ hKΩ χ) = T.translatePairing ρ y := by
    have hs : support (fun x => ρ (x - y)) ⊆ K := fun x hx =>
      ⟨y, hy, x - y, subset_tsupport _ hx, add_sub_cancel y x⟩
    let χ : 𝓓_{K}(E, ℝ) :=
      .of_support_subset (ρ.contDiff.comp (contDiff_id.sub contDiff_const)) hs
    have hχ : ⇑χ = fun x => ρ (x - y) :=
      funext <| ContDiffMapSupportedIn.coe_of_support_subset _ _
    refine ⟨χ, ?_, (translatePairing_eq T fun x => by simp [hχ]).symm⟩
    ext x k : 2
    rw [basisJetCLM_apply_apply, hΘ, hχ, iteratedFDeriv_comp_sub]
  -- The test function `ψ` is supported in `K`, and the path integrates to its jet.
  have hψK : support ψ ⊆ K := by
    rw [hψ]
    exact (support_convolution_subset _).trans
      (add_subset_add (subset_tsupport _) (subset_tsupport _))
  let ψK : 𝓓_{K}(E, ℝ) := .of_support_subset ψ.contDiff hψK
  have hψK' : ⇑ψK = ψ := funext <| ContDiffMapSupportedIn.coe_of_support_subset _ _
  have hψψK : ofSupportedInCLM ℝ hKΩ ψK = ψ := by
    ext x
    simp [hψK']
  have hint : ∫ y, f y • Θ y ∂μ = basisJetCLM K N ψK := by
    ext x k : 2
    have hL := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) k).comp
      (BoundedContinuousFunction.evalCLM ℝ x)).integral_comp_comm hfΘ
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      BoundedContinuousFunction.evalCLM_apply] at hL
    have hconv := (ρ.hasCompactSupport.iteratedFDeriv k.1).convolutionExists_right
      ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k.1 => E) ℝ ℝ).comp
        (lsmul ℝ ℝ)) hf.locallyIntegrable (ρ.contDiff.continuous_iteratedFDeriv (by simp)) x
    rw [← hL, basisJetCLM_apply_apply, hψK', hψ,
      ρ.hasCompactSupport.iteratedFDeriv_convolution_right _ hf.locallyIntegrable ρ.contDiff
        (by exact_mod_cast le_top), convolution_def,
      ContinuousMultilinearMap.integral_apply hconv]
    congr 1
    ext y
    simp [hΘ]
  -- Scalarize, and extend the bounded functional `T` from the jets of tests by Hahn–Banach.
  have hint' : Integrable (fun y => f y • T.translatePairing ρ y) μ := by
    have hcont : ContinuousOn (T.translatePairing ρ) (tsupport f) :=
      (T.contDiffOn_translatePairing ρ).continuousOn.mono hfρ
    refine (hf.integrableOn.smul_continuousOn hcont hfc.isCompact
      ).integrable_of_forall_notMem_eq_zero fun y hy => ?_
    simp [image_eq_zero_of_notMem_tsupport hy]
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun ℓ => ?_
  rw [← ContinuousLinearMap.integral_comp_comm ℓ hint']
  have hinj : Injective (basisJetCLM K N) := fun χ χ' h => by
    refine ContDiffMapSupportedIn.structureMapCLM_zero_injective ℝ (n := ⊤) ?_
    ext1 x
    have hx : (fun i : Fin (N + 1) => iteratedFDeriv ℝ i χ x) =
        fun i : Fin (N + 1) => iteratedFDeriv ℝ i χ' x :=
      basisEvalCLM_injective N (by rw [← basisJetCLM_apply K N χ x, ← basisJetCLM_apply, h])
    simpa [ContDiffMapSupportedIn.structureMapCLM_top_apply] using congrFun hx ⟨0, N.succ_pos⟩
  let e := LinearEquiv.ofInjective (basisJetCLM K N).toLinearMap hinj
  let g₁ : LinearMap.range (basisJetCLM K N).toLinearMap →ₗ[ℝ] ℝ :=
    (ℓ ∘L (T : 𝓓(Ω, ℝ) →L[ℝ] F) ∘L ofSupportedInCLM ℝ hKΩ).toLinearMap ∘ₗ e.symm.toLinearMap
  -- `g₁` is by definition `ℓ ∘ T` read through the inverse of `e`.
  have hg₁ (χ : 𝓓_{K}(E, ℝ)) : g₁ (e χ) = ℓ (T (ofSupportedInCLM ℝ hKΩ χ)) :=
    congrArg (fun χ => ℓ (T (ofSupportedInCLM ℝ hKΩ χ))) (e.symm_apply_apply χ)
  have hc : 0 ≤ ‖ℓ‖ * (C * C₀) := by positivity
  obtain ⟨g, hg, -⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm _ g₁
    (p := (‖ℓ‖ * (C * C₀)).toNNReal • normSeminorm ℝ _)
    (continuous_norm.const_smul _) fun w => by
      obtain ⟨χ, rfl⟩ := e.surjective w
      rw [hg₁, smul_apply, coe_normSeminorm, LinearEquiv.ofInjective_apply, NNReal.smul_def,
        Real.coe_toNNReal _ hc, smul_eq_mul, mul_assoc]
      exact (ℓ.le_opNorm _).trans (by gcongr; exact hbound χ)
  have hgjet (χ : 𝓓_{K}(E, ℝ)) :
      g (basisJetCLM K N χ) = ℓ (T (ofSupportedInCLM ℝ hKΩ χ)) := by
    rw [← hg₁, ← hg, LinearEquiv.ofInjective_apply, ContinuousLinearMap.coe_coe]
  have hpt (y : E) : g (f y • Θ y) = ℓ (f y • T.translatePairing ρ y) := by
    by_cases hy : y ∈ tsupport f
    · obtain ⟨χ, hχ, hTχ⟩ := htrans y hy
      rw [map_smul, map_smul, ← hχ, hgjet, hTχ]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  calc ℓ (T ψ) = g (∫ y, f y • Θ y ∂μ) := by rw [hint, hgjet, hψψK]
    _ = ∫ y, ℓ (f y • T.translatePairing ρ y) ∂μ := by
      rw [← g.integral_comp_comm hfΘ]
      exact integral_congr_ae (ae_of_all _ hpt)

end Convolution

end Distribution
