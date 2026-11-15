/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Transport
public import TauCeti.LinearAlgebra.Determinant.Endomorphism
import TauCeti.Analysis.Normed.Operator.Banach

/-!
# The canonical orientation of endomorphisms under transport

An endomorphism `T` of a finite-dimensional vector space `V` has a canonical trivialization of
its determinant line, `det T ≃ K` (`LinearMap.detLineEndEquiv`), defined through the exact
sequence `0 → ker T → V → V → coker T → 0` for every `T`, invertible or not. This file compares
it with the kernel charts through which the determinant lines of a family of operators are
glued into a line bundle (`ContinuousLinearMap.detLineChartEquiv`), and finds that, after a sign
depending only on the dimension of the cokernel, it is a continuous orientation of the
determinant lines over the whole space of endomorphisms.

**A global kernel chart.** Stabilize `T` by a bijective `D₂ : Λ → V`, and read the kernel of
`T.coprod D₂ : V × Λ → V`, which is the graph `{(x, -D₂⁻¹ T x)}`, through a coordinate
`q (x, l) = e x` with `e : V ≃ G`. This kernel chart is valid for every `T`. The kernel of the
stabilization is identified with `V` by the first projection, and with these identifications the
exact sequence `0 → ker T → ker (T.coprod D₂) → Λ → coker T → 0` of the chart becomes the exact
sequence `0 → ker T → V → V → coker T → 0` of `T`, with the last two maps negated. By naturality
of the four-term isomorphism (`TauCeti.detLineFourTermEquiv_congr`), the canonical trivialization
of `det T` is read in the chart as an explicit functional on `det G ⊗ (det Λ)^*` which does not
depend on `T`, times the sign `(-1) ^ (c (dim V + 1) + dim V)`, where `c` is the dimension of the
cokernel of `T` (`ContinuousLinearMap.detLineEndEquiv_detLineChartEquiv_symm_tmul`). Consequently
the element `(-1) ^ (c (dim V + 1)) • (detLineEndEquiv T)⁻¹ 1` of the determinant line of `T` is
read in this chart as one and the same element for every `T`
(`ContinuousLinearMap.neg_one_pow_smul_detLineChartEquiv_detLineEndEquiv_symm_one`).

**Coherence and transport.** Over `ℝ`, the sign-corrected canonical elements therefore form a
coherent family (`TauCeti.IsDetLineCoherentOn`) along an arbitrary family of endomorphisms of a
finite-dimensional normed space
(`TauCeti.isDetLineCoherentOn_neg_one_pow_smul_detLineEndEquiv_symm_one`), with no continuity
assumption, since the chart is global and reads them as a constant. Along a continuous path the
transport of orientations (`TauCeti.detLineOrientationTransport`) carries the canonical
orientation at one end to the canonical orientation at the other
(`TauCeti.detLineOrientationTransport_rayOfNeZero_neg_one_pow_smul_detLineEndEquiv_symm_one`).
For invertible ends the cokernel is zero, and the canonical element is `det T` times the element
which the trivialization by invertibility sends to `1`
(`LinearMap.detLineEquivOfBijective_symm_one_eq_inv_det_smul`). So transport carries the
orientation given by invertibility at `T₀` to the one given by invertibility at `T₁` multiplied
by the sign of `det T₀ * det T₁`
(`TauCeti.detLineOrientationTransport_rayOfNeZero_detLineEquivOfBijective_symm_one`): it is
reversed exactly when the determinant changes sign between the two ends.

The sign correction cannot be dropped in even dimension. For `V = ℝ²` and
`T t = diag (t, 1)`, the reading of the uncorrected canonical element in the global chart is, by
`ContinuousLinearMap.detLineEndEquiv_detLineChartEquiv_symm_tmul`, one element for `t ≠ 0` and
its negative at `t = 0`, where the cokernel is a line.

This is the finite-dimensional half of the orientation of a periodic orbit by transport. When an
operator has kernel and cokernel identified with those of an endomorphism `ε - P` of a finite
space, as the operator `d/dt - M(t)` on loops twisted by `ε`, with return map `P`
(`TauCeti.detLineTwistedLinearOperatorEquiv`), its canonical orientation is read off from
`det (ε - P)`; that it is the orientation transported from a reference is the statement here for
the finite part.

## Main results

* `ContinuousLinearMap.detLineEndEquiv_detLineChartEquiv_symm_tmul`: the canonical
  trivialization read in a kernel chart with a bijective stabilizer.
* `ContinuousLinearMap.neg_one_pow_smul_detLineChartEquiv_detLineEndEquiv_symm_one`: the
  sign-corrected canonical element is read in such a chart independently of the operator.
* `TauCeti.isDetLineCoherentOn_neg_one_pow_smul_detLineEndEquiv_symm_one`: the sign-corrected
  canonical elements are a continuous orientation of the determinant lines of any family of
  endomorphisms.
* `TauCeti.detLineOrientationTransport_rayOfNeZero_neg_one_pow_smul_detLineEndEquiv_symm_one` and
  `TauCeti.detLineOrientationTransport_rayOfNeZero_detLineEquivOfBijective_symm_one`: orientation
  transport along a path of endomorphisms.

## References

* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368 (normalization of the
  exact-sequence isomorphisms and their continuity).
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
-/

public section

open Module TensorProduct

namespace ContinuousLinearMap

section Chart

variable {𝕜 V Λ G : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  [ContinuousAdd V] [FiniteDimensional 𝕜 V] [AddCommGroup Λ] [Module 𝕜 Λ] [TopologicalSpace Λ]
  [FiniteDimensional 𝕜 Λ] [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
  [FiniteDimensional 𝕜 G] {T : V →L[𝕜] V} {D₂ : Λ →L[𝕜] V}

/-- For a bijective stabilizer `D₂`, the first projection identifies the kernel of
`T.coprod D₂`, the graph of `x ↦ -D₂⁻¹ (T x)`, with `V`. -/
private noncomputable def kerCoprodEquivOfBijective (hD₂ : Function.Bijective D₂) :
    (T.coprod D₂).ker ≃ₗ[𝕜] V :=
  LinearEquiv.ofBijective ((LinearMap.fst 𝕜 V Λ).comp (T.coprod D₂).ker.subtype) <| by
    refine ⟨fun a b hab ↦ Subtype.ext (Prod.ext hab (hD₂.1 ?_)), fun x ↦ ?_⟩
    · have ha := a.2
      have hb := b.2
      simp only [LinearMap.coe_comp, LinearMap.coe_fst, Function.comp_apply,
        Submodule.coe_subtype] at hab
      simp only [LinearMap.mem_ker, coe_coe, coprod_apply] at ha hb
      rw [hab] at ha
      exact add_left_cancel (ha.trans hb.symm)
    · obtain ⟨l, hl⟩ := hD₂.2 (-T x)
      exact ⟨⟨(x, l), by simp [hl]⟩, rfl⟩

omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 Λ] in
@[simp]
private theorem kerCoprodEquivOfBijective_apply (hD₂ : Function.Bijective D₂)
    (a : (T.coprod D₂).ker) : kerCoprodEquivOfBijective hD₂ a = (a : V × Λ).1 :=
  (rfl)

omit [TopologicalSpace V] [ContinuousAdd V] [FiniteDimensional 𝕜 V] in
/-- Negation of the second factor `W` acts on `L ⊗ (det W)^*` by `(-1) ^ dim W`. -/
private theorem tensorCongr_refl_neg_apply {L W : Type*} [AddCommGroup L] [Module 𝕜 L]
    [AddCommGroup W] [Module 𝕜 W] (y : L ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 W)) :
    TensorProduct.congr (LinearEquiv.refl 𝕜 L)
        (LinearEquiv.neg 𝕜 : W ≃ₗ[𝕜] W).detLineCongr.symm.dualMap y =
      (-1 : 𝕜) ^ finrank 𝕜 W • y := by
  induction y using TensorProduct.inductionOn with
  | add y z hy hz => rw [map_add, hy, hz, smul_add]
  | tmul a ψ =>
    rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, ← TensorProduct.tmul_smul]
    congr 1
    refine LinearMap.ext fun x ↦ ?_
    rw [LinearEquiv.dualMap_apply, LinearEquiv.detLineCongr_symm, LinearEquiv.symm_neg,
      LinearEquiv.detLineCongr_neg_apply, map_smul, LinearMap.smul_apply]

/-- The canonical trivialization of `det T` against the four-term isomorphism of the
stabilization by a bijective `D₂`: with the kernel of `T.coprod D₂` identified with `V` by the
first projection and `Λ` with `V` by `D₂`, it is the contraction `β ⊗ φ ↦ φ β` up to the sign
`(-1) ^ (dim (coker T) + dim V)`. -/
private theorem detLineEndEquiv_detLineCoprodEquiv_tmul (hD₂ : Function.Bijective D₂)
    (h : Function.Surjective (T.coprod D₂)) (b : TauCeti.detLine 𝕜 (T.coprod D₂).ker)
    (φ : Dual 𝕜 (TauCeti.detLine 𝕜 Λ)) :
    (T : V →ₗ[𝕜] V).detLineEndEquiv (detLineCoprodEquiv T D₂ h (b ⊗ₜ φ)) =
      (-1) ^ (finrank 𝕜 (V ⧸ LinearMap.range (T : V →ₗ[𝕜] V)) + finrank 𝕜 V) *
        φ ((LinearEquiv.ofBijective (D₂ : Λ →ₗ[𝕜] V) hD₂).symm.detLineCongr
          ((kerCoprodEquivOfBijective hD₂).detLineCongr b)) := by
  set c := finrank 𝕜 (V ⧸ LinearMap.range (T : V →ₗ[𝕜] V))
  set eΛ := LinearEquiv.ofBijective (D₂ : Λ →ₗ[𝕜] V) hD₂
  set eB := kerCoprodEquivOfBijective (T := T) hD₂
  -- The stabilization sequence `0 → ker T → ker (T.coprod D₂) → Λ → coker T → 0` is isomorphic
  -- to `0 → ker T → V → V → coker T → 0` through `id`, `eB`, `-D₂` and `-id`.
  have hnat := TauCeti.detLineFourTermEquiv_congr (kerCoprodHom_injective T D₂)
    (exact_kerCoprodHom_parameterProj T D₂) (exact_parameterProj_parameterToCoker T D₂)
    ((parameterToCoker_surjective_iff_coprod_surjective T D₂).2 h)
    (LinearMap.ker (T : V →ₗ[𝕜] V)).injective_subtype (T : V →ₗ[𝕜] V).exact_subtype_ker_map
    (T : V →ₗ[𝕜] V).exact_map_mkQ_range (LinearMap.range (T : V →ₗ[𝕜] V)).mkQ_surjective
    (LinearEquiv.refl 𝕜 _) eB (eΛ.trans (LinearEquiv.neg 𝕜)) (LinearEquiv.neg 𝕜)
    (LinearMap.ext fun x ↦ by simp [eB, kerCoprodHom_apply])
    (LinearMap.ext fun a ↦ by
      have ha := a.2
      simp only [LinearMap.mem_ker, coe_coe, coprod_apply] at ha
      simp [eB, eΛ, parameterProj_apply, eq_neg_of_add_eq_zero_left ha])
    (LinearMap.ext fun l ↦ by simp [eΛ, parameterToCoker_apply]) (b ⊗ₜ φ)
  rw [LinearEquiv.detLineCongr_refl, tensorCongr_refl_neg_apply] at hnat
  -- The negation of `V` acts on its determinant line by `(-1) ^ dim V`.
  have hC (y : TauCeti.detLine 𝕜 V) : (eΛ.trans (LinearEquiv.neg 𝕜)).symm.detLineCongr y =
      (-1 : 𝕜) ^ finrank 𝕜 V • eΛ.symm.detLineCongr y := by
    simp only [LinearEquiv.trans_symm, LinearEquiv.detLineCongr_trans, LinearEquiv.trans_apply,
      LinearEquiv.symm_neg, LinearEquiv.detLineCongr_neg_apply, map_smul]
  have h2 := congrArg (T : V →ₗ[𝕜] V).detLineEndEquiv hnat
  rw [TensorProduct.congr_tmul, LinearMap.detLineEndEquiv_detLineFourTermEquiv, map_smul,
    smul_eq_mul, LinearEquiv.dualMap_apply, LinearEquiv.detLineCongr_symm, hC] at h2
  rw [LinearMap.map_smul_of_tower φ] at h2
  simp only [smul_eq_mul] at h2
  -- `detLineCoprodEquiv` is the four-term isomorphism appearing in `h2`.
  have hdef := congrArg (fun Φ : _ ≃ₗ[𝕜] (T : V →ₗ[𝕜] V).detLine ↦
    (T : V →ₗ[𝕜] V).detLineEndEquiv (Φ (b ⊗ₜ φ))) (detLineCoprodEquiv_def h)
  have key (x : 𝕜)
      (hx : (-1) ^ finrank 𝕜 V * φ (eΛ.symm.detLineCongr (eB.detLineCongr b)) = (-1) ^ c * x) :
      x = (-1) ^ (c + finrank 𝕜 V) * φ (eΛ.symm.detLineCongr (eB.detLineCongr b)) := by
    have hc : (-1 : 𝕜) ^ c * (-1) ^ c = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    linear_combination (-(-1 : 𝕜) ^ c) * hx - x * hc
  exact hdef.trans (key _ h2)

variable {q : V × Λ →L[𝕜] G}

/-- **The canonical trivialization read in a kernel chart with a bijective stabilizer.** Let the
stabilizer `D₂ : Λ → V` be bijective and the kernel coordinate be `q (x, l) = e x` for a linear
isomorphism `e : V ≃ G`. Then the canonical trivialization `LinearMap.detLineEndEquiv` of the
determinant line of `T`, read through the kernel chart `ContinuousLinearMap.detLineChartEquiv`,
sends `g ⊗ φ` to `φ (D₂⁻¹ (e⁻¹ g))` times the sign `(-1) ^ (c (dim V + 1) + dim V)`, where `c` is
the dimension of the cokernel of `T`. Only the sign depends on `T`. -/
theorem detLineEndEquiv_detLineChartEquiv_symm_tmul (hD₂ : Function.Bijective D₂)
    (e : V ≃ₗ[𝕜] G) (hq : ∀ x l, q (x, l) = e x) (h : ((T.coprod D₂).prod q).IsInvertible)
    (g : TauCeti.detLine 𝕜 G) (φ : Dual 𝕜 (TauCeti.detLine 𝕜 Λ)) :
    (T : V →ₗ[𝕜] V).detLineEndEquiv ((detLineChartEquiv T D₂ q h).symm (g ⊗ₜ φ)) =
      (-1) ^ (finrank 𝕜 (V ⧸ LinearMap.range (T : V →ₗ[𝕜] V)) * (finrank 𝕜 V + 1) +
          finrank 𝕜 V) *
        φ ((LinearEquiv.ofBijective (D₂ : Λ →ₗ[𝕜] V) hD₂).symm.detLineCongr
          (e.symm.detLineCongr g)) := by
  -- The kernel coordinate followed by the first projection is `e⁻¹`.
  have hκ : (kerEquivOfProd _ q h).toLinearEquiv.trans (kerCoprodEquivOfBijective (T := T) hD₂) =
      e.symm := by
    refine LinearEquiv.ext fun g ↦ e.injective ?_
    rw [LinearEquiv.trans_apply, kerCoprodEquivOfBijective_apply, LinearEquiv.apply_symm_apply,
      ← hq, Prod.mk.eta]
    exact (kerEquivOfProd_symm_apply h _).symm.trans ((kerEquivOfProd _ q h).symm_apply_apply g)
  have hκ' : (kerCoprodEquivOfBijective (T := T) hD₂).detLineCongr
      ((kerEquivOfProd _ q h).toLinearEquiv.detLineCongr g) = e.symm.detLineCongr g := by
    rw [← LinearEquiv.trans_apply, ← LinearEquiv.detLineCongr_trans, hκ]
  -- The Koszul sign of the stabilization, with `dim Λ = dim V`.
  have hsign : (-1 : 𝕜) ^ (finrank 𝕜 (V ⧸ (T : V →L[𝕜] V).range) * finrank 𝕜 Λ) =
      (-1) ^ (finrank 𝕜 (V ⧸ LinearMap.range (T : V →ₗ[𝕜] V)) * finrank 𝕜 V) := by
    rw [(LinearEquiv.ofBijective (D₂ : Λ →ₗ[𝕜] V) hD₂).finrank_eq]
  rw [detLineChartEquiv_symm_tmul, detLineStabilizationEquiv_apply, map_smul, smul_eq_mul,
    detLineEndEquiv_detLineCoprodEquiv_tmul hD₂, hκ', hsign, ← mul_assoc, ← pow_add]
  congr 2
  ring

/-- **The canonical element is read in a chart independently of the operator.** For kernel
charts with the same bijective stabilizer `D₂` and the same kernel coordinate `q (x, l) = e x`,
the element `(-1) ^ (c (dim V + 1)) • (detLineEndEquiv T)⁻¹ 1` of the determinant line of `T`,
where `c` is the dimension of the cokernel of `T`, has the same reading for any two operators
`T` and `T'`. -/
theorem neg_one_pow_smul_detLineChartEquiv_detLineEndEquiv_symm_one {T' : V →L[𝕜] V}
    (hD₂ : Function.Bijective D₂) (e : V ≃ₗ[𝕜] G) (hq : ∀ x l, q (x, l) = e x)
    (h : ((T.coprod D₂).prod q).IsInvertible) (h' : ((T'.coprod D₂).prod q).IsInvertible) :
    (-1 : 𝕜) ^ (finrank 𝕜 (V ⧸ LinearMap.range (T : V →ₗ[𝕜] V)) * (finrank 𝕜 V + 1)) •
        detLineChartEquiv T D₂ q h ((T : V →ₗ[𝕜] V).detLineEndEquiv.symm 1) =
      (-1 : 𝕜) ^ (finrank 𝕜 (V ⧸ LinearMap.range (T' : V →ₗ[𝕜] V)) * (finrank 𝕜 V + 1)) •
        detLineChartEquiv T' D₂ q h' ((T' : V →ₗ[𝕜] V).detLineEndEquiv.symm 1) := by
  -- The functional `g ⊗ φ ↦ φ (D₂⁻¹ (e⁻¹ g))`, which does not depend on the operator.
  set Ψ : TauCeti.detLine 𝕜 G ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ) →ₗ[𝕜] 𝕜 :=
    TensorProduct.lift (Dual.eval 𝕜 _ ∘ₗ ((e.symm.detLineCongr).trans
      (LinearEquiv.ofBijective (D₂ : Λ →ₗ[𝕜] V) hD₂).symm.detLineCongr).toLinearMap)
  -- Through any such chart, the canonical trivialization of `S` is a sign times `Ψ`.
  have hΨ (S : V →L[𝕜] V) (hS : ((S.coprod D₂).prod q).IsInvertible) (z) :
      (S : V →ₗ[𝕜] V).detLineEndEquiv ((detLineChartEquiv S D₂ q hS).symm z) =
        (-1) ^ (finrank 𝕜 (V ⧸ LinearMap.range (S : V →ₗ[𝕜] V)) * (finrank 𝕜 V + 1) +
          finrank 𝕜 V) * Ψ z := by
    induction z using TensorProduct.inductionOn with
    | add y z hy hz => rw [map_add, map_add, hy, hz, map_add]; ring
    | tmul g φ =>
      rw [detLineEndEquiv_detLineChartEquiv_symm_tmul hD₂ e hq]
      simp only [Ψ, TensorProduct.lift.tmul, LinearMap.coe_comp, Function.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.trans_apply, Dual.eval_apply]
  -- So `Ψ` reads the sign-corrected canonical element of `S` as `(-1) ^ dim V`.
  have hval (S : V →L[𝕜] V) (hS : ((S.coprod D₂).prod q).IsInvertible) :
      Ψ ((-1 : 𝕜) ^ (finrank 𝕜 (V ⧸ LinearMap.range (S : V →ₗ[𝕜] V)) * (finrank 𝕜 V + 1)) •
        detLineChartEquiv S D₂ q hS ((S : V →ₗ[𝕜] V).detLineEndEquiv.symm 1)) =
          (-1) ^ finrank 𝕜 V := by
    have h1 := hΨ S hS (detLineChartEquiv S D₂ q hS ((S : V →ₗ[𝕜] V).detLineEndEquiv.symm 1))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply, pow_add] at h1
    rw [map_smul, smul_eq_mul]
    set P := Ψ (detLineChartEquiv S D₂ q hS ((S : V →ₗ[𝕜] V).detLineEndEquiv.symm 1))
    set s := (-1 : 𝕜) ^ (finrank 𝕜 (V ⧸ LinearMap.range (S : V →ₗ[𝕜] V)) * (finrank 𝕜 V + 1))
    have hn : (-1 : 𝕜) ^ finrank 𝕜 V * (-1) ^ finrank 𝕜 V = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    linear_combination (-(-1 : 𝕜) ^ finrank 𝕜 V) * h1 - s * P * hn
  -- `Ψ` is injective, being a sign times an isomorphism.
  have hinj : Function.Injective Ψ := fun y z hyz ↦ by
    have hy := hΨ T h y
    have hz := hΨ T h z
    rw [hyz, ← hz] at hy
    exact (detLineChartEquiv T D₂ q h).symm.injective ((T : V →ₗ[𝕜] V).detLineEndEquiv.injective
      hy)
  exact hinj ((hval T h).trans (hval T' h').symm)

end Chart

end ContinuousLinearMap

namespace TauCeti

open ContinuousLinearMap Set

variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace X]

/-- **The canonical orientation of endomorphisms is continuous.** For any family `T` of
endomorphisms of a finite-dimensional normed space `V`, the elements
`(-1) ^ (c (dim V + 1)) • (detLineEndEquiv (T x))⁻¹ 1` of the determinant lines, where `c` is the
dimension of the cokernel of `T x`, form a coherent family on every set: they are a continuous
orientation of the determinant lines. No continuity of `T` is needed, since a single kernel chart
is valid for every operator and reads all of them as the same element
(`ContinuousLinearMap.neg_one_pow_smul_detLineChartEquiv_detLineEndEquiv_symm_one`). In odd
dimension the sign is `1`. -/
theorem isDetLineCoherentOn_neg_one_pow_smul_detLineEndEquiv_symm_one (T : X → V →L[ℝ] V)
    (s : Set X) :
    IsDetLineCoherentOn T (fun x ↦ (-1 : ℝ) ^
      (finrank ℝ (V ⧸ LinearMap.range (T x : V →ₗ[ℝ] V)) * (finrank ℝ V + 1)) •
        (T x : V →ₗ[ℝ] V).detLineEndEquiv.symm 1) s := by
  refine (isDetLineCoherentOn_iff ..).2 fun x₀ _ ↦ (isDetLineCoherentWithinAt_iff ..).2
    ⟨smul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
    ((LinearEquiv.map_ne_zero_iff _).2 one_ne_zero), ?_⟩
  -- The global chart: stabilize by all of `V`, and read the kernel by its first component.
  let S : Submodule ℝ V := ⊤
  let G : Submodule ℝ (V × S) := LinearMap.ker (LinearMap.snd ℝ V S)
  let e : V ≃ₗ[ℝ] G :=
    { toFun x := ⟨(x, 0), by simp [G]⟩
      invFun g := (g : V × S).1
      map_add' x y := by ext <;> simp
      map_smul' c x := by ext <;> simp
      left_inv x := rfl
      right_inv g := Subtype.ext (Prod.ext rfl (LinearMap.mem_ker.1 g.2).symm) }
  let q : V × S →L[ℝ] G := (e.toContinuousLinearEquiv : V →L[ℝ] G).comp (fst ℝ V S)
  have hq (x : V) (l : S) : q (x, l) = e x := rfl
  have hS : Function.Bijective S.subtypeL := ⟨Subtype.val_injective, fun y ↦ ⟨⟨y, trivial⟩, rfl⟩⟩
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  have : CompleteSpace S := FiniteDimensional.completeSpace ℝ S
  have : CompleteSpace G := FiniteDimensional.completeSpace ℝ G
  -- The chart is valid for every operator.
  have hinv (A : V →L[ℝ] V) : ((A.coprod S.subtypeL).prod q).IsInvertible := by
    refine isInvertible_iff_bijective.2 ⟨fun a b hab ↦ ?_, fun y ↦ ?_⟩
    · simp only [ContinuousLinearMap.prod_apply, coprod_apply, Prod.mk.injEq] at hab
      have h1 : a.1 = b.1 := e.injective (by rw [← hq a.1 a.2, ← hq b.1 b.2]; exact hab.2)
      refine Prod.ext h1 (hS.1 ?_)
      rw [h1] at hab
      exact add_left_cancel hab.1
    · refine ⟨(e.symm y.2, ⟨y.1 - A (e.symm y.2), trivial⟩), ?_⟩
      simp [hq]
  refine ⟨S, inferInstance, G, inferInstance, q, hinv (T x₀),
    Filter.Eventually.of_forall fun x ↦ ⟨hinv (T x), ?_⟩⟩
  rw [map_smul, map_smul, neg_one_pow_smul_detLineChartEquiv_detLineEndEquiv_symm_one hS e hq
    (hinv (T x)) (hinv (T x₀))]

section Transport

variable {T : ℝ → V →L[ℝ] V} {a b : ℝ}

/-- **Transport of the canonical orientation.** Along a continuous path of endomorphisms of a
finite-dimensional normed space, orientation transport carries the orientation of
`(-1) ^ (c (dim V + 1)) • (detLineEndEquiv (T a))⁻¹ 1` to that of the same element at `T b`,
where `c` is the dimension of the cokernel. -/
theorem detLineOrientationTransport_rayOfNeZero_neg_one_pow_smul_detLineEndEquiv_symm_one
    [CompleteSpace V] (hT : ContinuousOn T (uIcc a b))
    (hF : ∀ t ∈ uIcc a b, IsFredholm (T t)) :
    detLineOrientationTransport a b hT hF (rayOfNeZero ℝ ((-1 : ℝ) ^
      (finrank ℝ (V ⧸ LinearMap.range (T a : V →ₗ[ℝ] V)) * (finrank ℝ V + 1)) •
        (T a : V →ₗ[ℝ] V).detLineEndEquiv.symm 1)
          ((isDetLineCoherentOn_neg_one_pow_smul_detLineEndEquiv_symm_one T (uIcc a b)).ne_zero
            left_mem_uIcc)) =
      rayOfNeZero ℝ ((-1 : ℝ) ^
        (finrank ℝ (V ⧸ LinearMap.range (T b : V →ₗ[ℝ] V)) * (finrank ℝ V + 1)) •
          (T b : V →ₗ[ℝ] V).detLineEndEquiv.symm 1)
          ((isDetLineCoherentOn_neg_one_pow_smul_detLineEndEquiv_symm_one T (uIcc a b)).ne_zero
            right_mem_uIcc) :=
  detLineOrientationTransport_rayOfNeZero hT hF
    (isDetLineCoherentOn_neg_one_pow_smul_detLineEndEquiv_symm_one T _)

/-- **Transport between invertible endomorphisms changes the orientation by the sign of the
determinants.** Along a continuous path of endomorphisms of a finite-dimensional normed space
with invertible ends, orientation transport carries the orientation of the determinant line of
`T a` given by invertibility (`LinearMap.detLineEquivOfBijective`) to the orientation of
`det (T a) * det (T b)` times the element given by invertibility at `T b`: the same orientation
when the two determinants have the same sign, and the opposite one otherwise. -/
theorem detLineOrientationTransport_rayOfNeZero_detLineEquivOfBijective_symm_one
    [CompleteSpace V] (hT : ContinuousOn T (uIcc a b))
    (hF : ∀ t ∈ uIcc a b, IsFredholm (T t)) (ha : Function.Bijective (T a))
    (hb : Function.Bijective (T b)) :
    detLineOrientationTransport a b hT hF
        (rayOfNeZero ℝ (((T a : V →ₗ[ℝ] V).detLineEquivOfBijective ha).symm 1)
          ((LinearEquiv.map_ne_zero_iff _).2 one_ne_zero)) =
      rayOfNeZero ℝ ((LinearMap.det (T a : V →ₗ[ℝ] V) * LinearMap.det (T b : V →ₗ[ℝ] V)) •
          ((T b : V →ₗ[ℝ] V).detLineEquivOfBijective hb).symm 1)
        (smul_ne_zero (mul_ne_zero
          ((LinearMap.isUnit_iff_isUnit_det _).1 ((Module.End.isUnit_iff _).2 ha)).ne_zero
          ((LinearMap.isUnit_iff_isUnit_det _).1 ((Module.End.isUnit_iff _).2 hb)).ne_zero)
          ((LinearEquiv.map_ne_zero_iff _).2 one_ne_zero)) := by
  have hdet {t : ℝ} (ht : Function.Bijective (T t)) : LinearMap.det (T t : V →ₗ[ℝ] V) ≠ 0 :=
    ((LinearMap.isUnit_iff_isUnit_det _).1 ((Module.End.isUnit_iff _).2 ht)).ne_zero
  -- At an invertible operator the cokernel is zero, so the sign correction is `1`, and the
  -- canonical element is `det` times the element given by invertibility.
  have hw {t : ℝ} (ht : Function.Bijective (T t)) :
      (-1 : ℝ) ^ (finrank ℝ (V ⧸ LinearMap.range (T t : V →ₗ[ℝ] V)) * (finrank ℝ V + 1)) •
          (T t : V →ₗ[ℝ] V).detLineEndEquiv.symm 1 =
        LinearMap.det (T t : V →ₗ[ℝ] V) •
          ((T t : V →ₗ[ℝ] V).detLineEquivOfBijective ht).symm 1 := by
    have h1 : (-1 : ℝ) ^ (finrank ℝ (V ⧸ LinearMap.range (T t : V →ₗ[ℝ] V)) *
        (finrank ℝ V + 1)) = 1 := by
      rw [LinearMap.finrank_quotient_range_eq_zero_of_surjective ht.2, zero_mul, pow_zero]
    rw [LinearMap.detLineEquivOfBijective_symm_one_eq_inv_det_smul, smul_smul,
      mul_inv_cancel₀ (hdet ht), one_smul, h1, one_smul]
  have key := detLineOrientationTransport_rayOfNeZero hT hF
    ((isDetLineCoherentOn_neg_one_pow_smul_detLineEndEquiv_symm_one T (uIcc a b)).smul
      (inv_ne_zero (hdet ha)))
  simp only [hw ha, hw hb, smul_smul, inv_mul_cancel₀ (hdet ha), one_smul] at key
  rw [key]
  -- The two coefficients of the element at `T b` differ by the factor `det (T a) ^ 2 > 0`.
  refine (ray_eq_iff _ _).2 ?_
  rw [show (LinearMap.det (T a : V →ₗ[ℝ] V) * LinearMap.det (T b : V →ₗ[ℝ] V)) •
      ((T b : V →ₗ[ℝ] V).detLineEquivOfBijective hb).symm 1 =
        (LinearMap.det (T a : V →ₗ[ℝ] V) * LinearMap.det (T a : V →ₗ[ℝ] V)) •
          ((LinearMap.det (T a : V →ₗ[ℝ] V))⁻¹ * LinearMap.det (T b : V →ₗ[ℝ] V)) •
            ((T b : V →ₗ[ℝ] V).detLineEquivOfBijective hb).symm 1 by
    rw [smul_smul]
    congr 1
    field_simp [hdet ha]]
  exact SameRay.sameRay_pos_smul_right _ (mul_self_pos.2 (hdet ha))

end Transport

end TauCeti
