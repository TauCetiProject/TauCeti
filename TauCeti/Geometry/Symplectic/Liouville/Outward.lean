/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import TauCeti.Geometry.Symplectic.Liouville.Domain
public import TauCeti.Geometry.Symplectic.Manifold.LiouvilleMeasure
import TauCeti.Geometry.Manifold.VectorField.Transverse
import TauCeti.Geometry.Symplectic.ExistsCompatible
import TauCeti.Geometry.Symplectic.Liouville.Scaling

/-!
# A Liouville field transverse to a connected hypersurface points outwards

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M` without boundary, with a
primitive `α`, `dα = ω`, and let `Z` be its Liouville field, `ι_Z ω = α`, assumed complete. Let
`W = {f ≤ c}` be compact, with `f` smooth along the level `Σ = f⁻¹(c)`, and suppose that `Z` is
transverse to `Σ`, `df(Z) ≠ 0` there. Then `Z` points into `W` along some components of `Σ` and out
of it along the others. If `Σ` is connected, it points outwards everywhere, so `W` is a Liouville
domain (`TauCeti.isLiouvilleDomain_setOf_le_of_isPreconnected`): the outward direction, part of
the definition of a Liouville domain `TauCeti.IsLiouvilleDomain`, follows from transversality.

The argument is by volume. On a preconnected level crossed transversally, `df(Z)` has a constant
sign (`TauCeti.forall_pos_or_forall_neg_mvfderiv_of_isPreconnected`). If `Z` pointed into `W`
along `Σ`, the forward flow `ψ` of `Z` would carry `W` into itself
(`TauCeti.apply_flowOf_lt_of_apply_le`). But a Liouville flow expands volume: since
`ψₜ^* ω = e^t ω`, it multiplies the Liouville measure `|ωⁿ / n!|` by `e^{n t}`
(`TauCeti.IsLiouvilleVectorField.liouvilleMeasure_image_globalFlow`), and a compact set with
nonempty interior has finite positive Liouville measure. So no such set is carried into itself by
a Liouville flow in positive time (`TauCeti.IsLiouvilleVectorField.not_mapsTo_globalFlow`). This
replaces the usual appeal to Stokes' theorem, `∫_Σ ι_Z(ωⁿ) = n ∫_W ωⁿ > 0`.

Connectedness cannot be dropped. In the cotangent bundle of a closed manifold with the Liouville
field `p ∂_p`, the shell `{1/2 ≤ |p| ≤ 2}` is compact, and its boundary, two cosphere bundles, is
transverse to `p ∂_p`, which points into the shell along the inner one.

The Liouville measure is built on Lindelöf manifolds, hence the Lindelöf hypothesis on `M`.

## Main results

* `TauCeti.IsLiouvilleVectorField.liouvilleMeasure_image_globalFlow`: the time-`t` map of a
  complete Liouville flow multiplies the Liouville measure by `e^{n t}`.
* `TauCeti.IsLiouvilleVectorField.not_mapsTo_globalFlow`: no compact set with nonempty interior is
  carried into itself by a Liouville flow in positive time.
* `TauCeti.isLiouvilleDomain_setOf_le_of_isPreconnected`: a compact sublevel set whose level is
  preconnected and transverse to a complete Liouville field is a Liouville domain.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Remark 1.3.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 3.5 (hypersurfaces of contact type).
-/

public section

noncomputable section

open Bundle Module MeasureTheory Set
open scoped Manifold ENNReal

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {Z : (x : M) → TangentSpace I x}

section Volume

variable [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]
  {ω : SmoothTwoForm I M}

/-- **A Liouville flow expands the Liouville measure.** Let `Z` be a complete `C¹` Liouville
vector field of the smooth two-form `ω`, `L_Z ω = ω`, on a Lindelöf manifold of dimension `2 * n`.
The time-`t` map `ψₜ` of its flow satisfies `ψₜ^* ω = e^t ω`, so it multiplies the Liouville
measure `|ωⁿ / n!|` by `e^{n t}`: `μ(ψₜ(s)) = e^{n t} μ(s)` for every set `s`. -/
theorem IsLiouvilleVectorField.liouvilleMeasure_image_globalFlow [MeasurableSpace M]
    [BorelSpace M] [LindelofSpace M] {n : ℕ} [Fact (finrank ℝ E = 2 * n)]
    (hZω : IsLiouvilleVectorField ω.val Z) (hc : IsCompleteVectorField Z)
    (hZ : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, Z y⟩ : TangentBundle I M))) (t : ℝ) (s : Set M) :
    ω.liouvilleMeasure n (globalFlow Z hZ hc t '' s) =
      ENNReal.ofReal (Real.exp (n * t)) * ω.liouvilleMeasure n s := by
  set Φ := (globalFlow Z hZ hc).toHomeomorph t
  have hΦ : MDifferentiable I I Φ :=
    (contMDiff_globalFlow_apply hc le_rfl hZ t).mdifferentiable one_ne_zero
  have hpull : mpullback I I Φ ω.val = (Real.exp t • ω).val := by
    rw [Submodule.coe_smul]
    exact hZω.mpullback_globalFlow_eq_exp_smul hc hZ ω.mdifferentiable t
  have hmp : MeasurePreserving Φ.toMeasurableEquiv
      (ENNReal.ofReal (|Real.exp t| ^ n) • ω.liouvilleMeasure n) (ω.liouvilleMeasure n) := by
    simpa using Φ.measurePreserving_liouvilleMeasure (n := n) hΦ hpull
  have hpre : Φ.toMeasurableEquiv ⁻¹' (globalFlow Z hZ hc t '' s) = s := Φ.preimage_image s
  rw [← hmp.measure_preimage_equiv, hpre, smul_apply, smul_eq_mul,
    abs_of_pos (Real.exp_pos t), ← Real.exp_natCast_mul]

/-- **No compact set is carried into itself by a Liouville flow.** Let `ω` be a nondegenerate
smooth two-form on a Lindelöf manifold of positive dimension, and `Z` a complete `C¹` Liouville
vector field of `ω`. Its flow expands the Liouville measure, so for `t > 0` the time-`t` map does
not carry a compact set with nonempty interior into itself. -/
theorem IsLiouvilleVectorField.not_mapsTo_globalFlow [LindelofSpace M] [Nontrivial E]
    (hω : ω.IsNondegenerate) (hZω : IsLiouvilleVectorField ω.val Z) (hc : IsCompleteVectorField Z)
    (hZ : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, Z y⟩ : TangentBundle I M))) {K : Set M}
    (hK : IsCompact K) (hKi : (interior K).Nonempty) {t : ℝ} (ht : 0 < t) :
    ¬MapsTo (globalFlow Z hZ hc t) K K := by
  intro hmaps
  borelize M
  -- The dimension is `2 * n` with `n ≠ 0`, since a nondegenerate form makes it even.
  obtain ⟨x₀, hx₀⟩ := hKi
  obtain ⟨n, hn⟩ := (hω.symplecticFormAt x₀).even_finrank
  have hE : finrank ℝ E = n + n := hn
  have : Fact (finrank ℝ E = 2 * n) := ⟨by rw [two_mul]; exact hE⟩
  have hn0 : 0 < n := by
    have := Module.finrank_pos (R := ℝ) (M := E)
    omega
  have := hω.isOpenPosMeasure_liouvilleMeasure (n := n)
  set μ := ω.liouvilleMeasure n
  have hfin : μ K ≠ ∞ := hK.measure_lt_top.ne
  have hpos : μ K ≠ 0 := (pos_mono interior_subset
    (isOpen_interior.measure_pos μ ⟨x₀, hx₀⟩)).ne'
  -- `e^{n t} μ(K) = μ(ψₜ(K)) ≤ μ(K)`, impossible for `t > 0` and `0 < μ(K) < ∞`.
  have hle : ENNReal.ofReal (Real.exp (n * t)) * μ K ≤ 1 * μ K := by
    rw [one_mul, ← hZω.liouvilleMeasure_image_globalFlow hc hZ]
    exact measure_mono (image_subset_iff.2 hmaps)
  have h1 := (ENNReal.mul_le_mul_iff_left hpos hfin).1 hle
  rw [ENNReal.ofReal_le_one, Real.exp_le_one_iff] at h1
  exact (mul_pos (Nat.cast_pos.2 hn0) ht).not_ge h1

end Volume

section Domain

variable [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]
  {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1} {f : M → ℝ} {c : ℝ}

/-- **A Liouville field transverse to a connected level points outwards.** Let `ω` be a
nondegenerate two-form on a Lindelöf manifold without boundary, `α` a primitive, `dα = ω`, and
`Z` its Liouville field, `ι_Z ω = α`, smooth and complete. Let `W = {f ≤ c}` be compact, with `f`
continuous, smooth along the level `f⁻¹(c)`, and `Z` transverse to that level, `df(Z) ≠ 0` there.
If the level is preconnected, then `Z` points out of `W` along it, so `W` is a Liouville domain.
Without connectedness this fails: `Z` may point into `W` along some components of the level. -/
theorem isLiouvilleDomain_setOf_le_of_isPreconnected [LindelofSpace M] (hω : ω.IsNondegenerate)
    (hdα : mextDeriv α.val = ω.val) (hZ : ContMDiff I I.tangent (⊤ : ℕ∞) (T% Z))
    (hZα : RoughForm.interior Z ω.val = α.val) (hc : IsCompleteVectorField Z) (hf : Continuous f)
    (hW : IsCompact {x | f x ≤ c}) (hfc : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ) (⊤ : ℕ∞) f x)
    (htr : ∀ x, f x = c → mvfderiv I f x (Z x) ≠ 0) (hconn : IsPreconnected {x | f x = c}) :
    IsLiouvilleDomain ω α {x | f x ≤ c} := by
  have hZ1 : ContMDiff I I.tangent 1 (T% Z) := hZ.of_le (by simp)
  have hfc1 : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ) 1 f x := fun x hx ↦ (hfc x hx).of_le (by simp)
  -- If `Z` points outwards along the level, `W` is a Liouville domain by definition.
  have hout (hpos : ∀ x, f x = c → 0 < mvfderiv I f x (Z x)) :
      IsLiouvilleDomain ω α {x | f x ≤ c} :=
    ⟨hω, hdα, hW, by simp [ModelWithCorners.interior_eq_univ],
      ⟨Z, hZ, hZα, f, c, hf, rfl, fun x hx ↦ ⟨hfc x hx, hpos x hx⟩⟩⟩
  rcases forall_pos_or_forall_neg_mvfderiv_of_isPreconnected hZ.continuous hfc1 htr hconn with
    hpos | hneg
  · exact hout hpos
  rcases {x | f x = c}.eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
  · exact hout fun x hx ↦ ((eq_empty_iff_forall_notMem.1 hempty) x hx).elim
  -- Otherwise `Z` points into `W` along the level, and its forward flow carries `W` into the open
  -- set `{f < c}`, a contradiction with the expansion of volume.
  exfalso
  have hx₀ : f x₀ = c := hx₀
  have : Nontrivial E :=
    ⟨⟨Z x₀, 0, fun h0 ↦ htr x₀ hx₀ (by rw [h0]; exact (mvfderiv I f x₀).map_zero)⟩⟩
  have hlt : ∀ x, f x ≤ c → f (globalFlow Z hZ1 hc 1 x) < c := fun x hx ↦ by
    rw [← flowOf_eq_globalFlow hZ1 hc]
    exact apply_flowOf_lt_of_apply_le hZ1 hf
      (fun y hy ↦ ⟨(hfc y hy).mdifferentiableAt (by simp), hneg y hy⟩) hx one_pos
      (hc.mem_flowDomain 1 x)
  have hint : (interior {x | f x ≤ c}).Nonempty :=
    ⟨_, interior_maximal (fun _ hy ↦ le_of_lt hy) (isOpen_lt hf continuous_const)
      (hlt x₀ hx₀.le)⟩
  have hZω : IsLiouvilleVectorField ω.val Z := by
    have := isLiouvilleVectorField_mextDeriv_of_interior_eq (α.isSmoothForm.of_le (by simp))
      (hZ.mdifferentiable (by simp)) (by rw [hdα, hZα])
    rwa [hdα] at this
  exact hZω.not_mapsTo_globalFlow hω hc hZ1 hW hint one_pos fun x hx ↦ (hlt x hx).le

end Domain

end TauCeti
