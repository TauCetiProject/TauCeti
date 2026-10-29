/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.VectorField.MappingTorus

/-!
# Closed orbits of the suspension flow through periodic points

Let `φ : M ≃ₘ⟮I, I⟯ M` be a diffeomorphism and `Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` its
smooth mapping torus (`TauCeti.SmoothMappingTorus φ`). If `x` is a periodic point of `φ` of period
`n`, that is `φ^[n] x = x`, then `t ↦ [t, x]` has period `n` because `[t + n, x] = [t, φ^[n] x]`,
so it descends to the closed curve

`γ : ℝ / nℤ → Y_φ`, `γ [t] = [t, x]`

(`TauCeti.SmoothMappingTorus.closedOrbit φ hx`). It traces the orbit of the suspension flow
`[t, x] ↦ [t + s, x]` through `[0, x]`, and its velocity is the suspension vector field `T = ∂_t`
of `Y_φ`, so it is a closed integral curve of `T`.

The curve `γ` is injective exactly when `n` is the least period of `x`: two parameters with the
same image differ by a period of the flow line, and these are the multiples of the least period
of `x` (`TauCeti.SmoothMappingTorus.isFixedPt_flow_mk_iff_mem_zmultiples`). Since its velocity `T`
is sent to `1` by the differential of the projection `p : Y_φ → ℝ / ℤ`, `γ` is an immersion; as a
continuous injection out of a compact circle it is then a closed smooth embedding. So the orbit
through a point of least period `d > 0` is a primitive embedded closed orbit of `T` of period `d`.
It meets the fibre `p⁻¹ [t]` in the `d` distinct points `[t, φ^[k] x]`, `0 ≤ k < d`, which are the
fibre coordinates of the orbit of `x` under `φ`. Starting at another point `φ^[k] x` of the same
orbit gives the same curve precomposed with the rotation by `k`, so the same image traversed
in the same direction.

Whatever the period `n`, the image of `γ` is the flow line through `[0, x]`; so for `n` a
multiple `k d` of the least period `d` with `k > 1`, `γ` is a non-injective parametrization of
the same closed orbit.

## Main definitions

* `TauCeti.SmoothMappingTorus.closedOrbit φ hx`: for `hx : IsPeriodicPt φ n x`, the closed orbit
  `ℝ / nℤ → Y_φ`, `[t] ↦ [t, x]`.

## Main results

* `TauCeti.SmoothMappingTorus.closedOrbit_coe`: `γ [t] = [t, x]`.
* `TauCeti.SmoothMappingTorus.closedOrbit_add_coe`, `TauCeti.SmoothMappingTorus.range_closedOrbit`:
  `γ (θ + s) = Φ_s (γ θ)` for the suspension flow `Φ`, so the image of `γ` is the flow line
  through `[0, x]`, whatever the period `n`.
* `TauCeti.SmoothMappingTorus.closedOrbit_apply_iterate`: changing the starting point to
  `φ^[k] x` rotates the parameter by `k`.
* `TauCeti.SmoothMappingTorus.closedOrbit_injective_iff`: `γ` is injective exactly when `n` is
  the least period of `x`.
* `TauCeti.SmoothMappingTorus.contMDiff_closedOrbit`,
  `TauCeti.SmoothMappingTorus.mfderiv_closedOrbit`: `γ` is smooth with velocity the field `T`.
* `TauCeti.SmoothMappingTorus.mfderiv_proj_comp_mfderiv_closedOrbit`,
  `TauCeti.SmoothMappingTorus.isImmersion_closedOrbit`: `dp ∘ dγ = id`, so `γ` is an immersion.
* `TauCeti.SmoothMappingTorus.isClosedEmbedding_closedOrbit`,
  `TauCeti.SmoothMappingTorus.isSmoothEmbedding_closedOrbit`: for `n` the positive least period,
  `γ` is a closed embedding and a smooth embedding.
* `TauCeti.SmoothMappingTorus.range_closedOrbit_inter_proj_preimage`: `γ` meets the fibre over
  `[t]` in the points `[t, φ^[k] x]`, `k < n`; these are distinct when `n` is the least period
  (`TauCeti.SmoothMappingTorus.injOn_mk_iterate`).

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354 (closed orbits of the mapping torus flow and periodic
  points of the monodromy).
-/

public section

noncomputable section

open Set Function Topology Manifold
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section Topology

variable {m : ℕ∞ω} (φ : M ≃ₘ^m⟮I, I⟯ M) {n : ℕ} {x : M}

/-- For a periodic point `x` of `φ` of period `n`, the map `t ↦ [t, x]` has period `n`. -/
theorem periodic_mk (hx : IsPeriodicPt φ n x) : Periodic (fun t : ℝ ↦ mk φ t x) n := fun t ↦ by
  have h := mk_add_intCast φ t n x
  rwa [Int.cast_natCast, zpow_natCast, Diffeomorph.coe_pow, hx.eq] at h

/-- The closed orbit `γ : ℝ / nℤ → Y_φ`, `[t] ↦ [t, x]`, of the suspension flow through a
periodic point `x` of `φ` of period `n`. It is injective exactly when `n` is the least period of
`x` (`TauCeti.SmoothMappingTorus.closedOrbit_injective_iff`), and its image is the flow line
through `[0, x]` whatever the period `n` (`TauCeti.SmoothMappingTorus.range_closedOrbit`). -/
def closedOrbit (hx : IsPeriodicPt φ n x) : AddCircle (n : ℝ) → SmoothMappingTorus φ :=
  (periodic_mk φ hx).lift

variable {φ}

/-- The closed orbit sends the class of `t` to `[t, x]`. -/
@[simp]
theorem closedOrbit_coe (hx : IsPeriodicPt φ n x) (t : ℝ) :
    closedOrbit φ hx t = mk φ t x :=
  (periodic_mk φ hx).lift_coe t

/-- The closed orbit sends the class of `t + k` to the point `[t, φ^[k] x]` of the fibre at
height `t`. -/
theorem closedOrbit_coe_add_natCast (hx : IsPeriodicPt φ n x) (t : ℝ) (k : ℕ) :
    closedOrbit φ hx ↑(t + k) = mk φ t (φ^[k] x) := by
  rw [closedOrbit_coe, ← Diffeomorph.coe_pow, ← zpow_natCast, ← mk_add_intCast, Int.cast_natCast]

/-- The closed orbit traces the suspension flow: `γ (θ + s) = Φ_s (γ θ)`. -/
theorem closedOrbit_add_coe (hx : IsPeriodicPt φ n x) (θ : AddCircle (n : ℝ)) (s : ℝ) :
    closedOrbit φ hx (θ + (s : AddCircle (n : ℝ))) = flow φ s (closedOrbit φ hx θ) := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  rw [← AddCircle.coe_add, closedOrbit_coe, closedOrbit_coe, flow_mk]

/-- The image of the closed orbit is the orbit of `[0, x]` under the suspension flow. -/
theorem range_closedOrbit (hx : IsPeriodicPt φ n x) :
    range (closedOrbit φ hx) = range fun s : ℝ ↦ flow φ s (mk φ 0 x) := by
  rw [← (QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (n : ℝ))).range_comp]
  congr 1
  funext s
  simp only [comp_apply, closedOrbit_coe, flow_mk, zero_add]

/-- Starting the closed orbit at the point `φ^[k] x` of the orbit of `x` rotates its parameter by
`k`. So the closed orbits through the points of one periodic orbit of `φ` have the same image,
traversed in the same direction. -/
theorem closedOrbit_apply_iterate (hx : IsPeriodicPt φ n x) (k : ℕ) (θ : AddCircle (n : ℝ)) :
    closedOrbit φ (hx.apply_iterate k) θ =
      closedOrbit φ hx (θ + ((k : ℝ) : AddCircle (n : ℝ))) := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  rw [← AddCircle.coe_add, closedOrbit_coe, closedOrbit_coe_add_natCast]

/-- The closed orbits through the points of one periodic orbit of `φ` have the same image. -/
theorem range_closedOrbit_apply_iterate (hx : IsPeriodicPt φ n x) (k : ℕ) :
    range (closedOrbit φ (hx.apply_iterate k)) = range (closedOrbit φ hx) := by
  rw [funext (closedOrbit_apply_iterate hx k)]
  exact (Equiv.addRight ((k : ℝ) : AddCircle (n : ℝ))).surjective.range_comp _

/-- Two parameters of the closed orbit have the same image exactly when they differ by an integer
multiple of the least period of `x`. -/
theorem closedOrbit_coe_eq_closedOrbit_coe_iff (hx : IsPeriodicPt φ n x) {s t : ℝ} :
    closedOrbit φ hx s = closedOrbit φ hx t ↔
      t - s ∈ AddSubgroup.zmultiples (minimalPeriod φ x : ℝ) := by
  rw [closedOrbit_coe, closedOrbit_coe, ← isFixedPt_flow_mk_iff_mem_zmultiples (t := s),
    IsFixedPt, flow_mk, add_sub_cancel, eq_comm]

/-- The closed orbit through a periodic point of period `n` is injective exactly when `n` is the
least period of the point. For `n = 0` this says that the flow line `t ↦ [t, x]` is injective
exactly when `x` is not a periodic point. -/
theorem closedOrbit_injective_iff (hx : IsPeriodicPt φ n x) :
    Injective (closedOrbit φ hx) ↔ minimalPeriod φ x = n := by
  constructor
  · intro h
    -- The parameters `0` and `d`, for `d` the least period, have the same image, so `n ∣ d`.
    have h₀ := (closedOrbit_coe_eq_closedOrbit_coe_iff hx (s := 0)
      (t := minimalPeriod φ x)).2 (by simp)
    obtain ⟨k, hk⟩ :=
      AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq_iff_sub_mem.1 (h h₀))
    have hk' : ((-k * n : ℤ) : ℝ) = ((minimalPeriod φ x : ℤ) : ℝ) := by
      rw [zsmul_eq_mul] at hk
      push_cast
      linarith
    exact Nat.dvd_antisymm hx.minimalPeriod_dvd
      (Int.natCast_dvd_natCast.1 (Dvd.intro_left (-k) (Int.cast_injective hk')))
  · intro h θ θ' hθ
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective θ
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ'
    rw [closedOrbit_coe_eq_closedOrbit_coe_iff, h] at hθ
    refine QuotientAddGroup.eq_iff_sub_mem.2 ?_
    rw [← neg_sub]
    exact neg_mem hθ

/-- The closed orbit is continuous. -/
theorem continuous_closedOrbit (hx : IsPeriodicPt φ n x) : Continuous (closedOrbit φ hx) :=
  continuous_quot_lift _ ((continuous_uncurry_mk φ).comp (continuous_id.prodMk continuous_const))

/-- The closed orbit meets the fibre over the class of `t` in the points `[t, φ^[k] x]`,
`k < n`. -/
theorem range_closedOrbit_inter_proj_preimage (hx : IsPeriodicPt φ n x) (hn : 0 < n) (t : ℝ) :
    range (closedOrbit φ hx) ∩ proj φ ⁻¹' {(t : UnitAddCircle)} =
      (fun k : ℕ ↦ mk φ t (φ^[k] x)) '' Iio n := by
  ext y
  simp only [mem_inter_iff, mem_range, mem_preimage, mem_singleton_iff, mem_image, mem_Iio]
  constructor
  · rintro ⟨⟨θ, rfl⟩, hy⟩
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective θ
    rw [closedOrbit_coe, proj_mk, QuotientAddGroup.eq_iff_sub_mem] at hy
    -- Write `s = t + j` with `j` an integer, and reduce `j` modulo `n` to `r = j - n q`.
    obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.1 hy
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    have hr₀ : 0 ≤ j % n := Int.emod_nonneg j hn'.ne'
    have hr₁ : j % n < n := Int.emod_lt_of_pos j hn'
    have hr : ((j % n).toNat : ℝ) = j - n * (j / n : ℤ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hr₀, Int.emod_def]
      push_cast
      ring
    refine ⟨(j % n).toNat, by omega, ?_⟩
    rw [← closedOrbit_coe_add_natCast hx]
    refine congrArg (closedOrbit φ hx)
      (QuotientAddGroup.eq_iff_sub_mem.2 (AddSubgroup.mem_zmultiples_iff.2 ⟨-(j / n), ?_⟩))
    rw [zsmul_eq_mul] at hj ⊢
    rw [hr]
    push_cast
    linarith
  · rintro ⟨k, -, rfl⟩
    exact ⟨⟨↑(t + k), closedOrbit_coe_add_natCast hx t k⟩, proj_mk φ t _⟩

/-- The points `[t, φ^[k] x]`, `k` less than the least period of `x`, are distinct. -/
theorem injOn_mk_iterate (t : ℝ) :
    InjOn (fun k : ℕ ↦ mk φ t (φ^[k] x)) (Iio (minimalPeriod φ x)) :=
  (mk_injective φ t).comp_injOn iterate_injOn_Iio_minimalPeriod

end Topology

section Smooth

variable [T2Space M] [LocallyCompactSpace M] {m : ℕ∞ω} [IsManifold I m M] {φ : M ≃ₘ^m⟮I, I⟯ M}
  {n : ℕ} [Fact (0 < (n : ℝ))] {x : M}

/-- The closed orbit of the mapping torus of a `C^m` diffeomorphism is `C^m`. -/
theorem contMDiff_closedOrbit (hx : IsPeriodicPt φ n x) :
    ContMDiff 𝓘(ℝ) (𝓘(ℝ).prod I) m (closedOrbit φ hx) := by
  rw [← (AddCircle.isLocalDiffeomorph_coe (n : ℝ) m).contMDiff_comp_iff
    QuotientAddGroup.mk_surjective le_rfl]
  have h : closedOrbit φ hx ∘ ((↑) : ℝ → AddCircle (n : ℝ)) = fun t ↦ mk φ t x :=
    funext (closedOrbit_coe hx)
  rw [h]
  exact (contMDiff_uncurry_mk φ).comp (contMDiff_id.prodMk contMDiff_const)

omit [IsManifold I m M] in
/-- When `n` is the least period of `x`, the closed orbit is a closed topological embedding: it
is a continuous injection out of a compact circle into a Hausdorff space. -/
theorem isClosedEmbedding_closedOrbit (hx : IsPeriodicPt φ n x) (h : minimalPeriod φ x = n) :
    IsClosedEmbedding (closedOrbit φ hx) :=
  (continuous_closedOrbit hx).isClosedEmbedding ((closedOrbit_injective_iff hx).2 h)

end Smooth

section Manifold

variable [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] {φ : M ≃ₘ⟮I, I⟯ M} {n : ℕ}
  [Fact (0 < (n : ℝ))] {x : M}

/-- The velocity of the closed orbit is the suspension vector field `T`: the orbit is a closed
integral curve of `T`. -/
theorem mfderiv_closedOrbit (hx : IsPeriodicPt φ n x) (θ : AddCircle (n : ℝ)) :
    mfderiv 𝓘(ℝ) (𝓘(ℝ).prod I) (closedOrbit φ hx) θ (1 : ℝ) =
      timeVectorField φ (closedOrbit φ hx θ) := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  have hd := (contMDiff_closedOrbit hx).mdifferentiableAt (x := (t : AddCircle (n : ℝ)))
    (by simp)
  rw [← AddCircle.mfderiv_comp_coe hd]
  have h : closedOrbit φ hx ∘ ((↑) : ℝ → AddCircle (n : ℝ)) = fun s ↦ flow φ s (mk φ 0 x) := by
    funext s
    simp
  have ht : closedOrbit φ hx t = flow φ t (mk φ 0 x) := by simp
  rw [h, ((isMIntegralCurve_flow φ (mk φ 0 x)) t).mfderiv, ht]
  -- `smulRight 1 v` sends `1` to `1 • v`.
  exact one_smul ℝ _

/-- The projection to the circle undoes the differential of the closed orbit: `dp ∘ dγ = id`,
since the velocity of `γ` is the field `T` and `dp(T) = 1`. -/
theorem mfderiv_proj_comp_mfderiv_closedOrbit (hx : IsPeriodicPt φ n x) (θ : AddCircle (n : ℝ)) :
    (mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) (closedOrbit φ hx θ)).comp
      (mfderiv 𝓘(ℝ) (𝓘(ℝ).prod I) (closedOrbit φ hx) θ) = ContinuousLinearMap.id ℝ ℝ := by
  refine ContinuousLinearMap.ext_ring ?_
  have h := mfderiv_proj_timeVectorField φ (closedOrbit φ hx θ)
  rw [← mfderiv_closedOrbit hx θ] at h
  -- The composite applied to `1` is `dp (dγ 1)`, and the identity sends `1` to `1`; `rw` cannot
  -- unfold the composite, as the tangent lines are only definitionally equal to `ℝ`.
  exact h

/-- The differential of the closed orbit is injective. -/
theorem injective_mfderiv_closedOrbit (hx : IsPeriodicPt φ n x) (θ : AddCircle (n : ℝ)) :
    Injective (mfderiv 𝓘(ℝ) (𝓘(ℝ).prod I) (closedOrbit φ hx) θ) :=
  LeftInverse.injective (g := mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) (closedOrbit φ hx θ))
    fun a ↦ DFunLike.congr_fun (mfderiv_proj_comp_mfderiv_closedOrbit hx θ) a

section Embedding

variable [FiniteDimensional ℝ E] [I.Boundaryless]

/-- The closed orbit is an immersion. -/
theorem isImmersion_closedOrbit (hx : IsPeriodicPt φ n x) :
    IsImmersion 𝓘(ℝ) (𝓘(ℝ).prod I) ∞ (closedOrbit φ hx) :=
  isImmersion_iff_forall_isImmersionAt.2 fun θ ↦
    ((contMDiff_closedOrbit hx).contMDiffOn.isImmersionAt_iff_injective_mfderiv isOpen_univ
      (mem_univ θ) (by simp)).2 (injective_mfderiv_closedOrbit hx θ)

/-- When `n` is the least period of `x`, the closed orbit is a smooth embedding: the orbit of the
suspension flow through `[0, x]` is a primitive embedded closed orbit of period `n`. -/
theorem isSmoothEmbedding_closedOrbit (hx : IsPeriodicPt φ n x) (h : minimalPeriod φ x = n) :
    IsSmoothEmbedding 𝓘(ℝ) (𝓘(ℝ).prod I) ∞ (closedOrbit φ hx) :=
  ⟨isImmersion_closedOrbit hx, (isClosedEmbedding_closedOrbit hx h).isEmbedding⟩

end Embedding

end Manifold

end SmoothMappingTorus

end TauCeti
