/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Immersion.Basic
public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.VectorField.MappingTorus

/-!
# Closed orbits of the suspension flow of a smooth mapping torus

Let `φ` be a diffeomorphism of a manifold `M` and `Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` its
smooth mapping torus (`TauCeti.SmoothMappingTorus φ`), with suspension flow `[t, x] ↦ [t + s, x]`
and vector field `T = ∂_t`. A point `x` with `φ^[d] x = x` gives the closed curve

`γ : ℝ / dℤ → Y_φ`,  `γ [t] = [t, x]`,

the orbit of the suspension flow through `[0, x]` parametrized by its time
(`TauCeti.SmoothMappingTorus.closedOrbit φ hx`). This file develops the basic API of these curves.

* `γ` is a smooth closed integral curve of `T`, and its image is the orbit of the suspension flow
  through `[0, x]`. It is injective exactly when `d` is the minimal period of `x`; it is then a
  closed embedding of the circle `ℝ / dℤ`, and a smooth embedding when `M` is finite-dimensional
  and modelled without boundary.
* It meets each fibre `{[t, y]}` of the projection `Y_φ → ℝ / ℤ` in exactly the points
  `[t, x], [t, φ x], …, [t, φ^[m - 1] x]`, where `m` is the minimal period of `x`; these are `m`
  distinct points.
* Starting from `φ^[j] x` instead of `x` rotates the parametrization: the curve of `φ^[j] x` is
  the curve of `x` precomposed with the translation by `j` of `ℝ / dℤ`. So the starting points of
  one periodic orbit of `φ` all give the same oriented image, and two periodic points give the same
  image exactly when they lie on the same orbit of `φ`; otherwise the images are disjoint.

When `φ` preserves a symplectic form on `M`, the products of these curves with the circle are
the embedded tori in the symplectic manifold `S¹ × Y_φ` attached to the periodic orbits of `φ`,
as in periodic Floer homology.

## Main definitions

* `TauCeti.SmoothMappingTorus.closedOrbit φ hx`: for `hx : IsPeriodicPt φ d x`, the curve
  `ℝ / dℤ → Y_φ`, `[t] ↦ [t, x]`.

## Main results

* `TauCeti.SmoothMappingTorus.injective_closedOrbit_iff`: the curve is injective exactly when `d`
  is the minimal period of `x`.
* `TauCeti.SmoothMappingTorus.range_closedOrbit`: its image is the orbit of the suspension flow
  through `[0, x]`.
* `TauCeti.SmoothMappingTorus.closedOrbit_apply_iterate`,
  `TauCeti.SmoothMappingTorus.range_closedOrbit_eq_iff`,
  `TauCeti.SmoothMappingTorus.disjoint_range_closedOrbit_iff`: change of starting point, and the
  images of two closed orbits.
* `TauCeti.SmoothMappingTorus.range_closedOrbit_inter_preimage_proj`,
  `TauCeti.SmoothMappingTorus.ncard_range_closedOrbit_inter_preimage_proj`: the intersection with
  a fibre is `{[t, φ^[j] x] | j < m}`, and has `m` points.
* `TauCeti.SmoothMappingTorus.hasMFDerivAt_closedOrbit`: the curve is an integral curve of `T`.
* `TauCeti.SmoothMappingTorus.isClosedEmbedding_closedOrbit`,
  `TauCeti.SmoothMappingTorus.isSmoothEmbedding_closedOrbit`: for the minimal period, the curve
  is a closed embedding, and a smooth embedding.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354 (periodic orbits of a mapping torus and the tori they
  give in its product with a circle).
-/

public noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

section Topology

variable (φ : M ≃ₘ^n⟮I, I⟯ M) {x : M} {d : ℕ}

/-- For a periodic point `x` of `φ` with period `d`, the curve `t ↦ [t, x]` is `d`-periodic. -/
theorem periodic_mk (hx : IsPeriodicPt φ d x) : Periodic (fun t ↦ mk φ t x) d := fun t ↦ by
  refine (mk_eq_mk_iff_sub_mem_zmultiples φ).2 ?_
  obtain ⟨k, hk⟩ := hx.minimalPeriod_dvd
  refine AddSubgroup.mem_zmultiples_iff.2 ⟨k, ?_⟩
  simp [hk, zsmul_eq_mul, mul_comm]

/-- The closed orbit of the suspension flow through `[0, x]`, for a periodic point `x` of `φ` with
period `d`: the curve `ℝ / dℤ → Y_φ`, `[t] ↦ [t, x]`. It is injective exactly when `d` is the
minimal period of `x` (`TauCeti.SmoothMappingTorus.injective_closedOrbit_iff`). -/
def closedOrbit (hx : IsPeriodicPt φ d x) : AddCircle (d : ℝ) → SmoothMappingTorus φ :=
  (periodic_mk φ hx).lift

variable (hx : IsPeriodicPt φ d x)

/-- The closed orbit sends the class of `t` to `[t, x]`. -/
@[simp]
theorem closedOrbit_coe (t : ℝ) : closedOrbit φ hx t = mk φ t x := (rfl)

/-- Read on the real line, the closed orbit is the curve `t ↦ [t, x]`. -/
@[simp]
theorem closedOrbit_comp_coe :
    closedOrbit φ hx ∘ ((↑) : ℝ → AddCircle (d : ℝ)) = fun t ↦ mk φ t x := (rfl)

/-- The closed orbit is injective exactly when its period `d` is the minimal period of `x`. -/
theorem injective_closedOrbit_iff : Injective (closedOrbit φ hx) ↔ minimalPeriod φ x = d := by
  constructor
  · intro h
    -- The classes of the minimal period and of `0` have the same image, so `d` divides the
    -- minimal period.
    have h₀ : ((minimalPeriod φ x : ℝ) : AddCircle (d : ℝ)) = ((0 : ℝ) : AddCircle (d : ℝ)) :=
      h (by
        rw [closedOrbit_coe, closedOrbit_coe, mk_eq_mk_iff_sub_mem_zmultiples, sub_zero]
        exact AddSubgroup.mem_zmultiples _)
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq_iff_sub_mem.1 h₀)
    have hk' : (minimalPeriod φ x : ℝ) = (d : ℝ) * k := by
      simpa [zsmul_eq_mul, mul_comm] using hk.symm
    have hdvd : d ∣ minimalPeriod φ x :=
      Int.natCast_dvd_natCast.1 ⟨k, by exact_mod_cast hk'⟩
    exact Nat.dvd_antisymm hx.minimalPeriod_dvd hdvd
  · intro hd θ θ' h
    induction θ using QuotientAddGroup.induction_on
    induction θ' using QuotientAddGroup.induction_on
    rw [closedOrbit_coe, closedOrbit_coe, mk_eq_mk_iff_sub_mem_zmultiples, hd] at h
    exact QuotientAddGroup.eq_iff_sub_mem.2 h

/-- The closed orbit is continuous. -/
theorem continuous_closedOrbit : Continuous (closedOrbit φ hx) := by
  rw [(QuotientAddGroup.isQuotientMap_mk _).continuous_iff, closedOrbit_comp_coe]
  exact (continuous_uncurry_mk φ).comp (continuous_id.prodMk continuous_const)

/-- The suspension flow moves along the closed orbit: the time-`s` map sends `γ θ` to
`γ (θ + s)`. -/
@[simp]
theorem flow_closedOrbit (s : ℝ) (θ : AddCircle (d : ℝ)) :
    flow φ s (closedOrbit φ hx θ) = closedOrbit φ hx (θ + s) := by
  induction θ using QuotientAddGroup.induction_on
  rw [closedOrbit_coe, flow_mk, ← QuotientAddGroup.mk_add, closedOrbit_coe]

/-- The image of the closed orbit is the orbit of the suspension flow through `[0, x]`; in
particular it does not depend on the chosen period `d`. -/
theorem range_closedOrbit : range (closedOrbit φ hx) = (flow φ).orbit (mk φ 0 x) := by
  ext z
  rw [Flow.mem_orbit_iff]
  constructor
  · rintro ⟨θ, rfl⟩
    induction θ using QuotientAddGroup.induction_on with | H t => exact ⟨t, by simp⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, by simp⟩

/-- Starting the closed orbit at `φ^[j] x` instead of `x` rotates its parametrization by `j`. -/
theorem closedOrbit_apply_iterate (j : ℕ) (θ : AddCircle (d : ℝ)) :
    closedOrbit φ (hx.apply_iterate j) θ = closedOrbit φ hx (θ + (j : ℝ)) := by
  induction θ using QuotientAddGroup.induction_on
  rw [← QuotientAddGroup.mk_add, closedOrbit_coe, closedOrbit_coe, mk_add_natCast]

/-- The closed orbits through the points `φ^[j] x` of one periodic orbit of `φ` all have the same
image. -/
theorem range_closedOrbit_apply_iterate (j : ℕ) :
    range (closedOrbit φ (hx.apply_iterate j)) = range (closedOrbit φ hx) := by
  have h : closedOrbit φ (hx.apply_iterate j) =
      closedOrbit φ hx ∘ (· + ((j : ℝ) : AddCircle (d : ℝ))) :=
    funext (closedOrbit_apply_iterate φ hx j)
  rw [h]
  exact (Equiv.addRight _).surjective.range_comp _

variable [Fact (0 < (d : ℝ))]

include hx in
/-- A periodic point of positive period has positive minimal period. -/
private theorem minimalPeriod_pos : 0 < minimalPeriod φ x :=
  hx.minimalPeriod_pos (Nat.cast_pos.1 (Fact.out : (0 : ℝ) < d))

/-- The point `[t, y]` lies on the closed orbit of `x` exactly when `y` lies on the forward orbit
of `x` under `φ`. -/
theorem mk_mem_range_closedOrbit_iff {t : ℝ} {y : M} :
    mk φ t y ∈ range (closedOrbit φ hx) ↔ ∃ j : ℕ, (⇑φ)^[j] x = y := by
  constructor
  · rintro ⟨θ, hθ⟩
    induction θ using QuotientAddGroup.induction_on
    rw [closedOrbit_coe, mk_eq_mk_iff] at hθ
    obtain ⟨k, -, hk⟩ := hθ
    -- So `y = φ ^ k x`, and the integer power is a forward iterate since `x` is periodic.
    have hpos : (0 : ℤ) < minimalPeriod φ x :=
      Nat.cast_pos.2 (minimalPeriod_pos φ hx)
    refine ⟨(k % minimalPeriod φ x).toNat, ?_⟩
    rw [← Diffeomorph.coe_pow, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hpos.ne')]
    refine (MulAction.zpow_smul_mod_minimalPeriod φ x k).trans ?_
    rw [Diffeomorph.smul_def, hk, zpow_neg]
    exact (φ ^ k).apply_symm_apply y
  · rintro ⟨j, rfl⟩
    exact ⟨((t + j : ℝ) : AddCircle (d : ℝ)), by rw [closedOrbit_coe, mk_add_natCast]⟩

/-- A fibre `{[t, y]}` of the projection to the circle meets the closed orbit of `x` exactly in the
points `[t, φ^[j] x]` with `j` less than the minimal period of `x`. -/
theorem range_closedOrbit_inter_preimage_proj (t : ℝ) :
    range (closedOrbit φ hx) ∩ proj φ ⁻¹' {(t : UnitAddCircle)} =
      range fun j : Fin (minimalPeriod φ x) ↦ mk φ t ((⇑φ)^[j] x) := by
  have hpos := minimalPeriod_pos φ hx
  rw [← range_mk]
  ext z
  constructor
  · rintro ⟨hz, y, rfl⟩
    obtain ⟨j, rfl⟩ := (mk_mem_range_closedOrbit_iff φ hx).1 hz
    exact ⟨⟨j % minimalPeriod φ x, Nat.mod_lt _ hpos⟩, by simp [iterate_mod_minimalPeriod_eq]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨(mk_mem_range_closedOrbit_iff φ hx).2 ⟨j, rfl⟩, mem_range_self _⟩

/-- The closed orbit of `x` meets each fibre of the projection to the circle in exactly as many
points as the minimal period of `x`. -/
theorem ncard_range_closedOrbit_inter_preimage_proj (t : ℝ) :
    (range (closedOrbit φ hx) ∩ proj φ ⁻¹' {(t : UnitAddCircle)}).ncard = minimalPeriod φ x := by
  rw [range_closedOrbit_inter_preimage_proj, ncard_range_of_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  exact (mk_injective φ t).comp fun i j h ↦ Fin.ext (iterate_injOn_Iio_minimalPeriod i.2 j.2 h)

variable {y : M} {e : ℕ} (hy : IsPeriodicPt φ e y)

/-- Two closed orbits have the same image exactly when their starting points lie on the same
orbit of `φ`. -/
theorem range_closedOrbit_eq_iff :
    range (closedOrbit φ hx) = range (closedOrbit φ hy) ↔ ∃ j : ℕ, (⇑φ)^[j] x = y := by
  constructor
  · intro h
    rw [← mk_mem_range_closedOrbit_iff φ hx (t := 0), h]
    exact ⟨0, closedOrbit_coe φ hy 0⟩
  · rintro ⟨j, rfl⟩
    rw [← range_closedOrbit_apply_iterate φ hx j, range_closedOrbit, range_closedOrbit]

/-- Two closed orbits have disjoint images exactly when their starting points lie on different
orbits of `φ`. -/
theorem disjoint_range_closedOrbit_iff [Fact (0 < (e : ℝ))] :
    Disjoint (range (closedOrbit φ hx)) (range (closedOrbit φ hy)) ↔ ¬∃ j : ℕ, (⇑φ)^[j] x = y := by
  rw [← range_closedOrbit_eq_iff φ hx hy]
  constructor
  · intro h heq
    exact (range_nonempty (closedOrbit φ hy)).ne_empty (disjoint_self.1 (heq ▸ h))
  · intro h
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨θ, rfl⟩ hθ
    induction θ using QuotientAddGroup.induction_on
    rw [closedOrbit_coe, mk_mem_range_closedOrbit_iff φ hy, ← range_closedOrbit_eq_iff φ hy hx]
      at hθ
    exact h hθ.symm

/-- For the minimal period, the closed orbit is a closed embedding of the circle `ℝ / dℤ`. -/
theorem isClosedEmbedding_closedOrbit [T2Space M] [LocallyCompactSpace M]
    (h : minimalPeriod φ x = d) : Topology.IsClosedEmbedding (closedOrbit φ hx) :=
  (continuous_closedOrbit φ hx).isClosedEmbedding ((injective_closedOrbit_iff φ hx).2 h)

end Topology

section Smooth

variable [T2Space M] [LocallyCompactSpace M] [IsManifold I n M]
  (φ : M ≃ₘ^n⟮I, I⟯ M) {x : M} {d : ℕ} (hx : IsPeriodicPt φ d x) [Fact (0 < (d : ℝ))]

/-- The closed orbit is a `C^n` curve. -/
theorem contMDiff_closedOrbit : ContMDiff 𝓘(ℝ) (𝓘(ℝ).prod I) n (closedOrbit φ hx) := by
  rw [← (AddCircle.isLocalDiffeomorph_coe (d : ℝ) n).contMDiff_comp_iff
    QuotientAddGroup.mk_surjective le_rfl]
  rw [closedOrbit_comp_coe]
  exact (contMDiff_uncurry_mk φ).comp (contMDiff_id.prodMk contMDiff_const)

end Smooth

section VectorField

variable [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M]
  (φ : M ≃ₘ⟮I, I⟯ M) {x : M} {d : ℕ} (hx : IsPeriodicPt φ d x) [Fact (0 < (d : ℝ))]

/-- The closed orbit is an integral curve of the vector field `T = ∂_t`: its velocity at `θ` is
`T (γ θ)`. -/
theorem hasMFDerivAt_closedOrbit (θ : AddCircle (d : ℝ)) :
    HasMFDerivAt 𝓘(ℝ) (𝓘(ℝ).prod I) (closedOrbit φ hx) θ
      ((1 : ℝ →L[ℝ] ℝ).smulRight (timeVectorField φ (closedOrbit φ hx θ))) := by
  induction θ using QuotientAddGroup.induction_on with | H t => ?_
  have hd : MDifferentiableAt 𝓘(ℝ) (𝓘(ℝ).prod I) (closedOrbit φ hx) t :=
    ((contMDiff_closedOrbit φ hx) _).mdifferentiableAt (by simp)
  -- Read on `ℝ`, the closed orbit is the orbit `s ↦ [s, x]` of the suspension flow.
  have hc : closedOrbit φ hx ∘ ((↑) : ℝ → AddCircle (d : ℝ)) = fun s ↦ flow φ s (mk φ 0 x) := by
    simp only [closedOrbit_comp_coe, flow_mk, zero_add]
  have hlift : HasMFDerivAt 𝓘(ℝ) (𝓘(ℝ).prod I) (closedOrbit φ hx ∘ ((↑) : ℝ → AddCircle (d : ℝ)))
      t ((1 : ℝ →L[ℝ] ℝ).smulRight (timeVectorField φ (closedOrbit φ hx t))) := by
    have h := isMIntegralCurve_flow φ (mk φ 0 x) t
    have hp : flow φ t (mk φ 0 x) = closedOrbit φ hx t := by simp
    beta_reduce at h
    rwa [hp, ← hc] at h
  rw [← (AddCircle.mfderiv_comp_coe hd).symm.trans hlift.mfderiv]
  exact hd.hasMFDerivAt

/-- The velocity of the closed orbit at `θ` is `T (γ θ)`. -/
theorem mfderiv_closedOrbit (θ : AddCircle (d : ℝ)) :
    mfderiv 𝓘(ℝ) (𝓘(ℝ).prod I) (closedOrbit φ hx) θ =
      (1 : ℝ →L[ℝ] ℝ).smulRight (timeVectorField φ (closedOrbit φ hx θ)) :=
  (hasMFDerivAt_closedOrbit φ hx θ).mfderiv

/-- For the minimal period, the closed orbit is a smooth embedding of the circle `ℝ / dℤ`: a
primitive embedded closed orbit of `T`. -/
theorem isSmoothEmbedding_closedOrbit [FiniteDimensional ℝ E] [I.Boundaryless]
    (h : minimalPeriod φ x = d) :
    IsSmoothEmbedding 𝓘(ℝ) (𝓘(ℝ).prod I) ∞ (closedOrbit φ hx) := by
  refine ⟨isImmersion_iff_forall_isImmersionAt.2 fun θ ↦ ?_,
    (isClosedEmbedding_closedOrbit φ hx h).isEmbedding⟩
  rw [(contMDiff_closedOrbit φ hx).contMDiffOn.isImmersionAt_iff_injective_mfderiv isOpen_univ
    (mem_univ θ) (by simp), mfderiv_closedOrbit]
  -- The differential of the projection sends `a • T` to `a`, so `a ↦ a • T` is injective.
  have key : ∀ c : ℝ, mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) (closedOrbit φ hx θ)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (timeVectorField φ (closedOrbit φ hx θ)) c) = c := fun c ↦ by
    rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, map_smul,
      mfderiv_proj_timeVectorField]
    -- The tangent space of the circle is `ℝ`, so `c • 1` is the product `c * 1`.
    exact mul_one c
  -- The tangent space of the circle at `θ` is `ℝ`, read in the charts of the circle.
  intro a b hab
  exact (key a).symm.trans ((congrArg _ hab).trans (key b))

end VectorField

end SmoothMappingTorus

end TauCeti
