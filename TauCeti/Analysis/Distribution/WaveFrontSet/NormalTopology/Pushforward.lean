/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.NormalTopology
public import TauCeti.Analysis.Distribution.WaveFrontSet.Pushforward
import TauCeti.Analysis.Normed.Module.Cone

/-!
# Continuity of the pushforward along a linear map in the normal topology

Let `A : E →L[ℝ] E'` be a linear map between finite-dimensional real inner product spaces, `Ω ⊆ E`
and `Ω' ⊆ E'` open sets and `χ` a test function on `Ω`. The pushforward `T ↦ A_* (χ T)`,
`f ↦ T (χ (f ∘ A))` (`Distribution.cutoffPushforwardCLM`), moves wave front sets along the
transpose of `A`: `WF(A_* (χ T))` lies over `A (supp χ)`, in the directions `η` with `Aᵀ η = 0`
or `(x, Aᵀ η) ∈ WF(T)` for some `x ∈ supp χ` with `A x` the base point
(`Distribution.waveFrontSet_cutoffPushforwardCLM_subset`). For a fixed set `Γ`, the distributions
with wave front set in `Γ` are therefore all sent into one fixed target set
`TauCeti.pushforwardCone (supp χ) A Γ`, which depends on `Γ` and `supp χ` but not on `T`:

`{(A x, η) | x ∈ supp χ, (x, Aᵀ η) ∈ Γ, or η ≠ 0 and Aᵀ η = 0}`.

When `Γ` contains no zero covectors, as for every wave front set, this is the set of nonzero
covectors `(A x, η)` with `x ∈ supp χ` and `(x, Aᵀ η) ∈ Γ ∪ (supp χ × {0})`: the target cone
that Hörmander's bound gives for the fixed cone `Γ` on the fixed support `supp χ`.

This file proves that the pushforward is continuous for the normal topologies of Hörmander's spaces
(`TauCeti.WaveFrontSpace.cutoffPushforwardCLM`):

`A_* (χ ·) : 𝓓'_Γ(Ω) →L[ℂ] 𝓓'_{Γ'}(Ω')`, `Γ' = TauCeti.pushforwardCone (supp χ) A Γ`.

Continuity into `𝓓'(Ω')` is that of the pushforward itself. For a seminorm `‖·‖_{f,V,N}` of the
target, localized Fourier transforms of `A_* (χ T)` are those of `T` at the transposed frequency,
with the pulled-back cutoff `χ (f ∘ A)` (`Distribution.localFourier_cutoffPushforwardCLM`). If
some point of `supp χ` is mapped into `supp f`, the admissibility of `(f, V, N)` forces `Aᵀ` to
have no zeros on `V \ {0}`; on the closed cone `V` it is then bounded below, `‖η‖ ≤ c ‖Aᵀ η‖`
(`TauCeti.exists_norm_le_mul_norm_apply_of_isClosed`), and the image `Aᵀ V` is again a closed cone
(`TauCeti.isClosed_image_of_isClosed`), admissible for `Γ` with the cutoff `χ (f ∘ A)`
(`TauCeti.WaveFrontSeminormIndex.cutoffPushforward`). This gives

`‖A_* (χ T)‖_{f,V,N} ≤ (1 + c) ^ N ‖T‖_{χ (f ∘ A), Aᵀ V, N}`

(`TauCeti.WaveFrontSpace.exists_seminorm_cutoffPushforwardCLM_le`). Otherwise the pulled-back
cutoff vanishes and so does the seminorm.

## Main declarations

* `TauCeti.pushforwardCone K A Γ`: the target set of covectors `(A x, η)`, `x ∈ K`, with
  `(x, Aᵀ η) ∈ Γ`, or `η ≠ 0` and `Aᵀ η = 0`.
* `Distribution.waveFrontSet_cutoffPushforwardCLM_subset_pushforwardCone`: the pushforward of a
  distribution with wave front set in `Γ` has wave front set in `pushforwardCone (supp χ) A Γ`.
* `TauCeti.WaveFrontSeminormIndex.cutoffPushforward`: the seminorm data `(χ (f ∘ A), Aᵀ V, N)` on
  `Ω` for the seminorm data `(f, V, N)` on `Ω'`.
* `TauCeti.WaveFrontSpace.cutoffPushforwardCLM`: the pushforward
  `𝓓'_Γ(Ω) →L[ℂ] 𝓓'_{pushforwardCone (supp χ) A Γ}(Ω')`, continuous in the normal topologies.
* `TauCeti.WaveFrontSpace.exists_seminorm_cutoffPushforwardCLM_le`: the seminorm estimate behind
  its continuity.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.13 (the wave front set of a pushforward).
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on
  distributions having a specified wave front set (with a counterexample by Semyon Alesker)*,
  Studia Math. 232 (2016), arXiv:1409.7662v2, §§3–5 (the normal topology and the continuity of
  pullback and pushforward in it).
-/

public section

noncomputable section

open Function Set TopologicalSpace TestFunction Distribution
open scoped Distributions InnerProduct

namespace TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']

/-! ### The target set of covectors -/

/-- The covectors `(A x, η)` with `x ∈ K` such that `(x, Aᵀ η) ∈ Γ`, or `η ≠ 0` and `Aᵀ η = 0`.
For `K = supp χ` it contains the wave front set of the pushforward `A_* (χ T)` of every
distribution `T` with wave front set in `Γ`
(`Distribution.waveFrontSet_cutoffPushforwardCLM_subset_pushforwardCone`). When `Γ` contains no
zero covectors, it consists of the nonzero covectors `(A x, η)`, `x ∈ K`, with
`(x, Aᵀ η) ∈ Γ ∪ (K × {0})`. -/
def pushforwardCone (K : Set E) (A : E →L[ℝ] E') (Γ : Set (E × E)) : Set (E' × E') :=
  {p | ∃ x ∈ K, A x = p.1 ∧ ((x, (A†) p.2) ∈ Γ ∨ (p.2 ≠ 0 ∧ (A†) p.2 = 0))}

@[simp]
theorem mem_pushforwardCone {K : Set E} {A : E →L[ℝ] E'} {Γ : Set (E × E)} {p : E' × E'} :
    p ∈ pushforwardCone K A Γ ↔
      ∃ x ∈ K, A x = p.1 ∧ ((x, (A†) p.2) ∈ Γ ∨ (p.2 ≠ 0 ∧ (A†) p.2 = 0)) :=
  Iff.rfl

/-- `pushforwardCone K A Γ` is monotone in `K` and in `Γ`. -/
theorem pushforwardCone_mono {K K' : Set E} {A : E →L[ℝ] E'} {Γ Γ' : Set (E × E)} (hK : K ⊆ K')
    (hΓ : Γ ⊆ Γ') : pushforwardCone K A Γ ⊆ pushforwardCone K' A Γ' :=
  fun _ ⟨x, hx, hxp, h⟩ ↦ ⟨x, hK hx, hxp, h.imp_left fun h ↦ hΓ h⟩

/-- Over a point `A x` with `x ∈ K`, a frequency `η` outside `pushforwardCone K A Γ` has
`(x, Aᵀ η) ∉ Γ`, and `Aᵀ η ≠ 0` unless `η = 0`. -/
theorem notMem_and_eq_zero_of_notMem_pushforwardCone {K : Set E} {A : E →L[ℝ] E'}
    {Γ : Set (E × E)} {x : E} (hx : x ∈ K) {η : E'} (h : (A x, η) ∉ pushforwardCone K A Γ) :
    (x, (A†) η) ∉ Γ ∧ ((A†) η = 0 → η = 0) :=
  ⟨fun hΓ ↦ h ⟨x, hx, rfl, .inl hΓ⟩, fun h0 ↦ by_contra fun hη ↦ h ⟨x, hx, rfl, .inr ⟨hη, h0⟩⟩⟩

end TauCeti

namespace Distribution

open TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  {Ω : Opens E} {Ω' : Opens E'}

/-- **The wave front set of a pushforward lies in a fixed set.** If the wave front set of `T` lies
in `Γ`, the wave front set of the pushforward `A_* (χ T)` lies in `pushforwardCone (supp χ) A Γ`,
a set independent of `T`. -/
theorem waveFrontSet_cutoffPushforwardCLM_subset_pushforwardCone (χ : 𝓓(Ω, ℝ))
    (A : E →L[ℝ] E') {Γ : Set (E × E)} {T : 𝓓'(Ω, ℂ)} (hT : T.waveFrontSet ⊆ Γ) :
    (cutoffPushforwardCLM χ A A.contDiff.contDiffOn T : 𝓓'(Ω', ℂ)).waveFrontSet ⊆
      pushforwardCone (tsupport χ) A Γ := fun p hp ↦ by
  obtain ⟨x, hx, hxp, h⟩ := waveFrontSet_cutoffPushforwardCLM_subset A T hp
  exact ⟨x, hx.1, hxp, h.symm.imp (fun h ↦ hT h) fun h ↦ ⟨(mem_waveFrontSet_iff.1 hp).2.1, h⟩⟩

end Distribution

namespace TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  {Ω : Opens E} {Ω' : Opens E'} {Γ : Set (E × E)}

/-! ### Transport of the seminorm data -/

namespace WaveFrontSeminormIndex

/-- If a point of `supp χ` is mapped by `A` into the support of the cutoff of the seminorm data
`i` for `pushforwardCone (supp χ) A Γ`, then `Aᵀ` has no zeros on the nonzero frequencies of the
cone of `i`. -/
theorem eq_zero_of_adjoint_apply_eq_zero {χ : 𝓓(Ω, ℝ)} {A : E →L[ℝ] E'}
    (i : WaveFrontSeminormIndex Ω' (pushforwardCone (tsupport χ) A Γ)) {x : E}
    (hx : x ∈ tsupport χ) (hAx : A x ∈ tsupport i.cutoff) {η : E'} (hη : η ∈ i.cone)
    (h0 : (A†) η = 0) : η = 0 :=
  (notMem_and_eq_zero_of_notMem_pushforwardCone hx
    (disjoint_left.1 i.disjoint (mk_mem_prod hAx hη))).2 h0

/-- The data `(χ (f ∘ A), Aᵀ V, N)` on `Ω` of a seminorm of `𝓓'_Γ(Ω)`, for the data
`i = (f, V, N)` of a seminorm of `𝓓'_{Γ'}(Ω')`, `Γ' = pushforwardCone (supp χ) A Γ`. The cone is
the closure of `Aᵀ V`, which is `Aᵀ V` itself whenever the cutoff `χ (f ∘ A)` is not zero. -/
def cutoffPushforward (χ : 𝓓(Ω, ℝ)) (A : E →L[ℝ] E')
    (i : WaveFrontSeminormIndex Ω' (pushforwardCone (tsupport χ) A Γ)) :
    WaveFrontSeminormIndex Ω Γ where
  cutoff := cutoffCompCLM χ A A.contDiff.contDiffOn i.cutoff
  cone := closure ((A†) '' i.cone)
  order := i.order
  isClosed_cone := isClosed_closure
  smul_mem_cone t ht ξ hξ := by
    refine closure_mono ?_
      (image_closure_subset_closure_image (continuous_const_smul t) ⟨ξ, hξ, rfl⟩)
    rintro _ ⟨_, ⟨η, hη, rfl⟩, rfl⟩
    exact ⟨t • η, i.smul_mem_cone t ht η hη, map_smul _ _ _⟩
  disjoint := by
    refine disjoint_left.2 fun ⟨x, ξ⟩ ⟨hx, hξ⟩ hΓ ↦ ?_
    obtain ⟨hxχ, hAx⟩ := tsupport_cutoffCompCLM_subset _ hx
    -- Over `A x`, the transpose `Aᵀ` has no zeros on the nonzero frequencies of the cone, so it
    -- maps the closed cone to a closed set.
    have hclosed : IsClosed ((A†) '' i.cone) := isClosed_image_of_isClosed i.isClosed_cone
      i.smul_mem_cone (A†) fun _ hη h0 ↦ i.eq_zero_of_adjoint_apply_eq_zero hxχ hAx hη h0
    obtain ⟨η, hη, rfl⟩ := hclosed.closure_eq ▸ hξ
    exact (notMem_and_eq_zero_of_notMem_pushforwardCone hxχ
      (disjoint_left.1 i.disjoint (mk_mem_prod hAx hη))).1 hΓ

@[simp]
theorem cutoffPushforward_cutoff (χ : 𝓓(Ω, ℝ)) (A : E →L[ℝ] E')
    (i : WaveFrontSeminormIndex Ω' (pushforwardCone (tsupport χ) A Γ)) :
    (i.cutoffPushforward χ A).cutoff = cutoffCompCLM χ A A.contDiff.contDiffOn i.cutoff :=
  (rfl)

@[simp]
theorem cutoffPushforward_cone (χ : 𝓓(Ω, ℝ)) (A : E →L[ℝ] E')
    (i : WaveFrontSeminormIndex Ω' (pushforwardCone (tsupport χ) A Γ)) :
    (i.cutoffPushforward χ A).cone = closure ((A†) '' i.cone) :=
  (rfl)

@[simp]
theorem cutoffPushforward_order (χ : 𝓓(Ω, ℝ)) (A : E →L[ℝ] E')
    (i : WaveFrontSeminormIndex Ω' (pushforwardCone (tsupport χ) A Γ)) :
    (i.cutoffPushforward χ A).order = i.order :=
  (rfl)

end WaveFrontSeminormIndex

/-! ### The pushforward on `𝓓'_Γ(Ω)` -/

namespace WaveFrontSpace

/-- The pushforward `T ↦ A_* (χ T)` as a linear map `𝓓'_Γ(Ω) → 𝓓'_{Γ'}(Ω')`,
`Γ' = pushforwardCone (supp χ) A Γ`, before its continuity is proved. -/
private def cutoffPushforwardₗ (χ : 𝓓(Ω, ℝ)) (A : E →L[ℝ] E') :
    WaveFrontSpace Ω Γ →ₗ[ℂ] WaveFrontSpace Ω' (pushforwardCone (tsupport χ) A Γ) where
  toFun u := mk (Distribution.cutoffPushforwardCLM χ A A.contDiff.contDiffOn u.toDistribution)
    (waveFrontSet_cutoffPushforwardCLM_subset_pushforwardCone χ A
      u.waveFrontSet_toDistribution_subset)
  map_add' _ _ := ext (by simp)
  map_smul' _ _ := ext (by ext; simp)

private theorem toDistribution_cutoffPushforwardₗ (χ : 𝓓(Ω, ℝ)) (A : E →L[ℝ] E')
    (u : WaveFrontSpace Ω Γ) :
    (cutoffPushforwardₗ (Ω' := Ω') χ A u).toDistribution =
      Distribution.cutoffPushforwardCLM χ A A.contDiff.contDiffOn u.toDistribution :=
  toDistribution_mk _ _

/-- **The seminorms of a pushforward.** For every seminorm `‖·‖_{f,V,N}` of
`𝓓'_{Γ'}(Ω')`, `Γ' = pushforwardCone (supp χ) A Γ`, there is `C ≥ 0` with
`‖A_* (χ T)‖_{f,V,N} ≤ C ‖T‖_{χ (f ∘ A), Aᵀ V, N}` for every `T ∈ 𝓓'_Γ(Ω)`: one can take
`C = (1 + c) ^ N` when `‖η‖ ≤ c ‖Aᵀ η‖` on `V`. -/
private theorem exists_seminorm_cutoffPushforwardₗ_le (χ : 𝓓(Ω, ℝ)) (A : E →L[ℝ] E')
    (i : WaveFrontSeminormIndex Ω' (pushforwardCone (tsupport χ) A Γ)) :
    ∃ C, 0 ≤ C ∧ ∀ u : WaveFrontSpace Ω Γ, WaveFrontSpace.seminorm i (cutoffPushforwardₗ χ A u) ≤
      C * WaveFrontSpace.seminorm (i.cutoffPushforward χ A) u := by
  by_cases h : ∃ x ∈ tsupport χ, A x ∈ tsupport i.cutoff
  · obtain ⟨x, hx, hAx⟩ := h
    obtain ⟨c, hc, hle⟩ := exists_norm_le_mul_norm_apply_of_isClosed i.isClosed_cone
      i.smul_mem_cone (A†) fun _ hη h0 ↦ i.eq_zero_of_adjoint_apply_eq_zero hx hAx hη h0
    refine ⟨(1 + c) ^ i.order, by positivity, fun u ↦
      seminorm_le_bound i _ (by positivity) fun η hη ↦ ?_⟩
    have hη' : 1 + ‖η‖ ≤ (1 + c) * (1 + ‖(A†) η‖) := by
      nlinarith [hle η hη, norm_nonneg ((A†) η)]
    have hmem : (A†) η ∈ (i.cutoffPushforward χ A).cone := subset_closure ⟨η, hη, rfl⟩
    calc (1 + ‖η‖) ^ i.order *
          ‖(cutoffPushforwardₗ χ A u).toDistribution.localFourier i.cutoff η‖
        = (1 + ‖η‖) ^ i.order *
            ‖u.toDistribution.localFourier (i.cutoffPushforward χ A).cutoff ((A†) η)‖ := by
          rw [toDistribution_cutoffPushforwardₗ, localFourier_cutoffPushforwardCLM,
            WaveFrontSeminormIndex.cutoffPushforward_cutoff]
      _ ≤ ((1 + c) * (1 + ‖(A†) η‖)) ^ i.order *
            ‖u.toDistribution.localFourier (i.cutoffPushforward χ A).cutoff ((A†) η)‖ := by
          gcongr
      _ = (1 + c) ^ i.order * ((1 + ‖(A†) η‖) ^ (i.cutoffPushforward χ A).order *
            ‖u.toDistribution.localFourier (i.cutoffPushforward χ A).cutoff ((A†) η)‖) := by
          rw [mul_pow, mul_assoc, WaveFrontSeminormIndex.cutoffPushforward_order]
      _ ≤ (1 + c) ^ i.order * WaveFrontSpace.seminorm (i.cutoffPushforward χ A) u := by
          gcongr
          exact le_seminorm _ u hmem
  · -- No point of `supp χ` is mapped into the support of the cutoff, so the pulled-back cutoff
    -- vanishes and so does the seminorm.
    push Not at h
    have hψ : cutoffCompCLM χ A A.contDiff.contDiffOn i.cutoff = 0 := by
      ext y
      by_contra hy
      obtain ⟨hyχ, hAy⟩ := tsupport_cutoffCompCLM_subset _ (subset_tsupport _ hy)
      exact h y hyχ hAy
    refine ⟨0, le_rfl, fun u ↦ ?_⟩
    rw [zero_mul]
    refine seminorm_le_bound i _ le_rfl fun η _ ↦ ?_
    rw [toDistribution_cutoffPushforwardₗ, localFourier_cutoffPushforwardCLM, hψ,
      localFourier_zero_cutoff, norm_zero, mul_zero]

/-- **Continuity of the pushforward in the normal topology.** For a linear map `A` and a test
function `χ`, the pushforward `T ↦ A_* (χ T)` is a continuous linear map
`𝓓'_Γ(Ω) →L[ℂ] 𝓓'_{Γ'}(Ω')` into Hörmander's space for the fixed set
`Γ' = pushforwardCone (supp χ) A Γ`: the seminorm `‖A_* (χ T)‖_{f,V,N}` is bounded by a multiple
of `‖T‖_{χ (f ∘ A), Aᵀ V, N}`. -/
def cutoffPushforwardCLM (χ : 𝓓(Ω, ℝ)) (A : E →L[ℝ] E') :
    WaveFrontSpace Ω Γ →L[ℂ] WaveFrontSpace Ω' (pushforwardCone (tsupport χ) A Γ) :=
  ⟨cutoffPushforwardₗ χ A, continuous_linearMap_of_le _
    (by
      have h : ⇑(toDistribution ∘ₗ cutoffPushforwardₗ (Γ := Γ) (Ω' := Ω') χ A) =
          Distribution.cutoffPushforwardCLM χ A A.contDiff.contDiffOn ∘ toDistribution := by
        funext u
        exact toDistribution_cutoffPushforwardₗ χ A u
      rw [h]
      exact (Distribution.cutoffPushforwardCLM χ A A.contDiff.contDiffOn).continuous.comp
        continuous_toDistribution) fun i ↦ by
      obtain ⟨C, hC, h⟩ := exists_seminorm_cutoffPushforwardₗ_le χ A i
      refine ⟨C.toNNReal • WaveFrontSpace.seminorm (i.cutoffPushforward χ A),
        (continuous_seminorm _).const_smul _, fun u ↦ ?_⟩
      simpa [NNReal.smul_def, Real.coe_toNNReal _ hC] using h u⟩

@[simp]
theorem toDistribution_cutoffPushforwardCLM (χ : 𝓓(Ω, ℝ)) (A : E →L[ℝ] E')
    (u : WaveFrontSpace Ω Γ) :
    (cutoffPushforwardCLM (Ω' := Ω') χ A u).toDistribution =
      Distribution.cutoffPushforwardCLM χ A A.contDiff.contDiffOn u.toDistribution :=
  toDistribution_cutoffPushforwardₗ χ A u

/-- **The seminorms of a pushforward.** For every seminorm `‖·‖_{f,V,N}` of
`𝓓'_{Γ'}(Ω')`, `Γ' = pushforwardCone (supp χ) A Γ`, there is `C ≥ 0` with
`‖A_* (χ T)‖_{f,V,N} ≤ C ‖T‖_{χ (f ∘ A), Aᵀ V, N}` for every `T ∈ 𝓓'_Γ(Ω)`: one can take
`C = (1 + c) ^ N` when `‖η‖ ≤ c ‖Aᵀ η‖` on `V`, and `C = 0` when `A` maps no point of `supp χ`
into `supp f`. -/
theorem exists_seminorm_cutoffPushforwardCLM_le (χ : 𝓓(Ω, ℝ)) (A : E →L[ℝ] E')
    (i : WaveFrontSeminormIndex Ω' (pushforwardCone (tsupport χ) A Γ)) :
    ∃ C, 0 ≤ C ∧ ∀ u : WaveFrontSpace Ω Γ,
      WaveFrontSpace.seminorm i (cutoffPushforwardCLM χ A u) ≤
        C * WaveFrontSpace.seminorm (i.cutoffPushforward χ A) u := by
  simpa only [cutoffPushforwardCLM, ContinuousLinearMap.coe_mk'] using
    exists_seminorm_cutoffPushforwardₗ_le χ A i

end WaveFrontSpace

end TauCeti
