/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Quotient
import TauCeti.Geometry.Manifold.Submersion.Basic

/-!
# Reductive complements of a closed subgroup

Let `K` be a closed subgroup of a finite-dimensional Lie group `G`, with projection
`π : G → G ⧸ K` and base point `o = [1]`. For a subspace `𝔪` of the Lie algebra `T_1 G`
complementary to the kernel `𝔨 = ker dπ_1`, the differential `dπ_1` restricts to a linear
equivalence `𝔪 ≃ T_o(G ⧸ K)`. When `𝔪` is a *reductive complement*, that is, stable under
`Ad(K)`, this equivalence intertwines `Ad(K)` on `𝔪` with the isotropy action `k ↦ d(k •)_o` of
`K` on `T_o(G ⧸ K)`.

Consequently a bilinear form on `𝔪` transports to a form on `T_o(G ⧸ K)`, and an `Ad(K)`-invariant
form on a reductive complement transports to an isotropy-invariant one. Conversely, every form on
`T_o(G ⧸ K)` is the transport of its pullback along `dπ_1`, and that pullback is `Ad(K)`-invariant
when the form is isotropy-invariant. Here a form on `𝔪` is given as a continuous bilinear form `b`
on `T_1 G` whose properties are only required on `𝔪`.

## Main definitions

* `Subgroup.complementEquivOne`: `dπ_1` on a complement `𝔪` of its kernel, as a linear
  equivalence onto `T_o(G ⧸ K)`.
* `Subgroup.complementLiftOne`: its inverse, followed by the inclusion of `𝔪` into `T_1 G`.
* `Subgroup.complementForm`: the form on `T_o(G ⧸ K)` transported from a form on `𝔪`.

## Main results

* `Subgroup.complementLiftOne_mfderiv_smul`: for an `Ad(K)`-stable complement, the lift
  intertwines the isotropy action with `Ad(K)`.
* `Subgroup.complementForm_mfderiv_smul`: the transport of an `Ad(K)`-invariant form on a
  reductive complement is isotropy-invariant.
* `Subgroup.complementForm_comp_mfderiv_quotientMk`: every form on `T_o(G ⧸ K)` is the transport
  of its pullback along `dπ_1`, and `Subgroup.mfderiv_quotientMk_adjoint_of_mfderiv_smul`: that
  pullback is `Ad(K)`-invariant when the form is isotropy-invariant.

## References

* J. Cheeger, D. G. Ebin, *Comparison Theorems in Riemannian Geometry*, North-Holland (1975),
  Chapter 3 (homogeneous spaces and reductive complements).
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Chapter 7 (homogeneous Riemannian
  manifolds and reductive homogeneous spaces).
-/

public section

open Function Manifold Set TauCeti
open scoped ContDiff Manifold

noncomputable section

namespace Subgroup

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {K : Subgroup G} (hK : IsClosed (K : Set G)) {𝔪 : Submodule ℝ (TangentSpace I (1 : G))}

section Lift

variable (I K) in
/-- **A complement of `𝔨` is `T_o(G ⧸ K)`.** The restriction of `dπ_1` to a complement `𝔪` of
its kernel `𝔨`, as a linear equivalence onto `T_o(G ⧸ K)`: Mathlib's
`LinearMap.kerComplementEquivRange` for `𝔪`, with the range identified with `T_o(G ⧸ K)` because
`dπ_1` is surjective. -/
def complementEquivOne
    (h𝔪 : letI := quotientChartedSpaceOfIsClosed I hK
      IsCompl 𝔪 (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1).ker) :
    letI := quotientChartedSpaceOfIsClosed I hK
    𝔪 ≃ₗ[ℝ] TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) :=
  letI := quotientChartedSpaceOfIsClosed I hK
  ((mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K)
      1).toLinearMap.kerComplementEquivRange h𝔪).trans
    (LinearEquiv.ofTop _ (LinearMap.range_eq_top.2
      ((isSubmersion_quotientMk (I := I) hK).surjective_mfderiv (by simp) 1)))

variable {hK}
variable {h𝔪 : letI := quotientChartedSpaceOfIsClosed I hK
  IsCompl 𝔪 (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1).ker}

/-- The equivalence `𝔪 ≃ T_o(G ⧸ K)` is `dπ_1` on `𝔪`. -/
@[simp]
theorem complementEquivOne_apply :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ a, complementEquivOne I K hK h𝔪 a =
      mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1
        (a : TangentSpace I (1 : G)) := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  intro a
  rw [complementEquivOne, LinearEquiv.trans_apply, LinearEquiv.ofTop_apply,
    LinearMap.kerComplementEquivRange_apply_coe, ContinuousLinearMap.coe_coe]

variable (I K hK h𝔪) in
/-- **The lift through a complement.** The inverse of the restriction of `dπ_1` to a complement
`𝔪` of its kernel, followed by the inclusion of `𝔪` into `T_1 G`. -/
def complementLiftOne :
    letI := quotientChartedSpaceOfIsClosed I hK
    TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ] TangentSpace I (1 : G) :=
  letI := quotientChartedSpaceOfIsClosed I hK
  LinearMap.toContinuousLinearMap (𝔪.subtype ∘ₗ (complementEquivOne I K hK h𝔪).symm.toLinearMap)

/-- The lift through `𝔪` is the inverse of `complementEquivOne`, as a vector of `T_1 G`. -/
theorem complementLiftOne_apply :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ u : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K),
      complementLiftOne I K hK h𝔪 u =
        ((complementEquivOne I K hK h𝔪).symm u : TangentSpace I (1 : G)) :=
  fun _ ↦ (rfl)

/-- The lift through `𝔪` takes values in `𝔪`. -/
theorem complementLiftOne_mem :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ u : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K),
      complementLiftOne I K hK h𝔪 u ∈ 𝔪 :=
  fun _ ↦ Subtype.property _

/-- The lift through `𝔪` is a right inverse of `dπ_1`. -/
@[simp]
theorem mfderiv_quotientMk_complementLiftOne :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ u : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K),
      mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1
        (complementLiftOne I K hK h𝔪 u) = u := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  intro u
  rw [complementLiftOne_apply, ← complementEquivOne_apply (h𝔪 := h𝔪),
    LinearEquiv.apply_symm_apply]

/-- A vector of `𝔪` is the lift of its image under `dπ_1`. -/
theorem complementLiftOne_mfderiv_quotientMk {a : TangentSpace I (1 : G)} (ha : a ∈ 𝔪) :
    letI := quotientChartedSpaceOfIsClosed I hK
    complementLiftOne I K hK h𝔪
      (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1 a) = a := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  rw [complementLiftOne_apply]
  refine congrArg Subtype.val (?_ : _ = Subtype.mk a ha)
  rw [LinearEquiv.symm_apply_eq, complementEquivOne_apply]

/-- **Equivariance of the lift through a reductive complement.** If `k ∈ K` and `𝔪` is
`Ad_k`-stable, then the lift of the isotropy translate `d(k •)_o u` is `Ad_k` applied to the lift
of `u`. -/
theorem complementLiftOne_mfderiv_smul {k : G} (hk : k ∈ K)
    (hAd : ∀ a ∈ 𝔪, Lie.adjointContinuousLinearMap (I := I) k a ∈ 𝔪) :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ u, complementLiftOne I K hK h𝔪
      (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
        (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) u) =
      (Lie.adjointContinuousLinearMap (I := I) k :
          TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G)) (complementLiftOne I K hK h𝔪 u) := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  intro u
  have h := mfderiv_smul_mfderiv_quotientMk_one hK hk (complementLiftOne I K hK h𝔪 u)
  rw [mfderiv_quotientMk_complementLiftOne] at h
  rw [h]
  exact complementLiftOne_mfderiv_quotientMk (hAd _ (complementLiftOne_mem u))

end Lift

section Form

variable {hK}
variable {h𝔪 : letI := quotientChartedSpaceOfIsClosed I hK
  IsCompl 𝔪 (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1).ker}

variable (I K hK h𝔪) in
/-- **The form on `T_o(G ⧸ K)` transported from `𝔪`.** For a bilinear form `b` on `T_1 G`, the
form `(u, v) ↦ b (ℓ u) (ℓ v)` on `T_o(G ⧸ K)`, where `ℓ` is the lift through the complement `𝔪`
(`Subgroup.complementLiftOne`). Only the restriction of `b` to `𝔪` matters. -/
def complementForm (b : TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G) →L[ℝ] ℝ) :
    letI := quotientChartedSpaceOfIsClosed I hK
    TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ]
      TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ] ℝ :=
  letI := quotientChartedSpaceOfIsClosed I hK
  (ContinuousLinearMap.precomp ℝ (complementLiftOne I K hK h𝔪)).comp
    (b.comp (complementLiftOne I K hK h𝔪))

variable {b : TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G) →L[ℝ] ℝ}

/-- The transported form evaluates `b` on the lifts through `𝔪`. -/
@[simp]
theorem complementForm_apply :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ u v : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K),
      complementForm I K hK h𝔪 b u v =
        b (complementLiftOne I K hK h𝔪 u) (complementLiftOne I K hK h𝔪 v) :=
  fun _ _ ↦ rfl

/-- The transported form pairs `dπ_1 a` and `dπ_1 c` to `b a c` for `a, c ∈ 𝔪`. -/
theorem complementForm_mfderiv_quotientMk {a c : TangentSpace I (1 : G)} (ha : a ∈ 𝔪)
    (hc : c ∈ 𝔪) :
    letI := quotientChartedSpaceOfIsClosed I hK
    complementForm I K hK h𝔪 b
        (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1 a)
        (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1 c) =
      b a c := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  rw [complementForm_apply, complementLiftOne_mfderiv_quotientMk ha,
    complementLiftOne_mfderiv_quotientMk hc]

/-- The transported form is symmetric if `b` is symmetric on `𝔪`. -/
theorem complementForm_comm (hsymm : ∀ a ∈ 𝔪, ∀ c ∈ 𝔪, b a c = b c a) :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ u v : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K),
      complementForm I K hK h𝔪 b u v = complementForm I K hK h𝔪 b v u := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  intro u v
  exact hsymm _ (complementLiftOne_mem u) _ (complementLiftOne_mem v)

/-- The transported form is positive definite if `b` is positive definite on `𝔪`. -/
theorem complementForm_pos (hpos : ∀ a ∈ 𝔪, a ≠ 0 → 0 < b a a) :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ u : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K),
      u ≠ 0 → 0 < complementForm I K hK h𝔪 b u u := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  intro u hu
  refine hpos _ (complementLiftOne_mem u) fun h ↦ hu ?_
  have h' : complementLiftOne I K hK h𝔪 u = 0 := h
  rw [← mfderiv_quotientMk_complementLiftOne (h𝔪 := h𝔪) u, h', map_zero]

/-- **Isotropy invariance of the transported form.** If `𝔪` and the restriction of `b` to `𝔪`
are `Ad(K)`-invariant, the transported form on `T_o(G ⧸ K)` is invariant under the isotropy
action of `K`. -/
theorem complementForm_mfderiv_smul
    (hAd : ∀ k ∈ K, ∀ a ∈ 𝔪, Lie.adjointContinuousLinearMap (I := I) k a ∈ 𝔪)
    (hb : ∀ k ∈ K, ∀ a ∈ 𝔪, ∀ c ∈ 𝔪,
      b (Lie.adjointContinuousLinearMap (I := I) k a)
        (Lie.adjointContinuousLinearMap (I := I) k c) = b a c) :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ k ∈ K, ∀ u v, complementForm I K hK h𝔪 b
        (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) u)
        (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) v) = complementForm I K hK h𝔪 b u v := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  intro k hk u v
  -- The arguments on the left live in the fibre at `k • o`, the fibre at `o` only up to defeq.
  change b (complementLiftOne I K hK h𝔪 _) (complementLiftOne I K hK h𝔪 _) =
    b (complementLiftOne I K hK h𝔪 u) (complementLiftOne I K hK h𝔪 v)
  rw [complementLiftOne_mfderiv_smul hk (hAd k hk),
    complementLiftOne_mfderiv_smul hk (hAd k hk)]
  exact hb k hk _ (complementLiftOne_mem u) _ (complementLiftOne_mem v)

/-- **Every form on `T_o(G ⧸ K)` comes from `𝔪`.** A bilinear form `β` on `T_o(G ⧸ K)` is the
transport of its pullback `(a, c) ↦ β (dπ_1 a) (dπ_1 c)` along `dπ_1`, for any complement `𝔪`. -/
theorem complementForm_comp_mfderiv_quotientMk
    (β : letI := quotientChartedSpaceOfIsClosed I hK
      TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ]
        TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ] ℝ) :
    letI := quotientChartedSpaceOfIsClosed I hK
    complementForm I K hK h𝔪 ((ContinuousLinearMap.precomp ℝ
      (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1)).comp
        (β.comp (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1))) =
      β := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  ext u v
  simp only [complementForm_apply, ContinuousLinearMap.coe_comp, comp_apply,
    ContinuousLinearMap.precomp_apply, mfderiv_quotientMk_complementLiftOne]

/-- For `k ∈ K`, the pullback along `dπ_1` of a form on `T_o(G ⧸ K)` invariant under the isotropy
action of `k` is `Ad_k`-invariant on all of `T_1 G`. -/
theorem mfderiv_quotientMk_adjoint_of_mfderiv_smul
    {β : letI := quotientChartedSpaceOfIsClosed I hK
      TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ]
        TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ] ℝ}
    {k : G} (hk : k ∈ K)
    (hβ : letI := quotientChartedSpaceOfIsClosed I hK
      ∀ u v, β (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) u)
          (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) v) = β u v)
    (a c : TangentSpace I (1 : G)) :
    letI := quotientChartedSpaceOfIsClosed I hK
    β (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1
        (Lie.adjointContinuousLinearMap (I := I) k a))
      (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1
        (Lie.adjointContinuousLinearMap (I := I) k c)) =
    β (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1 a)
      (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1 c) := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  rw [← mfderiv_smul_mfderiv_quotientMk_one hK hk, ← mfderiv_smul_mfderiv_quotientMk_one hK hk]
  exact hβ _ _

end Form

end Subgroup
