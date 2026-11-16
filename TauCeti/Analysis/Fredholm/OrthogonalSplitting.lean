/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.ConstantNullity
public import TauCeti.Analysis.InnerProductSpace.Adjoint

/-!
# Orthogonal kernel projections and right inverses of Fredholm families

Let `T x : E →L[𝕜] F` be a family of operators between Banach spaces over `ℝ` or `ℂ`, continuous
in a parameter `x` and Fredholm at `x₀`, and let `ι : E →L[𝕜] H` be an injective operator into a
Hilbert space. Typically `E` is a Sobolev space of sections and `ι` its inclusion into `L²`, so
that `⟪ι e, ι e'⟫` is the `L²` pairing on `E`, for whose norm `E` is in general not complete.
Near every parameter where the kernel of `T x` has the dimension of that of `T x₀`, the kernel
has a projection along its `ι`-orthogonal complement, and when `T x₀` is onto, the operators `T x`
near `x₀` have right inverses with values in that complement. This file shows that both depend
continuously on `x`.

The kernels move continuously by
`ContinuousLinearMap.IsFredholm.exists_continuousOn_ker_parametrization`: there is a continuous
family `κ x : V →L[𝕜] E` on a fixed finite-dimensional inner product space
`V` whose range is `ker (T x)` at the parameters of constant nullity. With `A = ι ∘ κ x`, the
projection is

`π x = κ x (A† A)⁻¹ A† ι`,

where the Gram operator `A† A` of `V` is invertible as long as `A` is injective, which is an open
condition. Since inversion is continuous on the units of the complete normed ring `V →L[𝕜] V`,
`π x` is continuous in `x`. It fixes `ker (T x)` and `ι (e - π x e)` is orthogonal to
`ι (ker (T x))`. When `T x₀` is onto, so is every `T x` near `x₀`, with a continuous family of
right inverses `R x` (`ContinuousLinearMap.IsFredholm.exists_continuousOn_splitting`), and
`Q x = (1 - π x) R x` is the right inverse with values in the `ι`-orthogonal complement of the
kernel. Every `e ∈ E` then splits as `e = π x e + Q x (T x e)`.

Over `ℝ`, a `C^n` family has `C^n` projections and right inverses, since the adjoint is then a
continuous linear map of operators (`ContinuousLinearMap.adjointRealCLM`) and inversion is
analytic. Over `ℂ` the projection depends on `κ x` conjugate-linearly as well, so only its
continuity is stated.

For the gauge-fixed operator of a plane vortex or of the linearized Seiberg–Witten equations on
a Sobolev space, these are the kernel projections and right inverses on `L²`-orthogonal
complements of the kernel, which move continuously with the solution about which one linearizes.

## Main results

* `ContinuousLinearMap.IsFredholm.exists_continuousOn_orthogonal_ker_projection`: continuous
  projections onto the kernels along their `ι`-orthogonal complements, at the parameters of
  constant nullity.
* `ContinuousLinearMap.IsFredholm.exists_continuousOn_orthogonal_rightInverse`: for a family onto
  at `x₀`, continuous kernel projections and right inverses near `x₀`, with values in the
  `ι`-orthogonal complements of the kernels, splitting `E` as `ker (T x) ⊕ Q x F`.
* `ContinuousLinearMap.IsFredholm.exists_contDiffOn_orthogonal_ker_projection` and
  `ContinuousLinearMap.IsFredholm.exists_contDiffOn_orthogonal_rightInverse`: the same for a
  real `C^n` family, with `C^n` projections and right inverses.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, second edition, Springer, 1976,
  Chapter IV, §5 (stability of the nullity and of the kernel under small perturbations).
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix A.2 (Fredholm families and their kernels).
-/

public section

open Function Module Set Topology Filter
open scoped InnerProductSpace

namespace ContinuousLinearMap

section Gram

variable {𝕜 E H V : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

/-- The projection `κ (A† A)⁻¹ A† ι` with `A = ι κ`, onto the range of `κ` along the
`ι`-orthogonal complement of that range. -/
private noncomputable def gramProjection (ι : E →L[𝕜] H) (κ : V →L[𝕜] E) : E →L[𝕜] E :=
  κ ∘L Ring.inverse (adjoint (ι ∘L κ) ∘L (ι ∘L κ)) ∘L adjoint (ι ∘L κ) ∘L ι

private theorem gramProjection_apply (ι : E →L[𝕜] H) (κ : V →L[𝕜] E) (e : E) :
    gramProjection ι κ e =
      κ (Ring.inverse (adjoint (ι ∘L κ) ∘L (ι ∘L κ)) (adjoint (ι ∘L κ) (ι e))) :=
  (rfl)

private theorem gramProjection_apply_apply {ι : E →L[𝕜] H} {κ : V →L[𝕜] E}
    (hG : IsUnit (adjoint (ι ∘L κ) ∘L (ι ∘L κ))) (v : V) :
    gramProjection ι κ (κ v) = κ v := by
  have h : (Ring.inverse (adjoint (ι ∘L κ) ∘L (ι ∘L κ)) * (adjoint (ι ∘L κ) ∘L (ι ∘L κ))) v =
      v := by
    rw [Ring.inverse_mul_cancel _ hG]; rfl
  rw [gramProjection_apply]
  exact congrArg κ h

private theorem inner_sub_gramProjection_apply {ι : E →L[𝕜] H} {κ : V →L[𝕜] E}
    (hG : IsUnit (adjoint (ι ∘L κ) ∘L (ι ∘L κ))) (e : E) (v : V) :
    ⟪ι (e - gramProjection ι κ e), ι (κ v)⟫_𝕜 = 0 := by
  set A := ι ∘L κ
  have h : ((adjoint A ∘L A) * Ring.inverse (adjoint A ∘L A)) (adjoint A (ι e)) =
      adjoint A (ι e) := by
    rw [Ring.mul_inverse_cancel _ hG]; rfl
  rw [mul_apply_eq_comp, ContinuousLinearMap.comp_apply] at h
  have hAv : ι (κ v) = A v := rfl
  rw [hAv, ← adjoint_inner_left, map_sub, map_sub, gramProjection_apply]
  exact (congrArg (⟪·, v⟫_𝕜) (sub_eq_zero.2 h.symm)).trans (inner_zero_left _)

/-- Where `A† A` is invertible and `κ` has range `K`, the projection `κ (A† A)⁻¹ A† ι` is the
projection onto `K` along the `ι`-orthogonal complement of `K`. -/
private theorem gramProjection_spec {ι : E →L[𝕜] H} {κ : V →L[𝕜] E} {K : Submodule 𝕜 E}
    (hG : IsUnit (adjoint (ι ∘L κ) ∘L (ι ∘L κ))) (hK : κ.range = K) :
    (∀ e, gramProjection ι κ e ∈ K) ∧ (∀ k ∈ K, gramProjection ι κ k = k) ∧
      ∀ e, ∀ k ∈ K, ⟪ι (e - gramProjection ι κ e), ι k⟫_𝕜 = 0 := by
  subst hK
  refine ⟨fun e ↦ LinearMap.mem_range_self _ _, fun k hk ↦ ?_, fun e k hk ↦ ?_⟩
  · obtain ⟨v, rfl⟩ := hk
    exact gramProjection_apply_apply hG v
  · obtain ⟨v, rfl⟩ := hk
    exact inner_sub_gramProjection_apply hG e v

/-- The projection `κ (A† A)⁻¹ A† ι` depends continuously on `κ` where `A† A` is invertible. -/
private theorem continuousAt_gramProjection (ι : E →L[𝕜] H) {κ₀ : V →L[𝕜] E}
    (hG : IsUnit (adjoint (ι ∘L κ₀) ∘L (ι ∘L κ₀))) :
    ContinuousAt (gramProjection ι) κ₀ := by
  have hA : Continuous fun κ : V →L[𝕜] E ↦ ι ∘L κ := (compL 𝕜 V E H ι).continuous
  have hA' : Continuous fun κ : V →L[𝕜] E ↦ adjoint (ι ∘L κ) :=
    (adjoint : (V →L[𝕜] H) ≃ₗᵢ⋆[𝕜] (H →L[𝕜] V)).continuous.comp hA
  obtain ⟨u, hu⟩ := hG
  have hinv : ContinuousAt (fun κ : V →L[𝕜] E ↦
      Ring.inverse (adjoint (ι ∘L κ) ∘L (ι ∘L κ))) κ₀ := by
    refine ContinuousAt.comp (g := Ring.inverse) ?_ (hA'.clm_comp hA).continuousAt
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  exact continuousAt_id.clm_comp (hinv.clm_comp (hA'.continuousAt.clm_comp continuousAt_const))

end Gram

/-- Over `ℝ`, the projection `κ (A† A)⁻¹ A† ι` is a smooth function of `κ` where `A† A` is
invertible. -/
private theorem contDiffAt_gramProjection {E H V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] {n : WithTop ℕ∞}
    (ι : E →L[ℝ] H) {κ₀ : V →L[ℝ] E} (hG : IsUnit (adjoint (ι ∘L κ₀) ∘L (ι ∘L κ₀))) :
    ContDiffAt ℝ n (gramProjection ι) κ₀ := by
  have hA : ContDiff ℝ n fun κ : V →L[ℝ] E ↦ ι ∘L κ := (compL ℝ V E H ι).contDiff
  have hA' : ContDiff ℝ n fun κ : V →L[ℝ] E ↦ adjoint (ι ∘L κ) := by
    simpa only [Function.comp_def, adjointRealCLM_apply] using
      (adjointRealCLM (𝕜 := ℝ) (V := V) (W := H)).contDiff.comp hA
  obtain ⟨u, hu⟩ := hG
  have hinv : ContDiffAt ℝ n (fun κ : V →L[ℝ] E ↦
      Ring.inverse (adjoint (ι ∘L κ) ∘L (ι ∘L κ))) κ₀ := by
    refine ContDiffAt.comp (g := Ring.inverse) κ₀ ?_ (hA'.clm_comp hA).contDiffAt
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  exact contDiffAt_id.clm_comp (hinv.clm_comp (hA'.contDiffAt.clm_comp contDiffAt_const))

section Family

variable {𝕜 E F H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The Euclidean parametrization of a finite-dimensional space, on which Gram operators live. -/
private noncomputable def euclideanEquiv (K : Submodule 𝕜 E) [FiniteDimensional 𝕜 K] :
    EuclideanSpace 𝕜 (Fin (finrank 𝕜 K)) ≃L[𝕜] K :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

omit [CompleteSpace E] [CompleteSpace F] in
/-- The pointwise half of the kernel projection theorems. Let `κ x` be operators on `ker (T x₀)`
which are injective with range `ker (T x)` at the parameters of constant nullity, and let `κ' x`
be `κ x` read on a Euclidean space. On an open set `U' ∋ x₀` the Gram operators of `ι κ' x` are
invertible, and the Gram projections of `κ' x` are projections onto the kernels along their
`ι`-orthogonal complements at the parameters of constant nullity. -/
private theorem orthogonal_ker_projection_of_ker_parametrization {X : Type*} [TopologicalSpace X]
    {T : X → E →L[𝕜] F} {x₀ : X} (ι : E →L[𝕜] H) (hι : Injective ι)
    [FiniteDimensional 𝕜 (T x₀).ker] {U : Set X} (hU : IsOpen U) (hx₀U : x₀ ∈ U)
    {κ : X → (T x₀).ker →L[𝕜] E} (hκ : ContinuousOn κ U)
    (hκker : ∀ x ∈ U, finrank 𝕜 (T x).ker = finrank 𝕜 (T x₀).ker →
      Injective (κ x) ∧ (κ x).range = (T x).ker) :
    ∃ U' ⊆ U, IsOpen U' ∧ x₀ ∈ U' ∧ ∀ x ∈ U',
      IsUnit (adjoint (ι ∘L κ x ∘L (euclideanEquiv (T x₀).ker).toContinuousLinearMap) ∘L
        (ι ∘L κ x ∘L (euclideanEquiv (T x₀).ker).toContinuousLinearMap)) ∧
      (finrank 𝕜 (T x).ker = finrank 𝕜 (T x₀).ker →
        (∀ e, gramProjection ι (κ x ∘L (euclideanEquiv (T x₀).ker).toContinuousLinearMap) e ∈
          (T x).ker) ∧
        (∀ k ∈ (T x).ker,
          gramProjection ι (κ x ∘L (euclideanEquiv (T x₀).ker).toContinuousLinearMap) k = k) ∧
        ∀ e, ∀ k ∈ (T x).ker, ⟪ι (e - gramProjection ι
          (κ x ∘L (euclideanEquiv (T x₀).ker).toContinuousLinearMap) e), ι k⟫_𝕜 = 0) := by
  set eL := (euclideanEquiv (T x₀).ker).toContinuousLinearMap
  have hGc : Continuous fun κ : EuclideanSpace 𝕜 (Fin (finrank 𝕜 (T x₀).ker)) →L[𝕜] E ↦
      adjoint (ι ∘L κ) ∘L (ι ∘L κ) :=
    ((adjoint : _ ≃ₗᵢ⋆[𝕜] _).continuous.comp (compL 𝕜 _ E H ι).continuous).clm_comp
      (compL 𝕜 _ E H ι).continuous
  refine ⟨U ∩ (fun x ↦ κ x ∘L eL) ⁻¹' {κ | IsUnit (adjoint (ι ∘L κ) ∘L (ι ∘L κ))},
    inter_subset_left, (hκ.clm_comp continuousOn_const).isOpen_inter_preimage hU
      (Units.isOpen.preimage hGc), ⟨hx₀U, ?_⟩, fun x hx ↦ ⟨hx.2, fun hker ↦ ?_⟩⟩
  · exact (isUnit_adjoint_comp_self_iff _).2
      (hι.comp (((hκker x₀ hx₀U rfl).1).comp (euclideanEquiv _).injective))
  refine gramProjection_spec hx.2 ?_
  rw [← (hκker x hx.1 hker).2]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearEquiv.range (euclideanEquiv (T x₀).ker).toLinearEquiv)

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace H] in
/-- The pointwise half of the right inverse theorems: from a projection `π` onto the kernel of
`T` along its `ι`-orthogonal complement and a right inverse `R` of `T`, the right inverse
`Q = R - π R` takes values in that complement, and `e = π e + Q (T e)`. -/
private theorem orthogonal_rightInverse_spec {ι : E →L[𝕜] H} (hι : Injective ι)
    {T : E →L[𝕜] F} {π : E →L[𝕜] E} {R : F →L[𝕜] E} (hmem : ∀ e, π e ∈ T.ker)
    (horth : ∀ e, ∀ k ∈ T.ker, ⟪ι (e - π e), ι k⟫_𝕜 = 0) (hR : ∀ y, T (R y) = y) :
    (∀ y, T ((R - π ∘L R) y) = y) ∧ (∀ y, ∀ k ∈ T.ker, ⟪ι ((R - π ∘L R) y), ι k⟫_𝕜 = 0) ∧
      ∀ e, π e + (R - π ∘L R) (T e) = e := by
  have hQ : ∀ y, T ((R - π ∘L R) y) = y := fun y ↦ by
    have h0 : T (π (R y)) = 0 := LinearMap.mem_ker.1 (hmem (R y))
    simp [hR y, h0]
  have hQorth : ∀ y, ∀ k ∈ T.ker, ⟪ι ((R - π ∘L R) y), ι k⟫_𝕜 = 0 :=
    fun y k hk ↦ horth (R y) k hk
  refine ⟨hQ, hQorth, fun e ↦ ?_⟩
  -- The defect `d = e - π e - Q (T e)` lies in the kernel and is `ι`-orthogonal to it.
  set d := e - π e - (R - π ∘L R) (T e)
  have hd : d ∈ T.ker := by
    rw [LinearMap.mem_ker]
    simp only [d, coe_coe, map_sub, hQ, LinearMap.mem_ker.1 (hmem e), sub_zero, sub_self]
  have hdd : ⟪ι d, ι d⟫_𝕜 = 0 := by
    have hιd : ι d = ι (e - π e) - ι ((R - π ∘L R) (T e)) := by
      simp only [d, map_sub]
    nth_rw 1 [hιd]
    rw [inner_sub_left, horth e d hd, hQorth _ d hd, sub_zero]
  have : d = 0 := hι (by simpa using hdd)
  exact (sub_eq_zero.1 (by simpa only [d, sub_sub] using this)).symm

variable {X : Type*} [TopologicalSpace X] {T : X → E →L[𝕜] F} {x₀ : X}

omit [CompleteSpace F] in
/-- Near a parameter where a continuous family is Fredholm and onto, the right inverses `R x` of a
splitting with `T x (R x y) + P x y = y` are right inverses, every `T x` is onto, and the nullity
is constant. -/
private theorem surjective_of_splitting (hT₀ : IsFredholm (T x₀)) (hsurj : Surjective (T x₀))
    (hT : ContinuousAt T x₀) {S : Submodule 𝕜 F} {U : Set X} (hx₀U : x₀ ∈ U)
    {R : X → F →L[𝕜] E} {P : X → F →L[𝕜] S}
    (hRP : ∀ x ∈ U, (∀ y, T x (R x y) + P x y = y) ∧
      (finrank 𝕜 (T x).ker = finrank 𝕜 (T x₀).ker →
        ∃ hS : S.IsTopCompl (T x).range, P x = S.projectionOntoL (T x).range hS)) :
    ∃ W : Set X, IsOpen W ∧ x₀ ∈ W ∧ ∀ x ∈ U ∩ W, (∀ y, T x (R x y) = y) ∧
      finrank 𝕜 (T x).ker = finrank 𝕜 (T x₀).ker := by
  obtain ⟨W, hW, hWo, hx₀W⟩ := eventually_nhds_iff.1 (hT₀.eventually_finrank_ker_eq_iff hT)
  -- `S` complements the range of `T x₀`, which is everything, so `S = 0`.
  have hS : S = ⊥ := by
    obtain ⟨hS, -⟩ := (hRP x₀ hx₀U).2 rfl
    simpa [LinearMap.range_eq_top.2 hsurj] using hS.isCompl.inf_eq_bot
  refine ⟨W, hWo, hx₀W, fun x hx ↦ ?_⟩
  have hTR : ∀ y, T x (R x y) = y := fun y ↦ by
    have hP : (P x y : F) = 0 := by simpa [hS] using (P x y).2
    simpa [hP] using (hRP x hx.1).1 y
  have hsurjx : Surjective (T x) := fun y ↦ ⟨R x y, hTR y⟩
  exact ⟨hTR, (hW x hx.2).2
    (by rw [LinearMap.range_eq_top.2 hsurjx, LinearMap.range_eq_top.2 hsurj])⟩

/-- **Orthogonal kernel projections of a Fredholm family move continuously.** Let `T` be
continuous on an open set `s` and Fredholm at `x₀ ∈ s`, and let `ι : E →L[𝕜] H` be injective, into
a Hilbert space. Near `x₀` there is a continuous family of operators `π x : E →L[𝕜] E` which, at
every parameter where the kernel of `T x` has the dimension of that of `T x₀`, is the projection
onto `ker (T x)` along its `ι`-orthogonal complement: `π x` takes values in `ker (T x)`, fixes it,
and `ι (e - π x e)` is orthogonal to `ι k` for every `k ∈ ker (T x)`. -/
theorem IsFredholm.exists_continuousOn_orthogonal_ker_projection (ι : E →L[𝕜] H)
    (hι : Injective ι) {s : Set X} (hT₀ : IsFredholm (T x₀)) (hT : ContinuousOn T s)
    (hs : IsOpen s) (hx₀ : x₀ ∈ s) :
    ∃ U ⊆ s, IsOpen U ∧ x₀ ∈ U ∧ ∃ π : X → E →L[𝕜] E, ContinuousOn π U ∧
      ∀ x ∈ U, finrank 𝕜 (T x).ker = finrank 𝕜 (T x₀).ker →
        (∀ e, π x e ∈ (T x).ker) ∧ (∀ k ∈ (T x).ker, π x k = k) ∧
          ∀ e, ∀ k ∈ (T x).ker, ⟪ι (e - π x e), ι k⟫_𝕜 = 0 := by
  obtain ⟨U, hUs, hU, hx₀U, κ, hκ, hκker⟩ :=
    hT₀.exists_continuousOn_ker_parametrization hT hs hx₀
  have := hT₀.finite_ker
  obtain ⟨U', hU'U, hU', hx₀U', hG⟩ :=
    orthogonal_ker_projection_of_ker_parametrization ι hι hU hx₀U hκ hκker
  set eL := (euclideanEquiv (T x₀).ker).toContinuousLinearMap
  exact ⟨U', hU'U.trans hUs, hU', hx₀U', fun x ↦ gramProjection ι (κ x ∘L eL), fun x hx ↦
    (continuousAt_gramProjection ι (hG x hx).1).comp_continuousWithinAt
      (f := fun x ↦ κ x ∘L eL) ((hκ.clm_comp continuousOn_const x (hU'U hx)).mono hU'U),
    fun x hx ↦ (hG x hx).2⟩

/-- **Orthogonal right inverses of a surjective Fredholm family move continuously.** Let `T` be
continuous on an open set `s` and Fredholm and onto at `x₀ ∈ s`, and let `ι : E →L[𝕜] H` be
injective, into a Hilbert space. Near `x₀` every `T x` is onto, and there are continuous families
of operators `π x : E →L[𝕜] E` and `Q x : F →L[𝕜] E` such that `π x` is the projection onto
`ker (T x)` along its `ι`-orthogonal complement and `Q x` is a right inverse of `T x` with values in
that complement. Every `e ∈ E` splits as `e = π x e + Q x (T x e)`. -/
theorem IsFredholm.exists_continuousOn_orthogonal_rightInverse (ι : E →L[𝕜] H)
    (hι : Injective ι) {s : Set X} (hT₀ : IsFredholm (T x₀)) (hsurj : Surjective (T x₀))
    (hT : ContinuousOn T s) (hs : IsOpen s) (hx₀ : x₀ ∈ s) :
    ∃ U ⊆ s, IsOpen U ∧ x₀ ∈ U ∧ ∃ π : X → E →L[𝕜] E, ∃ Q : X → F →L[𝕜] E,
      ContinuousOn π U ∧ ContinuousOn Q U ∧ ∀ x ∈ U, Surjective (T x) ∧
        (∀ e, π x e ∈ (T x).ker) ∧ (∀ k ∈ (T x).ker, π x k = k) ∧
        (∀ e, ∀ k ∈ (T x).ker, ⟪ι (e - π x e), ι k⟫_𝕜 = 0) ∧
        (∀ y, T x (Q x y) = y) ∧ (∀ y, ∀ k ∈ (T x).ker, ⟪ι (Q x y), ι k⟫_𝕜 = 0) ∧
        ∀ e, π x e + Q x (T x e) = e := by
  obtain ⟨U₁, hU₁s, hU₁, hx₀U₁, π, hπ, hπker⟩ :=
    hT₀.exists_continuousOn_orthogonal_ker_projection ι hι hT hs hx₀
  obtain ⟨S, -, -, U₂, -, hU₂, hx₀U₂, R, P, hR, -, hRP⟩ :=
    hT₀.exists_continuousOn_splitting hT hs hx₀ (D := ⊤) (by simp)
  obtain ⟨W, hWo, hx₀W, hW⟩ :=
    surjective_of_splitting hT₀ hsurj (hT.continuousAt (hs.mem_nhds hx₀)) hx₀U₂ hRP
  refine ⟨U₁ ∩ (U₂ ∩ W), inter_subset_left.trans hU₁s, hU₁.inter (hU₂.inter hWo),
    ⟨hx₀U₁, hx₀U₂, hx₀W⟩, π, fun x ↦ R x - π x ∘L R x, hπ.mono inter_subset_left, ?_,
    fun x hx ↦ ?_⟩
  · have hR' : ContinuousOn R (U₁ ∩ (U₂ ∩ W)) := hR.mono fun x hx ↦ hx.2.1
    exact hR'.sub ((hπ.mono inter_subset_left).clm_comp hR')
  obtain ⟨hTR, hker⟩ := hW x hx.2
  obtain ⟨hmem, hfix, horth⟩ := hπker x hx.1 hker
  exact ⟨fun y ↦ ⟨R x y, hTR y⟩, hmem, hfix, horth, orthogonal_rightInverse_spec hι hmem horth hTR⟩

end Family

section RealFamily

variable {E F H X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {T : X → E →L[ℝ] F} {x₀ : X} {n : WithTop ℕ∞}

/-- **Orthogonal kernel projections of a real `C^n` Fredholm family are `C^n`.** The projections
of `ContinuousLinearMap.IsFredholm.exists_continuousOn_orthogonal_ker_projection` have the
regularity of the family. -/
theorem IsFredholm.exists_contDiffOn_orthogonal_ker_projection (ι : E →L[ℝ] H)
    (hι : Injective ι) {s : Set X} (hT₀ : IsFredholm (T x₀)) (hT : ContDiffOn ℝ n T s)
    (hs : IsOpen s) (hx₀ : x₀ ∈ s) :
    ∃ U ⊆ s, IsOpen U ∧ x₀ ∈ U ∧ ∃ π : X → E →L[ℝ] E, ContDiffOn ℝ n π U ∧
      ∀ x ∈ U, finrank ℝ (T x).ker = finrank ℝ (T x₀).ker →
        (∀ e, π x e ∈ (T x).ker) ∧ (∀ k ∈ (T x).ker, π x k = k) ∧
          ∀ e, ∀ k ∈ (T x).ker, ⟪ι (e - π x e), ι k⟫_ℝ = 0 := by
  obtain ⟨U, hUs, hU, hx₀U, κ, hκ, hκker⟩ :=
    hT₀.exists_contDiffOn_ker_parametrization hT hs hx₀
  have := hT₀.finite_ker
  obtain ⟨U', hU'U, hU', hx₀U', hG⟩ :=
    orthogonal_ker_projection_of_ker_parametrization ι hι hU hx₀U hκ.continuousOn hκker
  set eL := (euclideanEquiv (T x₀).ker).toContinuousLinearMap
  refine ⟨U', hU'U.trans hUs, hU', hx₀U', fun x ↦ gramProjection ι (κ x ∘L eL), fun x hx ↦ ?_,
    fun x hx ↦ (hG x hx).2⟩
  exact (contDiffAt_gramProjection ι (hG x hx).1).comp_contDiffWithinAt (f := fun x ↦ κ x ∘L eL)
    x ((hκ.clm_comp contDiffOn_const x (hU'U hx)).mono hU'U)

/-- **Orthogonal right inverses of a real surjective `C^n` Fredholm family are `C^n`.** The
projections and right inverses of
`ContinuousLinearMap.IsFredholm.exists_continuousOn_orthogonal_rightInverse` have the regularity
of the family. -/
theorem IsFredholm.exists_contDiffOn_orthogonal_rightInverse (ι : E →L[ℝ] H)
    (hι : Injective ι) {s : Set X} (hT₀ : IsFredholm (T x₀)) (hsurj : Surjective (T x₀))
    (hT : ContDiffOn ℝ n T s) (hs : IsOpen s) (hx₀ : x₀ ∈ s) :
    ∃ U ⊆ s, IsOpen U ∧ x₀ ∈ U ∧ ∃ π : X → E →L[ℝ] E, ∃ Q : X → F →L[ℝ] E,
      ContDiffOn ℝ n π U ∧ ContDiffOn ℝ n Q U ∧ ∀ x ∈ U, Surjective (T x) ∧
        (∀ e, π x e ∈ (T x).ker) ∧ (∀ k ∈ (T x).ker, π x k = k) ∧
        (∀ e, ∀ k ∈ (T x).ker, ⟪ι (e - π x e), ι k⟫_ℝ = 0) ∧
        (∀ y, T x (Q x y) = y) ∧ (∀ y, ∀ k ∈ (T x).ker, ⟪ι (Q x y), ι k⟫_ℝ = 0) ∧
        ∀ e, π x e + Q x (T x e) = e := by
  obtain ⟨U₁, hU₁s, hU₁, hx₀U₁, π, hπ, hπker⟩ :=
    hT₀.exists_contDiffOn_orthogonal_ker_projection ι hι hT hs hx₀
  obtain ⟨S, -, -, U₂, -, hU₂, hx₀U₂, R, P, hR, -, hRP⟩ :=
    hT₀.exists_contDiffOn_splitting hT hs hx₀ (D := ⊤) (by simp)
  obtain ⟨W, hWo, hx₀W, hW⟩ := surjective_of_splitting hT₀ hsurj
    (hT.continuousOn.continuousAt (hs.mem_nhds hx₀)) hx₀U₂ hRP
  refine ⟨U₁ ∩ (U₂ ∩ W), inter_subset_left.trans hU₁s, hU₁.inter (hU₂.inter hWo),
    ⟨hx₀U₁, hx₀U₂, hx₀W⟩, π, fun x ↦ R x - π x ∘L R x, hπ.mono inter_subset_left, ?_,
    fun x hx ↦ ?_⟩
  · have hR' : ContDiffOn ℝ n R (U₁ ∩ (U₂ ∩ W)) := hR.mono fun x hx ↦ hx.2.1
    exact hR'.sub ((hπ.mono inter_subset_left).clm_comp hR')
  obtain ⟨hTR, hker⟩ := hW x hx.2
  obtain ⟨hmem, hfix, horth⟩ := hπker x hx.1 hker
  exact ⟨fun y ↦ ⟨R x y, hTR y⟩, hmem, hfix, horth, orthogonal_rightInverse_spec hι hmem horth hTR⟩

end RealFamily

end ContinuousLinearMap
