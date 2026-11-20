/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.ConstantNullity
public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.RangeProjection

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
family `κ x : ker (T x₀) →L[𝕜] E` whose range is `ker (T x)` at the parameters of constant
nullity. Reading `κ x` on `V = EuclideanSpace 𝕜 (Fin (finrank 𝕜 (T x₀).ker))` through a linear
equivalence, so that the Gram operator is defined, and with `A = ι ∘ κ x`, the projection is

`π x = κ x (A† A)⁻¹ A† ι`

(`ContinuousLinearMap.gramProjection`), where the Gram operator `A† A` of `V` is invertible as
long as `A` is injective, which is an open condition. Since inversion is continuous on the units of
the complete normed ring `V →L[𝕜] V`, `π x` is continuous in `x`. It fixes `ker (T x)` and
`ι (e - π x e)` is orthogonal to `ι (ker (T x))`. When `T x₀` is onto, so is every `T x` near
`x₀`, with a continuous family of right inverses `R x`
(`ContinuousLinearMap.IsFredholm.exists_continuousOn_splitting`), and `Q x = (1 - π x) R x` is
the right inverse with values in the `ι`-orthogonal complement of the kernel. Every `e ∈ E` then
splits as `e = π x e + Q x (T x e)`.

Over `ℝ`, a `C^n` family has `C^n` projections and right inverses, since the adjoint is a real
continuous linear map of operators (`ContinuousLinearMap.adjointRealCLM`) and inversion is
analytic. Over `ℂ` the projection depends on `κ x` conjugate-linearly as well, so it is not
complex-differentiable, and the `C^n` statements are made for real families.

For the gauge-fixed operator of a plane vortex or of the linearized Seiberg–Witten equations on
a Sobolev space, these are the kernel projections and right inverses on `L²`-orthogonal
complements of the kernel, which move continuously with the solution about which one linearizes.

## Main results

* `ContinuousLinearMap.rightInverse_sub_comp` and
  `ContinuousLinearMap.apply_add_apply_apply_eq_self`: for a single operator `T` and `π` with
  values in its kernel, `R - π R` is a right inverse of `T` whenever `R` is, and when `π` projects
  along the `ι`-orthogonal complement of the kernel, a right inverse `Q` with values in that
  complement splits every `e` as `e = π e + Q (T e)`.
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

section SingleOperator

variable {𝕜 E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- If `π` takes values in the kernel of `T` and `R` is a right inverse of `T`, then so is
`R - π R`. -/
theorem rightInverse_sub_comp [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [IsTopologicalAddGroup E] [AddCommGroup F] [Module 𝕜 F]
    {T : E →L[𝕜] F} {π : E →L[𝕜] E} {R : F →L[𝕜] E}
    (hmem : ∀ e, π e ∈ T.ker) (hR : RightInverse R T) : RightInverse (R - π ∘L R) T := fun y ↦ by
  have h0 : T (π (R y)) = 0 := LinearMap.mem_ker.1 (hmem (R y))
  simp [hR y, h0]

/-- Let `ι` be an injective operator into an inner product space, let `π` take values in the kernel
of `T` with `ι (e - π e)` orthogonal to `ι` of the kernel, and let `Q` be a right inverse of `T`
whose values are `ι`-orthogonal to the kernel. Then every `e` splits as `e = π e + Q (T e)`. -/
theorem apply_add_apply_apply_eq_self {H : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    {ι : E →L[𝕜] H} (hι : Injective ι) {T : E →L[𝕜] F}
    {π : E →L[𝕜] E} {Q : F →L[𝕜] E} (hmem : ∀ e, π e ∈ T.ker)
    (horth : ∀ e, ∀ k ∈ T.ker, ⟪ι (e - π e), ι k⟫_𝕜 = 0) (hQ : RightInverse Q T)
    (hQorth : ∀ y, ∀ k ∈ T.ker, ⟪ι (Q y), ι k⟫_𝕜 = 0) (e : E) : π e + Q (T e) = e := by
  -- The defect `d = e - π e - Q (T e)` lies in the kernel and is `ι`-orthogonal to it.
  set d := e - π e - Q (T e)
  have h0 : T (π e) = 0 := LinearMap.mem_ker.1 (hmem e)
  have hd : d ∈ T.ker := by
    simp [d, hQ (T e), h0]
  have hdd : ⟪ι d, ι d⟫_𝕜 = 0 := by
    have h : ⟪ι (e - π e) - ι (Q (T e)), ι d⟫_𝕜 = 0 := by
      rw [inner_sub_left, horth e d hd, hQorth _ d hd, sub_zero]
    rwa [← map_sub] at h
  have : d = 0 := hι (by simpa using hdd)
  exact (sub_eq_zero.1 (by simpa only [d, sub_sub] using this)).symm

end SingleOperator

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
  have hK : (κ x ∘L eL).range = (T x).ker := by
    rw [← (hκker x hx.1 hker).2]
    exact LinearMap.range_comp_of_range_eq_top _
      (LinearEquiv.range (euclideanEquiv (T x₀).ker).toLinearEquiv)
  rw [← hK]
  refine ⟨gramProjection_apply_mem_range ι _, fun k hk ↦ ?_, fun e k hk ↦ ?_⟩
  · obtain ⟨v, rfl⟩ := hk
    exact gramProjection_apply_apply hx.2 v
  · obtain ⟨v, rfl⟩ := hk
    exact gramProjection_inner_eq_zero hx.2 e v

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
    have hP : (P x y : F) = 0 := by simpa [hS] using (P x y).property
    simpa [hP] using (hRP x hx.1).1 y
  have hsurjx : Surjective (T x) := fun y ↦ ⟨R x y, hTR y⟩
  exact ⟨hTR, (hW x hx.2).2
    (by rw [LinearMap.range_eq_top.2 hsurjx, LinearMap.range_eq_top.2 hsurj])⟩

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace H] [TopologicalSpace X] in
/-- The pointwise half of the right inverse theorems for families: where `π x` is the projection
onto `ker (T x)` along its `ι`-orthogonal complement at constant nullity and `R x` is a right
inverse of `T x` at constant nullity, `T x` is onto and `R x - π x R x` is the right inverse with
values in that complement. -/
private theorem orthogonal_rightInverse_of_projection {ι : E →L[𝕜] H} (hι : Injective ι)
    {U₁ U₂ W : Set X} {π : X → E →L[𝕜] E} {R : X → F →L[𝕜] E}
    (hπker : ∀ x ∈ U₁, finrank 𝕜 (T x).ker = finrank 𝕜 (T x₀).ker →
      (∀ e, π x e ∈ (T x).ker) ∧ (∀ k ∈ (T x).ker, π x k = k) ∧
        ∀ e, ∀ k ∈ (T x).ker, ⟪ι (e - π x e), ι k⟫_𝕜 = 0)
    (hW : ∀ x ∈ U₂ ∩ W, (∀ y, T x (R x y) = y) ∧ finrank 𝕜 (T x).ker = finrank 𝕜 (T x₀).ker) :
    ∀ x ∈ U₁ ∩ (U₂ ∩ W), Surjective (T x) ∧
      (∀ e, π x e ∈ (T x).ker) ∧ (∀ k ∈ (T x).ker, π x k = k) ∧
      (∀ e, ∀ k ∈ (T x).ker, ⟪ι (e - π x e), ι k⟫_𝕜 = 0) ∧
      (∀ y, T x ((R x - π x ∘L R x) y) = y) ∧
      (∀ y, ∀ k ∈ (T x).ker, ⟪ι ((R x - π x ∘L R x) y), ι k⟫_𝕜 = 0) ∧
      ∀ e, π x e + (R x - π x ∘L R x) (T x e) = e := fun x hx ↦ by
  obtain ⟨hTR, hker⟩ := hW x hx.2
  obtain ⟨hmem, hfix, horth⟩ := hπker x hx.1 hker
  have hQorth : ∀ y, ∀ k ∈ (T x).ker, ⟪ι ((R x - π x ∘L R x) y), ι k⟫_𝕜 = 0 :=
    fun y k hk ↦ horth (R x y) k hk
  exact ⟨fun y ↦ ⟨R x y, hTR y⟩, hmem, hfix, horth, rightInverse_sub_comp hmem hTR, hQorth,
    apply_add_apply_apply_eq_self hι hmem horth (rightInverse_sub_comp hmem hTR) hQorth⟩

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
    orthogonal_rightInverse_of_projection hι hπker hW⟩
  have hR' : ContinuousOn R (U₁ ∩ (U₂ ∩ W)) := hR.mono fun x hx ↦ hx.2.1
  exact hR'.sub ((hπ.mono inter_subset_left).clm_comp hR')

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
    orthogonal_rightInverse_of_projection hι hπker hW⟩
  have hR' : ContDiffOn ℝ n R (U₁ ∩ (U₂ ∩ W)) := hR.mono fun x hx ↦ hx.2.1
  exact hR'.sub ((hπ.mono inter_subset_left).clm_comp hR')

end RealFamily

end ContinuousLinearMap
