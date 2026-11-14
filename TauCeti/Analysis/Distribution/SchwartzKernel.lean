/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ComplexPairing
public import TauCeti.Analysis.Distribution.TestFunction.SchwartzKernel
import TauCeti.Analysis.Distribution.Gluing
import TauCeti.Topology.MetricSpace.Pseudo.Lemmas

/-!
# The Schwartz kernel theorem on open sets

Let `Ω ⊆ ℝ^a` and `O ⊆ ℝ^b` be open sets and let `B` be a complex bilinear map on the complex
test functions `𝓓(Ω, ℂ) × 𝓓(O, ℂ)`, with values in a complex Banach space `F`, which is
continuous on each pair of compact sets: for compact sets `K₁ ⊆ Ω` and `K₂ ⊆ O` there are `C` and
`k` with `‖B φ ψ‖ ≤ C N_k(φ) N_k(ψ)` for `φ` supported in `K₁` and `ψ` supported in `K₂`, where
`N_k` is the `C^k` seminorm. Then there is exactly one continuous linear map `T` on the complex
test functions on `Ω × O` with

`T (φ ⊗ ψ) = B φ ψ`,

where `(φ ⊗ ψ)(x, y) = φ x * ψ y` is `TestFunction.tensor`
(`LinearMap.existsUnique_schwartzKernel_testFunction`). This is the Schwartz kernel theorem in the
form of the construction in Hörmander's proof, which first derives the estimate above from the
continuity of the map `ψ ↦ B (·) ψ` from `𝓓(O)` to `𝓓'(Ω)`; here the estimate is the hypothesis.
For `F = ℂ` the kernel is an actual distribution `K ∈ 𝓓'(Ω × O, ℂ)`, acting on complex test
functions through its complex-linear extension `Distribution.complexPairing`
(`LinearMap.existsUnique_schwartzKernel_distribution`).

## Proof

The kernel is assembled from the kernels on small boxes supplied by
`LinearMap.exists_schwartzKernel_supportedIn`. Call a box `closedBall x r ×ˢ closedBall y s` with
`r, s < 1 / 2` *small*; its factors meet none of their nonzero integer translates, so the theorem
on compact sets applies to it.

* **Uniqueness.** Two kernels of `B` on an open set `W ⊆ Ω × O` agree on every test supported in
  the half-size box `closedBall x (r / 2) ×ˢ closedBall y (s / 2)` of a small box inside `W`, since
  both restrict to the kernel on that half-size box. These half-size boxes form neighbourhoods
  of every point of `W`, so the two kernels are equal by localization
  (`AddMonoidHom.eq_zero_of_locally_vanishing`).
* **Existence.** On each open box `ball x (r / 2) ×ˢ ball y (s / 2)` the kernel on the compact
  half-size box is a kernel of `B`. By uniqueness these local kernels agree on overlaps, so they
  glue to a continuous complex-linear map on `Ω × O`
  (`Distribution.existsUnique_gluing_of_isScalarTower`). To evaluate it on `φ ⊗ ψ`, split `φ` and
  `ψ` into finite sums of test functions supported in small balls
  (`TestFunction.exists_sum_subordinate`); then
  `φ ⊗ ψ = ∑ᵢ ∑ⱼ φᵢ ⊗ ψⱼ`, each term lies in one of the boxes, and bilinearity of `B` gives
  `∑ᵢ ∑ⱼ B φᵢ ψⱼ = B φ ψ`.

## Main declarations

* `LinearMap.existsUnique_schwartzKernel_testFunction`: the Schwartz kernel theorem on open sets
  of `ℝ^a × ℝ^b`.
* `LinearMap.existsUnique_schwartzKernel_distribution`: its form for complex-valued
  distributions.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 5.2.1 (the Schwartz kernel theorem) and its proof.
-/

public section

noncomputable section

open Function Metric Set TopologicalSpace TestFunction
open scoped ContDiff Distributions

namespace LinearMap

variable {a b : Type*} [Fintype a] [Fintype b]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {Ω : Opens (a → ℝ)} {O : Opens (b → ℝ)} {B : 𝓓(Ω, ℂ) →ₗ[ℂ] 𝓓(O, ℂ) →ₗ[ℂ] F}

/-- `S` is a kernel of `B` on tests on `W`: it takes the value `B φ ψ` on every test function on
`W` of the form `(x, y) ↦ φ x * ψ y`. -/
private def IsKernelOn (B : 𝓓(Ω, ℂ) →ₗ[ℂ] 𝓓(O, ℂ) →ₗ[ℂ] F) {W : Opens ((a → ℝ) × (b → ℝ))}
    (S : 𝓓(W, ℂ) →L[ℂ] F) : Prop :=
  ∀ (φ : 𝓓(Ω, ℂ)) (ψ : 𝓓(O, ℂ)) (χ : 𝓓(W, ℂ)), (∀ p, χ p = φ p.1 * ψ p.2) → S χ = B φ ψ

/-- A closed ball as a compact set. -/
private def closedBallCompacts {d : Type*} [Fintype d] (x : d → ℝ) (r : ℝ) : Compacts (d → ℝ) :=
  ⟨closedBall x r, isCompact_closedBall x r⟩

/-- A smaller closed ball, as a compact set, lies in every set containing a closed ball. -/
private theorem coe_closedBallCompacts_subset {d : Type*} [Fintype d] {x : d → ℝ} {r r' : ℝ}
    {U : Set (d → ℝ)} (hr : r' ≤ r) (h : closedBall x r ⊆ U) :
    (closedBallCompacts x r' : Set (d → ℝ)) ⊆ U :=
  (closedBall_subset_closedBall hr).trans h

/-- The centres and radii in `(0, 1 / 2)` of the closed balls contained in `U`. -/
private abbrev SmallBall {d : Type*} [Fintype d] (U : Set (d → ℝ)) : Type _ :=
  {q : (d → ℝ) × ℝ // 0 < q.2 ∧ q.2 < 1 / 2 ∧ closedBall q.1 q.2 ⊆ U}

/-- The open balls of half the radius of the small balls in an open set cover it. -/
private theorem subset_iUnion_ball_smallBall {d : Type*} [Fintype d] {U : Set (d → ℝ)}
    (hU : IsOpen U) : U ⊆ ⋃ i : SmallBall U, ball i.1.1 (i.1.2 / 2) := fun x hx ↦ by
  obtain ⟨r, hr₀, hr, hrU⟩ :=
    TauCeti.exists_pos_lt_closedBall_subset (hU.mem_nhds hx) one_half_pos
  exact mem_iUnion.2 ⟨⟨(x, r), hr₀, hr, hrU⟩, mem_ball_self (by positivity)⟩

/-- The open ball of half the radius of a small ball in `U` lies in `U`. -/
private theorem ball_smallBall_subset {d : Type*} [Fintype d] {U : Set (d → ℝ)} (i : SmallBall U) :
    ball i.1.1 (i.1.2 / 2) ⊆ U :=
  ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith [i.2.1])).trans i.2.2.2)

/-- The products of two small balls, in `Ω` and in `O`. -/
private abbrev SmallBox (Ω : Opens (a → ℝ)) (O : Opens (b → ℝ)) : Type _ :=
  SmallBall (Ω : Set (a → ℝ)) × SmallBall (O : Set (b → ℝ))

omit [CompleteSpace F] in
/-- A map on tests on `V = Ω × O` which takes the value `B φ ψ` on `φ ⊗ ψ` whenever `φ` and `ψ` are
supported in open balls of half the radius of small balls takes this value on every `φ ⊗ ψ`: split
`φ` and `ψ` into tests supported in such balls and use bilinearity. -/
private theorem apply_tensor_of_forall_smallBall {V : Opens ((a → ℝ) × (b → ℝ))}
    (hV : (Ω : Set (a → ℝ)) ×ˢ (O : Set (b → ℝ)) ⊆ V) (S : 𝓓(V, ℂ) →L[ℂ] F)
    (hS : ∀ (i : SmallBall (Ω : Set (a → ℝ))) (j : SmallBall (O : Set (b → ℝ))) (φ : 𝓓(Ω, ℂ))
      (ψ : 𝓓(O, ℂ)), tsupport φ ⊆ ball i.1.1 (i.1.2 / 2) → tsupport ψ ⊆ ball j.1.1 (j.1.2 / 2) →
        S (φ.tensor ψ hV) = B φ ψ)
    (φ : 𝓓(Ω, ℂ)) (ψ : 𝓓(O, ℂ)) : S (φ.tensor ψ hV) = B φ ψ := by
  obtain ⟨s₁, φs, hφs, hφsum, -⟩ := φ.exists_sum_subordinate _ (fun _ ↦ isOpen_ball)
    (φ.tsupport_subset.trans (subset_iUnion_ball_smallBall Ω.isOpen))
  obtain ⟨s₂, ψs, hψs, hψsum, -⟩ := ψ.exists_sum_subordinate _ (fun _ ↦ isOpen_ball)
    (ψ.tsupport_subset.trans (subset_iUnion_ball_smallBall O.isOpen))
  have hsplit : φ.tensor ψ hV = ∑ i, ∑ j, (φs i).tensor (ψs j) hV := by
    ext p
    simp [← hφsum, ← hψsum, Finset.sum_mul_sum]
  have hterm (i : s₁) (j : s₂) : S ((φs i).tensor (ψs j) hV) = B (φs i) (ψs j) :=
    hS i.1 j.1 (φs i) (ψs j) (hφs i) (hψs j)
  rw [hsplit, map_sum]
  simp only [map_sum, hterm]
  conv_rhs => rw [← hφsum, ← hψsum]
  simp only [map_sum, LinearMap.sum_apply]
  exact Finset.sum_comm

section Kernel

variable (hB : ∀ (K₁ : Compacts (a → ℝ)) (K₂ : Compacts (b → ℝ)) (hK₁ : (K₁ : Set (a → ℝ)) ⊆ Ω)
  (hK₂ : (K₂ : Set (b → ℝ)) ⊆ O), ∃ (C : ℝ) (k : ℕ), ∀ φ ψ,
    ‖B (ofSupportedIn hK₁ φ) (ofSupportedIn hK₂ ψ)‖ ≤
      C * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₁ k φ *
        ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₂ k ψ)
include hB

/-- The kernel of `B` on the half-size box of a small box, from the theorem on compact sets: it
represents `B` there, and every kernel of `B` on a test space containing the small box restricts
to it. -/
private theorem exists_kernel_halfBox {x : a → ℝ} {y : b → ℝ} {r s : ℝ} (hr₀ : 0 < r)
    (hr : r < 1 / 2) (hs₀ : 0 < s) (hs : s < 1 / 2) (hxΩ : closedBall x r ⊆ Ω)
    (hyO : closedBall y s ⊆ O) :
    ∃ T : 𝓓_{closedBallCompacts x (r / 2) ×ˢ closedBallCompacts y (s / 2)}(
        (a → ℝ) × (b → ℝ), ℂ) →L[ℂ] F,
      (∀ (φ : 𝓓_{closedBallCompacts x (r / 2)}(a → ℝ, ℂ))
        (ψ : 𝓓_{closedBallCompacts y (s / 2)}(b → ℝ, ℂ)),
          T (φ.tensor ψ) = B (ofSupportedIn (coe_closedBallCompacts_subset (by linarith) hxΩ) φ)
            (ofSupportedIn (coe_closedBallCompacts_subset (by linarith) hyO) ψ)) ∧
      ∀ {W : Opens ((a → ℝ) × (b → ℝ))} (S : 𝓓(W, ℂ) →L[ℂ] F),
        closedBall x r ×ˢ closedBall y s ⊆ W → IsKernelOn B S →
          ∀ (Φ : 𝓓(W, ℂ)) (hΦ : tsupport Φ ⊆ closedBall x (r / 2) ×ˢ closedBall y (s / 2)),
            S Φ = T (.of_support_subset Φ.contDiff ((subset_tsupport _).trans hΦ)) := by
  have hK₁ : (closedBallCompacts x (r / 2) : Set (a → ℝ)) ⊆
      interior (closedBallCompacts x r : Set (a → ℝ)) :=
    (closedBall_subset_ball (by linarith)).trans ball_subset_interior_closedBall
  have hK₂ : (closedBallCompacts y (s / 2) : Set (b → ℝ)) ⊆
      interior (closedBallCompacts y s : Set (b → ℝ)) :=
    (closedBall_subset_ball (by linarith)).trans ball_subset_interior_closedBall
  have hKK₁ : closedBallCompacts x (r / 2) ≤ closedBallCompacts x r := hK₁.trans interior_subset
  have hKK₂ : closedBallCompacts y (s / 2) ≤ closedBallCompacts y s := hK₂.trans interior_subset
  have hKK : closedBallCompacts x (r / 2) ×ˢ closedBallCompacts y (s / 2) ≤
      closedBallCompacts x r ×ˢ closedBallCompacts y s := by
    rw [← SetLike.coe_subset_coe, Compacts.coe_prod, Compacts.coe_prod]
    exact prod_mono hKK₁ hKK₂
  have hxΩ' := coe_closedBallCompacts_subset le_rfl hxΩ
  have hyO' := coe_closedBallCompacts_subset le_rfl hyO
  -- The restriction of `B` to tests supported in the small box and its continuity estimate.
  obtain ⟨T, hT, hTuniq⟩ := exists_schwartzKernel_supportedIn
    (B.compl₁₂ (ofSupportedInCLM ℂ hxΩ').toLinearMap (ofSupportedInCLM ℂ hyO').toLinearMap)
    (hB _ _ hxΩ' hyO') (fun _ hz _ ↦ UnitAddTorus.eq_zero_of_add_mem_closedBall hr hz)
    (fun _ hz _ ↦ UnitAddTorus.eq_zero_of_add_mem_closedBall hs hz) hK₁ hK₂
  refine ⟨T, fun φ ψ ↦ ?_, fun {W} S hW hS Φ hΦ ↦ ?_⟩
  · rw [hT, compl₁₂_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe]
    congr 2
    · exact TestFunction.ext fun _ ↦ by simp [hKK₁]
    · exact TestFunction.ext fun _ ↦ by simp [hKK₂]
  · -- `S`, restricted to tests supported in the small box, is a kernel of `B` there.
    have hWK : ((closedBallCompacts x r ×ˢ closedBallCompacts y s : Compacts _) :
        Set ((a → ℝ) × (b → ℝ))) ⊆ W := by
      rwa [Compacts.coe_prod]
    have h := hTuniq (S ∘L ofSupportedInCLM ℂ hWK) (fun φ ψ ↦ hS _ _ _ fun p ↦ by simp)
      (.of_support_subset Φ.contDiff ((subset_tsupport _).trans hΦ))
    rw [← h, ContinuousLinearMap.comp_apply]
    congr 1
    ext p
    simp [hKK]

/-- **Uniqueness of kernels.** Two kernels of `B` on an open subset of `Ω × O` are equal. -/
private theorem eq_of_isKernelOn {W : Opens ((a → ℝ) × (b → ℝ))}
    (hWΩ : (W : Set ((a → ℝ) × (b → ℝ))) ⊆ (Ω : Set (a → ℝ)) ×ˢ (O : Set (b → ℝ)))
    {S S' : 𝓓(W, ℂ) →L[ℂ] F} (hS : IsKernelOn B S) (hS' : IsKernelOn B S') : S = S' := by
  have h := AddMonoidHom.eq_zero_of_locally_vanishing
    ((S : 𝓓(W, ℂ) →+ F) - (S' : 𝓓(W, ℂ) →+ F)) fun p hp ↦ ?_
  · ext Φ
    simpa [sub_eq_zero] using DFunLike.congr_fun h Φ
  -- Around `p`, both kernels restrict to the kernel on a half-size box.
  obtain ⟨r, hr₀, hr, hrW⟩ :=
    TauCeti.exists_pos_lt_closedBall_subset (W.isOpen.mem_nhds hp) one_half_pos
  rw [← closedBall_prod_same] at hrW
  have hxΩ : closedBall p.1 r ⊆ Ω := fun z hz ↦
    (hWΩ (hrW (mk_mem_prod hz (mem_closedBall_self hr₀.le)))).1
  have hyO : closedBall p.2 r ⊆ O := fun z hz ↦
    (hWΩ (hrW (mk_mem_prod (mem_closedBall_self hr₀.le) hz))).2
  obtain ⟨T, -, hT⟩ := exists_kernel_halfBox hB hr₀ hr hr₀ hr hxΩ hyO
  refine ⟨ball p.1 (r / 2) ×ˢ ball p.2 (r / 2), isOpen_ball.prod isOpen_ball,
    ⟨mem_ball_self (by positivity),
    mem_ball_self (by positivity)⟩, fun Φ hΦ ↦ ?_⟩
  have hΦ' := hΦ.trans (prod_mono ball_subset_closedBall ball_subset_closedBall)
  simpa [sub_eq_zero] using (hT S hrW hS Φ hΦ').trans (hT S' hrW hS' Φ hΦ').symm

/-- **Kernels on open boxes.** On the open box `ball x (r / 2) ×ˢ ball y (s / 2)` of a small box,
`B` has a kernel. -/
private theorem exists_isKernelOn_box {x : a → ℝ} {y : b → ℝ} {r s : ℝ} (hr₀ : 0 < r)
    (hr : r < 1 / 2) (hs₀ : 0 < s) (hs : s < 1 / 2) (hxΩ : closedBall x r ⊆ Ω)
    (hyO : closedBall y s ⊆ O) {U : Opens ((a → ℝ) × (b → ℝ))}
    (hU : (U : Set ((a → ℝ) × (b → ℝ))) = ball x (r / 2) ×ˢ ball y (s / 2)) :
    ∃ T : 𝓓(U, ℂ) →L[ℂ] F, IsKernelOn B T := by
  obtain ⟨T₀, hT₀, -⟩ := exists_kernel_halfBox hB hr₀ hr hs₀ hs hxΩ hyO
  have hUK : (U : Set ((a → ℝ) × (b → ℝ))) ⊆
      (closedBallCompacts x (r / 2) ×ˢ closedBallCompacts y (s / 2) : Compacts _) := by
    rw [hU, Compacts.coe_prod]
    exact prod_mono ball_subset_closedBall ball_subset_closedBall
  -- The local kernel, precomposed with the inclusion of tests on `U` into tests supported in `K`.
  let T : 𝓓(U, ℂ) →L[ℂ] F := TestFunction.limitCLM ℂ
    (fun θ ↦ T₀ (.of_support_subset θ.contDiff ((subset_tsupport _).trans
      (θ.tsupport_subset.trans hUK))))
    (fun _ _ ↦ T₀ ∘L ContDiffMapSupportedIn.monoCLM ℂ)
    (fun L hL f ↦ by
      have hLK : L ≤ closedBallCompacts x (r / 2) ×ˢ closedBallCompacts y (s / 2) :=
        hL.trans hUK
      rw [ContinuousLinearMap.comp_apply]
      congr 1
      ext p
      simp [hLK])
  refine ⟨T, fun φ ψ χ hχ ↦ ?_⟩
  -- If one factor vanishes, so does `χ`; otherwise both factors are supported in the closed
  -- balls, since `χ` is supported in `U`.
  rcases eq_or_ne ψ 0 with rfl | hψ
  · obtain rfl : χ = 0 := TestFunction.ext fun p ↦ by simp [hχ]
    simp
  rcases eq_or_ne φ 0 with rfl | hφ
  · obtain rfl : χ = 0 := TestFunction.ext fun p ↦ by simp [hχ]
    simp
  obtain ⟨y₀, hy₀⟩ : ∃ y, ψ y ≠ 0 := by
    by_contra! h
    exact hψ (TestFunction.ext fun y ↦ by simp [h])
  obtain ⟨x₀, hx₀⟩ : ∃ x, φ x ≠ 0 := by
    by_contra! h
    exact hφ (TestFunction.ext fun x ↦ by simp [h])
  have hmem {p : (a → ℝ) × (b → ℝ)} (hp : φ p.1 * ψ p.2 ≠ 0) :
      p ∈ ball x (r / 2) ×ˢ ball y (s / 2) := by
    rw [← hU]
    exact χ.tsupport_subset (subset_tsupport _ (by rwa [mem_support, hχ]))
  have hφK : support φ ⊆ closedBallCompacts x (r / 2) := fun z hz ↦
    ball_subset_closedBall (hmem (p := (z, y₀)) (mul_ne_zero hz hy₀)).1
  have hψK : support ψ ⊆ closedBallCompacts y (s / 2) := fun z hz ↦
    ball_subset_closedBall (hmem (p := (x₀, z)) (mul_ne_zero hx₀ hz)).2
  have hT : T χ = T₀ (.of_support_subset χ.contDiff
      ((subset_tsupport _).trans (χ.tsupport_subset.trans hUK))) :=
    TestFunction.limitCLM_apply ..
  have hχK : (.of_support_subset χ.contDiff ((subset_tsupport _).trans
      (χ.tsupport_subset.trans hUK)) :
        𝓓_{closedBallCompacts x (r / 2) ×ˢ closedBallCompacts y (s / 2)}((a → ℝ) × (b → ℝ), ℂ)) =
      (ContDiffMapSupportedIn.of_support_subset φ.contDiff hφK).tensor
        (.of_support_subset ψ.contDiff hψK) := by
    ext p
    simp [hχ]
  rw [hT, hχK, hT₀]
  exact congrArg₂ (B · ·) (TestFunction.ext fun _ ↦ by simp) (TestFunction.ext fun _ ↦ by simp)

variable (B) in
/-- **The Schwartz kernel theorem on open sets.** Let `B` be a complex bilinear map on the complex
test functions on open sets `Ω ⊆ ℝ^a` and `O ⊆ ℝ^b`, with values in a complex Banach space, such
that for all compact sets `K₁ ⊆ Ω` and `K₂ ⊆ O` some `C` and `k` give
`‖B φ ψ‖ ≤ C N_k(φ) N_k(ψ)` for `φ` supported in `K₁` and `ψ` supported in `K₂`. Then there is a
unique continuous linear map `T` on the complex test functions on `V = Ω × O` with
`T (φ ⊗ ψ) = B φ ψ` for all `φ` and `ψ`. -/
theorem existsUnique_schwartzKernel_testFunction {V : Opens ((a → ℝ) × (b → ℝ))}
    (hV : (V : Set ((a → ℝ) × (b → ℝ))) = (Ω : Set (a → ℝ)) ×ˢ (O : Set (b → ℝ))) :
    ∃! T : 𝓓(V, ℂ) →L[ℂ] F, ∀ (φ : 𝓓(Ω, ℂ)) (ψ : 𝓓(O, ℂ)),
      T (φ.tensor ψ hV.symm.subset) = B φ ψ := by
  -- Uniqueness is `eq_of_isKernelOn`. For existence, the kernels on the open boxes of the small
  -- boxes agree on overlaps and glue to a complex-linear map `S`, which represents `B` on tensor
  -- products by a partition of unity.
  -- A kernel on `V` in the sense of tensor products is a kernel in the sense of `IsKernelOn`.
  have hker {T : 𝓓(V, ℂ) →L[ℂ] F} (hT : ∀ φ ψ, T (φ.tensor ψ hV.symm.subset) = B φ ψ) :
      IsKernelOn B T := fun φ ψ χ hχ ↦ by
    rw [← hT φ ψ]
    congr 1
    ext p
    simp [hχ]
  -- The open boxes `ball x (r / 2) ×ˢ ball y (s / 2)` of the small boxes in `Ω × O`.
  let U (ij : SmallBox Ω O) : Opens ((a → ℝ) × (b → ℝ)) :=
    ⟨ball ij.1.1.1 (ij.1.1.2 / 2) ×ˢ ball ij.2.1.1 (ij.2.1.2 / 2), isOpen_ball.prod isOpen_ball⟩
  have hUV (ij : SmallBox Ω O) : (U ij : Set ((a → ℝ) × (b → ℝ))) ⊆ Ω ×ˢ O :=
    prod_mono (ball_smallBall_subset ij.1) (ball_smallBall_subset ij.2)
  have hU : ⨆ ij, U ij = V := by
    refine SetLike.coe_injective ?_
    rw [Opens.coe_iSup, hV]
    refine subset_antisymm (iUnion_subset hUV) fun p hp ↦ ?_
    obtain ⟨i, hi⟩ := mem_iUnion.1 (subset_iUnion_ball_smallBall Ω.isOpen hp.1)
    obtain ⟨j, hj⟩ := mem_iUnion.1 (subset_iUnion_ball_smallBall O.isOpen hp.2)
    exact mem_iUnion.2 ⟨(i, j), hi, hj⟩
  choose T hT using fun ij : SmallBox Ω O ↦ exists_isKernelOn_box hB ij.1.2.1 ij.1.2.2.1 ij.2.2.1
    ij.2.2.2.1 ij.1.2.2.2 ij.2.2.2.2 (U := U ij) rfl
  -- The local kernels agree on overlaps, since both restrict to kernels of `B` there.
  have hcompat (ij kl : SmallBox Ω O) (θ : 𝓓(U ij ⊓ U kl, ℂ)) :
      T ij (monoCLM ℂ θ) = T kl (monoCLM ℂ θ) := by
    have hres (mn : SmallBox Ω O) (h : U ij ⊓ U kl ≤ U mn) :
        IsKernelOn B (T mn ∘L (monoCLM ℂ : 𝓓(U ij ⊓ U kl, ℂ) →L[ℂ] 𝓓(U mn, ℂ))) :=
      fun φ ψ χ hχ ↦ hT mn φ ψ _ fun p ↦ by simp [h, hχ]
    have hW : ((U ij ⊓ U kl : Opens _) : Set ((a → ℝ) × (b → ℝ))) ⊆ Ω ×ˢ O := by
      rw [Opens.coe_inf]
      exact inter_subset_left.trans (hUV ij)
    exact DFunLike.congr_fun (eq_of_isKernelOn hB hW
      (hres ij inf_le_left) (hres kl inf_le_right)) θ
  obtain ⟨S, hS, -⟩ := Distribution.existsUnique_gluing_of_isScalarTower hU hcompat
  have hUle (ij : SmallBox Ω O) : U ij ≤ V := hU ▸ le_iSup U ij
  -- On `φ ⊗ ψ` with `φ` and `ψ` supported in the balls of a box `U ij`, the glued map is the local
  -- kernel on `U ij`.
  have hkernel : ∀ φ ψ, S (φ.tensor ψ hV.symm.subset) = B φ ψ :=
    apply_tensor_of_forall_smallBall _ S fun i j φ ψ hφ hψ ↦ by
      have hΦ := (tsupport_tensor_subset hV.symm.subset φ ψ).trans (prod_mono hφ hψ)
      let θ : 𝓓(U (i, j), ℂ) := ⟨_, (φ.tensor ψ _).contDiff, (φ.tensor ψ _).hasCompactSupport, hΦ⟩
      have hθ : monoCLM ℂ θ = φ.tensor ψ hV.symm.subset :=
        TestFunction.ext fun p ↦ by simp [θ, hUle (i, j)]
      rw [← hθ, ← ContinuousLinearMap.comp_apply, hS]
      exact hT _ _ _ θ fun p ↦ by simp [θ]
  exact ⟨S, hkernel, fun T' hT' ↦ eq_of_isKernelOn hB hV.subset (hker hT') (hker hkernel)⟩

end Kernel

/-- **The Schwartz kernel theorem for distributions on open sets.** Let `B` be a complex bilinear
form on the complex test functions on open sets `Ω ⊆ ℝ^a` and `O ⊆ ℝ^b` such that for all
compact sets `K₁ ⊆ Ω` and `K₂ ⊆ O` some `C` and `k` give `|B φ ψ| ≤ C N_k(φ) N_k(ψ)` for `φ`
supported in `K₁` and `ψ` supported in `K₂`. Then there is a unique complex-valued distribution
`K` on `V = Ω × O` whose complex-linear extension takes the value `B φ ψ` on `φ ⊗ ψ`. -/
theorem existsUnique_schwartzKernel_distribution (B : 𝓓(Ω, ℂ) →ₗ[ℂ] 𝓓(O, ℂ) →ₗ[ℂ] ℂ)
    (hB : ∀ (K₁ : Compacts (a → ℝ)) (K₂ : Compacts (b → ℝ)) (hK₁ : (K₁ : Set (a → ℝ)) ⊆ Ω)
      (hK₂ : (K₂ : Set (b → ℝ)) ⊆ O), ∃ (C : ℝ) (k : ℕ), ∀ φ ψ,
        ‖B (ofSupportedIn hK₁ φ) (ofSupportedIn hK₂ ψ)‖ ≤
          C * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₁ k φ *
            ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₂ k ψ)
    {V : Opens ((a → ℝ) × (b → ℝ))}
    (hV : (V : Set ((a → ℝ) × (b → ℝ))) = (Ω : Set (a → ℝ)) ×ˢ (O : Set (b → ℝ))) :
    ∃! K : 𝓓'(V, ℂ), ∀ (φ : 𝓓(Ω, ℂ)) (ψ : 𝓓(O, ℂ)),
      K.complexPairing (φ.tensor ψ hV.symm.subset) = B φ ψ := by
  obtain ⟨T, hT, hTuniq⟩ := existsUnique_schwartzKernel_testFunction B hB hV
  -- The restriction of `T` to real test functions, whose complex-linear extension is `T`.
  let K : 𝓓'(V, ℂ) := T.restrictScalars ℝ ∘L postcompCLM (𝕜 := ℝ) Complex.ofRealCLM
  have hK : K.complexPairing = T := by
    ext Φ
    have hΦ : postcompCLM (𝕜 := ℝ) Complex.ofRealCLM (postcompCLM (𝕜 := ℝ) Complex.reCLM Φ) +
        Complex.I • postcompCLM (𝕜 := ℝ) Complex.ofRealCLM
          (postcompCLM (𝕜 := ℝ) Complex.imCLM Φ) = Φ := by
      ext p
      simp [mul_comm Complex.I, Complex.re_add_im]
    have hKapp (φ : 𝓓(V, ℝ)) : K φ = T (postcompCLM (𝕜 := ℝ) Complex.ofRealCLM φ) := rfl
    rw [Distribution.complexPairing_apply, hKapp, hKapp, ← smul_eq_mul, ← map_smul, ← map_add,
      hΦ]
  refine ⟨K, fun φ ψ ↦ by rw [hK, hT], fun K' hK' ↦ ?_⟩
  have h := hTuniq K'.complexPairing hK'
  ext φ
  rw [← Distribution.complexPairing_postcompCLM_ofRealCLM, h, ← hK,
    Distribution.complexPairing_postcompCLM_ofRealCLM]

end LinearMap
