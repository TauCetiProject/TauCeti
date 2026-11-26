/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.LinearEquiv
public import TauCeti.Analysis.Distribution.Restriction
public import TauCeti.Analysis.Distribution.TestFunction.SchwartzKernel
import TauCeti.Analysis.Distribution.Gluing
import TauCeti.Analysis.Distribution.TestFunction.Complexify
import TauCeti.Analysis.Distribution.TestFunction.Frechet
import TauCeti.Analysis.Distribution.TestFunction.TensorDensity
import TauCeti.Analysis.Normed.Module.Complexification
import TauCeti.Topology.MetricSpace.Pseudo.Lemmas

/-!
# The Schwartz kernel theorem on open sets

Let `Ω ⊆ E` and `O ⊆ D` be open sets of finite-dimensional real normed spaces and let `B` be a
complex bilinear map on the complex test functions `𝓓(Ω, ℂ) × 𝓓(O, ℂ)`, with values in a complex
Banach space `F`, which is continuous on each pair of compact sets: for compact sets `K₁ ⊆ Ω` and
`K₂ ⊆ O` there are `C` and `k` with `‖B φ ψ‖ ≤ C N_k(φ) N_k(ψ)` for `φ` supported in `K₁` and `ψ`
supported in `K₂`, where `N_k` is the `C^k` seminorm. Then there is exactly one continuous linear
map `T` on the complex test functions on `Ω × O` with

`T (φ ⊗ ψ) = B φ ψ`,

where `(φ ⊗ ψ)(x, y) = φ x * ψ y` is `TestFunction.tensor`
(`LinearMap.existsUnique_schwartzKernel_testFunction`). This is the Schwartz kernel theorem in the
form of the construction in Hörmander's proof, which first derives the estimate above from the
continuity of the map `ψ ↦ B (·) ψ` from `𝓓(O)` to `𝓓'(Ω)`. For `F = ℂ` the kernel is an actual
distribution `K ∈ 𝓓'(Ω × O, ℂ)`, acting on complex test functions through its complex-linear
extension `Distribution.complexPairing` (`LinearMap.existsUnique_schwartzKernel_distribution`).

These two theorems take the estimate as a hypothesis, which is equivalent to `B` being continuous
in each variable for the topologies of test functions. If `B` is separately continuous, its
restriction to functions supported in `K₁` and `K₂` is a separately continuous bilinear map on two
Fréchet spaces, which has finite order (`LinearMap.exists_bound_supportedIn_of_continuous`,
through the Banach–Steinhaus theorem). Conversely, the estimate makes `B` continuous in each
variable, since a test function `ψ` is supported in the compact set `tsupport ψ`
(`LinearMap.continuous_apply_left_of_bound`). The forms of the theorem for separately continuous
`B` are `LinearMap.existsUnique_schwartzKernel_testFunction_of_continuous` and
`LinearMap.existsUnique_schwartzKernel_distribution_of_continuous`.

A real bilinear map `B` on the real test functions `𝓓(Ω, ℝ) × 𝓓(O, ℝ)` with values in a real
Banach space `G`, under the same estimate, has a unique kernel `T ∈ 𝓓'(Ω × O, G)` with
`T (φ ⊗ ψ) = B φ ψ` (`LinearMap.existsUnique_schwartzKernel_prodSMulCLM`). It is the real part of
the kernel of the complex-bilinear extension of `B` with values in the complexification of `G`
(`LinearMap.complexifyTestFunction`). If `B` is continuous in each variable it satisfies the
estimate (`LinearMap.existsUnique_schwartzKernel_prodSMulCLM_of_continuous`).

## Operators and their kernels

A distribution `K` on an open set `V ⊇ Ω ×ˢ O` defines the operator
`Distribution.kernelOperator hV K : 𝓓(O, ℝ) →ₗ[ℝ] 𝓓'(Ω, F)` by

`⟨kernelOperator hV K ψ, φ⟩ = K (φ ⊗ ψ)`,

where `(φ ⊗ ψ)(x, y) = ψ y • φ x` is `TestFunction.prodSMulCLM ψ hV φ`. It is continuous for the
weak topology of `𝓓'(Ω, F)`: each `ψ ↦ kernelOperator hV K ψ φ` is continuous
(`Distribution.continuous_kernelOperator_apply`), and for `V = Ω ×ˢ O` it determines `K`
(`Distribution.kernelOperator_injective`). The Schwartz kernel theorem says that every such
operator has a kernel: for a real Banach space `G`, a linear map `A : 𝓓(O, ℝ) →ₗ[ℝ] 𝓓'(Ω, G)`
with every `ψ ↦ A ψ φ` continuous is `kernelOperator hV K` for exactly one `K ∈ 𝓓'(Ω × O, G)`
(`LinearMap.existsUnique_kernelOperator_eq`), in particular every continuous linear map
`𝓓(O, ℝ) →L[ℝ] 𝓓'(Ω, G)` (`ContinuousLinearMap.existsUnique_kernelOperator_eq`). For the proof,
the real bilinear map `(φ, ψ) ↦ ⟨A ψ, φ⟩` is continuous in each variable, so
`LinearMap.existsUnique_schwartzKernel_prodSMulCLM_of_continuous` supplies `K`.

In the same way a continuous linear map `T : 𝓓(O, ℂ) → 𝓓'(Ω, ℂ)` on complex test functions has a
unique kernel `K ∈ 𝓓'(Ω × O, ℂ)` with

`K (φ ⊗ ψ) = (T ψ) φ`

(`ContinuousLinearMap.existsUnique_schwartzKernel`), its *Schwartz kernel*
`ContinuousLinearMap.schwartzKernel`. The kernel depends linearly on `T` and determines it. The
kernel of a transpose of `T`, a map `R : 𝓓(Ω, ℂ) → 𝓓'(O, ℂ)` with `(R φ) ψ = (T ψ) φ`, is the
kernel of `T` with its two variables exchanged, and the kernel of a restriction of `T` to smaller
open sets is the restriction of the kernel of `T`.

## Proof

The theorem is first proved for open sets of `ℝ^a × ℝ^b`, where test functions supported in small
boxes are functions on a torus. For general `E` and `D`, linear coordinates `e₁ : E ≃ ℝ^a` and
`e₂ : D ≃ ℝ^b` transport test functions, and with them tensor products and kernels, between the
two settings. The coordinates are only used for continuity, so the theorem is first transported
for separately continuous `B` (`LinearMap.existsUnique_schwartzKernel_testFunction_of_continuous`),
and the estimate makes `B` separately continuous, since a test function `ψ` is supported in the
compact set `tsupport ψ`.

On `ℝ^a × ℝ^b` the kernel is assembled from the kernels on small boxes supplied by
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
  of products `E × D` of finite-dimensional real normed spaces.
* `LinearMap.existsUnique_schwartzKernel_distribution`: its form for complex-valued
  distributions.
* `LinearMap.existsUnique_schwartzKernel_prodSMulCLM`: its form for real test functions and
  distributions with values in a real Banach space.
* `LinearMap.existsUnique_schwartzKernel_testFunction_of_continuous`,
  `LinearMap.existsUnique_schwartzKernel_distribution_of_continuous`,
  `LinearMap.existsUnique_schwartzKernel_prodSMulCLM_of_continuous`: the same for bilinear maps
  continuous in each variable.

* `Distribution.kernelOperator`: the operator `𝓓(O) → 𝓓'(Ω)` with kernel `K`, with
  `Distribution.kernelOperator_apply`, `Distribution.continuous_kernelOperator_apply` and
  `Distribution.kernelOperator_injective`.
* `LinearMap.existsUnique_kernelOperator_eq`, `ContinuousLinearMap.existsUnique_kernelOperator_eq`:
  the Schwartz kernel theorem for weakly continuous and for continuous linear maps
  `𝓓(O, ℝ) → 𝓓'(Ω, G)`, for a real Banach space `G`.
* `LinearMap.exists_kernelOperator_eq_iff`: the operators with a kernel are exactly the weakly
  continuous ones.
* `ContinuousLinearMap.existsUnique_schwartzKernel`: the Schwartz kernel theorem for continuous
  linear maps `𝓓(O, ℂ) → 𝓓'(Ω, ℂ)` on complex test functions.
* `ContinuousLinearMap.schwartzKernel`: the kernel of such a map, characterized by
  `ContinuousLinearMap.complexPairing_schwartzKernel_tensor` and
  `ContinuousLinearMap.eq_schwartzKernel_iff`; it determines the map
  (`ContinuousLinearMap.schwartzKernel_injective`).
* `ContinuousLinearMap.schwartzKernel_eq_transportCLM_of_complexPairing_eq`: the kernel of a
  transpose is obtained by exchanging the two variables.
* `ContinuousLinearMap.schwartzKernel_eq_restrictCLM_of_complexPairing_eq`: the kernel of a
  restriction is the restriction of the kernel.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 5.2.1 (the Schwartz kernel theorem) and its proof.
-/

public section

noncomputable section

open Function Metric Set TopologicalSpace TestFunction
open scoped ContDiff Distributions

namespace LinearMap

section Pi

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
    (hU : IsOpen U) : U ⊆ ⋃ i : SmallBall U, ball i.val.1 (i.val.2 / 2) := fun x hx ↦ by
  obtain ⟨r, hr₀, hr, hrU⟩ :=
    TauCeti.exists_pos_lt_closedBall_subset (hU.mem_nhds hx) one_half_pos
  exact mem_iUnion.2 ⟨⟨(x, r), hr₀, hr, hrU⟩, mem_ball_self (by positivity)⟩

/-- The open ball of half the radius of a small ball in `U` lies in `U`. -/
private theorem ball_smallBall_subset {d : Type*} [Fintype d] {U : Set (d → ℝ)} (i : SmallBall U) :
    ball i.val.1 (i.val.2 / 2) ⊆ U :=
  ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith
      [i.property.1])).trans i.property.2.2)

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
      (ψ : 𝓓(O, ℂ)), tsupport φ ⊆ ball i.val.1 (i.val.2 / 2) → tsupport ψ ⊆ ball j.val.1
          (j.val.2 / 2) →
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
    hS i.val j.val (φs i) (ψs j) (hφs i) (hψs j)
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
/-- The Schwartz kernel theorem on open sets of `ℝ^a × ℝ^b`, under the estimate `hB`, from the
kernels on small boxes. -/
private theorem existsUnique_schwartzKernel_testFunction_pi {V : Opens ((a → ℝ) × (b → ℝ))}
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
    ⟨ball ij.1.val.1 (ij.1.val.2 / 2) ×ˢ ball ij.2.val.1 (ij.2.val.2 / 2),
        isOpen_ball.prod isOpen_ball⟩
  have hUV (ij : SmallBox Ω O) : (U ij : Set ((a → ℝ) × (b → ℝ))) ⊆ Ω ×ˢ O :=
    prod_mono (ball_smallBall_subset ij.1) (ball_smallBall_subset ij.2)
  have hU : ⨆ ij, U ij = V := by
    refine SetLike.coe_injective ?_
    rw [Opens.coe_iSup, hV]
    refine subset_antisymm (iUnion_subset hUV) fun p hp ↦ ?_
    obtain ⟨i, hi⟩ := mem_iUnion.1 (subset_iUnion_ball_smallBall Ω.isOpen hp.1)
    obtain ⟨j, hj⟩ := mem_iUnion.1 (subset_iUnion_ball_smallBall O.isOpen hp.2)
    exact mem_iUnion.2 ⟨(i, j), hi, hj⟩
  choose T hT using fun ij : SmallBox Ω O ↦ exists_isKernelOn_box hB ij.1.property.1
      ij.1.property.2.1 ij.2.property.1
    ij.2.property.2.1 ij.1.property.2.2 ij.2.property.2.2 (U := U ij) rfl
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

end Pi

/-! ### Open sets of finite-dimensional spaces -/

section FiniteDimensional

variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D]
  [NormedSpace ℝ D] {Ω : Opens E} {O : Opens D} [FiniteDimensional ℝ E] [FiniteDimensional ℝ D]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {B : 𝓓(Ω, ℂ) →ₗ[ℂ] 𝓓(O, ℂ) →ₗ[ℂ] F}

variable (B) in
/-- **The Schwartz kernel theorem for separately continuous bilinear maps.** Let `B` be a complex
bilinear map on the complex test functions on open sets `Ω ⊆ E` and `O ⊆ D` of finite-dimensional
real normed spaces, with values in a complex Banach space, which is continuous in each variable.
Then there is a unique continuous linear map `T` on the complex test functions on `V = Ω × O` with
`T (φ ⊗ ψ) = B φ ψ` for all `φ` and `ψ`. -/
theorem existsUnique_schwartzKernel_testFunction_of_continuous
    (h₁ : ∀ ψ, Continuous fun φ ↦ B φ ψ) (h₂ : ∀ φ, Continuous (B φ))
    {V : Opens (E × D)} (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D)) :
    ∃! T : 𝓓(V, ℂ) →L[ℂ] F, ∀ (φ : 𝓓(Ω, ℂ)) (ψ : 𝓓(O, ℂ)),
      T (φ.tensor ψ hV.symm.subset) = B φ ψ := by
  -- Read `B` in linear coordinates `e₁ : E ≃ ℝ^a` and `e₂ : D ≃ ℝ^b`, apply the theorem on open
  -- sets of `ℝ^a × ℝ^b`, and transport its kernel back along `e₁ × e₂`.
  let e₁ := (Module.finBasis ℝ E).equivFunL
  let e₂ := (Module.finBasis ℝ D).equivFunL
  let Ω' : Opens (Fin (Module.finrank ℝ E) → ℝ) :=
    ⟨e₁.symm ⁻¹' Ω, Ω.isOpen.preimage e₁.symm.continuous⟩
  let O' : Opens (Fin (Module.finrank ℝ D) → ℝ) :=
    ⟨e₂.symm ⁻¹' O, O.isOpen.preimage e₂.symm.continuous⟩
  let V' : Opens ((Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ D) → ℝ)) :=
    ⟨e₁.symm.prodCongr e₂.symm ⁻¹' V, V.isOpen.preimage (e₁.symm.prodCongr e₂.symm).continuous⟩
  have hV' : (V' : Set ((Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ D) → ℝ))) =
      (Ω' : Set (Fin (Module.finrank ℝ E) → ℝ)) ×ˢ (O' : Set (Fin (Module.finrank ℝ D) → ℝ)) := by
    ext p
    simp [V', Ω', O', hV]
  have hΩ : MapsTo e₁.symm Ω' Ω := fun _ hx ↦ hx
  have hΩ' : MapsTo e₁ Ω Ω' := fun x hx ↦ by simpa [Ω'] using hx
  have hO : MapsTo e₂.symm O' O := fun _ hy ↦ hy
  have hO' : MapsTo e₂ O O' := fun y hy ↦ by simpa [O'] using hy
  have hV₁ : MapsTo (e₁.prodCongr e₂) V V' := fun p hp ↦ by simpa [V'] using hp
  have hV₂ : MapsTo (e₁.symm.prodCongr e₂.symm) V' V := fun _ hp ↦ hp
  let B' : 𝓓(Ω', ℂ) →ₗ[ℂ] 𝓓(O', ℂ) →ₗ[ℂ] F :=
    B.compl₁₂ (e₁.symm.transportTestFunctionComplex hΩ).toLinearMap
      (e₂.symm.transportTestFunctionComplex hO).toLinearMap
  obtain ⟨T', hT', hT'u⟩ := existsUnique_schwartzKernel_testFunction_pi B'
    (exists_bound_ofSupportedIn_of_continuous B'
      (fun _ ↦ (h₁ _).comp (e₁.symm.transportTestFunctionComplex hΩ).continuous)
      (fun _ ↦ (h₂ _).comp (e₂.symm.transportTestFunctionComplex hO).continuous)) hV'
  refine ⟨T'.comp ((e₁.prodCongr e₂).transportTestFunctionComplex hV₁), fun φ ψ ↦ ?_,
    fun T hT ↦ ?_⟩
  · rw [ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.transportTestFunctionComplex_prodCongr_tensor e₁ e₂ hΩ' hO' hV₁ _
        hV'.symm.subset, hT']
    exact congr_arg₂ (B · ·) (TestFunction.ext fun _ ↦ by simp) (TestFunction.ext fun _ ↦ by simp)
  · -- `T` read in the coordinates is a kernel of `B'`, hence is `T'`.
    have hTT' : T.comp ((e₁.symm.prodCongr e₂.symm).transportTestFunctionComplex hV₂) = T' :=
      hT'u _ fun φ ψ ↦ by
        rw [ContinuousLinearMap.comp_apply,
          ContinuousLinearEquiv.transportTestFunctionComplex_prodCongr_tensor e₁.symm e₂.symm hΩ hO
            hV₂ _ hV.symm.subset, hT]
        simp only [B', compl₁₂_apply, ContinuousLinearMap.coe_coe]
    ext Φ
    rw [← hTT', ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    exact congr_arg T (TestFunction.ext fun _ ↦ by simp)

variable (B) in
/-- **The Schwartz kernel theorem on open sets.** Let `B` be a complex bilinear map on the complex
test functions on open sets `Ω ⊆ E` and `O ⊆ D` of finite-dimensional real normed spaces, with
values in a complex Banach space, such that for all compact sets `K₁ ⊆ Ω` and `K₂ ⊆ O` some `C`
and `k` give `‖B φ ψ‖ ≤ C N_k(φ) N_k(ψ)` for `φ` supported in `K₁` and `ψ` supported in `K₂`.
Then there is a unique continuous linear map `T` on the complex test functions on `V = Ω × O` with
`T (φ ⊗ ψ) = B φ ψ` for all `φ` and `ψ`. -/
theorem existsUnique_schwartzKernel_testFunction
    (hB : ∀ (K₁ : Compacts E) (K₂ : Compacts D) (hK₁ : (K₁ : Set E) ⊆ Ω)
      (hK₂ : (K₂ : Set D) ⊆ O), ∃ (C : ℝ) (k : ℕ), ∀ φ ψ,
        ‖B (ofSupportedIn hK₁ φ) (ofSupportedIn hK₂ ψ)‖ ≤
          C * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₁ k φ *
            ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₂ k ψ)
    {V : Opens (E × D)} (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D)) :
    ∃! T : 𝓓(V, ℂ) →L[ℂ] F, ∀ (φ : 𝓓(Ω, ℂ)) (ψ : 𝓓(O, ℂ)),
      T (φ.tensor ψ hV.symm.subset) = B φ ψ := by
  -- The estimate makes `B` continuous in each variable; for the second variable apply this to the
  -- flipped map.
  refine existsUnique_schwartzKernel_testFunction_of_continuous B
    (continuous_apply_left_of_bound B hB) (fun φ ↦ ?_) hV
  refine continuous_apply_left_of_bound B.flip (fun K₂ K₁ hK₂ hK₁ ↦ ?_) φ
  obtain ⟨C, k, hC⟩ := hB K₁ K₂ hK₁ hK₂
  exact ⟨C, k, fun ψ φ ↦ by simpa only [flip_apply, mul_right_comm C] using hC φ ψ⟩

/-- **The Schwartz kernel theorem for distributions on open sets.** Let `B` be a complex bilinear
form on the complex test functions on open sets `Ω ⊆ E` and `O ⊆ D` such that for all
compact sets `K₁ ⊆ Ω` and `K₂ ⊆ O` some `C` and `k` give `|B φ ψ| ≤ C N_k(φ) N_k(ψ)` for `φ`
supported in `K₁` and `ψ` supported in `K₂`. Then there is a unique complex-valued distribution
`K` on `V = Ω × O` whose complex-linear extension takes the value `B φ ψ` on `φ ⊗ ψ`. -/
theorem existsUnique_schwartzKernel_distribution (B : 𝓓(Ω, ℂ) →ₗ[ℂ] 𝓓(O, ℂ) →ₗ[ℂ] ℂ)
    (hB : ∀ (K₁ : Compacts E) (K₂ : Compacts D) (hK₁ : (K₁ : Set E) ⊆ Ω)
      (hK₂ : (K₂ : Set D) ⊆ O), ∃ (C : ℝ) (k : ℕ), ∀ φ ψ,
        ‖B (ofSupportedIn hK₁ φ) (ofSupportedIn hK₂ ψ)‖ ≤
          C * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₁ k φ *
            ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₂ k ψ)
    {V : Opens (E × D)}
    (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D)) :
    ∃! K : 𝓓'(V, ℂ), ∀ (φ : 𝓓(Ω, ℂ)) (ψ : 𝓓(O, ℂ)),
      K.complexPairing (φ.tensor ψ hV.symm.subset) = B φ ψ := by
  obtain ⟨T, hT, hTuniq⟩ := existsUnique_schwartzKernel_testFunction B hB hV
  -- The restriction of `T` to real test functions, whose complex-linear extension is `T`.
  let K : 𝓓'(V, ℂ) := T.restrictScalars ℝ ∘L postcompCLM (𝕜 := ℝ) Complex.ofRealCLM
  have hK : K.complexPairing = T := by
    ext Φ
    have hKapp (φ : 𝓓(V, ℝ)) : K φ = T (postcompCLM (𝕜 := ℝ) Complex.ofRealCLM φ) := rfl
    rw [Distribution.complexPairing_apply, hKapp, hKapp, ← smul_eq_mul, ← map_smul, ← map_add,
      postcompCLM_re_add_I_smul_im Φ]
  refine ⟨K, fun φ ψ ↦ by rw [hK, hT], fun K' hK' ↦ ?_⟩
  have h := hTuniq K'.complexPairing hK'
  ext φ
  rw [← Distribution.complexPairing_postcompCLM_ofRealCLM, h, ← hK,
    Distribution.complexPairing_postcompCLM_ofRealCLM]

/-- **The Schwartz kernel theorem on open sets, for real test functions.** Let `B` be a real
bilinear map on the real test functions on open sets `Ω ⊆ E` and `O ⊆ D`, with values in a real
Banach space `G`, such that for all compact sets `K₁ ⊆ Ω` and `K₂ ⊆ O` some `C` and `k` give
`‖B φ ψ‖ ≤ C N_k(φ) N_k(ψ)` for `φ` supported in `K₁` and `ψ` supported in `K₂`. Then there is a
unique `G`-valued distribution `T` on `V = Ω × O` with `T (φ ⊗ ψ) = B φ ψ` for all `φ` and `ψ`. -/
theorem existsUnique_schwartzKernel_prodSMulCLM {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] (B : 𝓓(Ω, ℝ) →ₗ[ℝ] 𝓓(O, ℝ) →ₗ[ℝ] G)
    (hB : ∀ (K₁ : Compacts E) (K₂ : Compacts D) (hK₁ : (K₁ : Set E) ⊆ Ω)
      (hK₂ : (K₂ : Set D) ⊆ O), ∃ (C : ℝ) (k : ℕ), ∀ φ ψ,
        ‖B (ofSupportedIn hK₁ φ) (ofSupportedIn hK₂ ψ)‖ ≤
          C * ContDiffMapSupportedIn.supSeminorm ℝ _ ℝ ⊤ K₁ k φ *
            ContDiffMapSupportedIn.supSeminorm ℝ _ ℝ ⊤ K₂ k ψ)
    {V : Opens (E × D)}
    (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D)) :
    ∃! T : 𝓓'(V, G), ∀ (φ : 𝓓(Ω, ℝ)) (ψ : 𝓓(O, ℝ)), T (prodSMulCLM ψ hV.symm.subset φ) = B φ ψ := by
  -- The complex-bilinear extension of `B` with values in the complexification of `G`.
  let BC := complexifyTestFunction (B.compr₂ (TauCeti.Complexification.ofRealLI G).toLinearMap)
  have hBC (K₁ : Compacts E) (K₂ : Compacts D) (hK₁ : (K₁ : Set E) ⊆ Ω)
      (hK₂ : (K₂ : Set D) ⊆ O) : ∃ (C : ℝ) (k : ℕ), ∀ φ ψ,
        ‖BC (ofSupportedIn hK₁ φ) (ofSupportedIn hK₂ ψ)‖ ≤
          C * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₁ k φ *
            ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₂ k ψ := by
    obtain ⟨C, k, hC⟩ := hB K₁ K₂ hK₁ hK₂
    refine ⟨4 * max C 0, k, norm_complexifyTestFunction_ofSupportedIn_le hK₁ hK₂
      (le_max_right C 0) fun φ ψ ↦ ?_⟩
    rw [compr₂_apply, LinearIsometry.coe_toLinearMap, LinearIsometry.norm_map]
    refine (hC φ ψ).trans (mul_le_mul_of_nonneg_right ?_ (apply_nonneg _ _))
    exact mul_le_mul_of_nonneg_right (le_max_left C 0) (apply_nonneg _ _)
  obtain ⟨T, hT, -⟩ := existsUnique_schwartzKernel_testFunction BC hBC hV
  -- The real part of `T` on real test functions.
  let S : 𝓓'(V, G) := TauCeti.Complexification.reCLM G ∘L T.restrictScalars ℝ ∘L
    postcompCLM (𝕜 := ℝ) Complex.ofRealCLM
  have hS (φ : 𝓓(Ω, ℝ)) (ψ : 𝓓(O, ℝ)) : S (prodSMulCLM ψ hV.symm.subset φ) = B φ ψ := by
    have h : postcompCLM (𝕜 := ℝ) Complex.ofRealCLM (prodSMulCLM ψ hV.symm.subset φ) =
        (postcompCLM (𝕜 := ℝ) Complex.ofRealCLM φ).tensor
          (postcompCLM (𝕜 := ℝ) Complex.ofRealCLM ψ) hV.symm.subset := by
      ext p
      simp [prodSMulCLM_apply, tensor_apply, mul_comm]
    have hSapp (f : 𝓓(V, ℝ)) :
        S f = TauCeti.Complexification.reCLM G (T (postcompCLM (𝕜 := ℝ) Complex.ofRealCLM f)) :=
      rfl
    rw [hSapp, h, hT]
    simp [BC]
  -- Uniqueness is the density of tensor products.
  exact ⟨S, hS, fun S' hS' ↦ ext_prodSMulCLM hV fun ψ φ ↦ by rw [hS', hS]⟩

/-! ### Separately continuous bilinear maps -/

/-- **The Schwartz kernel theorem for separately continuous bilinear forms.** A complex bilinear
form on the complex test functions on open sets `Ω ⊆ E` and `O ⊆ D` which is continuous in each
variable is given by a unique complex-valued distribution `K` on `V = Ω × O`: the complex-linear
extension of `K` takes the value `B φ ψ` on `φ ⊗ ψ`. -/
theorem existsUnique_schwartzKernel_distribution_of_continuous
    (B : 𝓓(Ω, ℂ) →ₗ[ℂ] 𝓓(O, ℂ) →ₗ[ℂ] ℂ) (h₁ : ∀ ψ, Continuous fun φ ↦ B φ ψ)
    (h₂ : ∀ φ, Continuous (B φ)) {V : Opens (E × D)}
    (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D)) :
    ∃! K : 𝓓'(V, ℂ), ∀ (φ : 𝓓(Ω, ℂ)) (ψ : 𝓓(O, ℂ)),
      K.complexPairing (φ.tensor ψ hV.symm.subset) = B φ ψ :=
  existsUnique_schwartzKernel_distribution B (exists_bound_ofSupportedIn_of_continuous B h₁ h₂) hV

/-- **The Schwartz kernel theorem for separately continuous bilinear maps, for real test
functions.** A real bilinear map on the real test functions on open sets `Ω ⊆ E` and `O ⊆ D`,
with values in a real Banach space `G`, which is continuous in each variable is given by a unique
`G`-valued distribution `T` on `V = Ω × O` with `T (φ ⊗ ψ) = B φ ψ` for all `φ` and `ψ`. -/
theorem existsUnique_schwartzKernel_prodSMulCLM_of_continuous {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] (B : 𝓓(Ω, ℝ) →ₗ[ℝ] 𝓓(O, ℝ) →ₗ[ℝ] G)
    (h₁ : ∀ ψ, Continuous fun φ ↦ B φ ψ) (h₂ : ∀ φ, Continuous (B φ))
    {V : Opens (E × D)}
    (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D)) :
    ∃! T : 𝓓'(V, G), ∀ (φ : 𝓓(Ω, ℝ)) (ψ : 𝓓(O, ℝ)), T (prodSMulCLM ψ hV.symm.subset φ) = B φ ψ :=
  existsUnique_schwartzKernel_prodSMulCLM B (exists_bound_ofSupportedIn_of_continuous B h₁ h₂) hV

end FiniteDimensional

end LinearMap

/-! ### Operators and their kernels -/

namespace Distribution

variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D]
  [NormedSpace ℝ D] {Ω : Opens E} {O : Opens D} {V : Opens (E × D)}
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F]

/-- The distribution `φ ↦ K (φ ⊗ ψ)` on `Ω`. -/
private def compProdSMul (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V) (K : 𝓓'(V, F)) (ψ : 𝓓(O, ℝ)) :
    𝓓'(Ω, F) :=
  K.comp (prodSMulCLM ψ hV)

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
private theorem compProdSMul_apply (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V) (K : 𝓓'(V, F))
    (ψ : 𝓓(O, ℝ)) (φ : 𝓓(Ω, ℝ)) : compProdSMul hV K ψ φ = K (prodSMulCLM ψ hV φ) :=
  (rfl)

/-- The **operator with Schwartz kernel** `K`: a distribution `K` on an open set `V ⊇ Ω ×ˢ O`
defines the linear map `𝓓(O, ℝ) → 𝓓'(Ω, F)` sending `ψ` to the distribution `φ ↦ K (φ ⊗ ψ)`,
where `(φ ⊗ ψ)(x, y) = ψ y • φ x`. It is linear in `K`. -/
def kernelOperator (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V) :
    𝓓'(V, F) →ₗ[ℝ] 𝓓(O, ℝ) →ₗ[ℝ] 𝓓'(Ω, F) :=
  LinearMap.mk₂ ℝ (compProdSMul hV)
    (fun K K' _ ↦ ContinuousLinearMap.add_comp K K' _)
    (fun c K _ ↦ ContinuousLinearMap.smul_comp c K _)
    (fun K ψ ψ' ↦ by ext φ; simp [compProdSMul_apply, prodSMulCLM_add])
    (fun c K ψ ↦ by ext φ; simp [compProdSMul_apply, prodSMulCLM_smul])

/-- The operator with kernel `K` pairs `ψ` with `φ` to `K (φ ⊗ ψ)`. -/
@[simp]
theorem kernelOperator_apply (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V) (K : 𝓓'(V, F))
    (ψ : 𝓓(O, ℝ)) (φ : 𝓓(Ω, ℝ)) : kernelOperator hV K ψ φ = K (prodSMulCLM ψ hV φ) :=
  (rfl)

/-- The operator with kernel `K` is continuous for the weak topology of distributions:
`ψ ↦ ⟨kernelOperator hV K ψ, φ⟩` is continuous for every test function `φ`. -/
theorem continuous_kernelOperator_apply (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V) (K : 𝓓'(V, F))
    (φ : 𝓓(Ω, ℝ)) : Continuous fun ψ ↦ kernelOperator hV K ψ φ := by
  simp only [kernelOperator_apply]
  exact K.continuous.comp (continuous_prodSMulCLM_apply hV φ)

/-- A distribution on `Ω ×ˢ O` is determined by its operator, since tensor products of test
functions span a dense subspace (`TestFunction.ext_prodSMulCLM`). -/
theorem kernelOperator_injective [T2Space F]
    (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D)) :
    Function.Injective (kernelOperator (F := F) hV.symm.subset) := fun K K' h ↦
  ext_prodSMulCLM hV fun ψ φ ↦ by
    simpa using DFunLike.congr_fun (DFunLike.congr_fun h ψ) φ

end Distribution

namespace LinearMap

open Distribution

variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] {Ω : Opens E} {O : Opens D}
  {V : Opens (E × D)}
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- **The Schwartz kernel theorem.** Let `Ω ⊆ E` and `O ⊆ D` be open sets and let
`A : 𝓓(O, ℝ) → 𝓓'(Ω, G)` be a linear map into the distributions with values in a real Banach space
`G` which is continuous for the weak topology of distributions: `ψ ↦ ⟨A ψ, φ⟩` is continuous for
every test function `φ` on `Ω`. Then there is a unique `G`-valued distribution `K` on
`V = Ω × O`, the Schwartz kernel of `A`, with `⟨A ψ, φ⟩ = K (φ ⊗ ψ)`, that is,
`A = kernelOperator hV K`. -/
theorem existsUnique_kernelOperator_eq (A : 𝓓(O, ℝ) →ₗ[ℝ] 𝓓'(Ω, G))
    (hA : ∀ φ, Continuous fun ψ ↦ A ψ φ)
    (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D)) :
    ∃! K : 𝓓'(V, G), kernelOperator hV.symm.subset K = A := by
  -- The bilinear map `(φ, ψ) ↦ ⟨A ψ, φ⟩` is continuous in each variable.
  let B : 𝓓(Ω, ℝ) →ₗ[ℝ] 𝓓(O, ℝ) →ₗ[ℝ] G :=
    LinearMap.mk₂ ℝ (fun φ ψ ↦ A ψ φ) (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)
      (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)
  obtain ⟨K, hK, -⟩ := existsUnique_schwartzKernel_prodSMulCLM_of_continuous B
    (fun ψ ↦ (A ψ).continuous) hA hV
  have hKA : kernelOperator hV.symm.subset K = A := by
    ext ψ φ
    rw [kernelOperator_apply, hK, LinearMap.mk₂_apply]
  exact ⟨K, hKA, fun K' hK' ↦ kernelOperator_injective hV (hK'.trans hKA.symm)⟩

/-- **The operators with a Schwartz kernel** are exactly the linear maps `𝓓(O, ℝ) → 𝓓'(Ω, G)`
that are continuous for the weak topology of distributions. -/
theorem exists_kernelOperator_eq_iff (A : 𝓓(O, ℝ) →ₗ[ℝ] 𝓓'(Ω, G))
    (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D)) :
    (∃ K : 𝓓'(V, G), kernelOperator hV.symm.subset K = A) ↔
      ∀ φ, Continuous fun ψ ↦ A ψ φ := by
  refine ⟨?_, fun hA ↦ (existsUnique_kernelOperator_eq A hA hV).exists⟩
  rintro ⟨K, rfl⟩ φ
  exact continuous_kernelOperator_apply _ K φ

end LinearMap

namespace ContinuousLinearMap

open Distribution

variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] {Ω : Opens E} {O : Opens D}
  {V : Opens (E × D)}

/-- **The Schwartz kernel theorem for continuous operators.** Every continuous linear map
`A : 𝓓(O, ℝ) → 𝓓'(Ω, G)` into the distributions with values in a real Banach space `G`, for the
topology of compact convergence on distributions, is the operator `kernelOperator hV K` of a unique
`G`-valued distribution `K` on `V = Ω × O`. -/
theorem existsUnique_kernelOperator_eq {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (A : 𝓓(O, ℝ) →L[ℝ] 𝓓'(Ω, G))
    (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D)) :
    ∃! K : 𝓓'(V, G), kernelOperator hV.symm.subset K = A :=
  LinearMap.existsUnique_kernelOperator_eq _
    (fun φ ↦ (continuous_eval_const φ).comp A.continuous) hV

/-! ### The Schwartz kernel of a continuous linear map on complex test functions -/

section SchwartzKernel

variable (T S : 𝓓(O, ℂ) →L[ℂ] 𝓓'(Ω, ℂ))
  (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D))


/-- The bilinear form `(φ, ψ) ↦ (T ψ) φ` of a continuous linear map `T` from test functions to
distributions, with the distributions `T ψ` acting on complex test functions through their
complex-linear extensions. It is continuous in each variable. -/
private def pairing : 𝓓(Ω, ℂ) →ₗ[ℂ] 𝓓(O, ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun φ ψ ↦ (T ψ).complexPairing φ) (fun _ _ _ ↦ map_add _ _ _)
    (fun _ _ _ ↦ map_smul _ _ _) (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] in
private theorem pairing_apply (φ : 𝓓(Ω, ℂ)) (ψ : 𝓓(O, ℂ)) :
    pairing T φ ψ = (T ψ).complexPairing φ :=
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] in
private theorem continuous_pairing_left (ψ : 𝓓(O, ℂ)) : Continuous fun φ ↦ pairing T φ ψ := by
  simpa only [pairing_apply] using (T ψ).complexPairing.continuous

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] in
private theorem continuous_pairing_right (φ : 𝓓(Ω, ℂ)) : Continuous (pairing T φ) :=
  ((Distribution.continuous_complexPairing_apply φ).comp T.continuous).congr fun ψ ↦
    (pairing_apply T φ ψ).symm

/-- **The Schwartz kernel theorem.** A continuous linear map `T` from the complex test functions on
an open set `O ⊆ D` to the complex-valued distributions on an open set `Ω ⊆ E` has a unique
*kernel*: a complex-valued distribution `K` on `V = Ω × O` with `K (φ ⊗ ψ) = (T ψ) φ` for all
complex test functions `φ` on `Ω` and `ψ` on `O`, where both distributions act on complex test
functions through their complex-linear extensions. -/
theorem existsUnique_schwartzKernel :
    ∃! K : 𝓓'(V, ℂ), ∀ (φ : 𝓓(Ω, ℂ)) (ψ : 𝓓(O, ℂ)),
      K.complexPairing (φ.tensor ψ hV.symm.subset) = (T ψ).complexPairing φ := by
  simpa only [pairing_apply] using
    LinearMap.existsUnique_schwartzKernel_distribution_of_continuous (pairing T)
      (continuous_pairing_left T) (continuous_pairing_right T) hV

/-- The **Schwartz kernel** of a continuous linear map `T` from test functions on `O` to
distributions on `Ω`: the unique distribution on `V = Ω × O` taking the value `(T ψ) φ` on
`φ ⊗ ψ` (`ContinuousLinearMap.complexPairing_schwartzKernel_tensor`). -/
def schwartzKernel : 𝓓'(V, ℂ) :=
  (existsUnique_schwartzKernel T hV).exists.choose

/-- The defining property of the Schwartz kernel: `K (φ ⊗ ψ) = (T ψ) φ`. -/
@[simp]
theorem complexPairing_schwartzKernel_tensor (φ : 𝓓(Ω, ℂ)) (ψ : 𝓓(O, ℂ)) :
    (T.schwartzKernel hV).complexPairing (φ.tensor ψ hV.symm.subset) = (T ψ).complexPairing φ :=
  (existsUnique_schwartzKernel T hV).exists.choose_spec φ ψ

/-- A distribution on `Ω × O` is the Schwartz kernel of `T` exactly when it takes the value
`(T ψ) φ` on every `φ ⊗ ψ`. -/
theorem eq_schwartzKernel_iff {K : 𝓓'(V, ℂ)} :
    K = T.schwartzKernel hV ↔ ∀ (φ : 𝓓(Ω, ℂ)) (ψ : 𝓓(O, ℂ)),
      K.complexPairing (φ.tensor ψ hV.symm.subset) = (T ψ).complexPairing φ :=
  ⟨fun h ↦ h ▸ complexPairing_schwartzKernel_tensor T hV, fun h ↦
    (existsUnique_schwartzKernel T hV).unique h (complexPairing_schwartzKernel_tensor T hV)⟩

/-- The Schwartz kernel recovers `T`: for real test functions `φ`, the value `(T ψ) φ` is the
kernel paired with `φ ⊗ ψ`. -/
theorem apply_apply_eq_complexPairing_schwartzKernel (φ : 𝓓(Ω, ℝ)) (ψ : 𝓓(O, ℂ)) :
    T ψ φ = (T.schwartzKernel hV).complexPairing
      ((postcompCLM (𝕜 := ℝ) Complex.ofRealCLM φ).tensor ψ hV.symm.subset) := by
  rw [complexPairing_schwartzKernel_tensor, Distribution.complexPairing_postcompCLM_ofRealCLM]

/-- The Schwartz kernel of a sum is the sum of the Schwartz kernels. -/
@[simp]
theorem schwartzKernel_add :
    (T + S).schwartzKernel hV = T.schwartzKernel hV + S.schwartzKernel hV :=
  ((eq_schwartzKernel_iff _ hV).2 fun φ ψ ↦ by simp).symm

/-- The Schwartz kernel of `c • T` is `c` times the Schwartz kernel of `T`. -/
@[simp]
theorem schwartzKernel_smul (c : ℂ) : (c • T).schwartzKernel hV = c • T.schwartzKernel hV :=
  ((eq_schwartzKernel_iff _ hV).2 fun φ ψ ↦ by simp).symm

/-- The Schwartz kernel of the zero map is zero. -/
@[simp]
theorem schwartzKernel_zero : (0 : 𝓓(O, ℂ) →L[ℂ] 𝓓'(Ω, ℂ)).schwartzKernel hV = 0 :=
  ((eq_schwartzKernel_iff _ hV).2 fun φ ψ ↦ by simp).symm

/-- A continuous linear map from test functions to distributions is determined by its Schwartz
kernel. -/
theorem schwartzKernel_injective :
    Function.Injective fun T : 𝓓(O, ℂ) →L[ℂ] 𝓓'(Ω, ℂ) ↦ T.schwartzKernel hV := by
  intro T S h
  ext ψ φ
  simp only at h
  rw [apply_apply_eq_complexPairing_schwartzKernel _ hV, h,
    ← apply_apply_eq_complexPairing_schwartzKernel _ hV]

/-- Two continuous linear maps from test functions to distributions have the same Schwartz kernel
exactly when they are equal. -/
@[simp]
theorem schwartzKernel_inj : T.schwartzKernel hV = S.schwartzKernel hV ↔ T = S :=
  (schwartzKernel_injective hV).eq_iff

/-- **Transposition swaps the variables of the kernel.** If `R` is a transpose of `T`, that is
`(R φ) ψ = (T ψ) φ` for all complex test functions `φ` on `Ω` and `ψ` on `O`, then the kernel of
`R` on `O × Ω` is the kernel of `T` with its two variables exchanged: its transport along
`(y, x) ↦ (x, y)`. -/
theorem schwartzKernel_eq_transportCLM_of_complexPairing_eq {V' : Opens (D × E)}
    (hV' : (V' : Set (D × E)) = (O : Set D) ×ˢ (Ω : Set E))
    (R : 𝓓(Ω, ℂ) →L[ℂ] 𝓓'(O, ℂ))
    (hRT : ∀ φ ψ, (R φ).complexPairing ψ = (T ψ).complexPairing φ) :
    R.schwartzKernel hV' = Distribution.transportCLM (ContinuousLinearEquiv.prodComm ℝ _ _)
      (by rw [hV, hV']; exact fun p hp ↦ ⟨hp.2, hp.1⟩) (T.schwartzKernel hV) := by
  refine ((eq_schwartzKernel_iff R hV').2 fun ψ φ ↦ ?_).symm
  rw [Distribution.complexPairing_transportCLM, hRT, ← complexPairing_schwartzKernel_tensor T hV]
  congr 1
  ext p
  simp [mul_comm]

/-- **Restriction of the kernel.** Let `Ω' ⊆ Ω` and `O' ⊆ O` be open and let `R` be a restriction
of `T` to them: `(R ψ) φ = (T ψ) φ` for complex test functions `φ` on `Ω'` and `ψ` on `O'`,
extended by zero. Then the kernel of `R` on `Ω' × O'` is the restriction of the kernel of `T`. -/
theorem schwartzKernel_eq_restrictCLM_of_complexPairing_eq {Ω' : Opens E}
    {O' : Opens D} (hΩ : Ω' ≤ Ω) (hO : O' ≤ O) {V' : Opens (E × D)}
    (hV' : (V' : Set (E × D)) = (Ω' : Set E) ×ˢ (O' : Set D))
    (R : 𝓓(O', ℂ) →L[ℂ] 𝓓'(Ω', ℂ))
    (hRT : ∀ φ ψ, (R ψ).complexPairing φ = (T (monoCLM ℂ ψ)).complexPairing (monoCLM ℂ φ)) :
    R.schwartzKernel hV' = Distribution.restrictCLM (T.schwartzKernel hV) := by
  have hVV' : V' ≤ V := by
    rw [← SetLike.coe_subset_coe, hV, hV']
    exact prod_mono hΩ hO
  refine ((eq_schwartzKernel_iff R hV').2 fun φ ψ ↦ ?_).symm
  rw [Distribution.complexPairing_restrictCLM, hRT, ← complexPairing_schwartzKernel_tensor T hV]
  congr 1
  ext p
  simp [hΩ, hO, hVV']

end SchwartzKernel

end ContinuousLinearMap
