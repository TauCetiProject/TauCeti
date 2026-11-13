/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import Mathlib.Analysis.Distribution.Distribution
public import TauCeti.Analysis.Distribution.TestFunction.Prod
import TauCeti.Analysis.Distribution.Gluing
import TauCeti.Analysis.Distribution.TestFunction.Basic
import TauCeti.Analysis.Distribution.TestFunction.Complexify
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.TestFunction.SchwartzKernel
import TauCeti.Analysis.Distribution.TestFunction.TensorDensity
import TauCeti.Analysis.Fourier.Torus.Periodization
import TauCeti.Analysis.Normed.Module.Complexification

/-!
# The Schwartz kernel theorem

This file proves the Schwartz kernel theorem on open subsets of `ℝ^a × ℝ^b`: a continuous bilinear
map `B` on real test functions on open sets `Ω ⊆ ℝ^a` and `O ⊆ ℝ^b`, with values in a real Banach
space, has a unique distributional kernel, a distribution `T` on `Ω ×ˢ O` with `T (φ ⊗ ψ) = B φ ψ`
(`LinearMap.existsUnique_schwartzKernel_distribution`). Kernels are how linear operators between
spaces of functions on manifolds are described, for instance the pseudodifferential operators,
whose kernels are smooth away from the diagonal.

Let `B` be a bilinear map on `𝓓(Ω, ℝ) × 𝓓(O, ℝ)` with values in a real Banach space `F`, bounded
on functions supported in compact sets `K₁ ⊆ Ω` and `K₂ ⊆ O` by a product of `C^k` seminorms;
this is the form continuity takes on each pair `𝓓_{K₁} × 𝓓_{K₂}`. Cover `Ω` and `O` by open balls
`ball c r` with `r < 1/4` whose closed balls of radius `2 r` lie in `Ω`, respectively `O`. On a box
`ball c r ×ˢ ball c' r'` the kernel on compact sets `LinearMap.exists_schwartzKernel_supportedIn`
applies to the complex-bilinear extension
`(φ, ψ) ↦ B (Re φ) (Re ψ) - B (Im φ) (Im ψ) + i (B (Re φ) (Im ψ) + B (Im φ) (Re ψ))`
(`LinearMap.complexifySupportedIn`) of `B`, restricted to the closed balls of radius `2 r` and
`2 r'` and viewed with values in the complexification `TauCeti.Complexification F`. Its real part
is a distribution on the box which agrees with `B` on tensor products. Two of these local kernels
agree on the intersection of their boxes, which is again a box, because tensor products of test
functions span a dense subspace (`TestFunction.ext_prodSMulCLM`). They therefore glue to a
distribution on `Ω ×ˢ O` (`Distribution.existsUnique_gluing`). It agrees with `B` on tensor
products of test functions supported in balls of the cover, and hence on all tensor products,
because an additive map on test functions which vanishes locally vanishes
(`AddMonoidHom.eq_zero_of_locally_vanishing`). Uniqueness is again the density of tensor products.

## Main results

* `LinearMap.existsUnique_schwartzKernel_distribution`: **the Schwartz kernel theorem**, existence
  and uniqueness of the distributional kernel on `Ω ×ˢ O` of a bilinear map on test functions on
  open sets `Ω ⊆ ℝ^a` and `O ⊆ ℝ^b`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 5.2.1 (the Schwartz kernel theorem) and Theorem 2.2.4 (gluing of
  distributions).
-/

public section

noncomputable section

open Function Set TopologicalSpace
open scoped ContDiff Distributions

namespace LinearMap

open Complex ContDiffMapSupportedIn TestFunction Metric

section SmallBall

variable {d : Type*} [Fintype d] {Ω : Opens (d → ℝ)}

/-- Centres `c` and radii `r` of the balls covering an open set `Ω` on which the kernel theorem for
compact sets applies: `r < 1/4` and the closed ball of radius `2 r` lies in `Ω`, so that this
closed ball meets none of its nonzero integer translates. -/
private def SmallBall (Ω : Opens (d → ℝ)) : Type _ :=
  {p : (d → ℝ) × ℝ // 0 < p.2 ∧ p.2 < 1 / 4 ∧ closedBall p.1 (2 * p.2) ⊆ Ω}

namespace SmallBall

/-- The closed ball of radius `r`. -/
private def inner (i : SmallBall Ω) : Compacts (d → ℝ) :=
  ⟨closedBall i.1.1 i.1.2, isCompact_closedBall _ _⟩

/-- The closed ball of radius `2 r`. -/
private def outer (i : SmallBall Ω) : Compacts (d → ℝ) :=
  ⟨closedBall i.1.1 (2 * i.1.2), isCompact_closedBall _ _⟩

/-- The open ball of radius `r`. -/
private def ball (i : SmallBall Ω) : Opens (d → ℝ) := ⟨Metric.ball i.1.1 i.1.2, isOpen_ball⟩

private theorem ball_subset_inner (i : SmallBall Ω) : (i.ball : Set (d → ℝ)) ⊆ i.inner :=
  ball_subset_closedBall

private theorem inner_subset_interior_outer (i : SmallBall Ω) :
    (i.inner : Set (d → ℝ)) ⊆ interior i.outer :=
  (closedBall_subset_ball (by linarith [i.2.1])).trans ball_subset_interior_closedBall

private theorem inner_subset_outer (i : SmallBall Ω) : (i.inner : Set (d → ℝ)) ⊆ i.outer :=
  i.inner_subset_interior_outer.trans interior_subset

private theorem outer_subset (i : SmallBall Ω) : (i.outer : Set (d → ℝ)) ⊆ Ω := i.2.2.2

private theorem ball_le (i : SmallBall Ω) : i.ball ≤ Ω :=
  i.ball_subset_inner.trans (i.inner_subset_outer.trans i.outer_subset)

private theorem eq_zero_of_add_mem_outer (i : SmallBall Ω) {x : d → ℝ} (hx : x ∈ i.outer)
    {ℓ : d → ℤ} (hxℓ : x + (fun k ↦ (ℓ k : ℝ)) ∈ i.outer) : ℓ = 0 :=
  UnitAddTorus.eq_zero_of_add_mem_of_diam_lt_one isBounded_closedBall
    ((diam_closedBall (by linarith [i.2.1])).trans_lt (by linarith [i.2.2.1])) hx hxℓ

private theorem exists_mem_ball {x : d → ℝ} (hx : x ∈ Ω) : ∃ i : SmallBall Ω, x ∈ i.ball := by
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen x hx
  have hr : 0 < min (ε / 4) (1 / 8) := by positivity
  refine ⟨⟨(x, min (ε / 4) (1 / 8)), hr, by linarith [min_le_right (ε / 4) (1 / 8)],
    (closedBall_subset_ball ?_).trans hεΩ⟩, mem_ball_self hr⟩
  linarith [min_le_left (ε / 4) (1 / 8)]

end SmallBall

end SmallBall

section Kernel

variable {a b : Type*} [Fintype a] [Fintype b]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {Ω : Opens (a → ℝ)} {O : Opens (b → ℝ)} (B : 𝓓(Ω, ℝ) →ₗ[ℝ] 𝓓(O, ℝ) →ₗ[ℝ] F)

/-- `B` on real functions supported in the outer closed balls of `i` and `j`. -/
private def restrictOuter (i : SmallBall Ω) (j : SmallBall O) :
    𝓓_{i.outer}(a → ℝ, ℝ) →ₗ[ℝ] 𝓓_{j.outer}(b → ℝ, ℝ) →ₗ[ℝ] F :=
  B.compl₁₂ (ofSupportedInCLM ℝ i.outer_subset).toLinearMap
    (ofSupportedInCLM ℝ j.outer_subset).toLinearMap

/-- The open box `ball i ×ˢ ball j`. -/
private def box (i : SmallBall Ω) (j : SmallBall O) : Opens ((a → ℝ) × (b → ℝ)) :=
  ⟨i.ball ×ˢ j.ball, i.ball.isOpen.prod j.ball.isOpen⟩

private theorem coe_box (i : SmallBall Ω) (j : SmallBall O) :
    (box i j : Set ((a → ℝ) × (b → ℝ))) = (i.ball : Set (a → ℝ)) ×ˢ (j.ball : Set (b → ℝ)) :=
  (rfl)

private theorem box_subset (i : SmallBall Ω) (j : SmallBall O) :
    (box i j : Set ((a → ℝ) × (b → ℝ))) ⊆ (i.inner ×ˢ j.inner : Compacts _) :=
  prod_mono i.ball_subset_inner j.ball_subset_inner

variable {B}

/-- The kernel of `B` on a box: a distribution on `ball i ×ˢ ball j` which takes the value
`B φ ψ` on every test function `(x, y) ↦ ψ y • φ x` with `φ` supported in `ball i` and `ψ` in
`ball j`. It is the restriction to real test functions of the kernel on compact sets
`exists_schwartzKernel_supportedIn` of the complex-bilinear extension of `B`. -/
private theorem exists_kernel_box
    (hB : ∀ (K₁ : Compacts (a → ℝ)) (K₂ : Compacts (b → ℝ)) (hK₁ : (K₁ : Set (a → ℝ)) ⊆ Ω)
      (hK₂ : (K₂ : Set (b → ℝ)) ⊆ O), ∃ (C : ℝ) (k : ℕ),
        ∀ (φ : 𝓓_{K₁}(a → ℝ, ℝ)) (ψ : 𝓓_{K₂}(b → ℝ, ℝ)),
          ‖B (ofSupportedIn hK₁ φ) (ofSupportedIn hK₂ ψ)‖ ≤
            C * ContDiffMapSupportedIn.supSeminorm ℝ _ ℝ ⊤ K₁ k φ *
              ContDiffMapSupportedIn.supSeminorm ℝ _ ℝ ⊤ K₂ k ψ)
    (i : SmallBall Ω) (j : SmallBall O) :
    ∃ S : 𝓓(box i j, ℝ) →L[ℝ] F, ∀ {Ω' : Opens (a → ℝ)} {O' : Opens (b → ℝ)},
      Ω' ≤ i.ball → O' ≤ j.ball → ∀ (φ : 𝓓(Ω', ℝ)) (ψ : 𝓓(O', ℝ)) (f : 𝓓(box i j, ℝ)),
        (⇑f = fun p ↦ ψ p.2 • φ p.1) → S f = B (monoCLM ℝ φ) (monoCLM ℝ ψ) := by
  obtain ⟨C, k, hCk⟩ := hB i.outer j.outer i.outer_subset j.outer_subset
  -- `B` with values in the complexification of `F`, where it has a complex-bilinear extension.
  set Bc := (restrictOuter B i j).compr₂ (TauCeti.Complexification.ofRealLI F).toLinearMap
  have hbound : ∃ (C : ℝ) (k : ℕ), ∀ φ ψ, ‖complexifySupportedIn Bc φ ψ‖ ≤
      C * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ i.outer k φ *
        ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ j.outer k ψ :=
    ⟨4 * max C 0, k, norm_complexifySupportedIn_le (le_max_right _ _) fun φ ψ ↦
      ((TauCeti.Complexification.ofRealLI F).norm_map _).le.trans
        ((hCk φ ψ).trans (by gcongr; exact le_max_left _ _))⟩
  obtain ⟨T, hT, -⟩ := exists_schwartzKernel_supportedIn _ hbound
    (fun _ hx _ ↦ i.eq_zero_of_add_mem_outer hx) (fun _ hy _ ↦ j.eq_zero_of_add_mem_outer hy)
    i.inner_subset_interior_outer j.inner_subset_interior_outer
  refine ⟨TauCeti.Complexification.reCLM F ∘L T.restrictScalars ℝ ∘L
    ContDiffMapSupportedIn.postcompCLM (𝕜 := ℝ) ofRealCLM ∘L toSupportedInCLM ℝ (box_subset i j),
    fun {Ω' O'} hΩ' hO' φ ψ f hf ↦ ?_⟩
  have hφ : (Ω' : Set (a → ℝ)) ⊆ i.inner :=
    (SetLike.coe_subset_coe.2 hΩ').trans i.ball_subset_inner
  have hψ : (O' : Set (b → ℝ)) ⊆ j.inner :=
    (SetLike.coe_subset_coe.2 hO').trans j.ball_subset_inner
  -- Read on the compact boxes, `f` is the tensor product of `φ` and `ψ`.
  have htensor : ContDiffMapSupportedIn.postcompCLM (𝕜 := ℝ) ofRealCLM
      (toSupportedInCLM ℝ (box_subset i j) f) =
      (ContDiffMapSupportedIn.postcompCLM (𝕜 := ℝ) ofRealCLM (toSupportedInCLM ℝ hφ φ)).tensor
        (ContDiffMapSupportedIn.postcompCLM (𝕜 := ℝ) ofRealCLM (toSupportedInCLM ℝ hψ ψ)) := by
    ext p
    simp [hf, mul_comm]
  have hmono₁ : (ContDiffMapSupportedIn.monoCLM ℂ
      (ContDiffMapSupportedIn.postcompCLM (𝕜 := ℝ) ofRealCLM (toSupportedInCLM ℝ hφ φ)) :
        𝓓_{i.outer}(a → ℝ, ℂ)) =
      postcompCLM (𝕜 := ℝ) ofRealCLM (toSupportedInCLM ℝ (hφ.trans i.inner_subset_outer) φ) := by
    ext x
    simp [SetLike.coe_subset_coe.1 i.inner_subset_outer]
  have hmono₂ : (ContDiffMapSupportedIn.monoCLM ℂ
      (ContDiffMapSupportedIn.postcompCLM (𝕜 := ℝ) ofRealCLM (toSupportedInCLM ℝ hψ ψ)) :
        𝓓_{j.outer}(b → ℝ, ℂ)) =
      postcompCLM (𝕜 := ℝ) ofRealCLM (toSupportedInCLM ℝ (hψ.trans j.inner_subset_outer) ψ) := by
    ext x
    simp [SetLike.coe_subset_coe.1 j.inner_subset_outer]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', htensor, hT, hmono₁, hmono₂,
    complexifySupportedIn_postcompCLM_ofRealCLM, Bc, compr₂_apply, LinearIsometry.coe_toLinearMap,
    TauCeti.Complexification.ofRealLI_apply, TauCeti.Complexification.reCLM_apply,
    TauCeti.Complexification.ofReal_re, restrictOuter, compl₁₂_apply,
    ContinuousLinearMap.coe_coe, coe_ofSupportedInCLM, ofSupportedIn_toSupportedInCLM]

/-- The boxes `ball i ×ˢ ball j` cover `Ω ×ˢ O`. -/
private theorem iSup_box {V : Opens ((a → ℝ) × (b → ℝ))}
    (hV : (V : Set ((a → ℝ) × (b → ℝ))) = (Ω : Set (a → ℝ)) ×ˢ (O : Set (b → ℝ))) :
    ⨆ ij : SmallBall Ω × SmallBall O, box ij.1 ij.2 = V := by
  refine le_antisymm (iSup_le fun ij z hz ↦ ?_) fun z hz ↦ ?_
  · rw [← SetLike.mem_coe, hV]
    exact ⟨ij.1.ball_le hz.1, ij.2.ball_le hz.2⟩
  · rw [← SetLike.mem_coe, hV] at hz
    obtain ⟨i, hi⟩ := SmallBall.exists_mem_ball hz.1
    obtain ⟨j, hj⟩ := SmallBall.exists_mem_ball hz.2
    exact Opens.mem_iSup.2 ⟨(i, j), hi, hj⟩

omit [CompleteSpace F] in
/-- A continuous linear map on test functions on `Ω ×ˢ O` which agrees with `B` on the tensor
products of test functions supported in balls of the covers agrees with `B` on all tensor
products: localize first in `φ` and then in `ψ`. -/
private theorem prodSMulCLM_eq_of_forall_tsupport_subset_ball {V : Opens ((a → ℝ) × (b → ℝ))}
    (hV : (V : Set ((a → ℝ) × (b → ℝ))) = (Ω : Set (a → ℝ)) ×ˢ (O : Set (b → ℝ)))
    {S : 𝓓(V, ℝ) →L[ℝ] F}
    (hS : ∀ (i : SmallBall Ω) (j : SmallBall O) (φ : 𝓓(Ω, ℝ)) (ψ : 𝓓(O, ℝ)),
      tsupport φ ⊆ i.ball → tsupport ψ ⊆ j.ball → S (prodSMulCLM ψ hV.symm.subset φ) = B φ ψ)
    (φ : 𝓓(Ω, ℝ)) (ψ : 𝓓(O, ℝ)) : S (prodSMulCLM ψ hV.symm.subset φ) = B φ ψ := by
  have hloc (ψ : 𝓓(O, ℝ)) (hψ : ∃ j : SmallBall O, tsupport ψ ⊆ j.ball) (φ : 𝓓(Ω, ℝ)) :
      S (prodSMulCLM ψ hV.symm.subset φ) = B φ ψ := by
    obtain ⟨j, hj⟩ := hψ
    let Φ : 𝓓(Ω, ℝ) →+ F :=
      { toFun φ := S (prodSMulCLM ψ hV.symm.subset φ) - B φ ψ
        map_zero' := by simp
        map_add' φ₁ φ₂ := by simp only [map_add, LinearMap.add_apply]; abel }
    have hΦ : Φ = 0 := AddMonoidHom.eq_zero_of_locally_vanishing Φ fun x hx ↦ by
      obtain ⟨i, hi⟩ := SmallBall.exists_mem_ball hx
      exact ⟨i.ball, i.ball.isOpen, hi, fun φ hφ ↦ sub_eq_zero.2 (hS i j φ ψ hφ hj)⟩
    exact sub_eq_zero.1 (DFunLike.congr_fun hΦ φ)
  have hadd (ψ₁ ψ₂ : 𝓓(O, ℝ)) : prodSMulCLM (ψ₁ + ψ₂) hV.symm.subset φ =
      prodSMulCLM ψ₁ hV.symm.subset φ + prodSMulCLM ψ₂ hV.symm.subset φ := by
    ext z
    simp [add_mul]
  let Ψ : 𝓓(O, ℝ) →+ F :=
    { toFun ψ := S (prodSMulCLM ψ hV.symm.subset φ) - B φ ψ
      map_zero' := by
        rw [map_zero, sub_zero, ← map_zero S]
        congr 1
        ext z
        simp
      map_add' ψ₁ ψ₂ := by
        simp only [hadd, map_add]
        abel }
  have hΨ : Ψ = 0 := AddMonoidHom.eq_zero_of_locally_vanishing Ψ fun y hy ↦ by
    obtain ⟨j, hj⟩ := SmallBall.exists_mem_ball hy
    exact ⟨j.ball, j.ball.isOpen, hj, fun ψ hψ ↦ sub_eq_zero.2 (hloc ψ ⟨j, hψ⟩ φ)⟩
  exact sub_eq_zero.1 (DFunLike.congr_fun hΨ ψ)

/-- **The Schwartz kernel theorem.** Let `Ω ⊆ ℝ^a` and `O ⊆ ℝ^b` be open sets and let `B` be a
bilinear map on the real test functions on `Ω` and on `O`, with values in a real Banach space
`F`, which is continuous in the sense that on functions supported in compact sets `K₁ ⊆ Ω` and
`K₂ ⊆ O` it is bounded by a product of `C^k` seminorms. Then there is a unique distribution `T`
on `V = Ω ×ˢ O`, the kernel of `B`, with `T (φ ⊗ ψ) = B φ ψ` on the tensor products
`(φ ⊗ ψ)(x, y) = ψ y • φ x` (`TestFunction.prodSMulCLM`). -/
theorem existsUnique_schwartzKernel_distribution
    (hB : ∀ (K₁ : Compacts (a → ℝ)) (K₂ : Compacts (b → ℝ)) (hK₁ : (K₁ : Set (a → ℝ)) ⊆ Ω)
      (hK₂ : (K₂ : Set (b → ℝ)) ⊆ O), ∃ (C : ℝ) (k : ℕ),
        ∀ (φ : 𝓓_{K₁}(a → ℝ, ℝ)) (ψ : 𝓓_{K₂}(b → ℝ, ℝ)),
          ‖B (ofSupportedIn hK₁ φ) (ofSupportedIn hK₂ ψ)‖ ≤
            C * ContDiffMapSupportedIn.supSeminorm ℝ _ ℝ ⊤ K₁ k φ *
              ContDiffMapSupportedIn.supSeminorm ℝ _ ℝ ⊤ K₂ k ψ)
    {V : Opens ((a → ℝ) × (b → ℝ))}
    (hV : (V : Set ((a → ℝ) × (b → ℝ))) = (Ω : Set (a → ℝ)) ×ˢ (O : Set (b → ℝ))) :
    ∃! T : 𝓓'(V, F), ∀ φ ψ, T (prodSMulCLM ψ hV.symm.subset φ) = B φ ψ := by
  classical
  choose S hS using exists_kernel_box hB
  have hcover := iSup_box (Ω := Ω) (O := O) hV
  have hboxV (i : SmallBall Ω) (j : SmallBall O) : box i j ≤ V := by
    rw [← hcover]
    exact le_iSup (fun ij : SmallBall Ω × SmallBall O ↦ box ij.1 ij.2) (i, j)
  -- The kernels on two boxes agree on their intersection, a box on which they agree on tensor
  -- products, which span a dense subspace.
  have hcompat (ij kl : SmallBall Ω × SmallBall O)
      (f : 𝓓(box ij.1 ij.2 ⊓ box kl.1 kl.2, ℝ)) :
      S ij.1 ij.2 (monoCLM ℝ f) = S kl.1 kl.2 (monoCLM ℝ f) := by
    have hW : ((box ij.1 ij.2 ⊓ box kl.1 kl.2 : Opens _) : Set ((a → ℝ) × (b → ℝ))) =
        ((ij.1.ball ⊓ kl.1.ball : Opens _) : Set (a → ℝ)) ×ˢ
          ((ij.2.ball ⊓ kl.2.ball : Opens _) : Set (b → ℝ)) := by
      rw [Opens.coe_inf, coe_box, coe_box, Opens.coe_inf, Opens.coe_inf, prod_inter_prod]
    have := ext_prodSMulCLM (T₁ := S ij.1 ij.2 ∘L monoCLM ℝ) (T₂ := S kl.1 kl.2 ∘L monoCLM ℝ) hW
      fun ψ φ ↦ by
        simp only [ContinuousLinearMap.comp_apply]
        rw [hS _ _ inf_le_left inf_le_left φ ψ _ (by ext p; simp),
          hS _ _ inf_le_right inf_le_right φ ψ _ (by ext p; simp)]
    exact congr($this f)
  obtain ⟨S', hS', -⟩ := Distribution.existsUnique_gluing (V := F) (n := ⊤) (F := ℝ)
    (U := fun ij : SmallBall Ω × SmallBall O ↦ box ij.1 ij.2) (T := fun ij ↦ S ij.1 ij.2)
    hcover hcompat
  -- The glued distribution is a kernel of `B` on tensor products supported in a box.
  have hbox (i : SmallBall Ω) (j : SmallBall O) (φ : 𝓓(Ω, ℝ)) (ψ : 𝓓(O, ℝ))
      (hφ : tsupport φ ⊆ i.ball) (hψ : tsupport ψ ⊆ j.ball) :
      S' (prodSMulCLM ψ hV.symm.subset φ) = B φ ψ := by
    let φ' : 𝓓(i.ball, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφ⟩
    let ψ' : 𝓓(j.ball, ℝ) := ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, hψ⟩
    have hsub : (i.ball : Set (a → ℝ)) ×ˢ (j.ball : Set (b → ℝ)) ⊆ box i j := subset_rfl
    have hφ' : monoCLM ℝ φ' = φ := TestFunction.ext fun x ↦ by simp [φ', i.ball_le]
    have hψ' : monoCLM ℝ ψ' = ψ := TestFunction.ext fun x ↦ by simp [ψ', j.ball_le]
    have hmono : monoCLM ℝ (prodSMulCLM ψ' hsub φ') = prodSMulCLM ψ hV.symm.subset φ :=
      TestFunction.ext fun z ↦ by
        simp only [TestFunction.monoCLM_apply, hboxV i j, le_rfl, and_self, ite_true,
          prodSMulCLM_apply, φ', ψ', TestFunction.coe_mk]
    rw [← hmono, ← ContinuousLinearMap.comp_apply, hS' (i, j),
      hS i j le_rfl le_rfl φ' ψ' _ (by ext p; simp), hφ', hψ']
  have htensor := prodSMulCLM_eq_of_forall_tsupport_subset_ball hV hbox
  refine ⟨ContinuousLinearMap.toUniformConvergenceCLM _ F _ S', fun φ ψ ↦ ?_, fun T hT ↦ ?_⟩
  · simpa using htensor φ ψ
  · refine ext_prodSMulCLM hV fun ψ φ ↦ ?_
    simpa [hT] using (htensor φ ψ).symm

end Kernel

end LinearMap
