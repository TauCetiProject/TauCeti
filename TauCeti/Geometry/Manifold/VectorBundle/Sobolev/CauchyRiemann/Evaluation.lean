/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.ZeroCount
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Fredholm
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Regularity
import Mathlib.SetTheory.Cardinal.Embedding
import TauCeti.Geometry.Manifold.Connected
import TauCeti.Topology.VectorBundle.FiniteDimensional

/-!
# Evaluating the kernel of a real Cauchy–Riemann operator at points

Let `D` be a smooth real Cauchy–Riemann operator on a complex vector bundle `V` over a closed
Riemann surface `M`, realized as `D_p : W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)`. For `p > 1`, the
elements of the kernel of `D_p` are smooth sections, so they can be evaluated at points: for a
family of points `x : ι → M`, this file defines the evaluation map
`TauCeti.IsRealCauchyRiemannOperator.kerSobolevLEval : ker D_p → Π i, V (x i)`.

When `V = L` is a line bundle over a connected `M`, with first Chern number `d = c₁(L)[M]`, the
zero count of `TauCeti.IsRealCauchyRiemannOperator.ncard_le_evalFundamentalClass_complexEulerClass`
makes the evaluation at any `d + 1` distinct points injective
(`TauCeti.IsRealCauchyRiemannOperator.kerSobolevLEval_injective`). So the kernel has real
dimension at most `2 (d + 1)` (`TauCeti.IsRealCauchyRiemannOperator.finrank_ker_sobolevL_le`),
and the Fredholm index of `D_p`, which is at most this dimension, is at most `2 (d + 1)`
(`TauCeti.IsRealCauchyRiemannOperator.index_sobolevL_le`).

This is the automatic regularity of line operators of degree `d ≥ -1` used for embedded spheres in
four-manifolds: there the Riemann–Roch theorem gives `ind D_p = χ(S²) + 2 d = 2 (d + 1)`. Under the
hypothesis `2 (d + 1) ≤ ind D_p`, for `1 < p < ∞` and `d ≥ -1`:

* `D_p` is onto (`TauCeti.IsRealCauchyRiemannOperator.sobolevL_surjective_of_le_index`) and its
  kernel has real dimension exactly `2 (d + 1)`
  (`TauCeti.IsRealCauchyRiemannOperator.finrank_ker_sobolevL_eq_of_le_index`);
* the evaluation at at most `d + 1` distinct points is onto
  (`TauCeti.IsRealCauchyRiemannOperator.kerSobolevLEval_surjective_of_le_index`), and at exactly
  `d + 1` distinct points it is bijective
  (`TauCeti.IsRealCauchyRiemannOperator.kerSobolevLEval_bijective_of_le_index`);
* in particular, if `d ≥ 0`, every value at every point is taken by a smooth section in the kernel
  of `D` (`TauCeti.IsRealCauchyRiemannOperator.exists_contMDiff_apply_eq_of_le_index`), so a
  smooth solution of `D ξ = η` can be corrected by an element of the kernel to vanish at a given
  point.

For `d = -1` the kernel is zero and the hypothesis is `0 ≤ ind D_p`, so `D_p` is an isomorphism.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.kerSobolevLEval`: evaluation of the kernel at points.
* `TauCeti.IsRealCauchyRiemannOperator.kerSobolevLEval_injective`: on a line bundle, evaluation at
  more than `c₁(L)[M]` distinct points is injective.
* `TauCeti.IsRealCauchyRiemannOperator.finrank_ker_sobolevL_le`: the kernel has real dimension at
  most `2 (c₁(L)[M] + 1)`.
* `TauCeti.IsRealCauchyRiemannOperator.index_sobolevL_le`: the index is at most
  `2 (c₁(L)[M] + 1)`.
* `TauCeti.IsRealCauchyRiemannOperator.sobolevL_surjective_of_le_index`: automatic surjectivity
  in degree `≥ -1` when the index is `2 (c₁(L)[M] + 1)`.
* `TauCeti.IsRealCauchyRiemannOperator.kerSobolevLEval_bijective_of_le_index`: the kernel is then
  identified with the fibres at `c₁(L)[M] + 1` distinct points.

## Implementation notes

The first Chern number `c₁(L)[M]` is written, as in
`TauCeti.IsRealCauchyRiemannOperator.ncard_le_evalFundamentalClass_complexEulerClass`, as the
complex Euler class of `L` evaluated on the fundamental class of `M`; the results after the
injectivity theorem name it `d` through a hypothesis `hd`. Stating it needs `[CompactSpace M]`,
which also follows from the finite bundle atlas. The Riemann–Roch theorem is not proved here, so
the index enters as the hypothesis `2 (d + 1) ≤ ind D_p`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition, AMS
  Colloquium Publications 52 (2012), Theorem C.1.10 (iii) and its proof (p. 603).
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set Function
open scoped Manifold ENNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure

namespace IsRealCauchyRiemannOperator

section Evaluation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealCauchyRiemannEvaluation : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Evaluation of the kernel at points.** For `p > 1`, every element of the kernel of the
realization `W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)` of `D` is the Sobolev section of a unique `C¹`
section (`TauCeti.IsRealCauchyRiemannOperator.kerSobolevLEquivComap`); this is the real-linear map
evaluating that section at the points `x i`. -/
def kerSobolevLEval (hp : 1 < p) {ι : Type*} (x : ι → M) :
    (hD.sobolevL A hDs volume p).ker →ₗ[ℝ] Π i, V (x i) :=
  (LinearMap.pi fun i ↦ (ContMDiffSection.evalLinearMap 𝓘(ℝ, ℂ) F _ V (x i)).comp
    (Submodule.subtype _)) ∘ₗ (kerSobolevLEquivComap A hD hDs hp).symm.toLinearMap

/-- The evaluation of a kernel element is the evaluation of the `C¹` section it comes from. -/
theorem kerSobolevLEval_apply_eq_kerSobolevLEquivComap_symm (hp : 1 < p) {ι : Type*} (x : ι → M)
    (w : (hD.sobolevL A hDs volume p).ker) (i : ι) :
    kerSobolevLEval A hD hDs hp x w i =
      ((kerSobolevLEquivComap A hD hDs hp).symm w : Cₛ^((1 : ℕ) : WithTop ℕ∞)⟮𝓘(ℝ, ℂ); F, V⟯)
        (x i) := by
  simp [kerSobolevLEval]

/-- The evaluation of the Sobolev section of a `C¹` section `s` in the kernel is the evaluation of
`s`. -/
@[simp]
theorem kerSobolevLEval_apply (hp : 1 < p) {ι : Type*} (x : ι → M)
    {s : Cₛ^((1 : ℕ) : WithTop ℕ∞)⟮𝓘(ℝ, ℂ); F, V⟯}
    (hs : SobolevSection.ofContMDiffSection A volume p 1 s ∈ (hD.sobolevL A hDs volume p).ker)
    (i : ι) :
    kerSobolevLEval A hD hDs hp x ⟨_, hs⟩ i = s (x i) := by
  simp [kerSobolevLEval]

/-- The evaluation of a kernel element which is the Sobolev section of a `C¹` section `s` is the
evaluation of `s`. -/
theorem kerSobolevLEval_apply_of_eq (hp : 1 < p) {ι : Type*} (x : ι → M)
    {w : (hD.sobolevL A hDs volume p).ker} {s : Cₛ^((1 : ℕ) : WithTop ℕ∞)⟮𝓘(ℝ, ℂ); F, V⟯}
    (hws : (w : SobolevSection A volume p 1) = SobolevSection.ofContMDiffSection A volume p 1 s)
    (i : ι) :
    kerSobolevLEval A hD hDs hp x w i = s (x i) := by
  obtain ⟨w, hw⟩ := w
  subst hws
  exact kerSobolevLEval_apply A hD hDs hp x hw i

end Evaluation

section LineBundle

variable {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {L : M → Type} [TopologicalSpace (TotalSpace ℂ L)] [∀ x, AddCommGroup (L x)]
  [∀ x, Module ℝ (L x)] [∀ x, Module ℂ (L x)] [∀ x, IsScalarTower ℝ ℂ (L x)]
  [∀ x, TopologicalSpace (L x)] [∀ x, IsTopologicalAddGroup (L x)] [∀ x, ContinuousSMul ℝ (L x)]
  [∀ x, ContinuousSMul ℂ (L x)] [FiberBundle ℂ L] [VectorBundle ℂ ℂ L]

local instance instVectorBundleRealCauchyRiemannEvaluationLine : VectorBundle ℝ ℂ L :=
  VectorBundle.restrictScalars ℝ ℂ ℂ L

variable [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M ℂ L)
  {D : (Π x : M, L x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] L x}
  (hD : IsRealCauchyRiemannOperator ℂ (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn ℂ ∞ D univ)
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable [CompactSpace M] [ConnectedSpace M] {d : ℤ}
  (hd : ((complexHomologicalOrientation M).evalFundamentalClass Complex.finrank_real_complex
    (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id M)
    (complexEulerClass ℂ L (r := 0) (finrank_self ℂ))).down = d)

include hD hDs in
/-- **The kernel is detected at more than `c₁(L)[M]` points.** On a compact connected Riemann
surface, the evaluation of the kernel of the realization `W^{1,p}(M, L) → Lᵖ(M, Λ^{0,1} ⊗ L)`,
`p > 1`, of a smooth real Cauchy–Riemann operator on a complex line bundle `L` at a family of
distinct points is injective as soon as there are more than `c₁(L)[M]` of them (`Nat.card ι` is `0`
for an infinite family). -/
theorem kerSobolevLEval_injective (hp : 1 < p) {ι : Type*} {x : ι → M}
    (hx : Injective x)
    (hlt : ((complexHomologicalOrientation M).evalFundamentalClass Complex.finrank_real_complex
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id M)
        (complexEulerClass ℂ L (r := 0) (finrank_self ℂ))).down < Nat.card ι) :
    Injective (kerSobolevLEval A hD hDs hp x) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw ↦ ?_
  -- The kernel element `w` is the Sobolev section of a `C¹` section `t`, vanishing at the `x i`.
  set t := (kerSobolevLEquivComap A hD hDs hp).symm w with ht
  have hw' : w = kerSobolevLEquivComap A hD hDs hp t := by simp [ht]
  have hDt : ∀ y, D (t : Cₛ^((1 : ℕ) : WithTop ℕ∞)⟮𝓘(ℝ, ℂ); ℂ, L⟯) y = 0 :=
    (ofContMDiffSection_mem_ker_sobolevL_iff A hD hDs hp _).1 t.property
  have hval (i : ι) : (t : Cₛ^((1 : ℕ) : WithTop ℕ∞)⟮𝓘(ℝ, ℂ); ℂ, L⟯) (x i) = 0 :=
    (kerSobolevLEval_apply_eq_kerSobolevLEquivComap_symm A hD hDs hp x w i).symm.trans
      (congrFun hw i)
  have hzero := eq_zero_of_evalFundamentalClass_complexEulerClass_lt_ncard hD hDs
    (t : Cₛ^((1 : ℕ) : WithTop ℕ∞)⟮𝓘(ℝ, ℂ); ℂ, L⟯).contMDiff (funext hDt) (S := range x)
    (by rintro _ ⟨i, rfl⟩; exact hval i) (by rwa [ncard_range_of_injective hx])
  rw [hw', show t = 0 from Subtype.ext (ContMDiffSection.coe_injective hzero), map_zero]

include hD hDs hd in
/-- **The dimension of the kernel.** On a compact connected Riemann surface, the kernel of the
realization `W^{1,p}(M, L) → Lᵖ(M, Λ^{0,1} ⊗ L)`, `p > 1`, of a smooth real Cauchy–Riemann
operator on a complex line bundle `L` of degree `d = c₁(L)[M]` has real dimension at most
`2 (d + 1)`, and is zero if `d < 0`: evaluation at `d + 1` distinct points is injective. -/
theorem finrank_ker_sobolevL_le (hp : 1 < p) :
    finrank ℝ (hD.sobolevL A hDs volume p).ker ≤ 2 * (d + 1).toNat := by
  have : Infinite M := infinite_of_nontrivial_model (E := ℂ)
  -- Any `d + 1` distinct points of the infinite surface `M`.
  let x : Fin (d + 1).toNat ↪ M := Fin.valEmbedding.trans (Infinite.natEmbedding M)
  have := VectorBundle.finiteDimensional_pi ℝ ℂ L x
  have h := LinearMap.finrank_le_finrank_of_injective
    (kerSobolevLEval_injective A hD hDs hp x.injective (by rw [Nat.card_fin]; omega))
  have hdim : finrank ℝ (Π i, L (x i)) = (d + 1).toNat * 2 := by
    rw [VectorBundle.finrank_pi ℝ ℂ L, Nat.card_fin, Complex.finrank_real_complex]
  omega

include hD hDs hd in
/-- **An upper bound for the index.** On a compact connected Riemann surface, the index of the
realization `W^{1,p}(M, L) → Lᵖ(M, Λ^{0,1} ⊗ L)`, `p > 1`, of a smooth real Cauchy–Riemann operator
on a complex line bundle `L` of degree `d = c₁(L)[M]` is at most `2 (d + 1)`, and at most `0` if
`d < 0`, since it is at most the dimension of the kernel. -/
theorem index_sobolevL_le (hp : 1 < p) :
    (hD.sobolevL A hDs volume p).index ≤ 2 * (d + 1).toNat := by
  have hk := finrank_ker_sobolevL_le A hD hDs hd hp
  rw [ContinuousLinearMap.index_eq_finrank_sub]
  omega

include hD hDs hd in
/-- **Automatic surjectivity** (McDuff–Salamon, Theorem C.1.10 (iii), on the sphere). On a compact
connected Riemann surface, let `D` be a smooth real Cauchy–Riemann operator on a complex line
bundle `L` of degree `d = c₁(L)[M] ≥ -1`, whose realization
`W^{1,p}(M, L) → Lᵖ(M, Λ^{0,1} ⊗ L)`, `1 < p < ∞`, has index at least `2 (d + 1)`; on the sphere
this is the index given by the Riemann–Roch theorem. Then the realization is onto. -/
theorem sobolevL_surjective_of_le_index (hp : 1 < p) (hp_top : p ≠ ⊤) (hd₁ : -1 ≤ d)
    (hind : 2 * (d + 1) ≤ (hD.sobolevL A hDs volume p).index) :
    Surjective (hD.sobolevL A hDs volume p) := by
  have := (isFredholm_sobolevL A hD hDs hp hp_top).finite_coker
  have hk := finrank_ker_sobolevL_le A hD hDs hd hp
  rw [ContinuousLinearMap.index_eq_finrank_sub] at hind
  -- The cokernel has dimension at most `dim ker - ind ≤ 0`.
  have hc : Subsingleton (_ ⧸ LinearMap.range
      (hD.sobolevL A hDs volume p :
        SobolevSection A volume p 1 →ₗ[ℝ] zeroOneSobolevSections A volume p 0)) := by
    rw [← Module.finrank_zero_iff (R := ℝ)]
    omega
  rwa [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top] at hc

include hD hDs hd in
/-- Under the hypotheses of
`TauCeti.IsRealCauchyRiemannOperator.sobolevL_surjective_of_le_index`, the kernel of the
realization has real dimension exactly `2 (d + 1)`, where `d = c₁(L)[M]`. -/
theorem finrank_ker_sobolevL_eq_of_le_index (hp : 1 < p) (hd₁ : -1 ≤ d)
    (hind : 2 * (d + 1) ≤ (hD.sobolevL A hDs volume p).index) :
    (finrank ℝ (hD.sobolevL A hDs volume p).ker : ℤ) = 2 * (d + 1) := by
  have hk := finrank_ker_sobolevL_le A hD hDs hd hp
  rw [ContinuousLinearMap.index_eq_finrank_sub] at hind
  omega

include hD hDs hd in
/-- **The kernel takes all values at few points.** Under the hypotheses of
`TauCeti.IsRealCauchyRiemannOperator.sobolevL_surjective_of_le_index`, the evaluation of the
kernel at at most `d + 1` distinct points is onto, where `d = c₁(L)[M]`. -/
theorem kerSobolevLEval_surjective_of_le_index (hp : 1 < p) {ι : Type*} [Finite ι] {x : ι → M}
    (hx : Injective x) (hcard : Nat.card ι ≤ d + 1)
    (hind : 2 * (d + 1) ≤ (hD.sobolevL A hDs volume p).index) :
    Surjective (kerSobolevLEval A hD hDs hp x) := by
  have : Infinite M := infinite_of_nontrivial_model (E := ℂ)
  -- Complete `x` to a family `z` of `d + 1` distinct points.
  set m := (d + 1).toNat - Nat.card ι
  obtain ⟨y, hy⟩ := Fin.Embedding.exists_embedding_disjoint_range_of_add_le_ENat_card
    (s := Set.range x) (n := m) (by simp [ENat.card_eq_top_of_infinite])
  have hz : Injective (Sum.elim x y) :=
    hx.sumElim y.injective fun a b h ↦ Set.disjoint_left.1 hy ⟨a, rfl⟩ ⟨b, h.symm⟩
  set z := Sum.elim x y
  have hcardz : Nat.card (ι ⊕ Fin m) = (d + 1).toNat := by
    rw [Nat.card_sum, Nat.card_fin]
    omega
  -- At these points the evaluation is injective between spaces of the same dimension.
  have := VectorBundle.finiteDimensional_pi ℝ ℂ L z
  have hinj := kerSobolevLEval_injective A hD hDs hp hz (by rw [hcardz, hd]; omega)
  have hsurj : Surjective (kerSobolevLEval A hD hDs hp z) := by
    have hfin : FiniteDimensional ℝ (hD.sobolevL A hDs volume p).ker :=
      Module.Finite.of_injective _ hinj
    have hk := finrank_ker_sobolevL_eq_of_le_index A hD hDs hd hp (by omega) hind
    have hdim : finrank ℝ (Π k, L (z k)) = (d + 1).toNat * 2 := by
      rw [VectorBundle.finrank_pi ℝ ℂ L, hcardz, Complex.finrank_real_complex]
    have h : finrank ℝ (hD.sobolevL A hDs volume p).ker = finrank ℝ (Π k, L (z k)) := by
      omega
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ)
      (V := (hD.sobolevL A hDs volume p).ker) (V₂ := Π k, L (z k)) h).1 hinj
  intro g
  obtain ⟨w, hw⟩ := hsurj (Sum.rec g fun _ ↦ 0)
  refine ⟨w, funext fun i ↦ ?_⟩
  have hi := congrFun hw (Sum.inl i)
  -- `z (Sum.inl i)` is `x i` and the target value there is `g i`, by `Sum.elim_inl` and `Sum.rec`.
  simp only [z, kerSobolevLEval_apply_eq_kerSobolevLEquivComap_symm, Sum.elim_inl] at hi
  rwa [kerSobolevLEval_apply_eq_kerSobolevLEquivComap_symm]

include hD hDs hd in
/-- **The kernel is the space of values at `d + 1` points.** Under the hypotheses of
`TauCeti.IsRealCauchyRiemannOperator.sobolevL_surjective_of_le_index`, the evaluation of the
kernel at `d + 1` distinct points is bijective, where `d = c₁(L)[M]`. -/
theorem kerSobolevLEval_bijective_of_le_index (hp : 1 < p) {ι : Type*} [Finite ι] {x : ι → M}
    (hx : Injective x) (hcard : Nat.card ι = d + 1)
    (hind : 2 * (d + 1) ≤ (hD.sobolevL A hDs volume p).index) :
    Bijective (kerSobolevLEval A hD hDs hp x) :=
  ⟨kerSobolevLEval_injective A hD hDs hp hx (by omega),
    kerSobolevLEval_surjective_of_le_index A hD hDs hd hp hx hcard.le hind⟩

include hD hDs hd in
/-- **Prescribing the value at a point.** Under the hypotheses of
`TauCeti.IsRealCauchyRiemannOperator.sobolevL_surjective_of_le_index` with `d = c₁(L)[M] ≥ 0`,
every vector `v` in a fibre `L y` is the value at `y` of a smooth section in the kernel of `D`. So a
smooth solution of `D ξ = η` can be corrected by an element of the kernel to vanish at `y`. -/
theorem exists_contMDiff_apply_eq_of_le_index (hp : 1 < p) (hd₀ : 0 ≤ d)
    (hind : 2 * (d + 1) ≤ (hD.sobolevL A hDs volume p).index) (y : M) (v : L y) :
    ∃ s : Π x, L x, ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞ (T% s) ∧ (∀ x, D s x = 0) ∧
      s y = v := by
  obtain ⟨w, hw⟩ := kerSobolevLEval_surjective_of_le_index A hD hDs hd hp
    (x := fun _ : Unit ↦ y) (injective_of_subsingleton _) (by rw [Nat.card_unique]; omega) hind
    fun _ ↦ v
  obtain ⟨s, hs, hws, hDs0⟩ := exists_contMDiff_of_sobolevL_eq_zero A hD hDs hp w.property
  exact ⟨s, hs, hDs0,
    (kerSobolevLEval_apply_of_eq A hD hDs hp _ hws ()).symm.trans (congrFun hw ())⟩

end LineBundle

end IsRealCauchyRiemannOperator

end TauCeti
