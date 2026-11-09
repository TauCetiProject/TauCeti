/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.Foliation.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
import TauCeti.Geometry.Manifold.ContMDiff.Kernel
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# The kernel distribution of a two-form

Let `σ` be a smooth two-form on a real manifold `M`. Its *kernel* at `x` is the radical
`ker σ_x = {v | σ_x (v, ·) = 0}` of the alternating bilinear form `σ_x`, that is
`LinearMap.ker (σ.bilinFormAt x)`. This file studies the field of kernels `x ↦ ker σ_x` as a
distribution.

* If `M` is modelled on a finite-dimensional space and the kernels all have the same dimension
  `k`, they form a smooth distribution of rank `k`
  (`TauCeti.SmoothForm.isContMDiffDistribution_ker_bilinFormAt`). Read in a trivialization of the
  tangent bundle, `σ` is a smooth family of operators `E → E*` with kernels of constant
  dimension, and such kernels have smooth local bases (`ContMDiffOn.exists_contMDiffOn_basis_ker`).
* If `σ` is closed, the kernel field is involutive
  (`TauCeti.SmoothForm.isInvolutiveDistribution_ker_bilinFormAt`). For vector fields `V` and `W`
  tangent to the kernels on an open set and any vector field `Z`, every term of the invariant
  formula for `dσ (V, W, Z)` vanishes except `-σ ([V, W], Z)`, so `dσ = 0` puts `[V, W]` in the
  kernel. No constant-rank hypothesis is needed here.

A closed two-form whose kernels have constant dimension is a *presymplectic* form. Its kernel
field is therefore the tangent distribution of a foliation, the *characteristic foliation* of `σ`
(`TauCeti.SmoothForm.characteristicFoliation`), and by the Frobenius theorem
(`TauCeti.IsInvolutiveDistribution.exists_flatChart`) it is straightened by suitable charts near
every interior point. For instance, the pullback of a symplectic form to a coisotropic
submanifold is presymplectic, with kernels the symplectic complements of the tangent spaces, and
its characteristic leaves are the directions collapsed by coisotropic reduction. The rank
hypothesis cannot be dropped from the smoothness statement: `x dx ∧ dy` on `ℝ²` has kernel `ℝ²`
along the axis `x = 0` and `0` elsewhere.

## Main results

* `TauCeti.SmoothForm.isContMDiffDistribution_ker_bilinFormAt`: the kernels of a two-form of
  constant rank form a smooth distribution.
* `TauCeti.SmoothForm.isInvolutiveDistribution_ker_bilinFormAt`: the kernels of a closed two-form
  form an involutive distribution.
* `TauCeti.SmoothForm.characteristicFoliation`: the characteristic foliation of a presymplectic
  form.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 10
  (kernels of constant-rank bundle homomorphisms), Proposition 14.32 (the invariant formula for
  the exterior derivative) and Chapter 19 (involutive distributions and foliations).
* M. J. Gotay, *On coisotropic imbeddings of presymplectic manifolds*, Proceedings of the
  American Mathematical Society 84 (1982), 111–114 (the characteristic foliation of a
  presymplectic form).
-/

public section

noncomputable section

open Bundle Filter Module Set VectorField
open scoped Manifold ContDiff Topology

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

section Coordinates

variable [FiniteDimensional ℝ E]

/-- The two-form `σ` at `y`, read in the tangent trivialization at `x₀` as the operator
`u ↦ σ_y (u, ·)` from the model space to its dual. -/
private def trivBilin (σ : SmoothForm I M ℝ 2) (x₀ y : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  let s : E →ₗ[ℝ] TangentSpace I y := (trivializationAt E (TangentSpace I) x₀).symmL ℝ y
  ((σ.bilinFormAt y).compl₁₂ s s).toContinuousBilinearMap

private theorem trivBilin_apply (σ : SmoothForm I M ℝ 2) (x₀ y : M) (u w : E) :
    trivBilin σ x₀ y u w = σ.bilinFormAt y ((trivializationAt E (TangentSpace I) x₀).symmL ℝ y u)
      ((trivializationAt E (TangentSpace I) x₀).symmL ℝ y w) :=
  rfl

/-- The coordinate operators of a smooth two-form are `C^n` on the base set of the
trivialization. -/
private theorem contMDiffOn_trivBilin {n : ℕ∞ω} [ENat.LEInfty n] [IsManifold I (n + 1) M]
    (σ : SmoothForm I M ℝ 2) (x₀ : M) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) n (trivBilin σ x₀)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  let e := trivializationAt E (TangentSpace I) x₀
  intro y hy
  refine contMDiffWithinAt_clm_apply.mpr fun u ↦ contMDiffWithinAt_clm_apply.mpr fun w ↦ ?_
  -- Evaluate `σ` on the vector fields with constant coordinates `u` and `w` in `e`.
  have hσ := (σ.contMDiff.of_le (ENat.LEInfty.out : n ≤ ∞)).contMDiffOn (s := e.baseSet)
  have hv := hσ.continuousAlternatingMap_bundle_apply (b := id)
    (v := ![fun y ↦ e.symm y u, fun y ↦ e.symm y w]) fun i ↦ by
      fin_cases i
      exacts [Manifold.contMDiffOn_symm_baseSet u, Manifold.contMDiffOn_symm_baseSet w]
  have heq (z : M) (hz : z ∈ e.baseSet) :
      trivBilin σ x₀ z u w = σ.1 z ![e.symm z u, e.symm z w] := by
    rw [trivBilin_apply, bilinFormAt_apply, SmoothBundleForm.eval₂_apply, e.symmL_apply hz,
      e.symmL_apply hz]
  have hfun (z : M) : (fun i ↦ ![fun y ↦ e.symm y u, fun y ↦ e.symm y w] i z) =
      ![e.symm z u, e.symm z w] := by
    funext i
    fin_cases i <;> rfl
  have h := (contMDiffWithinAt_totalSpace.mp (hv y hy)).2
  simp only [hfun] at h
  exact (by simpa using h : ContMDiffWithinAt I 𝓘(ℝ, ℝ) n
    (fun z ↦ σ.1 z ![e.symm z u, e.symm z w]) e.baseSet y).congr heq (heq y hy)

/-- Over the base set of the trivialization, the kernel of `σ_y` corresponds to the kernel of its
coordinate operator. -/
private theorem ker_bilinFormAt_eq_comap (σ : SmoothForm I M ℝ 2) {x₀ y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    LinearMap.ker (σ.bilinFormAt y) = (trivBilin σ x₀ y).ker.comap
      ((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ y hy :
        TangentSpace I y →ₗ[ℝ] E) := by
  let L := (trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ y hy
  have hsymm : ⇑((trivializationAt E (TangentSpace I) x₀).symmL ℝ y) = ⇑L.symm :=
    ((trivializationAt E (TangentSpace I) x₀).symm_continuousLinearEquivAt_eq hy).symm
  ext v
  simp only [LinearMap.mem_ker, Submodule.mem_comap]
  constructor
  · intro h
    ext w
    simp [trivBilin_apply, hsymm, L, Trivialization.symm_apply_apply_mk _ hy, h]
  · intro h
    ext w
    simpa [trivBilin_apply, hsymm, L, Trivialization.symm_apply_apply_mk _ hy] using
      congr($h (L w))

end Coordinates

/-- **The kernels of a two-form of constant rank form a smooth distribution.** If the kernels
`ker σ_x` of a smooth two-form `σ` all have dimension `k`, then `x ↦ ker σ_x` is a `C^n`
distribution of rank `k`, for every `n ≤ ∞` such that `M` is `C^(n + 1)`. -/
theorem isContMDiffDistribution_ker_bilinFormAt [FiniteDimensional ℝ E] {n : ℕ∞ω}
    [ENat.LEInfty n] [IsManifold I (n + 1) M] (σ : SmoothForm I M ℝ 2) {k : ℕ}
    (hk : ∀ x, finrank ℝ (LinearMap.ker (σ.bilinFormAt x)) = k) :
    IsContMDiffDistribution I n k fun x ↦ LinearMap.ker (σ.bilinFormAt x) := by
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  refine isContMDiffDistribution_iff.mpr fun x₀ ↦ ?_
  let e := trivializationAt E (TangentSpace I) x₀
  let L (y : M) (hy : y ∈ e.baseSet) := e.continuousLinearEquivAt ℝ y hy
  have hkA (y : M) (hy : y ∈ e.baseSet) : finrank ℝ (trivBilin σ x₀ y).ker = k := by
    rw [← hk y, ker_bilinFormAt_eq_comap σ hy, Submodule.comap_equiv_eq_map_symm,
      LinearEquiv.finrank_map_eq]
  -- Smooth bases of the kernels of the coordinate operators, transported to the tangent spaces.
  obtain ⟨W, hW, hx₀W, hWe, v, hv, hvker⟩ :=
    (contMDiffOn_trivBilin (n := n) σ x₀).exists_contMDiffOn_basis_ker e.open_baseSet hkA
      (mem_baseSet_trivializationAt E (TangentSpace I) x₀)
  -- On `W`, the inverse of `e` at `y` is the inverse of the linear equivalence `L y`.
  have hsymm {y : M} (hy : y ∈ W) : e.symm y = ⇑(L y (hWe hy)).symm := by
    funext u
    rw [e.symm_continuousLinearEquivAt_eq (hWe hy), e.symmL_apply (hWe hy)]
  refine ⟨W, hW, hx₀W, fun i y ↦ e.symm y (v i y), ⟨fun i y hy ↦ ?_, fun {y} hy ↦ ?_,
    fun {y} hy ↦ ?_⟩⟩
  · -- In `e`, the coordinates of the frame are the smooth maps `v i`.
    refine (Trivialization.contMDiffWithinAt_section_iff (e := e) W (hWe hy)).2 ?_
    exact (hv i y hy).congr (fun z hz ↦ by simp only [e.apply_mk_symm (hWe hz)])
      (by simp only [e.apply_mk_symm (hWe hy)])
  · rw [hsymm hy]
    exact (hvker y hy).1.map' _ (L y (hWe hy)).symm.ker
  · -- Transport the span of the coordinate basis along `(L y).symm`.
    rw [ker_bilinFormAt_eq_comap σ (hWe hy), Submodule.comap_equiv_eq_map_symm,
      ← (hvker y hy).2, Submodule.map_span, ← range_comp]
    simp [e, Function.comp_def]

/-- **The kernels of a closed two-form form an involutive distribution.** If `σ` is closed and
`V`, `W` are vector fields differentiable and tangent to the kernels of `σ` on an open set, then
their Lie bracket is tangent to the kernels on that set. No constant-rank hypothesis is
needed. -/
theorem isInvolutiveDistribution_ker_bilinFormAt [IsManifold I 2 M] (σ : SmoothForm I M ℝ 2)
    (hσ : σ.IsClosed) : IsInvolutiveDistribution I fun x ↦ LinearMap.ker (σ.bilinFormAt x) := by
  have : IsManifold I (1 + 1) M := IsManifold.of_le (n := 2) one_add_one_eq_two.le
  let : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  refine isInvolutiveDistribution_iff.mpr fun U hU V W hV hW hVD hWD x hx ↦ ?_
  rw [LinearMap.mem_ker]
  ext w
  -- Extend `w` to a vector field `Z`.
  let Z : (y : M) → TangentSpace I y := FiberBundle.extend E w
  have hZx : Z x = w := FiberBundle.extend_apply_self E w
  have hZ : MDifferentiableAt I I.tangent (fun y ↦ (Z y : TangentBundle I M)) x :=
    FiberBundle.mdifferentiableAt_extend I E w
  have hVx := (hV x hx).mdifferentiableAt (hU.mem_nhds hx)
  have hWx := (hW x hx).mdifferentiableAt (hU.mem_nhds hx)
  -- Functions which vanish near `x` have zero derivative there.
  have hzero {f : M → ℝ} (hf : ∀ y ∈ U, f y = 0) : mvfderiv I f x = 0 := by
    have hf' : f =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := eventually_of_mem (hU.mem_nhds hx) hf
    ext v
    simp [mvfderiv, hf'.mfderiv_eq]
  have hker {X : (y : M) → TangentSpace I y} (hX : ∀ y ∈ U, X y ∈ LinearMap.ker (σ.bilinFormAt y))
      {y : M} (hy : y ∈ U) (u : TangentSpace I y) : σ.1 y ![X y, u] = 0 := by
    simpa using congr($(LinearMap.mem_ker.mp (hX y hy)) u)
  have hker' {X : (y : M) → TangentSpace I y}
      (hX : ∀ y ∈ U, X y ∈ LinearMap.ker (σ.bilinFormAt y)) {y : M} (hy : y ∈ U)
      (u : TangentSpace I y) : σ.1 y ![u, X y] = 0 := by
    have h := SmoothBundleForm.eval₂_swap σ y u (X y)
    simp only [SmoothBundleForm.eval₂_apply] at h
    rw [h, hker hX hy, neg_zero]
  -- In the invariant formula for `dσ (V, W, Z)` at `x`, only `-σ ([V, W], Z)` survives.
  have hd := mextDeriv_apply_two (φ := σ) hVx hWx hZ
  rw [(isClosed_def σ).mp hσ, hzero fun y hy ↦ hker hWD hy _, hzero fun y hy ↦ hker hVD hy _,
    hzero fun y hy ↦ hker hVD hy _, hker' hWD hx, hker' hVD hx, hZx] at hd
  simpa [bilinFormAt_apply, SmoothBundleForm.eval₂_apply, sub_eq_zero, eq_comm] using hd

/-- The **characteristic foliation** of a presymplectic form: for a closed two-form `σ` whose
kernels all have dimension `k`, the `C^n` foliation of rank `k` whose tangent distribution is
`x ↦ ker σ_x` (requires `1 ≤ n`). -/
def characteristicFoliation [FiniteDimensional ℝ E] {n : ℕ∞ω} [ENat.LEInfty n]
    [IsManifold I (n + 1) M] (σ : SmoothForm I M ℝ 2) (hσ : σ.IsClosed) {k : ℕ}
    (hk : ∀ x, finrank ℝ (LinearMap.ker (σ.bilinFormAt x)) = k) (hn : 1 ≤ n) :
    Foliation I n M k where
  one_le := hn
  distribution x := LinearMap.ker (σ.bilinFormAt x)
  isContMDiffDistribution := σ.isContMDiffDistribution_ker_bilinFormAt hk
  isInvolutiveDistribution :=
    have : IsManifold I 2 M :=
      IsManifold.of_le (n := n + 1) (by rw [← one_add_one_eq_two]; exact add_le_add hn le_rfl)
    σ.isInvolutiveDistribution_ker_bilinFormAt hσ

/-- The tangent distribution of the characteristic foliation of a presymplectic form is its
field of kernels. -/
@[simp]
theorem characteristicFoliation_distribution [FiniteDimensional ℝ E] {n : ℕ∞ω}
    [ENat.LEInfty n] [IsManifold I (n + 1) M] (σ : SmoothForm I M ℝ 2) (hσ : σ.IsClosed) {k : ℕ}
    (hk : ∀ x, finrank ℝ (LinearMap.ker (σ.bilinFormAt x)) = k) (hn : 1 ≤ n) (x : M) :
    (σ.characteristicFoliation hσ hk hn).distribution x = LinearMap.ker (σ.bilinFormAt x) :=
  (rfl)

end SmoothForm

end TauCeti
