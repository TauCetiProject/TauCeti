/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Involutive
import TauCeti.Geometry.Manifold.RegularValue.Snoc
import TauCeti.Geometry.Manifold.ContMDiff.Pi
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Geometry.Manifold.Flow.Straightening
import TauCeti.Geometry.Symplectic.Hamiltonian.Bracket

/-!
# Extending involutive families of independent functions

Let `σ` be a symplectic form on a boundaryless Hausdorff manifold `M` of dimension `2n`, with the
conventions `ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g) = df(X_g)`. A family `F = (F₁, …, F_k)` of
smooth functions which pairwise Poisson-commute near a point `x`, and whose differentials are
independent at `x`, has at most `n` members
(`TauCeti.SmoothTwoForm.IsNondegenerate.two_mul_card_le_finrank`). This file proves that the
bound is the only obstruction: every such family extends near `x` to a family of exactly `n`
functions with the same properties
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_isRegularPoint_castLE`). This is the first step of the
Carathéodory–Jacobi–Lie theorem, which then chooses the `n` functions as the momenta of a Darboux
chart.

The extension adds one function at a time
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_isRegularPoint_finSnoc`). Since the `F_i`
Poisson-commute near `x`, their Hamiltonian vector fields `X_i` commute there
(`TauCeti.SmoothTwoForm.IsNondegenerate.mlieBracket_hamiltonianVectorField_eq_zero`), and they are
independent at `x`
(`TauCeti.SmoothTwoForm.IsNondegenerate.linearIndependent_hamiltonianVectorField`). So some
chart `φ` around `x` straightens all of them at once: `dφ(X_i) = u_i` for constant vectors `u_i`
(`TauCeti.exists_chart_mfderiv_eq_const_of_eventually_mlieBracket_eq_zero`). A function
`g = ℓ ∘ φ`, for a linear form `ℓ` vanishing on every `u_i`, then satisfies
`{F_i, g} = -dg(X_i) = -ℓ(u_i) = 0` on the domain of `φ`. The `X_i(x)` span a subspace of
dimension `k` of `ker dF_x`, which has dimension `2n - k > k` when `k < n`. So there is a vector
`w ∈ ker dF_x` outside that span
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_mem_ker_mfderiv_notMem_span`), and `ℓ` can be
chosen with `ℓ(dφ_x w) = 1`, which makes `dg_x` independent of the `dF_i(x)`
(`TauCeti.IsRegularPoint.finSnoc`). A bump function extends `g` from a neighbourhood of `x` to a
smooth function on `M`.

## Main results

* `TauCeti.SmoothTwoForm.IsSymplectic.exists_poissonBracket_eventuallyEq_zero_mvfderiv_eq_one`: a
  function Poisson-commuting with the `F_i` near `x` whose differential at `x` is `1` on a given
  vector outside the span of the `X_{F_i}(x)`.
* `TauCeti.SmoothTwoForm.IsSymplectic.exists_isRegularPoint_finSnoc`: fewer than `n` independent
  functions which Poisson-commute near `x` can be extended by one more.
* `TauCeti.SmoothTwoForm.IsSymplectic.exists_isRegularPoint_castLE`: at most `n` independent
  functions which Poisson-commute near `x` extend to `n` such functions.

## References

* P. Libermann and C.-M. Marle, *Symplectic Geometry and Analytical Mechanics*, Mathematics and
  its Applications 35, D. Reidel, 1987 (the Carathéodory–Jacobi–Lie theorem).
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 9.46 (canonical form for commuting vector fields).
-/

public section

open Module Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothTwoForm

namespace IsSymplectic

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
  {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic) {x : M}

include hσ

/-- **A function commuting with an involutive family, with prescribed derivative.** Let the
smooth functions `F₁, …, F_k` pairwise Poisson-commute near `x` and have independent differentials
at `x`. For every tangent vector `w` at `x` outside the span of the Hamiltonian vectors
`X_{F_i}(x)` there is a smooth function `g` which Poisson-commutes with every `F_i` near `x` and
whose differential at `x` takes the value `1` on `w`. -/
theorem exists_poissonBracket_eventuallyEq_zero_mvfderiv_eq_one {ι : Type*} [Fintype ι]
    {F : M → ι → ℝ} (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
    (hcomm : ∀ i j, σ.poissonBracket (F · i) (F · j) =ᶠ[𝓝 x] fun _ ↦ 0)
    (hreg : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x) {w : TangentSpace I x}
    (hw : w ∉ Submodule.span ℝ (range fun i ↦ σ.hamiltonianVectorField (F · i) x)) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ g ∧
      (∀ i, σ.poissonBracket (F · i) g =ᶠ[𝓝 x] fun _ ↦ 0) ∧ mvfderiv I g x w = 1 := by
  have hn := hσ.isNondegenerate
  have hFi (i : ι) : ContMDiff I 𝓘(ℝ) ∞ (F · i) := contMDiff_pi_module_iff.1 hF i
  -- A chart `e` around `x` straightens the commuting Hamiltonian vector fields `X_{F_i}`:
  -- `D_y (X_{F_i}(y)) = u_i` for the differential `D_y` of `e` at every `y` in its domain.
  obtain ⟨e, u, he, hxe, -, heu⟩ :=
    exists_chart_mfderiv_eq_const_of_eventually_mlieBracket_eq_zero (m := ⊤) (n := ∞) le_top
      (by simp) (V := fun i ↦ σ.hamiltonianVectorField (F · i)) (U := univ)
      BoundarylessManifold.isInteriorPoint
      (fun i ↦ (hn.contMDiff_hamiltonianVectorField le_rfl (by simpa using hFi i)).contMDiffOn)
      univ_mem (hn.linearIndependent_hamiltonianVectorField hreg) fun i j _ ↦
        (hcomm i j).eventually_nhds.mono fun _ hy ↦
          hn.mlieBracket_hamiltonianVectorField_eq_zero hσ.isClosed ((hFi i).of_le (by simp))
            ((hFi j).of_le (by simp)) hy
  rw [← OpenPartialHomeomorph.extend_coe] at heu
  set D : TangentSpace I x →L[ℝ] E := mvfderiv I (e.extend I) x
  have hD : Function.Injective D := injective_mvfderiv_iff.2
    (isInvertible_mfderiv_extend (IsManifold.maximalAtlas_subset_of_le (by simp) he) hxe).injective
  -- A linear form `ℓ` vanishing on every `u_i = D (X_{F_i}(x))`, with `ℓ (D w) = 1`.
  set S := Submodule.span ℝ (range fun i ↦ σ.hamiltonianVectorField (F · i) x)
  have hDw : D w ∉ S.map D.toLinearMap := fun ⟨v, hv, hvw⟩ ↦ hw (hD hvw ▸ hv)
  obtain ⟨f, hfw, hfS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hDw inferInstance
  set ℓ : E →L[ℝ] ℝ := (f (D w))⁻¹ • LinearMap.toContinuousLinearMap f with hℓ
  have hℓ_apply (v : E) : ℓ v = (f (D w))⁻¹ * f v := by simp [hℓ]
  have hℓu (i : ι) : ℓ (u i) = 0 := by
    have h := Submodule.mem_map_of_mem (f := f) <| Submodule.mem_map_of_mem (f := D.toLinearMap)
      (Submodule.subset_span (mem_range_self i) : σ.hamiltonianVectorField (F · i) x ∈ S)
    rw [hfS, Submodule.mem_bot] at h
    rw [← heu x hxe i, ← mvfderiv_apply_eq_mfderiv_apply, hℓ_apply]
    exact mul_eq_zero_of_right _ h
  -- The function `g = ℓ ∘ e` near `x`, extended to a smooth function on `M`.
  obtain ⟨g, hg⟩ := ContMDiffOn.exists_contMDiffMap_eventuallyEq (n := ⊤)
    ((ℓ.contMDiff (n := ∞)).comp_contMDiffOn (e.contMDiffOn_extend he))
    (e.open_source.mem_nhds hxe)
  have hdg : ∀ᶠ y in 𝓝 x, ∀ v, mvfderiv I g y v = ℓ (mvfderiv I (e.extend I) y v) := by
    filter_upwards [hg.eventually_nhds, e.open_source.mem_nhds hxe] with y hy hye v
    rw [Filter.EventuallyEq.mvfderiv_eq (I := I) hy, ℓ.mvfderiv_comp_apply
      ((e.contMDiffAt_extend he hye).mdifferentiableAt (by simp))]
  refine ⟨g, g.contMDiff, fun i ↦ ?_, ?_⟩
  · filter_upwards [hdg, e.open_source.mem_nhds hxe] with y hy hye
    rw [poissonBracket_eq_neg_mvfderiv, hy, mvfderiv_apply_eq_mfderiv_apply, heu y hye i,
      hℓu i, neg_zero]
  · rw [hdg.self_of_nhds, hℓ_apply, inv_mul_cancel₀ hfw]

/-- **Extending an involutive family by one function.** On a symplectic manifold of dimension
`2n`, let `F₁, …, F_k` be smooth functions which pairwise Poisson-commute near `x` and have
independent differentials at `x`. If `k < n`, there is a smooth function `g` which Poisson-commutes
with every `F_i` near `x` and whose differential at `x` is independent of those of the `F_i`. -/
theorem exists_isRegularPoint_finSnoc {k : ℕ} {F : M → Fin k → ℝ}
    (hF : ContMDiff I 𝓘(ℝ, Fin k → ℝ) ∞ F)
    (hcomm : ∀ i j, σ.poissonBracket (F · i) (F · j) =ᶠ[𝓝 x] fun _ ↦ 0)
    (hreg : IsRegularPoint I 𝓘(ℝ, Fin k → ℝ) F x) (hk : 2 * k < finrank ℝ E) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ g ∧
      (∀ i, σ.poissonBracket (F · i) g =ᶠ[𝓝 x] fun _ ↦ 0) ∧
      IsRegularPoint I 𝓘(ℝ, Fin (k + 1) → ℝ)
        (fun y ↦ Fin.snoc (α := fun _ ↦ ℝ) (F y) (g y)) x := by
  obtain ⟨w, hwK, hwS⟩ := hσ.isNondegenerate.exists_mem_ker_mfderiv_notMem_span hreg
    (fun i j ↦ (hcomm i j).self_of_nhds) (by simpa using hk)
  obtain ⟨g, hg, hgF, hgw⟩ :=
    hσ.exists_poissonBracket_eventuallyEq_zero_mvfderiv_eq_one hF hcomm hreg hwS
  exact ⟨g, hg, hgF, hreg.finSnoc (hg.mdifferentiableAt (by simp)) hwK (hgw ▸ one_ne_zero)⟩

/-- **Extending an involutive family to `n` functions.** On a symplectic manifold `M`, let
`F₁, …, F_k` be smooth functions which pairwise Poisson-commute near `x` and have independent
differentials at `x`. Then for any `n` with `k ≤ n` and `2n ≤ dim M` they are the first `k` of `n`
smooth functions `G₁, …, G_n` which pairwise Poisson-commute near `x` and have independent
differentials at `x`. When `dim M = 2n` the hypothesis `k ≤ n` always holds
(`TauCeti.SmoothTwoForm.IsNondegenerate.two_mul_card_le_finrank`). -/
theorem exists_isRegularPoint_castLE {n k : ℕ} (hn : 2 * n ≤ finrank ℝ E) (hkn : k ≤ n)
    {F : M → Fin k → ℝ} (hF : ContMDiff I 𝓘(ℝ, Fin k → ℝ) ∞ F)
    (hcomm : ∀ i j, σ.poissonBracket (F · i) (F · j) =ᶠ[𝓝 x] fun _ ↦ 0)
    (hreg : IsRegularPoint I 𝓘(ℝ, Fin k → ℝ) F x) :
    ∃ G : M → Fin n → ℝ, ContMDiff I 𝓘(ℝ, Fin n → ℝ) ∞ G ∧
      (∀ i j, σ.poissonBracket (G · i) (G · j) =ᶠ[𝓝 x] fun _ ↦ 0) ∧
      IsRegularPoint I 𝓘(ℝ, Fin n → ℝ) G x ∧ ∀ i, (G · (Fin.castLE hkn i)) = (F · i) := by
  obtain ⟨d, hd⟩ : ∃ d, k + d = n := ⟨n - k, by omega⟩
  induction d generalizing k with
  | zero =>
    subst hd
    exact ⟨F, hF, hcomm, hreg, fun i ↦ rfl⟩
  | succ d ih =>
    -- Append one function `g`, then extend the `k + 1` functions by induction.
    obtain ⟨g, hg, hgF, hreg'⟩ := hσ.exists_isRegularPoint_finSnoc hF hcomm hreg (by omega)
    have hF' := hF.finSnoc (E' := fun _ ↦ ℝ) hg
    have hcomm' (i j : Fin (k + 1)) :
        σ.poissonBracket (fun y ↦ Fin.snoc (α := fun _ ↦ ℝ) (F y) (g y) i)
          (fun y ↦ Fin.snoc (α := fun _ ↦ ℝ) (F y) (g y) j) =ᶠ[𝓝 x] fun _ ↦ 0 := by
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact .of_forall fun y ↦ poissonBracket_self σ _ y
        | cast j =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          exact (hgF j).mono fun y hy ↦ by rw [← neg_poissonBracket, hy, neg_zero]
      | cast i =>
        induction j using Fin.lastCases with
        | last => simpa using hgF i
        | cast j => simpa using hcomm i j
    obtain ⟨G, hG, hGc, hGr, hGF⟩ := ih (by omega) hF' hcomm' hreg' (by omega)
    refine ⟨G, hG, hGc, hGr, fun i ↦ ?_⟩
    simpa using hGF i.castSucc

end IsSymplectic

end SmoothTwoForm

end TauCeti
