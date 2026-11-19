/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Flow
public import TauCeti.Geometry.Manifold.SmoothAmbientIsotopic.Basic
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Diffeotopy
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Velocity.Isotopy
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# The isotopy extension theorem

Let `F` be a smooth isotopy from `f₀` to `f₁`, a jointly smooth motion of a boundaryless manifold
`M` through smooth embeddings into a finite-dimensional boundaryless manifold `N`. On every compact
subset `A` of `M`, the motion is the restriction of a compactly supported diffeotopy of `N`
(`TauCeti.SmoothIsotopy.exists_diffeotopy_apply_eq`): there is a diffeotopy `Φ`, fixing every
point outside a compact set, with `Φ (t, f₀ x) = F (σ t, x)` for `x ∈ A`, where `σ` is the smooth
change of time `Real.smoothTransition`. In particular its final diffeomorphism carries `f₀` to `f₁`
on `A` (`TauCeti.SmoothIsotopy.exists_diffeotopy_final_apply_eq`). This is the isotopy extension
theorem of Hirsch, Chapter 8, Theorem 1.3, for compact parts of the source; the source itself need
not be compact. The diffeotopy can moreover be chosen to fix a closed set `C` which the moving part
of `A` never meets (`TauCeti.SmoothIsotopy.exists_diffeotopy_apply_eq_of_forall_notMem`): the
ambient velocity field is cut off by a smooth function equal to `1` on the motion of that part and
to `0` on `C`.

The proof integrates a velocity field. Run at the time `σ s`, the motion of `A` is stationary for
`s ≤ 0` and `s ≥ 1`, and `TauCeti.SmoothIsotopy.exists_ambientVelocityField` extends its velocity
to a time-dependent vector field `X` on `N` vanishing outside a fixed compact set `K`. Such a field
has a complete suspension (`TauCeti.isCompleteVectorField_timeDependentSuspensionField`), so its
time-dependent flow from time `0` is a diffeotopy (`TauCeti.timeDependentFlowDiffeotopy`), fixing
the complement of `K`. For `x ∈ A`, the curve `s ↦ F (σ s, x)` solves the time-dependent equation
of `X` and starts at `f₀ x`, so by uniqueness of solutions
(`TauCeti.timeDependentFlowOf_eq_of_hasMFDerivAt`) it is the flow line of `f₀ x`. The velocity
field loses one derivative: a `C^n` isotopy, `2 ≤ n`, gives a `C^m` diffeotopy for every `m` with
`1 ≤ m` and `m + 1 ≤ n`, and a smooth isotopy a smooth diffeotopy.

For a compact source, smooth isotopy and smooth ambient isotopy of smooth embeddings are therefore
the same relation (`TauCeti.smoothAmbientIsotopic_iff_smoothIsotopic`); the forward implication is
`TauCeti.SmoothAmbientIsotopic.smoothIsotopic`.

## Main results

* `TauCeti.SmoothIsotopy.exists_diffeotopy_apply_eq`: a smooth isotopy is, on a compact subset of
  its source, the restriction of a compactly supported diffeotopy, after the change of time
  `Real.smoothTransition`.
* `TauCeti.SmoothIsotopy.exists_diffeotopy_apply_eq_of_forall_notMem`: the same, with the
  diffeotopy fixing a closed set missed by the moving part of the compact subset.
* `TauCeti.SmoothIsotopy.exists_diffeotopy_final_apply_eq`: the final diffeomorphism of that
  diffeotopy carries the initial embedding to the final one on the compact subset.
* `TauCeti.SmoothIsotopic.smoothAmbientIsotopic`: smoothly isotopic smooth maps of a compact
  boundaryless manifold are smoothly ambient isotopic.
* `TauCeti.smoothAmbientIsotopic_iff_smoothIsotopic`: for smooth embeddings of a compact
  boundaryless manifold, smooth ambient isotopy is smooth isotopy.

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer (1976),
  Chapter 8, §1, Theorems 1.3 and 1.4.
-/

public section

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace TauCeti

variable {E E' H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  [I.Boundaryless] [J.Boundaryless] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]

/-- **Isotopy extension fixing a closed set.** Let `F` be a `C^n` isotopy through smooth embeddings
into a finite-dimensional boundaryless manifold, and `A`, `A₀` compact subsets of the source such
that `F` keeps fixed every point of `A` outside `A₀`. If the motion of `A₀` never
meets the closed set `C`, then the motion of `A` is the restriction of a `C^m` diffeotopy `Φ` of
the target fixing every point of `C` and every point outside a compact set, for `1 ≤ m` and
`m + 1 ≤ n`: `Φ (t, f₀ x) = F (σ t, x)` for `x ∈ A`, where `σ` is the change of time
`Real.smoothTransition`, and `Φ (t, y) = y` for `y ∈ C`.

This is how isotopy extension leaves alone a part of the target that the isotopy does not move,
such as the rest of a line along which an arc is straightened. -/
theorem SmoothIsotopy.exists_diffeotopy_apply_eq_of_forall_notMem {n m : ℕ∞} [IsManifold I n M]
    {f₀ f₁ : C^n⟮I, M; J, N⟯} (F : SmoothIsotopy f₀ f₁) {A₀ A : Set M} {C : Set N}
    (hA₀ : IsCompact A₀) (hA : IsCompact A) (hC : IsClosed C)
    (hA₀C : ∀ t, ∀ x ∈ A₀, F (t, x) ∉ C) (hstat : ∀ t, ∀ x ∈ A, x ∉ A₀ → F (t, x) = f₀ x)
    (hm : 1 ≤ m) (hmn : m + 1 ≤ n) :
    ∃ Φ : Diffeotopy J m N, ∃ K : Set N, IsCompact K ∧ (∀ t, ∀ y ∉ K, Φ (t, y) = y) ∧
      (∀ t, ∀ x ∈ A, Φ (t, f₀ x) = F (⟨Real.smoothTransition t, Real.smoothTransition.nonneg _,
        Real.smoothTransition.le_one _⟩, x)) ∧ ∀ t, ∀ y ∈ C, Φ (t, y) = y := by
  let σ : ℝ → unitInterval := fun s =>
    ⟨Real.smoothTransition s, Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  obtain ⟨X, K, hK, hXK, hX, hvel⟩ := F.exists_ambientVelocityField hA hm hmn
  -- A cutoff equal to `1` on the motion of `A₀` and to `0` on `C`.
  have hT : IsCompact ((fun p : unitInterval × M => F p) '' (univ ×ˢ A₀)) :=
    (isCompact_univ.prod hA₀).image F.contMDiff.continuous
  obtain ⟨ρ, hρC, hρT, -⟩ := exists_contMDiffMap_zero_one_of_isClosed J (n := m) hC hT.isClosed
    (by
      rw [Set.disjoint_right]
      rintro _ ⟨⟨t, x⟩, ⟨-, hx⟩, rfl⟩
      exact hA₀C t x hx)
  let Y : ℝ → (y : N) → TangentSpace J y := fun u y => ρ y • X u y
  have hYK : ∀ u, ∀ y ∉ K, Y u y = 0 := fun u y hy => by simp only [Y, hXK u y hy, smul_zero]
  have hY : ContMDiff (𝓘(ℝ, ℝ).prod J) J.tangent m
      (fun p : ℝ × N => (⟨p.2, Y p.1 p.2⟩ : TangentBundle J N)) :=
    (ρ.contMDiff.comp contMDiff_snd).smul_totalSpace hX
  -- Along the motion of `A`, the cut-off field is the velocity field: on the motion of `A₀` the
  -- cutoff is `1`, and the other points of `A` are stationary, where both fields vanish.
  have hYX : ∀ t, ∀ x ∈ A, Y t (F (σ t, x)) = X t (F (σ t, x)) := by
    intro t x hx
    by_cases hx₀ : x ∈ A₀
    · simp only [Y, hρT ⟨(σ t, x), ⟨mem_univ _, hx₀⟩, rfl⟩, Pi.one_apply, one_smul]
    · have hconst : (fun s => F (σ s, x)) = fun _ => f₀ x := funext fun s => hstat _ x hx hx₀
      have h0 : (1 : ℝ →L[ℝ] ℝ).smulRight (X t (F (σ t, x))) = 0 := by
        have h := (hvel t x hx).mfderiv
        rw [hconst, mfderiv_const] at h
        exact h.symm
      have hX0 : X t (F (σ t, x)) = 0 := by
        simpa using congrArg (fun L : ℝ →L[ℝ] TangentSpace J (F (σ t, x)) => L 1) h0
      simp only [Y, hX0, smul_zero]
  have hvelY : ∀ t, ∀ x ∈ A, HasMFDerivAt 𝓘(ℝ, ℝ) J (fun s => F (σ s, x)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (F (σ t, x)))) := fun t x hx => by
    rw [hYX t x hx]
    exact hvel t x hx
  have hY₁ := hY.of_le (m := 1) (by exact_mod_cast hm)
  have hcomplete := isCompleteVectorField_timeDependentSuspensionField hY₁ hK hYK
  refine ⟨timeDependentFlowDiffeotopy hm hY hcomplete, K, hK,
    fun t y hy => timeDependentFlowDiffeotopy_apply_of_forall_eq_zero hm hY hcomplete
      (fun u => hYK u y hy) t, fun t x hx => ?_, fun t y hy =>
    timeDependentFlowDiffeotopy_apply_of_forall_eq_zero hm hY hcomplete
      (fun u => by simp only [Y, hρC hy, Pi.zero_apply, zero_smul]) t⟩
  -- The curve `s ↦ F (σ s, x)` solves the time-dependent equation and starts at `f₀ x`.
  have h₀ : σ 0 = 0 := Subtype.ext Real.smoothTransition.zero
  have hsol := timeDependentFlowOf_eq_of_hasMFDerivAt hY₁ (a := -1) (b := 2) (s := 0) (t := t)
    (fun u _ => hvelY u x hx) ⟨by norm_num, by norm_num⟩ ⟨by linarith [t.2.1], by linarith [t.2.2]⟩
  rw [h₀, F.apply_zero] at hsol
  rw [timeDependentFlowDiffeotopy_apply]
  exact hsol

/-- **Isotopy extension on a compact subset.** A `C^n` isotopy `F` of a boundaryless manifold
through smooth embeddings into a finite-dimensional boundaryless manifold is, on any compact subset
`A` of the source, the restriction of a `C^m` diffeotopy `Φ` of the target fixing every point
outside a compact set, for `1 ≤ m` and `m + 1 ≤ n`: `Φ (t, f₀ x) = F (σ t, x)` for `x ∈ A`, where
`σ t = Real.smoothTransition t`. The source need not be compact. -/
theorem SmoothIsotopy.exists_diffeotopy_apply_eq {n m : ℕ∞} [IsManifold I n M]
    {f₀ f₁ : C^n⟮I, M; J, N⟯} (F : SmoothIsotopy f₀ f₁) {A : Set M} (hA : IsCompact A)
    (hm : 1 ≤ m) (hmn : m + 1 ≤ n) :
    ∃ Φ : Diffeotopy J m N, ∃ K : Set N, IsCompact K ∧ (∀ t, ∀ y ∉ K, Φ (t, y) = y) ∧
      ∀ t, ∀ x ∈ A, Φ (t, f₀ x) = F (⟨Real.smoothTransition t, Real.smoothTransition.nonneg _,
        Real.smoothTransition.le_one _⟩, x) := by
  obtain ⟨Φ, K, hK, hΦK, hΦ, -⟩ := F.exists_diffeotopy_apply_eq_of_forall_notMem (A₀ := A)
    (C := ∅) hA hA isClosed_empty (fun _ _ _ => notMem_empty _)
    (fun _ _ hx hx' => (hx' hx).elim) hm hmn
  exact ⟨Φ, K, hK, hΦK, hΦ⟩

/-- **Isotopy extension on a compact subset, final form.** The final diffeomorphism of a compactly
supported `C^m` diffeotopy carries the initial embedding `f₀` of a `C^n` isotopy to the final one
`f₁` on any compact subset of the source, for `1 ≤ m` and `m + 1 ≤ n`. -/
theorem SmoothIsotopy.exists_diffeotopy_final_apply_eq {n m : ℕ∞} [IsManifold I n M]
    {f₀ f₁ : C^n⟮I, M; J, N⟯} (F : SmoothIsotopy f₀ f₁) {A : Set M} (hA : IsCompact A)
    (hm : 1 ≤ m) (hmn : m + 1 ≤ n) :
    ∃ Φ : Diffeotopy J m N, ∃ K : Set N, IsCompact K ∧ (∀ t, ∀ y ∉ K, Φ (t, y) = y) ∧
      ∀ x ∈ A, Φ.final (f₀ x) = f₁ x := by
  obtain ⟨Φ, K, hK, hΦK, hΦ⟩ := F.exists_diffeotopy_apply_eq hA hm hmn
  refine ⟨Φ, K, hK, hΦK, fun x hx => ?_⟩
  have h₁ : (⟨Real.smoothTransition ((1 : unitInterval) : ℝ), Real.smoothTransition.nonneg _,
      Real.smoothTransition.le_one _⟩ : unitInterval) = 1 :=
    Subtype.ext (by simp)
  rw [Diffeotopy.final_apply, hΦ 1 x hx, h₁, F.apply_one]

/-- **Smooth isotopy implies smooth ambient isotopy for a compact source.** Smoothly isotopic smooth
maps of a compact boundaryless manifold into a finite-dimensional boundaryless manifold are
smoothly ambient isotopic. -/
theorem SmoothIsotopic.smoothAmbientIsotopic [CompactSpace M] [IsManifold I ∞ M]
    {f₀ f₁ : C^∞⟮I, M; J, N⟯} (h : SmoothIsotopic f₀ f₁) : SmoothAmbientIsotopic f₀ f₁ := by
  obtain ⟨F⟩ := smoothIsotopic_def.mp h
  obtain ⟨Φ, -, -, -, hΦ⟩ := F.exists_diffeotopy_final_apply_eq (m := ⊤) isCompact_univ
    le_top le_top
  exact .of_diffeotopy Φ (ContMDiffMap.ext fun x => hΦ x (mem_univ x))

/-- **Smooth ambient isotopy is smooth isotopy for a compact source.** A smooth embedding `f₀` of a
compact boundaryless manifold into a finite-dimensional boundaryless manifold is smoothly ambient
isotopic to a smooth map `f₁` exactly when it is smoothly isotopic to it. -/
theorem smoothAmbientIsotopic_iff_smoothIsotopic [CompactSpace M] [IsManifold I ∞ M]
    {f₀ f₁ : C^∞⟮I, M; J, N⟯} (hf₀ : IsSmoothEmbedding I J ∞ f₀) :
    SmoothAmbientIsotopic f₀ f₁ ↔ SmoothIsotopic f₀ f₁ :=
  ⟨fun h => h.smoothIsotopic hf₀, SmoothIsotopic.smoothAmbientIsotopic⟩

end TauCeti
