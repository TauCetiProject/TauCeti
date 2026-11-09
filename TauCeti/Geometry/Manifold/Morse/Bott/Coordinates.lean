/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic

/-!
# The normal Hessian in normal-bundle coordinates

Let `i : S → M` be a critical submanifold of a function `f` on a boundaryless manifold. Its normal
Hessian `TauCeti.SmoothEmbedding.IsCriticalSubmanifold.normalHessian` is a symmetric bilinear form
on each normal space `TangentSpace I (i s) ⧸ range (mfderiv J I i s)`, the fibre of the normal
bundle of `i` (`TauCeti.SmoothEmbedding.normalSpaceFiberBundle`). This file shows that these forms
make up a `C^k` family of bilinear forms on the normal bundle when `f` is `C^{k+2}` along the
submanifold: read in the local trivializations of the normal bundle, the normal Hessian is a
`C^k` map into the symmetric bilinear forms on the fibre model `P`. For a Morse–Bott submanifold
these forms are moreover nondegenerate.

The computation is explicit. The inverse normal coordinates at `s₀` send `w : P` to the normal
class of the ambient tangent vector whose coordinates in the tangent chart at `i s₀` are `B w`,
for a fixed linear map `B : P →L[ℝ] E`
(`TauCeti.SmoothEmbedding.exists_normalSpaceTrivialization_symm_apply`). At a critical point the
critical Hessian, evaluated on vectors given by their coordinates in the tangent chart at `i s₀`,
is the second derivative of the coordinate expression of `f` in the extended chart at `i s₀`
(`TauCeti.criticalHessian_trivializationAt_symm_apply`). So, with `φ = extChartAt I (i s₀)`, the
normal Hessian at `s` in these coordinates is

`(u, v) ↦ D²(f ∘ φ⁻¹)(φ (i s)) (B u, B v)`,

which is `C^k` in `s` because `f ∘ φ⁻¹` is `C^{k+2}` and `i` is `C^k`.

This is the regularity needed to split the normal bundle of a Morse–Bott submanifold into its
positive and negative normal subbundles, by smooth spectral projections of the normal Hessian.

## Main results

In the namespace `TauCeti.SmoothEmbedding`:

* `IsCriticalSubmanifold.normalHessian_normalClass_trivializationAt_symm`: the normal Hessian on
  normal classes of vectors given in a tangent chart.
* `IsCriticalSubmanifold.exists_contMDiffOn_normalHessian_normalSpaceTrivialization`: in each
  normal-bundle trivialization, the normal Hessian is a `C^k` family of symmetric bilinear forms
  on the fibre model.
* `IsNondegenerateCriticalSubmanifold.exists_contMDiffOn_normalHessian_normalSpaceTrivialization`:
  for a Morse–Bott submanifold these bilinear forms are nondegenerate.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* A. Banyaga and D. E. Hurtubise, *A proof of the Morse–Bott lemma*, Expositiones Mathematicae 22
  (2004), 365–373.
-/

public section

open Bundle Function Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.SmoothEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)

namespace IsCriticalSubmanifold

/-- **The normal Hessian in a tangent chart.** At a point `i s` of a critical submanifold in the
source of the preferred chart at `i s₀`, the normal Hessian, evaluated on the normal classes of the
tangent vectors with coordinates `a` and `b` in the tangent-bundle trivialization at `i s₀`, is the
second derivative at `i s` of the coordinate expression of `f` in the extended chart at `i s₀`,
applied to `a` and `b`. -/
theorem normalHessian_normalClass_trivializationAt_symm [I.Boundaryless] [IsManifold I 2 M]
    (h : i.IsCriticalSubmanifold f) {s₀ s : S} (hs : i s ∈ (chartAt H (i s₀)).source) (a b : E) :
    h.normalHessian hn s
        (i.normalClass s hn ((trivializationAt E (TangentSpace I) (i s₀)).symm (i s) a))
        (i.normalClass s hn ((trivializationAt E (TangentSpace I) (i s₀)).symm (i s) b)) =
      fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I (i s₀)).symm)) (extChartAt I (i s₀) (i s)) a b := by
  rw [normalHessian_normalClass, criticalHessian_trivializationAt_symm_apply hs (h.contMDiffAt s)
    (TauCeti.mem_criticalPoints.mp (h.mem_criticalPoints s))]

variable [I.Boundaryless] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold J 1 S]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- **The normal Hessian is a `C^k` family of bilinear forms on the normal bundle.** Let `i` be a
critical submanifold of `f`, with `f` of class `C^{k+2}` at every point of the submanifold and
`k ≤ n`. In the preferred normal-bundle trivialization at any point `s₀`, with fibre model `P`,
the normal Hessian is given over the base set of the trivialization by a family of symmetric
continuous bilinear forms on `P` which is `C^k` on the base set. -/
theorem exists_contMDiffOn_normalHessian_normalSpaceTrivialization {k : ℕ∞ω}
    [IsManifold I (k + 2) M] (h : i.IsCriticalSubmanifold f) (hk : k ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E') (s₀ : S) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    ∃ Q : S → P →L[ℝ] P →L[ℝ] ℝ,
      ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P →L[ℝ] ℝ) k Q
        (i.normalSpaceTrivialization hn hdim s₀).baseSet ∧
      ∀ s ∈ (i.normalSpaceTrivialization hn hdim s₀).baseSet, ∀ u v : P,
        h.normalHessian hn s ((i.normalSpaceTrivialization hn hdim s₀).symm s u)
            ((i.normalSpaceTrivialization hn hdim s₀).symm s v) = Q s u v ∧
          Q s u v = Q s v u := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I k M := .of_le (n := k + 2) le_self_add
  obtain ⟨B, hsub, hsymm⟩ := i.exists_normalSpaceTrivialization_symm_apply hn hdim s₀
  set φ := extChartAt I (i s₀)
  -- The bilinear forms `D²(f ∘ φ⁻¹)(φ (i s))`, restricted to the image of `B` in both slots.
  set D : S → E →L[ℝ] E →L[ℝ] ℝ := fun s ↦ fderiv ℝ (fderiv ℝ (f ∘ φ.symm)) (φ (i s))
  set R : (E →L[ℝ] ℝ) →L[ℝ] P →L[ℝ] ℝ := (ContinuousLinearMap.compL ℝ P E ℝ).flip B
  have hQ (s : S) (u v : P) : ((R ∘L D s) ∘L B) u v = D s (B u) (B v) := by simp [R]
  have heq {s : S} (hs : s ∈ (i.normalSpaceTrivialization hn hdim s₀).baseSet) (u v : P) :
      h.normalHessian hn s ((i.normalSpaceTrivialization hn hdim s₀).symm s u)
        ((i.normalSpaceTrivialization hn hdim s₀).symm s v) = ((R ∘L D s) ∘L B) u v := by
    rw [hQ, hsymm s hs, hsymm s hs,
      normalHessian_normalClass_trivializationAt_symm hn h (hsub hs).2]
  refine ⟨fun s ↦ (R ∘L D s) ∘L B, fun s hs ↦ ?_, fun s hs u v ↦ ⟨heq hs u v, ?_⟩⟩
  · have hy : i s ∈ (chartAt H (i s₀)).source := (hsub hs).2
    -- The coordinate expression of `f` is `C^{k+2}` near `φ (i s)`, so its second derivative is
    -- `C^k` there, and `s ↦ φ (i s)` is `C^k`.
    have hg : ContDiffAt ℝ (k + 1 + 1) (f ∘ φ.symm) (φ (i s)) := by
      rw [add_assoc, one_add_one_eq_two]
      exact (contMDiffAt_iff_contDiffAt_comp_extend_symm
        (IsManifold.chart_mem_maximalAtlas (i s₀)) hy).mp (hf s)
    have hφi : ContMDiffAt J 𝓘(ℝ, E) k (fun s ↦ φ (i s)) s :=
      (contMDiffAt_extChartAt' hy).comp s ((i.contMDiff s).of_le hk)
    have hD : ContMDiffAt J 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) k D s :=
      hg.fderiv_right_succ.fderiv_right_succ.comp_contMDiffAt (f := fun s ↦ φ (i s)) hφi
    exact ((contMDiffAt_const.clm_comp hD).clm_comp contMDiffAt_const).contMDiffWithinAt
  · rw [← heq hs, ← heq hs, (h.isSymm_normalHessian hn s).eq]

end IsCriticalSubmanifold

namespace IsNondegenerateCriticalSubmanifold

variable [I.Boundaryless] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold J 1 S]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- **The normal Hessian of a Morse–Bott submanifold is a `C^k` family of nondegenerate bilinear
forms on the normal bundle.** Let `i` be a nondegenerate critical submanifold of `f`, with `f` of
class `C^{k+2}` at every point of the submanifold and `k ≤ n`. In the preferred normal-bundle
trivialization at any point `s₀`, with fibre model `P`, the normal Hessian is given over the base
set of the trivialization by a family of symmetric nondegenerate continuous bilinear forms on `P`
which is `C^k` on the base set. -/
theorem exists_contMDiffOn_normalHessian_normalSpaceTrivialization {k : ℕ∞ω}
    [IsManifold I (k + 2) M] (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E') (s₀ : S) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    ∃ Q : S → P →L[ℝ] P →L[ℝ] ℝ,
      ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P →L[ℝ] ℝ) k Q
        (i.normalSpaceTrivialization hn hdim s₀).baseSet ∧
      ∀ s ∈ (i.normalSpaceTrivialization hn hdim s₀).baseSet,
        (∀ u v : P, h.normalHessian hn s ((i.normalSpaceTrivialization hn hdim s₀).symm s u)
            ((i.normalSpaceTrivialization hn hdim s₀).symm s v) = Q s u v ∧
          Q s u v = Q s v u) ∧
        Injective (Q s) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  obtain ⟨Q, hQ, hrep⟩ :=
    h.toIsCriticalSubmanifold.exists_contMDiffOn_normalHessian_normalSpaceTrivialization hn hk hf
      hdim s₀
  refine ⟨Q, hQ, fun s hs ↦ ⟨hrep s hs, fun u u' huu' ↦ ?_⟩⟩
  set e := i.normalSpaceTrivialization hn hdim s₀
  -- Over the base set, the inverse trivialization is a linear equivalence onto the normal space.
  let L := (e.linearEquivAt ℝ s hs).symm
  -- The difference `u - u'` pairs to zero with every normal vector, so it is zero.
  have hker : L (u - u') ∈ LinearMap.ker (h.normalHessian hn s) := by
    rw [LinearMap.mem_ker]
    ext p
    obtain ⟨v, rfl⟩ := L.surjective p
    rw [map_sub, LinearMap.map_sub₂, LinearMap.zero_apply]
    simp only [L, Trivialization.linearEquivAt_symm_apply]
    rw [(hrep s hs u v).1, (hrep s hs u' v).1, huu', sub_self]
  rw [h.ker_normalHessian hn s, Submodule.mem_bot, map_eq_zero_iff _ L.injective,
    sub_eq_zero] at hker
  exact hker

end IsNondegenerateCriticalSubmanifold

end TauCeti.SmoothEmbedding
