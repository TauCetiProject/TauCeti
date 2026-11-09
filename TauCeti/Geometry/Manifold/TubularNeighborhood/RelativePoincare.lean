/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Relative
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Existence

/-!
# The relative Poincaré lemma near an embedded submanifold

Let `f : M → N` be a smooth embedding of finite-dimensional boundaryless manifolds, with `N`
Hausdorff and second countable, and let `O` be an open neighbourhood of its image. This file
proves that `O` contains an open neighbourhood `W` of the image of `f` on which every closed form
of positive degree that restricts to zero along `f` is exact, with a primitive vanishing along
the image of `f` as a full ambient tensor
(`TauCeti.SmoothEmbedding.exists_isSmoothForm_relative_primitive`). The ambient form `η` itself
need not vanish along the image of `f`, only its pullback `f^* η` does. The neighbourhood `W`
is chosen before the form, so it serves every form of every degree at once.

The neighbourhood `W` is a tubular neighbourhood: by the tubular neighbourhood theorem
(`TauCeti.SmoothEmbedding.exists_diffeomorph_normalBundle_subset`) it is the image of a
diffeomorphism from the total space of the normal bundle of `f`, sending the zero section to
`f`. The primitive is transported from the fibre-scaling primitive on that total space
(`Diffeomorph.exists_isSmoothForm_relative_primitive`). Neither compactness nor closedness of the
image of `f` is needed.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, §6.2 (the relative Poincaré lemma).
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
-/

public section

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

variable {E V H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N] [SecondCountableTopology N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **The relative Poincaré lemma near an embedded submanifold.** Every open neighbourhood `O` of
the image of a smooth embedding `f : M → N` contains an open neighbourhood `W` of that image with
the following property. Every closed `C^r` form `η` of positive degree on `N`, with `1 ≤ r` and
`f^* η = 0`, restricts on `W` to the exterior derivative of a `C^r` form `β` that vanishes at
every point of the image of `f` as a full ambient tensor. -/
theorem exists_isSmoothForm_relative_primitive (f : SmoothEmbedding I J ∞ M N) {O : Set N}
    (hO : IsOpen O) (hfO : range f ⊆ O) :
    ∃ W : TopologicalSpace.Opens N, (W : Set N) ⊆ O ∧ ∃ hfW : range f ⊆ W,
      ∀ {k : ℕ} {r : ℕ∞}, 1 ≤ r → ∀ {η : RoughForm J N F (k + 1)}, IsSmoothForm J r η →
        mextDeriv η = 0 → mpullback I J f η = 0 →
        ∃ β : RoughForm J W F k, IsSmoothForm J r β ∧
          mextDeriv β = mpullback J J (Subtype.val : W → N) η ∧
          ∀ x, β ⟨f x, hfW (mem_range_self x)⟩ = 0 := by
  let P := EuclideanSpace ℝ (Fin (Module.finrank ℝ V - Module.finrank ℝ E))
  have hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E := by simp [P]
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  obtain ⟨W, hWO, Φ, hΦ⟩ := f.exists_diffeomorph_normalBundle_subset (P := P) hdim hO hfO
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  have : IsManifold I ((∞ : ℕ∞ω) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold J ((∞ : ℕ∞ω) + 1) N := IsManifold.of_le (n := ∞) (by simp)
  have := f.normalSpaceContMDiffVectorBundle (m := ∞) hn (by simp) hdim
  have hfW : range f ⊆ W := by
    rintro _ ⟨x, rfl⟩
    rw [← hΦ x]
    exact (Φ _).2
  refine ⟨W, hWO, hfW, fun {k r} hr {η} hη hclosed hi ↦ ?_⟩
  have hval : ContMDiff J J ∞ (Subtype.val : W → N) := contMDiff_subtype_val
  have hr' : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
  have hηW : IsSmoothForm J r (mpullback J J (Subtype.val : W → N) η) :=
    hη.mpullback (hval.of_le (by exact_mod_cast (le_top : r + 1 ≤ ⊤)))
  have hclosedW : mextDeriv (mpullback J J (Subtype.val : W → N) η) = 0 :=
    (hη.of_le hr').mextDeriv_mpullback_eq_zero hclosed (hval.of_le (by simp))
  have hcomp : (Subtype.val : W → N) ∘ (Φ ∘ zeroSection P fun x ↦ f.NormalSpace x hn) = f :=
    funext hΦ
  have hiW : mpullback I J (Φ ∘ zeroSection P fun x ↦ f.NormalSpace x hn)
      (mpullback J J (Subtype.val : W → N) η) = 0 := by
    rw [← mpullback_comp ((Φ.contMDiff.comp (contMDiff_zeroSection ℝ _)).mdifferentiable
      (by simp)) (hval.mdifferentiable (by simp)), hcomp, hi]
  obtain ⟨β, hβ, hdβ, hβ₀⟩ := Φ.exists_isSmoothForm_relative_primitive hr hηW hclosedW hiW
  refine ⟨β, hβ, hdβ, fun x ↦ ?_⟩
  rw [show (⟨f x, hfW (mem_range_self x)⟩ : W) = Φ (zeroSection P _ x) from
    Subtype.ext (hΦ x).symm]
  exact hβ₀ x

end TauCeti.SmoothEmbedding
