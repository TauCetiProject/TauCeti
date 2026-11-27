/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Relative.Family
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Existence
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family

/-!
# The relative Poincaré lemma near an embedded submanifold

Let `f : M → N` be a smooth embedding of finite-dimensional boundaryless manifolds, with `N`
Hausdorff and second countable, and let `O` be an open neighbourhood of its image. This file
proves that `O` contains an open neighbourhood `W` of the image of `f` with the following
property. Every closed `C^r` form `η` of positive degree on `N`, with `r ≥ 1`, that restricts to
zero along `f` becomes exact on restriction to `W`, with a `C^r` primitive vanishing along the
image of `f` as a full ambient tensor
(`TauCeti.SmoothEmbedding.exists_isSmoothForm_relative_primitive`). The ambient form `η` itself
need not vanish along the image of `f`, only its pullback `f^* η` does; at the points of the
image where `η` does vanish as a full ambient tensor, the primitive moreover has zero first jet.
The neighbourhood `W` is chosen before the form, so it serves every such form of every degree at
once.

The neighbourhood `W` is a tubular neighbourhood: by the tubular neighbourhood theorem
(`TauCeti.SmoothEmbedding.exists_diffeomorph_normalBundle_subset`) it is the image of a
diffeomorphism from the total space of the normal bundle of `f`, sending the zero section to
`f`. The primitive is transported from the fibre-scaling primitive on that total space
(`Diffeomorph.exists_isSmoothForm_relative_primitive`). Neither compactness nor closedness of the
image of `f` is needed.

The same neighbourhood construction gives the relative Poincaré lemma for families
(`TauCeti.SmoothEmbedding.exists_isSmoothForm_family_relative_primitive`): for a form `η` on
`P × N` whose slices `η_p` are closed and restrict to zero along `f`, the slices of the
restriction of `η` to `P × W` have primitives that depend jointly `C^r` on the parameter, given by
the family version on a tube (`Diffeomorph.exists_isSmoothForm_family_relative_primitive`).

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, §6.2 (the relative Poincaré lemma).
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
-/

universe uV

public section

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

variable {E : Type*} {V : Type uV} {H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N] [SecondCountableTopology N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- **Tubular neighbourhoods, in elimination form.** Every open neighbourhood `O` of the image of a
smooth embedding `f : M → N` contains an open neighbourhood `W` of that image that is the image of
a smooth diffeomorphism `Φ` from the total space of a smooth vector bundle over `M`, sending the
zero section to `f`. To prove a property of such a `W`, it suffices to prove it from `Φ`, with the
bundle instances in place, from the identification of each point `f x` of `W` with `Φ (0_x)`, and
from the identity `(Φ ∘ 0)^* (η|_W) = f^* η` for forms `η` on `N`. -/
private theorem exists_tube (f : SmoothEmbedding I J ∞ M N) {O : Set N} (hO : IsOpen O)
    (hfO : range f ⊆ O) {motive : (W : TopologicalSpace.Opens N) → range f ⊆ W → Prop}
    (h : ∀ (W : TopologicalSpace.Opens N) (hfW : range f ⊆ W) {FV : Type} {ν : M → Type uV}
      [∀ x, AddCommGroup (ν x)] [∀ x, Module ℝ (ν x)] [NormedAddCommGroup FV]
      [NormedSpace ℝ FV] [∀ x, TopologicalSpace (ν x)] [TopologicalSpace (TotalSpace FV ν)]
      [FiberBundle FV ν] [VectorBundle ℝ FV ν] [ContMDiffVectorBundle ∞ FV ν I]
      (Φ : TotalSpace FV ν ≃ₘ^∞⟮I.prod 𝓘(ℝ, FV), J⟯ W),
      (∀ x, (⟨f x, hfW (mem_range_self x)⟩ : W) = Φ (zeroSection FV ν x)) →
      (∀ {k : ℕ} (η : RoughForm J N F k), mpullback I J (Φ ∘ zeroSection FV ν)
        (mpullback J J (Subtype.val : W → N) η) = mpullback I J f η) →
      motive W hfW) :
    ∃ W : TopologicalSpace.Opens N, (W : Set N) ⊆ O ∧ ∃ hfW : range f ⊆ W, motive W hfW := by
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
    exact (Φ _).property
  have hcomp : (Subtype.val : W → N) ∘ (Φ ∘ zeroSection P fun x ↦ f.isImmersion.NormalSpace x hn) =
      f :=
    funext hΦ
  refine ⟨W, hWO, hfW, h W hfW Φ (fun x ↦ Subtype.ext (hΦ x).symm) fun η ↦ ?_⟩
  rw [← mpullback_comp ((Φ.contMDiff.comp (contMDiff_zeroSection ℝ _)).mdifferentiable (by simp))
    ((contMDiff_subtypeVal (n := 1)).mdifferentiable one_ne_zero), hcomp]

/-- **The relative Poincaré lemma near an embedded submanifold.** Every open neighbourhood `O` of
the image of a smooth embedding `f : M → N` contains an open neighbourhood `W` of that image with
the following property. Every closed `C^r` form `η` of positive degree on `N`, with `1 ≤ r` and
`f^* η = 0`, restricts on `W` to the exterior derivative of a `C^r` form `β` that vanishes at
every point of the image of `f` as a full ambient tensor. At every point `f x` where `η` itself
vanishes as a full ambient tensor, `β` moreover has zero first jet: its coordinate expression in
the chart at `f x` has zero derivative at the chart point of `f x`. -/
theorem exists_isSmoothForm_relative_primitive (f : SmoothEmbedding I J ∞ M N) {O : Set N}
    (hO : IsOpen O) (hfO : range f ⊆ O) :
    ∃ W : TopologicalSpace.Opens N, (W : Set N) ⊆ O ∧ ∃ hfW : range f ⊆ W,
      ∀ {k : ℕ} {r : ℕ∞}, 1 ≤ r → ∀ {η : RoughForm J N F (k + 1)}, IsSmoothForm J r η →
        mextDeriv η = 0 → mpullback I J f η = 0 →
        ∃ β : RoughForm J W F k, IsSmoothForm J r β ∧
          mextDeriv β = mpullback J J (Subtype.val : W → N) η ∧
          (∀ x, β ⟨f x, hfW (mem_range_self x)⟩ = 0) ∧
          ∀ x, η (f x) = 0 →
            HasFDerivAt (β.inChartAt ⟨f x, hfW (mem_range_self x)⟩)
              (0 : V →L[ℝ] V [⋀^Fin k]→L[ℝ] F)
              (extChartAt J (⟨f x, hfW (mem_range_self x)⟩ : W) ⟨f x, hfW (mem_range_self x)⟩) := by
  refine f.exists_tube (F := F) hO hfO ?_
  intro W hfW FV ν _ _ _ _ _ _ _ _ _ Φ hx hpull k r hr η hη hclosed hi
  have hval : ContMDiff J J ∞ (Subtype.val : W → N) := contMDiff_subtypeVal
  have hr' : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
  have hηW : IsSmoothForm J r (mpullback J J (Subtype.val : W → N) η) :=
    hη.mpullback (hval.of_le (by exact_mod_cast (le_top : r + 1 ≤ ⊤)))
  have hclosedW : mextDeriv (mpullback J J (Subtype.val : W → N) η) = 0 :=
    (hη.of_le hr').mextDeriv_mpullback_eq_zero hclosed (hval.of_le (by simp))
  obtain ⟨β, hβ, hdβ, hβ₀, hβ₁⟩ := Φ.exists_isSmoothForm_relative_primitive hr
    (by exact_mod_cast (le_top : r + 1 ≤ ⊤)) hηW hclosedW (by rw [hpull, hi])
  refine ⟨β, hβ, hdβ, fun x ↦ ?_, fun x hηx ↦ ?_⟩
  · rw [hx]
    exact hβ₀ x
  · have h := hβ₁ x (by rw [← hx]; exact mpullback_apply_eq_zero hηx)
    rw [ModelWithCorners.range_eq_univ, hasFDerivWithinAt_univ, ← hx] at h
    exact h

variable {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP ∞ P]

/-- **The relative Poincaré lemma for families near an embedded submanifold.** Every open
neighbourhood `O` of the image of a smooth embedding `f : M → N` contains an open neighbourhood
`W` of that image with the following property. Let `η` be a `C^r` form of positive degree on
`P × N`, with `1 ≤ r`, whose slices `η_p = ι_p^* η` are closed and satisfy `f^* η_p = 0`. Then
its restriction to `P × W` has a `C^r` form `β` on `P × W` whose slices are primitives of the
slices of that restriction, `d β_p = η_p|_W`, and which vanishes as a full ambient tensor of
`P × W` at every point `(p, f x)`. The neighbourhood `W` does not depend on the family. -/
theorem exists_isSmoothForm_family_relative_primitive (f : SmoothEmbedding I J ∞ M N) {O : Set N}
    (hO : IsOpen O) (hfO : range f ⊆ O) :
    ∃ W : TopologicalSpace.Opens N, (W : Set N) ⊆ O ∧ ∃ hfW : range f ⊆ W,
      ∀ {k : ℕ} {r : ℕ∞}, 1 ≤ r → ∀ {η : RoughForm (IP.prod J) (P × N) F (k + 1)},
        IsSmoothForm (IP.prod J) r η →
        (∀ p, mextDeriv (mpullback J (IP.prod J) (Prod.mk p) η) = 0) →
        (∀ p, mpullback I J f (mpullback J (IP.prod J) (Prod.mk p) η) = 0) →
        ∃ β : RoughForm (IP.prod J) (P × W) F k, IsSmoothForm (IP.prod J) r β ∧
          (∀ p, mextDeriv (mpullback J (IP.prod J) (Prod.mk p) β) =
            mpullback J J (Subtype.val : W → N) (mpullback J (IP.prod J) (Prod.mk p) η)) ∧
          ∀ p x, β (p, ⟨f x, hfW (mem_range_self x)⟩) = 0 := by
  refine f.exists_tube (F := F) hO hfO ?_
  intro W hfW FV ν _ _ _ _ _ _ _ _ _ Φ hx hpull k r hr η hη hclosed hi
  have hv : MDifferentiable J J (Subtype.val : W → N) :=
    (contMDiff_subtypeVal (n := 1)).mdifferentiable one_ne_zero
  -- Restrict the family to `P × W`; its slices are the restrictions of the slices of `η`.
  have hval : ContMDiff (IP.prod J) (IP.prod J) ∞
      (Prod.map (_root_.id : P → P) (Subtype.val : W → N)) :=
    contMDiff_id.prodMap contMDiff_subtypeVal
  have hηW : IsSmoothForm (IP.prod J) r
      (mpullback (IP.prod J) (IP.prod J) (Prod.map (_root_.id : P → P) (Subtype.val : W → N)) η) :=
    hη.mpullback (hval.of_le (by exact_mod_cast (le_top : r + 1 ≤ ⊤)))
  have hsliceW (p : P) := mpullback_prodMk_mpullback_prodMap hv η p
  have hclosedW (p : P) : mextDeriv (mpullback J (IP.prod J) (Prod.mk p)
      (mpullback (IP.prod J) (IP.prod J) (Prod.map (_root_.id : P → P) (Subtype.val : W → N))
        η)) = 0 := by
    rw [hsliceW]
    exact ((hη.mpullback (contMDiff_const.prodMk contMDiff_id)).of_le
      (by exact_mod_cast hr)).mextDeriv_mpullback_eq_zero (hclosed p) contMDiff_subtypeVal
  obtain ⟨β, hβ, hdβ, hβ₀⟩ := Φ.exists_isSmoothForm_family_relative_primitive hr
    (by exact_mod_cast (le_top : r + 1 ≤ ⊤)) hηW hclosedW fun p ↦ by rw [hsliceW, hpull, hi p]
  refine ⟨β, hβ, fun p ↦ ?_, fun p x ↦ ?_⟩
  · rw [hdβ p, hsliceW]
  · rw [hx]
    exact hβ₀ p x

end TauCeti.SmoothEmbedding
