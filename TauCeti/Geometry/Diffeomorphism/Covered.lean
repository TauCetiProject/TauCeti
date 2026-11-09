/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.Geometry.Diffeomorphism.Evaluation

/-!
# Manifolds covered by diffeomorphisms

Let `M` be a compact boundaryless `C^n` manifold of dimension `d`, oriented by `o`, and let
`Diff(M) = M ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M` carry the weak Whitney topology. Evaluation at a base
point `x₀` is a continuous map `ev : Diff(M) → M`, `φ ↦ φ x₀` (`Diffeomorph.evalAt`). For an
integer `ℓ`, the manifold `M` is **`ℓ`-covered by diffeomorphisms** at `x₀` if some class
`A ∈ H_d(Diff(M); ℤ)` satisfies `ev_* A = ℓ • [M]`
(`TauCeti.HomologicalOrientation.IsCoveredByDiffeomorphisms`). For `ℓ = 1` this says that
`M` is covered by diffeomorphisms; for `ℓ > 0` it is the variant where evaluation reaches a
nonzero multiple of the fundamental class. Every manifold is `0`-covered, so only `ℓ ≠ 0` carries
information.

These conditions are the input of the abundance criterion for 2-spheres of
Barraud–Damian–Humilière–Oancea (their Propositions 6.29 and 6.33): a closed connected oriented
manifold that is `ℓ`-covered by diffeomorphisms for some `ℓ > 0` and is not a `K(π, 1)`, and
such that either `π₂ ≠ 0` or its first nontrivial homotopy group in degree at least `3` is not
`ℓ`-torsion, carries a class of maps of the 2-sphere living over its fundamental class. This file
provides the condition and the ways it is established:

* a family of diffeomorphisms `φ : Z → Diff(M)` and a class `a ∈ H_d(Z; ℤ)` whose image under
  `ev ∘ φ` is `ℓ • [M]`; in particular a family parametrized by a compact oriented `d`-manifold
  `P` with `(ev ∘ φ)_*[P] = ℓ • [M]`, such as a rotation family of spheres;
* a continuous section `σ : M → Diff(M)` of evaluation, `σ x x₀ = x`, which makes `M` covered;
* a jointly smooth action of a group `G` on `M`, through the orbit map `g ↦ g • x₀`: if it sends
  a class of `H_d(G; ℤ)` to `ℓ • [M]`, then `M` is `ℓ`-covered;
* a compact Lie group is covered by diffeomorphisms, through left translations.

The condition is invariant under reversing the orientation and does not depend on the base point
within a path component, since evaluations at two points joined by a path are homotopic.

## Main definitions

* `TauCeti.HomologicalOrientation.IsCoveredByDiffeomorphisms o hd n x₀ ℓ`: some class of
  `H_d(Diff(M); ℤ)` evaluates at `x₀` to `ℓ • [M]`, characterized by
  `isCoveredByDiffeomorphisms_iff`.

## Main results

* `IsCoveredByDiffeomorphisms.of_homologyMap`, `IsCoveredByDiffeomorphisms.of_mapFundamentalClass`:
  the condition from a family of diffeomorphisms.
* `isCoveredByDiffeomorphisms_of_section`: a section of evaluation makes `M` covered.
* `isCoveredByDiffeomorphisms_of_smul`: the condition from a smooth group action.
* `isCoveredByDiffeomorphisms_of_lieGroup`: compact Lie groups are covered by diffeomorphisms.
* `IsCoveredByDiffeomorphisms.zsmul`: multiples of `ℓ`.
* `isCoveredByDiffeomorphisms_neg`: independence of the orientation.
* `isCoveredByDiffeomorphisms_iff_of_joined`,
  `isCoveredByDiffeomorphisms_iff_of_pathConnectedSpace`: independence of the base point.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.3, Definitions 6.26 and 6.32,
  Example 6.28 and Example 6.30.
* C. Viterbo, *Inverse reduction inequalities for spectral numbers and applications*,
  arXiv:2203.13172, Definition 6.1.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology Module
open scoped Manifold ContDiff TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

namespace HomologicalOrientation

section Covered

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  {d : ℕ} (o : HomologicalOrientation M E d) (hd : finrank ℝ E = d)
  (n : ℕ∞ω) [IsManifold 𝓘(ℝ, E) n M]

/-- A compact oriented `d`-manifold `M` is **`ℓ`-covered by diffeomorphisms** at the base point
`x₀` if some class `A ∈ H_d(Diff(M); ℤ)` is sent to `ℓ • [M]` by evaluation at `x₀`,
`Diff(M) → M`, `φ ↦ φ x₀`. Here `Diff(M)` is the group of `C^n` diffeomorphisms of `M` with the
weak Whitney topology. For `ℓ = 1` this is the condition that `M` is covered by diffeomorphisms.
The condition holds trivially for `ℓ = 0`. -/
def IsCoveredByDiffeomorphisms (x₀ : M) (ℓ : ℤ) : Prop :=
  ∃ A : ((singularHomologyFunctor (ModuleCat.{0} ℤ) d).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).obj
      (TopCat.of (M ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M)),
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) d).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
      (TopCat.ofHom (Diffeomorph.evalAt x₀))).hom A =
      ℓ • o.mapFundamentalClass hd (ContinuousMap.id M)

/-- Unfolding `IsCoveredByDiffeomorphisms`: some class of `H_d(Diff(M); ℤ)` evaluates at `x₀` to
`ℓ • [M]`. -/
theorem isCoveredByDiffeomorphisms_iff (x₀ : M) (ℓ : ℤ) :
    o.IsCoveredByDiffeomorphisms hd n x₀ ℓ ↔
      ∃ A : ((singularHomologyFunctor (ModuleCat.{0} ℤ) d).obj
          (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of (M ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M)),
        (((singularHomologyFunctor (ModuleCat.{0} ℤ) d).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
          (TopCat.ofHom (Diffeomorph.evalAt x₀))).hom A =
          ℓ • o.mapFundamentalClass hd (ContinuousMap.id M) :=
  Iff.rfl

variable {o hd n}

/-- **Covering by a family of diffeomorphisms.** If a continuous family `φ : Z → Diff(M)`
and a class `a ∈ H_d(Z; ℤ)` satisfy `(ev ∘ φ)_* a = ℓ • [M]`, then `M` is `ℓ`-covered by
diffeomorphisms, with `A = φ_* a`. -/
theorem IsCoveredByDiffeomorphisms.of_homologyMap {Z : Type} [TopologicalSpace Z]
    (φ : C(Z, M ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M)) {x₀ : M} {ℓ : ℤ}
    (a : ((singularHomologyFunctor (ModuleCat.{0} ℤ) d).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).obj
      (TopCat.of Z))
    (h : (((singularHomologyFunctor (ModuleCat.{0} ℤ) d).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
      (TopCat.ofHom ((Diffeomorph.evalAt x₀).comp φ))).hom a =
      ℓ • o.mapFundamentalClass hd (ContinuousMap.id M)) :
    o.IsCoveredByDiffeomorphisms hd n x₀ ℓ := by
  refine ⟨(((singularHomologyFunctor (ModuleCat.{0} ℤ) d).obj
    (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom φ)).hom a, ?_⟩
  rw [← h, TopCat.ofHom_comp, Functor.map_comp]
  rfl

/-- **Covering by a family of diffeomorphisms parametrized by a manifold.** If a continuous
family `φ : P → Diff(M)` parametrized by a compact oriented `d`-manifold `P` satisfies
`(ev ∘ φ)_*[P] = ℓ • [M]`, then `M` is `ℓ`-covered by diffeomorphisms. When `P` is connected
this says that `ev ∘ φ : P → M` has degree `ℓ`. -/
theorem IsCoveredByDiffeomorphisms.of_mapFundamentalClass {F P : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace P] [T2Space P] [ChartedSpace F P]
    [CompactSpace P] (o' : HomologicalOrientation P F d) (hF : finrank ℝ F = d)
    (φ : C(P, M ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M)) {x₀ : M} {ℓ : ℤ}
    (h : o'.mapFundamentalClass hF ((Diffeomorph.evalAt x₀).comp φ) =
      ℓ • o.mapFundamentalClass hd (ContinuousMap.id M)) :
    o.IsCoveredByDiffeomorphisms hd n x₀ ℓ :=
  .of_homologyMap φ (o'.fundamentalClass hF) (by rwa [mapFundamentalClass_def] at h)

variable (o hd n)

/-- Every manifold is `0`-covered by diffeomorphisms. -/
theorem isCoveredByDiffeomorphisms_zero (x₀ : M) : o.IsCoveredByDiffeomorphisms hd n x₀ 0 :=
  ⟨0, by rw [map_zero, zero_smul]⟩

/-- **A section of evaluation covers the manifold** (Example 6.28 of
Barraud–Damian–Humilière–Oancea). If a continuous family of diffeomorphisms `σ : M → Diff(M)`
satisfies `σ x x₀ = x` for every `x`, then `M` is covered by diffeomorphisms at `x₀`, with
`A = σ_*[M]`. -/
theorem isCoveredByDiffeomorphisms_of_section {x₀ : M} (σ : C(M, M ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M))
    (hσ : ∀ x, σ x x₀ = x) : o.IsCoveredByDiffeomorphisms hd n x₀ 1 :=
  .of_mapFundamentalClass o hd σ (by
    rw [one_smul]
    congr 1
    ext x
    simp [hσ])

/-- **Covering through a smooth group action.** Let a group `G`, a `C^n` manifold, act on `M` by a
jointly `C^n` action. If the orbit map `f : G → M`, `g ↦ g • x₀`, sends a class
`a ∈ H_d(G; ℤ)` to `ℓ • [M]`, then `M` is `ℓ`-covered by diffeomorphisms at `x₀`: the action is a
continuous map `G → Diff(M)` whose composite with evaluation at `x₀` is the orbit map. -/
theorem isCoveredByDiffeomorphisms_of_smul {F H : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {I : ModelWithCorners ℝ F H} {G : Type} [TopologicalSpace G]
    [ChartedSpace H G] [IsManifold I n G] [Group G] [MulAction G M]
    [ContMDiffSMul I 𝓘(ℝ, E) n G M] {x₀ : M} (f : C(G, M)) (hf : ∀ g, f g = g • x₀) {ℓ : ℤ}
    (a : ((singularHomologyFunctor (ModuleCat.{0} ℤ) d).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).obj
      (TopCat.of G))
    (h : (((singularHomologyFunctor (ModuleCat.{0} ℤ) d).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
      (TopCat.ofHom f)).hom a = ℓ • o.mapFundamentalClass hd (ContinuousMap.id M)) :
    o.IsCoveredByDiffeomorphisms hd n x₀ ℓ := by
  refine .of_homologyMap ⟨fun g ↦ Diffeomorph.smul I 𝓘(ℝ, E) n g,
    ContMDiff.continuous_diffeomorphWeakWhitney (by
      simp only [Diffeomorph.smul_apply]
      exact ContMDiffSMul.contMDiff_smul (I := I) (I' := 𝓘(ℝ, E)))⟩ a ?_
  convert h
  ext g
  simp [hf]

variable {o hd n}

/-- If `M` is `ℓ`-covered by diffeomorphisms, it is `k * ℓ`-covered for every integer `k`. -/
theorem IsCoveredByDiffeomorphisms.zsmul {x₀ : M} {ℓ : ℤ}
    (h : o.IsCoveredByDiffeomorphisms hd n x₀ ℓ) (k : ℤ) :
    o.IsCoveredByDiffeomorphisms hd n x₀ (k * ℓ) := by
  obtain ⟨A, hA⟩ := h
  exact ⟨k • A, by rw [map_zsmul, hA, mul_smul]⟩

/-- A manifold covered by diffeomorphisms is `ℓ`-covered for every `ℓ`. -/
theorem IsCoveredByDiffeomorphisms.of_one {x₀ : M} (h : o.IsCoveredByDiffeomorphisms hd n x₀ 1)
    (ℓ : ℤ) : o.IsCoveredByDiffeomorphisms hd n x₀ ℓ := by
  simpa using h.zsmul ℓ

/-- Covering by diffeomorphisms does not depend on the orientation. -/
@[simp]
theorem isCoveredByDiffeomorphisms_neg {x₀ : M} {ℓ : ℤ} :
    (-o).IsCoveredByDiffeomorphisms hd n x₀ ℓ ↔ o.IsCoveredByDiffeomorphisms hd n x₀ ℓ := by
  refine ⟨fun ⟨A, hA⟩ ↦ ⟨-A, ?_⟩, fun ⟨A, hA⟩ ↦ ⟨-A, ?_⟩⟩
  · rw [map_neg, hA, mapFundamentalClass_neg, zsmul_neg, neg_neg]
  · rw [map_neg, hA, mapFundamentalClass_neg, zsmul_neg]

/-- Evaluations at two points joined by a path `γ` are homotopic, through evaluation along `γ`. -/
private def evalAtHomotopy {x₀ x₁ : M} (γ : Path x₀ x₁) :
    ContinuousMap.Homotopy
      (Diffeomorph.evalAt (I := 𝓘(ℝ, E)) (J := 𝓘(ℝ, E)) (n := n) (N := M) x₀)
      (Diffeomorph.evalAt x₁) where
  toFun p := p.2 (γ p.1)
  continuous_toFun := by fun_prop
  map_zero_left φ := by simp
  map_one_left φ := by simp

/-- **Independence of the base point along a path.** At two points joined by a path, `M` is
`ℓ`-covered by diffeomorphisms at one exactly when it is at the other: the two evaluations are
homotopic, so they induce the same map on homology. -/
theorem isCoveredByDiffeomorphisms_iff_of_joined {x₀ x₁ : M} (hx : Joined x₀ x₁) {ℓ : ℤ} :
    o.IsCoveredByDiffeomorphisms hd n x₀ ℓ ↔ o.IsCoveredByDiffeomorphisms hd n x₁ ℓ := by
  have heq : ((singularHomologyFunctor (ModuleCat.{0} ℤ) d).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).map
      (TopCat.ofHom (Diffeomorph.evalAt (I := 𝓘(ℝ, E)) (J := 𝓘(ℝ, E)) (n := n) (N := M) x₀)) =
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) d).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom (Diffeomorph.evalAt x₁)) :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor (C := ModuleCat.{0} ℤ)
      (evalAtHomotopy (n := n) hx.somePath) _ d
  simp only [IsCoveredByDiffeomorphisms, heq]

/-- On a path-connected manifold, covering by diffeomorphisms does not depend on the base
point. -/
theorem isCoveredByDiffeomorphisms_iff_of_pathConnectedSpace [PathConnectedSpace M] (x₀ x₁ : M)
    {ℓ : ℤ} :
    o.IsCoveredByDiffeomorphisms hd n x₀ ℓ ↔ o.IsCoveredByDiffeomorphisms hd n x₁ ℓ :=
  isCoveredByDiffeomorphisms_iff_of_joined (PathConnectedSpace.joined x₀ x₁)

end Covered

section LieGroup

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  {d : ℕ} (o : HomologicalOrientation M E d) (hd : finrank ℝ E = d)
  (n : ℕ∞ω) [Group M] [LieGroup 𝓘(ℝ, E) n M]

/-- **Compact Lie groups are covered by diffeomorphisms** (Example 6.30 of
Barraud–Damian–Humilière–Oancea). For a compact `C^n` Lie group `M`, the left translations by
`g * x₀⁻¹` form a continuous section of evaluation at `x₀`. -/
theorem isCoveredByDiffeomorphisms_of_lieGroup (x₀ : M) :
    o.IsCoveredByDiffeomorphisms hd n x₀ 1 := by
  refine o.isCoveredByDiffeomorphisms_of_section hd n
    ⟨fun g ↦ Diffeomorph.smul 𝓘(ℝ, E) 𝓘(ℝ, E) n (g * x₀⁻¹),
      ContMDiff.continuous_diffeomorphWeakWhitney (by
        simp only [Diffeomorph.smul_apply, smul_eq_mul]
        exact (contMDiff_fst.mul contMDiff_const).mul contMDiff_snd)⟩ fun g ↦ ?_
  simp

end LieGroup

end HomologicalOrientation

end TauCeti
