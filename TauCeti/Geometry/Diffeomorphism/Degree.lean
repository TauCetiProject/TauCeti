/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Covered
public import TauCeti.Geometry.Manifold.Degree.Boundaryless
public import TauCeti.Geometry.Manifold.Degree.Global

/-!
# Covering a manifold by diffeomorphisms of prescribed smooth degree

Let `M` be a compact preconnected `(n + 1)`-dimensional manifold modelled on a real inner product
space `F`, and let `φ : P → Diff^k(M)` be a continuous family of `C^k` diffeomorphisms parametrized
by a compact oriented boundaryless `(n + 1)`-manifold `(P, I)` (possibly modelled on a different
space `(E, H, I)`, such as a product of spheres). Evaluating `φ` at a base point `x₀ ∈ M` gives the
map `p ↦ φ p x₀ : P → M`.

Combining the model-transport bridge `TauCeti.Geometry.Manifold.Degree.Boundaryless` with
`TauCeti.HomologicalOrientation.IsCoveredByDiffeomorphisms.of_mapFundamentalClass` shows that at any
regular value `y` of `p ↦ φ p x₀`, the manifold `M` is `ℓ`-covered by `C^k` diffeomorphisms for
`ℓ = degreeAtRegularValue oP oM (fun p ↦ φ p x₀) y` — and, when `M` is connected, this holds at
every base point `x ∈ M` and for every homological orientation `o` of `M`. When `(P, I)` and `M`
are `C^∞` and `p ↦ φ p x₀` is smooth, Sard's theorem removes the choice of regular value and gives
covering with multiplicity `degree oP oM (fun p ↦ φ p x₀)`.

This abstracts the passage from a smooth degree computation on a parameter manifold `P` to
`IsCoveredByDiffeomorphisms`, as used in Barraud–Damian–Humilière–Oancea, Proposition 6.34.

## Main results

* `TauCeti.Manifold.Orientation.isCoveredByDiffeomorphisms_of_degreeAtRegularValue`: a family
  `φ : C(P, Diff^k(M))` makes `M` `ℓ`-covered at `x₀` for the signed count `ℓ` over any regular
  value of `p ↦ φ p x₀`.
* `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_of_degreeAtRegularValue`: on a
  connected target `M`, the same holds for every homological orientation `o` and every base point
  `x ∈ M`.
* `TauCeti.Manifold.Orientation.isCoveredByDiffeomorphisms_of_degree`,
  `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_of_degree`: the `C^∞` versions in terms
  of the global mapping degree `degree oP oM (fun p ↦ φ p x₀)`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.3, Definitions 6.26 and 6.32,
  Proposition 6.34.
-/

public section

noncomputable section

open Function Module
open scoped ContDiff Manifold TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

/-- A continuous linear equivalence `E ≃L[ℝ] F` witnessing that an `(n + 1)`-oriented manifold
`(P, I)` and an `(n + 1)`-dimensional space `F` have equal finite dimension. -/
private def modelEquiv {E H P F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace P] [ChartedSpace H P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {n : ℕ} (oP : Manifold.Orientation I P (Fin (n + 1))) (hF : finrank ℝ F = n + 1) :
    E ≃L[ℝ] F :=
  (LinearEquiv.ofFinrankEq E F
    ((by simpa using oP.card_eq.symm : finrank ℝ E = n + 1).trans hF.symm)
    ).toContinuousLinearEquiv

section RegularValue

variable {E H P F M : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace P] [ChartedSpace H P] [T2Space P] [CompactSpace P] [IsManifold I 1 P]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace F M] [T2Space M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, F) 1 M]
  {n : ℕ} (hF : finrank ℝ F = n + 1) (k : ℕ∞ω) [IsManifold 𝓘(ℝ, F) k M]

/-- **Covering by diffeomorphisms via the signed count at a regular value.** Let
`φ : C(P, Diff^k(M))` be a continuous family of `C^k` diffeomorphisms of `M` parametrized by a
compact oriented boundaryless `C¹` manifold `(P, I, oP)`. For any base point `x₀ : M` and any
regular value `y` of `p ↦ φ p x₀`, the manifold `M` is `ℓ`-covered by `C^k` diffeomorphisms at
`x₀` with `ℓ = degreeAtRegularValue oP oM (fun p ↦ φ p x₀) y`. -/
theorem Manifold.Orientation.isCoveredByDiffeomorphisms_of_degreeAtRegularValue
    [PreconnectedSpace M]
    (oM : Manifold.Orientation 𝓘(ℝ, F) M (Fin (n + 1)))
    (oP : Manifold.Orientation I P (Fin (n + 1)))
    (φ : C(P, M ≃ₘ^k⟮𝓘(ℝ, F), 𝓘(ℝ, F)⟯ M)) {x₀ y : M}
    (hy : IsRegularValue I 𝓘(ℝ, F) (fun p ↦ φ p x₀) y) :
    (oM.toHomologicalOrientation hF).IsCoveredByDiffeomorphisms hF k x₀
      (degreeAtRegularValue oP oM (fun p ↦ φ p x₀) y) := by
  let L : E ≃L[ℝ] F := modelEquiv oP hF
  let ψ : C(BoundarylessModel (I.transContinuousLinearEquiv L) P, P) :=
    ⟨(BoundarylessModel.homeomorph (I.transContinuousLinearEquiv L) P).symm,
      (BoundarylessModel.homeomorph (I.transContinuousLinearEquiv L) P).symm.continuous⟩
  have heval : ⇑((Diffeomorph.evalAt x₀).comp φ) = fun p ↦ φ p x₀ := by
    ext p
    simp
  have hy' : IsRegularValue I 𝓘(ℝ, F) ((Diffeomorph.evalAt x₀).comp φ) y := heval.symm ▸ hy
  refine .of_mapFundamentalClass ((oP.toBoundarylessModel L).toHomologicalOrientation hF) hF
    (φ.comp ψ) ?_
  rw [← ContinuousMap.comp_assoc, HomologicalOrientation.mapFundamentalClass_id, ← heval]
  exact oP.mapFundamentalClass_toBoundarylessModel_eq_degreeAtRegularValue_smul hF oM L hy'

/-- **Orientation- and basepoint-independent covering from a regular value.** On a connected compact
manifold `M`, if `y` is a regular value of `p ↦ φ p x₀`, then for *every* homological orientation
`o` of `M` and *every* base point `x : M`, `M` is `ℓ`-covered by `C^k` diffeomorphisms at `x` with
`ℓ = degreeAtRegularValue oP oM (fun p ↦ φ p x₀) y`. -/
theorem HomologicalOrientation.isCoveredByDiffeomorphisms_of_degreeAtRegularValue
    [ConnectedSpace M] (o : HomologicalOrientation M F (n + 1))
    (oP : Manifold.Orientation I P (Fin (n + 1)))
    (oM : Manifold.Orientation 𝓘(ℝ, F) M (Fin (n + 1)))
    (φ : C(P, M ≃ₘ^k⟮𝓘(ℝ, F), 𝓘(ℝ, F)⟯ M)) {x₀ y : M}
    (hy : IsRegularValue I 𝓘(ℝ, F) (fun p ↦ φ p x₀) y) (x : M) :
    o.IsCoveredByDiffeomorphisms hF k x (degreeAtRegularValue oP oM (fun p ↦ φ p x₀) y) :=
  ((oM.toHomologicalOrientation hF).isCoveredByDiffeomorphisms_iff_of_connectedSpace o x₀ x).1
    (oM.isCoveredByDiffeomorphisms_of_degreeAtRegularValue hF k oP φ hy)

end RegularValue

section GlobalDegree

variable {E H P F M : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace P] [ChartedSpace H P] [T2Space P] [CompactSpace P] [IsManifold I ∞ P]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace F M] [T2Space M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, F) ∞ M]
  {n : ℕ} (hF : finrank ℝ F = n + 1) (k : ℕ∞ω) [IsManifold 𝓘(ℝ, F) k M]

private theorem exists_isRegularValue_and_degree_eq [ConnectedSpace M]
    (hF : finrank ℝ F = n + 1)
    (oP : Manifold.Orientation I P (Fin (n + 1)))
    (oM : Manifold.Orientation 𝓘(ℝ, F) M (Fin (n + 1))) {f : P → M}
    (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) :
    ∃ y : M, IsRegularValue I 𝓘(ℝ, F) f y ∧
      TauCeti.degree oP oM f = degreeAtRegularValue oP oM f y := by
  have : IsManifold I 1 P := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold 𝓘(ℝ, F) 1 M := IsManifold.of_le (n := ∞) (by simp)
  let L : E ≃L[ℝ] F := modelEquiv oP hF
  let Φ := BoundarylessModel.diffeomorphTransContinuousLinearEquiv I (M := P) L ∞
  have hf' : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F) ∞
      (f ∘ (BoundarylessModel.homeomorph (I.transContinuousLinearEquiv L) P).symm) := by
    rw [← BoundarylessModel.coe_diffeomorphTransContinuousLinearEquiv_symm I L ∞]
    exact hf.comp Φ.symm.contMDiff
  obtain ⟨y, hy'⟩ := (dense_isRegularValue rfl (hf'.mdifferentiable (by simp))).nonempty
  refine ⟨y, (BoundarylessModel.isRegularValue_comp_homeomorph_symm_iff L f y).1 hy', ?_⟩
  rw [← oP.degree_toBoundarylessModel oM L f,
    degree_eq_degreeAtRegularValue (oP.toBoundarylessModel L) oM hf' hy',
    oP.degreeAtRegularValue_toBoundarylessModel oM L f y]

/-- **Covering by diffeomorphisms via the smooth mapping degree.** When `(P, I)` and `M` are smooth
and the evaluation map `p ↦ φ p x₀` is `C^∞`, Sard's theorem supplies a regular value, so `M` is
`degree oP oM (fun p ↦ φ p x₀)`-covered by `C^k` diffeomorphisms at `x₀`. -/
theorem Manifold.Orientation.isCoveredByDiffeomorphisms_of_degree
    [PreconnectedSpace M]
    (oM : Manifold.Orientation 𝓘(ℝ, F) M (Fin (n + 1)))
    (oP : Manifold.Orientation I P (Fin (n + 1)))
    (φ : C(P, M ≃ₘ^k⟮𝓘(ℝ, F), 𝓘(ℝ, F)⟯ M)) {x₀ : M}
    (hf : ContMDiff I 𝓘(ℝ, F) ∞ fun p ↦ φ p x₀) :
    (oM.toHomologicalOrientation hF).IsCoveredByDiffeomorphisms hF k x₀
      (TauCeti.degree oP oM fun p ↦ φ p x₀) := by
  have : ConnectedSpace M := { toNonempty := ⟨x₀⟩ }
  have : IsManifold I 1 P := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold 𝓘(ℝ, F) 1 M := IsManifold.of_le (n := ∞) (by simp)
  obtain ⟨y, hy, hdeg⟩ := exists_isRegularValue_and_degree_eq hF oP oM hf
  rw [hdeg]
  exact oM.isCoveredByDiffeomorphisms_of_degreeAtRegularValue hF k oP φ hy

/-- **Orientation- and basepoint-independent covering via the smooth mapping degree.** -/
theorem HomologicalOrientation.isCoveredByDiffeomorphisms_of_degree
    [ConnectedSpace M]
    (o : HomologicalOrientation M F (n + 1))
    (oP : Manifold.Orientation I P (Fin (n + 1)))
    (oM : Manifold.Orientation 𝓘(ℝ, F) M (Fin (n + 1)))
    (φ : C(P, M ≃ₘ^k⟮𝓘(ℝ, F), 𝓘(ℝ, F)⟯ M)) {x₀ : M}
    (hf : ContMDiff I 𝓘(ℝ, F) ∞ fun p ↦ φ p x₀) (x : M) :
    o.IsCoveredByDiffeomorphisms hF k x (TauCeti.degree oP oM fun p ↦ φ p x₀) := by
  have : IsManifold I 1 P := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold 𝓘(ℝ, F) 1 M := IsManifold.of_le (n := ∞) (by simp)
  obtain ⟨y, hy, hdeg⟩ := exists_isRegularValue_and_degree_eq hF oP oM hf
  rw [hdeg]
  exact o.isCoveredByDiffeomorphisms_of_degreeAtRegularValue hF k oP oM φ hy x

end GlobalDegree

end TauCeti
