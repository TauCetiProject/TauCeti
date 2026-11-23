/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass
public import TauCeti.Geometry.Manifold.Degree.StiefelRotation
import TauCeti.Geometry.Manifold.Degree.Homological
import TauCeti.Geometry.Manifold.Instances.Stiefel.Projection
import TauCeti.Geometry.Sphere.Connected
import TauCeti.Geometry.Sphere.Equator

/-!
# The Stiefel rotation family on fundamental classes

Let `E` be a real inner product space of dimension `n + 2`, with unit sphere `Sⁿ⁺¹` and unit
tangent bundle the Stiefel manifold `V₂(E)` of orthonormal pairs. The Stiefel rotation family
(`TauCeti.stiefelRotationFamily`)

`τ : V₂(E) × S¹ → Sⁿ⁺¹ × Sⁿ⁺¹`, `τ ((u, v), z) = (u, Re z • u + Im z • v)`,

has degree `±(1 + (-1)ⁿ)` at its regular values
(`TauCeti.exists_degreeAtRegularValue_stiefelRotationFamily_eq`). This file reads that degree in
singular homology: for `n ≥ 1`, `τ` sends every integral fundamental class of `V₂(E) × S¹` to
`±(1 + (-1)ⁿ)` times any integral fundamental class of `Sⁿ⁺¹ × Sⁿ⁺¹`
(`TauCeti.exists_singularHomologyMap_stiefelRotationFamily_eq_smul`). So the image is `±2` times a
fundamental class for even `n`
(`TauCeti.singularHomologyMap_stiefelRotationFamily_eq_two_smul_or_eq_neg_two_smul`), and zero for
odd `n`.

This is the identity `τ_*[Σ_p × S¹] = ±2 [S^{m−1} × S^{m−1}]` of the proof of Proposition 6.17 of
Barraud–Damian–Humilière–Oancea, for the even-dimensional sphere `Sᵐ`, `m = n + 2`, with
`Σ_p = V₂(T_p Sᵐ)`. The fundamental classes are those of `TauCeti.IsFundamentalClass`, which need
no orientation datum and no chart on the products; on a compact connected manifold `M` with a
homological orientation they are `[M]` and `-[M]`
(`TauCeti.HomologicalOrientation.isFundamentalClass_iff_eq_or_eq_neg`).

The degree is read in homology through
`TauCeti.Manifold.Orientation.exists_singularHomologyMap_eq_degreeAtRegularValue_smul`, which
applies to manifolds with product models such as these, at the regular values `(p, q)` with `q ≠ ±p`
(`TauCeti.isRegularValue_stiefelRotationFamily`). It needs `V₂(E) × S¹` to be connected, which
holds for `n ≥ 1` (`TauCeti.pathConnectedSpace_stiefel`). For `n = 0` the Stiefel manifold is
`O(2)`, with two components, on which a fundamental class may carry independent signs.

## Main results

* `TauCeti.exists_singularHomologyMap_stiefelRotationFamily_eq_smul`: for `n ≥ 1`, `τ_* μ` is
  `±(1 + (-1)ⁿ) • ν` for fundamental classes `μ` and `ν`.
* `TauCeti.singularHomologyMap_stiefelRotationFamily_eq_two_smul_or_eq_neg_two_smul`: for even
  `n ≥ 2`, `τ_* μ = 2 • ν` or `τ_* μ = -2 • ν`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2 (proof of Proposition 6.17).
-/

public section

noncomputable section

open Metric Module AlgebraicTopology TauCeti.Manifold.Orientation
open scoped Manifold ContDiff

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1 + 1)]

/-- **The Stiefel rotation family on fundamental classes.** For `n ≥ 1`, the Stiefel rotation family
`τ : V₂(E) × S¹ → Sⁿ⁺¹ × Sⁿ⁺¹` sends any integral fundamental class `μ` of `V₂(E) × S¹` to
`s * (1 + (-1)ⁿ)` times any integral fundamental class `ν` of `Sⁿ⁺¹ × Sⁿ⁺¹`, for a sign
`s = ±1`. -/
theorem exists_singularHomologyMap_stiefelRotationFamily_eq_smul (hn : n ≠ 0)
    {μ : ((TopCat.toSSet.obj (TopCat.of (stiefel E 2 × sphere (0 : ℂ) 1))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) (2 * n + 1 + 1) : ModuleCat.{0} ℤ)}
    (hμ : IsFundamentalClass μ)
    {ν : ((TopCat.toSSet.obj (TopCat.of (sphere (0 : E) 1 × sphere (0 : E) 1))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) (2 * n + 1 + 1) : ModuleCat.{0} ℤ)}
    (hν : IsFundamentalClass ν) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (2 * n + 1 + 1)).obj
          (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom ⟨stiefelRotationFamily, continuous_stiefelRotationFamily⟩)).hom μ =
        (s * (1 + (-1) ^ n)) • ν := by
  have hE : finrank ℝ E = n + 1 + 1 := Fact.out
  -- Both products are connected.
  have := pathConnectedSpace_stiefel (E := E) (k := 2) (by omega)
  have := connectedSpace_sphere (E := E) (n + 1)
  have := connectedSpace_sphere (E := ℂ) 1
  -- Orientations of `V₂(E) × S¹` and `Sⁿ⁺¹ × Sⁿ⁺¹`.
  let O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4)) :=
    (finBasisOfFinrankEq ℝ (Fin 2 → E) (by
      rw [Module.finrank_pi_fintype]
      simp [hE]
      ring)).orientation
  let oE : _root_.Orientation ℝ E (Fin (n + 1 + 1)) := (finBasisOfFinrankEq ℝ E hE).orientation
  let oP := O.stiefelTwoOrientation.prod Complex.orientation.sphereOrientation
  let oN : Manifold.Orientation ((𝓡 (n + 1)).prod (𝓡 (n + 1)))
      (sphere (0 : E) 1 × sphere (0 : E) 1) (Fin (2 * n + 1 + 1)) :=
    (oE.sphereOrientation.prod oE.sphereOrientation).reindex (finCongr (by ring))
  -- The degree at a regular value `(p, q)` with `q ≠ ±p`, read in homology.
  obtain ⟨p⟩ : Nonempty (sphere (0 : E) 1) := inferInstance
  obtain ⟨q, hqp, hqp'⟩ := exists_ne_and_ne_neg_sphere (by omega : 1 < finrank ℝ E) p
  obtain ⟨s, hs, hdeg⟩ :=
    exists_degreeAtRegularValue_stiefelRotationFamily_eq O oN (y := (p, q)) hqp hqp'
  obtain ⟨s', hs', h⟩ := exists_singularHomologyMap_eq_degreeAtRegularValue_smul
    (by rw [finrank_prod, finrank_stiefelTwoModel (n := n), finrank_euclideanSpace_fin])
    (by rw [finrank_prod, finrank_euclideanSpace_fin]; ring)
    oP oN (f := ⟨stiefelRotationFamily, continuous_stiefelRotationFamily⟩)
    (contMDiff_stiefelRotationFamily.of_le (by simp))
    (isRegularValue_stiefelRotationFamily (y := (p, q)) hqp hqp') hμ hν
  refine ⟨s' * s, ?_, h.trans ?_⟩
  · rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> simp
  · rw [ContinuousMap.coe_mk, hdeg, mul_assoc]

/-- **The Stiefel rotation family doubles fundamental classes** when the fibre sphere `Sⁿ` of the
unit tangent bundle has even dimension `n ≥ 2`: `τ` sends any integral fundamental class `μ` of
`V₂(E) × S¹` to `2 • ν` or `-2 • ν`, for any integral fundamental class `ν` of `Sⁿ⁺¹ × Sⁿ⁺¹`.
This is the identity `τ_*[Σ_p × S¹] = ±2 [S^{m−1} × S^{m−1}]` of the proof of Proposition 6.17 of
Barraud–Damian–Humilière–Oancea, for `m = n + 2`. -/
theorem singularHomologyMap_stiefelRotationFamily_eq_two_smul_or_eq_neg_two_smul (hn : Even n)
    (hn₀ : n ≠ 0)
    {μ : ((TopCat.toSSet.obj (TopCat.of (stiefel E 2 × sphere (0 : ℂ) 1))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) (2 * n + 1 + 1) : ModuleCat.{0} ℤ)}
    (hμ : IsFundamentalClass μ)
    {ν : ((TopCat.toSSet.obj (TopCat.of (sphere (0 : E) 1 × sphere (0 : E) 1))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) (2 * n + 1 + 1) : ModuleCat.{0} ℤ)}
    (hν : IsFundamentalClass ν) :
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) (2 * n + 1 + 1)).obj
          (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom ⟨stiefelRotationFamily, continuous_stiefelRotationFamily⟩)).hom μ =
        (2 : ℤ) • ν ∨
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (2 * n + 1 + 1)).obj
          (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom ⟨stiefelRotationFamily, continuous_stiefelRotationFamily⟩)).hom μ =
        (-2 : ℤ) • ν := by
  obtain ⟨s, hs, h⟩ := exists_singularHomologyMap_stiefelRotationFamily_eq_smul hn₀ hμ hν
  rw [hn.neg_one_pow] at h
  rcases hs with rfl | rfl
  · exact Or.inl (h.trans (congrArg (· • ν) (by norm_num)))
  · exact Or.inr (h.trans (congrArg (· • ν) (by norm_num)))

end TauCeti
