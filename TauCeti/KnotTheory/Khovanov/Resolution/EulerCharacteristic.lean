/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Cube.EulerCharacteristic
public import TauCeti.KnotTheory.Khovanov.Rank
public import TauCeti.KnotTheory.Khovanov.Resolution.Cube

/-!
# The Euler characteristic of the unnormalized Khovanov complex

Let `D` be a planar PD-code with `n` crossings. In each quantum degree `j`, the unnormalized
Khovanov complex `⟦D⟧ʲ = TauCeti.PDCode.khovanovBracket D hD R j` is the signed totalization of
the degree-`j` cube of resolutions, whose vertex `S` is the degree `j - |S|` piece of the circle
tensor of the resolution of `S`. These pieces are finite free, so `⟦D⟧ʲ` is a complex of finite
free modules concentrated in the cochain degrees `0, …, n`. By Euler–Poincaré for cubes, over a
Noetherian ring with the rank-nullity property (such as `ℤ` or a field) the Euler characteristic of
the cohomology of `⟦D⟧ʲ` is `∑ S, (-1) ^ |S| rank V(S)_{j - |S|}`.

For an oriented code with `n₊` positive and `n₋` negative crossings, the normalized Khovanov
complex in bidegree `(i, j)` is `⟦D⟧` in bidegree `(i + n₋, j - n₊ + 2 n₋)`. Comparing with the
coefficientwise formula `TauCeti.OrientedPDCode.coeff_enhancedStateSum` for the enhanced state sum
shows that the coefficient of `q ^ j` of the enhanced state sum is `(-1) ^ n₋` times the Euler
characteristic of the cohomology of `⟦D⟧` in quantum degree `j - n₊ + 2 n₋`. For a nonempty
diagram the enhanced state sum is `(q + q⁻¹)` times the Jones polynomial at `t ^ (1/2) = -q`, so
this identifies, quantum degree by quantum degree, the graded Euler characteristic of the
cohomology of the unnormalized Khovanov complex, regraded by the normalization shifts, with
`(q + q⁻¹)` times the Jones polynomial.

## Main results

* `TauCeti.PDCode.eulerChar_khovanovBracket`: the Euler characteristic of `⟦D⟧ʲ` is
  `∑ S, (-1) ^ |S| rank V(S)_{j - |S|}`.
* `TauCeti.PDCode.homologyEulerChar_khovanovBracket`: Euler–Poincaré for `⟦D⟧ʲ`, the Euler
  characteristic of its cohomology is the same signed sum.
* `TauCeti.OrientedPDCode.coeff_enhancedStateSum_eq_homologyEulerChar_khovanovBracket`: the
  coefficient of `q ^ j` of the enhanced state sum is `(-1) ^ n₋` times the Euler characteristic of
  the cohomology of `⟦D⟧` in quantum degree `j - n₊ + 2 n₋`.
* `TauCeti.OrientedPDCode.coeff_mul_eval₂_jonesPolynomial_eq_homologyEulerChar_khovanovBracket`:
  for a nonempty diagram, the coefficient of `q ^ j` of `(q + q⁻¹)` times the Jones polynomial at
  `t ^ (1/2) = -q` is `(-1) ^ n₋` times the Euler characteristic of the cohomology of `⟦D⟧` in
  quantum degree `j - n₊ + 2 n₋`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §§2–3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), §1.3 and §2.
-/

public section

open CategoryTheory Finset Module LaurentPolynomial

namespace TauCeti

universe u

variable {n : ℕ}

namespace PDCode

variable (D : PDCode n) (hD : D.IsPlanar) (R : Type u) [CommRing R] (j : ℤ)

/-- The vertices of the cube of resolutions are free: they are homogeneous pieces of circle
tensors. -/
instance (S : Finset (Fin n)) : Module.Free R ((D.resolutionCube hD R j).obj S) := by
  rw [resolutionCube_obj]
  infer_instance

/-- The vertices of the cube of resolutions are finitely generated: they are homogeneous pieces of
circle tensors. -/
instance (S : Finset (Fin n)) : Module.Finite R ((D.resolutionCube hD R j).obj S) := by
  rw [resolutionCube_obj]
  infer_instance

/-- The terms of the unnormalized Khovanov complex are free. -/
instance (r : ℤ) : Module.Free R ((D.khovanovBracket hD R j).X r) := by
  rw [khovanovBracket_apply]
  infer_instance

/-- The terms of the unnormalized Khovanov complex are finitely generated. -/
instance (r : ℤ) : Module.Finite R ((D.khovanovBracket hD R j).X r) := by
  rw [khovanovBracket_apply]
  infer_instance

/-- The unnormalized Khovanov complex vanishes in negative cochain degrees. -/
instance : (D.khovanovBracket hD R j).IsStrictlyGE 0 := by
  rw [khovanovBracket_apply]
  infer_instance

/-- The unnormalized Khovanov complex of a code with `n` crossings vanishes in cochain degrees
above `n`. -/
instance : (D.khovanovBracket hD R j).IsStrictlyLE n := by
  have h : (D.resolutionCube hD R j).cubeComplex.IsStrictlyLE (Fintype.card (Fin n)) :=
    inferInstance
  rwa [Fintype.card_fin, ← khovanovBracket_apply] at h

/-- **The Euler characteristic of the unnormalized Khovanov complex.** Over a nontrivial
commutative ring, the Euler characteristic of the degree-`j` component of the unnormalized
Khovanov complex of a planar code is the sum over the vertices `S` of the cube of resolutions of
the rank of the degree `j - |S|` piece of the circle tensor of the resolution of `S`, with sign
`(-1) ^ |S|`. -/
theorem eulerChar_khovanovBracket [Nontrivial R] :
    (D.khovanovBracket hD R j).eulerChar = ∑ S : Finset (Fin n), ((#S : ℤ).negOnePow : ℤ) *
      finrank R ((Khovanov.circleQuantumGrading R (D.ResolvedCircle (cubeState S))).piece
        (j - #S)) := by
  rw [khovanovBracket_apply, Functor.eulerChar_cubeComplex]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [resolutionCube_obj]

/-- **Euler–Poincaré for the unnormalized Khovanov complex.** Over a Noetherian commutative ring
with the rank-nullity property, such as `ℤ` or a field, the Euler characteristic of the cohomology
of the degree-`j` component of the unnormalized Khovanov complex of a planar code is the sum over
the vertices `S` of the cube of resolutions of the rank of the degree `j - |S|` piece of the
circle tensor of the resolution of `S`, with sign `(-1) ^ |S|`. Over `ℤ` the rank of a cohomology
group is the rank of its free part, so torsion does not contribute. -/
theorem homologyEulerChar_khovanovBracket [IsNoetherianRing R] [HasRankNullity.{u} R] :
    (D.khovanovBracket hD R j).homologyEulerChar = ∑ S : Finset (Fin n),
      ((#S : ℤ).negOnePow : ℤ) *
        finrank R ((Khovanov.circleQuantumGrading R (D.ResolvedCircle (cubeState S))).piece
          (j - #S)) := by
  rw [khovanovBracket_apply, Functor.homologyEulerChar_cubeComplex]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [resolutionCube_obj]

end PDCode

namespace OrientedPDCode

variable (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar) (R : Type u) [CommRing R]
  [IsNoetherianRing R] [HasRankNullity.{u} R] (j : ℤ)

/-- **The enhanced state sum as the Euler characteristic of Khovanov cohomology.** For a planar
oriented code with `n₊` positive and `n₋` negative crossings, the coefficient of `q ^ j` of the
enhanced state sum is `(-1) ^ n₋` times the Euler characteristic of the cohomology of the
unnormalized Khovanov complex in quantum degree `j - n₊ + 2 n₋`, computed over any Noetherian
commutative ring with the rank-nullity property, such as `ℤ` or a field. -/
theorem coeff_enhancedStateSum_eq_homologyEulerChar_khovanovBracket :
    D.enhancedStateSum.coeff j = ((D.negativeCrossingCount : ℤ).negOnePow : ℤ) *
      (D.toPDCode.khovanovBracket hD R
        (j - (D.positiveCrossingCount - 2 * D.negativeCrossingCount))).homologyEulerChar := by
  rw [coeff_enhancedStateSum D R, PDCode.homologyEulerChar_khovanovBracket, Finset.mul_sum]
  -- Reindex the sum over the states by the vertices `S` of the cube, the state of `S` having the
  -- `B`-smoothing exactly at the crossings of `S`.
  refine (Fintype.sum_bijective _ PDCode.cubeState_bijective _ _ fun S ↦ ?_).symm
  have hj : j - (D.positiveCrossingCount - 2 * D.negativeCrossingCount) - #S =
      j - (#S + D.positiveCrossingCount - 2 * D.negativeCrossingCount) := by
    ring
  -- The quantum degree sits inside the type of the `finrank`, so it is matched by `rw`.
  rw [stateQuantumShift_def, PDCode.filter_cubeState_eq_false, hj]
  simp [stateCochainDegree_def, Int.negOnePow_sub, Units.smul_def]
  ring

/-- **The Jones polynomial as the Euler characteristic of Khovanov cohomology.** For a nonempty
planar oriented code with `n₊` positive and `n₋` negative crossings, the coefficient of `q ^ j` of
`(q + q⁻¹)` times the Jones polynomial at `t ^ (1/2) = -q` is `(-1) ^ n₋` times the Euler
characteristic of the cohomology of the unnormalized Khovanov complex in quantum degree
`j - n₊ + 2 n₋`, computed over any Noetherian commutative ring with the rank-nullity property,
such as `ℤ` or a field. The hypothesis `0 < componentCount` says that the diagram is nonempty. -/
theorem coeff_mul_eval₂_jonesPolynomial_eq_homologyEulerChar_khovanovBracket
    (h : 0 < D.toPDCode.componentCount) :
    ((T 1 + T (-1)) * eval₂ (Int.castRingHom ℤ[T;T⁻¹]) (-genericUnit ℤ) D.jonesPolynomial).coeff j =
      ((D.negativeCrossingCount : ℤ).negOnePow : ℤ) *
        (D.toPDCode.khovanovBracket hD R
          (j - (D.positiveCrossingCount - 2 * D.negativeCrossingCount))).homologyEulerChar := by
  rw [← enhancedStateSum_eq_mul_eval₂_jonesPolynomial D h]
  exact coeff_enhancedStateSum_eq_homologyEulerChar_khovanovBracket D hD R j

end OrientedPDCode

end TauCeti
