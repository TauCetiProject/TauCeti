/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Smale
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.SetTheory.Cardinal.Finite
import TauCeti.AlgebraicTopology.Singular.Sphere
import TauCeti.Geometry.Diffeomorphism.Evaluation
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic
import TauCeti.Topology.Algebra.OrthogonalGroup

/-!
# Cerf's theorem: the path components of `Diff(S³)`

Cerf proved that every orientation-preserving diffeomorphism of the three-sphere is isotopic to
the identity, that is, `π₀ Diff⁺(S³) = 0`. This file states that theorem against the weak Whitney
topology on `Diff(S³)`, as `TauCeti.CerfTheorem`, and records what can be proved about the path
components of the diffeomorphism group of a sphere without it.

The statement avoids orientations of diffeomorphisms by comparing with the orthogonal group:
`TauCeti.CerfTheorem` says that every smooth diffeomorphism of `S³` is joined, in `Diff(S³)`, to
the restriction of an orthogonal transformation of `ℝ⁴`, so the map `π₀ O(4) → π₀ Diff(S³)`
induced by the reference inclusion `TauCeti.orthogonalToDiffSphere` is surjective. That map is
injective in every dimension (`TauCeti.joined_orthogonalToDiffSphere_iff`): two orthogonal
transformations of `ℝⁿ⁺¹` are isotopic as diffeomorphisms of `Sⁿ` exactly when they have the same
determinant. A path of diffeomorphisms is a homotopy of maps, because evaluation is continuous for
the weak Whitney topology, and an orthogonal transformation acts on the reduced homology
`Hₙ(Sⁿ; ℤ) ≅ ℤ` by the sign of its determinant; conversely matrices of equal determinant are
joined in the orthogonal group (`TauCeti.Matrix.joined_orthogonalGroup_iff_det_eq`). So `Diff(Sⁿ)`
is never path-connected (`TauCeti.not_pathConnectedSpace_diff_sphere`), and Cerf's theorem is
equivalent to `Diff(S³)` having exactly two path components
(`TauCeti.cerfTheorem_iff_natCard_zerothHomotopy_eq_two`).

The orientation-free form is equivalent to Cerf's: a diffeomorphism isotopic to an orthogonal
transformation of determinant `-1` reverses orientation, so under `TauCeti.CerfTheorem` an
orientation-preserving diffeomorphism is isotopic to an element of `SO(4)`, hence to the identity;
and conversely an orientation-reversing diffeomorphism composed with a reflection preserves
orientation. Orientation-preservation of diffeomorphisms is not used here.

Cerf's theorem follows from the Smale conjecture `Diff(S³) ≃ O(4)` (Hatcher), since a homotopy
equivalence is surjective on path components (`TauCeti.SmaleConjecture.cerfTheorem`). It is not
proved here. Cerf's corollary `Γ₄ = 0`, that every diffeomorphism of `S³` extends over the
four-ball, is not stated here either.

## Main definitions

* `TauCeti.CerfTheorem`: every smooth diffeomorphism of `S³` is isotopic to an orthogonal one.

## Main results

* `TauCeti.det_eq_of_joined_orthogonalToDiffSphere`: orthogonal transformations isotopic as
  diffeomorphisms of `Sⁿ` have the same determinant.
* `TauCeti.joined_orthogonalToDiffSphere_iff`: they are isotopic exactly when their determinants
  agree.
* `TauCeti.not_pathConnectedSpace_diff_sphere`: the diffeomorphism group of a sphere is not
  path-connected.
* `TauCeti.SmaleConjecture.cerfTheorem`: the Smale conjecture implies Cerf's theorem.
* `TauCeti.cerfTheorem_iff_natCard_zerothHomotopy_eq_two`: Cerf's theorem holds exactly when
  `Diff(S³)` has two path components.

## References

* J. Cerf, *Sur les difféomorphismes de la sphère de dimension trois (Γ₄ = 0)*, Lecture Notes in
  Mathematics 53, Springer (1968), Théorème 1.
* A. Hatcher, *A proof of the Smale conjecture, `Diff(S³) ≃ O(4)`*, Ann. of Math. 117 (1983),
  553–607.
-/

public section

open Metric CategoryTheory
open scoped Manifold ContDiff EuclideanSpace TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

/-! ### Isotopy classes of orthogonal transformations of a sphere -/

section Orthogonal

variable {n : ℕ} {m : ℕ∞ω}

/-- **Isotopic orthogonal transformations have the same determinant.** If the restrictions of two
orthogonal transformations of `ℝⁿ⁺¹` to the unit sphere `Sⁿ` are joined by a path of `C^m`
diffeomorphisms, for the weak Whitney topology, then the two matrices have the same
determinant. -/
theorem det_eq_of_joined_orthogonalToDiffSphere {A B : Matrix.orthogonalGroup (Fin (n + 1)) ℝ}
    (h : Joined (orthogonalToDiffSphere n m A) (orthogonalToDiffSphere n m B)) :
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).det =
      (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).det := by
  obtain ⟨γ⟩ := h
  set eA := (orthogonalGroupToLinearIsometryEquiv A).toLinearIsometry
  set eB := (orthogonalGroupToLinearIsometryEquiv B).toLinearIsometry
  -- Evaluation is continuous on `Diff(Sⁿ)`, so the path is a homotopy of maps of the sphere.
  let H : TopCat.Homotopy (TopCat.ofHom ⟨eA.unitSphereMap, eA.continuous_unitSphereMap⟩)
      (TopCat.ofHom ⟨eB.unitSphereMap, eB.continuous_unitSphereMap⟩) :=
    { toFun := fun p ↦ γ p.1 p.2
      continuous_toFun := continuous_eval.comp (γ.continuous.prodMap continuous_id)
      map_zero_left := fun x ↦ Subtype.ext (by simp [eA])
      map_one_left := fun x ↦ Subtype.ext (by simp [eB]) }
  -- The two maps act on reduced homology `Hₙ(Sⁿ; ℤ)` by the signs of the determinants.
  have hH := reducedSingularHomologyFunctor_map_eq_of_homotopy (ModuleCat.of ℤ ℤ) H n
  rw [reducedSingularHomologyFunctor_map_unitSphereMap _ finrank_euclideanSpace_fin eA,
    reducedSingularHomologyFunctor_map_unitSphereMap _ finrank_euclideanSpace_fin eB,
    det_orthogonalGroupToLinearIsometryEquiv, det_orthogonalGroupToLinearIsometryEquiv] at hH
  -- Read both sides through the reduced-homology isomorphism `Hₙ(Sⁿ; ℤ) ≅ ℤ` and evaluate at `1`.
  let e := reducedSingularHomologySphereIso (ModuleCat.of ℤ ℤ)
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)
  have hsign := congrArg (fun φ ↦ (e.inv ≫ φ ≫ e.hom).hom (1 : ℤ)) hH
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp,
    Iso.inv_hom_id, ModuleCat.hom_zsmul, ModuleCat.hom_id, LinearMap.smul_apply,
    LinearMap.id_apply, smul_eq_mul, mul_one] at hsign
  rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup A.2 with hA | hA <;>
    rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup B.2 with hB | hB <;>
    simp_all

/-- **The isotopy classes of orthogonal transformations of a sphere.** The restrictions of two
orthogonal transformations of `ℝⁿ⁺¹` to `Sⁿ` are joined by a path of `C^m` diffeomorphisms
exactly when the two matrices have the same determinant. So the map `π₀ O(n + 1) → π₀ Diff(Sⁿ)`
is injective, and its image consists of two path components. -/
theorem joined_orthogonalToDiffSphere_iff {A B : Matrix.orthogonalGroup (Fin (n + 1)) ℝ} :
    Joined (orthogonalToDiffSphere n m A) (orthogonalToDiffSphere n m B) ↔
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).det =
        (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).det :=
  ⟨det_eq_of_joined_orthogonalToDiffSphere, fun h ↦
    (Matrix.joined_orthogonalGroup_iff_det_eq.2 h).map (continuous_orthogonalToDiffSphere n m)⟩

/-- An orthogonal transformation of determinant `-1`, such as a reflection, is not isotopic to the
identity as a diffeomorphism of the sphere. -/
theorem not_joined_one_orthogonalToDiffSphere_of_det_eq_neg_one
    {A : Matrix.orthogonalGroup (Fin (n + 1)) ℝ}
    (hA : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).det = -1) :
    ¬ Joined 1 (orthogonalToDiffSphere n m A) := by
  rw [← map_one (orthogonalToDiffSphere n m), joined_orthogonalToDiffSphere_iff, hA]
  norm_num

/-- **The diffeomorphism group of a sphere is not path-connected**, for the weak Whitney `C^m`
topology: a reflection of `Sⁿ` is not isotopic to the identity. -/
theorem not_pathConnectedSpace_diff_sphere :
    ¬ PathConnectedSpace (Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) :=
  fun h ↦ not_joined_one_orthogonalToDiffSphere_of_det_eq_neg_one
    (det_orthogonalDiagonalReflection ℝ 0) (h.joined _ _)

end Orthogonal

/-! ### Cerf's theorem -/

/-- **Cerf's theorem**, `π₀ Diff⁺(S³) = 0`, in orientation-free form: every smooth
diffeomorphism of the three-sphere is joined, in the weak Whitney topology, to the restriction of
an orthogonal transformation of `ℝ⁴`. Together with
`TauCeti.joined_orthogonalToDiffSphere_iff` this says that `Diff(S³)` has two path components,
the isotopy classes of the identity and of a reflection
(`TauCeti.cerfTheorem_iff_natCard_zerothHomotopy_eq_two`). It is stated, not proved. -/
def CerfTheorem : Prop :=
  ∀ f : Diff (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞,
    ∃ A : Matrix.orthogonalGroup (Fin 4) ℝ, Joined (orthogonalToDiffSphere 3 ∞ A) f

/-- **The Smale conjecture implies Cerf's theorem.** A homotopy equivalence is surjective on path
components: if `g` is a homotopy inverse of the inclusion `O(4) → Diff(S³)`, then every `f` is
joined to the image of `g f` by the homotopy from the composite to the identity. -/
theorem SmaleConjecture.cerfTheorem (h : SmaleConjecture) : CerfTheorem := by
  obtain ⟨g, -, ⟨H⟩⟩ := smaleConjecture_iff_exists_homotopyInverse.1 h
  exact fun f ↦ ⟨g f, ⟨(H.evalAt f).cast (by simp) rfl⟩⟩

/-- The class in `π₀ Diff(S³)` of the diffeomorphism induced by an orthogonal transformation is
that of the identity or that of the reflection `TauCeti.orthogonalDiagonalReflection`. -/
private lemma joined_orthogonalToDiffSphere_one_or_reflection
    (A : Matrix.orthogonalGroup (Fin 4) ℝ) :
    Joined 1 (orthogonalToDiffSphere 3 ∞ A) ∨
      Joined (orthogonalToDiffSphere 3 ∞ (orthogonalDiagonalReflection ℝ 0))
        (orthogonalToDiffSphere 3 ∞ A) := by
  rw [← map_one (orthogonalToDiffSphere 3 ∞), joined_orthogonalToDiffSphere_iff,
    joined_orthogonalToDiffSphere_iff, det_orthogonalDiagonalReflection]
  rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup A.2 with hA | hA <;> simp [hA]

/-- **Cerf's theorem as a count of path components.** Cerf's theorem holds exactly when the
diffeomorphism group of `S³` has two path components. -/
theorem cerfTheorem_iff_natCard_zerothHomotopy_eq_two :
    CerfTheorem ↔
      Nat.card (ZerothHomotopy (Diff (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞)) = 2 := by
  set ρ := orthogonalToDiffSphere 3 ∞ (orthogonalDiagonalReflection ℝ 0)
  have hmk : ∀ f g : Diff (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞,
      ZerothHomotopy.mk f = ZerothHomotopy.mk g ↔ Joined f g := fun _ _ ↦ Quotient.eq
  have hρ : ZerothHomotopy.mk ρ ≠ ZerothHomotopy.mk 1 := fun h ↦
    not_joined_one_orthogonalToDiffSphere_of_det_eq_neg_one
      (det_orthogonalDiagonalReflection ℝ 0) ((hmk _ _).1 h).symm
  rw [Nat.card_eq_two_iff' (ZerothHomotopy.mk 1)]
  constructor
  · -- Every class is that of the identity or of the reflection.
    refine fun h ↦ ⟨ZerothHomotopy.mk ρ, hρ, fun c hc ↦ ?_⟩
    induction c with | mk f => ?_
    obtain ⟨A, hA⟩ := h f
    rcases joined_orthogonalToDiffSphere_one_or_reflection A with h1 | h1
    · exact (hc ((hmk _ _).2 (h1.trans hA).symm)).elim
    · exact ((hmk _ _).2 (h1.trans hA)).symm
  · -- Conversely, a class other than that of the identity is that of the reflection.
    rintro ⟨c, -, hc⟩ f
    by_cases hf : ZerothHomotopy.mk f = ZerothHomotopy.mk 1
    · exact ⟨1, by rw [map_one]; exact ((hmk _ _).1 hf).symm⟩
    · refine ⟨orthogonalDiagonalReflection ℝ 0, (hmk _ _).1 ?_⟩
      exact (hc _ hρ).trans (hc _ hf).symm

end TauCeti
