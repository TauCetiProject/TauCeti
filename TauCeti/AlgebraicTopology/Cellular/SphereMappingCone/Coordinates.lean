/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.SphereMappingCone.Basic

/-!
# Oriented cellular coordinates for a sphere mapping cone

For an attaching map `f : Sⁿ⁺¹ → Sⁿ⁺¹`, the two positive-dimensional cellular chain groups of
`Sⁿ⁺¹ ∪_f Dⁿ⁺²` are copies of the coefficient ring. The characteristic-map coordinates give
boundary coefficient `m * u`, where `m` is the degree of `f` and `u` is an orientation unit
independent of `f`. Rescale the lower coordinate by `u⁻¹`, leaving the top cell unchanged.
In these coordinates the cellular differential is exactly right multiplication by `m`.
Over the integers this rescaling is just a choice of sign for the lower cell.

The coordinate equivalences and their inverse formulas keep the actual cellular chain groups
visible. Coefficients may be any ring, including a noncommutative ring: integer degrees are
central, and coordinates act by right multiplication.

The construction uses `TauCeti.exists_cellularIncidence_sphereMappingCone_eq_mul` and
`TauCeti.cellularChainCoord`. See Hatcher, *Algebraic Topology*, Section 2.2, for the cellular
boundary calculation of `Sⁿ ∪_f eⁿ⁺¹`.
-/

public section

noncomputable section

open CategoryTheory Metric Topology Topology.RelCWComplex

universe u

namespace TauCeti

variable {ι : Type u} [Fintype ι] {n : ℕ} (h : Fintype.card ι = n + 1 + 1)
  (R : Type u) [Ring R]
  (b : OrthonormalBasis (Fin (n + 1 + 1)) ℝ (EuclideanSpace ℝ ι))
  (i : letI := sphereCWComplex h; cell (sphere (0 : EuclideanSpace ℝ ι) 1) (n + 1))

/-- The orientation unit comparing the sphere generator determined by `b` with the
characteristic-map generator of `i`. It is chosen once, independently of the attaching map. -/
def sphereMappingConeOrientationUnit : Rˣ :=
  (exists_cellularIncidence_sphereMappingCone_eq_mul h R b i).choose

variable (f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 1 + 1))) 1,
  sphere (0 : EuclideanSpace ℝ ι) 1))

/-- The chosen orientation unit accounts for the difference between the incidence coefficient
and the degree measured with the sphere generator determined by `b`. -/
lemma cellularIncidence_sphereMappingCone_eq_degree_mul (m : ℤ)
    (hf : (reducedSingularHomologyTopCatSphereIso (ModuleCat.of R R) (n + 1)).inv ≫
        (reducedSingularHomologyFunctor (ModuleCat.of R R) (n + 1)).map
          (TopCat.ofHom (f.comp ⟨ULift.down, continuous_uliftDown⟩)) =
      m • (reducedSingularHomologySphereIso (ModuleCat.of R R) b).inv) :
    letI := sphereMappingConeCWComplex h f
    cellularIncidence (sphereMappingCone f) R (n + 1)
        (sphereMappingConeSphereCell h f i) (sphereMappingConeTopCell h f) =
      (m : R) * sphereMappingConeOrientationUnit h R b i :=
  (exists_cellularIncidence_sphereMappingCone_eq_mul h R b i).choose_spec f m hf

private lemma subsingleton_sphereCell :
    letI := sphereMappingConeCWComplex h f
    Subsingleton (cell (sphereMappingCone f) (n + 1)) := by
  let := sphereMappingConeCWComplex h f
  have hc := nat_card_cell_sphereMappingConeCWComplex h f (n + 1)
  have hc' : Nat.card (cell (sphereMappingCone f) (n + 1)) = 1 := by
    simpa using hc
  exact (Nat.card_eq_one_iff_unique.mp hc').1

private lemma subsingleton_topCell :
    letI := sphereMappingConeCWComplex h f
    Subsingleton (cell (sphereMappingCone f) (n + 1 + 1)) := by
  let := sphereMappingConeCWComplex h f
  exact ⟨fun a c ↦ (eq_sphereMappingConeTopCell h f a).trans
    (eq_sphereMappingConeTopCell h f c).symm⟩

/-- The coordinate of the top cell of the sphere mapping cone, with its characteristic-map
orientation unchanged. -/
def sphereMappingConeTopCoord :
    letI := sphereMappingConeCWComplex h f
    (cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)).X (n + 1 + 1) ≃ₗ[R] R := by
  letI := sphereMappingConeCWComplex h f
  letI := subsingleton_topCell h f
  exact cellularChainCoord (sphereMappingCone f) R (sphereMappingConeTopCell h f)

/-- The coordinate of the sphere cell of the mapping cone, normalized to the orientation
specified by `b`. The normalization is independent of the attaching map. -/
def sphereMappingConeSphereCoord :
    letI := sphereMappingConeCWComplex h f
    (cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)).X (n + 1) ≃ₗ[R] R := by
  letI := sphereMappingConeCWComplex h f
  letI := subsingleton_sphereCell h f
  exact (cellularChainCoord (sphereMappingCone f) R (sphereMappingConeSphereCell h f i)).trans
    ((sphereMappingConeOrientationUnit h R b i)⁻¹.mulRightLinearEquiv R)

/-- The top coordinate sends the characteristic-map generator to `1`. -/
@[simp]
lemma sphereMappingConeTopCoord_basis :
    letI := sphereMappingConeCWComplex h f
    sphereMappingConeTopCoord h R f
      (eqToHom (cellularChainComplex_X (sphereMappingCone f) (ModuleCat.of R R) _).symm
        ((cellularChainGroupIso (sphereMappingCone f) (ModuleCat.of R R) (n + 1 + 1)).inv
          (Limits.Sigma.ι (fun _ ↦ ModuleCat.of R R) (sphereMappingConeTopCell h f) 1))) = 1 := by
  let := sphereMappingConeCWComplex h f
  let := subsingleton_topCell h f
  rw [sphereMappingConeTopCoord]
  simpa only [cellularChainBasis_apply] using
    cellularChainCoord_cellularChainBasis (sphereMappingCone f) R (sphereMappingConeTopCell h f)

/-- The lower coordinate sends the characteristic-map generator to the inverse orientation
unit. -/
@[simp]
lemma sphereMappingConeSphereCoord_basis :
    letI := sphereMappingConeCWComplex h f
    sphereMappingConeSphereCoord h R b i f
      (eqToHom (cellularChainComplex_X (sphereMappingCone f) (ModuleCat.of R R) _).symm
        ((cellularChainGroupIso (sphereMappingCone f) (ModuleCat.of R R) (n + 1)).inv
          (Limits.Sigma.ι (fun _ ↦ ModuleCat.of R R) (sphereMappingConeSphereCell h f i) 1))) =
      ↑(sphereMappingConeOrientationUnit h R b i)⁻¹ := by
  let := sphereMappingConeCWComplex h f
  let := subsingleton_sphereCell h f
  rw [sphereMappingConeSphereCoord, LinearEquiv.trans_apply,
    Units.mulRightLinearEquiv_apply, ← cellularChainBasis_apply,
    cellularChainCoord_cellularChainBasis, one_mul]

/-- Inverse top coordinates are multiples of the characteristic-map generator. -/
@[simp]
lemma sphereMappingConeTopCoord_symm_apply (r : R) :
    letI := sphereMappingConeCWComplex h f
    (sphereMappingConeTopCoord h R f).symm r =
      eqToHom (cellularChainComplex_X (sphereMappingCone f) (ModuleCat.of R R) _).symm
        (r • cellularChainBasis (sphereMappingCone f) R (n + 1 + 1)
          (sphereMappingConeTopCell h f)) := by
  let := sphereMappingConeCWComplex h f
  let := subsingleton_topCell h f
  exact cellularChainCoord_symm_apply _ _ _ _

/-- Inverse lower coordinates are multiples of the orientation-normalized sphere generator. -/
@[simp]
lemma sphereMappingConeSphereCoord_symm_apply (r : R) :
    letI := sphereMappingConeCWComplex h f
    (sphereMappingConeSphereCoord h R b i f).symm r =
      eqToHom (cellularChainComplex_X (sphereMappingCone f) (ModuleCat.of R R) _).symm
        ((r * sphereMappingConeOrientationUnit h R b i) •
          cellularChainBasis (sphereMappingCone f) R (n + 1)
            (sphereMappingConeSphereCell h f i)) := by
  let := sphereMappingConeCWComplex h f
  let := subsingleton_sphereCell h f
  simp only [sphereMappingConeSphereCoord, LinearEquiv.symm_trans_apply,
    Units.mulRightLinearEquiv_apply, Units.symm_mulRightLinearEquiv,
    inv_inv, cellularChainCoord_symm_apply]

/-- **The cellular differential in oriented two-cell coordinates is multiplication by the
attaching degree.** The top coordinate is fixed by its characteristic map, and the lower
coordinate is normalized once for all attaching maps. -/
theorem sphereMappingConeSphereCoord_d (m : ℤ)
    (hf : (reducedSingularHomologyTopCatSphereIso (ModuleCat.of R R) (n + 1)).inv ≫
        (reducedSingularHomologyFunctor (ModuleCat.of R R) (n + 1)).map
          (TopCat.ofHom (f.comp ⟨ULift.down, continuous_uliftDown⟩)) =
      m • (reducedSingularHomologySphereIso (ModuleCat.of R R) b).inv) :
    letI := sphereMappingConeCWComplex h f
    ∀ x : (cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)).X (n + 1 + 1),
      sphereMappingConeSphereCoord h R b i f
          ((cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)).d
            (n + 1 + 1) (n + 1) x) =
        sphereMappingConeTopCoord h R f x * (m : R) := by
  let := sphereMappingConeCWComplex h f
  let := subsingleton_sphereCell h f
  let := subsingleton_topCell h f
  intro x
  rw [sphereMappingConeSphereCoord, LinearEquiv.trans_apply,
    Units.mulRightLinearEquiv_apply, cellularChainCoord_d,
    cellularIncidence_sphereMappingCone_eq_degree_mul h R b i f m hf]
  simp [sphereMappingConeTopCoord, mul_assoc]

end TauCeti
