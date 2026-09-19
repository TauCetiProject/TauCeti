/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Basis
public import TauCeti.RepresentationTheory.ProjectiveRepresentation.Basic

/-!
# Projective representations in matrix projective linear groups

A projective representation is most naturally described without coordinates, as a family of
linear automorphisms whose products agree up to scalar.  After choosing a finite basis, each
automorphism is an invertible matrix, and quotienting by scalar matrices turns that family into an
honest homomorphism to Mathlib's projective general linear group.

`TauCeti.IsProjectiveRep.toPGL` performs this passage.  Its value is unchanged when the chosen
lift is rescaled.  Conversely, every homomorphism to `PGL` admits a normalized lift with a factor
set, so the basis-free and matrix descriptions carry the same projective actions.

## Main definitions

* `TauCeti.IsProjectiveRep.toPGL`: the homomorphism to `PGL` determined by a projective
  representation after choosing a basis.

## Main results

* `TauCeti.IsProjectiveRep.toPGL_rescale`: rescaling a lift does not change its map to `PGL`.
* `MonoidHom.exists_isProjectiveRep_toPGL_eq`: every homomorphism to `PGL` is obtained from a
  projective representation on the coordinate module.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985), Ch. 1.
* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Ch. 11.
-/

public section

namespace TauCeti

open scoped MatrixGroups

universe u v w

variable {k : Type u} {G : Type v} {V : Type w} {ι : Type*}
  [CommRing k] [Monoid G] [AddCommGroup V] [Module k V] [Fintype ι] [DecidableEq ι]

section ToPGL

variable {ρ : G → V ≃ₗ[k] V} {α : G → G → kˣ}

/-- A projective representation on a finite free module gives a homomorphism to Mathlib's matrix
projective general linear group after a basis is chosen.  The quotient kills exactly the scalar
factor in the multiplication law. -/
noncomputable def IsProjectiveRep.toPGL (h : IsProjectiveRep ρ α)
    (b : Module.Basis ι k V) : G →* PGL(ι, k) where
  toFun g := Matrix.ProjGenLinGroup.mk (b.toGL (ρ g))
  map_one' := by
    rw [h.map_one, _root_.map_one]
    exact Matrix.ProjGenLinGroup.mk_one
  map_mul' g₁ g₂ := by
    rw [← map_mul]
    apply (Matrix.ProjGenLinGroup.mk_eq_mk_iff).2
    refine ⟨α g₁ g₂, ?_⟩
    rw [← Module.Basis.toGL_smulOfUnit b (α g₁ g₂), ← map_mul, ← map_mul]
    congr 1
    ext x
    simpa only [LinearEquiv.mul_apply, LinearEquiv.smulOfUnit_apply, map_smul, Units.smul_def]
      using (h.mul_apply g₁ g₂ x).symm

/-- The homomorphism to `PGL` is represented by the matrix of the chosen lift. -/
@[simp]
theorem IsProjectiveRep.toPGL_apply (h : IsProjectiveRep ρ α)
    (b : Module.Basis ι k V) (g : G) :
    h.toPGL b g = Matrix.ProjGenLinGroup.mk (b.toGL (ρ g)) :=
  (rfl)

/-- Rescaling a projective lift by units does not change the homomorphism to `PGL` that it
represents. -/
theorem IsProjectiveRep.toPGL_rescale (h : IsProjectiveRep ρ α) (b : Module.Basis ι k V)
    (c : G → kˣ) (hc : c 1 = 1) :
    (h.rescale c hc).toPGL b = h.toPGL b := by
  ext g
  rw [toPGL_apply, toPGL_apply, Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨(c g)⁻¹, ?_⟩
  rw [← Module.Basis.toGL_smulOfUnit b (c g)⁻¹, ← map_mul]
  congr 1
  ext x
  simp [LinearEquiv.mul_apply, LinearEquiv.trans_apply, LinearEquiv.smulOfUnit_apply,
    map_smul, smul_smul, ← Units.val_mul]

/-!
## Lifting a homomorphism from `PGL`

A representative is chosen for every projective matrix, with the representative of the identity
fixed to be the identity matrix.  Comparing the representative of a product with the product of
the representatives supplies the factor set.
-/

section FromPGL

private noncomputable def pglLift (q : G →* PGL(ι, k)) (g : G) : GL ι k :=
  by
    classical
    exact if g = 1 then 1 else Classical.choose (Matrix.ProjGenLinGroup.mk_surjective (q g))

private theorem pglLift_one (q : G →* PGL(ι, k)) : pglLift q 1 = 1 := by
  classical
  simp [pglLift]

private theorem mk_pglLift (q : G →* PGL(ι, k)) (g : G) :
    Matrix.ProjGenLinGroup.mk (pglLift q g) = q g := by
  classical
  by_cases hg : g = 1
  · subst g
    simp [pglLift]
  · simpa only [pglLift, hg, ↓reduceIte] using
      Classical.choose_spec (Matrix.ProjGenLinGroup.mk_surjective (q g))

private theorem mk_pglLift_mul (q : G →* PGL(ι, k)) (g₁ g₂ : G) :
    Matrix.ProjGenLinGroup.mk (pglLift q g₁ * pglLift q g₂) =
      Matrix.ProjGenLinGroup.mk (pglLift q (g₁ * g₂)) := by
  rw [map_mul, mk_pglLift, mk_pglLift, mk_pglLift, q.map_mul]

private noncomputable def pglComparisonScalar (q : G →* PGL(ι, k)) (g₁ g₂ : G) : kˣ :=
  Classical.choose ((Matrix.ProjGenLinGroup.mk_eq_mk_iff).1 (mk_pglLift_mul q g₁ g₂))

private theorem pglLift_mul_scalar (q : G →* PGL(ι, k)) (g₁ g₂ : G) :
    pglLift q g₁ * pglLift q g₂ * Matrix.GeneralLinearGroup.scalar ι
      (pglComparisonScalar q g₁ g₂) = pglLift q (g₁ * g₂) :=
  Classical.choose_spec ((Matrix.ProjGenLinGroup.mk_eq_mk_iff).1 (mk_pglLift_mul q g₁ g₂))

private theorem pglLift_mul (q : G →* PGL(ι, k)) (g₁ g₂ : G) :
    pglLift q g₁ * pglLift q g₂ =
      Matrix.GeneralLinearGroup.scalar ι (pglComparisonScalar q g₁ g₂)⁻¹ *
        pglLift q (g₁ * g₂) := by
  calc
    pglLift q g₁ * pglLift q g₂ =
        (pglLift q g₁ * pglLift q g₂ *
          Matrix.GeneralLinearGroup.scalar ι (pglComparisonScalar q g₁ g₂)) *
            Matrix.GeneralLinearGroup.scalar ι (pglComparisonScalar q g₁ g₂)⁻¹ := by
              simp
    _ = pglLift q (g₁ * g₂) *
        Matrix.GeneralLinearGroup.scalar ι (pglComparisonScalar q g₁ g₂)⁻¹ := by
          rw [pglLift_mul_scalar]
    _ = Matrix.GeneralLinearGroup.scalar ι (pglComparisonScalar q g₁ g₂)⁻¹ *
        pglLift q (g₁ * g₂) :=
      (Matrix.GeneralLinearGroup.scalar_commute (n := ι)
        (pglComparisonScalar q g₁ g₂)⁻¹ (pglLift q (g₁ * g₂))).symm

private noncomputable def pglLinearLift (q : G →* PGL(ι, k)) (g : G) :
    (ι → k) ≃ₗ[k] ι → k :=
  (Pi.basisFun k ι).toGL.symm (pglLift q g)

private theorem toGL_pglLinearLift (q : G →* PGL(ι, k)) (g : G) :
    (Pi.basisFun k ι).toGL (pglLinearLift q g) = pglLift q g :=
  MulEquiv.apply_symm_apply _ _

private theorem pglLinearLift_one (q : G →* PGL(ι, k)) : pglLinearLift q 1 = 1 := by
  rw [pglLinearLift, pglLift_one, map_one]

private theorem pglLinearLift_mul_apply (q : G →* PGL(ι, k)) (g₁ g₂ : G) (x : ι → k) :
    pglLinearLift q g₁ (pglLinearLift q g₂ x) =
      (((pglComparisonScalar q g₁ g₂)⁻¹ : kˣ) : k) • pglLinearLift q (g₁ * g₂) x := by
  have hmul : pglLinearLift q g₁ * pglLinearLift q g₂ =
      LinearEquiv.smulOfUnit (pglComparisonScalar q g₁ g₂)⁻¹ *
        pglLinearLift q (g₁ * g₂) := by
    apply (Pi.basisFun k ι).toGL.injective
    rw [map_mul, map_mul, Module.Basis.toGL_smulOfUnit, toGL_pglLinearLift, toGL_pglLinearLift,
      toGL_pglLinearLift]
    exact pglLift_mul q g₁ g₂
  exact DFunLike.congr_fun hmul x

end FromPGL

end ToPGL

end TauCeti

namespace MonoidHom

open TauCeti

open scoped MatrixGroups

variable {k G ι : Type*} [CommRing k] [Monoid G] [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Every homomorphism to a matrix projective general linear group is represented by a normalized
projective lift on the coordinate module.  The nonempty-index hypothesis excludes the zero module,
where scalar factors cannot be recovered faithfully from their action. -/
theorem exists_isProjectiveRep_toPGL_eq (q : G →* PGL(ι, k)) :
    ∃ (ρ : G → (ι → k) ≃ₗ[k] ι → k) (α : G → G → kˣ)
      (h : IsProjectiveRep ρ α), h.toPGL (Pi.basisFun k ι) = q := by
  refine ⟨pglLinearLift q, fun g₁ g₂ ↦ (pglComparisonScalar q g₁ g₂)⁻¹,
    IsProjectiveRep.of_map_one_mul_apply (pglLinearLift_one q) (pglLinearLift_mul_apply q), ?_⟩
  ext g
  rw [IsProjectiveRep.toPGL_apply, toGL_pglLinearLift, mk_pglLift]

end MonoidHom
