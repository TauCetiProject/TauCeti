/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Conjugation
import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.FaithfullyFlat
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Smooth
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Finiteness and centrality of `SLₙ → PGLₙ`

The conjugation homomorphism `SLₙ → PGLₙ` is the map underlying the expected central isogeny
from the simply connected form to the adjoint form of type `Aₙ₋₁` (for `n ≥ 1`). This file does
not prove that it is a central isogeny. Over every commutative base ring, and in every rank, it
proves:

* its coordinate morphism `O(PGLₙ) → O(SLₙ)` is finite;
* its scheme-theoretic kernel is central.

Over a field, it also reduces the central-isogeny property to injectivity of the coordinate
morphism, as explained below.

Finiteness and centrality are two of the three conditions in
`TauCeti.CommHopfAlgCat.IsCentralIsogeny`. Over a field, the third, faithful flatness, follows
from injectivity of the coordinate morphism. Thus `SLₙ → PGLₙ` is a central isogeny exactly when
its coordinate morphism is injective, that is, when the homomorphism is schematically dominant.
That injectivity is not proved in this file.

## Main declarations

* `TauCeti.SpecialLinear.finite_conjugationMap`: the coordinate morphism of `SLₙ → PGLₙ` is
  finite.
* `TauCeti.SpecialLinear.isCentral_kernelHopfIdeal_conjugationMap`: the kernel of `SLₙ → PGLₙ`
  is central.
* `TauCeti.SpecialLinear.isCentralIsogeny_conjugationMap_iff_injective`: over a field,
  `SLₙ → PGLₙ` is a central isogeny exactly when its coordinate morphism is injective.

## References

* J. S. Milne, *Algebraic Groups* (2017), Examples 5.49 and 21.4, and Proposition 1.70.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.SpecialLinear

universe u v

noncomputable section

variable (n : ℕ)

section Ring

variable (R : Type u) [CommRing R]

/-- **`SLₙ → PGLₙ` is finite**: the special-linear coordinate Hopf algebra is a finite module over
the coordinate Hopf algebra of `PGLₙ`, over every commutative ring and in every rank. -/
theorem finite_conjugationMap : (conjugationMap n R).hom.toAlgHom.Finite := by
  let P := ProjectiveGeneralLinear.coordinateHopfAlgebra n R
  let S := coordinateHopfAlgebra R n
  let φ := (conjugationMap n R).hom.toAlgHom
  let X := (GeneralLinear.genericMatrix R n).map (coordinateMap R n).hom
  let : Algebra P S := φ.toAlgebra
  have : IsScalarTower R P S := .of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  have hX : X.det = 1 := det_map_genericMatrix_coordinateMap R n
  have hY : X⁻¹.det = 1 := by rw [Matrix.det_nonsing_inv, hX, Ring.inverse_one]
  -- The coordinates of `PGLₙ` pull back to the products of an entry of `X` and one of `X⁻¹`.
  have hentry (a c : Fin (n * n)) : ∃ x : P, φ x =
      X (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm c).1 *
        X⁻¹ (finProdFinEquiv.symm c).2 (finProdFinEquiv.symm a).2 :=
    ⟨_, (congrFun (congrFun (map_genericMatrix_conjugationMap n R) a) c).trans
      (ProjectiveGeneralLinear.conjugationMatrix_apply _ _ a c)⟩
  -- If `c • Z` has entries in the image for some `Z` of determinant one, then so does
  -- `cⁿ = det (c • Z)`, so `c` is integral.
  have hint {c : S} {Z : Matrix (Fin n) (Fin n) S} (hZ : Z.det = 1)
      (h : ∀ l m, ∃ x : P, φ x = c * Z l m) (hn : 0 < n) : IsIntegral P c := by
    choose M hM using h
    have hc : φ (Matrix.of M).det = c ^ n := by
      have hsmul : (c • Z).det = c ^ n * Z.det := by rw [Matrix.det_smul, Fintype.card_fin]
      rw [AlgHom.map_det, ← mul_one (c ^ n), ← hZ, ← hsmul]
      congr 1
      ext l m
      rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hM, Matrix.smul_apply,
        smul_eq_mul]
    refine IsIntegral.of_pow hn ?_
    rw [← hc]
    exact isIntegral_algebraMap
  -- Hence every entry of `X` is integral over `O(PGLₙ)`.
  have hle := Algebra.adjoin_le (S := (integralClosure P S).restrictScalars R) (s :=
    Set.range (fun ij : Fin n × Fin n ↦ X ij.1 ij.2)) <| by
    rintro _ ⟨⟨i, j⟩, rfl⟩
    refine hint hY (fun l m ↦ ?_) (Fin.pos i)
    simpa using hentry (finProdFinEquiv (i, m)) (finProdFinEquiv (j, l))
  rw [adjoin_range_map_genericMatrix, top_le_iff] at hle
  have : Algebra.IsIntegral P S := ⟨fun x ↦ by
    have hx : x ∈ (integralClosure P S).restrictScalars R := hle ▸ Algebra.mem_top
    rwa [Subalgebra.mem_restrictScalars, mem_integralClosure_iff] at hx⟩
  have : Algebra.FiniteType P S := .of_restrictScalars_finiteType R P S
  exact Algebra.IsIntegral.finite

/-- **The kernel of `SLₙ → PGLₙ` is central**, over every commutative ring and in every rank:
its points are central special-linear matrices, and this persists under extension of values. -/
theorem isCentral_kernelHopfIdeal_conjugationMap :
    (CommHopfAlgCat.kernelHopfIdeal (conjugationMap n R)).IsCentral := by
  rw [CommHopfAlgCat.isCentral_iff_forall_isCentralPoint]
  intro A g hg
  rw [HopfAlgebra.isCentralPoint_def]
  intro B _ _ χ h
  have hχ := CommHopfAlgCat.mapValue_mem_quotientPointsSubgroup _ _ χ hg
  rw [mem_quotientPointsSubgroup_kernelHopfIdeal_conjugationMap_iff] at hχ
  apply (pointsMulEquiv (R := R) (A := CommAlgCat.of R B) n).injective
  rw [map_mul, map_mul]
  exact (Subgroup.mem_center_iff.mp hχ _).symm

end Ring

/-- **`SLₙ → PGLₙ` is a central isogeny exactly when it is schematically dominant**, that is,
when its coordinate morphism is injective. Over a field, finiteness
and centrality always hold, and once the coordinate morphism is injective, `PGLₙ` inherits
geometric reducedness from the smooth group `SLₙ`, which makes the morphism faithfully flat. -/
@[simp]
theorem isCentralIsogeny_conjugationMap_iff_injective (k : Type u) [Field k] :
    CommHopfAlgCat.IsCentralIsogeny (conjugationMap n k) ↔
      Function.Injective (conjugationMap n k).hom := by
  refine ⟨fun h ↦ h.isIsogeny.injective, fun hinj ↦ ?_⟩
  have : Algebra.IsGeometricallyReduced k (coordinateHopfAlgebra k n) :=
    isGeometricallyReduced_of_smooth k _
  have : Algebra.IsGeometricallyReduced k (ProjectiveGeneralLinear.coordinateHopfAlgebra n k) :=
    .of_injective (conjugationMap n k).hom.toAlgHom hinj
  exact (CommHopfAlgCat.isCentralIsogeny_iff _).mpr ⟨finite_conjugationMap n k,
    (CommHopfAlgCat.faithfullyFlat_iff_injective_of_isGeometricallyReduced _).mpr hinj,
    isCentral_kernelHopfIdeal_conjugationMap n k⟩

end

end TauCeti.SpecialLinear
