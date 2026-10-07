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

The conjugation homomorphism `SLₙ → PGLₙ` is the standard central isogeny from the simply
connected form to the adjoint form of type `Aₙ₋₁`. This file proves the two parts of that
statement that hold over every commutative base ring, in every rank:

* its coordinate morphism `O(PGLₙ) → O(SLₙ)` is finite;
* its scheme-theoretic kernel is central.

Finiteness is integrality of the generic matrix `X` of `SLₙ` and of its inverse `Y`. The
coordinates of `PGLₙ` pull back to the products `Xₚᵢ Yⱼq`, so for a fixed entry `c` of `X` the
scaled matrix `c • Y` has all its entries in the image of `O(PGLₙ)`. Since `det Y = 1`, its
determinant `cⁿ` lies in that image as well, so `c` is integral. The same argument with the roles
of `X` and `Y` exchanged applies to the entries of `Y`, and these entries generate `O(SLₙ)`.

Over a field, the target `PGLₙ` is geometrically reduced as soon as the coordinate morphism is
injective, since `SLₙ` is smooth. Injectivity then gives faithful flatness. Thus `SLₙ → PGLₙ` is
a central isogeny exactly when its coordinate morphism is injective, that is, when the
homomorphism is schematically dominant.

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
  -- Hence every entry of `X` and of `X⁻¹` is integral over `O(PGLₙ)`.
  have hle := Algebra.adjoin_le (S := (integralClosure P S).restrictScalars R) (s :=
    Set.range (fun ij : Fin n × Fin n ↦ X ij.1 ij.2) ∪
      Set.range (fun ij : Fin n × Fin n ↦ X⁻¹ ij.1 ij.2)) <| by
    rintro _ (⟨⟨i, j⟩, rfl⟩ | ⟨⟨i, j⟩, rfl⟩)
    · refine hint hY (fun l m ↦ ?_) (Fin.pos i)
      simpa using hentry (finProdFinEquiv (i, m)) (finProdFinEquiv (j, l))
    · refine hint hX (fun l m ↦ ?_) (Fin.pos i)
      obtain ⟨x, hx⟩ := hentry (finProdFinEquiv (l, j)) (finProdFinEquiv (m, i))
      exact ⟨x, by simpa [mul_comm] using hx⟩
  rw [adjoin_range_map_genericMatrix_union_range_inv, top_le_iff] at hle
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
