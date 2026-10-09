/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Kernel
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Conjugation
import Mathlib.RingTheory.AdjoinRoot
import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Quotient
import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Reduced
import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.FaithfullyFlat

/-!
# `SLₙ → PGLₙ` is a central isogeny

The conjugation homomorphism `SLₙ → PGLₙ` is the central isogeny from the simply connected form to
the adjoint form of type `Aₙ₋₁` (for `n ≥ 1`). Over every commutative base ring, and in every rank,
this file proves:

* its coordinate morphism `O(PGLₙ) → O(SLₙ)` is finite;
* its scheme-theoretic kernel is central;
* every point of `PGLₙ` lifts to `SLₙ` after a faithfully flat, finitely presented extension of
  its value algebra. Hence `PGLₙ` is the fppf quotient of `SLₙ` by that kernel, and the coordinate
  morphism is injective, that is, `SLₙ → PGLₙ` is schematically dominant.

Over a field these give the three conditions of `TauCeti.CommHopfAlgCat.IsCentralIsogeny`:
faithful flatness follows from injectivity and geometric reducedness of `PGLₙ`.

## Main declarations

* `TauCeti.SpecialLinear.finite_conjugationMap`: the coordinate morphism of `SLₙ → PGLₙ` is
  finite.
* `TauCeti.SpecialLinear.isCentral_kernelHopfIdeal_conjugationMap`: the kernel of `SLₙ → PGLₙ`
  is central.
* `TauCeti.SpecialLinear.exists_lift_conjugationMap`: points of `PGLₙ` lift to `SLₙ`
  fppf-locally.
* `TauCeti.SpecialLinear.isIso_kernelFppfQuotientHom_conjugationMap`: `PGLₙ` is the fppf quotient
  of `SLₙ` by the kernel of `SLₙ → PGLₙ`.
* `TauCeti.SpecialLinear.injective_conjugationMap`: `SLₙ → PGLₙ` is schematically dominant.
* `TauCeti.SpecialLinear.isCentralIsogeny_conjugationMap`: over a field, `SLₙ → PGLₙ` is a
  central isogeny.

## Implementation notes

A point of `PGLₙ` lifts Zariski-locally to a point `g` of `GLₙ`
(`TauCeti.ProjectiveGeneralLinear.exists_lift_conjugationMap`). Adjoining an `n`-th root `s` of
`(det g)⁻¹` is a free extension of rank `n`, hence faithfully flat and finitely presented, and over
it `s • g` has determinant one and the same inner automorphism of the matrix algebra as `g`.

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

section Lift

variable {R : Type u} [CommRing R]

/-- A point `z` of `GLₙ` and a determinant-one matrix `h` with the same inner automorphism of the
matrix algebra have the same image in `PGLₙ`. -/
private theorem comp_conjugationMap_eq_of_innerAut_eq {B : CommAlgCat.{u} R}
    (z : GeneralLinear.coordinateHopfAlgebra R n →ₐ[R] B)
    (h : Matrix.SpecialLinearGroup (Fin n) B)
    (hh : Matrix.GeneralLinearGroup.innerAut (Matrix.SpecialLinearGroup.toGL h) =
      Matrix.GeneralLinearGroup.innerAut (GeneralLinear.pointsMulEquiv n (toConv z))) :
    ((pointsMulEquiv (R := R) (A := B) n).symm h).ofConv.comp
        ((conjugationMap n R).hom :
          ProjectiveGeneralLinear.coordinateHopfAlgebra n R →ₐ[R] coordinateHopfAlgebra R n) =
      z.comp ((ProjectiveGeneralLinear.conjugationMap n R).hom :
        ProjectiveGeneralLinear.coordinateHopfAlgebra n R →ₐ[R]
          GeneralLinear.coordinateHopfAlgebra R n) := by
  apply toConv_injective
  apply (ProjectiveGeneralLinear.pointsMulEquiv n R B).injective
  rw [pointsMulEquiv_conjugationMap, MulEquiv.apply_symm_apply, hh, ← ofConv_toConv z,
    ProjectiveGeneralLinear.pointsMulEquiv_conjugationMap, toConv_ofConv]

/-- Over a nontrivial value algebra and in positive rank, every point `z` of `GLₙ` has the same
image in `PGLₙ` as a point of `SLₙ`, after adjoining an `n`-th root `s` of the inverse determinant
of `z`: the matrix `s • z` has determinant one and the same inner automorphism as `z`. This
extension is free of rank `n`, hence faithfully flat and finitely presented. -/
private theorem exists_rescale_conjugationMap {B : CommAlgCat.{u} R} [Nontrivial B] (hn : n ≠ 0)
    (z : GeneralLinear.coordinateHopfAlgebra R n →ₐ[R] B) :
    ∃ (C : CommAlgCat.{u} R) (ψ : B ⟶ C) (w : coordinateHopfAlgebra R n →ₐ[R] C),
      ψ.hom.toRingHom.FaithfullyFlat ∧ ψ.hom.toRingHom.FinitePresentation ∧
        w.comp (conjugationMap n R).hom.toAlgHom =
          ψ.hom.comp (z.comp (ProjectiveGeneralLinear.conjugationMap n R).hom.toAlgHom) := by
  let g := GeneralLinear.pointsMulEquiv n (toConv z)
  let u : (↑B)ˣ := (Matrix.GeneralLinearGroup.det g)⁻¹
  let p : Polynomial B := Polynomial.X ^ n - Polynomial.C (u : B)
  have hp : p.Monic := Polynomial.monic_X_pow_sub_C _ hn
  let ψ : B →ₐ[R] AdjoinRoot p := IsScalarTower.toAlgHom R B (AdjoinRoot p)
  let s := AdjoinRoot.root p
  have hs : s ^ n = ψ u := by
    have := AdjoinRoot.eval₂_root p
    rwa [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero] at this
  have hsu : IsUnit s := (isUnit_pow_iff hn).1 (hs ▸ (Units.isUnit _).map ψ)
  let gψ := Matrix.GeneralLinearGroup.map (ψ : B →+* AdjoinRoot p) g
  let h : Matrix.SpecialLinearGroup (Fin n) (AdjoinRoot p) :=
    ⟨s • (gψ : Matrix (Fin n) (Fin n) (AdjoinRoot p)), by
      rw [Matrix.det_smul, Fintype.card_fin, hs, ← Matrix.GeneralLinearGroup.val_det_apply,
        Matrix.GeneralLinearGroup.map_det, Units.coe_map]
      simp only [MonoidHom.coe_ofClass, RingHom.coe_coe]
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]⟩
  have : Nonempty (Fin p.natDegree) :=
    ⟨⟨0, by rw [Polynomial.natDegree_X_pow_sub_C]; exact Nat.pos_of_ne_zero hn⟩⟩
  have : Module.FaithfullyFlat B (AdjoinRoot p) :=
    .of_linearEquiv _ _ (AdjoinRoot.powerBasisAux' hp).repr
  refine ⟨CommAlgCat.of R (AdjoinRoot p), CommAlgCat.ofHom ψ,
    ((pointsMulEquiv (R := R) (A := CommAlgCat.of R (AdjoinRoot p)) n).symm h).ofConv,
    RingHom.faithfullyFlat_algebraMap_iff.2 this,
    RingHom.finitePresentation_algebraMap.2 inferInstance, ?_⟩
  -- The scalar `s` is central and invertible, so `s • g` and `g` have the same inner automorphism.
  let c : GL (Fin n) (AdjoinRoot p) := Units.map
    (Matrix.scalar (Fin n) : AdjoinRoot p →+* Matrix (Fin n) (Fin n) (AdjoinRoot p)) hsu.unit
  have hc : c ∈ Subgroup.center (GL (Fin n) (AdjoinRoot p)) :=
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2 ⟨s, rfl⟩
  have hgh : Matrix.SpecialLinearGroup.toGL h = c * gψ := Units.ext (by
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    simp [h, c, Matrix.smul_eq_diagonal_mul])
  refine (comp_conjugationMap_eq_of_innerAut_eq n (B := CommAlgCat.of R (AdjoinRoot p))
    (ψ.comp z) h ?_).trans (AlgHom.comp_assoc ψ z _)
  rw [hgh, map_mul, (Matrix.GeneralLinearGroup.innerAut_eq_one_iff c).2 hc, one_mul,
    ← ofConv_toConv z, ← AlgHom.mapValue_apply, GeneralLinear.pointsMulEquiv_mapValue]

/-- **Points of `PGLₙ` lift to `SLₙ` fppf-locally.** Every point of `PGLₙ` lifts through
`SLₙ → PGLₙ` after a faithfully flat, finitely presented extension of its value algebra. -/
theorem exists_lift_conjugationMap (A : CommAlgCat.{u} R)
    (y : ProjectiveGeneralLinear.coordinateHopfAlgebra n R →ₐ[R] A) :
    ∃ (B : CommAlgCat.{u} R) (φ : A ⟶ B) (z : coordinateHopfAlgebra R n →ₐ[R] B),
      φ.hom.toRingHom.FaithfullyFlat ∧ φ.hom.toRingHom.FinitePresentation ∧
        z.comp (conjugationMap n R).hom.toAlgHom = φ.hom.comp y := by
  -- First lift the point to `GLₙ` Zariski-locally, then rescale the lift into `SLₙ`.
  obtain ⟨B, φ, z, hflat, hfp, hz⟩ := ProjectiveGeneralLinear.exists_lift_conjugationMap n A y
  by_cases hM : Subsingleton (Matrix (Fin n) (Fin n) B)
  · -- When the matrix algebra is trivial (`n = 0` or `B = 0`), so is every inner automorphism.
    exact ⟨B, φ, ((pointsMulEquiv (R := R) (A := B) n).symm 1).ofConv, hflat, hfp,
      (comp_conjugationMap_eq_of_innerAut_eq n z 1
        (AlgEquiv.ext fun _ ↦ Subsingleton.elim _ _)).trans hz⟩
  have hn : n ≠ 0 := by
    rintro rfl
    exact hM inferInstance
  have : Nontrivial B := by
    by_contra hB
    rw [not_nontrivial_iff_subsingleton] at hB
    exact hM inferInstance
  obtain ⟨C, ψ, w, hψflat, hψfp, hw⟩ := exists_rescale_conjugationMap n hn z
  refine ⟨C, φ ≫ ψ, w, RingHom.FaithfullyFlat.stableUnderComposition _ _ hflat hψflat,
    RingHom.FinitePresentation.comp hψfp hfp, ?_⟩
  rw [hw, hz, CommAlgCat.hom_comp, AlgHom.comp_assoc]

/-- **`SLₙ → PGLₙ` is an fppf quotient map**: over any commutative ring, the comparison from the
fppf quotient of `SLₙ` by the kernel of the conjugation homomorphism to `PGLₙ` is an isomorphism of
group objects in fppf sheaves. -/
instance isIso_kernelFppfQuotientHom_conjugationMap :
    IsIso (CommHopfAlgCat.kernelFppfQuotientHom (conjugationMap n R)) :=
  CommHopfAlgCat.isIso_kernelFppfQuotientHom_of_exists_lift _ (exists_lift_conjugationMap n)

variable (R) in
/-- **`SLₙ → PGLₙ` is schematically dominant**: over any commutative ring, its coordinate morphism
`O(PGLₙ) → O(SLₙ)` is injective. -/
theorem injective_conjugationMap : Function.Injective (conjugationMap n R).hom := by
  -- Lift the universal point of `PGLₙ` to `SLₙ` over a faithfully flat extension.
  obtain ⟨B, φ, z, hflat, -, hz⟩ := exists_lift_conjugationMap n
    (CommAlgCat.of R (ProjectiveGeneralLinear.coordinateHopfAlgebra n R)) (AlgHom.id R _)
  refine Function.Injective.of_comp (f := z) fun a b hab ↦ hflat.injective ?_
  exact (DFunLike.congr_fun hz a).symm.trans (hab.trans (DFunLike.congr_fun hz b))

end Lift

/-- **`SLₙ → PGLₙ` is a central isogeny** over a field, in every rank: it is finite with central
kernel, and faithfully flat because it is schematically dominant and `PGLₙ` is geometrically
reduced. -/
theorem isCentralIsogeny_conjugationMap (k : Type u) [Field k] :
    CommHopfAlgCat.IsCentralIsogeny (conjugationMap n k) := by
  have hinj := injective_conjugationMap n k
  exact (CommHopfAlgCat.isCentralIsogeny_iff _).mpr ⟨finite_conjugationMap n k,
    (CommHopfAlgCat.faithfullyFlat_iff_injective_of_isGeometricallyReduced
      (conjugationMap n k)).mpr hinj,
    isCentral_kernelHopfIdeal_conjugationMap n k⟩

end

end TauCeti.SpecialLinear
