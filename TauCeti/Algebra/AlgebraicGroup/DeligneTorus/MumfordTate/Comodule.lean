/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.MumfordTate.Kernel
public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Tate
public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Tautological
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Centralizer.Coordinate
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.PointSeparation
public import TauCeti.Algebra.AlgebraicGroup.Representation.Coordinate
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Intertwiner
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Complex
import TauCeti.FieldTheory.IsAlgClosed.Units

/-!
# Mumford–Tate groups of representations of the Deligne torus

A representation of the Deligne torus `S` on a finite-dimensional real vector space `M`, that is,
an `S`-comodule, together with a basis `b` of `M` indexed by `Fin d`, gives a homomorphism
`h_b : S → GL_{d,ℝ}` (`TauCeti.DeligneTorus.comoduleDeligneHom`). Its target is the real extension
of `GL_{d,ℚ}`, the general linear group of the rational structure spanned by `b`, so it has a
Mumford–Tate group (`TauCeti.DeligneTorus.mumfordTateHopfIdeal`).

This file computes the Mumford–Tate group in the basic examples.

* For a trivial representation, and in particular for the Tate comodule `ℝ(0)`, the Mumford–Tate
  group is trivial; so is the Mumford–Tate group of any `h` into `GL₀`.
* For the Tate comodule `ℝ(m)` with `m ≠ 0`, on which a real point `z ∈ ℂˣ` acts by `|z| ^ (2m)`,
  the Mumford–Tate ideal is zero: `MT = 𝔾ₘ = GL₁`. For `m = 1` this is `ℚ(1)`.
* An endomorphism of the representation whose matrix in the basis is rational puts the
  Mumford–Tate group inside the centralizer of that matrix.
* For the tautological representation of `S` on `ℂ`, in the basis `(1, i)`, a real point
  `a + b i` acts by the matrix `[[a, -b], [b, a]]`. This is `H₁(ℂ/ℤ[i], ℚ)`. The
  multiplication by `i` is an endomorphism of the representation, so the Mumford–Tate group lies
  in the centralizer of `J = [[0, -1], [1, 0]]`: the equations `X₁₁ - X₂₂` and `X₁₂ + X₂₁` lie in
  the Mumford–Tate ideal, and the Mumford–Tate group is not all of `GL₂`.

## Main declarations

* `TauCeti.DeligneTorus.comoduleDeligneHom`: the homomorphism `S → GL_{d,ℝ}` of an `S`-comodule
  with a basis.
* `TauCeti.DeligneTorus.mumfordTateHopfIdeal_comoduleDeligneHom_eq_augmentation` and
  `TauCeti.DeligneTorus.mumfordTateHopfIdeal_tateComodule_zero_eq_augmentation`: trivial
  representations, such as `ℝ(0)`, have trivial Mumford–Tate group.
* `TauCeti.DeligneTorus.centralizerHopfIdeal_le_mumfordTateHopfIdeal_comoduleDeligneHom`: the
  Mumford–Tate group lies in the centralizer of the matrix of an endomorphism defined over `ℚ`.
* `TauCeti.DeligneTorus.mumfordTateHopfIdeal_eq_augmentation_of_zero`: the Mumford–Tate group of
  any homomorphism into `GL₀` is trivial.
* `TauCeti.DeligneTorus.mumfordTateHopfIdeal_tateComodule_eq_bot`: `MT(ℚ(m)) = GL₁` for `m ≠ 0`.
* `TauCeti.DeligneTorus.centralizerHopfIdeal_le_mumfordTateHopfIdeal_tautologicalComodule`,
  `TauCeti.DeligneTorus.genericMatrix_sub_mem_mumfordTateHopfIdeal_tautologicalComodule`,
  `TauCeti.DeligneTorus.genericMatrix_add_mem_mumfordTateHopfIdeal_tautologicalComodule` and
  `TauCeti.DeligneTorus.mumfordTateHopfIdeal_tautologicalComodule_ne_bot`: the Mumford–Tate
  group of `H₁(ℂ/ℤ[i], ℚ)` lies in the centralizer of `J`, a proper subgroup of `GL₂`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, pp. 26–27, and the aside after
  Definition 2.16, p. 31.
-/

public section

open CategoryTheory _root_.CommHopfAlgCat TauCeti.CommHopfAlgCat TauCeti.GeneralLinear WithConv
open scoped TensorProduct

namespace TauCeti.DeligneTorus

/-! ### The homomorphism of a comodule with a basis -/

section Comodule

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {d : ℕ}

section Instance

variable [Comodule ℝ S M]

/-- **The homomorphism `S → GL_{d,ℝ}` of a representation of the Deligne torus with a basis**:
for an `S`-comodule `M` with a basis `b` indexed by `Fin d`, the morphism
`ℝ ⊗[ℚ] O(GL_d) ⟶ O(S)` of commutative Hopf `ℝ`-algebras sending the generic matrix to the
coefficient matrix of `b` (`TauCeti.DeligneTorus.comoduleDeligneHom_one_tmul_X`). Its target is
the real extension of the general linear group of the rational span of `b`. -/
noncomputable def comoduleDeligneHom (b : Module.Basis (Fin d) ℝ M) :
    baseChange (K := ℝ) (coordinateHopfAlgebra ℚ d) ⟶ _root_.CommHopfAlgCat.of ℝ S :=
  (coordinateHopfAlgebraBaseChangeIso ℚ ℝ d).hom ≫
    _root_.CommHopfAlgCat.ofHom (Comodule.coordinateBialgHom (H := S) b)

/-- `comoduleDeligneHom` sends the generic entry `Xᵢⱼ` to the corresponding entry of the
coefficient matrix of the basis. -/
@[simp]
theorem comoduleDeligneHom_one_tmul_X (b : Module.Basis (Fin d) ℝ M) (i j : Fin d) :
    (comoduleDeligneHom b).hom ((1 : ℝ) ⊗ₜ[ℚ]
        coordinateHopfAlgebraAlgEquiv ℚ d (coordinateRingMap ℚ d (MvPolynomial.X (i, j)))) =
      Comodule.coefficientMatrix (C := S) b i j := by
  rw [comoduleDeligneHom, _root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply,
    coordinateHopfAlgebraBaseChangeIso_hom_one_tmul_X, _root_.CommHopfAlgCat.hom_ofHom,
    Comodule.coordinateBialgHom_X]

/-- **Trivial representations have trivial Mumford–Tate group**: if `S` acts trivially on `M`,
the Mumford–Tate ideal of `comoduleDeligneHom b` is the augmentation ideal. -/
theorem mumfordTateHopfIdeal_comoduleDeligneHom_eq_augmentation (b : Module.Basis (Fin d) ℝ M)
    (htriv : ∀ m : M, (‹Comodule ℝ S M›).coact m = m ⊗ₜ[ℝ] (1 : S)) :
    mumfordTateHopfIdeal (comoduleDeligneHom b) =
      HopfIdeal.augmentation ℚ (coordinateHopfAlgebra ℚ d) := by
  rw [mumfordTateHopfIdeal_eq_augmentation_iff]
  intro x
  rw [comoduleDeligneHom, _root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply,
    _root_.CommHopfAlgCat.hom_ofHom,
    Comodule.coordinateBialgHom_eq_unit_comp_counit_of_coact_eq_tmul_one b htriv,
    BialgHom.comp_apply, Bialgebra.counitBialgHom_apply, Bialgebra.unitBialgHom_apply,
    CoalgHomClass.counit_comp_apply]

/-- **Endomorphisms defined over `ℚ` bound the Mumford–Tate group**: if a linear endomorphism
`f` of `M` commutes with the coaction, and its matrix in the basis `b` is a rational matrix `A`,
then the Mumford–Tate group of `comoduleDeligneHom b` lies in the centralizer of `A` in `GL_d`. -/
theorem centralizerHopfIdeal_le_mumfordTateHopfIdeal_comoduleDeligneHom
    (b : Module.Basis (Fin d) ℝ M) (f : M →ₗ[ℝ] M)
    (hf : TensorProduct.map f LinearMap.id ∘ₗ (‹Comodule ℝ S M›).coact =
      (‹Comodule ℝ S M›).coact ∘ₗ f)
    (A : Matrix (Fin d) (Fin d) ℚ) (hA : A.map (algebraMap ℚ ℝ) = LinearMap.toMatrix b b f) :
    centralizerHopfIdeal (coordinateHopfAlgebra ℚ d)
        ((cotangentDualMatrixEquiv (k := ℚ) (n := d)).symm A) ≤
      mumfordTateHopfIdeal (comoduleDeligneHom b) := by
  let : Algebra ℚ S := Algebra.compHom S (algebraMap ℚ ℝ)
  have : IsScalarTower ℚ ℝ S := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  rw [le_mumfordTateHopfIdeal_iff_toIdeal_le_rationalCoordinateKernel,
    centralizerHopfIdeal_toIdeal_eq_map_centralizerIdeal, LinearEquiv.apply_symm_apply,
    Ideal.map_le_iff_le_comap]
  let g : MvPolynomial (Fin d × Fin d) ℚ →ₐ[ℚ] S :=
    ((rationalCoordinateMap (comoduleDeligneHom b)).comp
      ((coordinateHopfAlgebraAlgEquiv ℚ d).toAlgHom.comp (coordinateRingMap ℚ d)).toRingHom
      ).toRatAlgHom
  suffices hg : Matrix.centralizerIdeal A ≤ RingHom.ker g by
    intro x hx
    simpa [g, mem_rationalCoordinateKernel] using hg hx
  rw [Matrix.centralizerIdeal_le_ker_iff]
  have hX : (Matrix.mvPolynomialX (Fin d) (Fin d) ℚ).map g =
      Comodule.coefficientMatrix (C := S) b := by
    ext i j
    simp only [g, Matrix.map_apply, Matrix.mvPolynomialX_apply, RingHom.toRatAlgHom_apply,
      RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.comp_apply,
      AlgEquiv.coe_toAlgHom, rationalCoordinateMap_apply]
    exact comoduleDeligneHom_one_tmul_X b i j
  have hA' : A.map (algebraMap ℚ S) = (LinearMap.toMatrix b b f).map (algebraMap ℝ S) := by
    rw [← hA, Matrix.map_map, IsScalarTower.algebraMap_eq ℚ ℝ S, RingHom.coe_comp]
  rw [hX, hA', commute_iff_eq]
  exact (Module.Basis.map_coact_iff_coefficientMatrix _ _ _).mp hf

end Instance

/-- **The Tate comodule `ℝ(0)` has trivial Mumford–Tate group.** -/
theorem mumfordTateHopfIdeal_tateComodule_zero_eq_augmentation (b : Module.Basis (Fin d) ℝ M) :
    letI := tateComodule M 0
    mumfordTateHopfIdeal (comoduleDeligneHom b) =
      HopfIdeal.augmentation ℚ (coordinateHopfAlgebra ℚ d) := by
  let := tateComodule M 0
  exact mumfordTateHopfIdeal_comoduleDeligneHom_eq_augmentation b fun m ↦ by
    rw [tateComodule_coact_apply, zpow_zero, GroupLike.val_one]

/-- **`MT(ℚ(m)) = GL₁` for `m ≠ 0`.** The Tate comodule `ℝ(m)`, on which a point of `S` acts by
the `m`-th power of its norm, has zero Mumford–Tate ideal in every basis. For `m = 1` this is the
Hodge structure `ℚ(1)` of type `(-1, -1)`. -/
theorem mumfordTateHopfIdeal_tateComodule_eq_bot {m : ℤ} (hm : m ≠ 0)
    (b : Module.Basis (Fin 1) ℝ M) :
    letI := tateComodule M m
    mumfordTateHopfIdeal (comoduleDeligneHom b) = ⊥ := by
  let := tateComodule M m
  -- The values of the norm on complex points of `S` are all of `ℂˣ`, so the rational coordinate
  -- map of `comoduleDeligneHom b` is injective by the Zariski density of `GL₁(ℚ)`.
  refine eq_bot_iff.mpr fun x hx ↦ HopfIdeal.mem_bot.mpr ?_
  have hx0 : (comoduleDeligneHom b).hom ((1 : ℝ) ⊗ₜ[ℚ] x) = 0 :=
    mem_rationalCoordinateKernel.mp
      (mumfordTateHopfIdeal_toIdeal_le_rationalCoordinateKernel _ hx)
  have hcoef : Comodule.coefficientMatrix (C := S) b 0 0 =
      ((normGroupLike ^ m : GroupLike ℝ S) : S) := by
    simp [Comodule.coefficientMatrix_apply]
  refine eq_of_forall_generalLinearToPoint_apply_eq fun g ↦ ?_
  rw [map_zero]
  -- a complex point of `S` whose norm has `m`-th power `det g`
  let := Group.rootableByIntOfRootableByNat ℂˣ
  obtain ⟨w, hw : w ^ m = _⟩ :=
    RootableBy.surjective_pow ℂˣ ℤ hm (Units.map (algebraMap ℚ ℂ).toMonoidHom g.det)
  let p : WithConv (S →ₐ[ℝ] ℂ) := (complexSplitting ℂ).symm (w, 1)
  let φ : coordinateHopfAlgebra ℚ 1 →ₐ[ℚ] ℂ :=
    ((p.ofConv.comp (comoduleDeligneHom b).hom.toAlgHom).restrictScalars ℚ).comp
      Algebra.TensorProduct.includeRight
  have hp : norm ℂ p = w := by
    apply Units.ext
    rw [coe_norm_eq_mul, MulEquiv.apply_symm_apply, Units.val_one, mul_one]
  have hφ : φ = (Algebra.ofId ℚ ℂ).comp (generalLinearToPoint 1 g).ofConv := by
    refine coordinateHopfAlgebra_algHom_ext ℚ 1 fun i j ↦ ?_
    obtain rfl := Subsingleton.elim i 0
    obtain rfl := Subsingleton.elim j 0
    simp only [φ, AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
      AlgHom.restrictScalars_apply, BialgHom.coe_toAlgHom]
    rw [comoduleDeligneHom_one_tmul_X, hcoef, apply_normGroupLike_zpow,
      generalLinearToPoint_apply, hp, hw, Units.coe_map, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.det_unique, Algebra.ofId_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      Fin.default_eq_zero]
  have := DFunLike.congr_fun hφ x
  simp only [φ, AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
    AlgHom.restrictScalars_apply, BialgHom.coe_toAlgHom, hx0, map_zero] at this
  exact (algebraMap ℚ ℂ).injective (by simpa using this.symm)

end Comodule

/-- **The Mumford–Tate group of a homomorphism into `GL₀` is trivial**: `O(GL₀) = ℚ`, so every
homomorphism `S → GL_{0,ℝ}` is trivial. -/
theorem mumfordTateHopfIdeal_eq_augmentation_of_zero
    (h : baseChange (K := ℝ) (coordinateHopfAlgebra ℚ 0) ⟶ _root_.CommHopfAlgCat.of ℝ S) :
    mumfordTateHopfIdeal h = HopfIdeal.augmentation ℚ (coordinateHopfAlgebra ℚ 0) := by
  rw [mumfordTateHopfIdeal_eq_augmentation_iff]
  let : Algebra ℚ S := Algebra.compHom S (algebraMap ℚ ℝ)
  have : IsScalarTower ℚ ℝ S := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have key : h.hom.toAlgHom = (Algebra.ofId ℝ S).comp (Bialgebra.counitAlgHom ℝ _) :=
    Algebra.TensorProduct.ext (Subsingleton.elim _ _)
      (coordinateHopfAlgebra_algHom_ext ℚ 0 fun i ↦ i.elim0)
  intro x
  simpa using DFunLike.congr_fun key x

/-! ### The tautological representation on `ℂ` -/

/-- **The Mumford–Tate group of `H₁(ℂ/ℤ[i], ℚ)` lies in the centralizer of `J`.** In the basis
`(1, i)` of the tautological representation of `S` on `ℂ`, through which a real point `a + b i`
acts by `[[a, -b], [b, a]]`, the Mumford–Tate group is contained in the centralizer of
`J = [[0, -1], [1, 0]]` in `GL₂`, the torus `Res_{ℚ(i)/ℚ} 𝔾ₘ`: multiplication by `i` is an
endomorphism of the representation. -/
theorem centralizerHopfIdeal_le_mumfordTateHopfIdeal_tautologicalComodule :
    letI := tautologicalComodule
    centralizerHopfIdeal (coordinateHopfAlgebra ℚ 2)
        ((cotangentDualMatrixEquiv (k := ℚ) (n := 2)).symm !![0, -1; 1, 0]) ≤
      mumfordTateHopfIdeal (comoduleDeligneHom Complex.basisOneI) := by
  let := tautologicalComodule
  refine centralizerHopfIdeal_le_mumfordTateHopfIdeal_comoduleDeligneHom _ _
    (map_mulLeft_comp_tautologicalComodule_coact Complex.I) _ ?_
  rw [Algebra.toMatrix_lmul_eq, Algebra.leftMulMatrix_complex]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- An entry of the generic commutator `X J - J X` lies in the centralizer ideal of `J`, read in
`O(GL₂)`. -/
private theorem commutator_mem_map_centralizerIdeal (i j : Fin 2) :
    ((coordinateHopfAlgebraAlgEquiv ℚ 2).toAlgHom.comp (coordinateRingMap ℚ 2)).toRingHom
        ((Matrix.mvPolynomialX (Fin 2) (Fin 2) ℚ *
            (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ).map MvPolynomial.C -
          (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ).map MvPolynomial.C *
            Matrix.mvPolynomialX (Fin 2) (Fin 2) ℚ :
              Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 2 × Fin 2) ℚ)) i j) ∈
      (Matrix.centralizerIdeal (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ)).map
        ((coordinateHopfAlgebraAlgEquiv ℚ 2).toAlgHom.comp (coordinateRingMap ℚ 2)).toRingHom :=
  Ideal.mem_map_of_mem _ (by
    rw [Matrix.centralizerIdeal_def]
    exact Ideal.subset_span ⟨(i, j), rfl⟩)

/-- **`X₁₁ - X₂₂` lies in the Mumford–Tate ideal of `H₁(ℂ/ℤ[i], ℚ)`.** -/
theorem genericMatrix_sub_mem_mumfordTateHopfIdeal_tautologicalComodule :
    letI := tautologicalComodule
    genericMatrix ℚ 2 0 0 - genericMatrix ℚ 2 1 1 ∈
      mumfordTateHopfIdeal (comoduleDeligneHom Complex.basisOneI) := by
  let := tautologicalComodule
  refine centralizerHopfIdeal_le_mumfordTateHopfIdeal_tautologicalComodule ?_
  rw [← HopfIdeal.mem_toIdeal, centralizerHopfIdeal_toIdeal_eq_map_centralizerIdeal,
    LinearEquiv.apply_symm_apply, ← neg_sub]
  refine neg_mem ?_
  convert commutator_mem_map_centralizerIdeal 0 1 using 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, genericMatrix_apply]
  abel

/-- **`X₁₂ + X₂₁` lies in the Mumford–Tate ideal of `H₁(ℂ/ℤ[i], ℚ)`.** -/
theorem genericMatrix_add_mem_mumfordTateHopfIdeal_tautologicalComodule :
    letI := tautologicalComodule
    genericMatrix ℚ 2 0 1 + genericMatrix ℚ 2 1 0 ∈
      mumfordTateHopfIdeal (comoduleDeligneHom Complex.basisOneI) := by
  let := tautologicalComodule
  refine centralizerHopfIdeal_le_mumfordTateHopfIdeal_tautologicalComodule ?_
  rw [← HopfIdeal.mem_toIdeal, centralizerHopfIdeal_toIdeal_eq_map_centralizerIdeal,
    LinearEquiv.apply_symm_apply]
  convert commutator_mem_map_centralizerIdeal 0 0 using 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, genericMatrix_apply]

/-- **The Mumford–Tate group of `H₁(ℂ/ℤ[i], ℚ)` is not all of `GL₂`**: its ideal contains the
nonzero function `X₁₁ - X₂₂`. -/
theorem mumfordTateHopfIdeal_tautologicalComodule_ne_bot :
    letI := tautologicalComodule
    mumfordTateHopfIdeal (comoduleDeligneHom Complex.basisOneI) ≠ ⊥ := by
  let := tautologicalComodule
  intro h
  have hmem := genericMatrix_sub_mem_mumfordTateHopfIdeal_tautologicalComodule
  rw [h, HopfIdeal.mem_bot, sub_eq_zero] at hmem
  let g : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![1, 2])
    (by simp)
  have := congr((generalLinearToPoint 2 g).ofConv $hmem)
  simp [genericMatrix_apply, g] at this

end TauCeti.DeligneTorus
