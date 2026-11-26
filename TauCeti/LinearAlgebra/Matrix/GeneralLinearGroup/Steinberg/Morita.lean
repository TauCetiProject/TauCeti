/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.MoritaK1
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.K2
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.UniversalCentralExtension

import TauCeti.GroupTheory.Commutator

/-!
# Morita invariance of the Steinberg group and of algebraic `K₂`

For a nonempty finite index type `ι`, flattening block matrices is an isomorphism
`Φ : GL_∞(Matrix ι ι R) ≃* GL_∞(R)` (`TauCeti.StableGeneralLinearGroup.matrixEquiv`), which
carries `E_∞(Matrix ι ι R)` onto `E_∞(R)`, as these are the commutator subgroups. By the
Kervaire–Steinberg theorem both
`St(Matrix ι ι R) → E_∞(Matrix ι ι R)` and `St(R) → E_∞(R)` are universal central extensions, so
they are isomorphic over `Φ`: there is exactly one homomorphism `St(Matrix ι ι R) →* St(R)` lying
over `Φ`, and it is an isomorphism. Restricting it to the kernels of the projections to `GL_∞`
gives the **Morita invariance of Milnor's `K₂`**:

  `K₂(Mₙ(R)) ≃* K₂(R)` for `n ≥ 1`,

`TauCeti.AlgebraicK2.matrixEquiv`, natural in ring homomorphisms `R →+* S`. For `ι` empty,
`Matrix ι ι R` is the zero ring, whose `K₂` is trivial, while `K₂(ℤ)` is cyclic of order two
(Milnor, §10).

## Main definitions

* `TauCeti.SteinbergGroup.matrixEquiv`: the Morita isomorphism
  `St(Matrix ι ι R) ≃* St(R)` over the flattening isomorphism of `GL_∞`.
* `TauCeti.AlgebraicK2.matrixEquiv`: the Morita isomorphism `K₂(Matrix ι ι R) ≃* K₂(R)`.

## Main results

* `TauCeti.SteinbergGroup.toStableGL_matrixEquiv`,
  `TauCeti.SteinbergGroup.toStableGL_matrixEquiv_symm`: the Morita isomorphism of Steinberg
  groups lies over the flattening isomorphism of `GL_∞`.
* `TauCeti.SteinbergGroup.matrixEquiv_unique`: it is the only homomorphism doing so.
* `TauCeti.SteinbergGroup.map_matrixEquiv`, `TauCeti.AlgebraicK2.map_matrixEquiv`: naturality
  in ring homomorphisms.
* `TauCeti.AlgebraicK2.coe_matrixEquiv`, `TauCeti.AlgebraicK2.coe_matrixEquiv_symm`: the Morita
  isomorphism of `K₂` is the restriction of that of Steinberg groups.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §5.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Corollary 5.6.1 (Morita invariance of `K₂`, from the
  universal central extension).
-/

public section

noncomputable section

namespace TauCeti

/-! ## The Morita isomorphism of Steinberg groups -/

namespace SteinbergGroup

variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

variable (R ι) in
/-- The homomorphism `St(Matrix ι ι R) →* St(R)` over the flattening isomorphism of `GL_∞`. -/
private def flattenHom : SteinbergGroup (Matrix ι ι R) →* SteinbergGroup R :=
  (existsUnique_toStableGL_comp_eq
    (StableGeneralLinearGroup.matrixEquiv R ι).toMonoidHom).exists.choose

private theorem toStableGL_flattenHom (z : SteinbergGroup (Matrix ι ι R)) :
    toStableGL R (flattenHom R ι z) =
      StableGeneralLinearGroup.matrixEquiv R ι (toStableGL (Matrix ι ι R) z) :=
  DFunLike.congr_fun (existsUnique_toStableGL_comp_eq _).exists.choose_spec z

variable (R ι) in
/-- The homomorphism `St(R) →* St(Matrix ι ι R)` over the inverse flattening isomorphism. -/
private def unflattenHom : SteinbergGroup R →* SteinbergGroup (Matrix ι ι R) :=
  (existsUnique_toStableGL_comp_eq
    (StableGeneralLinearGroup.matrixEquiv R ι).symm.toMonoidHom).exists.choose

private theorem toStableGL_unflattenHom (z : SteinbergGroup R) :
    toStableGL (Matrix ι ι R) (unflattenHom R ι z) =
      (StableGeneralLinearGroup.matrixEquiv R ι).symm (toStableGL R z) :=
  DFunLike.congr_fun (existsUnique_toStableGL_comp_eq _).exists.choose_spec z

variable (R ι) in
/-- **Morita invariance of the Steinberg group**: for a nonempty finite index type `ι`, the
Steinberg groups `St(Matrix ι ι R)` and `St(R)` are isomorphic over the flattening isomorphism
`GL_∞(Matrix ι ι R) ≃* GL_∞(R)` (`TauCeti.SteinbergGroup.toStableGL_matrixEquiv`), and this
property determines the isomorphism (`TauCeti.SteinbergGroup.matrixEquiv_unique`). -/
def matrixEquiv : SteinbergGroup (Matrix ι ι R) ≃* SteinbergGroup R where
  toFun := flattenHom R ι
  invFun := unflattenHom R ι
  left_inv z := by
    have : (unflattenHom R ι).comp (flattenHom R ι) = MonoidHom.id _ :=
      MonoidHom.eq_of_comp_eq_of_ker_le_center ker_toStableGL_le_center <| MonoidHom.ext fun z ↦ by
        simp [toStableGL_unflattenHom, toStableGL_flattenHom]
    exact DFunLike.congr_fun this z
  right_inv z := by
    have : (flattenHom R ι).comp (unflattenHom R ι) = MonoidHom.id _ :=
      MonoidHom.eq_of_comp_eq_of_ker_le_center ker_toStableGL_le_center <| MonoidHom.ext fun z ↦ by
        simp [toStableGL_unflattenHom, toStableGL_flattenHom]
    exact DFunLike.congr_fun this z
  map_mul' := map_mul _

/-- The Morita isomorphism of Steinberg groups lies over the flattening isomorphism of `GL_∞`. -/
@[simp]
theorem toStableGL_matrixEquiv (z : SteinbergGroup (Matrix ι ι R)) :
    toStableGL R (matrixEquiv R ι z) =
      StableGeneralLinearGroup.matrixEquiv R ι (toStableGL (Matrix ι ι R) z) :=
  toStableGL_flattenHom z

/-- The inverse Morita isomorphism of Steinberg groups lies over the inverse flattening
isomorphism of `GL_∞`. -/
@[simp]
theorem toStableGL_matrixEquiv_symm (z : SteinbergGroup R) :
    toStableGL (Matrix ι ι R) ((matrixEquiv R ι).symm z) =
      (StableGeneralLinearGroup.matrixEquiv R ι).symm (toStableGL R z) :=
  toStableGL_unflattenHom z

/-- **Uniqueness of the Morita isomorphism**: every homomorphism `St(Matrix ι ι R) →* St(R)` over
the flattening isomorphism of `GL_∞` is the Morita isomorphism. -/
theorem matrixEquiv_unique (ψ : SteinbergGroup (Matrix ι ι R) →* SteinbergGroup R)
    (hψ : (toStableGL R).comp ψ =
      (StableGeneralLinearGroup.matrixEquiv R ι).toMonoidHom.comp (toStableGL (Matrix ι ι R))) :
    ψ = (matrixEquiv R ι).toMonoidHom :=
  MonoidHom.eq_of_comp_eq_of_ker_le_center ker_toStableGL_le_center <|
    hψ.trans <| MonoidHom.ext fun z ↦ by simp

/-- The Morita isomorphism of Steinberg groups is natural in ring homomorphisms `f : R →+* S`: it
intertwines `St(f)` with `St` of `f` applied to the entries of `ι × ι` matrices. -/
theorem map_matrixEquiv {S : Type*} [Ring S] (f : R →+* S)
    (z : SteinbergGroup (Matrix ι ι R)) :
    IndexedSteinbergGroup.map f (matrixEquiv R ι z) =
      matrixEquiv S ι (IndexedSteinbergGroup.map f.mapMatrix z) := by
  have : (IndexedSteinbergGroup.map f).comp (matrixEquiv R ι).toMonoidHom =
      (matrixEquiv S ι).toMonoidHom.comp (IndexedSteinbergGroup.map f.mapMatrix) :=
    MonoidHom.eq_of_comp_eq_of_ker_le_center ker_toStableGL_le_center <| MonoidHom.ext fun z ↦ by
      simp [StableGeneralLinearGroup.map_matrixEquiv]
  exact DFunLike.congr_fun this z

end SteinbergGroup

/-! ## The Morita isomorphism of `K₂` -/

namespace AlgebraicK2

variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

variable (R ι) in
/-- **Morita invariance of algebraic `K₂`**: for a nonempty finite index type `ι`, the Morita
isomorphism of Steinberg groups restricts to an isomorphism `K₂(Matrix ι ι R) ≃* K₂(R)` of the
kernels of the projections to `GL_∞`. -/
def matrixEquiv : AlgebraicK2 (Matrix ι ι R) ≃* AlgebraicK2 R where
  toFun x := ⟨SteinbergGroup.matrixEquiv R ι x, by simp⟩
  invFun y := ⟨(SteinbergGroup.matrixEquiv R ι).symm y, by simp⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

/-- The Morita isomorphism of `K₂` is the restriction of that of Steinberg groups. -/
@[simp]
theorem coe_matrixEquiv (x : AlgebraicK2 (Matrix ι ι R)) :
    (matrixEquiv R ι x : SteinbergGroup R) = SteinbergGroup.matrixEquiv R ι x :=
  (rfl)

/-- The inverse Morita isomorphism of `K₂` is the restriction of that of Steinberg groups. -/
@[simp]
theorem coe_matrixEquiv_symm (y : AlgebraicK2 R) :
    ((matrixEquiv R ι).symm y : SteinbergGroup (Matrix ι ι R)) =
      (SteinbergGroup.matrixEquiv R ι).symm y :=
  (rfl)

/-- The Morita isomorphism of `K₂` is natural in ring homomorphisms `f : R →+* S`: it intertwines
`K₂(f)` with `K₂` of `f` applied to the entries of `ι × ι` matrices. -/
theorem map_matrixEquiv {S : Type*} [Ring S] (f : R →+* S) (x : AlgebraicK2 (Matrix ι ι R)) :
    map f (matrixEquiv R ι x) = matrixEquiv S ι (map f.mapMatrix x) :=
  Subtype.ext (by simp [SteinbergGroup.map_matrixEquiv])

end AlgebraicK2

end TauCeti
