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

By the Kervaire–Steinberg theorem, `St(A) → E_∞(A)` is a universal central extension, and every
homomorphism `GL_∞(A) →* GL_∞(B)` carries the commutator subgroup `E_∞(A)` into `E_∞(B)`. Hence
every isomorphism `Φ : GL_∞(A) ≃* GL_∞(B)` lifts uniquely to an isomorphism
`St(A) ≃* St(B)` over it (`TauCeti.SteinbergGroup.congr`), which restricts to an isomorphism
`K₂(A) ≃* K₂(B)` (`TauCeti.AlgebraicK2.congr`).

For a nonempty finite index type `ι`, flattening block matrices is an isomorphism
`Φ : GL_∞(Matrix ι ι R) ≃* GL_∞(R)` (`TauCeti.StableGeneralLinearGroup.matrixEquiv`), so there
is exactly one homomorphism `St(Matrix ι ι R) →* St(R)` lying over `Φ`, and it is an isomorphism.
Restricting it to the kernels of the projections to `GL_∞` gives the **Morita invariance of
Milnor's `K₂`**:

  `K₂(Mₙ(R)) ≃* K₂(R)` for `n ≥ 1`,

`TauCeti.AlgebraicK2.matrixEquiv`, natural in ring homomorphisms `R →+* S`. For `ι` empty,
`Matrix ι ι R` is the zero ring, whose `K₂` is trivial, while `K₂(ℤ)` is cyclic of order two
(Milnor, §10).

## Main definitions

* `TauCeti.SteinbergGroup.congr`: the isomorphism `St(A) ≃* St(B)` over an isomorphism
  `GL_∞(A) ≃* GL_∞(B)`.
* `TauCeti.AlgebraicK2.congr`: its restriction `K₂(A) ≃* K₂(B)`.
* `TauCeti.SteinbergGroup.matrixEquiv`: the Morita isomorphism
  `St(Matrix ι ι R) ≃* St(R)` over the flattening isomorphism of `GL_∞`.
* `TauCeti.AlgebraicK2.matrixEquiv`: the Morita isomorphism `K₂(Matrix ι ι R) ≃* K₂(R)`.

## Main results

* `TauCeti.SteinbergGroup.toStableGL_congr`, `TauCeti.SteinbergGroup.toStableGL_congr_symm`,
  `TauCeti.SteinbergGroup.congr_unique`: the lift of an isomorphism of `GL_∞` lies over it, and is
  the only homomorphism doing so.
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

/-! ## Isomorphisms of Steinberg groups over isomorphisms of `GL_∞` -/

namespace SteinbergGroup

section congr

variable {A B : Type*} [Ring A] [Ring B]

/-- The unique homomorphism `St(A) →* St(B)` over a homomorphism `GL_∞(A) →* GL_∞(B)`. -/
private def liftHom (Ψ : StableGeneralLinearGroup A →* StableGeneralLinearGroup B) :
    SteinbergGroup A →* SteinbergGroup B :=
  (existsUnique_toStableGL_comp_eq Ψ).exists.choose

private theorem toStableGL_liftHom (Ψ : StableGeneralLinearGroup A →* StableGeneralLinearGroup B)
    (z : SteinbergGroup A) : toStableGL B (liftHom Ψ z) = Ψ (toStableGL A z) :=
  DFunLike.congr_fun (existsUnique_toStableGL_comp_eq Ψ).exists.choose_spec z

/-- An isomorphism `Φ : GL_∞(A) ≃* GL_∞(B)` lifts to an isomorphism `St(A) ≃* St(B)` over it
(`TauCeti.SteinbergGroup.toStableGL_congr`), and this property determines the lift
(`TauCeti.SteinbergGroup.congr_unique`). No compatibility with elementary matrices is assumed. -/
def congr (Φ : StableGeneralLinearGroup A ≃* StableGeneralLinearGroup B) :
    SteinbergGroup A ≃* SteinbergGroup B :=
  MonoidHom.toMulEquiv (liftHom Φ.toMonoidHom) (liftHom Φ.symm.toMonoidHom)
    (MonoidHom.eq_of_comp_eq_of_ker_le_center ker_toStableGL_le_center <| MonoidHom.ext fun z ↦ by
      simp [toStableGL_liftHom])
    (MonoidHom.eq_of_comp_eq_of_ker_le_center ker_toStableGL_le_center <| MonoidHom.ext fun z ↦ by
      simp [toStableGL_liftHom])

/-- The lift of an isomorphism of `GL_∞` to Steinberg groups lies over it. -/
@[simp]
theorem toStableGL_congr (Φ : StableGeneralLinearGroup A ≃* StableGeneralLinearGroup B)
    (z : SteinbergGroup A) : toStableGL B (congr Φ z) = Φ (toStableGL A z) :=
  toStableGL_liftHom _ z

/-- The inverse of the lift of an isomorphism of `GL_∞` to Steinberg groups lies over the inverse
isomorphism. -/
@[simp]
theorem toStableGL_congr_symm (Φ : StableGeneralLinearGroup A ≃* StableGeneralLinearGroup B)
    (z : SteinbergGroup B) : toStableGL A ((congr Φ).symm z) = Φ.symm (toStableGL B z) :=
  toStableGL_liftHom _ z

/-- **Uniqueness of the lift**: every homomorphism `St(A) →* St(B)` over an isomorphism
`Φ : GL_∞(A) ≃* GL_∞(B)` is `TauCeti.SteinbergGroup.congr Φ`. -/
theorem congr_unique (Φ : StableGeneralLinearGroup A ≃* StableGeneralLinearGroup B)
    (ψ : SteinbergGroup A →* SteinbergGroup B)
    (hψ : (toStableGL B).comp ψ = Φ.toMonoidHom.comp (toStableGL A)) :
    ψ = (congr Φ).toMonoidHom :=
  MonoidHom.eq_of_comp_eq_of_ker_le_center ker_toStableGL_le_center <|
    hψ.trans <| MonoidHom.ext fun z ↦ by simp

end congr

/-! ## The Morita isomorphism of Steinberg groups -/

variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

variable (R ι) in
/-- **Morita invariance of the Steinberg group**: for a nonempty finite index type `ι`, the
Steinberg groups `St(Matrix ι ι R)` and `St(R)` are isomorphic over the flattening isomorphism
`GL_∞(Matrix ι ι R) ≃* GL_∞(R)` (`TauCeti.SteinbergGroup.toStableGL_matrixEquiv`), and this
property determines the isomorphism (`TauCeti.SteinbergGroup.matrixEquiv_unique`). -/
def matrixEquiv : SteinbergGroup (Matrix ι ι R) ≃* SteinbergGroup R :=
  congr (StableGeneralLinearGroup.matrixEquiv R ι)

/-- The Morita isomorphism of Steinberg groups lies over the flattening isomorphism of `GL_∞`. -/
@[simp]
theorem toStableGL_matrixEquiv (z : SteinbergGroup (Matrix ι ι R)) :
    toStableGL R (matrixEquiv R ι z) =
      StableGeneralLinearGroup.matrixEquiv R ι (toStableGL (Matrix ι ι R) z) :=
  toStableGL_congr _ z

/-- The inverse Morita isomorphism of Steinberg groups lies over the inverse flattening
isomorphism of `GL_∞`. -/
@[simp]
theorem toStableGL_matrixEquiv_symm (z : SteinbergGroup R) :
    toStableGL (Matrix ι ι R) ((matrixEquiv R ι).symm z) =
      (StableGeneralLinearGroup.matrixEquiv R ι).symm (toStableGL R z) :=
  toStableGL_congr_symm _ z

/-- **Uniqueness of the Morita isomorphism**: every homomorphism `St(Matrix ι ι R) →* St(R)` over
the flattening isomorphism of `GL_∞` is the Morita isomorphism. -/
theorem matrixEquiv_unique (ψ : SteinbergGroup (Matrix ι ι R) →* SteinbergGroup R)
    (hψ : (toStableGL R).comp ψ =
      (StableGeneralLinearGroup.matrixEquiv R ι).toMonoidHom.comp (toStableGL (Matrix ι ι R))) :
    ψ = (matrixEquiv R ι).toMonoidHom :=
  congr_unique _ ψ hψ

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

/-! ## Isomorphisms of `K₂` over isomorphisms of `GL_∞` -/

namespace AlgebraicK2

section congr

variable {A B : Type*} [Ring A] [Ring B]

/-- An isomorphism `Φ : GL_∞(A) ≃* GL_∞(B)` induces an isomorphism `K₂(A) ≃* K₂(B)`: the
restriction of its lift `TauCeti.SteinbergGroup.congr Φ` to the kernels of the projections to
`GL_∞`. -/
def congr (Φ : StableGeneralLinearGroup A ≃* StableGeneralLinearGroup B) :
    AlgebraicK2 A ≃* AlgebraicK2 B where
  toFun x := ⟨SteinbergGroup.congr Φ x, by simp⟩
  invFun y := ⟨(SteinbergGroup.congr Φ).symm y, by simp⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

/-- The isomorphism of `K₂` induced by an isomorphism of `GL_∞` is the restriction of its lift to
Steinberg groups. -/
@[simp]
theorem coe_congr (Φ : StableGeneralLinearGroup A ≃* StableGeneralLinearGroup B)
    (x : AlgebraicK2 A) : (congr Φ x : SteinbergGroup B) = SteinbergGroup.congr Φ x :=
  (rfl)

/-- The inverse of the isomorphism of `K₂` induced by an isomorphism of `GL_∞` is the restriction
of the inverse of its lift to Steinberg groups. -/
@[simp]
theorem coe_congr_symm (Φ : StableGeneralLinearGroup A ≃* StableGeneralLinearGroup B)
    (y : AlgebraicK2 B) :
    ((congr Φ).symm y : SteinbergGroup A) = (SteinbergGroup.congr Φ).symm y :=
  (rfl)

end congr

/-! ## The Morita isomorphism of `K₂` -/

variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

variable (R ι) in
/-- **Morita invariance of algebraic `K₂`**: for a nonempty finite index type `ι`, the Morita
isomorphism of Steinberg groups restricts to an isomorphism `K₂(Matrix ι ι R) ≃* K₂(R)` of the
kernels of the projections to `GL_∞`. -/
def matrixEquiv : AlgebraicK2 (Matrix ι ι R) ≃* AlgebraicK2 R :=
  congr (StableGeneralLinearGroup.matrixEquiv R ι)

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
