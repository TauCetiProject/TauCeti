/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Mathlib.RingTheory.FinitePresentation
public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import TauCeti.RingTheory.WittVector.Truncated.MvPolynomial

/-!
# The coordinate Hopf algebra of the Witt vector group `W_n`

Fix a prime `p` and a length `n`. For a commutative ring `R`, the truncated Witt vectors
`W_n(A) = TruncatedWittVector p n A` of length `n`, as `A` ranges over commutative `R`-algebras,
form a group-valued functor whose underlying set-valued functor is corepresented by the
polynomial ring `R[X₀, …, X_{n-1}]`: an `R`-algebra map `f` out of the polynomial ring is the
same as the truncated Witt vector with coordinates `f(X₀), …, f(X_{n-1})`
(`TruncatedWittVector.algHomEquiv`). Transporting the Witt vector addition along this bijection
equips the polynomial ring with a commutative Hopf algebra structure, the coordinate Hopf
algebra of the additive group scheme `W_n` of Witt vectors of length `n`:

* the comultiplication sends `X_i` to the `i`-th coordinate of the sum of the two generic Witt
  vectors `(X_j ⊗ 1)_j` and `(1 ⊗ X_j)_j`, that is, to Witt's addition polynomial
  `S_i(X ⊗ 1, 1 ⊗ X)`;
* the counit corresponds to the zero Witt vector, so it sends every `X_i` to `0`;
* the antipode corresponds to the negative of the generic Witt vector `(X_j)_j`.

Every Hopf algebra law is checked on points: two algebra maps out of the polynomial ring agree as
soon as their Witt vectors agree, and the Witt vector of an algebra map precomposed with the
comultiplication is the sum of the Witt vectors of its two tensor components
(`TauCeti.WittGroup.algHomEquiv_comp_comul`). The ring laws of truncated Witt vectors then give
coassociativity, the counit laws, the antipode laws and cocommutativity.

The resulting convolution group of `A`-valued points is the additive group `W_n(A)`
(`TauCeti.WittGroup.pointsMulEquiv`), naturally in `A`. This is the representable description
of `W_n` used to build the finite Witt group schemes `ker(F^m : W_n → W_n)` and the Dieudonné
module of a unipotent finite group scheme over a perfect field. No hypothesis on `R` is needed:
the construction works over every commutative ring, including `ℤ` and rings in which `p` is
invertible.

The raw structure dictionaries are named values rather than global instances, since the
polynomial ring carries other coalgebra structures; `TauCeti.WittGroup.coordinateHopfAlgebra`
is the bundled object.

## Main declarations

* `TauCeti.WittGroup.comul`, `TauCeti.WittGroup.counit`, `TauCeti.WittGroup.antipode`: the Hopf
  structure maps, characterized on points by `TauCeti.WittGroup.algHomEquiv_comp_comul`,
  `TauCeti.WittGroup.algHomEquiv_counit` and `TauCeti.WittGroup.algHomEquiv_antipode`.
* `TauCeti.WittGroup.hopfAlgebra`: the selected Hopf-algebra dictionary.
* `TauCeti.WittGroup.coordinateHopfAlgebra`: the bundled commutative Hopf algebra, which is
  cocommutative and finitely presented; its structure maps on the coordinates are
  `TauCeti.WittGroup.coordinateHopfAlgebra_comul_X`,
  `TauCeti.WittGroup.coordinateHopfAlgebra_counit_X` and
  `TauCeti.WittGroup.coordinateHopfAlgebra_antipode_X`, and algebra maps out of it are
  determined by these coordinates (`TauCeti.WittGroup.coordinateHopfAlgebra_algHom_ext`).
* `TauCeti.WittGroup.pointsMulEquiv`: its convolution group of `A`-valued points is the additive
  group of `W_n(A)`, naturally in `A` (`TauCeti.WittGroup.pointsMulEquiv_mapValue`).

## References

* R. Pink, *Finite group schemes*, lecture course WS 2004/05, ETH Zürich lecture notes, §22,
  <https://people.math.ethz.ch/~pink/ftp/FGS/CompleteNotes.pdf>.
* M. Demazure, *Lectures on p-divisible groups*, Lecture Notes in Mathematics 302, Springer,
  1972, Chapter III, §1.
-/

public section

noncomputable section

open scoped TensorProduct

open MvPolynomial Algebra.TensorProduct WithConv
open TruncatedWittVector (algHomEquiv algHomEquiv_comp)

namespace TauCeti

namespace WittGroup

universe u v w

variable (p : ℕ) [Fact p.Prime] (n : ℕ) (R : Type u) [CommRing R]

/-- The comultiplication of the coordinate Hopf algebra of `W_n`: the algebra map
corresponding to the sum of the two generic Witt vectors `(X_j ⊗ 1)_j` and `(1 ⊗ X_j)_j`. -/
def comul : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R ⊗[R] MvPolynomial (Fin n) R :=
  (algHomEquiv p n R).symm
    (algHomEquiv p n R includeLeft + algHomEquiv p n R (includeRight (A := MvPolynomial (Fin n) R)))

/-- The counit of the coordinate Hopf algebra of `W_n`: the algebra map corresponding to the
zero Witt vector. -/
def counit : MvPolynomial (Fin n) R →ₐ[R] R :=
  (algHomEquiv p n R).symm 0

/-- The antipode of the coordinate Hopf algebra of `W_n`: the algebra map corresponding to the
negative of the generic Witt vector `(X_j)_j`. -/
def antipode : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  (algHomEquiv p n R).symm (-algHomEquiv p n R (AlgHom.id R _))

/-- The Witt vector of the comultiplication is the sum of the two generic Witt vectors of the
tensor square. -/
@[simp]
theorem algHomEquiv_comul :
    algHomEquiv p n R (comul p n R) =
      algHomEquiv p n R includeLeft +
        algHomEquiv p n R (includeRight (A := MvPolynomial (Fin n) R)) :=
  Equiv.apply_symm_apply _ _

/-- The counit corresponds to the zero Witt vector. -/
@[simp]
theorem algHomEquiv_counit : algHomEquiv p n R (counit p n R) = 0 :=
  Equiv.apply_symm_apply _ _

/-- The antipode corresponds to the negative of the generic Witt vector. -/
@[simp]
theorem algHomEquiv_antipode :
    algHomEquiv p n R (antipode p n R) = -algHomEquiv p n R (AlgHom.id R _) :=
  Equiv.apply_symm_apply _ _

/-- The comultiplication sends the variable `X_i` to the `i`-th coordinate of the sum of the
two generic Witt vectors of the tensor square. -/
@[simp]
theorem comul_X (i : Fin n) :
    comul p n R (X i) =
      (algHomEquiv p n R includeLeft +
        algHomEquiv p n R (includeRight (A := MvPolynomial (Fin n) R))).coeff i :=
  TruncatedWittVector.algHomEquiv_symm_apply_X _ _ _ _ _

/-- The counit sends every variable to zero. -/
@[simp]
theorem counit_X (i : Fin n) : counit p n R (X i) = 0 := by
  rw [counit, TruncatedWittVector.algHomEquiv_symm_apply_X, TruncatedWittVector.coeff_zero]

/-- The antipode sends the variable `X_i` to the `i`-th coordinate of the negative of the
generic Witt vector. -/
@[simp]
theorem antipode_X (i : Fin n) :
    antipode p n R (X i) = (-algHomEquiv p n R (AlgHom.id R _)).coeff i :=
  TruncatedWittVector.algHomEquiv_symm_apply_X _ _ _ _ _

variable {p n R} in
/-- **Comultiplication on points.** Precomposing an algebra map `F` out of the tensor square
with the comultiplication adds the Witt vectors of its two tensor components. -/
theorem algHomEquiv_comp_comul {A : Type v} [CommRing A] [Algebra R A]
    (F : MvPolynomial (Fin n) R ⊗[R] MvPolynomial (Fin n) R →ₐ[R] A) :
    algHomEquiv p n R (F.comp (comul p n R)) =
      algHomEquiv p n R (F.comp includeLeft) + algHomEquiv p n R (F.comp includeRight) := by
  rw [algHomEquiv_comp, algHomEquiv_comul, map_add, ← algHomEquiv_comp, ← algHomEquiv_comp]

private theorem comul_coassoc :
    (Algebra.TensorProduct.assoc R R R _ _ _).toAlgHom.comp
        ((Algebra.TensorProduct.map (comul p n R) (.id R _)).comp (comul p n R)) =
      (Algebra.TensorProduct.map (.id R _) (comul p n R)).comp (comul p n R) := by
  refine (algHomEquiv p n R (A := MvPolynomial (Fin n) R ⊗[R]
    (MvPolynomial (Fin n) R ⊗[R] MvPolynomial (Fin n) R))).injective ?_
  -- Instantiate at the triple tensor product so the ring instances are synthesized rather
  -- than unified against the semiring instances the goal carries.
  have h := algHomEquiv_comp_comul (p := p) (n := n) (R := R) (A := MvPolynomial (Fin n) R ⊗[R]
    (MvPolynomial (Fin n) R ⊗[R] MvPolynomial (Fin n) R))
  rw [← AlgHom.comp_assoc, h, h, AlgHom.comp_assoc, map_comp_includeLeft, ← AlgHom.comp_assoc, h]
  simp only [AlgHom.comp_assoc, map_comp_includeLeft, map_comp_includeRight, AlgHom.comp_id]
  rw [h]
  refine (add_assoc (G := TruncatedWittVector p n
    (MvPolynomial (Fin n) R ⊗[R] (MvPolynomial (Fin n) R ⊗[R] MvPolynomial (Fin n) R)))
    _ _ _).trans ?_
  -- The three inclusions into the triple tensor product match across the associator.
  refine congrArg₂ (· + ·) (congrArg _ ?_)
    (congrArg₂ (· + ·) (congrArg _ ?_) (congrArg _ ?_)) <;> ext <;>
      simp [Algebra.TensorProduct.one_def]

private theorem comul_rTensor_counit :
    (Algebra.TensorProduct.map (counit p n R) (.id R _)).comp (comul p n R) =
      (Algebra.TensorProduct.lid R (MvPolynomial (Fin n) R)).symm := by
  have h : ((Algebra.TensorProduct.lid R (MvPolynomial (Fin n) R)).symm :
      MvPolynomial (Fin n) R →ₐ[R] R ⊗[R] MvPolynomial (Fin n) R) = includeRight := by
    ext
    simp
  rw [h]
  apply (algHomEquiv p n R).injective
  rw [algHomEquiv_comp_comul, map_comp_includeLeft, map_comp_includeRight, AlgHom.comp_id,
    algHomEquiv_comp, algHomEquiv_counit, map_zero, zero_add]

private theorem comul_lTensor_counit :
    (Algebra.TensorProduct.map (.id R _) (counit p n R)).comp (comul p n R) =
      (Algebra.TensorProduct.rid R R (MvPolynomial (Fin n) R)).symm := by
  have h : ((Algebra.TensorProduct.rid R R (MvPolynomial (Fin n) R)).symm :
      MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R ⊗[R] R) = includeLeft := by
    ext
    simp
  rw [h]
  apply (algHomEquiv p n R).injective
  rw [algHomEquiv_comp_comul, map_comp_includeLeft, map_comp_includeRight, AlgHom.comp_id,
    algHomEquiv_comp, algHomEquiv_counit, map_zero, add_zero]

/-- **Cocommutativity.** Swapping the tensor factors fixes the comultiplication, because Witt
vector addition is commutative. -/
theorem comm_comp_comul :
    (Algebra.TensorProduct.comm R (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R)).toAlgHom.comp
      (comul p n R) = comul p n R := by
  apply (algHomEquiv p n R).injective
  rw [algHomEquiv_comp_comul, comm_comp_includeLeft,
    comm_comp_includeRight, algHomEquiv_comul, add_comm]

/-- The bialgebra structure on `R[X₀, …, X_{n-1}]` whose comultiplication is Witt vector
addition and whose counit is the zero Witt vector.

This is intentionally a named value rather than a global instance. -/
@[instance_reducible]
def bialgebra : Bialgebra R (MvPolynomial (Fin n) R) :=
  Bialgebra.ofAlgHom (comul p n R) (counit p n R)
    (comul_coassoc p n R) (comul_rTensor_counit p n R) (comul_lTensor_counit p n R)

private theorem mul_antipode_rTensor_comul :
    (Algebra.TensorProduct.lift (antipode p n R) (.id R (MvPolynomial (Fin n) R))
      fun _ _ ↦ Commute.all _ _).comp (comul p n R) =
        (Algebra.ofId R (MvPolynomial (Fin n) R)).comp (counit p n R) := by
  apply (algHomEquiv p n R).injective
  rw [algHomEquiv_comp_comul, lift_comp_includeLeft, lift_comp_includeRight', algHomEquiv_comp,
    algHomEquiv_counit, map_zero, algHomEquiv_antipode, neg_add_cancel]

private theorem mul_antipode_lTensor_comul :
    (Algebra.TensorProduct.lift (.id R (MvPolynomial (Fin n) R)) (antipode p n R)
      fun _ _ ↦ Commute.all _ _).comp (comul p n R) =
        (Algebra.ofId R (MvPolynomial (Fin n) R)).comp (counit p n R) := by
  apply (algHomEquiv p n R).injective
  rw [algHomEquiv_comp_comul, lift_comp_includeLeft, lift_comp_includeRight', algHomEquiv_comp,
    algHomEquiv_counit, map_zero, algHomEquiv_antipode, add_neg_cancel]

/-- The Hopf-algebra structure on `R[X₀, …, X_{n-1}]` representing the additive group of Witt
vectors of length `n`; its antipode is Witt vector negation.

This is intentionally a named value rather than a global instance. Use `coordinateHopfAlgebra`
as the bundled coherence boundary. -/
@[instance_reducible]
def hopfAlgebra : HopfAlgebra R (MvPolynomial (Fin n) R) :=
  letI : Bialgebra R (MvPolynomial (Fin n) R) := bialgebra p n R
  HopfAlgebra.ofAlgHom (antipode p n R)
    (mul_antipode_rTensor_comul p n R) (mul_antipode_lTensor_comul p n R)

/-- The coordinate Hopf algebra of the Witt vector group `W_n` over `R`: the polynomial ring
`R[X₀, …, X_{n-1}]` with the comultiplication, counit and antipode of Witt vector addition. -/
def coordinateHopfAlgebra : CommHopfAlgCat.{u} R :=
  letI : HopfAlgebra R (MvPolynomial (Fin n) R) := hopfAlgebra p n R
  CommHopfAlgCat.of R (MvPolynomial (Fin n) R)

/-- The identification of the polynomial ring with the carrier of the bundled coordinate Hopf
algebra of `W_n`. -/
def coordinateAlgEquiv : MvPolynomial (Fin n) R ≃ₐ[R] coordinateHopfAlgebra p n R :=
  letI : HopfAlgebra R (MvPolynomial (Fin n) R) := hopfAlgebra p n R
  AlgEquiv.refl

/-- The coordinate algebra of `W_n` is a polynomial algebra in `n` variables, hence finitely
presented. -/
instance finitePresentation_coordinateHopfAlgebra :
    Algebra.FinitePresentation R (coordinateHopfAlgebra p n R) :=
  .equiv (coordinateAlgEquiv p n R)

/-- The comultiplication of the bundled coordinate Hopf algebra is `comul`, transported along
`coordinateAlgEquiv`. -/
theorem comulAlgHom_comp_coordinateAlgEquiv :
    (Bialgebra.comulAlgHom R (coordinateHopfAlgebra p n R)).comp
        (coordinateAlgEquiv p n R).toAlgHom =
      (Algebra.TensorProduct.map (coordinateAlgEquiv p n R).toAlgHom
        (coordinateAlgEquiv p n R).toAlgHom).comp (comul p n R) := by
  -- `coordinateHopfAlgebra` stores `comul` on the polynomial ring itself and
  -- `coordinateAlgEquiv` is the identity of that carrier; Mathlib has no lemma exposing the
  -- comultiplication stored by `CommHopfAlgCat.of`, so the two wrappers are crossed by `change`.
  change comul p n R = (Algebra.TensorProduct.map (AlgHom.id R _) (AlgHom.id R _)).comp _
  rw [Algebra.TensorProduct.map_id, AlgHom.id_comp]

/-- The comultiplication of the bundled coordinate Hopf algebra is `comul`, transported along
`coordinateAlgEquiv`. -/
@[simp low]
theorem coordinateHopfAlgebra_comul_apply (x : MvPolynomial (Fin n) R) :
    Coalgebra.comul (R := R) (A := coordinateHopfAlgebra p n R) (coordinateAlgEquiv p n R x) =
      Algebra.TensorProduct.map (coordinateAlgEquiv p n R).toAlgHom
        (coordinateAlgEquiv p n R).toAlgHom (comul p n R x) :=
  DFunLike.congr_fun (comulAlgHom_comp_coordinateAlgEquiv p n R) x

/-- The counit of the bundled coordinate Hopf algebra is `counit`, transported along
`coordinateAlgEquiv`. -/
@[simp low]
theorem coordinateHopfAlgebra_counit_apply (x : MvPolynomial (Fin n) R) :
    Coalgebra.counit (R := R) (A := coordinateHopfAlgebra p n R) (coordinateAlgEquiv p n R x) =
      counit p n R x :=
  -- `coordinateHopfAlgebra` stores `counit` on the polynomial ring itself and
  -- `coordinateAlgEquiv` is the identity of that carrier.
  (rfl)

/-- The antipode of the bundled coordinate Hopf algebra is `antipode`, transported along
`coordinateAlgEquiv`. -/
@[simp low]
theorem coordinateHopfAlgebra_antipode_apply (x : MvPolynomial (Fin n) R) :
    HopfAlgebra.antipode R (A := coordinateHopfAlgebra p n R) (coordinateAlgEquiv p n R x) =
      coordinateAlgEquiv p n R (antipode p n R x) :=
  -- As for the counit, both wrappers are the identity on the stored antipode.
  (rfl)

/-- Two algebra maps out of the bundled coordinate Hopf algebra of `W_n` are equal as soon as
they agree on the coordinates `X₀, …, X_{n-1}`. -/
theorem coordinateHopfAlgebra_algHom_ext {T : Type v} [Semiring T] [Algebra R T]
    {f g : coordinateHopfAlgebra p n R →ₐ[R] T}
    (h : ∀ i, f (coordinateAlgEquiv p n R (X i)) = g (coordinateAlgEquiv p n R (X i))) :
    f = g :=
  (AlgHom.cancel_right (coordinateAlgEquiv p n R).surjective).mp <|
    MvPolynomial.algHom_ext (f := f.comp (coordinateAlgEquiv p n R).toAlgHom) h

/-- The comultiplication of the bundled coordinate Hopf algebra sends the coordinate `X_i` to the
`i`-th coordinate of the sum of the two generic Witt vectors `(X_j ⊗ 1)_j` and `(1 ⊗ X_j)_j`. -/
@[simp]
theorem coordinateHopfAlgebra_comul_X (i : Fin n) :
    Coalgebra.comul (R := R) (A := coordinateHopfAlgebra p n R) (coordinateAlgEquiv p n R (X i)) =
      (TruncatedWittVector.mk p (fun j ↦ coordinateAlgEquiv p n R (X j) ⊗ₜ[R] 1) +
        TruncatedWittVector.mk p (fun j ↦ 1 ⊗ₜ[R] coordinateAlgEquiv p n R (X j))).coeff i := by
  rw [coordinateHopfAlgebra_comul_apply, ← AlgHom.comp_apply,
    ← TruncatedWittVector.coeff_algHomEquiv p n R, algHomEquiv_comp_comul]
  congr 2 <;> ext j <;> simp

/-- The counit of the bundled coordinate Hopf algebra sends every coordinate to zero. -/
@[simp]
theorem coordinateHopfAlgebra_counit_X (i : Fin n) :
    Coalgebra.counit (R := R) (A := coordinateHopfAlgebra p n R)
      (coordinateAlgEquiv p n R (X i)) = 0 := by
  rw [coordinateHopfAlgebra_counit_apply, counit_X]

/-- The antipode of the bundled coordinate Hopf algebra sends the coordinate `X_i` to the `i`-th
coordinate of the negative of the generic Witt vector `(X_j)_j`. -/
@[simp]
theorem coordinateHopfAlgebra_antipode_X (i : Fin n) :
    HopfAlgebra.antipode R (A := coordinateHopfAlgebra p n R) (coordinateAlgEquiv p n R (X i)) =
      (-TruncatedWittVector.mk p (fun j ↦ coordinateAlgEquiv p n R (X j))).coeff i := by
  rw [coordinateHopfAlgebra_antipode_apply, ← AlgEquiv.coe_toAlgHom, ← AlgHom.comp_apply,
    ← TruncatedWittVector.coeff_algHomEquiv p n R, algHomEquiv_comp, algHomEquiv_antipode,
    map_neg, ← algHomEquiv_comp, AlgHom.comp_id]
  congr 2
  ext j
  simp

/-- The bundled coordinate Hopf algebra of `W_n` is cocommutative. -/
instance : Coalgebra.IsCocomm R (coordinateHopfAlgebra p n R) where
  comm_comp_comul := by
    -- As in `comulAlgHom_comp_coordinateAlgEquiv`, the stored comultiplication is `comul`.
    change (Algebra.TensorProduct.comm R (MvPolynomial (Fin n) R)
      (MvPolynomial (Fin n) R)).toAlgHom.toLinearMap.comp (comul p n R).toLinearMap =
        (comul p n R).toLinearMap
    rw [← AlgHom.comp_toLinearMap, comm_comp_comul]

section Points

variable {p n R} {A : Type v} [CommRing A] [Algebra R A] {B : Type w} [CommRing B] [Algebra R B]

/-- **The points of `W_n` are the truncated Witt vectors.** For a commutative `R`-algebra `A`,
the convolution group of `A`-valued points of the coordinate Hopf algebra of `W_n` is the
additive group of truncated Witt vectors of length `n` over `A`: a point corresponds to the Witt
vector of its values on the coordinates `X₀, …, X_{n-1}`. -/
def pointsMulEquiv :
    WithConv (coordinateHopfAlgebra p n R →ₐ[R] A) ≃*
      Multiplicative (TruncatedWittVector p n A) where
  toFun F := .ofAdd (algHomEquiv p n R (F.ofConv.comp (coordinateAlgEquiv p n R).toAlgHom))
  invFun x :=
    toConv (((algHomEquiv p n R).symm x.toAdd).comp (coordinateAlgEquiv p n R).symm.toAlgHom)
  left_inv F := by
    simp only [toAdd_ofAdd, Equiv.symm_apply_apply, AlgHom.comp_assoc,
      AlgEquiv.comp_symm, AlgHom.comp_id, toConv_ofConv]
  right_inv x := by
    simp only [AlgHom.comp_assoc,
      AlgEquiv.symm_comp, AlgHom.comp_id, Equiv.apply_symm_apply, ofAdd_toAdd]
  map_mul' F G := by
    rw [AlgHom.convMul_def, ofConv_toConv, AlgHom.comp_assoc, AlgHom.comp_assoc,
      comulAlgHom_comp_coordinateAlgEquiv, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc,
      algHomEquiv_comp_comul, ← ofAdd_add]
    congr 3
    · rw [AlgHom.comp_assoc, map_comp_includeLeft, ← AlgHom.comp_assoc, lmul'_comp_map,
        lift_comp_includeLeft]
    · rw [AlgHom.comp_assoc, map_comp_includeRight, ← AlgHom.comp_assoc, lmul'_comp_map,
        lift_comp_includeRight']

/-- The Witt vector of a point is the Witt vector of the corresponding algebra map out of the
polynomial ring. -/
theorem toAdd_pointsMulEquiv (F : WithConv (coordinateHopfAlgebra p n R →ₐ[R] A)) :
    (pointsMulEquiv F).toAdd =
      algHomEquiv p n R (F.ofConv.comp (coordinateAlgEquiv p n R).toAlgHom) :=
  (rfl)

/-- The coordinates of the Witt vector of a point are its values on the coordinates
`X₀, …, X_{n-1}` of `W_n`. -/
@[simp]
theorem coeff_toAdd_pointsMulEquiv (F : WithConv (coordinateHopfAlgebra p n R →ₐ[R] A))
    (i : Fin n) :
    (pointsMulEquiv F).toAdd.coeff i = F.ofConv (coordinateAlgEquiv p n R (X i)) := by
  simp [toAdd_pointsMulEquiv]

/-- The point attached to a Witt vector `x` sends the coordinate `X_i` of `W_n` to the `i`-th
coordinate of `x`. -/
@[simp]
theorem ofConv_pointsMulEquiv_symm_apply_coordinate (x : Multiplicative (TruncatedWittVector p n A))
    (i : Fin n) :
    (pointsMulEquiv.symm x).ofConv (coordinateAlgEquiv p n R (X i)) = x.toAdd.coeff i := by
  rw [← coeff_toAdd_pointsMulEquiv, MulEquiv.apply_symm_apply]

/-- The identification of points of `W_n` with truncated Witt vectors is natural in the value
algebra: post-composing a point with `φ : A →ₐ[R] B` changes the coefficients of its Witt vector
along `φ`. -/
theorem pointsMulEquiv_mapValue (φ : A →ₐ[R] B)
    (F : WithConv (coordinateHopfAlgebra p n R →ₐ[R] A)) :
    pointsMulEquiv (AlgHom.mapValue φ F) =
      .ofAdd (TruncatedWittVector.map n φ.toRingHom (pointsMulEquiv F).toAdd) := by
  rw [← ofAdd_toAdd (pointsMulEquiv _), toAdd_pointsMulEquiv, toAdd_pointsMulEquiv,
    AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_assoc, algHomEquiv_comp]

end Points

end WittGroup

end TauCeti
