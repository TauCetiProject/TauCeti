/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import TauCeti.RepresentationTheory.PeriodRing.Regular
import TauCeti.RingTheory.TensorProduct.Free

/-!
# Fontaine's period invariants and the comparison map

Let `ρ` be a representation of a group `G` on a vector space `V` over a field `F`, and let `G`
act on a commutative `F`-algebra `B` by `F`-algebra automorphisms. Then `G` acts diagonally on
`B ⊗[F] V`, by `b ⊗ v ↦ (g • b) ⊗ ρ g v`; this action is semilinear over `B`. Its invariants

`D_B(V) = (B ⊗[F] V)^G`

form a module over every ring `E` of `G`-invariant scalars of `B`, and there is a natural
`B`-linear comparison map

`α_V : B ⊗[E] D_B(V) → B ⊗[F] V,  b ⊗ x ↦ b • x`.

When `B` is a regular period ring with field of invariants `E`, Fontaine's basic theorem says
that `α_V` is injective and `dim_E D_B(V) ≤ dim_F V`, with equality exactly when `α_V` is an
isomorphism. The representations for which equality holds are the `B`-admissible ones: for
`B = B_dR`, `B_cris`, `B_st` and `B_HT` these are the de Rham, crystalline, semistable and
Hodge–Tate representations.

Injectivity uses only that the invariants of the fraction field of `B` are `E`
(`LinearIndependent.of_invariant`). The converse direction of the dimension criterion uses the
second condition of regularity: the determinant of the matrix of `α_V` in bases of `D_B(V)` and
`V` spans a `G`-stable `F`-line, since `g` multiplies it by the inverse determinant of `ρ g`. It
is nonzero because `α_V` is injective, so it is a unit, and `α_V` is bijective.

## Main definitions

* `Representation.periodAction B ρ g`: the diagonal action of `g` on `B ⊗[F] V`, a `B`-semilinear
  map.
* `Representation.periodInvariants B E ρ`: Fontaine's `D_B(V) = (B ⊗[F] V)^G`, as an `E`-module.
* `Representation.periodComparison B E ρ`: the comparison map `B ⊗[E] D_B(V) → B ⊗[F] V`.

## Main results

* `Representation.linearIndependent_coe_periodInvariants`: elements of `D_B(V)` that are
  independent over `E` are independent over `B` in `B ⊗[F] V`.
* `Representation.periodComparison_injective`: the comparison map is injective.
* `Representation.rank_periodInvariants_le`, `Representation.finrank_periodInvariants_le`:
  `dim_E D_B(V) ≤ dim_F V`.
* `Representation.periodComparison_bijective_iff`: for finite-dimensional `V`, the comparison
  map is bijective if and only if `dim_E D_B(V) = dim_F V`.

## References

* O. Brinon and B. Conrad, *CMI Summer School notes on p-adic Hodge theory* (2009),
  Theorem 5.2.1.
* J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois representations*, Theorem 2.13.
-/

public section

open Module TensorProduct
open scoped TensorProduct

namespace Representation

universe uB uV

variable {F G : Type*} (B : Type uB) {V : Type uV} [Field F] [CommRing B] [Algebra F B]
  [AddCommGroup V] [Module F V]

section Monoid

variable [Monoid G] [MulSemiringAction G B] [SMulCommClass G F B]

/-- The diagonal action `b ⊗ v ↦ (g • b) ⊗ ρ g v` of `g` on `B ⊗[F] V`. It is semilinear over
`B` along the action of `g` on `B`. -/
def periodAction (ρ : Representation F G V) (g : G) :
    B ⊗[F] V →ₛₗ[MulSemiringAction.toRingHom G B g] B ⊗[F] V where
  toFun := TensorProduct.map (MulSemiringAction.toAlgHom F B g).toLinearMap (ρ g)
  map_add' := map_add _
  map_smul' b x := by
    induction x using TensorProduct.inductionOn with
    | tmul c v => simp [smul_tmul', smul_mul']
    | add x y hx hy => simp_all

variable {B} (ρ : Representation F G V)

/-- The diagonal action on pure tensors. -/
@[simp]
theorem periodAction_tmul (g : G) (b : B) (v : V) :
    ρ.periodAction B g (b ⊗ₜ v) = (g • b) ⊗ₜ ρ g v :=
  (rfl)

/-- The identity acts trivially on `B ⊗[F] V`. -/
@[simp]
theorem periodAction_one_apply (x : B ⊗[F] V) : ρ.periodAction B 1 x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul b v => simp
  | add x y hx hy => simp_all

/-- The diagonal action is an action: `g * h` acts as `g` after `h`. -/
theorem periodAction_mul_apply (g h : G) (x : B ⊗[F] V) :
    ρ.periodAction B (g * h) x = ρ.periodAction B g (ρ.periodAction B h x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b v => simp [mul_smul]
  | add x y hx hy => simp_all

section Invariants

variable (B) (E : Type*) [CommSemiring E] [Algebra E B] [SMulCommClass F E B]
  [SMulCommClass G E B]

/-- **Fontaine's period invariants** `D_B(V) = (B ⊗[F] V)^G` of a representation `V`, for the
diagonal action of `G` on `B ⊗[F] V`. They form a module over every ring `E` of `G`-invariant
scalars of `B`; for a regular period ring, `E` is its field of invariants. -/
def periodInvariants : Submodule E (B ⊗[F] V) where
  carrier := {x | ∀ g, ρ.periodAction B g x = x}
  add_mem' hx hy g := by simp [hx g, hy g]
  zero_mem' g := map_zero _
  smul_mem' e x hx g := by
    rw [← algebraMap_smul B e x, map_smulₛₗ, MulSemiringAction.toRingHom_apply, smul_algebraMap,
      hx g]

variable {B E} in
/-- A tensor lies in `D_B(V)` exactly when every `g` fixes it. -/
@[simp]
theorem mem_periodInvariants_iff {x : B ⊗[F] V} :
    x ∈ ρ.periodInvariants B E ↔ ∀ g, ρ.periodAction B g x = x :=
  Iff.rfl

/-- **Fontaine's comparison map** `B ⊗[E] D_B(V) → B ⊗[F] V`, `b ⊗ x ↦ b • x`. -/
def periodComparison : B ⊗[E] ρ.periodInvariants B E →ₗ[B] B ⊗[F] V :=
  (ρ.periodInvariants B E).subtype.liftBaseChange B

variable {B E} in
/-- The comparison map on pure tensors. -/
@[simp]
theorem periodComparison_tmul (b : B) (x : ρ.periodInvariants B E) :
    ρ.periodComparison B E (b ⊗ₜ x) = b • (x : B ⊗[F] V) :=
  LinearMap.liftBaseChange_tmul _ _ _ _

end Invariants

variable {E : Type*} [Field E] [Algebra E B] [SMulCommClass F E B] [SMulCommClass G E B]

/-- Elements of `D_B(V)` that are linearly independent over the field of invariants `E` of a
regular period ring `B` are linearly independent over `B` in `B ⊗[F] V`. -/
theorem linearIndependent_coe_periodInvariants
    (h : TauCeti.IsRegularPeriodRing F E G B) {ι : Type*} {x : ι → ρ.periodInvariants B E}
    (hx : LinearIndependent E x) : LinearIndependent B fun i ↦ (x i : B ⊗[F] V) := by
  have := h.isDomain
  have hx' : LinearIndependent E ((ρ.periodInvariants B E).subtype ∘ x) :=
    hx.map_injOn _ (Submodule.injective_subtype _).injOn
  exact hx'.of_invariant (ρ.periodAction B) (fun g i ↦ (x i).prop g) h.exists_algebraMap_mul_eq

/-- **Fontaine's comparison map is injective** for a regular period ring `B` with field of
invariants `E`. -/
theorem periodComparison_injective
    (h : TauCeti.IsRegularPeriodRing F E G B) : Function.Injective (ρ.periodComparison B E) := by
  have : Module.Free E (ρ.periodInvariants B E) :=
    .of_divisionRing E (ρ.periodInvariants B E)
  let b := Module.Free.chooseBasis E (ρ.periodInvariants B E)
  refine LinearMap.injective_of_linearIndependent (Algebra.TensorProduct.basis B b).span_eq ?_
  convert ρ.linearIndependent_coe_periodInvariants h b.linearIndependent with i
  simp

/-- The period invariants of a regular period ring have dimension at most `dim_F V`. -/
theorem rank_periodInvariants_le (h : TauCeti.IsRegularPeriodRing F E G B) :
    Module.rank E (ρ.periodInvariants B E) ≤ Cardinal.lift.{uB} (Module.rank F V) := by
  have := h.isDomain
  have : Module.Free E (ρ.periodInvariants B E) :=
    .of_divisionRing E (ρ.periodInvariants B E)
  rw [Module.Free.rank_eq_card_chooseBasisIndex, ← Module.rank_baseChange (R := B)]
  exact (ρ.linearIndependent_coe_periodInvariants h
    (Module.Free.chooseBasis E (ρ.periodInvariants B E)).linearIndependent).cardinal_le_rank

/-- The period invariants of a finite-dimensional representation for a regular period ring are
finite-dimensional. -/
theorem finiteDimensional_periodInvariants [FiniteDimensional F V]
    (h : TauCeti.IsRegularPeriodRing F E G B) : FiniteDimensional E (ρ.periodInvariants B E) :=
  have : Module.Free E (ρ.periodInvariants B E) := .of_divisionRing E (ρ.periodInvariants B E)
  Module.rank_lt_aleph0_iff.1 <| (ρ.rank_periodInvariants_le h).trans_lt <|
    Cardinal.lift_lt_aleph0.2 <| Module.rank_lt_aleph0_iff.2 inferInstance

/-- The period invariants of a finite-dimensional representation for a regular period ring have
dimension at most `dim_F V`. -/
theorem finrank_periodInvariants_le [FiniteDimensional F V]
    (h : TauCeti.IsRegularPeriodRing F E G B) :
    finrank E (ρ.periodInvariants B E) ≤ finrank F V := by
  have := h.isDomain
  have : Module.Free E (ρ.periodInvariants B E) := .of_divisionRing E (ρ.periodInvariants B E)
  have := ρ.finiteDimensional_periodInvariants h
  have := Module.Finite.of_basis (Algebra.TensorProduct.basis B (Module.finBasis F V))
  simpa using (ρ.linearIndependent_coe_periodInvariants h
    (Module.finBasis E (ρ.periodInvariants B E)).linearIndependent).fintype_card_le_finrank

end Monoid

section Group

variable {B} [Group G] [MulSemiringAction G B] [SMulCommClass G F B] (ρ : Representation F G V)
  {E : Type*} [Field E] [Algebra E B] [SMulCommClass F E B] [SMulCommClass G E B]

/-- The diagonal action of `g` is `(g • ·) ⊗ id` followed by the scalar extension of `ρ g`. -/
private theorem periodAction_eq_baseChange (g : G) (x : B ⊗[F] V) :
    ρ.periodAction B g x = (ρ g).baseChange B
      ((MulSemiringAction.toAlgHom F B g).toLinearMap.rTensor V x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c v => simp
  | add x y hx hy => simp_all

/-- The determinant of the matrix of the comparison map, in bases of `D_B(V)` and `V` of the same
size, is multiplied by `g` by the inverse of the determinant of `ρ g`. -/
private theorem det_toMatrix_periodComparison {n : ℕ} (b : Basis (Fin n) E (ρ.periodInvariants B E))
    (b' : Basis (Fin n) F V) (g : G) :
    (LinearMap.toMatrix (Algebra.TensorProduct.basis B b) (Algebra.TensorProduct.basis B b')
      (ρ.periodComparison B E)).det =
      algebraMap F B (LinearMap.det (ρ g)) *
        g • (LinearMap.toMatrix (Algebra.TensorProduct.basis B b)
          (Algebra.TensorProduct.basis B b') (ρ.periodComparison B E)).det := by
  set cV := Algebra.TensorProduct.basis B b'
  set M := LinearMap.toMatrix (Algebra.TensorProduct.basis B b) cV (ρ.periodComparison B E)
  have hcol (i j : Fin n) : M i j = cV.repr (b j) i := by
    simp [M, LinearMap.toMatrix_apply]
  -- Each column of `M` is the coordinate vector of an invariant tensor.
  have hM : M = (LinearMap.toMatrix b' b' (ρ g)).map (algebraMap F B) *
      (MulSemiringAction.toRingHom G B g).mapMatrix M := by
    ext i j
    rw [hcol, ← (b j).prop g, periodAction_eq_baseChange,
      ← LinearMap.toMatrix_mulVec_repr (v₁ := cV) (v₂ := cV)]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hcol, cV]
  conv_lhs => rw [hM]
  rw [Matrix.det_mul, ← RingHom.map_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    LinearMap.det_toMatrix, MulSemiringAction.toRingHom_apply]

/-- **Fontaine's dimension criterion.** For a finite-dimensional representation `V` and a regular
period ring `B` with field of invariants `E`, the comparison map `B ⊗[E] D_B(V) → B ⊗[F] V` is
bijective if and only if `dim_E D_B(V) = dim_F V`. -/
theorem periodComparison_bijective_iff [FiniteDimensional F V]
    (h : TauCeti.IsRegularPeriodRing F E G B) :
    Function.Bijective (ρ.periodComparison B E) ↔
      finrank E (ρ.periodInvariants B E) = finrank F V := by
  have := h.isDomain
  have : Module.Free E (ρ.periodInvariants B E) := .of_divisionRing E (ρ.periodInvariants B E)
  have := ρ.finiteDimensional_periodInvariants h
  refine ⟨fun hbij ↦ ?_, fun hdim ↦ ⟨ρ.periodComparison_injective h, ?_⟩⟩
  · simpa using (LinearEquiv.ofBijective _ hbij).finrank_eq
  let b := Module.finBasisOfFinrankEq E (ρ.periodInvariants B E) hdim
  let b' := Module.finBasis F V
  set cD := Algebra.TensorProduct.basis B b
  set cV := Algebra.TensorProduct.basis B b'
  set M := LinearMap.toMatrix cD cV (ρ.periodComparison B E)
  -- The determinant of `M` is nonzero: its columns, the coordinates of a basis of `D_B(V)`, are
  -- independent over `B`.
  have hne : M.det ≠ 0 := by
    have hinj : Function.Injective M.mulVec := by
      rw [Matrix.mulVec_injective_iff]
      convert (ρ.linearIndependent_coe_periodInvariants h b.linearIndependent).map'
        cV.equivFun.toLinearMap cV.equivFun.ker
      ext i
      simp [M, cD, LinearMap.toMatrix_apply]
    rw [Ne, ← Matrix.exists_mulVec_eq_zero_iff]
    rintro ⟨v, hv, hMv⟩
    exact hv (hinj (hMv.trans M.mulVec_zero.symm))
  -- It spans a `G`-stable line, so it is a unit.
  have hunit : IsUnit M.det := h.isUnit hne fun g ↦ by
    refine Submodule.mem_span_singleton.2 ⟨LinearMap.det (ρ g⁻¹), ?_⟩
    rw [Algebra.smul_def]
    conv_rhs => rw [ρ.det_toMatrix_periodComparison b b' g⁻¹, smul_mul', smul_algebraMap,
      smul_inv_smul]
  intro y
  refine ⟨Matrix.toLin cV cD M⁻¹ y, ?_⟩
  rw [← Matrix.toLin_toMatrix cD cV (ρ.periodComparison B E), ← LinearMap.comp_apply,
    ← Matrix.toLin_mul, Matrix.mul_nonsing_inv _ hunit, Matrix.toLin_one, LinearMap.id_apply]

end Group

end Representation
