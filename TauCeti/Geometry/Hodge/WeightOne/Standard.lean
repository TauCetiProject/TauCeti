/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.PeriodDomain
public import TauCeti.Geometry.Hodge.WeightOne.RiemannForm
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# The standard principally polarized Hodge structure of weight one on `ℤ^{2g}`

For a finite type `l` (of cardinality `g`), this file constructs the standard polarized effective
Hodge structure of weight one on the lattice `ℤ^{l ⊕ l} ≅ ℤ^{2g}`. Its datum `(Λ, J, E)` of a
lattice, a complex structure and a Riemann form is that of the complex torus `ℂ^g / (ℤ^g + i ℤ^g)`
with its standard principal polarization.

Both of its data are given by Mathlib's standard symplectic matrix
`Matrix.J l ℤ = !![0, -1; 1, 0]`:

* the complex structure on the realification `ℝ ⊗[ℤ] ℤ^{l ⊕ l}` acts in coordinates by
  `Matrix.J l ℝ`, that is, `(x, y) ↦ (-y, x)`;
* the Riemann form is the standard symplectic form `Matrix.toBilin' (Matrix.J l ℤ)`, the form
  behind Mathlib's `Matrix.symplecticGroup l ℤ`.

The Riemann bilinear relations reduce to the matrix identities `Jᵀ J J = J` and `Jᵀ J = 1`, so the
symplectic form is a Riemann form (`TauCeti.AlmostComplexStructure.IsRiemannForm`). The Hodge
structure and its polarization are then the general constructions
`TauCeti.AlmostComplexStructure.latticeHodgeStructure` and
`TauCeti.AlmostComplexStructure.IsRiemannForm.polarization`, computed here on the coordinate
complexification `ℂ^{l ⊕ l}`. Its Hodge numbers are `h^{1,0} = h^{0,1} = g`, and it is a point of
the period domain of `(ℤ^{l ⊕ l}, Matrix.J)` at its own Hodge type.

The construction and conventions follow Birkenhake–Lange, *Complex Abelian Varieties*, §4.1 and
Chapter 8 (the standard symplectic lattice), Voisin, *Hodge Theory and Complex Algebraic
Geometry I*, §6 and §7, and Peters–Steenbrink, *Mixed Hodge Structures*, §2.

## Main declarations

* `TauCeti.Hodge.StandardWeightOne.almostComplexStructure`: the standard complex structure on the
  realification of `ℤ^{l ⊕ l}`.
* `TauCeti.Hodge.StandardWeightOne.riemannForm`: the standard symplectic form on `ℤ^{l ⊕ l}`.
* `TauCeti.Hodge.StandardWeightOne.isRiemannForm_riemannForm`: it is a Riemann form.
* `TauCeti.Hodge.StandardWeightOne.hodgeStructure`: the standard effective weight-one Hodge
  structure on `ℤ^{l ⊕ l}`.
* `TauCeti.Hodge.StandardWeightOne.hodgeStructure_hodgeNumber`: its Hodge numbers.
* `TauCeti.Hodge.StandardWeightOne.polarization`: its polarization by the symplectic form.
* `TauCeti.Hodge.StandardWeightOne.point`: the corresponding point of the period domain.
-/

public section

namespace TauCeti.Hodge.StandardWeightOne

open Matrix
open scoped TensorProduct

variable (l : Type*)

/-! ### The standard lattice and its complexification -/

/-- The integral lattice `ℤ^{l ⊕ l}` underlying the standard weight-one example. -/
abbrev Lattice := l ⊕ l → ℤ

/-- The rational vector space `ℚ^{l ⊕ l}` underlying the standard weight-one example. -/
abbrev RationalSpace := l ⊕ l → ℚ

/-- The complex vector space `ℂ^{l ⊕ l}` underlying the standard weight-one example. -/
abbrev ComplexSpace := l ⊕ l → ℂ

/-- The rational scalar action on the complexification of the standard rational space. -/
noncomputable local instance moduleRatOfComplex : Module ℚ (ComplexSpace l) :=
  Module.restrictScalars ℚ ℂ (ComplexSpace l)

/-- Coordinatewise inclusion of the standard lattice into its rationalization. -/
def latticeToRational : Lattice l →ₗ[ℤ] RationalSpace l :=
  (Algebra.linearMap ℤ ℚ).compLeft (l ⊕ l)

/-- Coordinatewise inclusion of the standard lattice into its complexification. -/
def latticeToComplex : Lattice l →ₗ[ℤ] ComplexSpace l :=
  (Algebra.linearMap ℤ ℂ).compLeft (l ⊕ l)

@[simp]
theorem latticeToRational_apply (x : Lattice l) (i : l ⊕ l) :
    latticeToRational l x i = (x i : ℚ) := (rfl)

@[simp]
theorem latticeToComplex_apply (x : Lattice l) (i : l ⊕ l) :
    latticeToComplex l x i = (x i : ℂ) := (rfl)

section Finite

variable [Finite l]

/-- The coordinatewise rational inclusion is a base change from `ℤ` to `ℚ`. -/
theorem isBaseChange_latticeToRational : IsBaseChange ℚ (latticeToRational l) :=
  IsBaseChange.finitePow _ (IsBaseChange.linearMap ℤ ℚ)

/-- The coordinatewise complex inclusion is a base change from `ℤ` to `ℂ`. -/
theorem isBaseChange_latticeToComplex : IsBaseChange ℂ (latticeToComplex l) :=
  IsBaseChange.finitePow _ (IsBaseChange.linearMap ℤ ℂ)

/-- Coordinatewise inclusion of the rationalization into the complexification. -/
noncomputable def rationalToComplex : RationalSpace l →ₗ[ℚ] ComplexSpace l :=
  Hodge.rationalToComplexMap (isBaseChange_latticeToRational l) (latticeToComplex l)

@[simp]
theorem rationalToComplex_apply (x : RationalSpace l) (i : l ⊕ l) :
    rationalToComplex l x i = (x i : ℂ) := by
  induction x using (isBaseChange_latticeToRational l).inductionOn with
  | tmul x =>
      rw [rationalToComplex, Hodge.rationalToComplexMap_apply_ι]
      simp
  | smul q x hx =>
      rw [LinearMap.map_smul (rationalToComplex l)]
      -- The rational action on `ComplexSpace l` is the local restricted-scalar instance, which
      -- has no application lemma; expose it as multiplication by the cast scalar.
      change (q : ℂ) * rationalToComplex l x i = _
      simp [hx]
  | add x y hx hy =>
      simp [hx, hy]

/-- The coordinatewise inclusion from `ℚ^{l ⊕ l}` to `ℂ^{l ⊕ l}` is a base change. -/
theorem isBaseChange_rationalToComplex : IsBaseChange ℂ (rationalToComplex l) :=
  Hodge.isBaseChange_rationalToComplexMap (isBaseChange_latticeToRational l)
    (isBaseChange_latticeToComplex l)

/-- Lattice conjugation for the coordinate complexification is coordinatewise complex
conjugation. -/
@[simp]
theorem latticeConj_apply (z : ComplexSpace l) :
    latticeConj (isBaseChange_latticeToComplex l) z = star z := by
  rw [← latticeConj_unique (isBaseChange_latticeToComplex l)
    (starLinearEquiv ℂ (A := ComplexSpace l)).toLinearMap]
  · rfl
  · intro x
    ext
    simp

private theorem isBaseChange_latticeToReal :
    IsBaseChange ℝ ((Algebra.linearMap ℤ ℝ).compLeft (l ⊕ l)) :=
  IsBaseChange.finitePow _ (IsBaseChange.linearMap ℤ ℝ)

/-- Coordinates on the realification of the standard lattice. -/
private noncomputable def realCoord : Realification (Lattice l) ≃ₗ[ℝ] (l ⊕ l → ℝ) :=
  (isBaseChange_latticeToReal l).equiv

private theorem realCoord_one_tmul (x : Lattice l) :
    realCoord l (1 ⊗ₜ[ℤ] x) = fun i ↦ (x i : ℝ) := by
  rw [realCoord, IsBaseChange.equiv_tmul, one_smul]
  rfl

end Finite

/-! ### The standard complex structure and Riemann form -/

variable [Fintype l] [DecidableEq l]

/-- The integral matrix `J` sends the cast of a vector to the cast of its image. -/
private theorem J_mulVec_comp_cast {R : Type*} [CommRing R] (x : Lattice l) :
    J l R *ᵥ (fun i ↦ (x i : R)) = fun i ↦ ((J l ℤ *ᵥ x) i : R) := by
  ext i
  have h := RingHom.map_mulVec (Int.castRingHom R) (J l ℤ) x i
  rw [map_J] at h
  exact h.symm

omit [DecidableEq l] in
/-- Casting integer vectors commutes with the dot product. -/
private theorem cast_dotProduct {R : Type*} [CommRing R] (x y : Lattice l) :
    ((x ⬝ᵥ y : ℤ) : R) = (fun i ↦ (x i : R)) ⬝ᵥ fun i ↦ (y i : R) :=
  RingHom.map_dotProduct (Int.castRingHom R) x y

/-- The standard complex structure on the realification `ℝ ⊗[ℤ] ℤ^{l ⊕ l}`: in coordinates it is
the matrix `J = !![0, -1; 1, 0]`, sending `(x, y)` to `(-y, x)`. -/
noncomputable def almostComplexStructure : AlmostComplexStructure (Realification (Lattice l)) where
  toLinearMap := (realCoord l).symm.conj (toLin' (J l ℝ))
  square_neg := by
    rw [← LinearEquiv.conj_comp, ← toLin'_mul, J_squared, map_neg, toLin'_one, map_neg,
      LinearEquiv.conj_id]

private theorem realCoord_almostComplexStructure (x : Realification (Lattice l)) :
    realCoord l (almostComplexStructure l x) = J l ℝ *ᵥ realCoord l x := by
  simp [almostComplexStructure, LinearEquiv.conj_apply_apply]

/-- The standard complex structure is the scalar extension of the integral matrix `J`. -/
@[simp]
theorem almostComplexStructure_one_tmul (x : Lattice l) :
    almostComplexStructure l (1 ⊗ₜ[ℤ] x) = 1 ⊗ₜ[ℤ] (J l ℤ *ᵥ x) := by
  apply (realCoord l).injective
  rw [realCoord_almostComplexStructure, realCoord_one_tmul, realCoord_one_tmul,
    J_mulVec_comp_cast]

/-- The standard symplectic form on `ℤ^{l ⊕ l}`: the bilinear form of the matrix
`J = !![0, -1; 1, 0]`, which also defines Mathlib's `Matrix.symplecticGroup l ℤ`. -/
noncomputable def riemannForm : LinearMap.BilinForm ℤ (Lattice l) :=
  toBilin' (J l ℤ)

/-- The standard symplectic form is the bilinear form of `Matrix.J l ℤ`. -/
theorem riemannForm_def : riemannForm l = toBilin' (J l ℤ) := (rfl)

/-- In coordinates, the standard symplectic form is
`Q(x, y) = ∑ᵢ (x_{inr i} y_{inl i} - x_{inl i} y_{inr i})`. -/
@[simp]
theorem riemannForm_apply (x y : Lattice l) :
    riemannForm l x y = ∑ i, (x (.inr i) * y (.inl i) - x (.inl i) * y (.inr i)) := by
  simp only [riemannForm, toBilin'_apply', J, fromBlocks_mulVec, zero_mulVec, neg_mulVec,
    one_mulVec, zero_add, add_zero, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Pi.neg_apply, Function.comp_apply, mul_neg, Finset.sum_neg_distrib, Finset.sum_sub_distrib]
  ring

/-- The real scalar extension of the standard symplectic form, in coordinates. -/
private theorem baseChange_riemannForm_apply (x y : Realification (Lattice l)) :
    (riemannForm l).baseChange ℝ x y = toBilin' (J l ℝ) (realCoord l x) (realCoord l y) := by
  have h := TensorProduct.isBaseChange ℤ (Lattice l) ℝ
  suffices (riemannForm l).baseChange ℝ =
      (toBilin' (J l ℝ)).compl₁₂ (realCoord l).toLinearMap (realCoord l).toLinearMap by
    rw [this]
    rfl
  refine h.algHom_ext _ _ fun x ↦ h.algHom_ext _ _ fun y ↦ ?_
  simp [riemannForm, LinearMap.BilinForm.baseChange_tmul, realCoord_one_tmul, toBilin'_apply',
    J_mulVec_comp_cast, cast_dotProduct]

/-- **The standard symplectic form is a Riemann form for the standard complex structure**: the
two Riemann bilinear relations are the matrix identities `Jᵀ J J = J` and `Jᵀ J = 1`. -/
theorem isRiemannForm_riemannForm :
    (almostComplexStructure l).IsRiemannForm (riemannForm l) where
  isAlt x := by
    simp only [riemannForm_apply]
    exact Finset.sum_eq_zero fun i _ ↦ by ring
  invariant x y := by
    rw [baseChange_riemannForm_apply, baseChange_riemannForm_apply,
      realCoord_almostComplexStructure, realCoord_almostComplexStructure, ← toLin'_apply,
      ← toLin'_apply, ← LinearMap.BilinForm.comp_apply, toBilin'_comp, J_transpose, Matrix.neg_mul,
      J_squared, neg_neg, Matrix.one_mul]
  positive x hx := by
    -- `E_ℝ (J x) x = (J x) ⬝ᵥ (J x)`, a sum of squares, and `J x ≠ 0` since `J` is invertible.
    rw [baseChange_riemannForm_apply, realCoord_almostComplexStructure, toBilin'_apply']
    refine lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _) (Ne.symm ?_)
    rw [Ne, dotProduct_self_eq_zero]
    intro h
    have h' := congrArg (J l ℝ *ᵥ ·) h
    simp only [mulVec_mulVec, J_squared, mulVec_zero, neg_mulVec, one_mulVec, neg_eq_zero,
      LinearEquiv.map_eq_zero_iff] at h'
    exact hx h'

/-! ### The standard Hodge structure -/

/-- The standard effective Hodge structure of weight one on `ℤ^{l ⊕ l}`: the Hodge structure of
the standard complex structure. Its `H^{1,0}` is the `i`-eigenspace of `J` on `ℂ^{l ⊕ l}`. -/
noncomputable def hodgeStructure : HodgeStructure (isBaseChange_latticeToComplex l) 1 :=
  (almostComplexStructure l).latticeHodgeStructure (isBaseChange_latticeToComplex l)

/-- The complex-linear extension of the standard complex structure to `ℂ^{l ⊕ l}` is the matrix
`J`. -/
private theorem latticeComplexification_almostComplexStructure :
    (almostComplexStructure l).latticeComplexification (isBaseChange_latticeToComplex l) =
      toLin' (J l ℂ) := by
  refine (isBaseChange_latticeToComplex l).algHom_ext _ _ fun x ↦ ?_
  conv_lhs => rw [← realificationComplexEquiv_one_tmul_realificationMap
    (isBaseChange_latticeToComplex l)]
  rw [AlmostComplexStructure.latticeComplexification_realificationComplexEquiv_one_tmul,
    realificationMap_apply, almostComplexStructure_one_tmul, ← realificationMap_apply,
    realificationComplexEquiv_one_tmul_realificationMap, toLin'_apply]
  exact (J_mulVec_comp_cast l (R := ℂ) x).symm

/-- The filtration is top in nonpositive degrees, the `i`-eigenspace of `J` in degree one, and
bottom above degree one. -/
@[simp]
theorem hodgeStructure_F (p : ℤ) :
    (hodgeStructure l).F p = if p ≤ 0 then ⊤ else if p = 1 then
      Module.End.eigenspace (toLin' (J l ℂ)) Complex.I else ⊥ := by
  rw [hodgeStructure, AlmostComplexStructure.latticeHodgeStructure_F,
    latticeComplexification_almostComplexStructure]

/-- The standard weight-one Hodge structure is effective. -/
theorem isEffective_hodgeStructure : (hodgeStructure l).IsEffective :=
  AlmostComplexStructure.isEffective_latticeHodgeStructure _ _

/-- The `H^{1,0}` component is the `i`-eigenspace of `J`. -/
@[simp]
theorem hodgeStructure_piece_one :
    (hodgeStructure l).piece 1 = Module.End.eigenspace (toLin' (J l ℂ)) Complex.I := by
  rw [hodgeStructure, AlmostComplexStructure.latticeHodgeStructure_piece_one,
    latticeComplexification_almostComplexStructure]

/-- The `H^{0,1}` component is the `-i`-eigenspace of `J`. -/
@[simp]
theorem hodgeStructure_piece_zero :
    (hodgeStructure l).piece 0 = Module.End.eigenspace (toLin' (J l ℂ)) (-Complex.I) := by
  rw [hodgeStructure, AlmostComplexStructure.latticeHodgeStructure_piece_zero,
    latticeComplexification_almostComplexStructure]

/-- Every Hodge component except `H^{1,0}` and `H^{0,1}` vanishes. -/
theorem hodgeStructure_piece_eq_bot {p : ℤ} (hpzero : p ≠ 0) (hpone : p ≠ 1) :
    (hodgeStructure l).piece p = ⊥ :=
  AlmostComplexStructure.latticeHodgeStructure_piece_eq_bot _ _ hpzero hpone

/-- The Weil operator of the standard weight-one Hodge structure is the matrix `J`. -/
@[simp]
theorem hodgeStructure_weilOperator : (hodgeStructure l).weilOperator = toLin' (J l ℂ) := by
  rw [hodgeStructure, AlmostComplexStructure.latticeHodgeStructure_weilOperator,
    latticeComplexification_almostComplexStructure]

/-- **The Hodge numbers of the standard structure**: `h^{1,0} = h^{0,1} = g`, where `g` is the
cardinality of `l`, and all other Hodge numbers vanish. -/
theorem hodgeStructure_hodgeNumber (p : ℤ) :
    (hodgeStructure l).hodgeNumber p = if p = 0 ∨ p = 1 then Fintype.card l else 0 := by
  have hzero : ∀ p, p ≠ 0 → p ≠ 1 → (hodgeStructure l).hodgeNumber p = 0 := fun p h₀ h₁ ↦ by
    rw [HodgeStructureOn.hodgeNumber_def, hodgeStructure_piece_eq_bot l h₀ h₁, finrank_bot]
  have hsymm : (hodgeStructure l).hodgeNumber 1 = (hodgeStructure l).hodgeNumber 0 :=
    (hodgeStructure l).hodgeNumber_symm 1
  have hsum : (hodgeStructure l).hodgeNumber 0 + (hodgeStructure l).hodgeNumber 1 =
      2 * Fintype.card l := by
    have h := finsum_hodgeNumber_eq_finrank_lattice (hodgeStructure l)
    rw [finsum_eq_sum_of_support_subset (s := {0, 1}) _ fun p hp ↦ by
      by_contra hp'
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_or] at hp'
      exact hp (hzero p hp'.1 hp'.2)] at h
    rw [Finset.sum_pair (by decide), Module.finrank_fintype_fun_eq_card, Fintype.card_sum] at h
    omega
  split_ifs with hp
  · rcases hp with rfl | rfl <;> omega
  · exact hzero p (not_or.mp hp).1 (not_or.mp hp).2

/-! ### The standard polarization -/

/-- The standard symplectic form, bundled as a polarization of the standard weight-one Hodge
structure. -/
noncomputable def polarization :
    Polarization (isBaseChange_latticeToComplex l) (hodgeStructure l) :=
  (isRiemannForm_riemannForm l).polarization (isBaseChange_latticeToComplex l)

@[simp]
theorem polarization_Qint : (polarization l).Qint = riemannForm l :=
  AlmostComplexStructure.IsRiemannForm.polarization_Qint _ _

/-- The complex form of the standard polarization is the symplectic form of `J` on
`ℂ^{l ⊕ l}`. -/
@[simp]
theorem polarization_Q : (polarization l).Q = toBilin' (J l ℂ) := by
  rw [Polarization.Q_def, polarization_Qint]
  symm
  refine integralFormBaseChange_unique _ _ _ fun x y ↦ ?_
  rw [riemannForm, toBilin'_apply', toBilin'_apply', cast_dotProduct]
  exact congrArg _ (J_mulVec_comp_cast l y)

/-- The standard polarized weight-one Hodge structure as a point of the period domain of
`(ℤ^{l ⊕ l}, Matrix.J)` at its own Hodge type. -/
noncomputable def point :
    PeriodDomain.Point (isBaseChange_latticeToComplex l) 1 (riemannForm l)
      (hodgeStructure l).hodgeType where
  hs := hodgeStructure l
  htype_weight := HodgeStructureOn.hodgeType_weight _
  pol := (isRiemannForm_riemannForm l).isPolarization _
  hodge_numbers _ := by rw [HodgeStructureOn.hodgeType_h]

@[simp]
theorem point_hs : (point l).hs = hodgeStructure l := by
  rfl

end TauCeti.Hodge.StandardWeightOne
