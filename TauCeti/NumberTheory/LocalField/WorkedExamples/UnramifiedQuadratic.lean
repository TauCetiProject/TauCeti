/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import TauCeti.NumberTheory.LocalField.ResidueCorrespondence
public import TauCeti.NumberTheory.LocalField.RootsOfUnity.Unramified
public import TauCeti.NumberTheory.LocalField.Unramified.Criterion
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# The unramified quadratic extension `ℚ₂(ζ₃)`

The polynomial `X² + X + 1` is irreducible over `ℚ₂`: a root would make `-3` a square, although
`-3` is not a square modulo `8`. Its root field is the cyclotomic extension `ℚ₂(ζ₃)`, equipped
here with the canonical nonarchimedean local-field structure extending that of `ℚ₂`.

The extension is unramified. Its distinguished root `ζ₃` is integral, and the derivative
`2ζ₃ + 1` has square `-3`, a unit in `ℤ₂`. Thus the simple-root criterion applies. In particular,
the extension has exactly two `2`-power roots of unity, and its arithmetic Frobenius has order two,
so its Galois group is nontrivial.

## Main definitions

* `TauCeti.unramifiedQuadraticPoly`: the polynomial `X² + X + 1` over `ℚ₂`.
* `TauCeti.UnramifiedQuadratic`: its root field `ℚ₂(ζ₃)`.
* `TauCeti.UnramifiedQuadratic.zetaThree`: the distinguished primitive cube root.

## Main results

* `TauCeti.unramifiedQuadraticPoly_irreducible`: `X² + X + 1` is irreducible over `ℚ₂`.
* `TauCeti.UnramifiedQuadratic.finrank_eq_two`: the root field has degree two.
* The instance `TauCeti.IsUnramified ℚ_[2] TauCeti.UnramifiedQuadratic`.
* `TauCeti.localRootOfUnityOrder_two_unramifiedQuadratic`: `q(ℚ₂(ζ₃)) = 2`.
* `TauCeti.nontrivial_algEquiv_unramifiedQuadratic`: the Galois group is nontrivial.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §5.
-/

public section
noncomputable section

open Polynomial ValuativeRel

namespace TauCeti

/-- The third cyclotomic polynomial `X² + X + 1` over `ℚ₂`. -/
noncomputable abbrev unramifiedQuadraticPoly : ℚ_[2][X] := X ^ 2 + X + 1

/-- The third cyclotomic polynomial is irreducible over `ℚ₂`, since its discriminant `-3` is not
a square modulo `8`. -/
theorem unramifiedQuadraticPoly_irreducible : Irreducible unramifiedQuadraticPoly := by
  have hns : ¬ IsSquare (-3 : ℚ_[2]) :=
    Padic.not_isSquare_intCast_of_not_isSquare_zmod (p := 2) (a := -3) (k := 3)
      (by rintro ⟨x, hx⟩; revert x hx; decide)
  have hdeg : unramifiedQuadraticPoly.natDegree = 2 := by
    dsimp only [unramifiedQuadraticPoly]
    compute_degree!
  have hmonic : unramifiedQuadraticPoly.Monic := by
    dsimp only [unramifiedQuadraticPoly]
    monicity!
  rw [hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega),
    Multiset.eq_zero_iff_forall_notMem]
  intro r hr
  rw [mem_roots hmonic.ne_zero, IsRoot] at hr
  dsimp only [unramifiedQuadraticPoly] at hr
  simp only [eval_add, eval_pow, eval_X, eval_one] at hr
  exact hns ⟨2 * r + 1, by linear_combination (-4 : ℚ_[2]) * hr⟩

instance : Fact (Irreducible unramifiedQuadraticPoly) :=
  ⟨unramifiedQuadraticPoly_irreducible⟩

/-- The unramified quadratic extension `ℚ₂(ζ₃)`, presented as the root field of
`X² + X + 1`. -/
abbrev UnramifiedQuadratic : Type := AdjoinRoot unramifiedQuadraticPoly

namespace UnramifiedQuadratic

instance : Field UnramifiedQuadratic :=
  inferInstanceAs (Field (AdjoinRoot unramifiedQuadraticPoly))

instance : Algebra ℚ_[2] UnramifiedQuadratic :=
  inferInstanceAs (Algebra ℚ_[2] (AdjoinRoot unramifiedQuadraticPoly))

/-- The power basis `1, ζ₃` of `ℚ₂(ζ₃)` over `ℚ₂`. -/
private def powerBasis : PowerBasis ℚ_[2] UnramifiedQuadratic :=
  AdjoinRoot.powerBasis (Fact.out : Irreducible unramifiedQuadraticPoly).ne_zero

instance : FiniteDimensional ℚ_[2] UnramifiedQuadratic := powerBasis.finite

instance : CharZero UnramifiedQuadratic :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[2] UnramifiedQuadratic).injective

instance : ValuativeRel UnramifiedQuadratic :=
  finiteExtensionValuativeRel ℚ_[2] UnramifiedQuadratic

instance : TopologicalSpace UnramifiedQuadratic :=
  finiteExtensionNormedFieldTopology ℚ_[2] UnramifiedQuadratic

instance : ValuativeExtension ℚ_[2] UnramifiedQuadratic :=
  finiteExtension_valuativeExtension ℚ_[2] UnramifiedQuadratic

instance : IsNonarchimedeanLocalField UnramifiedQuadratic :=
  finiteExtension_isNonarchimedeanLocalField ℚ_[2] UnramifiedQuadratic

/-- The distinguished primitive cube root in `ℚ₂(ζ₃)`. -/
def zetaThree : UnramifiedQuadratic := AdjoinRoot.root unramifiedQuadraticPoly

/-- The defining equation `ζ₃² + ζ₃ + 1 = 0`. -/
theorem zetaThree_sq_add_zetaThree_add_one : zetaThree ^ 2 + zetaThree + 1 = 0 := by
  have h := AdjoinRoot.eval₂_root unramifiedQuadraticPoly
  simpa [unramifiedQuadraticPoly, zetaThree] using h

/-- The distinguished root `ζ₃` is a primitive cube root of unity. -/
theorem isPrimitiveRoot_zetaThree : IsPrimitiveRoot zetaThree 3 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  apply orderOf_eq_prime
  · calc
      zetaThree ^ 3 =
          (zetaThree - 1) * (zetaThree ^ 2 + zetaThree + 1) + 1 := by ring
      _ = 1 := by rw [zetaThree_sq_add_zetaThree_add_one, mul_zero, zero_add]
  · intro h
    have hrel := zetaThree_sq_add_zetaThree_add_one
    rw [h] at hrel
    norm_num at hrel

/-- The distinguished root generates `ℚ₂(ζ₃)` over `ℚ₂`. -/
theorem adjoin_zetaThree_eq_top : IntermediateField.adjoin ℚ_[2] {zetaThree} = ⊤ :=
  IntermediateField.adjoin_root_eq_top _

/-- The extension `ℚ₂(ζ₃)/ℚ₂` has degree two. -/
theorem finrank_eq_two : Module.finrank ℚ_[2] UnramifiedQuadratic = 2 := by
  rw [powerBasis.finrank, powerBasis, AdjoinRoot.powerBasis_dim]
  dsimp only [unramifiedQuadraticPoly]
  compute_degree!

instance : Algebra.IsQuadraticExtension ℚ_[2] UnramifiedQuadratic := ⟨finrank_eq_two⟩

/-- The extension `ℚ₂(ζ₃)/ℚ₂` is unramified. The integral generator `ζ₃` is a simple root of
`X² + X + 1`, since the square of the derivative `2ζ₃ + 1` is the unit `-3`. -/
instance : IsUnramified ℚ_[2] UnramifiedQuadratic := by
  have hint : IsIntegral 𝒪[ℚ_[2]] zetaThree :=
    ⟨X ^ 2 + X + 1, by monicity!, by simp [zetaThree_sq_add_zetaThree_add_one]⟩
  let b : 𝒪[UnramifiedQuadratic] :=
    ⟨zetaThree, (Valuation.Integers.isIntegral_iff_valuation_le_one
      (Valuation.integer.integers (valuation ℚ_[2])) _).1 hint⟩
  have hb : (b : UnramifiedQuadratic) = zetaThree := rfl
  refine isUnramified_of_adjoin_eq_top_of_isUnit_aeval_derivative (b := b)
    (p := X ^ 2 + X + 1) ?_ ?_ ?_
  · exact adjoin_zetaThree_eq_top
  · apply Subtype.ext
    simp [hb, zetaThree_sq_add_zetaThree_add_one]
  · set u := aeval b (derivative (X ^ 2 + X + 1 : 𝒪[ℚ_[2]][X]))
    have hu : (u : UnramifiedQuadratic) = 2 * zetaThree + 1 := by
      simp only [u, derivative_add, derivative_X_sq, derivative_X, derivative_one, add_zero,
        aeval_add, aeval_mul, aeval_X, map_ofNat, map_one]
      norm_cast
    have hnegThree : u * u = -3 := by
      apply Subtype.ext
      -- Extensionality reduces the equality in the valuation ring to one in the field.
      change (u : UnramifiedQuadratic) * u = (-3 : UnramifiedQuadratic)
      rw [hu]
      linear_combination 4 * zetaThree_sq_add_zetaThree_add_one
    have h3K : IsUnit (3 : 𝒪[ℚ_[2]]) := by
      simpa using (natCastValuation_eq_zero_iff (K := ℚ_[2]) 3 (by norm_num)).1 (by
        rw [Padic.natCastValuation_eq_padicValNat]
        exact padicValNat.eq_zero_of_not_dvd (by norm_num))
    have hnegThreeL : IsUnit (-3 : 𝒪[UnramifiedQuadratic]) := by
      rw [← map_ofNat (algebraMap 𝒪[ℚ_[2]] 𝒪[UnramifiedQuadratic]) 3]
      exact IsUnit.neg (h3K.map _)
    exact isUnit_of_mul_isUnit_left (hnegThree ▸ hnegThreeL)

end UnramifiedQuadratic

/-- The `2`-power roots of unity in `ℚ₂(ζ₃)` have order two. -/
theorem localRootOfUnityOrder_two_unramifiedQuadratic :
    localRootOfUnityOrder 2 UnramifiedQuadratic
      (finite_pPowerRootsOfUnity (by norm_num)) = 2 :=
  localRootOfUnityOrder_two_of_isUnramified UnramifiedQuadratic (by norm_num)

/-- The automorphism group of the unramified quadratic extension `ℚ₂(ζ₃)/ℚ₂` is nontrivial. -/
theorem nontrivial_algEquiv_unramifiedQuadratic :
    Nontrivial (UnramifiedQuadratic ≃ₐ[ℚ_[2]] UnramifiedQuadratic) := by
  let _ : IsGalois ℚ_[2] UnramifiedQuadratic := inferInstance
  apply nontrivial_of_ne (frobeniusAlgEquiv (K := ℚ_[2]) (L := UnramifiedQuadratic)) 1
  intro h
  have horder := orderOf_frobeniusAlgEquiv (K := ℚ_[2]) (L := UnramifiedQuadratic)
  rw [h, orderOf_one, IsUnramified.inertiaDegree_eq_finrank,
    UnramifiedQuadratic.finrank_eq_two] at horder
  norm_num at horder

end TauCeti
