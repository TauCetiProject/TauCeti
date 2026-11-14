/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RankOne.Basic
public import TauCeti.NumberTheory.IntegralLattice.DiscriminantGenus
import Mathlib.Tactic.FinCases
import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Operations
import TauCeti.LinearAlgebra.IntegralLattice.RankOne.Discriminant
import TauCeti.LinearAlgebra.IntegralLattice.StandardCoordinates
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Form

/-!
# Binary genus witnesses of odd discriminant

This file constructs two concrete rank-two test pairs of odd discriminant illustrating the genus
classification of `TauCeti.NumberTheory.IntegralLattice.DiscriminantGenus`:

* `⟨1⟩ ⊕ ⟨5⟩` and `binaryDeterminantFive` (`!![2, 1; 1, 3]`) are positive definite odd binary
  lattices of determinant `5` that **do not** lie in the same genus: the discriminant pairing of
  `⟨1⟩ ⊕ ⟨5⟩` on `ℤ/5` takes values `k² / 5 mod ℤ`, whereas `!![2, 1; 1, 3]` has a dual vector
  `(3/5, -1/5)` of self-pairing `3/5 mod ℤ`, and `3` is a quadratic nonresidue modulo `5`.
* `⟨1⟩ ⊕ ⟨39⟩` and `⟨3⟩ ⊕ ⟨13⟩` are positive definite odd binary lattices of determinant `39`
  that **lie in the same genus** (`1/3 + 9/13 = 40/39 ≡ 1/39 mod ℤ`), yet are **not isometric**
  because only the first represents `1`.

## Main results

* `TauCeti.IntegralLattice.binaryDeterminantFive`: the positive definite odd binary lattice on
  `Fin 2 → ℚ` with Gram matrix `!![2, 1; 1, 3]`, together with its carrier, form, determinant,
  non-evenness, and positive-definiteness characterizations.
* `TauCeti.IntegralLattice.not_sameGenus_rankOne_one_five_binaryDeterminantFive`: `⟨1⟩ ⊕ ⟨5⟩` and
  `binaryDeterminantFive` lie in distinct genera.
* `TauCeti.IntegralLattice.sameGenus_rankOne_one_thirtyNine_three_thirteen` and
  `TauCeti.IntegralLattice.isEmpty_isometry_rankOne_one_thirtyNine_three_thirteen`: `⟨1⟩ ⊕ ⟨39⟩`
  and `⟨3⟩ ⊕ ⟨13⟩` lie in one genus but are not isometric.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, Corollaries
  1.9.4 and 1.16.3.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

namespace TauCeti.IntegralLattice

private def binaryFiveMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 3]

private theorem binaryFiveMatrix_isSymm : binaryFiveMatrix.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The positive definite odd binary integral lattice on `Fin 2 → ℚ` with Gram matrix
`!![2, 1; 1, 3]` and determinant `5`. -/
noncomputable def binaryDeterminantFive : IntegralLattice (Fin 2 → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin 2)) binaryFiveMatrix binaryFiveMatrix_isSymm

/-- `binaryDeterminantFive` is the standard-coordinate lattice of the Gram matrix
`!![2, 1; 1, 3]`. -/
theorem binaryDeterminantFive_eq_ofGramMatrix
    (hG : (!![2, 1; 1, 3] : Matrix (Fin 2) (Fin 2) ℤ).IsSymm) :
    binaryDeterminantFive = ofGramMatrix (Pi.basisFun ℚ (Fin 2)) !![2, 1; 1, 3] hG := by
  rfl

/-- A rational vector belongs to `binaryDeterminantFive` exactly when both coordinates are
integers. -/
@[simp]
theorem mem_binaryDeterminantFive_carrier_iff (x : Fin 2 → ℚ) :
    x ∈ binaryDeterminantFive.carrier ↔ ∀ i, ∃ z : ℤ, (z : ℚ) = x i :=
  mem_ofGramMatrix_basisFun_carrier_iff binaryFiveMatrix binaryFiveMatrix_isSymm x

/-- Coordinate formula for the bilinear form of `binaryDeterminantFive`. -/
@[simp]
theorem binaryDeterminantFive_form_apply (x y : Fin 2 → ℚ) :
    binaryDeterminantFive.form x y =
      2 * x 0 * y 0 + x 0 * y 1 + x 1 * y 0 + 3 * x 1 * y 1 := by
  rw [binaryDeterminantFive, form_ofGramMatrix_basisFun_apply]
  simp only [Fin.sum_univ_two, binaryFiveMatrix, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Int.cast_ofNat, Int.cast_one]
  ring

/-- The signed determinant of `binaryDeterminantFive` is `5`. -/
@[simp]
theorem binaryDeterminantFive_determinant : binaryDeterminantFive.determinant = 5 := by
  rw [binaryDeterminantFive, determinant_ofGramMatrix]
  norm_num [binaryFiveMatrix, Matrix.det_fin_two]

/-- The lattice `binaryDeterminantFive` is nondegenerate. -/
instance : binaryDeterminantFive.IsNondegenerate :=
  ⟨binaryDeterminantFive.determinant_ne_zero_iff.mp (by simp)⟩

/-- The lattice `binaryDeterminantFive` is odd: its second basis vector has norm `3`. -/
@[simp]
theorem not_isEven_binaryDeterminantFive : ¬binaryDeterminantFive.IsEven := by
  intro he
  dsimp only [binaryDeterminantFive] at he
  let b := ofGramMatrix.basis (Pi.basisFun ℚ (Fin 2)) binaryFiveMatrix binaryFiveMatrix_isSymm
  have h1 := ((ofGramMatrix (Pi.basisFun ℚ (Fin 2)) binaryFiveMatrix
    binaryFiveMatrix_isSymm).isEven_iff_basis b).mp he 1
  rw [integralNorm_apply, ← gramMatrix_apply, gramMatrix_ofGramMatrix] at h1
  exact (by decide : ¬Even (binaryFiveMatrix 1 1)) h1

/-- The lattice `binaryDeterminantFive` is positive definite. -/
theorem binaryDeterminantFive_isPosDef : binaryDeterminantFive.IsPosDef := by
  rw [binaryDeterminantFive.isPosDef_iff]
  intro x hx
  rw [binaryDeterminantFive_form_apply]
  have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra! h
    apply hx
    ext i
    fin_cases i <;> simp [h]
  rcases hx' with h | h
  · have := sq_pos_iff.mpr h
    nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 1)]
  · have := sq_pos_iff.mpr h
    nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0)]

private theorem zsmul_val_rankOneDiscriminantEquiv_rankOneClass (a : ℤ) [NeZero a]
    (c : (rankOne a).DiscriminantGroup) :
    ((rankOneDiscriminantEquiv a c).val : ℤ) • rankOneClass a = c := by
  apply (rankOneDiscriminantEquiv a).injective
  rw [rankOneDiscriminantEquiv_zsmul_rankOneClass, Int.cast_natCast, ZMod.natCast_zmod_val]

private theorem subsingleton_discriminantBilinearModule_rankOne_one :
    Subsingleton (rankOne 1).discriminantBilinearModule := by
  rw [subsingleton_discriminantBilinearModule_iff,
    ← (rankOne 1).isUnimodular_iff_subsingleton_discriminantGroup]
  exact (isUnimodular_rankOne_iff 1).mpr isUnit_one

/-- **`⟨1⟩ ⊕ ⟨5⟩` and `!![2, 1; 1, 3]` do not lie in the same genus.** Both are positive definite
odd binary lattices of determinant `5`, yet the discriminant pairing of `⟨1⟩ ⊕ ⟨5⟩` takes values
`k² / 5 mod ℤ` while `!![2, 1; 1, 3]` has a dual vector `(3/5, -1/5)` of self-pairing
`3/5 mod ℤ`. -/
theorem not_sameGenus_rankOne_one_five_binaryDeterminantFive :
    ¬((rankOne 1).orthogonalSum (rankOne 5)).SameGenus binaryDeterminantFive := by
  have : NeZero (5 : ℤ) := ⟨by decide⟩
  have := subsingleton_discriminantBilinearModule_rankOne_one
  intro h
  obtain ⟨f⟩ := h.symm.nonempty_isometry_discriminantBilinearModule
  let v_vec : Fin 2 → ℚ := ![3 / 5, -1 / 5]
  have hv_dual : v_vec ∈ binaryDeterminantFive.dualCarrier := by
    rw [binaryDeterminantFive, mem_ofGramMatrix_basisFun_dualCarrier_iff]
    intro i
    fin_cases i
    · exact ⟨1, by simp [v_vec, binaryFiveMatrix, Fin.sum_univ_two]; norm_num⟩
    · exact ⟨0, by simp [v_vec, binaryFiveMatrix, Fin.sum_univ_two]; norm_num⟩
  let c : binaryDeterminantFive.discriminantBilinearModule :=
    Submodule.Quotient.mk ⟨v_vec, hv_dual⟩
  have hpair_c : binaryDeterminantFive.discriminantBilinearModule.pairing c c =
      ((3 / 5 : ℚ) : AddCircle (1 : ℚ)) := by
    rw [discriminantBilinearModule_pairing, discriminantPairing_mk,
      binaryDeterminantFive_form_apply]
    congr 1
    simp [v_vec]
    norm_num
  -- Decompose `f c` in `A_{⟨1⟩ ⊕ ⟨5⟩} ≃ A_{⟨1⟩} × A_{⟨5⟩}`; `A_{⟨1⟩}` is trivial.
  let e := (rankOne 1).discriminantBilinearIsometryOrthogonalSum (rankOne 5)
  have hpair_img := (e.map_pairing (f c) (f c)).trans (f.map_pairing c c)
  rw [hpair_c, FiniteBilinearModule.prod_pairing, Subsingleton.elim (e (f c)).1 0,
    FiniteBilinearModule.pairing_zero_left, zero_add] at hpair_img
  let c₅ : (rankOne 5).DiscriminantGroup := (e (f c)).2
  let k : ℕ := (rankOneDiscriminantEquiv 5 c₅).val
  have hk_lt : k < 5 := ZMod.val_lt _
  have hc5_pair : (rankOne 5).discriminantBilinearModule.pairing (e (f c)).2 (e (f c)).2 =
      ((((k : ℤ) : ℚ) * ((k : ℤ) : ℚ) / (5 : ℤ) : ℚ) : AddCircle (1 : ℚ)) := by
    rw [(rankOne 5).discriminantBilinearModule_pairing c₅ c₅,
      ← zsmul_val_rankOneDiscriminantEquiv_rankOneClass 5 c₅,
      discriminantPairing_zsmul_rankOneClass]
  rw [hc5_pair, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at hpair_img
  obtain ⟨m, hm⟩ := hpair_img
  rw [zsmul_one] at hm
  have hmod : (k : ℤ) * k - 3 = 5 * m := by
    have hq : ((k : ℤ) * k - 3 : ℚ) = (5 * m : ℤ) := by
      push_cast at hm ⊢
      linarith
    exact_mod_cast hq
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with
    hk | hk | hk | hk | hk <;> (rw [hk] at hmod; omega)

/-- The additive homomorphism `ZMod 39 →+ A_{⟨3⟩} × A_{⟨13⟩}` sending `k` to
`(k • rankOneClass 3, (3 * k) • rankOneClass 13)`. -/
private noncomputable def zmodThirtyNineHomProd :
    ZMod 39 →+ (rankOne 3).DiscriminantGroup × (rankOne 13).DiscriminantGroup :=
  haveI : NeZero (3 : ℤ) := ⟨by decide⟩
  haveI : NeZero (13 : ℤ) := ⟨by decide⟩
  ((rankOneDiscriminantEquiv 3).symm.toAddMonoidHom.comp
      (ZMod.castHom (by decide : 3 ∣ 39) (ZMod 3)).toAddMonoidHom).prod
    ((rankOneDiscriminantEquiv 13).symm.toAddMonoidHom.comp
      ((3 : ℕ) • (ZMod.castHom (by decide : 13 ∣ 39) (ZMod 13)).toAddMonoidHom))

private theorem zmodThirtyNineHomProd_intCast (k : ℤ) :
    zmodThirtyNineHomProd (k : ZMod 39) =
      (haveI : NeZero (3 : ℤ) := ⟨by decide⟩
       haveI : NeZero (13 : ℤ) := ⟨by decide⟩
       (k • rankOneClass 3, (3 * k) • rankOneClass 13)) := by
  have : NeZero (3 : ℤ) := ⟨by decide⟩
  have : NeZero (13 : ℤ) := ⟨by decide⟩
  ext
  · apply (rankOneDiscriminantEquiv 3).injective
    rw [rankOneDiscriminantEquiv_zsmul_rankOneClass]
    simp [zmodThirtyNineHomProd]
  · apply (rankOneDiscriminantEquiv 13).injective
    rw [rankOneDiscriminantEquiv_zsmul_rankOneClass]
    simp [zmodThirtyNineHomProd]

/-- The pairing-preserving morphism `A_{⟨1⟩} × A_{⟨39⟩} → A_{⟨3⟩} × A_{⟨13⟩}` sending the generator
of `ℤ/39` to `(1, 3) ∈ ℤ/3 × ℤ/13` via `1/3 + 9/13 = 40/39 ≡ 1/39 (mod 1)`. -/
private noncomputable def discriminantHom_one_thirtyNine_three_thirteen :
    FiniteBilinearModule.Hom
      ((rankOne 1).discriminantBilinearModule.prod (rankOne 39).discriminantBilinearModule)
      ((rankOne 3).discriminantBilinearModule.prod (rankOne 13).discriminantBilinearModule) := by
  haveI : NeZero (3 : ℤ) := ⟨by decide⟩
  haveI : NeZero (13 : ℤ) := ⟨by decide⟩
  haveI : NeZero (39 : ℤ) := ⟨by decide⟩
  let φ : ((rankOne 1).discriminantBilinearModule.prod (rankOne 39).discriminantBilinearModule) →+
      ((rankOne 3).discriminantBilinearModule.prod (rankOne 13).discriminantBilinearModule) :=
    { toFun := fun x ↦
        zmodThirtyNineHomProd (rankOneDiscriminantEquiv 39 (x.2 : (rankOne 39).DiscriminantGroup))
      map_zero' :=
        (congrArg zmodThirtyNineHomProd (rankOneDiscriminantEquiv 39).map_zero).trans
          zmodThirtyNineHomProd.map_zero
      map_add' := fun x y ↦
        (congrArg zmodThirtyNineHomProd ((rankOneDiscriminantEquiv 39).map_add x.2 y.2)).trans
          (zmodThirtyNineHomProd.map_add _ _) }
  refine { toAddMonoidHom := φ, map_pairing' := fun x y ↦ ?_ }
  have := subsingleton_discriminantBilinearModule_rankOne_one
  let x₂ : (rankOne 39).DiscriminantGroup := x.2
  let y₂ : (rankOne 39).DiscriminantGroup := y.2
  let kx : ℤ := (rankOneDiscriminantEquiv 39 x₂).val
  let ky : ℤ := (rankOneDiscriminantEquiv 39 y₂).val
  have hx2 : x₂ = kx • rankOneClass 39 :=
    (zsmul_val_rankOneDiscriminantEquiv_rankOneClass 39 x₂).symm
  have hy2 : y₂ = ky • rankOneClass 39 :=
    (zsmul_val_rankOneDiscriminantEquiv_rankOneClass 39 y₂).symm
  have hgx : zmodThirtyNineHomProd (rankOneDiscriminantEquiv 39 x₂) =
      (kx • rankOneClass 3, (3 * kx) • rankOneClass 13) := by
    rw [hx2, rankOneDiscriminantEquiv_zsmul_rankOneClass, zmodThirtyNineHomProd_intCast]
  have hgy : zmodThirtyNineHomProd (rankOneDiscriminantEquiv 39 y₂) =
      (ky • rankOneClass 3, (3 * ky) • rankOneClass 13) := by
    rw [hy2, rankOneDiscriminantEquiv_zsmul_rankOneClass, zmodThirtyNineHomProd_intCast]
  have hφx1 : ((φ x).1 : (rankOne 3).DiscriminantGroup) = kx • rankOneClass 3 :=
    congrArg Prod.fst hgx
  have hφy1 : ((φ y).1 : (rankOne 3).DiscriminantGroup) = ky • rankOneClass 3 :=
    congrArg Prod.fst hgy
  have hφx2 : ((φ x).2 : (rankOne 13).DiscriminantGroup) = (3 * kx) • rankOneClass 13 :=
    congrArg Prod.snd hgx
  have hφy2 : ((φ y).2 : (rankOne 13).DiscriminantGroup) = (3 * ky) • rankOneClass 13 :=
    congrArg Prod.snd hgy
  rw [FiniteBilinearModule.prod_pairing, FiniteBilinearModule.prod_pairing,
    Subsingleton.elim x.1 0, FiniteBilinearModule.pairing_zero_left, zero_add,
    (rankOne 3).discriminantBilinearModule_pairing (φ x).1 (φ y).1,
    (rankOne 13).discriminantBilinearModule_pairing (φ x).2 (φ y).2,
    (rankOne 39).discriminantBilinearModule_pairing x₂ y₂,
    hφx1, hφy1, hφx2, hφy2, hx2, hy2,
    discriminantPairing_zsmul_rankOneClass, discriminantPairing_zsmul_rankOneClass,
    discriminantPairing_zsmul_rankOneClass, ← AddCircle.coe_add, ← sub_eq_zero,
    ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  refine ⟨kx * ky, ?_⟩
  rw [zsmul_one]
  push_cast
  ring

/-- An explicit bilinear isometry between the discriminant forms of `⟨1⟩ ⊕ ⟨39⟩` and
`⟨3⟩ ⊕ ⟨13⟩`. -/
private noncomputable def discriminantIsometry_one_thirtyNine_three_thirteen :
    FiniteBilinearModule.Isometry
      ((rankOne 1).orthogonalSum (rankOne 39)).discriminantBilinearModule
      ((rankOne 3).orthogonalSum (rankOne 13)).discriminantBilinearModule := by
  haveI : NeZero (1 : ℤ) := ⟨by decide⟩
  haveI : NeZero (3 : ℤ) := ⟨by decide⟩
  haveI : NeZero (13 : ℤ) := ⟨by decide⟩
  haveI : NeZero (39 : ℤ) := ⟨by decide⟩
  let g := discriminantHom_one_thirtyNine_three_thirteen
  have hnd : ((rankOne 1).discriminantBilinearModule.prod
      (rankOne 39).discriminantBilinearModule).IsNondegenerate :=
    ((rankOne 1).discriminantBilinearModule.isNondegenerate_prod
      (rankOne 39).discriminantBilinearModule).mpr
      ⟨(rankOne 1).isNondegenerate_discriminantBilinearModule,
        (rankOne 39).isNondegenerate_discriminantBilinearModule⟩
  have hcard : Nat.card ((rankOne 1).discriminantBilinearModule.prod
        (rankOne 39).discriminantBilinearModule) =
      Nat.card ((rankOne 3).discriminantBilinearModule.prod
        (rankOne 13).discriminantBilinearModule) := by
    simp only [Nat.card_prod, natCard_discriminantBilinearModule, natCard_rankOne_discriminantGroup]
    norm_num
  let mid := g.toIsometry ((Nat.bijective_iff_injective_and_card g).mpr ⟨g.injective hnd, hcard⟩)
  exact ((rankOne 1).discriminantBilinearIsometryOrthogonalSum (rankOne 39)).trans
    (mid.trans ((rankOne 3).discriminantBilinearIsometryOrthogonalSum (rankOne 13)).symm)

/-- **`⟨1⟩ ⊕ ⟨39⟩` and `⟨3⟩ ⊕ ⟨13⟩` lie in the same genus.** Both are positive definite odd
binary lattices of odd discriminant `39` with isometric discriminant bilinear modules, so
`sameGenus_iff_of_odd_discriminant` applies directly. -/
theorem sameGenus_rankOne_one_thirtyNine_three_thirteen :
    ((rankOne 1).orthogonalSum (rankOne 39)).SameGenus
      ((rankOne 3).orthogonalSum (rankOne 13)) := by
  have hodd : Odd ((rankOne 1).orthogonalSum (rankOne 39)).discriminant := by
    rw [discriminant_orthogonalSum, rankOne_discriminant, rankOne_discriminant]
    decide
  refine (((rankOne 1).orthogonalSum (rankOne 39)).sameGenus_iff_of_odd_discriminant
    ((rankOne 3).orthogonalSum (rankOne 13)) hodd).mpr ⟨?_, ?_,
      ⟨discriminantIsometry_one_thirtyNine_three_thirteen⟩⟩
  · rw [signature_orthogonalSum, signature_orthogonalSum]
    have h1 := rankOne_signature_of_pos (a := 1) (by norm_num)
    have h39 := rankOne_signature_of_pos (a := 39) (by norm_num)
    have h3 := rankOne_signature_of_pos (a := 3) (by norm_num)
    have h13 := rankOne_signature_of_pos (a := 13) (by norm_num)
    simp only [signature, Prod.mk.injEq] at h1 h39 h3 h13 ⊢
    omega
  · rw [isEven_orthogonalSum_iff, isEven_orthogonalSum_iff, isEven_rankOne_iff,
      isEven_rankOne_iff, isEven_rankOne_iff, isEven_rankOne_iff]
    decide

/-- **`⟨1⟩ ⊕ ⟨39⟩` and `⟨3⟩ ⊕ ⟨13⟩` are not isometric**, even though they lie in the same genus:
`(1, 0)` has norm `1` in `⟨1⟩ ⊕ ⟨39⟩`, whereas every vector in `⟨3⟩ ⊕ ⟨13⟩` has norm
`3x² + 13y²`. -/
theorem isEmpty_isometry_rankOne_one_thirtyNine_three_thirteen :
    IsEmpty (Isometry ((rankOne 1).orthogonalSum (rankOne 39))
      ((rankOne 3).orthogonalSum (rankOne 13))) := by
  refine ⟨fun e ↦ ?_⟩
  let u₁ : rankOne 1 := ⟨1, (mem_rankOne_carrier_iff 1 1).mpr ⟨1, by norm_num⟩⟩
  let v := orthogonalSumInl (rankOne 1) (rankOne 39) u₁
  have hv_norm : ((rankOne 1).orthogonalSum (rankOne 39)).integralNorm v = 1 := by
    rw [integralNorm_orthogonalSum, orthogonalSumFst_inl, orthogonalSumSnd_inl,
      integralNorm_zero, add_zero, integralNorm_rankOne_eq u₁ (k := 1) rfl]
    norm_num
  have himg_norm : ((rankOne 3).orthogonalSum (rankOne 13)).integralNorm (e.carrierEquiv v) = 1 :=
    by rw [integralNorm_apply, e.carrierEquiv_map_integralForm, ← integralNorm_apply, hv_norm]
  rw [integralNorm_orthogonalSum] at himg_norm
  obtain ⟨x, hx⟩ := (mem_rankOne_carrier_iff 3 _).mp
    (orthogonalSumFst (rankOne 3) (rankOne 13) (e.carrierEquiv v)).2
  obtain ⟨y, hy⟩ := (mem_rankOne_carrier_iff 13 _).mp
    (orthogonalSumSnd (rankOne 3) (rankOne 13) (e.carrierEquiv v)).2
  rw [integralNorm_rankOne_eq _ hx.symm, integralNorm_rankOne_eq _ hy.symm] at himg_norm
  rcases eq_or_ne x 0 with rfl | hx0
  · rcases eq_or_ne y 0 with rfl | hy0
    · omega
    · have : 0 < y ^ 2 := sq_pos_iff.mpr hy0
      nlinarith
  · have : 0 < x ^ 2 := sq_pos_iff.mpr hx0
    have : 0 ≤ y ^ 2 := sq_nonneg y
    nlinarith

end TauCeti.IntegralLattice
