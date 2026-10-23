/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.OreExtension.Triangular
public import TauCeti.Algebra.Polynomial.Laurent.Basic
public import TauCeti.QuantumGroups.UqSl2.Basic

import Mathlib.Data.Matrix.Mul
import TauCeti.Algebra.OreExtension.Degree
import Mathlib.Tactic

/-!
# The iterated Ore presentation of U_q(sl₂)

For a nonzero parameter `q`, the quantized enveloping algebra `UqSl2 q` is an iterated Ore
extension of the Laurent polynomial ring `ℂ[K, K⁻¹]`:

* first adjoin `F` with the twist `σ_F (K) = q² K` and zero derivation, giving the lower Borel
  part `ℂ[K, K⁻¹][F; σ_F]`, in which `F K = q² K F`;
* then adjoin `E` with the twist `σ_E (K) = q⁻² K`, `σ_E (F) = F` and the `σ_E`-derivation
  `δ_E (K) = 0`, `δ_E (F) = (K - K⁻¹) / (q - q⁻¹)`, so that `E K = q⁻² K E` and
  `E F = F E + (K - K⁻¹) / (q - q⁻¹)`.

The twist `σ_E` extends from `ℂ[K, K⁻¹]` by the universal property of the first Ore extension.
The derivation `δ_E` is the upper-right corner of the algebra map
`r ↦ !![σ_E r, δ_E r; 0, r]` into `2 × 2` matrices, which is likewise produced by that universal
property from its values on `K` and `F`.

The two universal properties, of the presentation and of the Ore extensions, give mutually
inverse algebra maps, so `UqSl2 q` is isomorphic to the tower. Since an Ore extension is free on
its left monomials, this identification is the source of the PBW basis `K^b F^a E^c` of
`UqSl2 q`. Both twists are injective, so the tower, and hence `UqSl2 q`, is a domain; in
particular the presentation is nontrivial.

## Main definitions

* `TauCeti.UqSl2.sigmaF`: the automorphism `K ↦ q² K` of `ℂ[K, K⁻¹]`.
* `TauCeti.UqSl2.LowerBorel`: the first Ore extension `ℂ[K, K⁻¹][F; σ_F]`.
* `TauCeti.UqSl2.sigmaE` and `TauCeti.UqSl2.deltaE`: the twist and skew derivation of the
  second extension.
* `TauCeti.UqSl2.OreTower`: the second Ore extension `ℂ[K, K⁻¹][F; σ_F][E; σ_E, δ_E]`.
* `TauCeti.UqSl2.oreTowerEquiv`: the algebra isomorphism `UqSl2 q ≃ₐ[ℂ] OreTower q`.

## Main results

* `TauCeti.UqSl2.instIsDomain`: `UqSl2 q` is a domain for every nonzero `q`.

## References

* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Section VI.1, for the
  iterated Ore extension and the resulting PBW basis of `U_q(sl₂)`.
* A. Virelizier, *Quantum groups*, Section 2.3, for the presentation conventions.
-/

public noncomputable section

open LaurentPolynomial

namespace TauCeti.UqSl2

variable (q : ℂ) [Fact (q ≠ 0)]

/-! ### The first extension: adjoining `F` -/

/-- The automorphism `K ↦ q² K` of the Laurent polynomial ring `ℂ[K, K⁻¹]`, the twist of the
first Ore extension of the tower presenting `UqSl2 q`. -/
def sigmaF : ℂ[T;T⁻¹] →ₐ[ℂ] ℂ[T;T⁻¹] :=
  rescale ℂ (Units.mk0 q Fact.out ^ 2)

/-- `sigmaF` is the rescaling `K ↦ q² K`. -/
theorem sigmaF_apply (a : ℂ[T;T⁻¹]) : sigmaF q a = rescale ℂ (Units.mk0 q Fact.out ^ 2) a :=
  (rfl)

/-- `sigmaF` sends `Kⁿ` to `q²ⁿ Kⁿ`. -/
@[simp]
theorem sigmaF_T (n : ℤ) : sigmaF q (T n) = C (q ^ (2 * n)) * T n := by
  rw [sigmaF_apply, rescale_T, zpow_mul]
  simp

/-- `sigmaF` fixes the constants. -/
@[simp]
theorem sigmaF_C (a : ℂ) : sigmaF q (C a) = C a :=
  rescale_C _ a

/-- The lower Borel part `ℂ[K, K⁻¹][F; σ_F]` of `UqSl2 q`, the Ore extension of the Laurent
polynomials in `K` by a variable `F` with `F K = q² K F`. -/
abbrev LowerBorel : Type := OreExtension (sigmaF q) 0

/-- The automorphism `K ↦ q⁻² K` of `ℂ[K, K⁻¹]`, inverse to `sigmaF`. -/
private def tauE : ℂ[T;T⁻¹] →ₐ[ℂ] ℂ[T;T⁻¹] :=
  rescale ℂ (Units.mk0 q Fact.out ^ 2)⁻¹

private theorem tauE_sigmaF (a : ℂ[T;T⁻¹]) : tauE q (sigmaF q a) = a := by
  simp [tauE, sigmaF]

private theorem sigmaF_tauE (a : ℂ[T;T⁻¹]) : sigmaF q (tauE q a) = a := by
  simp [tauE, sigmaF]

/-! ### The second extension: adjoining `E` -/

/-- The twist of the second Ore extension: the algebra endomorphism of `LowerBorel q` with
`K ↦ q⁻² K` and `F ↦ F`. -/
def sigmaE : LowerBorel q →ₐ[ℂ] LowerBorel q :=
  OreExtension.liftAlgHom (OreExtension.CAlgHom.comp (tauE q)) OreExtension.X fun a => by
    simp [OreExtension.X_mul_C, sigmaF_tauE, tauE_sigmaF]

/-- `sigmaE` rescales `ℂ[K, K⁻¹]` by `K ↦ q⁻² K`. -/
@[simp]
theorem sigmaE_C (a : ℂ[T;T⁻¹]) :
    sigmaE q (OreExtension.C a) =
      OreExtension.C (rescale ℂ (Units.mk0 q Fact.out ^ 2)⁻¹ a) := by
  simp [sigmaE, tauE]

/-- `sigmaE` fixes `F`. -/
@[simp]
theorem sigmaE_X : sigmaE q OreExtension.X = OreExtension.X := by
  simp [sigmaE]

/-- The value `(K - K⁻¹) / (q - q⁻¹)` of `deltaE` at `F`. -/
private def cartanQuotient : ℂ[T;T⁻¹] := (q - q⁻¹)⁻¹ • (T 1 - T (-1))

/-- The diagonal algebra map `r ↦ !![σ_E r, 0; 0, r]`. -/
private def diagonalMap : LowerBorel q →ₐ[ℂ] Matrix (Fin 2) (Fin 2) (LowerBorel q) :=
  (Matrix.diagonalAlgHom ℂ).comp (AlgHom.pi ![sigmaE q, AlgHom.id ℂ _])

private theorem diagonalMap_apply (r : LowerBorel q) :
    diagonalMap q r = Matrix.diagonal ![sigmaE q r, r] := by
  -- `Matrix.diagonalAlgHom` is `Matrix.diagonal` by definition, and has no `apply` lemma.
  ext i j
  fin_cases i <;> rfl

/-- The matrix `!![F, (K - K⁻¹)/(q - q⁻¹); 0, F]`, the value at `F` of the triangular
representation defining `deltaE`. -/
private def xMatrix : Matrix (Fin 2) (Fin 2) (LowerBorel q) :=
  !![OreExtension.X, OreExtension.C (cartanQuotient q); 0, OreExtension.X]

/-- The triangular representation `r ↦ !![σ_E r, δ_E r; 0, r]` of `LowerBorel q`. -/
private def triangularMap : LowerBorel q →ₐ[ℂ] Matrix (Fin 2) (Fin 2) (LowerBorel q) :=
  OreExtension.liftAlgHom ((diagonalMap q).comp OreExtension.CAlgHom) (xMatrix q) fun a => by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [xMatrix, diagonalMap_apply, Matrix.mul_apply, Fin.sum_univ_two, sigmaE_C,
        OreExtension.X_mul_C, ← OreExtension.C_mul, mul_comm (cartanQuotient q), ← tauE.eq_def,
        tauE_sigmaF, sigmaF_tauE]

private theorem triangularMap_shape (r : LowerBorel q) :
    triangularMap q r 0 0 = sigmaE q r ∧ triangularMap q r 1 0 = 0 ∧
      triangularMap q r 1 1 = r := by
  induction r using OreExtension.induction_on_mul with
  | C a => simp [triangularMap, diagonalMap_apply]
  | X => simp [triangularMap, xMatrix]
  | add r s hr hs => simp [hr.1, hr.2.1, hr.2.2, hs.1, hs.2.1, hs.2.2]
  | mul r s hr hs =>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hr.1, hr.2.1, hr.2.2, hs.1, hs.2.1, hs.2.2]

/-- The skew derivation of the second Ore extension: the `sigmaE`-derivation of
`LowerBorel q` vanishing on `ℂ[K, K⁻¹]` with `F ↦ (K - K⁻¹) / (q - q⁻¹)`. -/
def deltaE : SigmaDerivation (sigmaE q) :=
  SigmaDerivation.ofMatrix (triangularMap q) (fun r => (triangularMap_shape q r).1)
    (fun r => (triangularMap_shape q r).2.2)

/-- `deltaE` vanishes on `ℂ[K, K⁻¹]`. -/
@[simp]
theorem deltaE_C (a : ℂ[T;T⁻¹]) : deltaE q (OreExtension.C a) = 0 := by
  simp [deltaE, triangularMap, diagonalMap_apply]

/-- `deltaE` sends `F` to `(K - K⁻¹) / (q - q⁻¹)`. -/
@[simp]
theorem deltaE_X :
    deltaE q OreExtension.X = OreExtension.C ((q - q⁻¹)⁻¹ • (T 1 - T (-1))) := by
  simp [deltaE, triangularMap, xMatrix, cartanQuotient]

/-- The iterated Ore extension `ℂ[K, K⁻¹][F; σ_F][E; σ_E, δ_E]` presenting `UqSl2 q`. -/
abbrev OreTower : Type := OreExtension (sigmaE q) (deltaE q)

/-! ### Comparison with the presentation -/

/-- The generators `E`, `F`, `K`, `K⁻¹` of the Ore tower satisfy the defining relations of
`UqSl2 q`. -/
private def towerTuple : GeneratorTuple q (OreTower q) where
  e := OreExtension.X
  f := OreExtension.C OreExtension.X
  k := OreExtension.C (OreExtension.C (T 1))
  kInv := OreExtension.C (OreExtension.C (T (-1)))
  k_mul_kInv := by
    rw [← OreExtension.C_mul, ← OreExtension.C_mul, ← T_add]
    simp
  kInv_mul_k := by
    rw [← OreExtension.C_mul, ← OreExtension.C_mul, ← T_add]
    simp
  k_mul_e := by
    -- `E K = q⁻² K E` is the commutation relation of the second extension.
    rw [OreExtension.X_mul_C, sigmaE_C, deltaE_C, rescale_T, ← smul_eq_C_mul]
    simp only [map_smul, map_zero, add_zero, zpow_one]
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.val_mk0, smul_mul_assoc,
      smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 Fact.out), one_smul]
  k_mul_f := by
    -- `F K = q² K F` is the commutation relation of the first extension.
    rw [← OreExtension.C_mul, ← OreExtension.C_mul, OreExtension.X_mul_C, sigmaF_apply,
      rescale_T, ← smul_eq_C_mul]
    simp only [SigmaDerivation.coe_zero, Pi.zero_apply, map_zero, add_zero, map_smul,
      smul_mul_assoc, smul_smul, zpow_one, Units.val_pow_eq_pow_val, Units.val_mk0, inv_pow]
    rw [inv_mul_cancel₀ (pow_ne_zero 2 Fact.out), one_smul]
  e_mul_f_sub_f_mul_e := by
    rw [OreExtension.X_mul_C, sigmaE_X, deltaE_X]
    simp only [map_smul, map_sub]
    -- `simp` does not close `a + b - a = b` here: the subtraction of the Ore tower comes from its
    -- `Ring` instance, so the cancellation lemma is applied at that ring explicitly.
    exact add_sub_cancel_left (G := OreTower q) _ _

/-- The algebra map from `UqSl2 q` to its Ore tower. -/
private def toTower : UqSl2 q →ₐ[ℂ] OreTower q := lift (towerTuple q)

/-- `F K = q² K F` in `UqSl2 q`. -/
private theorem f_mul_kUnit :
    f q * (kUnit q : UqSl2 q) = ((Units.mk0 q Fact.out ^ 2 : ℂˣ) : ℂ) • (↑(kUnit q) * f q) := by
  rw [kUnit_val, k_mul_f, smul_smul, Units.val_pow_eq_pow_val, Units.val_mk0, inv_pow,
    mul_inv_cancel₀ (pow_ne_zero 2 Fact.out), one_smul]

/-- `E K = q⁻² K E` in `UqSl2 q`. -/
theorem e_mul_kUnit :
    e q * (kUnit q : UqSl2 q) =
      (((Units.mk0 q Fact.out ^ 2)⁻¹ : ℂˣ) : ℂ) • (↑(kUnit q) * e q) := by
  rw [kUnit_val, k_mul_e, smul_smul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    Units.val_mk0, inv_mul_cancel₀ (pow_ne_zero 2 Fact.out), one_smul]

/-- The algebra map from the lower Borel part to `UqSl2 q`. -/
private def fromLowerBorel : LowerBorel q →ₐ[ℂ] UqSl2 q :=
  OreExtension.liftAlgHom (laurentEval (kUnit q)) (f q) fun a => by
    simpa [sigmaF_apply, SigmaDerivation.coe_zero, Pi.zero_apply] using
      mul_laurentEval (f_mul_kUnit q) a

/-- `E` satisfies the commutation relation of the second extension in `UqSl2 q`. -/
private theorem e_mul_fromLowerBorel (r : LowerBorel q) :
    e q * fromLowerBorel q r =
      fromLowerBorel q (sigmaE q r) * e q + fromLowerBorel q (deltaE q r) := by
  induction r using OreExtension.induction_on_mul with
  | C a =>
    simpa [fromLowerBorel, sigmaE_C] using mul_laurentEval (e_mul_kUnit q) a
  | X =>
    rw [sigmaE_X, deltaE_X]
    simp only [fromLowerBorel, OreExtension.liftAlgHom_X, OreExtension.liftAlgHom_C, map_smul,
      map_sub, laurentEval_T, zpow_one, zpow_neg_one, kUnit_val, kUnit_inv]
    exact eq_add_of_sub_eq' e_mul_f_sub_f_mul_e
  | add r s hr hs => simp only [map_add, mul_add, add_mul, hr, hs]; abel
  | mul r s hr hs =>
    rw [map_mul, map_mul, SigmaDerivation.leibniz, map_add, map_mul, map_mul, map_mul,
      ← mul_assoc, hr, add_mul, mul_assoc, hs, mul_add, ← mul_assoc]
    abel

/-- The algebra map from the Ore tower to `UqSl2 q`. -/
private def fromTower : OreTower q →ₐ[ℂ] UqSl2 q :=
  OreExtension.liftAlgHom (fromLowerBorel q) (e q) (e_mul_fromLowerBorel q)

private theorem fromTower_comp_toTower : (fromTower q).comp (toTower q) = AlgHom.id ℂ _ :=
  hom_ext (by simp [fromTower, toTower, towerTuple])
    (by simp [fromTower, toTower, towerTuple, fromLowerBorel])
    (by simp [fromTower, toTower, towerTuple, fromLowerBorel])
    (by simp [fromTower, toTower, towerTuple, fromLowerBorel])

private theorem toTower_comp_fromLowerBorel :
    (toTower q).comp (fromLowerBorel q) = OreExtension.CAlgHom := by
  refine OreExtension.algHom_ext (fun a => ?_) (by simp [fromLowerBorel, toTower, towerTuple])
  have h : (toTower q).comp (laurentEval (kUnit q)) =
      (OreExtension.CAlgHom.comp OreExtension.CAlgHom : ℂ[T;T⁻¹] →ₐ[ℂ] OreTower q) :=
    (comp_laurentEval _ _).trans (laurentEval_unique _ _ (by simp [toTower, towerTuple])).symm
  have h' := DFunLike.congr_fun h a
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at h'
  simpa only [AlgHom.comp_apply, fromLowerBorel, OreExtension.liftAlgHom_C,
    OreExtension.CAlgHom_eq_C] using h'

private theorem toTower_comp_fromTower : (toTower q).comp (fromTower q) = AlgHom.id ℂ _ :=
  OreExtension.algHom_ext
    (fun a => by simpa [fromTower] using DFunLike.congr_fun (toTower_comp_fromLowerBorel q) a)
    (by simp [fromTower, toTower, towerTuple])

/-- The isomorphism between `UqSl2 q` and its iterated Ore presentation
`ℂ[K, K⁻¹][F; σ_F][E; σ_E, δ_E]`, matching the generators `E`, `F`, `K` and `K⁻¹`. -/
def oreTowerEquiv : UqSl2 q ≃ₐ[ℂ] OreTower q :=
  AlgEquiv.ofAlgHom (toTower q) (fromTower q) (toTower_comp_fromTower q)
    (fromTower_comp_toTower q)

/-- The forward map of `oreTowerEquiv` is the map induced by the generators of the tower. -/
private theorem oreTowerEquiv_apply (x : UqSl2 q) : oreTowerEquiv q x = toTower q x := (rfl)

/-- The inverse of `oreTowerEquiv` is the map induced by the Ore universal properties. -/
private theorem oreTowerEquiv_symm_apply (x : OreTower q) :
    (oreTowerEquiv q).symm x = fromTower q x := (rfl)

/-- `oreTowerEquiv` sends `E` to the variable of the second extension. -/
@[simp]
theorem oreTowerEquiv_e : oreTowerEquiv q (e q) = OreExtension.X := by
  simp [oreTowerEquiv_apply, toTower, towerTuple]

/-- `oreTowerEquiv` sends `F` to the variable of the first extension. -/
@[simp]
theorem oreTowerEquiv_f : oreTowerEquiv q (f q) = OreExtension.C OreExtension.X := by
  simp [oreTowerEquiv_apply, toTower, towerTuple]

/-- `oreTowerEquiv` sends `K` to the Laurent variable. -/
@[simp]
theorem oreTowerEquiv_k :
    oreTowerEquiv q (k q) = OreExtension.C (OreExtension.C (T 1)) := by
  simp [oreTowerEquiv_apply, toTower, towerTuple]

/-- `oreTowerEquiv` sends `K⁻¹` to the inverse Laurent variable. -/
@[simp]
theorem oreTowerEquiv_kInv :
    oreTowerEquiv q (kInv q) = OreExtension.C (OreExtension.C (T (-1))) := by
  simp [oreTowerEquiv_apply, toTower, towerTuple]

/-- The inverse of `oreTowerEquiv` sends the variable of the second extension to `E`. -/
@[simp]
theorem oreTowerEquiv_symm_X : (oreTowerEquiv q).symm OreExtension.X = e q := by
  rw [AlgEquiv.symm_apply_eq, oreTowerEquiv_e]

/-- The inverse of `oreTowerEquiv` sends the variable of the first extension to `F`. -/
@[simp]
theorem oreTowerEquiv_symm_C_X :
    (oreTowerEquiv q).symm (OreExtension.C OreExtension.X) = f q := by
  rw [AlgEquiv.symm_apply_eq, oreTowerEquiv_f]

/-- The Laurent polynomials in `K` correspond to the Laurent evaluations at the unit `K`. -/
@[simp]
theorem oreTowerEquiv_symm_C_C (a : ℂ[T;T⁻¹]) :
    (oreTowerEquiv q).symm (OreExtension.C (OreExtension.C a)) = laurentEval (kUnit q) a := by
  simp [oreTowerEquiv_symm_apply, fromTower, fromLowerBorel]

/-! ### The domain theorem -/

/-- The algebra endomorphism of `LowerBorel q` with `K ↦ q² K` and `F ↦ F`, inverse to
`sigmaE`. -/
private def sigmaEInv : LowerBorel q →ₐ[ℂ] LowerBorel q :=
  OreExtension.liftAlgHom (OreExtension.CAlgHom.comp (sigmaF q)) OreExtension.X fun a => by
    simp [OreExtension.X_mul_C]

private theorem sigmaEInv_sigmaE (r : LowerBorel q) : sigmaEInv q (sigmaE q r) = r := by
  have h : (sigmaEInv q).comp (sigmaE q) = AlgHom.id ℂ _ :=
    OreExtension.algHom_ext (fun a => by simp [sigmaEInv, sigmaE_C, sigmaF_apply])
      (by simp [sigmaEInv])
  exact DFunLike.congr_fun h r

/-- For a nonzero parameter, `UqSl2 q` is a domain: both twists of its Ore tower are injective,
and an Ore extension of a domain by an injective twist is a domain. In particular the
presentation is nontrivial. -/
instance instIsDomain : IsDomain (UqSl2 q) :=
  have : IsDomain (LowerBorel q) :=
    OreExtension.isDomain (Function.LeftInverse.injective (tauE_sigmaF q))
  have : IsDomain (OreTower q) :=
    OreExtension.isDomain (Function.LeftInverse.injective (sigmaEInv_sigmaE q))
  MulEquiv.isDomain (OreTower q) (oreTowerEquiv q).toMulEquiv

end TauCeti.UqSl2
