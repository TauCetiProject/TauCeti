/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.WeightOne.Basic
public import TauCeti.Geometry.Hodge.Polarization
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# The standard polarized effective Hodge structure of weight one

This file constructs the standard rank-two integral example of an effective weight-one Hodge
structure, together with its Riemann-form polarization. The construction and conventions follow
Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §6, and Peters--Steenbrink, *Mixed Hodge
Structures*, §2.

## Main declarations

* `TauCeti.Hodge.StandardWeightOne.hodgeStructure`: the standard rank-two integral example.
* `TauCeti.Hodge.StandardWeightOne.polarization`: its standard Riemann-form polarization.
-/

public section

namespace TauCeti.Hodge.StandardWeightOne

open scoped ComplexOrder
open scoped TensorProduct

/-! ### The standard rank-two lattice and its complex structure -/

/-- The integral lattice underlying the standard rank-two weight-one example. -/
abbrev Lattice := ℤ × ℤ

/-- The rational vector space underlying the standard rank-two weight-one example. -/
abbrev RationalSpace := ℚ × ℚ

/-- The complex vector space underlying the standard rank-two weight-one example. -/
abbrev ComplexSpace := ℂ × ℂ

/-- The rational scalar action on the complexification of the standard rational space. -/
noncomputable local instance moduleRatOfComplex : Module ℚ ComplexSpace :=
  Module.restrictScalars ℚ ℂ ComplexSpace

/-- Coordinatewise inclusion of the standard lattice into its rationalization. -/
def latticeToRational : Lattice →ₗ[ℤ] RationalSpace :=
  (Algebra.linearMap ℤ ℚ).prodMap (Algebra.linearMap ℤ ℚ)

/-- The coordinatewise rational inclusion is a base change from `ℤ` to `ℚ`. -/
theorem isBaseChange_latticeToRational : IsBaseChange ℚ latticeToRational :=
  IsBaseChange.prodMap _ _ (IsBaseChange.linearMap ℤ ℚ) (IsBaseChange.linearMap ℤ ℚ)

/-- Coordinatewise inclusion of the standard lattice into its complexification. -/
def latticeToComplex : Lattice →ₗ[ℤ] ComplexSpace :=
  (Algebra.linearMap ℤ ℂ).prodMap (Algebra.linearMap ℤ ℂ)

/-- Coordinatewise inclusion of the rationalization into the complexification. -/
noncomputable def rationalToComplex : RationalSpace →ₗ[ℚ] ComplexSpace :=
  Hodge.rationalToComplexMap isBaseChange_latticeToRational latticeToComplex

@[simp]
theorem latticeToRational_apply (x : Lattice) :
    latticeToRational x = ((x.1 : ℚ), (x.2 : ℚ)) := by
  simp [latticeToRational]

@[simp]
theorem latticeToComplex_apply (x : Lattice) :
    latticeToComplex x = ((x.1 : ℂ), (x.2 : ℂ)) := by
  simp [latticeToComplex]

@[simp]
theorem rationalToComplex_apply (x : RationalSpace) :
    rationalToComplex x = ((x.1 : ℂ), (x.2 : ℂ)) := by
  induction x using isBaseChange_latticeToRational.inductionOn with
  | zero =>
      rw [LinearMap.map_zero]
      ext <;> norm_num
  | tmul x =>
      rw [rationalToComplex, Hodge.rationalToComplexMap_apply_ι]
      simp
  | smul q x hx =>
      rw [LinearMap.map_smul rationalToComplex, hx]
      -- Expose the restricted-scalar action on the product so that its coordinates can be
      -- simplified explicitly; the generic product simp lemmas do not unfold this action.
      change (((q : ℂ) • (x.1 : ℂ)), ((q : ℂ) • (x.2 : ℂ))) = _
      ext <;> simp [Algebra.smul_def]
  | add x y hx hy =>
      simp only [map_add, hx, hy]
      ext <;> simp

/-- The two coordinatewise inclusions agree after passing through the rationalization. -/
theorem rationalToComplex_comp_latticeToRational (x : Lattice) :
    rationalToComplex (latticeToRational x) = latticeToComplex x := by
  exact Hodge.rationalToComplexMap_apply_ι isBaseChange_latticeToRational latticeToComplex x

/-- The coordinatewise complex inclusion is a base change from `ℤ` to `ℂ`. -/
theorem isBaseChange_latticeToComplex : IsBaseChange ℂ latticeToComplex :=
  IsBaseChange.prodMap _ _ (IsBaseChange.linearMap ℤ ℂ) (IsBaseChange.linearMap ℤ ℂ)

/-- The coordinatewise inclusion from `ℚ × ℚ` to `ℂ × ℂ` is a base change. -/
theorem isBaseChange_rationalToComplex : IsBaseChange ℂ rationalToComplex :=
  Hodge.isBaseChange_rationalToComplexMap isBaseChange_latticeToRational
    isBaseChange_latticeToComplex

private noncomputable def coordinateConjugation :
    ComplexSpace →ₛₗ[starRingEnd ℂ] ComplexSpace where
  toFun z := (starRingEnd ℂ z.1, starRingEnd ℂ z.2)
  map_add' z w := by ext <;> simp
  map_smul' c z := by ext <;> simp

/-- Lattice conjugation for the coordinate complexification is coordinatewise complex
conjugation. -/
@[simp]
theorem latticeConj_apply (z : ComplexSpace) :
    latticeConj isBaseChange_latticeToComplex z =
      (starRingEnd ℂ z.1, starRingEnd ℂ z.2) := by
  rw [← latticeConj_unique isBaseChange_latticeToComplex coordinateConjugation]
  · rfl
  · intro x
    ext <;> simp [coordinateConjugation]

private abbrev RealSpace := ℝ × ℝ

private noncomputable def realAlmostComplexStructure : AlmostComplexStructure RealSpace :=
  AlmostComplexStructure.product ℝ

private noncomputable def complexificationEquiv :
    ℂ ⊗[ℝ] RealSpace ≃ₗ[ℂ] ComplexSpace :=
  (TensorProduct.prodRight ℝ ℂ ℂ ℝ ℝ).trans
    ((TensorProduct.AlgebraTensorModule.rid ℝ ℂ ℂ).prodCongr
      (TensorProduct.AlgebraTensorModule.rid ℝ ℂ ℂ))

@[simp]
private theorem complexificationEquiv_tmul (z : ℂ) (x : RealSpace) :
    complexificationEquiv (z ⊗ₜ[ℝ] x) = (z * x.1, z * x.2) := by
  simp only [complexificationEquiv, LinearEquiv.trans_apply, TensorProduct.prodRight_tmul,
    LinearEquiv.prodCongr_apply, TensorProduct.AlgebraTensorModule.rid_tmul]
  ext <;> simp [Algebra.smul_def, mul_comm]

private theorem complexificationEquiv_conj (x : ℂ ⊗[ℝ] RealSpace) :
    complexificationEquiv ((Hodge.complexificationConjugation RealSpace).toEquiv x) =
      coordinateConjugation (complexificationEquiv x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, coordinateConjugation.map_add]
  | tmul z x =>
      rw [Hodge.complexificationConjugation_toEquiv_tmul, complexificationEquiv_tmul,
        complexificationEquiv_tmul]
      simp [coordinateConjugation]

private theorem complexificationEquiv_J (x : ℂ ⊗[ℝ] RealSpace) :
    complexificationEquiv (realAlmostComplexStructure.toLinearMap.baseChange ℂ x) =
      (LinearEquiv.skewSwap ℂ ℂ ℂ) (complexificationEquiv x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [complexificationEquiv]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul z x =>
      rw [LinearMap.baseChange_tmul, complexificationEquiv_tmul, complexificationEquiv_tmul]
      simp [realAlmostComplexStructure, AlmostComplexStructure.product]

private theorem complexificationEquiv_conj_symm (x : ComplexSpace) :
    complexificationEquiv.symm ((latticeConjugation isBaseChange_latticeToComplex).toEquiv x) =
      (Hodge.complexificationConjugation RealSpace).toEquiv
        (complexificationEquiv.symm x) := by
  apply complexificationEquiv.injective
  rw [complexificationEquiv.apply_symm_apply, latticeConjugation_toEquiv_apply,
    complexificationEquiv_conj]
  simp only [complexificationEquiv.apply_symm_apply]
  rw [latticeConj_apply]
  rfl

private theorem complexificationEquiv_eigenspace_comap (μ : ℂ) :
    (Module.End.eigenspace (realAlmostComplexStructure.toLinearMap.baseChange ℂ) μ).comap
        complexificationEquiv.symm.toLinearMap =
      Module.End.eigenspace (LinearEquiv.skewSwap ℂ ℂ ℂ).toLinearMap μ := by
  ext x
  rw [Submodule.mem_comap, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff]
  constructor
  · intro hx
    calc
      (LinearEquiv.skewSwap ℂ ℂ ℂ) x =
          complexificationEquiv
            (realAlmostComplexStructure.toLinearMap.baseChange ℂ
              (complexificationEquiv.symm x)) := by
            rw [complexificationEquiv_J, complexificationEquiv.apply_symm_apply]
      _ = complexificationEquiv (μ • complexificationEquiv.symm x) := congrArg _ hx
      _ = μ • x := by rw [map_smul, complexificationEquiv.apply_symm_apply]
  · intro hx
    apply complexificationEquiv.injective
    calc
      complexificationEquiv
          (realAlmostComplexStructure.toLinearMap.baseChange ℂ
            (complexificationEquiv.symm x)) = (LinearEquiv.skewSwap ℂ ℂ ℂ) x := by
              rw [complexificationEquiv_J, complexificationEquiv.apply_symm_apply]
      _ = μ • x := hx
      _ = complexificationEquiv (μ • complexificationEquiv.symm x) := by
        rw [map_smul, complexificationEquiv.apply_symm_apply]

private theorem comap_weilOperator (hs : HodgeStructureOn (ℂ ⊗[ℝ] RealSpace)
    (Hodge.complexificationConjugation RealSpace) 1) :
    (hs.comap complexificationEquiv.symm complexificationEquiv_conj_symm).weilOperator =
      complexificationEquiv.toLinearMap ∘ₗ hs.weilOperator ∘ₗ
        complexificationEquiv.symm.toLinearMap := by
  symm
  apply (hs.comap complexificationEquiv.symm complexificationEquiv_conj_symm).weilOperator_unique
  intro p x hx
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  have hx' : complexificationEquiv.symm x ∈ hs.piece p := by
    rw [HodgeStructureOn.comap_piece] at hx
    exact hx
  calc
    complexificationEquiv (hs.weilOperator (complexificationEquiv.symm x)) =
        complexificationEquiv
          (Complex.I ^ (2 * p - 1) • complexificationEquiv.symm x) :=
      congrArg complexificationEquiv (hs.weilOperator_apply_of_mem hx')
    _ = _ := by rw [map_smul, complexificationEquiv.apply_symm_apply]

/-- The standard effective Hodge structure of weight one on `ℤ × ℤ`. Its degree-one
filtration is the `i`-eigenspace of `J(x, y) = (-y, x)`. -/
noncomputable def hodgeStructure :
    HodgeStructure isBaseChange_latticeToComplex 1 :=
  HodgeStructureOn.comap complexificationEquiv.symm complexificationEquiv_conj_symm
      (realAlmostComplexStructure.hodgeStructure)

/-- The filtration is top in nonpositive degrees, the `i`-eigenspace in degree one, and bottom
above degree one. -/
@[simp]
theorem hodgeStructure_F (p : ℤ) :
    hodgeStructure.F p = if p ≤ 0 then ⊤ else if p = 1 then
      Module.End.eigenspace (LinearEquiv.skewSwap ℂ ℂ ℂ).toLinearMap Complex.I else ⊥ :=
  by
    rw [hodgeStructure, HodgeStructureOn.comap_F,
      realAlmostComplexStructure.hodgeStructure_F]
    by_cases hp : p ≤ 0
    · simp [hp]
    · by_cases hpone : p = 1
      · simp [hpone, complexificationEquiv_eigenspace_comap]
      · simp [hp, hpone]

/-- The standard weight-one Hodge structure is effective. -/
theorem isEffective_hodgeStructure : hodgeStructure.IsEffective := by
  rw [HodgeStructureOn.isEffective_iff, hodgeStructure_F]
  simp

/-- The `H^{1,0}` piece is the `i`-eigenspace of the standard complex structure. -/
@[simp]
theorem hodgeStructure_piece_one :
    hodgeStructure.piece 1 =
      Module.End.eigenspace (LinearEquiv.skewSwap ℂ ℂ ℂ).toLinearMap Complex.I := by
  rw [hodgeStructure, HodgeStructureOn.comap_piece,
    realAlmostComplexStructure.hodgeStructure_piece_one,
    complexificationEquiv_eigenspace_comap]

/-- The `H^{0,1}` piece is the `-i`-eigenspace of the standard complex structure. -/
@[simp]
theorem hodgeStructure_piece_zero :
    hodgeStructure.piece 0 =
      Module.End.eigenspace (LinearEquiv.skewSwap ℂ ℂ ℂ).toLinearMap (-Complex.I) := by
  rw [hodgeStructure, HodgeStructureOn.comap_piece,
    realAlmostComplexStructure.hodgeStructure_piece_zero,
    complexificationEquiv_eigenspace_comap]

/-- Every Hodge piece except `H^{1,0}` and `H^{0,1}` vanishes. -/
theorem hodgeStructure_piece_eq_bot {p : ℤ} (hpzero : p ≠ 0) (hpone : p ≠ 1) :
    hodgeStructure.piece p = ⊥ := by
  by_cases hp : p < 0
  · exact isEffective_hodgeStructure.piece_eq_bot_of_neg hp
  · exact isEffective_hodgeStructure.piece_eq_bot_of_weight_lt (by omega)

/-- The Weil operator of the standard weight-one Hodge structure is its standard complex structure.
-/
@[simp]
theorem hodgeStructure_weilOperator :
    hodgeStructure.weilOperator = (LinearEquiv.skewSwap ℂ ℂ ℂ).toLinearMap := by
  rw [hodgeStructure, comap_weilOperator,
    realAlmostComplexStructure.hodgeStructure_weilOperator]
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := complexificationEquiv.surjective x
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  calc
    complexificationEquiv
        (realAlmostComplexStructure.toLinearMap.baseChange ℂ
          (complexificationEquiv.symm (complexificationEquiv y))) =
        complexificationEquiv
          (realAlmostComplexStructure.toLinearMap.baseChange ℂ y) := by
      rw [complexificationEquiv.symm_apply_apply]
    _ = (LinearEquiv.skewSwap ℂ ℂ ℂ) (complexificationEquiv y) :=
      complexificationEquiv_J y

/-! ### The standard Riemann form -/

/-- The standard alternating Riemann form
`Q((x, y), (u, v)) = y * u - x * v` on `ℤ × ℤ`. -/
def riemannForm : LinearMap.BilinForm ℤ Lattice :=
  LinearMap.mk₂ ℤ (fun x y : Lattice ↦ x.2 * y.1 - x.1 * y.2)
    (by rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩; simp; ring)
    (by rintro c ⟨a, b⟩ ⟨d, e⟩; simp; ring)
    (by rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩; simp; ring)
    (by rintro c ⟨a, b⟩ ⟨d, e⟩; simp; ring)

@[simp]
theorem riemannForm_apply (x y : Lattice) :
    riemannForm x y = x.2 * y.1 - x.1 * y.2 := by
  simp [riemannForm]

/-- The standard Riemann form has no left or right radical. -/
theorem riemannForm_nondegenerate : riemannForm.Nondegenerate := by
  constructor
  · intro x hx
    have hfst := hx (0, 1)
    have hsnd := hx (1, 0)
    apply Prod.ext
    · simpa using neg_eq_zero.mp (by simpa using hfst)
    · simpa using hsnd
  · intro y hy
    have hfst := hy (0, 1)
    have hsnd := hy (1, 0)
    apply Prod.ext
    · simpa using hfst
    · simpa using neg_eq_zero.mp (by simpa using hsnd)

private def complexRiemannForm : LinearMap.BilinForm ℂ ComplexSpace :=
  LinearMap.mk₂ ℂ (fun x y : ComplexSpace ↦ x.2 * y.1 - x.1 * y.2)
    (by rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩; simp; ring)
    (by rintro c ⟨a, b⟩ ⟨d, e⟩; simp; ring)
    (by rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩; simp; ring)
    (by rintro c ⟨a, b⟩ ⟨d, e⟩; simp; ring)

private theorem integralFormBaseChange_riemannForm :
    integralFormBaseChange isBaseChange_latticeToComplex riemannForm = complexRiemannForm := by
  symm
  apply integralFormBaseChange_unique
  intro x y
  simp [complexRiemannForm]

/-- The complexification of the standard Riemann form has the same coordinate formula. -/
@[simp]
theorem integralFormBaseChange_riemannForm_apply (x y : ComplexSpace) :
    integralFormBaseChange isBaseChange_latticeToComplex riemannForm x y =
      x.2 * y.1 - x.1 * y.2 := by
  rw [integralFormBaseChange_riemannForm]
  simp [complexRiemannForm]

private theorem snd_eq_neg_I_mul_fst_of_mem_I {x : ComplexSpace}
    (hx : x ∈ Module.End.eigenspace
        (LinearEquiv.skewSwap ℂ ℂ ℂ).toLinearMap Complex.I) :
    x.2 = -Complex.I * x.1 := by
  rw [Module.End.mem_eigenspace_iff] at hx
  have h := congrArg Prod.fst hx
  calc
    x.2 = -(-x.2) := by simp
    _ = -(Complex.I * x.1) := congrArg Neg.neg (by
      simpa only [LinearEquiv.coe_toLinearMap, LinearEquiv.skewSwap_apply,
        Prod.fst, Prod.smul_fst, smul_eq_mul] using h)
    _ = -Complex.I * x.1 := by ring

private theorem snd_eq_I_mul_fst_of_mem_neg_I {x : ComplexSpace}
    (hx : x ∈ Module.End.eigenspace
        (LinearEquiv.skewSwap ℂ ℂ ℂ).toLinearMap (-Complex.I)) :
    x.2 = Complex.I * x.1 := by
  rw [Module.End.mem_eigenspace_iff] at hx
  have h := congrArg Prod.fst hx
  calc
    x.2 = -(-x.2) := by simp
    _ = -((-Complex.I) * x.1) := congrArg Neg.neg (by
      simpa only [LinearEquiv.coe_toLinearMap, LinearEquiv.skewSwap_apply,
        Prod.fst, Prod.smul_fst, smul_eq_mul] using h)
    _ = Complex.I * x.1 := by ring

private theorem positive_coordinate_I (z : ℂ) (hz : z ≠ 0) :
    0 < Complex.I *
      ((-Complex.I * z) * starRingEnd ℂ z -
        z * starRingEnd ℂ (-Complex.I * z)) := by
  have hcalc : Complex.I *
      ((-Complex.I * z) * starRingEnd ℂ z -
        z * starRingEnd ℂ (-Complex.I * z)) = (2 * Complex.normSq z : ℝ) := by
    rw [map_mul, map_neg]
    norm_num
    rw [Complex.normSq_eq_conj_mul_self]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hcalc]
  exact Complex.zero_lt_real.mpr (mul_pos (by norm_num) (Complex.normSq_pos.mpr hz))

private theorem positive_coordinate_neg_I (z : ℂ) (hz : z ≠ 0) :
    0 < (-Complex.I) *
      ((Complex.I * z) * starRingEnd ℂ z -
        z * starRingEnd ℂ (Complex.I * z)) := by
  have heq : (-Complex.I) *
      ((Complex.I * z) * starRingEnd ℂ z -
        z * starRingEnd ℂ (Complex.I * z)) = Complex.I *
      ((-Complex.I * z) * starRingEnd ℂ z -
        z * starRingEnd ℂ (-Complex.I * z)) := by
    rw [map_mul]
    norm_num
    ring
  rw [heq]
  exact positive_coordinate_I z hz

/-- The standard alternating form satisfies the Hodge–Riemann relations for the standard
weight-one Hodge structure. -/
theorem isPolarization_riemannForm :
    IsPolarization isBaseChange_latticeToComplex hodgeStructure riemannForm where
  symm_weight x y := by
    norm_num [riemannForm_apply]
    ring
  nondegenerate := riemannForm_nondegenerate
  orthogonal p x hx y hy := by
    by_cases hp : p ≤ 0
    · have hother : ¬1 + 1 - p ≤ 0 := by omega
      have hotherone : 1 + 1 - p ≠ 1 := by omega
      have hyzero : y = 0 := by
        have : y ∈ (⊥ : Submodule ℂ ComplexSpace) := by
          rw [hodgeStructure_F, ite_eq_right hother, ite_eq_right hotherone] at hy
          exact hy
        exact this
      subst y
      simp
    · by_cases hpone : p = 1
      · subst p
        have hxI : x ∈ Module.End.eigenspace
            (LinearEquiv.skewSwap ℂ ℂ ℂ).toLinearMap Complex.I := by
          simpa [hodgeStructure_F] using hx
        have hyI : y ∈ Module.End.eigenspace
            (LinearEquiv.skewSwap ℂ ℂ ℂ).toLinearMap Complex.I := by
          simpa [hodgeStructure_F] using hy
        rw [integralFormBaseChange_riemannForm_apply,
          snd_eq_neg_I_mul_fst_of_mem_I hxI, snd_eq_neg_I_mul_fst_of_mem_I hyI]
        ring
      · have hxzero : x = 0 := by
          have : x ∈ (⊥ : Submodule ℂ ComplexSpace) := by
            rw [hodgeStructure_F, ite_eq_right hp, ite_eq_right hpone] at hx
            exact hx
          exact this
        subst x
        simp
  positive p x hx hx0 := by
    by_cases hpone : p = 1
    · subst p
      rw [hodgeStructure_piece_one] at hx
      have hrel := snd_eq_neg_I_mul_fst_of_mem_I hx
      have hfst : x.1 ≠ 0 := by
        intro hzero
        apply hx0
        apply Prod.ext <;> simp [hzero, hrel]
      rw [integralFormBaseChange_riemannForm_apply, latticeConj_apply, hrel]
      norm_num
      simpa using positive_coordinate_I x.1 hfst
    by_cases hpzero : p = 0
    · subst p
      rw [hodgeStructure_piece_zero] at hx
      have hrel := snd_eq_I_mul_fst_of_mem_neg_I hx
      have hfst : x.1 ≠ 0 := by
        intro hzero
        apply hx0
        apply Prod.ext <;> simp [hzero, hrel]
      rw [integralFormBaseChange_riemannForm_apply, latticeConj_apply, hrel]
      norm_num
      simpa using positive_coordinate_neg_I x.1 hfst
    · rw [hodgeStructure_piece_eq_bot hpzero hpone, Submodule.mem_bot] at hx
      exact (hx0 hx).elim

/-- The standard Riemann form bundled as a polarization of the standard weight-one Hodge
structure. -/
noncomputable def polarization :
    Polarization isBaseChange_latticeToComplex hodgeStructure where
  Qint := riemannForm
  isPolarization := isPolarization_riemannForm

@[simp]
theorem polarization_Qint : polarization.Qint = riemannForm := (rfl)

@[simp]
theorem polarization_Q (x y : ComplexSpace) :
    polarization.Q x y = x.2 * y.1 - x.1 * y.2 := by
  rw [Polarization.Q_def, polarization_Qint, integralFormBaseChange_riemannForm_apply]

end TauCeti.Hodge.StandardWeightOne
