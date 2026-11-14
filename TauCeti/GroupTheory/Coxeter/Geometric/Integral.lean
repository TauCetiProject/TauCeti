/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import TauCeti.GroupTheory.Coxeter.Geometric.Sign
public import TauCeti.LinearAlgebra.Matrix.FinsuppBilinForm
public import TauCeti.RepresentationTheory.BaseChange
import TauCeti.Data.Finsupp.Order

/-!
# Integral forms of the geometric representation

Let `cs : CoxeterSystem M W` be a Coxeter system with arbitrary index set `I`, and let `B` be the
canonical bilinear form on `I →₀ ℝ`, with `B(αᵢ, αⱼ) = -cos (π / M i j)`. Suppose that the doubled
Gram matrix `2 B(αᵢ, αⱼ)` has its entries in a subring: there is a matrix `A` over a commutative
ring `R` with an injective algebra map `R → ℝ`, such that `A i j` maps to `2 B(αᵢ, αⱼ)` for all
`i` and `j`. The off-diagonal entries are `2 B(αᵢ, αⱼ) = -2 cos (π / M i j)`, which is an integer
exactly when `M i j` is `2`, `3` or `∞`
(`CoxeterMatrix.exists_algebraMap_int_eq_two_mul_geometricForm_iff`); then `R = ℤ` and
`M.integralGramMatrix` give the canonical integral geometric realization. Other entries need larger
rings, such as `ℤ[√2]` for `M i j = 4` or `ℤ[(1 + √5) / 2]` for `M i j = 5`, and the argument is
the same.

On the free `R`-module `L = I →₀ R` the matrix defines reflections
`x ↦ x - (∑ⱼ xⱼ A i j) eᵢ`, Mathlib's `Module.preReflection` of `eᵢ` along the functional
`Finsupp.linearCombination R (A i)`. Coefficientwise application of the
algebra map, `c : L → I →₀ ℝ`, sends `eᵢ` to `αᵢ` and intertwines these reflections with the
real simple reflections, so the real Coxeter relations transfer along the injective map `c`.
This gives a representation of `W` on `L` (`CoxeterSystem.reflectionRepresentation`) with
`c (ρ_R(w) x) = ρ(w) (c x)`, which is faithful because the real one is (Tits' theorem). No
assumption on the determinant of `A` is made: the infinite dihedral matrix `!![2, -2; -2, 2]` is
allowed.

Pushing `A` forward along an arbitrary ring homomorphism `f : R →+* S` induces a reflection
representation `CoxeterSystem.mapReflectionRepresentation` on `I →₀ S` (including reductions modulo
an integer or ideal, which need not remain faithful). Transporting `reflectionRepresentation` along
an `I`-indexed basis `b` of another free `R`-module `L'` produces
`CoxeterSystem.reflectionRepresentationOfBasis`, whose scalar extension `S ⊗[R] L'` is equivariantly
identified with `I →₀ S` (`CoxeterSystem.baseChangeReflectionRepresentationOfBasisEquiv`) and, at
`S = ℝ`, with `cs.geometricRepresentation`
(`CoxeterSystem.baseChangeRealReflectionRepresentationOfBasisEquiv`).

## Main definitions

* `CoxeterMatrix.integralGramMatrix`: the canonical integer matrix with entries `2, 0, -1, -2` at
  `M i j = 1, 2, 3, 0` (and `0` for `M i j ≥ 4`).
* `CoxeterSystem.reflectionRepresentation`: the representation of `W` on `I →₀ R` in which
  `s i` acts by the reflection `x ↦ x - (∑ⱼ xⱼ A i j) eᵢ`.
* `CoxeterSystem.reflectionRoots`: the `W`-orbit of the simple basis vectors in `I →₀ R`.
* `CoxeterSystem.mapReflectionRepresentation`: the induced representation on `I →₀ S` along any
  ring homomorphism `f : R →+* S` (such as `ℤ →+* ZMod n`).
* `CoxeterSystem.reflectionRepresentationOfBasis`: transport of `reflectionRepresentation` along a
  basis `b : Module.Basis I R L'` of a free `R`-module `L'`.
* `CoxeterSystem.baseChangeReflectionRepresentationOfBasisEquiv` and
  `CoxeterSystem.baseChangeRealReflectionRepresentationOfBasisEquiv`: equivariant identifications
  `S ⊗[R] L' ≃ I →₀ S` and `ℝ ⊗[R] L' ≃ I →₀ ℝ` induced by `(b.baseChange ·).repr`.

## Main results

* `CoxeterMatrix.algebraMap_finsuppBilinForm` and `CoxeterMatrix.mapRange_preReflection`:
  the coefficient map carries the form of `A` to twice the canonical form and the reflections of
  `A` to the geometric reflections.
* `CoxeterMatrix.exists_algebraMap_int_eq_two_mul_geometricForm_iff`: an integer matrix represents
  `2 B` on the simple basis if and only if every entry of `M` is at most `3`.
* `CoxeterSystem.mapRange_reflectionRepresentation`: the coefficient map intertwines the
  representation over `R` with the geometric representation.
* `TauCeti.apply_same_eq_two_of_algebraMap_eq_two_mul_geometricForm`: the diagonal entries of `A`
  are `2`, so each `eᵢ` is negated by its reflection
  (`CoxeterSystem.reflectionRepresentation_simple_single_self`).
* `CoxeterSystem.reflectionRepresentation_injective`: the representation over `R` is faithful.
* `CoxeterSystem.finsuppBilinForm_reflectionRepresentation`: it preserves the form of `A`.
* `CoxeterSystem.reflectionRepresentation_single_pos_iff`,
  `CoxeterSystem.reflectionRepresentation_single_neg_iff`, and
  `CoxeterSystem.pos_or_neg_of_mem_reflectionRoots`: the sign criterion and positive/negative root
  dichotomy over any ordered subring of `ℝ`.
* `CoxeterSystem.mrange_reflectionRepresentation`: its image is the monoid generated by the
  reflections of `A`, and
  `CoxeterSystem.range_generalLinearEquiv_comp_asGroupHom_reflectionRepresentation`: its image in
  the linear automorphisms is the subgroup generated by the reflections of `A`.
* `CoxeterSystem.geometricRepresentation_apply_mem_range_mapRange_iff`: the real geometric
  representation preserves the lattice of vectors with coefficients in `R`, when a matrix over `R`
  maps entrywise to the doubled Gram matrix.

## References

* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, CUP (1990), Section 5.3 (the
  reflection formula) and Section 5.4, Corollary (faithfulness).
-/

public section

open Real TensorProduct

namespace CoxeterMatrix

section Subring

variable {I R : Type*} [CommRing R] [Algebra R ℝ] {M : CoxeterMatrix I} {A : Matrix I I R}

/-- **The coefficient map carries the form of `A` to twice the canonical form**, when `A` maps
entrywise to the doubled Gram matrix `2 B(αᵢ, αⱼ)` of the canonical form. -/
theorem algebraMap_finsuppBilinForm
    (hA : ∀ i j, algebraMap R ℝ (A i j) =
      2 * M.geometricForm (Finsupp.single i 1) (Finsupp.single j 1))
    (x y : I →₀ R) :
    algebraMap R ℝ (A.finsuppBilinForm x y) =
      2 * M.geometricForm (x.mapRange (algebraMap R ℝ) (map_zero _))
        (y.mapRange (algebraMap R ℝ) (map_zero _)) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply, h₁, h₂, Finsupp.mapRange_add (map_add _), mul_add]
  | single i a =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂, Finsupp.mapRange_add (map_add _), mul_add]
    | single j b =>
      simp only [Matrix.finsuppBilinForm_single_single, Finsupp.mapRange_single, map_mul, hA,
        geometricForm_single_single]
      ring

/-- **The coefficient map intertwines the reflections of `A` with the geometric reflections**,
when `A` maps entrywise to the doubled Gram matrix `2 B(αᵢ, αⱼ)` of the canonical form. -/
theorem mapRange_preReflection
    (hA : ∀ i j, algebraMap R ℝ (A i j) =
      2 * M.geometricForm (Finsupp.single i 1) (Finsupp.single j 1))
    (i : I) (x : I →₀ R) :
    (Module.preReflection (Finsupp.single i 1) (Finsupp.linearCombination R (A i)) x).mapRange
        (algebraMap R ℝ) (map_zero _) =
      M.geometricReflection i (x.mapRange (algebraMap R ℝ) (map_zero _)) := by
  have h := algebraMap_finsuppBilinForm hA (Finsupp.single i 1) x
  rw [Finsupp.mapRange_single, map_one, Matrix.finsuppBilinForm_single_left, one_smul] at h
  rw [Module.preReflection_apply, geometricReflection_apply, ← h,
    Finsupp.mapRange_sub (map_sub _), Finsupp.smul_single_one, Finsupp.smul_single_one,
    Finsupp.mapRange_single]

/-- **The reflections of `A` satisfy the Coxeter relations**, when `A` maps entrywise to the
doubled Gram matrix of the canonical form along an injective algebra map `R → ℝ`: the
coefficient map is injective and carries them to the geometric reflections, which satisfy them. -/
theorem isLiftable_preReflection (hR : Function.Injective (algebraMap R ℝ))
    (hA : ∀ i j, algebraMap R ℝ (A i j) =
      2 * M.geometricForm (Finsupp.single i 1) (Finsupp.single j 1)) :
    M.IsLiftable fun i ↦ Module.preReflection (Finsupp.single i 1)
      (Finsupp.linearCombination R (A i)) := by
  intro i i'
  let c : (I →₀ R) →ₛₗ[algebraMap R ℝ] I →₀ ℝ :=
    Finsupp.mapRange.linearMap (algebraMap R ℝ).toSemilinearMap
  have hc (x : I →₀ R) : c x = x.mapRange (algebraMap R ℝ) (map_zero _) := by
    simp [c]
  have hcomm : (M.geometricReflection i * M.geometricReflection i').comp c =
      c.comp (Module.preReflection (Finsupp.single i 1) (Finsupp.linearCombination R (A i)) *
        Module.preReflection (Finsupp.single i' 1) (Finsupp.linearCombination R (A i'))) :=
    LinearMap.ext fun x ↦ by
      simp only [LinearMap.comp_apply, mul_apply_eq_comp, hc, mapRange_preReflection hA]
  have hpow := Module.End.commute_pow_left_of_commute hcomm (M i i')
  rw [M.isLiftable_geometricReflection i i', Module.End.one_eq_id, LinearMap.id_comp] at hpow
  refine LinearMap.ext fun x ↦ Finsupp.mapRange_injective _ (map_zero _) hR ?_
  rw [one_apply_eq_self, ← hc, ← hc, ← LinearMap.comp_apply, ← hpow]

end Subring

/-- **Pushing Coxeter-liftable matrix pre-reflections along any ring homomorphism preserves the
Coxeter relations.** -/
theorem isLiftable_preReflection_map {I R S : Type*} [CommRing R] [CommRing S]
    {M : CoxeterMatrix I} {A : Matrix I I R}
    (h : M.IsLiftable fun i ↦
      Module.preReflection (Finsupp.single i 1) (Finsupp.linearCombination R (A i)))
    (f : R →+* S) :
    M.IsLiftable fun i ↦
      Module.preReflection (Finsupp.single i 1) (Finsupp.linearCombination S (A.map f i)) := by
  intro i j
  let c : (I →₀ R) →ₛₗ[f] I →₀ S := Finsupp.mapRange.linearMap f.toSemilinearMap
  have hc (x : I →₀ R) : c x = x.mapRange f f.map_zero := by
    simp [c]
  have hcomm :
      (Module.preReflection (Finsupp.single i 1) (Finsupp.linearCombination S (A.map f i)) *
          Module.preReflection (Finsupp.single j 1)
            (Finsupp.linearCombination S (A.map f j))).comp c =
        c.comp (Module.preReflection (Finsupp.single i 1) (Finsupp.linearCombination R (A i)) *
          Module.preReflection (Finsupp.single j 1) (Finsupp.linearCombination R (A j))) :=
    LinearMap.ext fun x ↦ by
      simp only [LinearMap.comp_apply, mul_apply_eq_comp, hc,
        A.mapRange_preReflection_single_linearCombination f]
  have hpow := Module.End.commute_pow_left_of_commute hcomm (M i j)
  rw [h i j, Module.End.one_eq_id, LinearMap.comp_id] at hpow
  refine Finsupp.lhom_ext' fun k ↦ LinearMap.ext_ring ?_
  have hk := LinearMap.congr_fun hpow (Finsupp.single k 1)
  simpa [hc, Finsupp.mapRange_single] using hk

end CoxeterMatrix

namespace TauCeti

variable {I R : Type*} [CommRing R] [Algebra R ℝ] {M : CoxeterMatrix I} {A : Matrix I I R}

/-- Two matrices over `R` mapping entrywise to `2 * M.geometricForm` along an injective algebra map
`R → ℝ` are equal. -/
theorem eq_of_algebraMap_eq_two_mul_geometricForm {A' : Matrix I I R}
    (hR : Function.Injective (algebraMap R ℝ))
    (hA : ∀ i j, algebraMap R ℝ (A i j) =
      2 * M.geometricForm (Finsupp.single i 1) (Finsupp.single j 1))
    (hA' : ∀ i j, algebraMap R ℝ (A' i j) =
      2 * M.geometricForm (Finsupp.single i 1) (Finsupp.single j 1)) :
    A = A' := by
  ext i j
  exact hR ((hA i j).trans (hA' i j).symm)

/-- A matrix over `R` mapping entrywise to `2 * M.geometricForm` along an injective algebra map
`R → ℝ` is symmetric. -/
theorem isSymm_of_algebraMap_eq_two_mul_geometricForm
    (hR : Function.Injective (algebraMap R ℝ))
    (hA : ∀ i j, algebraMap R ℝ (A i j) =
      2 * M.geometricForm (Finsupp.single i 1) (Finsupp.single j 1)) :
    A.IsSymm := by
  refine Matrix.IsSymm.ext fun i j ↦ hR ?_
  rw [hA j i, hA i j, M.geometricForm_comm]

/-- Cosine formula for a single matrix entry mapping to `2 * M.geometricForm (eᵢ, eⱼ)`. -/
theorem algebraMap_apply_eq_neg_two_mul_cos_of_algebraMap_eq_two_mul_geometricForm {i j : I}
    (hA : algebraMap R ℝ (A i j) =
      2 * M.geometricForm (Finsupp.single i 1) (Finsupp.single j 1)) :
    algebraMap R ℝ (A i j) = -2 * Real.cos (Real.pi / M i j) := by
  rw [hA, M.geometricForm_single_single]
  ring

/-- **The diagonal entries of `A` are `2`**, when `A` maps entrywise to the doubled Gram matrix
`2 B(αᵢ, αⱼ)` of the canonical form along an injective algebra map `R → ℝ`. -/
theorem apply_same_eq_two_of_algebraMap_eq_two_mul_geometricForm
    (hR : Function.Injective (algebraMap R ℝ))
    (hA : ∀ i j, algebraMap R ℝ (A i j) =
      2 * M.geometricForm (Finsupp.single i 1) (Finsupp.single j 1))
    (i : I) : A i i = 2 := by
  refine hR ?_
  rw [hA, CoxeterMatrix.geometricForm_single_self, map_ofNat, mul_one]

/-- The functional `x ↦ ∑ⱼ xⱼ A i j` takes the value `2` on `eᵢ`, when `A` maps entrywise to the
doubled Gram matrix `2 B(αᵢ, αⱼ)` of the canonical form along an injective algebra map `R → ℝ`, so
that the reflection of `A` along it is a reflection in the sense of `Module.reflection`. -/
theorem linearCombination_single_eq_two_of_algebraMap_eq_two_mul_geometricForm
    (hR : Function.Injective (algebraMap R ℝ))
    (hA : ∀ i j, algebraMap R ℝ (A i j) =
      2 * M.geometricForm (Finsupp.single i 1) (Finsupp.single j 1))
    (i : I) : Finsupp.linearCombination R (A i) (Finsupp.single i 1) = 2 := by
  rw [Finsupp.linearCombination_single, one_smul,
    apply_same_eq_two_of_algebraMap_eq_two_mul_geometricForm hR hA]

end TauCeti

namespace CoxeterMatrix

/-! ### Characterization of integrally realizable Coxeter matrices -/

section IntegralGramMatrix

variable {I : Type*} (M : CoxeterMatrix I)

/-- **The canonical integer Gram matrix of a Coxeter matrix** with entries in `{0, 1, 2, 3}`:
`2` at `1` (diagonal), `0` at `2` (commuting generators), `-1` at `3` (braid length three), `-2`
at `0` (infinite order), and `0` when `M i j ≥ 4`. -/
def integralGramMatrix : Matrix I I ℤ :=
  Matrix.of fun i j ↦
    match M i j with
    | 0 => -2
    | 1 => 2
    | 2 => 0
    | 3 => -1
    | _ => 0

/-- Entrywise formula for `CoxeterMatrix.integralGramMatrix`. -/
theorem integralGramMatrix_apply (i j : I) :
    M.integralGramMatrix i j =
      match M i j with
      | 0 => -2
      | 1 => 2
      | 2 => 0
      | 3 => -1
      | _ => 0 :=
  (rfl)

/-- An infinite-order entry `M i j = 0` gives `-2` in `M.integralGramMatrix`. -/
theorem integralGramMatrix_of_eq_zero {i j : I} (h : M i j = 0) :
    M.integralGramMatrix i j = -2 := by
  simp [integralGramMatrix_apply, h]

/-- An entry `M i j = 1` gives `2` in `M.integralGramMatrix`. -/
theorem integralGramMatrix_of_eq_one {i j : I} (h : M i j = 1) :
    M.integralGramMatrix i j = 2 := by
  simp [integralGramMatrix_apply, h]

/-- Commuting generators (`M i j = 2`) give `0` in `M.integralGramMatrix`. -/
theorem integralGramMatrix_of_eq_two {i j : I} (h : M i j = 2) :
    M.integralGramMatrix i j = 0 := by
  simp [integralGramMatrix_apply, h]

/-- Braid-three entries (`M i j = 3`) give `-1` in `M.integralGramMatrix`. -/
theorem integralGramMatrix_of_eq_three {i j : I} (h : M i j = 3) :
    M.integralGramMatrix i j = -1 := by
  simp [integralGramMatrix_apply, h]

/-- Entries `4 ≤ M i j` (for which `-2 cos(π / M i j)` is non-integral) default to `0` in
`M.integralGramMatrix`. -/
theorem integralGramMatrix_of_four_le {i j : I} (h : 4 ≤ M i j) :
    M.integralGramMatrix i j = 0 := by
  rw [integralGramMatrix_apply]
  rcases hM : M i j with _ | _ | _ | _ | n <;> first | omega | simp

/-- Every diagonal entry of `M.integralGramMatrix` is `2`. -/
@[simp]
theorem integralGramMatrix_self (i : I) : M.integralGramMatrix i i = 2 :=
  M.integralGramMatrix_of_eq_one (M.diagonal i)

/-- `M.integralGramMatrix` is symmetric for every Coxeter matrix `M`. -/
@[simp]
theorem isSymm_integralGramMatrix : M.integralGramMatrix.IsSymm :=
  Matrix.IsSymm.ext fun i j ↦ by simp [integralGramMatrix_apply, M.symmetric i j]

/-- At any pair `(i, j)` with `M i j ≤ 3`, `M.integralGramMatrix i j` maps in `ℝ` to
`2 * M.geometricForm (eᵢ, eⱼ)`. -/
theorem algebraMap_integralGramMatrix_eq_two_mul_geometricForm_of_le_three {i j : I}
    (hM : M i j ≤ 3) :
    algebraMap ℤ ℝ (M.integralGramMatrix i j) =
      2 * M.geometricForm (Finsupp.single i 1) (Finsupp.single j 1) := by
  rw [integralGramMatrix_apply, M.geometricForm_single_single, eq_intCast]
  rcases h : M i j with _ | _ | _ | _ | n
  · simp
  · simp
  · simp
  · norm_num [Real.cos_pi_div_three]
  · omega

/-- **Existence of an integer Gram matrix for `2 * M.geometricForm`.** In the standard unit-root
normalization, an integer matrix `A` with `algebraMap ℤ ℝ (A i j) = 2 * B(αᵢ, αⱼ)` exists if and
only if every entry of `M` lies in `{0, 1, 2, 3}` (`M i j ≤ 3`): for `m ≥ 4` the value
`-2 cos(π / m)` lies strictly between `-2` and `-1`. -/
theorem exists_algebraMap_int_eq_two_mul_geometricForm_iff :
    (∃ A : Matrix I I ℤ,
      ∀ i j, algebraMap ℤ ℝ (A i j) =
        2 * M.geometricForm (Finsupp.single i 1) (Finsupp.single j 1)) ↔
      ∀ i j, M i j ≤ 3 := by
  refine ⟨fun ⟨A, hA⟩ i j ↦ ?_, fun hM ↦ ⟨M.integralGramMatrix,
    fun i j ↦ M.algebraMap_integralGramMatrix_eq_two_mul_geometricForm_of_le_three (hM i j)⟩⟩
  by_contra hlt
  push Not at hlt
  have hm_pos : (0 : ℝ) < M i j := Nat.cast_pos.mpr (by omega)
  have hpi_div_pos : 0 < Real.pi / M i j := div_pos Real.pi_pos hm_pos
  have hpi_div_lt : Real.pi / M i j < Real.pi / 3 :=
    div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by exact_mod_cast hlt)
  have hmem₁ : (0 : ℝ) ∈ Set.Icc 0 Real.pi := ⟨le_rfl, Real.pi_pos.le⟩
  have hmem₂ : Real.pi / M i j ∈ Set.Icc 0 Real.pi :=
    ⟨hpi_div_pos.le, hpi_div_lt.le.trans (div_le_self Real.pi_pos.le (by norm_num))⟩
  have hmem₃ : Real.pi / 3 ∈ Set.Icc 0 Real.pi :=
    ⟨by positivity, div_le_self Real.pi_pos.le (by norm_num)⟩
  have hcos_lt_one : Real.cos (Real.pi / M i j) < 1 := by
    simpa using Real.strictAntiOn_cos hmem₁ hmem₂ hpi_div_pos
  have hhalf_lt_cos : (1 / 2 : ℝ) < Real.cos (Real.pi / M i j) := by
    simpa [Real.cos_pi_div_three] using Real.strictAntiOn_cos hmem₂ hmem₃ hpi_div_lt
  have hentry :=
    TauCeti.algebraMap_apply_eq_neg_two_mul_cos_of_algebraMap_eq_two_mul_geometricForm (hA i j)
  rw [eq_intCast] at hentry
  have hgt : ((-2 : ℤ) : ℝ) < (A i j : ℝ) := by
    push_cast
    linarith
  have hlt' : (A i j : ℝ) < ((-1 : ℤ) : ℝ) := by
    push_cast
    linarith
  have hgtℤ : -2 < A i j := Int.cast_lt.mp hgt
  have hltℤ : A i j < -1 := Int.cast_lt.mp hlt'
  omega

end IntegralGramMatrix

end CoxeterMatrix

namespace CoxeterSystem

variable {I W R : Type*} [Group W] [CommRing R] [Algebra R ℝ] {M : CoxeterMatrix I}
  (cs : CoxeterSystem M W) {A : Matrix I I R} (hR : Function.Injective (algebraMap R ℝ))
  (hA : ∀ i j, algebraMap R ℝ (A i j) =
    2 * M.geometricForm (Finsupp.single i 1) (Finsupp.single j 1))

/-! ### The reflection representation over a subring of `ℝ` -/

/-- **The geometric representation over a subring**: given a matrix `A` over `R`, with
`R → ℝ` injective, whose entries map to the doubled Gram matrix `2 B(αᵢ, αⱼ)` of the canonical
form, the representation of `W` on the free module `I →₀ R` in which `s i` acts by the reflection
`x ↦ x - (∑ⱼ xⱼ A i j) eᵢ`. For `R = ℤ` this is the integral geometric realization; the
coefficient map identifies it with the geometric representation
(`CoxeterSystem.mapRange_reflectionRepresentation`). -/
noncomputable def reflectionRepresentation : Representation R W (I →₀ R) :=
  cs.lift ⟨_, CoxeterMatrix.isLiftable_preReflection hR hA⟩

/-- Each simple reflection acts by the corresponding reflection of the matrix. -/
theorem reflectionRepresentation_simple (i : I) :
    cs.reflectionRepresentation hR hA (cs.simple i) =
      Module.preReflection (Finsupp.single i 1) (Finsupp.linearCombination R (A i)) :=
  cs.lift_apply_simple (CoxeterMatrix.isLiftable_preReflection hR hA) i

/-- **The reflection formula**: the simple reflection `s i` sends `x` to
`x - (∑ⱼ xⱼ A i j) eᵢ`. -/
@[simp]
theorem reflectionRepresentation_simple_apply (i : I) (x : I →₀ R) :
    cs.reflectionRepresentation hR hA (cs.simple i) x =
      x - Finsupp.linearCombination R (A i) x • Finsupp.single i 1 := by
  rw [reflectionRepresentation_simple, Module.preReflection_apply]

/-- Each simple reflection negates the corresponding basis vector. -/
theorem reflectionRepresentation_simple_single_self (i : I) :
    cs.reflectionRepresentation hR hA (cs.simple i) (Finsupp.single i 1) = -Finsupp.single i 1 := by
  rw [reflectionRepresentation_simple]
  exact Module.preReflection_apply_self
    (TauCeti.linearCombination_single_eq_two_of_algebraMap_eq_two_mul_geometricForm hR hA i)

/-- Multiplying on the right by `cs.simple i` negates the image of the `i`-th simple basis
vector. -/
theorem reflectionRepresentation_mul_simple_single (w : W) (i : I) :
    cs.reflectionRepresentation hR hA (w * cs.simple i) (Finsupp.single i 1) =
      -cs.reflectionRepresentation hR hA w (Finsupp.single i 1) := by
  rw [map_mul, mul_apply_eq_comp, reflectionRepresentation_simple_single_self, map_neg]

/-- **The coefficient map intertwines the representation over `R` with the geometric
representation**: `c (ρ_R(w) x) = ρ(w) (c x)` for the map `c` applying `R → ℝ` to every
coefficient. -/
theorem mapRange_reflectionRepresentation (w : W) (x : I →₀ R) :
    (cs.reflectionRepresentation hR hA w x).mapRange (algebraMap R ℝ) (map_zero _) =
      cs.geometricRepresentation w (x.mapRange (algebraMap R ℝ) (map_zero _)) := by
  induction w using cs.simple_induction generalizing x with
  | simple i =>
    rw [reflectionRepresentation_simple, geometricRepresentation_simple,
      CoxeterMatrix.mapRange_preReflection hA]
  | one => simp
  | mul w w' hw hw' => simp only [map_mul, mul_apply_eq_comp, hw, hw']

/-- **The representation over `R` is faithful.** An element acting trivially on `I →₀ R` fixes
every simple root of the geometric representation, so it is trivial by Tits' theorem
`CoxeterSystem.geometricRepresentation_injective`. -/
theorem reflectionRepresentation_injective :
    Function.Injective (cs.reflectionRepresentation hR hA) := by
  refine (injective_iff_map_eq_one _).2 fun w hw ↦ cs.geometricRepresentation_injective ?_
  rw [map_one]
  refine Finsupp.lhom_ext fun i r ↦ ?_
  have h := cs.mapRange_reflectionRepresentation hR hA w (Finsupp.single i 1)
  rw [hw, one_apply_eq_self, Finsupp.mapRange_single, map_one] at h
  rw [one_apply_eq_self, ← mul_one r, ← smul_eq_mul, ← Finsupp.smul_single, map_smul, ← h]

/-- **The representation over `R` preserves the form of `A`.** -/
theorem finsuppBilinForm_reflectionRepresentation (w : W) (x y : I →₀ R) :
    A.finsuppBilinForm (cs.reflectionRepresentation hR hA w x)
        (cs.reflectionRepresentation hR hA w y) = A.finsuppBilinForm x y := by
  refine hR ?_
  rw [CoxeterMatrix.algebraMap_finsuppBilinForm hA, CoxeterMatrix.algebraMap_finsuppBilinForm hA,
    mapRange_reflectionRepresentation, mapRange_reflectionRepresentation,
    geometricForm_geometricRepresentation]

/-- For a finite index set with decidable equality, `cs.reflectionRepresentation hR hA` preserves
`Matrix.toBilin' A`. -/
theorem toBilin'_reflectionRepresentation [Fintype I] [DecidableEq I] (w : W) (x y : I →₀ R) :
    Matrix.toBilin' A (cs.reflectionRepresentation hR hA w x)
        (cs.reflectionRepresentation hR hA w y) =
      Matrix.toBilin' A x y := by
  rw [← A.finsuppBilinForm_apply_eq_toBilin', ← A.finsuppBilinForm_apply_eq_toBilin',
    cs.finsuppBilinForm_reflectionRepresentation]

/-- **The image of the representation over `R` is generated by the reflections of `A`**: it is
the submonoid of `Module.End R (I →₀ R)` generated by the reflections `x ↦ x - (∑ⱼ xⱼ A i j) eᵢ`. -/
theorem mrange_reflectionRepresentation :
    MonoidHom.mrange (cs.reflectionRepresentation hR hA) =
      Submonoid.closure (Set.range fun i ↦
        Module.preReflection (Finsupp.single i 1) (Finsupp.linearCombination R (A i))) := by
  rw [MonoidHom.mrange_eq_map, ← cs.submonoidClosure_range_simple, MonoidHom.map_mclosure,
    ← Set.range_comp]
  simp only [Function.comp_def, reflectionRepresentation_simple]

open TauCeti in
/-- **The image of the representation over `R` in the linear automorphisms is generated by the
reflections of `A`**: it is the subgroup of `(I →₀ R) ≃ₗ[R] (I →₀ R)` generated by the
reflections `x ↦ x - (∑ⱼ xⱼ A i j) eᵢ`. -/
theorem range_generalLinearEquiv_comp_asGroupHom_reflectionRepresentation :
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv R (I →₀ R)).toMonoidHom.comp
        (cs.reflectionRepresentation hR hA).asGroupHom).range =
      Subgroup.closure (Set.range fun i ↦
        Module.reflection
          (linearCombination_single_eq_two_of_algebraMap_eq_two_mul_geometricForm hR hA i)) := by
  rw [MonoidHom.range_eq_map, ← cs.subgroupClosure_range_simple, MonoidHom.map_closure,
    ← Set.range_comp]
  congr 2
  funext i
  refine LinearEquiv.ext fun x ↦ ?_
  simp [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, Representation.asGroupHom_apply,
    reflectionRepresentation_simple, Module.reflection_apply, Module.preReflection_apply]

include hA in
/-- **The geometric representation preserves the vectors with coefficients in `R`**, when a
matrix `A` over `R` maps entrywise to the doubled Gram matrix `2 B(αᵢ, αⱼ)` of the canonical form:
a vector of `I →₀ ℝ` has all of its coefficients in the image of `R` exactly when its image under
any element of `W` does. Injectivity of `R → ℝ` is not needed. -/
theorem geometricRepresentation_apply_mem_range_mapRange_iff (w : W) {v : I →₀ ℝ} :
    cs.geometricRepresentation w v ∈ Set.range (Finsupp.mapRange (algebraMap R ℝ) (map_zero _)) ↔
      v ∈ Set.range (Finsupp.mapRange (algebraMap R ℝ) (map_zero _)) := by
  have hmaps (w : W) : Set.MapsTo (cs.geometricRepresentation w)
      (Set.range (Finsupp.mapRange (algebraMap R ℝ) (map_zero _)))
      (Set.range (Finsupp.mapRange (algebraMap R ℝ) (map_zero _))) := by
    induction w using cs.simple_induction with
    | simple i =>
      rintro _ ⟨x, rfl⟩
      exact ⟨Module.preReflection (Finsupp.single i 1) (Finsupp.linearCombination R (A i)) x, by
        rw [geometricRepresentation_simple, CoxeterMatrix.mapRange_preReflection hA]⟩
    | one => simp
    | mul w w' hw hw' =>
      rw [map_mul, FunLike.coe_mul_eq_comp]
      exact hw.comp hw'
  refine ⟨fun h ↦ ?_, fun h ↦ hmaps w h⟩
  have := hmaps w⁻¹ h
  rwa [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self] at this

/-! ### Roots and sign criterion over subrings -/

/-- **The roots of `cs.reflectionRepresentation hR hA`**: the `W`-orbit of the standard basis
vectors `Finsupp.single i 1` in `I →₀ R`. -/
def reflectionRoots : Set (I →₀ R) :=
  {x | ∃ (w : W) (i : I), cs.reflectionRepresentation hR hA w (Finsupp.single i 1) = x}

/-- Membership in `CoxeterSystem.reflectionRoots` means lying in the `W`-orbit of the standard basis
vectors `Finsupp.single i 1`. -/
theorem mem_reflectionRoots {x : I →₀ R} :
    x ∈ cs.reflectionRoots hR hA ↔
      ∃ (w : W) (i : I), cs.reflectionRepresentation hR hA w (Finsupp.single i 1) = x :=
  Iff.rfl

/-- Every standard basis vector `Finsupp.single i 1` is a root in `I →₀ R`. -/
@[simp]
theorem single_mem_reflectionRoots (i : I) :
    Finsupp.single i 1 ∈ cs.reflectionRoots hR hA :=
  ⟨1, i, by simp⟩

/-- The set of roots in `I →₀ R` is invariant under `W`. -/
@[simp]
theorem reflectionRepresentation_apply_mem_reflectionRoots_iff (w : W) {x : I →₀ R} :
    cs.reflectionRepresentation hR hA w x ∈ cs.reflectionRoots hR hA ↔
      x ∈ cs.reflectionRoots hR hA := by
  have forward (g : W) {u : I →₀ R} (hu : u ∈ cs.reflectionRoots hR hA) :
      cs.reflectionRepresentation hR hA g u ∈ cs.reflectionRoots hR hA := by
    obtain ⟨w', i, rfl⟩ := hu
    exact ⟨g * w', i, by rw [map_mul, mul_apply_eq_comp]⟩
  exact ⟨fun h ↦ by simpa using forward w⁻¹ h, forward w⟩

/-- The set of roots in `I →₀ R` is closed under negation. -/
@[simp]
theorem neg_mem_reflectionRoots_iff {x : I →₀ R} :
    -x ∈ cs.reflectionRoots hR hA ↔ x ∈ cs.reflectionRoots hR hA := by
  have forward {u : I →₀ R} (hu : u ∈ cs.reflectionRoots hR hA) :
      -u ∈ cs.reflectionRoots hR hA := by
    obtain ⟨w, i, rfl⟩ := hu
    exact ⟨w * cs.simple i, i, cs.reflectionRepresentation_mul_simple_single hR hA w i⟩
  exact ⟨fun h ↦ by simpa using forward h, forward⟩

/-- Coefficientwise application of `algebraMap R ℝ` maps `cs.reflectionRoots hR hA` onto
`cs.geometricRoots`. -/
theorem image_mapRange_reflectionRoots :
    Finsupp.mapRange (algebraMap R ℝ) (map_zero _) '' cs.reflectionRoots hR hA =
      cs.geometricRoots := by
  ext v
  rw [Set.mem_image, cs.mem_geometricRoots]
  constructor
  · rintro ⟨x, ⟨w, i, rfl⟩, rfl⟩
    exact ⟨w, i, by
      simpa [Finsupp.mapRange_single] using
        (cs.mapRange_reflectionRepresentation hR hA w (Finsupp.single i 1)).symm⟩
  · rintro ⟨w, i, rfl⟩
    refine ⟨cs.reflectionRepresentation hR hA w (Finsupp.single i 1), ⟨w, i, rfl⟩, ?_⟩
    simpa [Finsupp.mapRange_single] using
      cs.mapRange_reflectionRepresentation hR hA w (Finsupp.single i 1)

/-- A vector in `I →₀ R` maps to a real geometric root if and only if it belongs to
`cs.reflectionRoots hR hA`. -/
theorem mapRange_mem_geometricRoots_iff {x : I →₀ R} :
    x.mapRange (algebraMap R ℝ) (map_zero _) ∈ cs.geometricRoots ↔
      x ∈ cs.reflectionRoots hR hA := by
  rw [← cs.image_mapRange_reflectionRoots hR hA,
    (Finsupp.mapRange_injective _ (map_zero _) hR).mem_set_image]

/-- Every root in `cs.reflectionRoots hR hA` has self-pairing `2` under `A.finsuppBilinForm`. -/
theorem finsuppBilinForm_self_of_mem_reflectionRoots {x : I →₀ R}
    (hx : x ∈ cs.reflectionRoots hR hA) : A.finsuppBilinForm x x = 2 := by
  obtain ⟨w, i, rfl⟩ := hx
  rw [cs.finsuppBilinForm_reflectionRepresentation hR hA, Matrix.finsuppBilinForm_single_single,
    TauCeti.apply_same_eq_two_of_algebraMap_eq_two_mul_geometricForm hR hA i, one_mul, one_mul]

section OrderedSubring

variable [LinearOrder R]

/-- **The sign criterion over an ordered subring of `ℝ`, positive case** (for instance `R = ℤ` with
`Int.cast_strictMono`): `0 < ρ_R(w) eᵢ` if and only if `i` is not a right descent of `w`. -/
theorem reflectionRepresentation_single_pos_iff (hmono : StrictMono (algebraMap R ℝ))
    (w : W) (i : I) :
    0 < cs.reflectionRepresentation hR hA w (Finsupp.single i 1) ↔ ¬cs.IsRightDescent w i := by
  rw [← Finsupp.mapRange_lt_mapRange_iff hmono (map_zero _), Finsupp.mapRange_zero,
    cs.mapRange_reflectionRepresentation hR hA, Finsupp.mapRange_single, map_one,
    cs.geometricRepresentation_single_pos_iff]

/-- **The sign criterion over an ordered subring of `ℝ`, negative case**: `ρ_R(w) eᵢ < 0` if and
only if `i` is a right descent of `w`. -/
theorem reflectionRepresentation_single_neg_iff (hmono : StrictMono (algebraMap R ℝ))
    (w : W) (i : I) :
    cs.reflectionRepresentation hR hA w (Finsupp.single i 1) < 0 ↔ cs.IsRightDescent w i := by
  rw [← Finsupp.mapRange_lt_mapRange_iff hmono (map_zero _), Finsupp.mapRange_zero,
    cs.mapRange_reflectionRepresentation hR hA, Finsupp.mapRange_single, map_one,
    cs.geometricRepresentation_single_neg_iff]

/-- **Every root over an ordered subring of `ℝ` is strictly positive or strictly negative.** -/
theorem pos_or_neg_of_mem_reflectionRoots (hmono : StrictMono (algebraMap R ℝ)) {x : I →₀ R}
    (hx : x ∈ cs.reflectionRoots hR hA) : 0 < x ∨ x < 0 := by
  obtain ⟨w, i, rfl⟩ := hx
  by_cases h : cs.IsRightDescent w i
  · exact Or.inr ((cs.reflectionRepresentation_single_neg_iff hR hA hmono w i).2 h)
  · exact Or.inl ((cs.reflectionRepresentation_single_pos_iff hR hA hmono w i).2 h)

end OrderedSubring

/-! ### Scalar change along ring homomorphisms and reduction modulo an ideal or integer -/

section ScalarChange

variable {S T : Type*} [CommRing S] [CommRing T]

/-- **The reflection representation on `I →₀ S` pushed forward from
`cs.reflectionRepresentation hR hA` along a ring homomorphism `f : R →+* S`** (for `A` mapping
entrywise to the doubled Gram matrix `2 * M.geometricForm` along an injective algebra map
`R → ℝ`), in which `s i` acts by `x ↦ x - (∑ⱼ xⱼ f (A i j)) eᵢ`. Taking `R = ℤ` and
`f = Int.castRingHom S` gives the reduced action on `I →₀ (ZMod n)` or
`I →₀ (ℤ ⧸ Ideal.span {m})`, which need not be faithful (for instance in rank one modulo `2`
the generator acts trivially). -/
noncomputable def mapReflectionRepresentation (f : R →+* S) : Representation S W (I →₀ S) :=
  cs.lift ⟨_, CoxeterMatrix.isLiftable_preReflection_map
    (CoxeterMatrix.isLiftable_preReflection hR hA) f⟩

/-- Over `S`, `cs.simple i` acts by the pre-reflection of `A.map f` at `i`. -/
theorem mapReflectionRepresentation_simple (f : R →+* S) (i : I) :
    cs.mapReflectionRepresentation hR hA f (cs.simple i) =
      Module.preReflection (Finsupp.single i 1) (Finsupp.linearCombination S (A.map f i)) :=
  cs.lift_apply_simple
    (CoxeterMatrix.isLiftable_preReflection_map
      (CoxeterMatrix.isLiftable_preReflection hR hA) f) i

/-- **Generator formula** for `cs.mapReflectionRepresentation hR hA f`. -/
@[simp]
theorem mapReflectionRepresentation_simple_apply (f : R →+* S) (i : I) (x : I →₀ S) :
    cs.mapReflectionRepresentation hR hA f (cs.simple i) x =
      x - Finsupp.linearCombination S (A.map f i) x • Finsupp.single i 1 := by
  rw [mapReflectionRepresentation_simple, Module.preReflection_apply]

/-- Along `RingHom.id R`, `mapReflectionRepresentation` recovers `reflectionRepresentation`. -/
@[simp]
theorem mapReflectionRepresentation_id :
    cs.mapReflectionRepresentation hR hA (RingHom.id R) = cs.reflectionRepresentation hR hA := by
  refine cs.ext_simple fun i ↦ LinearMap.ext fun x ↦ ?_
  simp

/-- Along `algebraMap R ℝ`, `mapReflectionRepresentation` recovers `geometricRepresentation`. -/
@[simp]
theorem mapReflectionRepresentation_algebraMap_real :
    cs.mapReflectionRepresentation hR hA (algebraMap R ℝ) = cs.geometricRepresentation := by
  refine cs.ext_simple fun i ↦ Finsupp.lhom_ext' fun j ↦ LinearMap.ext_ring ?_
  simp [cs.geometricRepresentation_simple, CoxeterMatrix.geometricReflection_apply, hA]

/-- **Functoriality of `mapReflectionRepresentation` under ring homomorphisms**:
`Finsupp.mapRange g` intertwines the `f`-mapped representation on `I →₀ S` with the
`(g.comp f)`-mapped representation on `I →₀ T`. -/
theorem mapRange_mapReflectionRepresentation (f : R →+* S) (g : S →+* T) (w : W) (x : I →₀ S) :
    (cs.mapReflectionRepresentation hR hA f w x).mapRange g g.map_zero =
      cs.mapReflectionRepresentation hR hA (g.comp f) w (x.mapRange g g.map_zero) := by
  induction w using cs.simple_induction generalizing x with
  | simple i =>
    rw [mapReflectionRepresentation_simple, mapReflectionRepresentation_simple,
      (A.map f).mapRange_preReflection_single_linearCombination g i x, Matrix.map_map,
      ← RingHom.coe_comp]
  | one => simp
  | mul w₁ w₂ hw₁ hw₂ =>
    simp only [map_mul, mul_apply_eq_comp, hw₁, hw₂]

/-- Coefficientwise application of any ring homomorphism `f : R →+* S` intertwines
`cs.reflectionRepresentation hR hA` with `cs.mapReflectionRepresentation hR hA f`. -/
theorem mapRange_ringHom_reflectionRepresentation (f : R →+* S) (w : W) (x : I →₀ R) :
    (cs.reflectionRepresentation hR hA w x).mapRange f f.map_zero =
      cs.mapReflectionRepresentation hR hA f w (x.mapRange f f.map_zero) := by
  simpa using cs.mapRange_mapReflectionRepresentation hR hA (RingHom.id R) f w x

/-- `cs.mapReflectionRepresentation hR hA f` preserves the mapped Gram form
`(A.map f).finsuppBilinForm`. -/
theorem finsuppBilinForm_mapReflectionRepresentation (f : R →+* S) (w : W) (x y : I →₀ S) :
    (A.map f).finsuppBilinForm (cs.mapReflectionRepresentation hR hA f w x)
        (cs.mapReflectionRepresentation hR hA f w y) =
      (A.map f).finsuppBilinForm x y := by
  have hsym : (A.map f).IsSymm :=
    (TauCeti.isSymm_of_algebraMap_eq_two_mul_geometricForm hR hA).map f
  have hdiag (i : I) : A.map f i i = 2 := by
    rw [Matrix.map_apply,
      TauCeti.apply_same_eq_two_of_algebraMap_eq_two_mul_geometricForm hR hA i, map_ofNat]
  induction w using cs.simple_induction generalizing x y with
  | simple i =>
    rw [mapReflectionRepresentation_simple]
    exact Matrix.finsuppBilinForm_preReflection_single_linearCombination hsym (hdiag i) x y
  | one => simp
  | mul w₁ w₂ hw₁ hw₂ =>
    simp only [map_mul, mul_apply_eq_comp, hw₁, hw₂]

/-- Simple-reflection formula for the quotient reduction
`(cs.reflectionRepresentation hR hA).quotSMulTop m` modulo a scalar `m : R`. -/
theorem quotSMulTop_reflectionRepresentation_simple_mk (m : R) (i : I) (x : I →₀ R) :
    (cs.reflectionRepresentation hR hA).quotSMulTop m (cs.simple i) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (x - Finsupp.linearCombination R (A i) x • Finsupp.single i 1) := by
  rw [Representation.quotSMulTop_apply_mk, reflectionRepresentation_simple_apply]

end ScalarChange

/-! ### Transport along a basis of a free `R`-module and scalar extension -/

section BasisTransport

variable {L' : Type*} [AddCommGroup L'] [Module R L'] (b : Module.Basis I R L')

/-- **Transport of `cs.reflectionRepresentation hR hA` along a basis `b : Module.Basis I R L'`**:
conjugation by `b.repr.symm : (I →₀ R) ≃ₗ[R] L'`, which sends `Finsupp.single i 1` to `b i`. -/
noncomputable def reflectionRepresentationOfBasis : Representation R W L' :=
  (b.repr.symm.conjRingEquiv : Module.End R (I →₀ R) →* Module.End R L').comp
    (cs.reflectionRepresentation hR hA)

/-- Defining formula for `cs.reflectionRepresentationOfBasis hR hA b` via `b.repr`. -/
theorem reflectionRepresentationOfBasis_apply (w : W) (x : L') :
    cs.reflectionRepresentationOfBasis hR hA b w x =
      b.repr.symm (cs.reflectionRepresentation hR hA w (b.repr x)) := by
  simp [reflectionRepresentationOfBasis]

/-- `b.repr` intertwines `cs.reflectionRepresentationOfBasis hR hA b` with
`cs.reflectionRepresentation hR hA`. -/
@[simp]
theorem repr_reflectionRepresentationOfBasis (w : W) (x : L') :
    b.repr (cs.reflectionRepresentationOfBasis hR hA b w x) =
      cs.reflectionRepresentation hR hA w (b.repr x) := by
  simp [reflectionRepresentationOfBasis_apply]

/-- `b.repr.symm` intertwines `cs.reflectionRepresentation hR hA` with
`cs.reflectionRepresentationOfBasis hR hA b`. -/
theorem reflectionRepresentationOfBasis_repr_symm (w : W) (x : I →₀ R) :
    cs.reflectionRepresentationOfBasis hR hA b w (b.repr.symm x) =
      b.repr.symm (cs.reflectionRepresentation hR hA w x) := by
  simp [reflectionRepresentationOfBasis_apply]

/-- Simple-reflection formula in the coordinates of `b`. -/
theorem reflectionRepresentationOfBasis_simple_apply (i : I) (x : L') :
    cs.reflectionRepresentationOfBasis hR hA b (cs.simple i) x =
      x - Finsupp.linearCombination R (A i) (b.repr x) • b i := by
  rw [reflectionRepresentationOfBasis_apply, reflectionRepresentation_simple_apply, map_sub,
    b.repr.symm_apply_apply, LinearEquiv.map_smul]
  simp

/-- Action of `cs.simple i` on a basis vector `b j`. -/
@[simp]
theorem reflectionRepresentationOfBasis_simple_basis (i j : I) :
    cs.reflectionRepresentationOfBasis hR hA b (cs.simple i) (b j) = b j - A i j • b i := by
  simp [reflectionRepresentationOfBasis_simple_apply]

/-- `cs.simple i` negates the basis vector `b i`. -/
theorem reflectionRepresentationOfBasis_simple_self (i : I) :
    cs.reflectionRepresentationOfBasis hR hA b (cs.simple i) (b i) = -b i := by
  rw [reflectionRepresentationOfBasis_simple_basis,
    TauCeti.apply_same_eq_two_of_algebraMap_eq_two_mul_geometricForm hR hA i, two_smul,
    sub_add_eq_sub_sub, sub_self, zero_sub]

/-- Faithfulness of the transported representation on `L'`. -/
theorem reflectionRepresentationOfBasis_injective :
    Function.Injective (cs.reflectionRepresentationOfBasis hR hA b) :=
  b.repr.symm.conjRingEquiv.injective.comp (cs.reflectionRepresentation_injective hR hA)

/-- For a finite index set, the transported representation on `L'` preserves
`Matrix.toBilin b A`. -/
theorem toBilin_reflectionRepresentationOfBasis [Fintype I] [DecidableEq I] (w : W) (x y : L') :
    Matrix.toBilin b A (cs.reflectionRepresentationOfBasis hR hA b w x)
        (cs.reflectionRepresentationOfBasis hR hA b w y) =
      Matrix.toBilin b A x y := by
  rw [← A.finsuppBilinForm_repr_eq_toBilin b, ← A.finsuppBilinForm_repr_eq_toBilin b,
    cs.repr_reflectionRepresentationOfBasis, cs.repr_reflectionRepresentationOfBasis,
    cs.finsuppBilinForm_reflectionRepresentation]

/-- **The coordinate equivalence `b.repr : L' ≃ₗ[R] (I →₀ R)` as an equivalence of `R`-linear
`W`-representations**, sending `b i` to `Finsupp.single i 1`. -/
noncomputable def reflectionRepresentationOfBasisEquiv :
    (cs.reflectionRepresentationOfBasis hR hA b).Equiv (cs.reflectionRepresentation hR hA) :=
  Representation.Equiv.mk b.repr fun w ↦
    LinearMap.ext fun x ↦ cs.repr_reflectionRepresentationOfBasis hR hA b w x

/-- Underlying linear equivalence of `reflectionRepresentationOfBasisEquiv`. -/
@[simp]
theorem toLinearEquiv_reflectionRepresentationOfBasisEquiv :
    (cs.reflectionRepresentationOfBasisEquiv hR hA b).toLinearEquiv = b.repr :=
  (rfl)

/-- Forward evaluation of `reflectionRepresentationOfBasisEquiv` is `b.repr`. -/
@[simp]
theorem reflectionRepresentationOfBasisEquiv_apply (x : L') :
    cs.reflectionRepresentationOfBasisEquiv hR hA b x = b.repr x :=
  (rfl)

/-- Inverse evaluation of `reflectionRepresentationOfBasisEquiv` is `b.repr.symm`. -/
@[simp]
theorem reflectionRepresentationOfBasisEquiv_symm_apply (x : I →₀ R) :
    (cs.reflectionRepresentationOfBasisEquiv hR hA b).symm x = b.repr.symm x := by
  simp [reflectionRepresentationOfBasisEquiv]

/-- **Extending scalars of `L'` along an `R`-algebra `S`**: the coordinate equivalence
`(b.baseChange S).repr` intertwines `Representation.baseChange S` of
`cs.reflectionRepresentationOfBasis hR hA b` with
`cs.mapReflectionRepresentation hR hA (algebraMap R S)`. -/
theorem repr_baseChange_reflectionRepresentationOfBasis (S : Type*) [CommRing S] [Algebra R S]
    (w : W) (z : S ⊗[R] L') :
    (b.baseChange S).repr
        (Representation.baseChange S (cs.reflectionRepresentationOfBasis hR hA b) w z) =
      cs.mapReflectionRepresentation hR hA (algebraMap R S) w ((b.baseChange S).repr z) := by
  have hMap :
      (b.baseChange S).repr.toLinearMap ∘ₗ
          Representation.baseChange S (cs.reflectionRepresentationOfBasis hR hA b) w =
        cs.mapReflectionRepresentation hR hA (algebraMap R S) w ∘ₗ
          (b.baseChange S).repr.toLinearMap := by
    refine (b.baseChange S).ext fun j ↦ ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Module.Basis.baseChange_apply, Representation.baseChange_apply, LinearMap.baseChange_tmul,
      b.baseChange_repr_one_tmul, cs.repr_reflectionRepresentationOfBasis, b.repr_self,
      cs.mapRange_ringHom_reflectionRepresentation hR hA (algebraMap R S) w]
  exact LinearMap.congr_fun hMap z

/-- **Equivariant scalar-extension isomorphism `S ⊗[R] L' ≃ I →₀ S`** for any commutative
`R`-algebra `S`, given by `(b.baseChange S).repr`. -/
noncomputable def baseChangeReflectionRepresentationOfBasisEquiv
    (S : Type*) [CommRing S] [Algebra R S] :
    (Representation.baseChange S (cs.reflectionRepresentationOfBasis hR hA b)).Equiv
      (cs.mapReflectionRepresentation hR hA (algebraMap R S)) :=
  Representation.Equiv.mk (b.baseChange S).repr fun w ↦
    LinearMap.ext fun z ↦ cs.repr_baseChange_reflectionRepresentationOfBasis hR hA b S w z

/-- Underlying linear equivalence of `baseChangeReflectionRepresentationOfBasisEquiv`. -/
@[simp]
theorem toLinearEquiv_baseChangeReflectionRepresentationOfBasisEquiv
    (S : Type*) [CommRing S] [Algebra R S] :
    (cs.baseChangeReflectionRepresentationOfBasisEquiv hR hA b S).toLinearEquiv =
      (b.baseChange S).repr :=
  (rfl)

/-- Forward evaluation of `baseChangeReflectionRepresentationOfBasisEquiv` is
`(b.baseChange S).repr`. -/
@[simp]
theorem baseChangeReflectionRepresentationOfBasisEquiv_apply
    (S : Type*) [CommRing S] [Algebra R S] (z : S ⊗[R] L') :
    cs.baseChangeReflectionRepresentationOfBasisEquiv hR hA b S z = (b.baseChange S).repr z :=
  (rfl)

/-- Inverse evaluation of `baseChangeReflectionRepresentationOfBasisEquiv` is
`(b.baseChange S).repr.symm`. -/
@[simp]
theorem baseChangeReflectionRepresentationOfBasisEquiv_symm_apply
    (S : Type*) [CommRing S] [Algebra R S] (y : I →₀ S) :
    (cs.baseChangeReflectionRepresentationOfBasisEquiv hR hA b S).symm y =
      (b.baseChange S).repr.symm y := by
  simp [baseChangeReflectionRepresentationOfBasisEquiv]

/-- **Equivariant isomorphism `(ℝ ⊗[R] L') ≃ (I →₀ ℝ)`** identifying the real scalar extension of
the transported representation along `b` with `cs.geometricRepresentation`, sending `1 ⊗ₜ b i` to
the simple root `Finsupp.single i 1`. -/
noncomputable def baseChangeRealReflectionRepresentationOfBasisEquiv :
    (Representation.baseChange ℝ (cs.reflectionRepresentationOfBasis hR hA b)).Equiv
      cs.geometricRepresentation :=
  Representation.Equiv.mk (b.baseChange ℝ).repr fun w ↦
    LinearMap.ext fun z ↦ by
      simpa using cs.repr_baseChange_reflectionRepresentationOfBasis hR hA b ℝ w z

/-- Underlying linear equivalence of `baseChangeRealReflectionRepresentationOfBasisEquiv`. -/
@[simp]
theorem toLinearEquiv_baseChangeRealReflectionRepresentationOfBasisEquiv :
    (cs.baseChangeRealReflectionRepresentationOfBasisEquiv hR hA b).toLinearEquiv =
      (b.baseChange ℝ).repr :=
  (rfl)

/-- Forward evaluation of `baseChangeRealReflectionRepresentationOfBasisEquiv` is
`(b.baseChange ℝ).repr`. -/
@[simp]
theorem baseChangeRealReflectionRepresentationOfBasisEquiv_apply (z : ℝ ⊗[R] L') :
    cs.baseChangeRealReflectionRepresentationOfBasisEquiv hR hA b z = (b.baseChange ℝ).repr z :=
  (rfl)

/-- Inverse evaluation of `baseChangeRealReflectionRepresentationOfBasisEquiv` is
`(b.baseChange ℝ).repr.symm`. -/
@[simp]
theorem baseChangeRealReflectionRepresentationOfBasisEquiv_symm_apply (y : I →₀ ℝ) :
    (cs.baseChangeRealReflectionRepresentationOfBasisEquiv hR hA b).symm y =
      (b.baseChange ℝ).repr.symm y := by
  simp [baseChangeRealReflectionRepresentationOfBasisEquiv]

end BasisTransport

/-- Transporting `cs.reflectionRepresentation hR hA` along `Finsupp.basisSingleOne` gives back
`cs.reflectionRepresentation hR hA`. -/
@[simp]
theorem reflectionRepresentationOfBasis_basisSingleOne :
    cs.reflectionRepresentationOfBasis hR hA (Finsupp.basisSingleOne (ι := I) (R := R)) =
      cs.reflectionRepresentation hR hA := by
  refine MonoidHom.ext fun w ↦ LinearMap.ext fun x ↦ ?_
  simp [reflectionRepresentationOfBasis_apply]

end CoxeterSystem

namespace CoxeterMatrix

/-- **The entry `M i j` is the exact order of the product of two simple reflections of `A`**, when
`A` maps entrywise to the doubled Gram matrix `2 * M.geometricForm` along an injective algebra map
`R → ℝ`. -/
theorem pow_preReflection_mul_eq_one_iff {I R : Type*} [CommRing R] [Algebra R ℝ]
    {M : CoxeterMatrix I} {A : Matrix I I R} (hR : Function.Injective (algebraMap R ℝ))
    (hA : ∀ i j, algebraMap R ℝ (A i j) =
      2 * M.geometricForm (Finsupp.single i 1) (Finsupp.single j 1))
    (i j : I) (n : ℕ) :
    (Module.preReflection (Finsupp.single i 1) (Finsupp.linearCombination R (A i)) *
        Module.preReflection (Finsupp.single j 1) (Finsupp.linearCombination R (A j))) ^ n = 1 ↔
      M i j ∣ n := by
  rw [← M.toCoxeterSystem.reflectionRepresentation_simple hR hA i,
    ← M.toCoxeterSystem.reflectionRepresentation_simple hR hA j, ← map_mul, ← map_pow,
    ← map_one (M.toCoxeterSystem.reflectionRepresentation hR hA),
    (M.toCoxeterSystem.reflectionRepresentation_injective hR hA).eq_iff,
    M.toCoxeterSystem.simple_mul_simple_pow_eq_one_iff]

end CoxeterMatrix
