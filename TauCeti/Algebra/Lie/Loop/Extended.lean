/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Loop
public import TauCeti.Algebra.Lie.Extension.Basic
public import TauCeti.Algebra.Lie.Loop.Cocycle
public import TauCeti.Algebra.Lie.SemiDirect.Basic
-- Proof-only: graded tensor membership.
import TauCeti.RingTheory.GradedAlgebra.DecomposeTensor

/-!
# The extended affine loop algebra and its invariant bilinear form

Let `L` be a Lie algebra over a commutative ring `R`, and let `loopAlgebra R ℤ L = R[t, t⁻¹] ⊗ L`
have modes `x_n = tⁿ ⊗ x`. The **degree derivation** `d = t d/dt`
(`TauCeti.LieAlgebra.LoopAlgebra.degreeDerivation`) acts by `d(x_n) = n x_n`.

For an invariant symmetric bilinear form `Φ` on `L` (over an additively torsion-free ring `R`),
`ofTwoCocycle (twoCocycleOfBilinear R ℤ L Φ hΦ hΦs)` is the residue central extension `ĝ` with
central element `K = (0, 1)`. Adjoining the lifted derivation `extensionDegreeDerivation` gives the
**extended affine loop algebra** `ĝ' = extendedResidueExtension Φ hΦ hΦs = ĝ ⋊ R d`, with
`⁅d, x_n⁆ = n x_n`, `⁅d, K⁆ = 0`, and `K` central.

Combining `-constantTermPairing Φ` (where `(x_m, y_n)_0 = Φ(x, y) δ_{m + n, 0}`) with the
hyperbolic pairing `(K, d) = 1` yields the symmetric invariant bilinear form `extendedBilinForm` on
`ĝ'`, which is nondegenerate whenever `Φ` is. Rescaling `Ψ = r • Φ` induces `extendedLevelHom`
and `extendedLevelEquiv`, scaling `extendedBilinForm` by `r`.

## Main definitions

* `TauCeti.LieAlgebra.LoopAlgebra.degreeDerivationOf`, `degreeDerivation`, `constantTermPairing`,
  `extensionDegreeDerivation`, `extendedResidueExtension`, `toExtendedResidueExtension`,
  `degreeElement`, `degreeProj`, `extendedToProd`, `mode`, `constHom`, `extendedBilinForm`,
  `extendedLevelHom`, `extendedLevelEquiv`.

## Main results

* `TauCeti.LieAlgebra.LoopAlgebra.lie_mode_mode`, `lie_degreeElement_mode`,
  `toExtendedResidueExtension_centralElement_mem_center`, `mode_injective`, `constHom_injective`.
* `TauCeti.LieAlgebra.LoopAlgebra.extendedBilinForm_isSymm`, `extendedBilinForm_lieInvariant`,
  `extendedBilinForm_nondegenerate`, `extendedBilinForm_extendedLevelHom`,
  `extendedBilinForm_extendedLevelEquiv`, `extendedLevelEquiv_symm`.

## References

* V. G. Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., §7.2–7.4.
-/

public section

noncomputable section

open scoped TensorProduct
open _root_.LieAlgebra _root_.LieAlgebra.LoopAlgebra _root_.LieAlgebra.SemiDirectSum
open _root_.LieModule.Cohomology
open _root_.LieAlgebra.ofTwoCocycle (centralElement centralElement_mem_center)

namespace TauCeti.LieAlgebra.LoopAlgebra

/-! ### The degree derivation and constant-term pairing on polynomial loops -/

section Base

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

variable (R L) in
/-- **The generalized degree derivation** on `loopAlgebra R A L` attached to `χ : A →+ R`,
acting on modes by `D_χ (tᵃ ⊗ x) = χ a • (tᵃ ⊗ x)`. -/
def degreeDerivationOf {A : Type*} [AddCommMonoid A] [DecidableEq A] (χ : A →+ R) :
    LieDerivation R (loopAlgebra R A L) (loopAlgebra R A L) :=
  LieDerivation.ofGrading
    (fun a : A ↦ DirectSum.decomposeTensor (AddMonoidAlgebra.grade R) L a) χ

/-- On modes, `degreeDerivationOf R L χ` scales `tᵃ ⊗ x` by `χ a`. -/
@[simp]
theorem degreeDerivationOf_single_tmul {A : Type*} [AddCommMonoid A] [DecidableEq A]
    (χ : A →+ R) (a : A) (x : L) :
    degreeDerivationOf R L χ (AddMonoidAlgebra.single a (1 : R) ⊗ₜ[R] x) =
      χ a • (AddMonoidAlgebra.single a (1 : R) ⊗ₜ[R] x) :=
  LieDerivation.ofGrading_apply_apply _ χ
    (DirectSum.tmul_mem_decomposeTensor (AddMonoidAlgebra.single_mem_grade a 1) x)

/-- `degreeDerivationOf R L χ` vanishes on constant loops `1 ⊗ x`. -/
@[simp]
theorem degreeDerivationOf_one_tmul {A : Type*} [AddCommMonoid A] [DecidableEq A]
    (χ : A →+ R) (x : L) :
    degreeDerivationOf R L χ (1 ⊗ₜ[R] x) = 0 := by
  rw [AddMonoidAlgebra.one_def, degreeDerivationOf_single_tmul, map_zero, zero_smul]

variable (R L) in
/-- **The degree derivation `d = t d/dt`** on `loopAlgebra R ℤ L`: `d (tⁿ ⊗ x) = n (tⁿ ⊗ x)`. -/
def degreeDerivation : LieDerivation R (loopAlgebra R ℤ L) (loopAlgebra R ℤ L) :=
  degreeDerivationOf R L (Int.castAddHom R)

/-- On modes, the degree derivation multiplies `tⁿ ⊗ x` by `n`. -/
theorem degreeDerivation_single_tmul (n : ℤ) (x : L) :
    degreeDerivation R L (AddMonoidAlgebra.single n (1 : R) ⊗ₜ[R] x) =
      n • (AddMonoidAlgebra.single n (1 : R) ⊗ₜ[R] x) := by
  rw [degreeDerivation, degreeDerivationOf_single_tmul]
  exact Int.cast_smul_eq_zsmul R n (AddMonoidAlgebra.single n (1 : R) ⊗ₜ[R] x)

/-- On Laurent modes, the degree derivation multiplies `T n ⊗ x` by `n`. -/
@[simp]
theorem degreeDerivation_T_tmul (n : ℤ) (x : L) :
    degreeDerivation R L (LaurentPolynomial.T n ⊗ₜ[R] x) =
      n • (LaurentPolynomial.T n ⊗ₜ[R] x) := by
  have h : LaurentPolynomial.T n = AddMonoidAlgebra.single n (1 : R) := by
    simp only [LaurentPolynomial.single_eq_C_mul_T, map_one, one_mul]
  rw [h, degreeDerivation_single_tmul]

/-- The degree derivation vanishes on constant loops `1 ⊗ x`. -/
@[simp]
theorem degreeDerivation_one_tmul (x : L) :
    degreeDerivation R L (1 ⊗ₜ[R] x) = 0 :=
  degreeDerivationOf_one_tmul (Int.castAddHom R) x

/-- **The constant-term pairing** on `loopAlgebra R A L`: pairs `tᵐ ⊗ x` with `tⁿ ⊗ y` to
`Φ(x, y)` if `m + n = 0` and `0` otherwise. -/
def constantTermPairing {A : Type*} [AddCommGroup A] (Φ : LinearMap.BilinForm R L) :
    LinearMap.BilinForm R (loopAlgebra R A L) :=
  (Finsupp.lsum R fun m : A ↦ Φ.compl₂ (Finsupp.lapply (-m))).compl₁₂
    (toFinsupp R A L).toLinearMap (toFinsupp R A L).toLinearMap

/-- On modes, `constantTermPairing Φ` pairs `tᵐ ⊗ x` with `tⁿ ⊗ y` to
`Φ(x, y) δ_{m + n, 0}`. -/
@[simp]
theorem constantTermPairing_single_tmul {A : Type*} [AddCommGroup A] [DecidableEq A]
    (Φ : LinearMap.BilinForm R L) (m n : A) (x y : L) :
    constantTermPairing Φ (AddMonoidAlgebra.single m (1 : R) ⊗ₜ[R] x)
        (AddMonoidAlgebra.single n (1 : R) ⊗ₜ[R] y) =
      if m + n = 0 then Φ x y else 0 := by
  simp only [constantTermPairing, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
    toFinsupp_single_tmul, Finsupp.lsum_single, LinearMap.compl₂_apply, Finsupp.lapply_apply,
    Finsupp.single_apply]
  split_ifs with h₁ h₂ h₃
  · rfl
  · exact absurd (by rw [h₁, add_neg_cancel]) h₂
  · exact absurd (eq_neg_of_add_eq_zero_right h₃) h₁
  · exact map_zero (Φ x)

/-- Rescaling `Φ` rescales `constantTermPairing Φ`. -/
@[simp]
theorem constantTermPairing_smul {A : Type*} [AddCommGroup A]
    (r : R) (Φ : LinearMap.BilinForm R L) :
    constantTermPairing (A := A) (r • Φ) = r • constantTermPairing (A := A) Φ := by
  classical
  refine linearMap_ext_single_tmul fun m x ↦ linearMap_ext_single_tmul fun n y ↦ ?_
  simp only [LinearMap.smul_apply, smul_eq_mul, constantTermPairing_single_tmul]
  split_ifs <;> simp

/-- If `Φ` is symmetric, then `constantTermPairing Φ` is symmetric. -/
theorem constantTermPairing_isSymm {A : Type*} [AddCommGroup A]
    {Φ : LinearMap.BilinForm R L} (hΦs : Φ.IsSymm) :
    (constantTermPairing (A := A) Φ).IsSymm := by
  classical
  suffices h : constantTermPairing (A := A) Φ = (constantTermPairing (A := A) Φ).flip from
    LinearMap.BilinForm.isSymm_def.mpr fun u v ↦ LinearMap.congr_fun (LinearMap.congr_fun h u) v
  refine linearMap_ext_single_tmul fun m x ↦ linearMap_ext_single_tmul fun n y ↦ ?_
  simp [add_comm m n, hΦs.eq x y]

/-- If `Φ` is invariant on `L`, then `constantTermPairing Φ` is invariant on
`loopAlgebra R A L`. -/
theorem constantTermPairing_lieInvariant {A : Type*} [AddCommGroup A]
    {Φ : LinearMap.BilinForm R L} (hΦ : Φ.lieInvariant L) :
    (constantTermPairing (A := A) Φ).lieInvariant (loopAlgebra R A L) := by
  classical
  let B := constantTermPairing (A := A) Φ
  let lhs : loopAlgebra R A L →ₗ[R] loopAlgebra R A L →ₗ[R] loopAlgebra R A L →ₗ[R] R :=
    { toFun u := B.compl₁₂ (ad R (loopAlgebra R A L) u) LinearMap.id
      map_add' _ _ := LinearMap.ext₂ fun _ _ ↦ by simp
      map_smul' _ _ := LinearMap.ext₂ fun _ _ ↦ by simp }
  let rhs : loopAlgebra R A L →ₗ[R] loopAlgebra R A L →ₗ[R] loopAlgebra R A L →ₗ[R] R :=
    { toFun u := -(B.compl₂ (ad R (loopAlgebra R A L) u))
      map_add' _ _ := LinearMap.ext₂ fun _ _ ↦ by simp; abel
      map_smul' _ _ := LinearMap.ext₂ fun _ _ ↦ by simp }
  suffices h : lhs = rhs from fun u v w ↦ by
    simpa only [lhs, rhs, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.neg_apply,
      LinearMap.compl₁₂_apply, LinearMap.id_apply, LinearMap.compl₂_apply, ad_apply] using
      LinearMap.congr_fun₂ (LinearMap.congr_fun h u) v w
  refine linearMap_ext_single_tmul fun k x ↦ linearMap_ext_single_tmul fun m y ↦
    linearMap_ext_single_tmul fun n z ↦ ?_
  simp only [lhs, rhs, B, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.neg_apply,
    LinearMap.compl₁₂_apply, LinearMap.id_apply, LinearMap.compl₂_apply, ad_apply,
    ExtendScalars.bracket_tmul, AddMonoidAlgebra.single_mul_single, mul_one,
    constantTermPairing_single_tmul, add_left_comm m k n, add_assoc]
  split_ifs <;> simp [hΦ x y z]

/-- If `Φ` is left-separating on `L`, then `constantTermPairing Φ` is left-separating on
`loopAlgebra R A L`. -/
theorem constantTermPairing_separatingLeft {A : Type*} [AddCommGroup A]
    {Φ : LinearMap.BilinForm R L} (hΦ : Φ.SeparatingLeft) :
    (constantTermPairing (A := A) Φ).SeparatingLeft := by
  classical
  intro u hu
  apply (toFinsupp R A L).injective; ext m; rw [map_zero, Finsupp.zero_apply]
  refine hΦ _ fun y ↦ ?_
  have h := hu (AddMonoidAlgebra.single (-m) (1 : R) ⊗ₜ[R] y)
  simp only [constantTermPairing, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
    toFinsupp_single_tmul, Finsupp.lsum_apply, Finsupp.sum, LinearMap.sum_apply,
    LinearMap.compl₂_apply, Finsupp.lapply_apply] at h
  rw [Finset.sum_eq_single m
    (fun k _ hkm ↦ by simp [Finsupp.single_eq_of_ne (fun hk ↦ hkm (neg_inj.mp hk))])
    (fun hm ↦ by simp [Finsupp.notMem_support_iff.mp hm])] at h
  simpa using h

/-- The generalized degree derivation is skew for `constantTermPairing Φ`:
`(D_χ u, v)_0 + (u, D_χ v)_0 = 0`. -/
theorem constantTermPairing_degreeDerivationOf_add_eq_zero {A : Type*} [AddCommGroup A]
    [DecidableEq A] (χ : A →+ R) (Φ : LinearMap.BilinForm R L) (u v : loopAlgebra R A L) :
    constantTermPairing Φ (degreeDerivationOf R L χ u) v +
      constantTermPairing Φ u (degreeDerivationOf R L χ v) = 0 := by
  let B := constantTermPairing (A := A) Φ
  let D : loopAlgebra R A L →ₗ[R] loopAlgebra R A L := degreeDerivationOf R L χ
  suffices h : B.compl₁₂ D LinearMap.id + B.compl₂ D = 0 by
    simpa only [B, D, LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.id_apply,
      LinearMap.compl₂_apply, LieDerivation.coeFn_coe, LinearMap.zero_apply] using
      LinearMap.congr_fun (LinearMap.congr_fun h u) v
  refine linearMap_ext_single_tmul fun m x ↦ linearMap_ext_single_tmul fun n y ↦ ?_
  simp only [B, D, LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.id_apply,
    LinearMap.compl₂_apply, LieDerivation.coeFn_coe, LinearMap.zero_apply,
    degreeDerivationOf_single_tmul, map_smul, LinearMap.smul_apply,
    constantTermPairing_single_tmul, smul_eq_mul]
  split_ifs with h
  · rw [← add_mul, ← map_add, h, map_zero, zero_mul]
  · simp

/-- The degree derivation is skew for `constantTermPairing Φ`: `(d u, v)_0 + (u, d v)_0 = 0`. -/
theorem constantTermPairing_degreeDerivation_add_eq_zero (Φ : LinearMap.BilinForm R L)
    (u v : loopAlgebra R ℤ L) :
    constantTermPairing Φ (degreeDerivation R L u) v +
      constantTermPairing Φ u (degreeDerivation R L v) = 0 :=
  constantTermPairing_degreeDerivationOf_add_eq_zero (Int.castAddHom R) Φ u v

/-- **Constant-term pairing against the degree derivation equals the residue pairing**:
`(u, d v)_0 = Res(u dv)`. -/
theorem constantTermPairing_degreeDerivation_right (Φ : LinearMap.BilinForm R L)
    (u v : loopAlgebra R ℤ L) :
    constantTermPairing Φ u (degreeDerivation R L v) = residuePairing R ℤ L Φ u v := by
  let B := constantTermPairing (A := ℤ) Φ
  let D : loopAlgebra R ℤ L →ₗ[R] loopAlgebra R ℤ L := degreeDerivation R L
  suffices h : B.compl₂ D = residuePairing R ℤ L Φ by
    simpa only [B, D, LinearMap.compl₂_apply, LieDerivation.coeFn_coe] using
      LinearMap.congr_fun (LinearMap.congr_fun h u) v
  refine linearMap_ext_single_tmul fun m x ↦ linearMap_ext_single_tmul fun n y ↦ ?_
  simp only [B, D, LinearMap.compl₂_apply, LieDerivation.coeFn_coe,
    degreeDerivation_single_tmul, map_zsmul, constantTermPairing_single_tmul,
    residuePairing_single_tmul]
  split_ifs <;> simp

/-- The degree derivation is skew for the residue pairing: `Res(d(u) dv) + Res(u d(dv)) = 0`. -/
theorem residuePairing_degreeDerivation_add_eq_zero (Φ : LinearMap.BilinForm R L)
    (u v : loopAlgebra R ℤ L) :
    residuePairing R ℤ L Φ (degreeDerivation R L u) v +
      residuePairing R ℤ L Φ u (degreeDerivation R L v) = 0 := by
  rw [← constantTermPairing_degreeDerivation_right,
    ← constantTermPairing_degreeDerivation_right]
  exact constantTermPairing_degreeDerivation_add_eq_zero Φ u (degreeDerivation R L v)

end Base

/-! ### The extended affine loop algebra -/

section Extension

-- The ring of scalars is used as the one-dimensional abelian Lie algebra spanned by `d`.
attribute [local instance 100] LieRing.ofAssociativeRing

variable {R L : Type*} [CommRing R] [HasUniqueDiv R] [LieRing L] [LieAlgebra R L]
variable (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)

local notation "P" => loopAlgebra R ℤ L
local notation "c" => twoCocycleOfBilinear R ℤ L Φ hΦ hΦs
local notation "E" => ofTwoCocycle c

/-- The degree derivation is skew for the residue cocycle. -/
theorem residuePairing_degreeDerivation_add (u v : P) :
    (c : twoCochain R P (TrivialLieModule R P R)) (degreeDerivation R L u) v +
      (c : twoCochain R P (TrivialLieModule R P R)) u (degreeDerivation R L v) = 0 := by
  simp only [twoCocycleOfBilinear_coe, twoCochainOfBilinear_apply_apply, ← map_add,
    residuePairing_degreeDerivation_add_eq_zero Φ u v, map_zero]

/-- **The degree derivation on the central extension** `ĝ = ofTwoCocycle c`, acting by `t d/dt`
on loop modes and annihilating the central element `K`. -/
def extensionDegreeDerivation : LieDerivation R E E :=
  ofTwoCocycle.derivation c (degreeDerivation R L) (residuePairing_degreeDerivation_add Φ hΦ hΦs)

@[simp]
theorem extensionDegreeDerivation_ofProd (u : P) (z : TrivialLieModule R P R) :
    extensionDegreeDerivation Φ hΦ hΦs (ofProd c (u, z)) =
      ofProd c (degreeDerivation R L u, 0) :=
  ofTwoCocycle.derivation_ofProd c (degreeDerivation R L) _ u z

@[simp]
theorem extensionDegreeDerivation_centralElement :
    extensionDegreeDerivation Φ hΦ hΦs (centralElement c) = 0 :=
  ofTwoCocycle.derivation_centralElement c (degreeDerivation R L) _

local notation "δ" => extensionDegreeDerivation Φ hΦ hΦs

/-- **The extended affine loop algebra** `ĝ' = ĝ ⋊ R d`: the residue central extension of
`loopAlgebra R ℤ L` by `Φ` with the degree derivation `d = t d/dt` adjoined. -/
def extendedResidueExtension : Type _ :=
  ofTwoCocycle.derivationExtension c (degreeDerivation R L)
    (residuePairing_degreeDerivation_add Φ hΦ hΦs)

instance : LieRing (extendedResidueExtension Φ hΦ hΦs) :=
  inferInstanceAs (LieRing
    (ofTwoCocycle.derivationExtension c (degreeDerivation R L)
      (residuePairing_degreeDerivation_add Φ hΦ hΦs)))

instance : LieAlgebra R (extendedResidueExtension Φ hΦ hΦs) :=
  inferInstanceAs (LieAlgebra R
    (ofTwoCocycle.derivationExtension c (degreeDerivation R L)
      (residuePairing_degreeDerivation_add Φ hΦ hΦs)))

local notation "E'" => extendedResidueExtension Φ hΦ hΦs

/-- The inclusion of the residue central extension `ĝ` into the extended affine loop algebra. -/
def toExtendedResidueExtension : E →ₗ⁅R⁆ E' :=
  ofTwoCocycle.toDerivationExtension c (degreeDerivation R L)
    (residuePairing_degreeDerivation_add Φ hΦ hΦs)

/-- The adjoined degree element `d` of the extended affine loop algebra. -/
def degreeElement : E' :=
  ofTwoCocycle.derivationElement c (degreeDerivation R L)
    (residuePairing_degreeDerivation_add Φ hΦ hΦs)

/-- The projection from the extended affine loop algebra onto the degree coordinate `R`. -/
def degreeProj : E' →ₗ⁅R⁆ R :=
  ofTwoCocycle.derivationProj c (degreeDerivation R L)
    (residuePairing_degreeDerivation_add Φ hΦ hΦs)

/-- The degree projection vanishes on the residue central extension `ĝ`. -/
@[simp]
theorem degreeProj_toExtendedResidueExtension (x : E) :
    degreeProj Φ hΦ hΦs (toExtendedResidueExtension Φ hΦ hΦs x) = 0 :=
  ofTwoCocycle.derivationProj_toDerivationExtension c (degreeDerivation R L) _ x

/-- The degree projection sends the degree element `d` to `1`. -/
@[simp]
theorem degreeProj_degreeElement : degreeProj Φ hΦ hΦs (degreeElement Φ hΦ hΦs) = 1 :=
  ofTwoCocycle.derivationProj_derivationElement c (degreeDerivation R L) _

/-- The linear equivalence identifying `extendedResidueExtension Φ hΦ hΦs` with `ĝ × R`. -/
def extendedToProd : E' ≃ₗ[R] E × R :=
  ofTwoCocycle.derivationToProd c (degreeDerivation R L)
    (residuePairing_degreeDerivation_add Φ hΦ hΦs)

@[simp]
theorem extendedToProd_toExtendedResidueExtension (x : E) :
    extendedToProd Φ hΦ hΦs (toExtendedResidueExtension Φ hΦ hΦs x) = (x, 0) :=
  ofTwoCocycle.derivationToProd_toDerivationExtension c (degreeDerivation R L) _ x

@[simp]
theorem extendedToProd_degreeElement :
    extendedToProd Φ hΦ hΦs (degreeElement Φ hΦ hΦs) = (0, 1) :=
  ofTwoCocycle.derivationToProd_derivationElement c (degreeDerivation R L) _

/-- Reconstructing an element of `extendedResidueExtension` from `(P × R) × R` coordinates. -/
theorem extendedToProd_symm_apply (x : E) (t : R) :
    (extendedToProd Φ hΦ hΦs).symm (x, t) =
      toExtendedResidueExtension Φ hΦ hΦs x + t • degreeElement Φ hΦ hΦs :=
  ofTwoCocycle.derivationToProd_symm_apply c (degreeDerivation R L) _ x t

/-- The second coordinate under `extendedToProd` is `degreeProj`. -/
theorem snd_extendedToProd (y : E') :
    (extendedToProd Φ hΦ hΦs y).snd = degreeProj Φ hΦ hΦs y :=
  ofTwoCocycle.snd_derivationToProd c (degreeDerivation R L) _ y

/-- The inclusion of `ĝ` in the extended affine loop algebra is injective. -/
theorem toExtendedResidueExtension_injective :
    Function.Injective (toExtendedResidueExtension Φ hΦ hΦs) :=
  ofTwoCocycle.toDerivationExtension_injective c (degreeDerivation R L) _

/-- The range of `toExtendedResidueExtension` is the kernel of `degreeProj`. -/
theorem range_toExtendedResidueExtension_eq_ker_degreeProj :
    (toExtendedResidueExtension Φ hΦ hΦs).range.toSubmodule =
      (degreeProj Φ hΦ hΦs).ker.toSubmodule :=
  ofTwoCocycle.range_toDerivationExtension_eq_ker_derivationProj c (degreeDerivation R L) _

/-- Every element of `extendedResidueExtension Φ hΦ hΦs` is `x + t • d` for `x ∈ ĝ`, `t ∈ R`. -/
theorem exists_eq_add_smul_degreeElement (y : E') : ∃ (x : E) (t : R),
    y = toExtendedResidueExtension Φ hΦ hΦs x + t • degreeElement Φ hΦ hΦs :=
  ofTwoCocycle.exists_eq_add_smul_derivationElement c (degreeDerivation R L) _ y

/-- **The degree element acts by the degree derivation**: `⁅d, x⁆ = δ x` for `x ∈ ĝ`. -/
theorem lie_degreeElement_toExtendedResidueExtension (x : E) :
    ⁅degreeElement Φ hΦ hΦs, toExtendedResidueExtension Φ hΦ hΦs x⁆ =
      toExtendedResidueExtension Φ hΦ hΦs (δ x) :=
  ofTwoCocycle.lie_derivationElement_toDerivationExtension c (degreeDerivation R L) _ x

/-- **The degree element commutes with `K`.** -/
@[simp]
theorem lie_degreeElement_centralElement :
    ⁅degreeElement Φ hΦ hΦs, toExtendedResidueExtension Φ hΦ hΦs (centralElement c)⁆ = 0 :=
  ofTwoCocycle.lie_derivationElement_centralElement c (degreeDerivation R L) _

/-- **`K` is central in the extended affine loop algebra.** -/
theorem toExtendedResidueExtension_centralElement_mem_center :
    toExtendedResidueExtension Φ hΦ hΦs (centralElement c) ∈ center R E' :=
  ofTwoCocycle.toDerivationExtension_centralElement_mem_center c (degreeDerivation R L) _

/-- **The `n`-th mode map** `x ↦ tⁿ ⊗ x` from `L` into the extended affine loop algebra. -/
def mode (n : ℤ) : L →ₗ[R] E' :=
  (toExtendedResidueExtension Φ hΦ hΦs).toLinearMap ∘ₗ
    (ofProdLinearEquiv c).toLinearMap ∘ₗ LinearMap.inl R P (TrivialLieModule R P R) ∘ₗ
    TensorProduct.mk R (AddMonoidAlgebra R ℤ) L (AddMonoidAlgebra.single n 1)

theorem mode_apply (n : ℤ) (x : L) :
    mode Φ hΦ hΦs n x = toExtendedResidueExtension Φ hΦ hΦs
      (ofProd c (AddMonoidAlgebra.single n (1 : R) ⊗ₜ[R] x, 0)) := by simp [mode]

/-- Each mode map `x ↦ tⁿ ⊗ x` into `ĝ'` is injective. -/
theorem mode_injective (n : ℤ) : Function.Injective (mode Φ hΦ hΦs n) := fun x y h ↦ by
  have h' := congrArg
    (fun v ↦ toFinsupp R ℤ L ((ofProd c).symm (extendedToProd Φ hΦ hΦs v).fst).fst n) h
  simp only [mode_apply, extendedToProd_toExtendedResidueExtension, Equiv.symm_apply_apply,
    toFinsupp_single_tmul, Finsupp.single_eq_same] at h'
  exact h'

/-- The degree projection vanishes on every loop mode `tⁿ ⊗ x`. -/
@[simp]
theorem degreeProj_mode (n : ℤ) (x : L) : degreeProj Φ hΦ hΦs (mode Φ hΦ hΦs n x) = 0 := by
  rw [mode_apply, degreeProj_toExtendedResidueExtension]

/-- **The bracket of two modes** in the extended affine loop algebra:
`⁅tᵐ ⊗ x, tⁿ ⊗ y⁆ = t^{m + n} ⊗ ⁅x, y⁆ + δ_{m + n, 0} n Φ(x, y) K`. -/
theorem lie_mode_mode (m n : ℤ) (x y : L) :
    ⁅mode Φ hΦ hΦs m x, mode Φ hΦ hΦs n y⁆ = mode Φ hΦ hΦs (m + n) ⁅x, y⁆ +
      (if m + n = 0 then (n : R) * Φ x y else 0) •
        toExtendedResidueExtension Φ hΦ hΦs (centralElement c) := by
  simp only [mode_apply, ← LieHom.map_lie, bracket_ofTwoCocycle, Equiv.symm_apply_apply,
    ExtendScalars.bracket_tmul, AddMonoidAlgebra.single_mul_single, mul_one, trivial_lie_zero,
    sub_zero, twoCocycleOfBilinear_coe, twoCochain_val_apply, twoCochainOfBilinear_apply_apply,
    residuePairing_single_tmul, add_zero]
  rw [ofTwoCocycle.ofProd_eq_add_smul_centralElement, LinearEquiv.apply_symm_apply, map_add,
    map_smul]
  split_ifs <;> simp [zsmul_eq_mul]

/-- **The constant loop embedding** `x ↦ 1 ⊗ x` from `L` into `ĝ'` as a Lie homomorphism. -/
def constHom : L →ₗ⁅R⁆ E' where
  toLinearMap := mode Φ hΦ hΦs 0
  map_lie' {x y} := by
    rw [LinearMap.toFun_eq_coe, lie_mode_mode]
    simp

@[simp]
theorem constHom_apply (x : L) : constHom Φ hΦ hΦs x = mode Φ hΦ hΦs 0 x := (rfl)

/-- The constant loop embedding `L →ₗ⁅R⁆ ĝ'` is injective. -/
theorem constHom_injective : Function.Injective (constHom Φ hΦ hΦs) :=
  mode_injective Φ hΦ hΦs 0

/-- **The degree element on modes**: `⁅d, tⁿ ⊗ x⁆ = n (tⁿ ⊗ x)`. -/
@[simp]
theorem lie_degreeElement_mode (n : ℤ) (x : L) :
    ⁅degreeElement Φ hΦ hΦs, mode Φ hΦ hΦs n x⁆ = n • mode Φ hΦ hΦs n x := by
  have h := map_zsmul (ofProdLinearEquiv c) n (AddMonoidAlgebra.single n (1 : R) ⊗ₜ[R] x, 0)
  simp only [coe_ofProdLinearEquiv, Prod.smul_mk, zsmul_zero] at h
  rw [mode_apply, lie_degreeElement_toExtendedResidueExtension, extensionDegreeDerivation_ofProd,
    degreeDerivation_single_tmul, h, map_zsmul]

/-! ### The invariant symmetric bilinear form on the extended affine loop algebra -/

/-- **The invariant symmetric bilinear form** on `extendedResidueExtension Φ hΦ hΦs`: on
`((u, z), a)` and `((v, w), b)`, it equals `-constantTermPairing Φ u v + z * b + a * w`. In Kac's
convention `Φ = -κ`, this pairs `tᵐ ⊗ x` with `tⁿ ⊗ y` to `κ(x, y) δ_{m + n, 0}`, pairs `K` with
`d` to `1`, and vanishes on `(K, K)`, `(d, d)`, and cross terms between loops and `{K, d}`. -/
def extendedBilinForm : LinearMap.BilinForm R E' :=
  let loopProj : E' →ₗ[R] P := (ofTwoCocycle.proj c).toLinearMap ∘ₗ
    LinearMap.fst R E R ∘ₗ (extendedToProd Φ hΦ hΦs).toLinearMap
  let zProj : E' →ₗ[R] R := (TrivialLieModule.equiv R P R).toLinearMap ∘ₗ
    LinearMap.snd R P (TrivialLieModule R P R) ∘ₗ (ofProdLinearEquiv c).symm.toLinearMap ∘ₗ
    LinearMap.fst R E R ∘ₗ (extendedToProd Φ hΦ hΦs).toLinearMap
  let dProj : E' →ₗ[R] R := LinearMap.snd R E R ∘ₗ (extendedToProd Φ hΦ hΦs).toLinearMap
  (LinearMap.mul R R).compl₁₂ zProj dProj + (LinearMap.mul R R).compl₁₂ dProj zProj -
    (constantTermPairing Φ).compl₁₂ loopProj loopProj

/-- Coordinate formula for `extendedBilinForm Φ` in `(P × R) × R` coordinates. -/
theorem extendedBilinForm_apply (x y : E') :
    extendedBilinForm Φ hΦ hΦs x y =
      -constantTermPairing Φ ((ofProd c).symm (extendedToProd Φ hΦ hΦs x).fst).fst
          ((ofProd c).symm (extendedToProd Φ hΦ hΦs y).fst).fst +
        TrivialLieModule.equiv R P R ((ofProd c).symm (extendedToProd Φ hΦ hΦs x).fst).snd *
          (extendedToProd Φ hΦ hΦs y).snd +
        (extendedToProd Φ hΦ hΦs x).snd *
          TrivialLieModule.equiv R P R ((ofProd c).symm (extendedToProd Φ hΦ hΦs y).fst).snd := by
  simp only [extendedBilinForm, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.compl₁₂_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LieHom.coe_toLinearMap, LinearMap.fst_apply,
    LinearMap.snd_apply, coe_ofProdLinearEquiv_symm, ofTwoCocycle.proj_apply, LinearMap.mul_apply']
  ring

/-- On modes, `extendedBilinForm Φ` pairs `tᵐ ⊗ x` with `tⁿ ⊗ y` to
`-Φ(x, y) δ_{m + n, 0}`. -/
@[simp]
theorem extendedBilinForm_mode_mode (m n : ℤ) (x y : L) :
    extendedBilinForm Φ hΦ hΦs (mode Φ hΦ hΦs m x) (mode Φ hΦ hΦs n y) =
      if m + n = 0 then -Φ x y else 0 := by
  rw [extendedBilinForm_apply, mode_apply, mode_apply,
    extendedToProd_toExtendedResidueExtension, extendedToProd_toExtendedResidueExtension]
  simp only [Equiv.symm_apply_apply, map_zero, mul_zero, add_zero, constantTermPairing_single_tmul]
  split_ifs <;> simp

/-- `K` is orthogonal to every mode. -/
@[simp]
theorem extendedBilinForm_centralElement_mode (n : ℤ) (x : L) :
    extendedBilinForm Φ hΦ hΦs (toExtendedResidueExtension Φ hΦ hΦs (centralElement c))
      (mode Φ hΦ hΦs n x) = 0 := by simp [extendedBilinForm_apply, mode_apply]

/-- Every mode is orthogonal to `K`. -/
@[simp]
theorem extendedBilinForm_mode_centralElement (n : ℤ) (x : L) :
    extendedBilinForm Φ hΦ hΦs (mode Φ hΦ hΦs n x)
      (toExtendedResidueExtension Φ hΦ hΦs (centralElement c)) = 0 := by
  simp [extendedBilinForm_apply, mode_apply]

/-- `d` is orthogonal to every mode. -/
@[simp]
theorem extendedBilinForm_degreeElement_mode (n : ℤ) (x : L) :
    extendedBilinForm Φ hΦ hΦs (degreeElement Φ hΦ hΦs) (mode Φ hΦ hΦs n x) = 0 := by
  simp [extendedBilinForm_apply, mode_apply]

/-- Every mode is orthogonal to `d`. -/
@[simp]
theorem extendedBilinForm_mode_degreeElement (n : ℤ) (x : L) :
    extendedBilinForm Φ hΦ hΦs (mode Φ hΦ hΦs n x) (degreeElement Φ hΦ hΦs) = 0 := by
  simp [extendedBilinForm_apply, mode_apply]

/-- `(K, d) = 1`. -/
@[simp]
theorem extendedBilinForm_centralElement_degreeElement :
    extendedBilinForm Φ hΦ hΦs (toExtendedResidueExtension Φ hΦ hΦs (centralElement c))
      (degreeElement Φ hΦ hΦs) = 1 := by simp [extendedBilinForm_apply]

/-- `(d, K) = 1`. -/
@[simp]
theorem extendedBilinForm_degreeElement_centralElement :
    extendedBilinForm Φ hΦ hΦs (degreeElement Φ hΦ hΦs)
      (toExtendedResidueExtension Φ hΦ hΦs (centralElement c)) = 1 := by
  simp [extendedBilinForm_apply]

/-- `(K, K) = 0`. -/
@[simp]
theorem extendedBilinForm_centralElement_centralElement :
    extendedBilinForm Φ hΦ hΦs (toExtendedResidueExtension Φ hΦ hΦs (centralElement c))
      (toExtendedResidueExtension Φ hΦ hΦs (centralElement c)) = 0 := by
  simp [extendedBilinForm_apply]

/-- `(d, d) = 0`. -/
@[simp]
theorem extendedBilinForm_degreeElement_degreeElement :
    extendedBilinForm Φ hΦ hΦs (degreeElement Φ hΦ hΦs) (degreeElement Φ hΦ hΦs) = 0 := by
  simp [extendedBilinForm_apply]

/-- **`extendedBilinForm` is symmetric.** -/
theorem extendedBilinForm_isSymm : (extendedBilinForm Φ hΦ hΦs).IsSymm :=
  LinearMap.BilinForm.isSymm_def.mpr fun x y ↦ by
    rw [extendedBilinForm_apply, extendedBilinForm_apply, (constantTermPairing_isSymm hΦs).eq]
    ring

/-- The bracket in `extendedResidueExtension` read in `(P × R) × R` coordinates. -/
theorem extendedToProd_lie (x y : E') :
    let px := (ofProd c).symm (extendedToProd Φ hΦ hΦs x).fst
    let py := (ofProd c).symm (extendedToProd Φ hΦ hΦs y).fst
    let ax := (extendedToProd Φ hΦ hΦs x).snd
    let ay := (extendedToProd Φ hΦ hΦs y).snd
    extendedToProd Φ hΦ hΦs ⁅x, y⁆ =
      (ofProd c (⁅px.fst, py.fst⁆ + ax • degreeDerivation R L py.fst -
          ay • degreeDerivation R L px.fst,
        (TrivialLieModule.equiv R P R).symm (residuePairing R ℤ L Φ px.fst py.fst)), 0) := by
  dsimp only
  have hcoc (u v : P) :
      (TrivialLieModule.equiv R P R).symm (residuePairing R ℤ L Φ u v) =
        (c : twoCochain R P (TrivialLieModule R P R)) u v := by
    simp [twoCocycleOfBilinear_coe, twoCochainOfBilinear_apply_apply]
  rw [hcoc]
  -- `extendedResidueExtension` is a `def` whose `LieRing` and `Module` instances are
  -- definitionally equal to `ofTwoCocycle.derivationExtension`, and `extendedToProd` unfolds to
  -- `ofTwoCocycle.derivationToProd`.
  exact ofTwoCocycle.derivationToProd_lie_ofProd c (degreeDerivation R L)
    (residuePairing_degreeDerivation_add Φ hΦ hΦs) x y

/-- **`extendedBilinForm` is `ĝ'`-invariant**: `B(⁅x, y⁆, w) + B(y, ⁅x, w⁆) = 0`. -/
theorem extendedBilinForm_lieInvariant : (extendedBilinForm Φ hΦ hΦs).lieInvariant E' := by
  intro x y w
  rw [extendedBilinForm_apply, extendedBilinForm_apply,
    extendedToProd_lie Φ hΦ hΦs x y, extendedToProd_lie Φ hΦ hΦs x w]
  set u := ((ofProd c).symm (extendedToProd Φ hΦ hΦs x).fst).fst
  set v := ((ofProd c).symm (extendedToProd Φ hΦ hΦs y).fst).fst
  set p := ((ofProd c).symm (extendedToProd Φ hΦ hΦs w).fst).fst
  set a := (extendedToProd Φ hΦ hΦs x).snd
  set b := (extendedToProd Φ hΦ hΦs y).snd
  set q := (extendedToProd Φ hΦ hΦs w).snd
  simp only [Equiv.symm_apply_apply, LinearEquiv.apply_symm_apply, map_sub, map_add, map_smul,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, zero_mul,
    mul_zero, add_zero]
  linear_combination -(constantTermPairing_lieInvariant hΦ u v p) -
    a * (constantTermPairing_degreeDerivation_add_eq_zero Φ v p) +
    b * (constantTermPairing_degreeDerivation_add_eq_zero Φ u p) +
    q * (constantTermPairing_degreeDerivation_add_eq_zero Φ u v) -
    b * (constantTermPairing_degreeDerivation_right Φ u p) -
    q * (constantTermPairing_degreeDerivation_right Φ u v) +
    q * (constantTermPairing_isSymm hΦs).eq v (degreeDerivation R L u)

/-- **`extendedBilinForm` is nondegenerate** whenever `Φ` is nondegenerate on `L`. -/
theorem extendedBilinForm_nondegenerate (hΦn : Φ.Nondegenerate) :
    (extendedBilinForm Φ hΦ hΦs).Nondegenerate := by
  have hleft : (extendedBilinForm Φ hΦ hΦs).SeparatingLeft := fun x hx ↦
    (extendedToProd Φ hΦ hΦs).injective <| by
      have ha : (extendedToProd Φ hΦ hΦs x).snd = 0 := by
        simpa [extendedBilinForm_apply] using
          hx (toExtendedResidueExtension Φ hΦ hΦs (centralElement c))
      have hz : ((ofProd c).symm (extendedToProd Φ hΦ hΦs x).fst).snd = 0 :=
        (TrivialLieModule.equiv R P R).injective <| by
          simpa [extendedBilinForm_apply] using hx (degreeElement Φ hΦ hΦs)
      have hu : ((ofProd c).symm (extendedToProd Φ hΦ hΦs x).fst).fst = 0 :=
        constantTermPairing_separatingLeft hΦn.1 _ fun v ↦ by
          simpa [extendedBilinForm_apply] using
            hx (toExtendedResidueExtension Φ hΦ hΦs (ofProd c (v, 0)))
      rw [map_zero]
      exact Prod.ext ((ofProd c).symm.injective
        (by rw [Prod.fst_zero, of_symm_zero]; exact Prod.ext hu hz)) ha
  exact ⟨hleft, fun y hy ↦ hleft y fun x ↦ by
    rw [(extendedBilinForm_isSymm Φ hΦ hΦs).eq]; exact hy x⟩

end Extension

/-! ### Level transport along `Ψ = r • Φ` -/

section Level

-- The ring of scalars is used as the one-dimensional abelian Lie algebra spanned by `d`.
attribute [local instance 100] LieRing.ofAssociativeRing

variable {R L : Type*} [CommRing R] [HasUniqueDiv R] [LieRing L] [LieAlgebra R L]
variable {Φ Ψ : LinearMap.BilinForm R L} (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)
  (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm)

local notation "P" => loopAlgebra R ℤ L
local notation "cΦ" => twoCocycleOfBilinear R ℤ L Φ hΦ hΦs
local notation "cΨ" => twoCocycleOfBilinear R ℤ L Ψ hΨ hΨs

/-- **Level transport on extended affine loop algebras**: if `Ψ = r • Φ`, the Lie algebra
homomorphism `extendedResidueExtension Φ →ₗ⁅R⁆ extendedResidueExtension Ψ` fixing all loop
modes and `d` while sending `K ↦ r • K`. -/
def extendedLevelHom {r : R} (h : Ψ = r • Φ) :
    extendedResidueExtension Φ hΦ hΦs →ₗ⁅R⁆ extendedResidueExtension Ψ hΨ hΨs :=
  ofTwoCocycle.smulMapDerivationHom cΦ (degreeDerivation R L) _ cΨ _ r
    (twoCocycleOfBilinear_eq_smul hΦ hΦs hΨ hΨs h)

@[simp]
theorem extendedToProd_extendedLevelHom {r : R} (h : Ψ = r • Φ)
    (x : extendedResidueExtension Φ hΦ hΦs) :
    extendedToProd Ψ hΨ hΨs (extendedLevelHom hΦ hΦs hΨ hΨs h x) =
      (ofTwoCocycle.smulMap cΦ cΨ r (twoCocycleOfBilinear_eq_smul hΦ hΦs hΨ hΨs h)
          (extendedToProd Φ hΦ hΦs x).fst,
        (extendedToProd Φ hΦ hΦs x).snd) :=
  ofTwoCocycle.derivationToProd_smulMapDerivationHom cΦ (degreeDerivation R L) _ cΨ _ r _ x

/-- `extendedLevelHom` restricts to `ofTwoCocycle.smulMap` on the residue central extension. -/
@[simp]
theorem extendedLevelHom_toExtendedResidueExtension {r : R} (h : Ψ = r • Φ)
    (x : ofTwoCocycle cΦ) :
    extendedLevelHom hΦ hΦs hΨ hΨs h (toExtendedResidueExtension Φ hΦ hΦs x) =
      toExtendedResidueExtension Ψ hΨ hΨs
        (ofTwoCocycle.smulMap cΦ cΨ r (twoCocycleOfBilinear_eq_smul hΦ hΦs hΨ hΨs h) x) :=
  ofTwoCocycle.smulMapDerivationHom_toDerivationExtension cΦ (degreeDerivation R L) _ cΨ _ r _ x

/-- `extendedLevelHom` fixes every loop mode `tⁿ ⊗ x`. -/
@[simp]
theorem extendedLevelHom_mode {r : R} (h : Ψ = r • Φ) (n : ℤ) (x : L) :
    extendedLevelHom hΦ hΦs hΨ hΨs h (mode Φ hΦ hΦs n x) = mode Ψ hΨ hΨs n x := by
  simp [mode_apply]

/-- `extendedLevelHom` scales the canonical central element by `r`. -/
theorem extendedLevelHom_centralElement {r : R} (h : Ψ = r • Φ) :
    extendedLevelHom hΦ hΦs hΨ hΨs h
        (toExtendedResidueExtension Φ hΦ hΦs (centralElement cΦ)) =
      r • toExtendedResidueExtension Ψ hΨ hΨs (centralElement cΨ) :=
  ofTwoCocycle.smulMapDerivationHom_centralElement cΦ (degreeDerivation R L) _ cΨ _ r _

/-- `extendedLevelHom` preserves the degree element `d`. -/
@[simp]
theorem extendedLevelHom_degreeElement {r : R} (h : Ψ = r • Φ) :
    extendedLevelHom hΦ hΦs hΨ hΨs h (degreeElement Φ hΦ hΦs) = degreeElement Ψ hΨ hΨs :=
  ofTwoCocycle.smulMapDerivationHom_derivationElement cΦ (degreeDerivation R L) _ cΨ _ r _

/-- **Level transport scales the invariant bilinear form by `r`**: for `Ψ = r • Φ`,
`B_Ψ(f x, f y) = r * B_Φ(x, y)`. -/
theorem extendedBilinForm_extendedLevelHom {r : R} (h : Ψ = r • Φ)
    (x y : extendedResidueExtension Φ hΦ hΦs) :
    extendedBilinForm Ψ hΨ hΨs (extendedLevelHom hΦ hΦs hΨ hΨs h x)
        (extendedLevelHom hΦ hΦs hΨ hΨs h y) =
      r * extendedBilinForm Φ hΦ hΦs x y := by
  have hct : constantTermPairing (A := ℤ) Ψ = r • constantTermPairing Φ := by
    rw [h, constantTermPairing_smul]
  rw [extendedBilinForm_apply, extendedBilinForm_apply, extendedToProd_extendedLevelHom,
    extendedToProd_extendedLevelHom, ofTwoCocycle.ofProd_symm_smulMap,
    ofTwoCocycle.ofProd_symm_smulMap, hct]
  simp only [LinearMap.smul_apply, smul_eq_mul, map_smul]; ring

/-- **Level isomorphism for extended affine loop algebras**: if `Ψ = u • Φ` for a unit `u`, then
`extendedResidueExtension Φ` and `extendedResidueExtension Ψ` are isomorphic as Lie algebras via
the map fixing all loop modes and `d` and sending `K ↦ u • K`. -/
def extendedLevelEquiv {u : Rˣ} (h : Ψ = (u : R) • Φ) :
    extendedResidueExtension Φ hΦ hΦs ≃ₗ⁅R⁆ extendedResidueExtension Ψ hΨ hΨs :=
  ofTwoCocycle.smulMapDerivationEquiv cΦ (degreeDerivation R L) _ cΨ _ u
    (twoCocycleOfBilinear_eq_smul hΦ hΦs hΨ hΨs h)

@[simp]
theorem toLieHom_extendedLevelEquiv {u : Rˣ} (h : Ψ = (u : R) • Φ) :
    (extendedLevelEquiv hΦ hΦs hΨ hΨs h).toLieHom = extendedLevelHom hΦ hΦs hΨ hΨs h :=
  ofTwoCocycle.toLieHom_smulMapDerivationEquiv cΦ (degreeDerivation R L) _ cΨ _ u _

/-- `extendedLevelEquiv` acts by `ofTwoCocycle.smulMapEquiv` on the `ĝ` coordinate and fixes the
`R` coordinate. -/
@[simp]
theorem extendedToProd_extendedLevelEquiv {u : Rˣ} (h : Ψ = (u : R) • Φ)
    (x : extendedResidueExtension Φ hΦ hΦs) :
    extendedToProd Ψ hΨ hΨs (extendedLevelEquiv hΦ hΦs hΨ hΨs h x) =
      (ofTwoCocycle.smulMapEquiv cΦ cΨ u (twoCocycleOfBilinear_eq_smul hΦ hΦs hΨ hΨs h)
          (extendedToProd Φ hΦ hΦs x).fst,
        (extendedToProd Φ hΦ hΦs x).snd) :=
  ofTwoCocycle.derivationToProd_smulMapDerivationEquiv cΦ (degreeDerivation R L) _ cΨ _ u _ x

/-- The inverse of `extendedLevelEquiv` is the extended level isomorphism for `u⁻¹`. -/
theorem extendedLevelEquiv_symm {u : Rˣ} (h : Ψ = (u : R) • Φ) :
    (extendedLevelEquiv hΦ hΦs hΨ hΨs h).symm =
      extendedLevelEquiv (u := u⁻¹) hΨ hΨs hΦ hΦs (by simp [h, smul_smul]) :=
  ofTwoCocycle.smulMapDerivationEquiv_symm cΦ (degreeDerivation R L) _ cΨ _ u _

@[simp]
theorem extendedLevelEquiv_mode {u : Rˣ} (h : Ψ = (u : R) • Φ) (n : ℤ) (x : L) :
    extendedLevelEquiv hΦ hΦs hΨ hΨs h (mode Φ hΦ hΦs n x) = mode Ψ hΨ hΨs n x := by
  rw [← LieEquiv.coe_toLieHom, toLieHom_extendedLevelEquiv, extendedLevelHom_mode]

@[simp]
theorem extendedLevelEquiv_centralElement {u : Rˣ} (h : Ψ = (u : R) • Φ) :
    extendedLevelEquiv hΦ hΦs hΨ hΨs h
        (toExtendedResidueExtension Φ hΦ hΦs (centralElement cΦ)) =
      (u : R) • toExtendedResidueExtension Ψ hΨ hΨs (centralElement cΨ) :=
  ofTwoCocycle.smulMapDerivationEquiv_centralElement cΦ (degreeDerivation R L) _ cΨ _ u _

@[simp]
theorem extendedLevelEquiv_degreeElement {u : Rˣ} (h : Ψ = (u : R) • Φ) :
    extendedLevelEquiv hΦ hΦs hΨ hΨs h (degreeElement Φ hΦ hΦs) = degreeElement Ψ hΨ hΨs :=
  ofTwoCocycle.smulMapDerivationEquiv_derivationElement cΦ (degreeDerivation R L) _ cΨ _ u _

@[simp]
theorem extendedLevelEquiv_symm_mode {u : Rˣ} (h : Ψ = (u : R) • Φ) (n : ℤ) (x : L) :
    (extendedLevelEquiv hΦ hΦs hΨ hΨs h).symm (mode Ψ hΨ hΨs n x) = mode Φ hΦ hΦs n x := by
  rw [extendedLevelEquiv_symm, extendedLevelEquiv_mode]

@[simp]
theorem extendedLevelEquiv_symm_centralElement {u : Rˣ} (h : Ψ = (u : R) • Φ) :
    (extendedLevelEquiv hΦ hΦs hΨ hΨs h).symm
        (toExtendedResidueExtension Ψ hΨ hΨs (centralElement cΨ)) =
      (↑u⁻¹ : R) • toExtendedResidueExtension Φ hΦ hΦs (centralElement cΦ) :=
  ofTwoCocycle.smulMapDerivationEquiv_symm_centralElement cΦ (degreeDerivation R L) _ cΨ _ u _

@[simp]
theorem extendedLevelEquiv_symm_degreeElement {u : Rˣ} (h : Ψ = (u : R) • Φ) :
    (extendedLevelEquiv hΦ hΦs hΨ hΨs h).symm (degreeElement Ψ hΨ hΨs) =
      degreeElement Φ hΦ hΦs :=
  ofTwoCocycle.smulMapDerivationEquiv_symm_derivationElement cΦ (degreeDerivation R L) _ cΨ _ u _

/-- Under `extendedLevelEquiv`, `extendedBilinForm Ψ` pulls back to `u * extendedBilinForm Φ`. -/
theorem extendedBilinForm_extendedLevelEquiv {u : Rˣ} (h : Ψ = (u : R) • Φ)
    (x y : extendedResidueExtension Φ hΦ hΦs) :
    extendedBilinForm Ψ hΨ hΨs (extendedLevelEquiv hΦ hΦs hΨ hΨs h x)
        (extendedLevelEquiv hΦ hΦs hΨ hΨs h y) =
      (u : R) * extendedBilinForm Φ hΦ hΦs x y := by
  rw [← LieEquiv.coe_toLieHom, toLieHom_extendedLevelEquiv, extendedBilinForm_extendedLevelHom]

end Level

end TauCeti.LieAlgebra.LoopAlgebra
