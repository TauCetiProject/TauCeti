/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Loop
public import TauCeti.Algebra.Lie.Extension.Basic
public import TauCeti.Algebra.Lie.SemiDirect.Basic
-- Proof-only: mode formulas and bilinear-rescaling lemma for the residue pairing.
import TauCeti.Algebra.Lie.Loop.Cocycle

/-!
# The extended affine loop algebra and its invariant bilinear form

Let `L` be a Lie algebra over a commutative ring `R`, and let `loopAlgebra R ℤ L = R[t, t⁻¹] ⊗ L`
be its polynomial loop algebra with modes `x_n = tⁿ ⊗ x`. The **degree derivation**
`d = t d/dt` (`TauCeti.LieAlgebra.LoopAlgebra.degreeDerivation`) acts on modes by
`d(x_n) = n x_n`.

For an invariant symmetric bilinear form `Φ` on `L` (over an additively torsion-free ring `R`),
Mathlib constructs the residue 2-cocycle `c = twoCocycleOfBilinear R ℤ L Φ hΦ hΦs`, with values
`c(x_m, y_n) = n Φ(x, y) δ_{m + n, 0}`, and its central extension `ĝ = ofTwoCocycle c`, with
central element `K = (0, 1)`. Since `d` is skew for the residue pairing, it lifts to a derivation
`extensionDegreeDerivation` of `ĝ` killing `K`. Adjoining `d` as a semidirect sum produces the
**extended affine loop algebra**

`ĝ' = extendedResidueExtension Φ hΦ hΦs = ĝ ⋊ R d`,

in which `⁅d, x_n⁆ = n x_n`, `⁅d, K⁆ = 0`, and `K` remains central.

The constant-term pairing `constantTermPairing Φ` on `loopAlgebra R ℤ L` pairs `x_m` with `y_n`
to `Φ(x, y) δ_{m + n, 0}`, and satisfies `(u, d v)_0 = Res(u dv)`. Combining its negation with the
hyperbolic pairing between `K` and `d` gives the symmetric invariant bilinear form
`extendedBilinForm Φ hΦ hΦs` on `ĝ'`:

* `(x_m, y_n) = -Φ(x, y) δ_{m + n, 0}` (equivalently `+κ(x, y) δ_{m + n, 0}` in Kac's affine
  convention `Φ = -κ`),
* `(K, d) = (d, K) = 1`, `(K, K) = (d, d) = 0`, and `K, d` are orthogonal to all loop modes.

When `Φ` is nondegenerate on `L`, `extendedBilinForm` is nondegenerate on `ĝ'`.

Rescaling the form `Ψ = r • Φ` induces the Lie algebra homomorphisms `levelHom` on `ĝ` and
`extendedLevelHom` on `ĝ'` fixing all loop modes and `d` while sending `K ↦ r • K`, scaling
`extendedBilinForm` by `r`. When `r` is a unit, these are Lie algebra isomorphisms (`levelEquiv`,
`extendedLevelEquiv`).

## Main definitions

* `TauCeti.LieAlgebra.LoopAlgebra.degreeDerivationOf`: the graded degree derivation on
  `loopAlgebra R A L` associated with an additive homomorphism `χ : A →+ R`.
* `TauCeti.LieAlgebra.LoopAlgebra.degreeDerivation`: the degree derivation `t d/dt` on
  `loopAlgebra R ℤ L`.
* `TauCeti.LieAlgebra.LoopAlgebra.constantTermPairing`: the constant-term bilinear form
  `(x_m, y_n) ↦ Φ(x, y) δ_{m + n, 0}` on `loopAlgebra R A L` for any additive group `A`.
* `TauCeti.LieAlgebra.LoopAlgebra.extensionDegreeDerivation`: the lift of `degreeDerivation` to
  `ofTwoCocycle c`.
* `TauCeti.LieAlgebra.LoopAlgebra.extendedResidueExtension`: the extended affine loop algebra
  `ĝ ⋊ R d`.
* `TauCeti.LieAlgebra.LoopAlgebra.toExtendedResidueExtension`,
  `TauCeti.LieAlgebra.LoopAlgebra.degreeElement`,
  `TauCeti.LieAlgebra.LoopAlgebra.mode`, and `TauCeti.LieAlgebra.LoopAlgebra.constHom`:
  the inclusion of `ĝ`, the degree element `d`, the mode maps `x ↦ tⁿ ⊗ x`, and the constant
  subalgebra embedding `L →ₗ⁅R⁆ ĝ'`.
* `TauCeti.LieAlgebra.LoopAlgebra.extendedBilinForm`: the invariant symmetric bilinear form on `ĝ'`.
* `TauCeti.LieAlgebra.LoopAlgebra.levelHom`, `TauCeti.LieAlgebra.LoopAlgebra.levelEquiv`,
  `TauCeti.LieAlgebra.LoopAlgebra.extendedLevelHom`, and
  `TauCeti.LieAlgebra.LoopAlgebra.extendedLevelEquiv`: level transport along `Ψ = r • Φ`.

## Main results

* `TauCeti.LieAlgebra.LoopAlgebra.lie_mode_mode`,
  `TauCeti.LieAlgebra.LoopAlgebra.lie_degreeElement_mode`, and
  `TauCeti.LieAlgebra.LoopAlgebra.toExtendedResidueExtension_centralElement_mem_center`: the
  defining bracket relations of the extended affine loop algebra.
* `TauCeti.LieAlgebra.LoopAlgebra.mode_injective` and
  `TauCeti.LieAlgebra.LoopAlgebra.constHom_injective`: injectivity of modes and constant loops.
* `TauCeti.LieAlgebra.LoopAlgebra.extendedBilinForm_isSymm`,
  `TauCeti.LieAlgebra.LoopAlgebra.extendedBilinForm_lieInvariant`, and
  `TauCeti.LieAlgebra.LoopAlgebra.extendedBilinForm_nondegenerate`: `extendedBilinForm` is
  symmetric, invariant, and nondegenerate whenever `Φ` is.
* `TauCeti.LieAlgebra.LoopAlgebra.extendedBilinForm_extendedLevelHom`,
  `TauCeti.LieAlgebra.LoopAlgebra.extendedBilinForm_extendedLevelEquiv`,
  `TauCeti.LieAlgebra.LoopAlgebra.levelEquiv_symm`, and
  `TauCeti.LieAlgebra.LoopAlgebra.extendedLevelEquiv_symm`: level transport scales the invariant
  form by `r` and inverts via the reciprocal unit.

## References

* V. G. Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., §7.2–7.4, for the polynomial loop
  algebra central extension, the degree derivation `d = t d/dt`, and the invariant bilinear form.
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

/-- Linear induction on `loopAlgebra R A L` reduced to `0`, `+`, and pure modes `tᵃ ⊗ x`. -/
private theorem loopAlgebra_induction_linear {A : Type*}
    (P : loopAlgebra R A L → Prop)
    (zero : P 0) (add : ∀ u v, P u → P v → P (u + v))
    (single : ∀ (a : A) (x : L), P (AddMonoidAlgebra.single a (1 : R) ⊗ₜ[R] x))
    (u : loopAlgebra R A L) : P u := by
  obtain ⟨f, rfl⟩ := (toFinsupp R A L).symm.surjective u
  induction f using Finsupp.induction_linear with
  | zero => simpa using zero
  | add f₁ f₂ h₁ h₂ =>
    rw [map_add]
    exact add _ _ h₁ h₂
  | single a x =>
    rw [toFinsupp_symm_single]
    exact single a x

open DirectSum in
/-- Every pure mode `tᵃ ⊗ x` lies in the `a`-th graded piece of `loopAlgebra R A L`. -/
private theorem single_tmul_mem_decomposeTensor {A : Type*} (a : A) (x : L) :
    (AddMonoidAlgebra.single a (1 : R) ⊗ₜ[R] x : loopAlgebra R A L) ∈
      decomposeTensor (AddMonoidAlgebra.grade R) L a := by
  rw [decomposeTensor_apply]
  exact ⟨⟨AddMonoidAlgebra.single a 1, AddMonoidAlgebra.single_mem_grade a 1⟩ ⊗ₜ[R] x, by simp⟩

variable (R L) in
/-- **The generalized degree derivation** on `loopAlgebra R A L` associated with an additive
homomorphism `χ : A →+ R`, acting on modes by `D_χ (tᵃ ⊗ x) = χ a • (tᵃ ⊗ x)`. -/
def degreeDerivationOf {A : Type*} [AddCommMonoid A] [DecidableEq A] (χ : A →+ R) :
    LieDerivation R (loopAlgebra R A L) (loopAlgebra R A L) :=
  LieDerivation.ofGrading
    (fun a : A ↦ DirectSum.decomposeTensor (AddMonoidAlgebra.grade R) L a) χ

/-- On modes, `degreeDerivationOf R L χ` scales `tᵃ ⊗ x` by `χ a`. -/
theorem degreeDerivationOf_single_tmul {A : Type*} [AddCommMonoid A] [DecidableEq A]
    (χ : A →+ R) (a : A) (x : L) :
    degreeDerivationOf R L χ (AddMonoidAlgebra.single a (1 : R) ⊗ₜ[R] x) =
      χ a • (AddMonoidAlgebra.single a (1 : R) ⊗ₜ[R] x) :=
  LieDerivation.ofGrading_apply_apply _ χ (single_tmul_mem_decomposeTensor a x)

/-- `degreeDerivationOf R L χ` vanishes on constant loops `1 ⊗ x`. -/
@[simp]
theorem degreeDerivationOf_one_tmul {A : Type*} [AddCommMonoid A] [DecidableEq A]
    (χ : A →+ R) (x : L) :
    degreeDerivationOf R L χ (1 ⊗ₜ[R] x) = 0 := by
  rw [AddMonoidAlgebra.one_def, degreeDerivationOf_single_tmul, map_zero, zero_smul]

variable (R L) in
/-- **The degree derivation `d = t d/dt`** on the polynomial loop algebra `loopAlgebra R ℤ L`,
acting on modes by `d (tⁿ ⊗ x) = n (tⁿ ⊗ x)`. -/
def degreeDerivation : LieDerivation R (loopAlgebra R ℤ L) (loopAlgebra R ℤ L) :=
  degreeDerivationOf R L (Int.castAddHom R)

/-- On modes, the degree derivation multiplies `tⁿ ⊗ x` by `n`. -/
theorem degreeDerivation_single_tmul (n : ℤ) (x : L) :
    degreeDerivation R L (AddMonoidAlgebra.single n (1 : R) ⊗ₜ[R] x) =
      n • (AddMonoidAlgebra.single n (1 : R) ⊗ₜ[R] x) := by
  rw [degreeDerivation, degreeDerivationOf_single_tmul]
  exact Int.cast_smul_eq_zsmul R n (AddMonoidAlgebra.single n (1 : R) ⊗ₜ[R] x)

/-- The degree derivation vanishes on constant loops `1 ⊗ x`. -/
@[simp]
theorem degreeDerivation_one_tmul (x : L) :
    degreeDerivation R L (1 ⊗ₜ[R] x) = 0 :=
  degreeDerivationOf_one_tmul (Int.castAddHom R) x

/-- **The constant-term pairing** on `loopAlgebra R A L` induced by a bilinear form `Φ` on `L`:
it pairs `tᵐ ⊗ x` with `tⁿ ⊗ y` to `Φ(x, y)` if `m + n = 0` and `0` otherwise. -/
def constantTermPairing {A : Type*} [AddCommGroup A] [DecidableEq A]
    (Φ : LinearMap.BilinForm R L) :
    LinearMap.BilinForm R (loopAlgebra R A L) :=
  LinearMap.mk₂ R
    (fun u v ↦ (toFinsupp R A L u).sum fun m x ↦ Φ x (toFinsupp R A L v (-m)))
    (fun u₁ u₂ v ↦ by
      rw [map_add, Finsupp.sum_add_index (by simp) (fun _ _ _ _ ↦ by simp)])
    (fun r u v ↦ by
      rw [map_smul, Finsupp.sum_smul_index' (by simp), Finsupp.smul_sum]
      exact Finset.sum_congr rfl fun m _ ↦ by simp)
    (fun u v₁ v₂ ↦ by simp only [map_add, Finsupp.add_apply, Finsupp.sum_add])
    (fun r u v ↦ by simp only [map_smul, Finsupp.smul_apply, Finsupp.smul_sum])

/-- On modes, `constantTermPairing Φ` pairs `tᵐ ⊗ x` with `tⁿ ⊗ y` to `Φ(x, y) δ_{m + n, 0}`. -/
theorem constantTermPairing_single_tmul {A : Type*} [AddCommGroup A] [DecidableEq A]
    (Φ : LinearMap.BilinForm R L) (m n : A) (x y : L) :
    constantTermPairing Φ (AddMonoidAlgebra.single m (1 : R) ⊗ₜ[R] x)
        (AddMonoidAlgebra.single n (1 : R) ⊗ₜ[R] y) =
      if m + n = 0 then Φ x y else 0 := by
  rw [constantTermPairing, LinearMap.mk₂_apply, toFinsupp_single_tmul, toFinsupp_single_tmul,
    Finsupp.sum_single_index (by simp)]
  split_ifs with h
  · rw [eq_neg_of_add_eq_zero_right h, Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne (fun h' ↦ h (by rw [← h', add_neg_cancel])), map_zero]

/-- Rescaling `Φ` rescales `constantTermPairing Φ`. -/
@[simp]
theorem constantTermPairing_smul {A : Type*} [AddCommGroup A] [DecidableEq A]
    (r : R) (Φ : LinearMap.BilinForm R L) :
    constantTermPairing (A := A) (r • Φ) = r • constantTermPairing (A := A) Φ := by
  refine LinearMap.ext₂ fun u v ↦ ?_
  simp only [constantTermPairing, LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul,
    Finsupp.mul_sum]

/-- If `Φ` is symmetric, then `constantTermPairing Φ` is symmetric. -/
theorem constantTermPairing_isSymm {A : Type*} [AddCommGroup A] [DecidableEq A]
    {Φ : LinearMap.BilinForm R L} (hΦs : Φ.IsSymm) :
    (constantTermPairing (A := A) Φ).IsSymm := by
  refine LinearMap.BilinForm.isSymm_def.mpr fun u v ↦ ?_
  refine loopAlgebra_induction_linear
    (fun u ↦ constantTermPairing Φ u v = constantTermPairing Φ v u)
    (by simp) (fun _ _ h₁ h₂ ↦ by simp [h₁, h₂]) (fun m x ↦ ?_) u
  refine loopAlgebra_induction_linear
    (fun v ↦ constantTermPairing Φ (AddMonoidAlgebra.single m 1 ⊗ₜ[R] x) v =
      constantTermPairing Φ v (AddMonoidAlgebra.single m 1 ⊗ₜ[R] x))
    (by simp) (fun _ _ h₁ h₂ ↦ by simp [h₁, h₂]) (fun n y ↦ ?_) v
  simp only [constantTermPairing_single_tmul, add_comm m n, hΦs.eq x y]

/-- If `Φ` is invariant on `L`, then `constantTermPairing Φ` is invariant on
`loopAlgebra R A L`. -/
theorem constantTermPairing_lieInvariant {A : Type*} [AddCommGroup A] [DecidableEq A]
    {Φ : LinearMap.BilinForm R L} (hΦ : Φ.lieInvariant L) :
    (constantTermPairing (A := A) Φ).lieInvariant (loopAlgebra R A L) := by
  have hzl := @zero_lie (loopAlgebra R A L) (loopAlgebra R A L) _ _
  have hlz := @lie_zero (loopAlgebra R A L) (loopAlgebra R A L) _ _
  have hal := @add_lie (loopAlgebra R A L) (loopAlgebra R A L) _ _
  have hla := @lie_add (loopAlgebra R A L) (loopAlgebra R A L) _ _
  intro u v w
  refine loopAlgebra_induction_linear
    (fun u ↦ constantTermPairing Φ ⁅u, v⁆ w = -constantTermPairing Φ v ⁅u, w⁆)
    (by simp only [hzl, map_zero, LinearMap.zero_apply, neg_zero])
    (fun _ _ h₁ h₂ ↦ by
      simp only [hal, map_add, LinearMap.add_apply]; linear_combination h₁ + h₂)
    (fun k x ↦ ?_) u
  refine loopAlgebra_induction_linear
    (fun v ↦ constantTermPairing Φ ⁅AddMonoidAlgebra.single k 1 ⊗ₜ[R] x, v⁆ w =
      -constantTermPairing Φ v ⁅AddMonoidAlgebra.single k 1 ⊗ₜ[R] x, w⁆)
    (by simp only [hlz, map_zero, LinearMap.zero_apply, neg_zero])
    (fun _ _ h₁ h₂ ↦ by
      simp only [hla, map_add, LinearMap.add_apply]; linear_combination h₁ + h₂)
    (fun m y ↦ ?_) v
  refine loopAlgebra_induction_linear
    (fun w ↦ constantTermPairing Φ ⁅AddMonoidAlgebra.single k 1 ⊗ₜ[R] x,
        AddMonoidAlgebra.single m 1 ⊗ₜ[R] y⁆ w =
      -constantTermPairing Φ (AddMonoidAlgebra.single m 1 ⊗ₜ[R] y)
        ⁅AddMonoidAlgebra.single k 1 ⊗ₜ[R] x, w⁆)
    (by simp only [hlz, map_zero, neg_zero])
    (fun _ _ h₁ h₂ ↦ by simp only [hla, map_add]; linear_combination h₁ + h₂)
    (fun n z ↦ ?_) w
  simp only [ExtendScalars.bracket_tmul, AddMonoidAlgebra.single_mul_single, mul_one,
    constantTermPairing_single_tmul]
  have hiff : m + (k + n) = 0 ↔ k + m + n = 0 := by rw [add_left_comm, add_assoc]
  simp only [hiff]
  split_ifs <;> simp [hΦ x y z]

/-- If `Φ` is left-separating on `L`, then `constantTermPairing Φ` is left-separating on
`loopAlgebra R A L`. -/
theorem constantTermPairing_separatingLeft {A : Type*} [AddCommGroup A] [DecidableEq A]
    {Φ : LinearMap.BilinForm R L} (hΦ : Φ.SeparatingLeft) :
    (constantTermPairing (A := A) Φ).SeparatingLeft := by
  intro u hu
  apply (toFinsupp R A L).injective; ext m; rw [map_zero, Finsupp.zero_apply]
  refine hΦ _ fun y ↦ ?_
  have h := hu (AddMonoidAlgebra.single (-m) (1 : R) ⊗ₜ[R] y)
  rw [constantTermPairing, LinearMap.mk₂_apply, toFinsupp_single_tmul, Finsupp.sum_eq_single m
    (fun k _ hkm ↦ by rw [Finsupp.single_eq_of_ne (fun hk ↦ hkm (neg_inj.mp hk)), map_zero])
    (by simp)] at h
  simpa using h

/-- The generalized degree derivation is skew for `constantTermPairing Φ`:
`(D_χ u, v)_0 + (u, D_χ v)_0 = 0`. -/
theorem constantTermPairing_degreeDerivationOf_add_eq_zero {A : Type*} [AddCommGroup A]
    [DecidableEq A] (χ : A →+ R) (Φ : LinearMap.BilinForm R L) (u v : loopAlgebra R A L) :
    constantTermPairing Φ (degreeDerivationOf R L χ u) v +
      constantTermPairing Φ u (degreeDerivationOf R L χ v) = 0 := by
  refine loopAlgebra_induction_linear
    (fun u ↦ constantTermPairing Φ (degreeDerivationOf R L χ u) v +
      constantTermPairing Φ u (degreeDerivationOf R L χ v) = 0)
    (by simp)
    (fun _ _ h₁ h₂ ↦ by simp only [map_add, LinearMap.add_apply]; linear_combination h₁ + h₂)
    (fun m x ↦ ?_) u
  refine loopAlgebra_induction_linear
    (fun v ↦ constantTermPairing Φ
        (degreeDerivationOf R L χ (AddMonoidAlgebra.single m 1 ⊗ₜ[R] x)) v +
      constantTermPairing Φ (AddMonoidAlgebra.single m 1 ⊗ₜ[R] x)
        (degreeDerivationOf R L χ v) = 0)
    (by simp)
    (fun _ _ h₁ h₂ ↦ by simp only [map_add]; linear_combination h₁ + h₂)
    (fun n y ↦ ?_) v
  simp only [degreeDerivationOf_single_tmul, map_smul, LinearMap.smul_apply,
    constantTermPairing_single_tmul, smul_eq_mul]
  split_ifs with h
  · rw [← add_mul, ← map_add, h, map_zero, zero_mul]
  · simp

/-- The degree derivation is skew for `constantTermPairing Φ`:
`(d u, v)_0 + (u, d v)_0 = 0`. -/
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
  refine loopAlgebra_induction_linear
    (fun u ↦ constantTermPairing Φ u (degreeDerivation R L v) = residuePairing R ℤ L Φ u v)
    (by simp)
    (fun _ _ h₁ h₂ ↦ by simp only [map_add, LinearMap.add_apply]; rw [h₁, h₂])
    (fun m x ↦ ?_) u
  refine loopAlgebra_induction_linear
    (fun v ↦ constantTermPairing Φ (AddMonoidAlgebra.single m 1 ⊗ₜ[R] x) (degreeDerivation R L v) =
      residuePairing R ℤ L Φ (AddMonoidAlgebra.single m 1 ⊗ₜ[R] x) v)
    (by simp) (fun _ _ h₁ h₂ ↦ by simp only [map_add]; rw [h₁, h₂]) (fun n y ↦ ?_) v
  simp only [degreeDerivation_single_tmul, map_zsmul, constantTermPairing_single_tmul,
    residuePairing_single_tmul]
  split_ifs <;> simp

/-- The degree derivation is skew for the residue pairing of every bilinear form on `L`:
`Res(d(u) dv) + Res(u d(dv)) = 0`. -/
theorem residuePairing_degreeDerivation_add_eq_zero (Φ : LinearMap.BilinForm R L)
    (u v : loopAlgebra R ℤ L) :
    residuePairing R ℤ L Φ (degreeDerivation R L u) v +
      residuePairing R ℤ L Φ u (degreeDerivation R L v) = 0 := by
  rw [← constantTermPairing_degreeDerivation_right, ← constantTermPairing_degreeDerivation_right]
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

/-- **The degree derivation on the central extension** `ĝ = ofTwoCocycle c`, acting by `t d/dt`
on loop modes and annihilating the central element `K`. -/
def extensionDegreeDerivation : LieDerivation R E E :=
  ofTwoCocycle.derivation c (degreeDerivation R L) fun u v ↦ by
    simp only [twoCocycleOfBilinear_coe, twoCochainOfBilinear_apply_apply, ← map_add,
      residuePairing_degreeDerivation_add_eq_zero Φ u v, map_zero]

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
local notation "ψ" => LieDerivation.lineHom (extensionDegreeDerivation Φ hΦ hΦs)

/-- **The extended affine loop algebra** `ĝ' = ĝ ⋊ R d`: the residue central extension of
`loopAlgebra R ℤ L` by `Φ` with the degree derivation `d = t d/dt` adjoined. -/
def extendedResidueExtension : Type _ :=
  E ⋊⁅LieDerivation.lineHom (extensionDegreeDerivation Φ hΦ hΦs)⁆ R

instance : LieRing (extendedResidueExtension Φ hΦ hΦs) :=
  inferInstanceAs (LieRing (E ⋊⁅ψ⁆ R))

instance : LieAlgebra R (extendedResidueExtension Φ hΦ hΦs) :=
  inferInstanceAs (LieAlgebra R (E ⋊⁅ψ⁆ R))

local notation "E'" => extendedResidueExtension Φ hΦ hΦs

/-- The inclusion of the residue central extension `ĝ` into the extended affine loop algebra. -/
def toExtendedResidueExtension : E →ₗ⁅R⁆ E' :=
  inl ψ

/-- The adjoined degree element `d` of the extended affine loop algebra. -/
def degreeElement : E' :=
  inr ψ (1 : R)

/-- The projection from the extended affine loop algebra onto the degree coordinate `R`. -/
def degreeProj : E' →ₗ⁅R⁆ R :=
  projr ψ

/-- The degree projection vanishes on the residue central extension `ĝ`. -/
@[simp]
theorem degreeProj_toExtendedResidueExtension (x : E) :
    degreeProj Φ hΦ hΦs (toExtendedResidueExtension Φ hΦ hΦs x) = 0 :=
  projr_inl_apply ψ

/-- The degree projection sends the degree element `d` to `1`. -/
@[simp]
theorem degreeProj_degreeElement :
    degreeProj Φ hΦ hΦs (degreeElement Φ hΦ hΦs) = 1 :=
  projr_inr_apply ψ

/-- The linear equivalence identifying `extendedResidueExtension Φ hΦ hΦs` with `ĝ × R`. -/
def extendedToProd : E' ≃ₗ[R] E × R :=
  toProdl ψ

@[simp]
theorem extendedToProd_toExtendedResidueExtension (x : E) :
    extendedToProd Φ hΦ hΦs (toExtendedResidueExtension Φ hΦ hΦs x) = (x, 0) :=
  (rfl)

@[simp]
theorem extendedToProd_degreeElement :
    extendedToProd Φ hΦ hΦs (degreeElement Φ hΦ hΦs) = (0, 1) :=
  (rfl)

/-- The inclusion of `ĝ` in the extended affine loop algebra is injective. -/
theorem toExtendedResidueExtension_injective :
    Function.Injective (toExtendedResidueExtension Φ hΦ hΦs) :=
  inl_injective ψ

/-- The range of `toExtendedResidueExtension` is the kernel of `degreeProj`. -/
theorem range_toExtendedResidueExtension_eq_ker_degreeProj :
    (toExtendedResidueExtension Φ hΦ hΦs).range.toSubmodule =
      (degreeProj Φ hΦ hΦs).ker.toSubmodule := by
  ext x
  exact SetLike.ext_iff.mp (IsExtension.exact (i := inl ψ) (p := projr ψ)) x

/-- Every element of `extendedResidueExtension Φ hΦ hΦs` is `x + t • d` for some `x ∈ ĝ` and
`t ∈ R`. -/
theorem exists_eq_add_smul_degreeElement (y : E') :
    ∃ (x : E) (t : R), y = toExtendedResidueExtension Φ hΦ hΦs x + t • degreeElement Φ hΦ hΦs :=
  LieDerivation.exists_eq_add_smul_inr_one δ y

/-- **The degree element acts by the degree derivation**: `⁅d, x⁆ = δ x` for `x ∈ ĝ`. -/
theorem lie_degreeElement_toExtendedResidueExtension (x : E) :
    ⁅degreeElement Φ hΦ hΦs, toExtendedResidueExtension Φ hΦ hΦs x⁆ =
      toExtendedResidueExtension Φ hΦ hΦs (δ x) :=
  LieDerivation.lie_inr_lineHom_one_inl δ x

/-- **The degree element commutes with `K`.** -/
@[simp]
theorem lie_degreeElement_centralElement :
    ⁅degreeElement Φ hΦ hΦs,
      toExtendedResidueExtension Φ hΦ hΦs (centralElement c)⁆ = 0 :=
  LieDerivation.lie_inr_lineHom_one_inl_eq_zero δ
    (extensionDegreeDerivation_centralElement Φ hΦ hΦs)

/-- **`K` is central in the extended affine loop algebra.** -/
theorem toExtendedResidueExtension_centralElement_mem_center :
    toExtendedResidueExtension Φ hΦ hΦs (centralElement c) ∈ center R E' :=
  LieDerivation.inl_lineHom_mem_center δ (centralElement_mem_center c)
    (extensionDegreeDerivation_centralElement Φ hΦ hΦs)

/-- **The `n`-th mode map** `x ↦ tⁿ ⊗ x` from `L` into the extended affine loop algebra. -/
def mode (n : ℤ) : L →ₗ[R] E' :=
  (toExtendedResidueExtension Φ hΦ hΦs).toLinearMap ∘ₗ
    (ofProdLinearEquiv c).toLinearMap ∘ₗ
    LinearMap.inl R P (TrivialLieModule R P R) ∘ₗ
    TensorProduct.mk R (AddMonoidAlgebra R ℤ) L (AddMonoidAlgebra.single n 1)

theorem mode_apply (n : ℤ) (x : L) :
    mode Φ hΦ hΦs n x =
      toExtendedResidueExtension Φ hΦ hΦs
        (ofProd c (AddMonoidAlgebra.single n (1 : R) ⊗ₜ[R] x, 0)) := by
  simp [mode]

/-- Each mode map `x ↦ tⁿ ⊗ x` into `ĝ'` is injective. -/
theorem mode_injective (n : ℤ) : Function.Injective (mode Φ hΦ hΦs n) := by
  intro x y h
  have h' := congrArg
    (fun v ↦ toFinsupp R ℤ L ((ofProd c).symm (extendedToProd Φ hΦ hΦs v).fst).fst n) h
  rw [mode_apply, mode_apply, extendedToProd_toExtendedResidueExtension,
    extendedToProd_toExtendedResidueExtension, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    toFinsupp_single_tmul, toFinsupp_single_tmul, Finsupp.single_eq_same,
    Finsupp.single_eq_same] at h'
  exact h'

/-- The degree projection vanishes on every loop mode `tⁿ ⊗ x`. -/
@[simp]
theorem degreeProj_mode (n : ℤ) (x : L) :
    degreeProj Φ hΦ hΦs (mode Φ hΦ hΦs n x) = 0 := by
  rw [mode_apply, degreeProj_toExtendedResidueExtension]

/-- **The bracket of two modes** in the extended affine loop algebra:
`⁅tᵐ ⊗ x, tⁿ ⊗ y⁆ = t^{m + n} ⊗ ⁅x, y⁆ + δ_{m + n, 0} n Φ(x, y) K`. -/
theorem lie_mode_mode (m n : ℤ) (x y : L) :
    ⁅mode Φ hΦ hΦs m x, mode Φ hΦ hΦs n y⁆ =
      mode Φ hΦ hΦs (m + n) ⁅x, y⁆ +
        (if m + n = 0 then (n : R) * Φ x y else 0) •
          toExtendedResidueExtension Φ hΦ hΦs (centralElement c) := by
  simp only [mode_apply, ← LieHom.map_lie, bracket_ofTwoCocycle, Equiv.symm_apply_apply,
    ExtendScalars.bracket_tmul, AddMonoidAlgebra.single_mul_single, mul_one, trivial_lie_zero,
    sub_zero, twoCocycleOfBilinear_coe, twoCochain_val_apply, twoCochainOfBilinear_apply_apply,
    residuePairing_single_tmul, add_zero]
  rw [ofTwoCocycle.ofProd_eq_add_smul_centralElement, LinearEquiv.apply_symm_apply, map_add,
    map_smul]
  split_ifs <;> simp [zsmul_eq_mul]

/-- **The constant loop embedding** `x ↦ 1 ⊗ x` from `L` into the extended affine loop algebra,
as a Lie algebra homomorphism. -/
def constHom : L →ₗ⁅R⁆ E' where
  toLinearMap := mode Φ hΦ hΦs 0
  map_lie' {x y} := by simp [lie_mode_mode]

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

/-- **The invariant symmetric bilinear form** on `extendedResidueExtension Φ hΦ hΦs`:
on `((u, z), a)` and `((v, w), b)`, it takes the value `-constantTermPairing Φ u v + z * b + a * w`.
In Kac's affine convention `Φ = -κ`, this pairs `tᵐ ⊗ x` with `tⁿ ⊗ y` to `κ(x, y) δ_{m + n, 0}`,
pairs `K` with `d` to `1`, and vanishes on `(K, K)`, `(d, d)`, and cross terms between loops and
`{K, d}`. -/
def extendedBilinForm : LinearMap.BilinForm R E' :=
  let loopProj : E' →ₗ[R] P :=
    (ofTwoCocycle.proj c).toLinearMap ∘ₗ LinearMap.fst R E R ∘ₗ
      (extendedToProd Φ hΦ hΦs).toLinearMap
  let zProj : E' →ₗ[R] R :=
    (TrivialLieModule.equiv R P R).toLinearMap ∘ₗ
      LinearMap.snd R P (TrivialLieModule R P R) ∘ₗ
      (ofProdLinearEquiv c).symm.toLinearMap ∘ₗ
      LinearMap.fst R E R ∘ₗ (extendedToProd Φ hΦ hΦs).toLinearMap
  let dProj : E' →ₗ[R] R := LinearMap.snd R E R ∘ₗ (extendedToProd Φ hΦ hΦs).toLinearMap
  (LinearMap.mul R R).compl₁₂ zProj dProj +
    (LinearMap.mul R R).compl₁₂ dProj zProj -
    (constantTermPairing Φ).compl₁₂ loopProj loopProj

/-- Coordinate formula for `extendedBilinForm Φ` in `(P × R) × R` coordinates. -/
theorem extendedBilinForm_apply (x y : E') :
    extendedBilinForm Φ hΦ hΦs x y =
      -constantTermPairing Φ
          ((ofProd c).symm (extendedToProd Φ hΦ hΦs x).fst).fst
          ((ofProd c).symm (extendedToProd Φ hΦ hΦs y).fst).fst +
        TrivialLieModule.equiv R P R ((ofProd c).symm (extendedToProd Φ hΦ hΦs x).fst).snd *
          (extendedToProd Φ hΦ hΦs y).snd +
        (extendedToProd Φ hΦ hΦs x).snd *
          TrivialLieModule.equiv R P R ((ofProd c).symm (extendedToProd Φ hΦ hΦs y).fst).snd := by
  simp only [extendedBilinForm, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.compl₁₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LieHom.coe_toLinearMap,
    LinearMap.fst_apply, LinearMap.snd_apply, coe_ofProdLinearEquiv_symm, ofTwoCocycle.proj_apply,
    LinearMap.mul_apply']
  ring

/-- On modes, `extendedBilinForm Φ` pairs `tᵐ ⊗ x` with `tⁿ ⊗ y` to `-Φ(x, y) δ_{m + n, 0}`. -/
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
      (mode Φ hΦ hΦs n x) = 0 := by
  simp [extendedBilinForm_apply, mode_apply]

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
      (degreeElement Φ hΦ hΦs) = 1 := by
  simp [extendedBilinForm_apply]

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
theorem extendedBilinForm_isSymm : (extendedBilinForm Φ hΦ hΦs).IsSymm := by
  refine LinearMap.BilinForm.isSymm_def.mpr fun x y ↦ ?_
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
  obtain ⟨xl, ax, rfl⟩ := exists_eq_add_smul_degreeElement Φ hΦ hΦs x
  obtain ⟨yl, ay, rfl⟩ := exists_eq_add_smul_degreeElement Φ hΦ hΦs y
  obtain ⟨⟨ux, cx⟩, rfl⟩ := (ofProd c).surjective xl
  obtain ⟨⟨uy, cy⟩, rfl⟩ := (ofProd c).surjective yl
  have hbra :
      ⁅toExtendedResidueExtension Φ hΦ hΦs (ofProd c (ux, cx)) + ax • degreeElement Φ hΦ hΦs,
        toExtendedResidueExtension Φ hΦ hΦs (ofProd c (uy, cy)) + ay • degreeElement Φ hΦ hΦs⁆ =
        toExtendedResidueExtension Φ hΦ hΦs (⁅ofProd c (ux, cx), ofProd c (uy, cy)⁆ +
          ax • δ (ofProd c (uy, cy)) - ay • δ (ofProd c (ux, cx))) := by
    simp only [add_lie, lie_add, smul_lie, lie_smul, lie_self, smul_zero, add_zero,
      lie_degreeElement_toExtendedResidueExtension, ← LieHom.map_lie]
    rw [← lie_skew _ (degreeElement Φ hΦ hΦs), lie_degreeElement_toExtendedResidueExtension]
    simp only [map_sub, map_add, map_smul, smul_neg]
    abel
  have hprod (w : E) (a : R) :
      extendedToProd Φ hΦ hΦs (toExtendedResidueExtension Φ hΦ hΦs w + a • degreeElement Φ hΦ hΦs) =
        (w, a) := by simp [map_add, map_smul]
  rw [hbra, hprod, hprod]
  simp only [Equiv.symm_apply_apply, extendedToProd_toExtendedResidueExtension, Prod.mk.injEq,
    and_true]
  apply (ofProd c).symm.injective
  rw [← coe_ofProdLinearEquiv_symm, map_sub, map_add, map_smul, map_smul]
  simp [bracket_ofTwoCocycle, trivial_lie_zero, sub_eq_add_neg,
    twoCocycleOfBilinear_coe, twoCochainOfBilinear_apply_apply]

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
  have hinv := constantTermPairing_lieInvariant hΦ u v p
  have hD1 := constantTermPairing_degreeDerivation_add_eq_zero Φ v p
  have hD2 := constantTermPairing_degreeDerivation_add_eq_zero Φ u p
  have hD3 := constantTermPairing_degreeDerivation_add_eq_zero Φ u v
  have hR1 := constantTermPairing_degreeDerivation_right Φ u p
  have hR2 := constantTermPairing_degreeDerivation_right Φ u v
  have hsym := (constantTermPairing_isSymm hΦs).eq v (degreeDerivation R L u)
  linear_combination -hinv - a * hD1 + b * hD2 + q * hD3 - b * hR1 - q * hR2 + q * hsym

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
      exact Prod.ext
        ((ofProd c).symm.injective (by rw [Prod.fst_zero, of_symm_zero]; exact Prod.ext hu hz)) ha
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
local notation "Z" => TrivialLieModule R P R
local notation "cΦ" => twoCocycleOfBilinear R ℤ L Φ hΦ hΦs
local notation "cΨ" => twoCocycleOfBilinear R ℤ L Ψ hΨ hΨs

private theorem twoCocycleOfBilinear_eq_smul {r : R} (h : Ψ = r • Φ) : cΨ = r • cΦ := by
  subst h
  exact Subtype.ext (twoCochainOfBilinear_smul r hΦs hΨs)

/-- Rescaling the level of the polynomial loop central extension: if `Ψ = r • Φ`, the Lie algebra
homomorphism `ofTwoCocycle cΦ →ₗ⁅R⁆ ofTwoCocycle cΨ` fixing loops and sending `K ↦ r • K`. -/
def levelHom {r : R} (h : Ψ = r • Φ) : ofTwoCocycle cΦ →ₗ⁅R⁆ ofTwoCocycle cΨ :=
  ofTwoCocycle.smulMap cΦ cΨ r (twoCocycleOfBilinear_eq_smul hΦ hΦs hΨ hΨs h)

@[simp]
theorem levelHom_ofProd {r : R} (h : Ψ = r • Φ) (u : P) (z : Z) :
    levelHom hΦ hΦs hΨ hΨs h (ofProd cΦ (u, z)) = ofProd cΨ (u, r • z) :=
  ofTwoCocycle.smulMap_ofProd cΦ cΨ r _ u z

@[simp]
theorem ofProd_symm_levelHom {r : R} (h : Ψ = r • Φ) (v : ofTwoCocycle cΦ) :
    (ofProd cΨ).symm (levelHom hΦ hΦs hΨ hΨs h v) =
      (((ofProd cΦ).symm v).fst, r • ((ofProd cΦ).symm v).snd) :=
  ofTwoCocycle.ofProd_symm_smulMap cΦ cΨ r _ v

@[simp]
theorem levelHom_centralElement {r : R} (h : Ψ = r • Φ) :
    levelHom hΦ hΦs hΨ hΨs h (centralElement cΦ) = r • centralElement cΨ :=
  ofTwoCocycle.smulMap_centralElement cΦ cΨ r _

/-- If `Ψ = u • Φ` for a unit `u`, the central extensions `ofTwoCocycle cΦ` and `ofTwoCocycle cΨ`
are isomorphic via `(v, z) ↦ (v, u • z)`. -/
def levelEquiv {u : Rˣ} (h : Ψ = (u : R) • Φ) : ofTwoCocycle cΦ ≃ₗ⁅R⁆ ofTwoCocycle cΨ :=
  ofTwoCocycle.smulMapEquiv cΦ cΨ u (twoCocycleOfBilinear_eq_smul hΦ hΦs hΨ hΨs h)

@[simp]
theorem levelEquiv_ofProd {u : Rˣ} (h : Ψ = (u : R) • Φ) (v : P) (z : Z) :
    levelEquiv hΦ hΦs hΨ hΨs h (ofProd cΦ (v, z)) = ofProd cΨ (v, (u : R) • z) := by
  rw [levelEquiv]
  simp [Units.smul_def]

@[simp]
theorem levelEquiv_centralElement {u : Rˣ} (h : Ψ = (u : R) • Φ) :
    levelEquiv hΦ hΦs hΨ hΨs h (centralElement cΦ) = (u : R) • centralElement cΨ :=
  ofTwoCocycle.smulMapEquiv_centralElement cΦ cΨ u _

/-- The inverse of `levelEquiv` is the level isomorphism for the reciprocal scalar `u⁻¹`. -/
theorem levelEquiv_symm {u : Rˣ} (h : Ψ = (u : R) • Φ) :
    (levelEquiv hΦ hΦs hΨ hΨs h).symm =
      levelEquiv (u := u⁻¹) hΨ hΨs hΦ hΦs (by rw [h, smul_smul, Units.inv_mul, one_smul]) := by
  rw [levelEquiv, levelEquiv]
  exact ofTwoCocycle.smulMapEquiv_symm cΦ cΨ u _

/-- **Level transport on extended affine loop algebras**: if `Ψ = r • Φ`, the Lie algebra
homomorphism `extendedResidueExtension Φ →ₗ⁅R⁆ extendedResidueExtension Ψ` fixing all loop modes
and `d` while sending `K ↦ r • K`. -/
def extendedLevelHom {r : R} (h : Ψ = r • Φ) :
    extendedResidueExtension Φ hΦ hΦs →ₗ⁅R⁆ extendedResidueExtension Ψ hΨ hΨs where
  __ := (extendedToProd Ψ hΨ hΨs).symm.toLinearMap ∘ₗ
    LinearMap.prodMap (levelHom hΦ hΦs hΨ hΨs h).toLinearMap LinearMap.id ∘ₗ
    (extendedToProd Φ hΦ hΦs).toLinearMap
  map_lie' {x y} := by
    apply (extendedToProd Ψ hΨ hΨs).injective
    simp only [LinearMap.toFun_eq_coe, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearMap.prodMap_apply, LieHom.coe_toLinearMap, LinearMap.id_coe,
      id_eq, LinearEquiv.apply_symm_apply, extendedToProd_lie Ψ hΨ hΨs,
      extendedToProd_lie Φ hΦ hΦs, ofProd_symm_levelHom, levelHom_ofProd]
    refine Prod.ext (congrArg (ofProd cΨ) (Prod.ext rfl ?_)) rfl
    apply (TrivialLieModule.equiv R P R).injective
    simp [h, residuePairing_smul]

@[simp]
theorem extendedToProd_extendedLevelHom {r : R} (h : Ψ = r • Φ)
    (x : extendedResidueExtension Φ hΦ hΦs) :
    extendedToProd Ψ hΨ hΨs (extendedLevelHom hΦ hΦs hΨ hΨs h x) =
      (levelHom hΦ hΦs hΨ hΨs h (extendedToProd Φ hΦ hΦs x).fst,
        (extendedToProd Φ hΦ hΦs x).snd) :=
  (extendedToProd Ψ hΨ hΨs).apply_symm_apply _

/-- `extendedLevelHom` restricts to `levelHom` on the derived central extension. -/
theorem extendedLevelHom_toExtendedResidueExtension {r : R} (h : Ψ = r • Φ) (x : ofTwoCocycle cΦ) :
    extendedLevelHom hΦ hΦs hΨ hΨs h (toExtendedResidueExtension Φ hΦ hΦs x) =
      toExtendedResidueExtension Ψ hΨ hΨs (levelHom hΦ hΦs hΨ hΨs h x) :=
  (extendedToProd Ψ hΨ hΨs).injective (by simp)

/-- `extendedLevelHom` fixes every loop mode `tⁿ ⊗ x`. -/
@[simp]
theorem extendedLevelHom_mode {r : R} (h : Ψ = r • Φ) (n : ℤ) (x : L) :
    extendedLevelHom hΦ hΦs hΨ hΨs h (mode Φ hΦ hΦs n x) = mode Ψ hΨ hΨs n x := by
  simp [mode_apply, extendedLevelHom_toExtendedResidueExtension]

/-- `extendedLevelHom` scales the canonical central element by `r`. -/
@[simp]
theorem extendedLevelHom_centralElement {r : R} (h : Ψ = r • Φ) :
    extendedLevelHom hΦ hΦs hΨ hΨs h (toExtendedResidueExtension Φ hΦ hΦs (centralElement cΦ)) =
      r • toExtendedResidueExtension Ψ hΨ hΨs (centralElement cΨ) := by
  rw [extendedLevelHom_toExtendedResidueExtension, levelHom_centralElement, map_smul]

/-- `extendedLevelHom` preserves the degree element `d`. -/
@[simp]
theorem extendedLevelHom_degreeElement {r : R} (h : Ψ = r • Φ) :
    extendedLevelHom hΦ hΦs hΨ hΨs h (degreeElement Φ hΦ hΦs) = degreeElement Ψ hΨ hΨs :=
  (extendedToProd Ψ hΨ hΨs).injective (by simp)

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
    extendedToProd_extendedLevelHom, ofProd_symm_levelHom, ofProd_symm_levelHom, hct]
  simp only [LinearMap.smul_apply, smul_eq_mul, map_smul]
  ring

/-- **Level isomorphism for extended affine loop algebras**: if `Ψ = u • Φ` for a unit `u`, then
`extendedResidueExtension Φ` and `extendedResidueExtension Ψ` are isomorphic as Lie algebras via
the map fixing all loop modes and `d` and sending `K ↦ u • K`. -/
def extendedLevelEquiv {u : Rˣ} (h : Ψ = (u : R) • Φ) :
    extendedResidueExtension Φ hΦ hΦs ≃ₗ⁅R⁆ extendedResidueExtension Ψ hΨ hΨs where
  __ := extendedLevelHom hΦ hΦs hΨ hΨs h
  invFun := extendedLevelHom hΨ hΨs hΦ hΦs (by rw [h, smul_smul, Units.inv_mul, one_smul])
  left_inv x := (extendedToProd Φ hΦ hΦs).injective <|
    Prod.ext ((ofProd cΦ).symm.injective (by simp [smul_smul])) (by simp)
  right_inv y := (extendedToProd Ψ hΨ hΨs).injective <|
    Prod.ext ((ofProd cΨ).symm.injective (by simp [smul_smul])) (by simp)

/-- The inverse of `extendedLevelEquiv` is the extended level isomorphism for `u⁻¹`. -/
theorem extendedLevelEquiv_symm {u : Rˣ} (h : Ψ = (u : R) • Φ) :
    (extendedLevelEquiv hΦ hΦs hΨ hΨs h).symm =
      extendedLevelEquiv (u := u⁻¹) hΨ hΨs hΦ hΦs
        (by rw [h, smul_smul, Units.inv_mul, one_smul]) :=
  LieEquiv.ext fun _ ↦ rfl

@[simp]
theorem extendedLevelEquiv_mode {u : Rˣ} (h : Ψ = (u : R) • Φ) (n : ℤ) (x : L) :
    extendedLevelEquiv hΦ hΦs hΨ hΨs h (mode Φ hΦ hΦs n x) = mode Ψ hΨ hΨs n x :=
  extendedLevelHom_mode hΦ hΦs hΨ hΨs h n x

@[simp]
theorem extendedLevelEquiv_centralElement {u : Rˣ} (h : Ψ = (u : R) • Φ) :
    extendedLevelEquiv hΦ hΦs hΨ hΨs h (toExtendedResidueExtension Φ hΦ hΦs (centralElement cΦ)) =
      (u : R) • toExtendedResidueExtension Ψ hΨ hΨs (centralElement cΨ) :=
  extendedLevelHom_centralElement hΦ hΦs hΨ hΨs h

@[simp]
theorem extendedLevelEquiv_degreeElement {u : Rˣ} (h : Ψ = (u : R) • Φ) :
    extendedLevelEquiv hΦ hΦs hΨ hΨs h (degreeElement Φ hΦ hΦs) = degreeElement Ψ hΨ hΨs :=
  extendedLevelHom_degreeElement hΦ hΦs hΨ hΨs h

/-- Under `extendedLevelEquiv`, `extendedBilinForm Ψ` pulls back to `u * extendedBilinForm Φ`. -/
theorem extendedBilinForm_extendedLevelEquiv {u : Rˣ} (h : Ψ = (u : R) • Φ)
    (x y : extendedResidueExtension Φ hΦ hΦs) :
    extendedBilinForm Ψ hΨ hΨs (extendedLevelEquiv hΦ hΦs hΨ hΨs h x)
        (extendedLevelEquiv hΦ hΦs hΨ hΨs h y) =
      (u : R) * extendedBilinForm Φ hΦ hΦs x y :=
  extendedBilinForm_extendedLevelHom hΦ hΦs hΨ hΨs h x y

end Level

end TauCeti.LieAlgebra.LoopAlgebra
