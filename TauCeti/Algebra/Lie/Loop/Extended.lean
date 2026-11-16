/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Algebra.Lie.Loop
public import TauCeti.Algebra.Lie.Extension.Basic
public import TauCeti.Algebra.Lie.SemiDirect.Basic
-- Proof-only: mode formula, H² classification on loops, and dual separation of nonzero vectors.
import Mathlib.LinearAlgebra.Dual.Lemmas
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

Finally, over a characteristic-zero field `K` when `L` has nondegenerate Killing form and a
one-dimensional space of invariant forms spanned by `Φ`, `ofTwoCocycle c` satisfies the universal
central extension property: for any surjective homomorphism `f : G →ₗ⁅K⁆ ofTwoCocycle c` from a
perfect Lie algebra `G` admitting a central lift of `K` expressed as a bracket combination with
nonzero residue pairing, the kernel satisfies `⁅⊤, f.ker⁆ = f.ker`
(`TauCeti.LieAlgebra.LoopAlgebra.lie_top_ker_eq_ker_of_surjective_ofTwoCocycle`).

## Main definitions

* `TauCeti.LieAlgebra.LoopAlgebra.degreeDerivation`: the degree derivation `t d/dt` on
  `loopAlgebra R ℤ L`.
* `TauCeti.LieAlgebra.LoopAlgebra.constantTermPairing`: the constant-term bilinear form
  `(x_m, y_n) ↦ Φ(x, y) δ_{m + n, 0}` on `loopAlgebra R ℤ L`.
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
* `TauCeti.LieAlgebra.LoopAlgebra.extendedBilinForm_isSymm`,
  `TauCeti.LieAlgebra.LoopAlgebra.extendedBilinForm_lieInvariant`, and
  `TauCeti.LieAlgebra.LoopAlgebra.extendedBilinForm_nondegenerate`: `extendedBilinForm` is
  symmetric, invariant, and nondegenerate whenever `Φ` is.
* `TauCeti.LieAlgebra.LoopAlgebra.extendedBilinForm_extendedLevelHom` and
  `TauCeti.LieAlgebra.LoopAlgebra.extendedBilinForm_extendedLevelEquiv`: level transport scales the
  invariant form by `r`.
* `TauCeti.LieAlgebra.LoopAlgebra.lie_top_ker_eq_ker_of_surjective_ofTwoCocycle`: universal central
  extension property (`⁅⊤, f.ker⁆ = f.ker`) for perfect covers of `ofTwoCocycle c`.

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

/-- The underlying linear map of the degree derivation `t d/dt` on `loopAlgebra R ℤ L`. -/
private def degreeLinearMap (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] :
    loopAlgebra R ℤ L →ₗ[R] loopAlgebra R ℤ L :=
  (Finsupp.lsum R fun n : ℤ ↦
      (n : R) • ((toFinsupp R ℤ L).symm.toLinearMap ∘ₗ Finsupp.lsingle n)) ∘ₗ
    (toFinsupp R ℤ L).toLinearMap

private theorem degreeLinearMap_single_tmul (n : ℤ) (x : L) :
    degreeLinearMap R L (AddMonoidAlgebra.single n (1 : R) ⊗ₜ[R] x) =
      n • (AddMonoidAlgebra.single n (1 : R) ⊗ₜ[R] x) := by
  have h : toFinsupp R ℤ L (AddMonoidAlgebra.single n (1 : R) ⊗ₜ[R] x) = Finsupp.single n x := by
    rw [← toFinsupp_symm_single, LinearEquiv.apply_symm_apply]
  simp only [degreeLinearMap, LinearMap.comp_apply, LinearEquiv.coe_coe, h, Finsupp.lsum_single,
    LinearMap.smul_apply, Finsupp.lsingle_apply, toFinsupp_symm_single, Int.cast_smul_eq_zsmul]

variable (R L) in
/-- **The degree derivation `d = t d/dt`** on the polynomial loop algebra `loopAlgebra R ℤ L`,
acting on modes by `d (tⁿ ⊗ x) = n (tⁿ ⊗ x)`. -/
def degreeDerivation : LieDerivation R (loopAlgebra R ℤ L) (loopAlgebra R ℤ L) where
  toLinearMap := degreeLinearMap R L
  leibniz' u v := by
    obtain ⟨f, rfl⟩ := (toFinsupp R ℤ L).symm.surjective u
    obtain ⟨g, rfl⟩ := (toFinsupp R ℤ L).symm.surjective v
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ h₁ h₂ =>
      simp only [map_add, add_lie, lie_add, h₁, h₂]
      abel
    | single m x =>
      induction g using Finsupp.induction_linear with
      | zero => simp
      | add g₁ g₂ h₁ h₂ =>
        simp only [map_add, add_lie, lie_add, h₁, h₂]
        abel
      | single n y =>
        simp only [toFinsupp_symm_single, ExtendScalars.bracket_tmul,
          AddMonoidAlgebra.single_mul_single, mul_one, degreeLinearMap_single_tmul, lie_zsmul,
          add_zsmul, add_comm m n]
        rw [← lie_skew x y, TensorProduct.tmul_neg, smul_neg, smul_neg, sub_eq_add_neg]

/-- On modes, the degree derivation multiplies `tⁿ ⊗ x` by `n`. -/
theorem degreeDerivation_single_tmul (n : ℤ) (x : L) :
    degreeDerivation R L (AddMonoidAlgebra.single n (1 : R) ⊗ₜ[R] x) =
      n • (AddMonoidAlgebra.single n (1 : R) ⊗ₜ[R] x) :=
  degreeLinearMap_single_tmul n x

/-- The degree derivation vanishes on constant loops `1 ⊗ x`. -/
@[simp]
theorem degreeDerivation_one_tmul (x : L) :
    degreeDerivation R L (1 ⊗ₜ[R] x) = 0 := by
  rw [AddMonoidAlgebra.one_def, degreeDerivation_single_tmul, zero_zsmul]

/-- The degree derivation is skew for the residue pairing of every bilinear form on `L`:
`Res(d(u) dv) + Res(u d(dv)) = 0`. -/
theorem residuePairing_degreeDerivation_add (Φ : LinearMap.BilinForm R L)
    (u v : loopAlgebra R ℤ L) :
    residuePairing R ℤ L Φ (degreeDerivation R L u) v +
      residuePairing R ℤ L Φ u (degreeDerivation R L v) = 0 := by
  obtain ⟨f, rfl⟩ := (toFinsupp R ℤ L).symm.surjective u
  obtain ⟨g, rfl⟩ := (toFinsupp R ℤ L).symm.surjective v
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply]
    linear_combination h₁ + h₂
  | single m x =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g₁ g₂ h₁ h₂ =>
      simp only [map_add]
      linear_combination h₁ + h₂
    | single n y =>
      simp only [toFinsupp_symm_single, degreeDerivation_single_tmul, map_zsmul,
        LinearMap.smul_apply, residuePairing_single_tmul]
      split_ifs with h
      · rw [← add_zsmul, h, zero_zsmul]
      · simp

/-- **The constant-term pairing** on `loopAlgebra R ℤ L` induced by a bilinear form `Φ` on `L`:
it pairs `tᵐ ⊗ x` with `tⁿ ⊗ y` to `Φ(x, y)` if `m + n = 0` and `0` otherwise. -/
def constantTermPairing (Φ : LinearMap.BilinForm R L) :
    LinearMap.BilinForm R (loopAlgebra R ℤ L) :=
  LinearMap.mk₂ R
    (fun u v ↦ (toFinsupp R ℤ L u).sum fun m x ↦ Φ x (toFinsupp R ℤ L v (-m)))
    (fun u₁ u₂ v ↦ by
      rw [map_add, Finsupp.sum_add_index (by simp) (fun _ _ _ _ ↦ by simp)])
    (fun r u v ↦ by
      rw [map_smul, Finsupp.sum_smul_index' (by simp), Finsupp.smul_sum]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      simp)
    (fun u v₁ v₂ ↦ by
      simp only [map_add, Finsupp.add_apply, Finsupp.sum_add])
    (fun r u v ↦ by
      simp only [map_smul, Finsupp.smul_apply, Finsupp.smul_sum])

/-- On modes, `constantTermPairing Φ` pairs `tᵐ ⊗ x` with `tⁿ ⊗ y` to `Φ(x, y) δ_{m + n, 0}`. -/
theorem constantTermPairing_single_tmul (Φ : LinearMap.BilinForm R L) (m n : ℤ) (x y : L) :
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
theorem constantTermPairing_smul (r : R) (Φ : LinearMap.BilinForm R L) :
    constantTermPairing (r • Φ) = r • constantTermPairing Φ := by
  refine LinearMap.ext₂ fun u v ↦ ?_
  simp only [constantTermPairing, LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul,
    Finsupp.mul_sum]

/-- If `Φ` is symmetric, then `constantTermPairing Φ` is symmetric. -/
theorem constantTermPairing_isSymm {Φ : LinearMap.BilinForm R L} (hΦs : Φ.IsSymm) :
    (constantTermPairing Φ).IsSymm := by
  refine LinearMap.BilinForm.isSymm_def.mpr fun u v ↦ ?_
  obtain ⟨f, rfl⟩ := (toFinsupp R ℤ L).symm.surjective u
  obtain ⟨g, rfl⟩ := (toFinsupp R ℤ L).symm.surjective v
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | single m x =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g₁ g₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
    | single n y =>
      simp only [toFinsupp_symm_single, constantTermPairing_single_tmul, add_comm m n, hΦs.eq x y]

/-- If `Φ` is invariant on `L`, then `constantTermPairing Φ` is invariant on
`loopAlgebra R ℤ L`. -/
theorem constantTermPairing_lieInvariant {Φ : LinearMap.BilinForm R L} (hΦ : Φ.lieInvariant L) :
    (constantTermPairing Φ).lieInvariant (loopAlgebra R ℤ L) := by
  intro u v w
  obtain ⟨f, rfl⟩ := (toFinsupp R ℤ L).symm.surjective u
  obtain ⟨g, rfl⟩ := (toFinsupp R ℤ L).symm.surjective v
  obtain ⟨h, rfl⟩ := (toFinsupp R ℤ L).symm.surjective w
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, zero_lie, LinearMap.zero_apply, neg_zero]
  | add f₁ f₂ h₁ h₂ =>
    simp only [map_add, add_lie, LinearMap.add_apply]
    linear_combination h₁ + h₂
  | single k x =>
    induction g using Finsupp.induction_linear with
    | zero => simp only [map_zero, lie_zero, LinearMap.zero_apply, neg_zero]
    | add g₁ g₂ h₁ h₂ =>
      simp only [map_add, lie_add, LinearMap.add_apply]
      linear_combination h₁ + h₂
    | single m y =>
      induction h using Finsupp.induction_linear with
      | zero => simp only [map_zero, lie_zero, neg_zero]
      | add h₁ h₂ ih₁ ih₂ =>
        simp only [map_add, lie_add]
        linear_combination ih₁ + ih₂
      | single n z =>
        simp only [toFinsupp_symm_single, ExtendScalars.bracket_tmul,
          AddMonoidAlgebra.single_mul_single, mul_one, constantTermPairing_single_tmul]
        by_cases hsum : k + m + n = 0
        · simp only [hsum, show m + (k + n) = 0 by omega, ↓reduceIte, hΦ x y z]
        · simp only [hsum, show ¬(m + (k + n) = 0) by omega, ↓reduceIte, neg_zero]

/-- If `Φ` is left-separating on `L`, then `constantTermPairing Φ` is left-separating on
`loopAlgebra R ℤ L`. -/
theorem constantTermPairing_separatingLeft {Φ : LinearMap.BilinForm R L}
    (hΦ : Φ.SeparatingLeft) : (constantTermPairing Φ).SeparatingLeft := by
  intro u hu
  apply (toFinsupp R ℤ L).injective
  ext m
  rw [map_zero, Finsupp.zero_apply]
  refine hΦ _ fun y ↦ ?_
  have h := hu (AddMonoidAlgebra.single (-m) (1 : R) ⊗ₜ[R] y)
  rw [constantTermPairing, LinearMap.mk₂_apply, toFinsupp_single_tmul] at h
  rw [Finsupp.sum_eq_single m (fun k _ hkm ↦ by
      rw [Finsupp.single_eq_of_ne (fun hk ↦ hkm (neg_inj.mp hk)), map_zero])
    (by simp)] at h
  simpa using h

/-- **Constant-term pairing against the degree derivation equals the residue pairing**:
`(u, d v)_0 = Res(u dv)`. -/
theorem constantTermPairing_degreeDerivation_right (Φ : LinearMap.BilinForm R L)
    (u v : loopAlgebra R ℤ L) :
    constantTermPairing Φ u (degreeDerivation R L v) = residuePairing R ℤ L Φ u v := by
  obtain ⟨f, rfl⟩ := (toFinsupp R ℤ L).symm.surjective u
  obtain ⟨g, rfl⟩ := (toFinsupp R ℤ L).symm.surjective v
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | single m x =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g₁ g₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | single n y =>
      simp only [toFinsupp_symm_single, degreeDerivation_single_tmul, map_zsmul,
        constantTermPairing_single_tmul, residuePairing_single_tmul]
      split_ifs <;> simp

/-- The degree derivation is skew for `constantTermPairing Φ`:
`(d u, v)_0 + (u, d v)_0 = 0`. -/
theorem constantTermPairing_degreeDerivation_add (Φ : LinearMap.BilinForm R L)
    (u v : loopAlgebra R ℤ L) :
    constantTermPairing Φ (degreeDerivation R L u) v +
      constantTermPairing Φ u (degreeDerivation R L v) = 0 := by
  obtain ⟨f, rfl⟩ := (toFinsupp R ℤ L).symm.surjective u
  obtain ⟨g, rfl⟩ := (toFinsupp R ℤ L).symm.surjective v
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply]
    linear_combination h₁ + h₂
  | single m x =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g₁ g₂ h₁ h₂ =>
      simp only [map_add]
      linear_combination h₁ + h₂
    | single n y =>
      simp only [toFinsupp_symm_single, degreeDerivation_single_tmul, map_zsmul,
        LinearMap.smul_apply, constantTermPairing_single_tmul]
      split_ifs with h
      · rw [← add_zsmul, h, zero_zsmul]
      · simp

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
      residuePairing_degreeDerivation_add Φ u v, map_zero]

@[simp]
theorem extensionDegreeDerivation_ofProd (u : P) (z : TrivialLieModule R P R) :
    extensionDegreeDerivation Φ hΦ hΦs (ofProd c (u, z)) =
      ofProd c (degreeDerivation R L u, 0) :=
  ofTwoCocycle.derivation_ofProd c (degreeDerivation R L) _ u z

@[simp]
theorem extensionDegreeDerivation_centralElement :
    extensionDegreeDerivation Φ hΦ hΦs (centralElement c) = 0 := by
  apply (ofProd c).symm.injective
  simp [extensionDegreeDerivation]

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
  have h (y : E ⋊⁅ψ⁆ R) : y = inl ψ y.left + y.right • inr ψ 1 := by ext <;> simp
  ⟨_, _, h y⟩

/-- **The degree element acts by the degree derivation**: `⁅d, x⁆ = δ x` for `x ∈ ĝ`. -/
theorem lie_degreeElement_toExtendedResidueExtension (x : E) :
    ⁅degreeElement Φ hΦ hΦs, toExtendedResidueExtension Φ hΦ hΦs x⁆ =
      toExtendedResidueExtension Φ hΦ hΦs (δ x) :=
  LieDerivation.lie_inr_lineHom_one_inl δ x

/-- **The degree element commutes with `K`.** -/
@[simp]
theorem lie_degreeElement_centralElement :
    ⁅degreeElement Φ hΦ hΦs,
      toExtendedResidueExtension Φ hΦ hΦs (centralElement c)⁆ = 0 := by
  rw [lie_degreeElement_toExtendedResidueExtension, extensionDegreeDerivation_centralElement,
    map_zero]

/-- **`K` is central in the extended affine loop algebra.** -/
theorem toExtendedResidueExtension_centralElement_mem_center :
    toExtendedResidueExtension Φ hΦ hΦs (centralElement c) ∈ center R E' := by
  refine (LieModule.mem_maxTrivSubmodule R E' E' _).2 fun y ↦ ?_
  obtain ⟨x, t, rfl⟩ := exists_eq_add_smul_degreeElement Φ hΦ hΦs y
  rw [add_lie, smul_lie, lie_degreeElement_centralElement, smul_zero, add_zero, ← LieHom.map_lie,
    (LieModule.mem_maxTrivSubmodule R E E _).1 (centralElement_mem_center c) x, map_zero]

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

/-- **The degree element on modes**: `⁅d, tⁿ ⊗ x⁆ = n (tⁿ ⊗ x)`. -/
@[simp]
theorem lie_degreeElement_mode (n : ℤ) (x : L) :
    ⁅degreeElement Φ hΦ hΦs, mode Φ hΦ hΦs n x⁆ = n • mode Φ hΦ hΦs n x := by
  have h : ofProd c (n • (AddMonoidAlgebra.single n (1 : R) ⊗ₜ[R] x), 0) =
      n • ofProd c (AddMonoidAlgebra.single n (1 : R) ⊗ₜ[R] x, 0) := by
    simpa [coe_ofProdLinearEquiv] using
      map_zsmul (ofProdLinearEquiv c) n (AddMonoidAlgebra.single n (1 : R) ⊗ₜ[R] x, 0)
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

private theorem extendedBilinForm_apply_aux (x y : E') :
    extendedBilinForm Φ hΦ hΦs x y =
      -constantTermPairing Φ
          ((ofProd c).symm (extendedToProd Φ hΦ hΦs x).1).1
          ((ofProd c).symm (extendedToProd Φ hΦ hΦs y).1).1 +
        TrivialLieModule.equiv R P R ((ofProd c).symm (extendedToProd Φ hΦ hΦs x).1).2 *
          (extendedToProd Φ hΦ hΦs y).2 +
        (extendedToProd Φ hΦ hΦs x).2 *
          TrivialLieModule.equiv R P R ((ofProd c).symm (extendedToProd Φ hΦ hΦs y).1).2 := by
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
  rw [extendedBilinForm_apply_aux, mode_apply, mode_apply,
    extendedToProd_toExtendedResidueExtension, extendedToProd_toExtendedResidueExtension]
  simp only [Equiv.symm_apply_apply, map_zero, mul_zero, add_zero, constantTermPairing_single_tmul]
  split_ifs <;> simp

/-- `K` is orthogonal to every mode. -/
@[simp]
theorem extendedBilinForm_centralElement_mode (n : ℤ) (x : L) :
    extendedBilinForm Φ hΦ hΦs (toExtendedResidueExtension Φ hΦ hΦs (centralElement c))
      (mode Φ hΦ hΦs n x) = 0 := by
  rw [extendedBilinForm_apply_aux, mode_apply, extendedToProd_toExtendedResidueExtension,
    extendedToProd_toExtendedResidueExtension]
  simp

/-- Every mode is orthogonal to `K`. -/
@[simp]
theorem extendedBilinForm_mode_centralElement (n : ℤ) (x : L) :
    extendedBilinForm Φ hΦ hΦs (mode Φ hΦ hΦs n x)
      (toExtendedResidueExtension Φ hΦ hΦs (centralElement c)) = 0 := by
  rw [extendedBilinForm_apply_aux, mode_apply, extendedToProd_toExtendedResidueExtension,
    extendedToProd_toExtendedResidueExtension]
  simp

/-- `d` is orthogonal to every mode. -/
@[simp]
theorem extendedBilinForm_degreeElement_mode (n : ℤ) (x : L) :
    extendedBilinForm Φ hΦ hΦs (degreeElement Φ hΦ hΦs) (mode Φ hΦ hΦs n x) = 0 := by
  rw [extendedBilinForm_apply_aux, mode_apply, extendedToProd_degreeElement,
    extendedToProd_toExtendedResidueExtension]
  simp

/-- Every mode is orthogonal to `d`. -/
@[simp]
theorem extendedBilinForm_mode_degreeElement (n : ℤ) (x : L) :
    extendedBilinForm Φ hΦ hΦs (mode Φ hΦ hΦs n x) (degreeElement Φ hΦ hΦs) = 0 := by
  rw [extendedBilinForm_apply_aux, mode_apply, extendedToProd_toExtendedResidueExtension,
    extendedToProd_degreeElement]
  simp

/-- `(K, d) = 1`. -/
@[simp]
theorem extendedBilinForm_centralElement_degreeElement :
    extendedBilinForm Φ hΦ hΦs (toExtendedResidueExtension Φ hΦ hΦs (centralElement c))
      (degreeElement Φ hΦ hΦs) = 1 := by
  rw [extendedBilinForm_apply_aux, extendedToProd_toExtendedResidueExtension,
    extendedToProd_degreeElement]
  simp

/-- `(d, K) = 1`. -/
@[simp]
theorem extendedBilinForm_degreeElement_centralElement :
    extendedBilinForm Φ hΦ hΦs (degreeElement Φ hΦ hΦs)
      (toExtendedResidueExtension Φ hΦ hΦs (centralElement c)) = 1 := by
  rw [extendedBilinForm_apply_aux, extendedToProd_degreeElement,
    extendedToProd_toExtendedResidueExtension]
  simp

/-- `(K, K) = 0`. -/
@[simp]
theorem extendedBilinForm_centralElement_centralElement :
    extendedBilinForm Φ hΦ hΦs (toExtendedResidueExtension Φ hΦ hΦs (centralElement c))
      (toExtendedResidueExtension Φ hΦ hΦs (centralElement c)) = 0 := by
  rw [extendedBilinForm_apply_aux, extendedToProd_toExtendedResidueExtension]
  simp

/-- `(d, d) = 0`. -/
@[simp]
theorem extendedBilinForm_degreeElement_degreeElement :
    extendedBilinForm Φ hΦ hΦs (degreeElement Φ hΦ hΦs) (degreeElement Φ hΦ hΦs) = 0 := by
  rw [extendedBilinForm_apply_aux, extendedToProd_degreeElement]
  simp

/-- **`extendedBilinForm` is symmetric.** -/
theorem extendedBilinForm_isSymm : (extendedBilinForm Φ hΦ hΦs).IsSymm := by
  refine LinearMap.BilinForm.isSymm_def.mpr fun x y ↦ ?_
  rw [extendedBilinForm_apply_aux, extendedBilinForm_apply_aux,
    (constantTermPairing_isSymm hΦs).eq]
  ring

/-- The bracket in `extendedResidueExtension` read in `P × R × R` coordinates. -/
private theorem extendedToProd_lie (x y : E') :
    let px := (ofProd c).symm (extendedToProd Φ hΦ hΦs x).1
    let py := (ofProd c).symm (extendedToProd Φ hΦ hΦs y).1
    let ax := (extendedToProd Φ hΦ hΦs x).2
    let ay := (extendedToProd Φ hΦ hΦs y).2
    extendedToProd Φ hΦ hΦs ⁅x, y⁆ =
      (ofProd c (⁅px.1, py.1⁆ + ax • degreeDerivation R L py.1 - ay • degreeDerivation R L px.1,
        (TrivialLieModule.equiv R P R).symm (residuePairing R ℤ L Φ px.1 py.1)), 0) := by
  revert x y
  -- Read `x` and `y` in the underlying semidirect sum `E ⋊⁅ψ⁆ R`.
  change ∀ x y : E ⋊⁅ψ⁆ R,
    let px := (ofProd c).symm x.left
    let py := (ofProd c).symm y.left
    (⁅x, y⁆.left, ⁅x, y⁆.right) =
      (ofProd c (⁅px.1, py.1⁆ + x.right • degreeDerivation R L py.1 -
          y.right • degreeDerivation R L px.1,
        (TrivialLieModule.equiv R P R).symm (residuePairing R ℤ L Φ px.1 py.1)), 0)
  rintro ⟨xl, xr⟩ ⟨yl, yr⟩
  obtain ⟨⟨ux, cx⟩, rfl⟩ := (ofProd c).surjective xl
  obtain ⟨⟨uy, cy⟩, rfl⟩ := (ofProd c).surjective yl
  refine Prod.ext ((ofProd c).symm.injective ?_) (by simp [Ring.lie_def, mul_comm])
  dsimp only
  rw [SemiDirectSum.lie_eq_mk]
  dsimp only
  rw [LieDerivation.lineHom_apply, LieDerivation.lineHom_apply,
    LieDerivation.smul_apply, LieDerivation.smul_apply]
  have hsub (a b : E) : (ofProd c).symm (a - b) = (ofProd c).symm a - (ofProd c).symm b := rfl
  have hδ (u : P) (z : TrivialLieModule R P R) :
      (ofProd c).symm (δ (ofProd c (u, z))) = (degreeDerivation R L u, 0) := by
    simp [extensionDegreeDerivation]
  rw [hsub, of_symm_add, bracket_ofTwoCocycle, of_symm_smul, of_symm_smul, hδ, hδ]
  simp only [Equiv.symm_apply_apply]
  refine Prod.ext ?_ ?_
  · simp
  · simp [trivial_lie_zero, twoCocycleOfBilinear_coe, twoCochain_val_apply,
      twoCochainOfBilinear_apply_apply]

/-- **`extendedBilinForm` is `ĝ'`-invariant**: `B(⁅x, y⁆, w) + B(y, ⁅x, w⁆) = 0`. -/
theorem extendedBilinForm_lieInvariant : (extendedBilinForm Φ hΦ hΦs).lieInvariant E' := by
  intro x y w
  rw [extendedBilinForm_apply_aux, extendedBilinForm_apply_aux,
    extendedToProd_lie Φ hΦ hΦs x y, extendedToProd_lie Φ hΦ hΦs x w]
  set u := ((ofProd c).symm (extendedToProd Φ hΦ hΦs x).1).1
  set v := ((ofProd c).symm (extendedToProd Φ hΦ hΦs y).1).1
  set p := ((ofProd c).symm (extendedToProd Φ hΦ hΦs w).1).1
  set a := (extendedToProd Φ hΦ hΦs x).2
  set b := (extendedToProd Φ hΦ hΦs y).2
  set q := (extendedToProd Φ hΦ hΦs w).2
  simp only [Equiv.symm_apply_apply, LinearEquiv.apply_symm_apply, map_sub, map_add, map_smul,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, zero_mul,
    mul_zero, add_zero]
  have hinv := constantTermPairing_lieInvariant hΦ u v p
  have hD1 := constantTermPairing_degreeDerivation_add Φ v p
  have hD2 := constantTermPairing_degreeDerivation_add Φ u p
  have hD3 := constantTermPairing_degreeDerivation_add Φ u v
  have hR1 := constantTermPairing_degreeDerivation_right Φ u p
  have hR2 := constantTermPairing_degreeDerivation_right Φ u v
  have hsym := (constantTermPairing_isSymm hΦs).eq v (degreeDerivation R L u)
  linear_combination -hinv - a * hD1 + b * hD2 + q * hD3 - b * hR1 - q * hR2 + q * hsym

/-- **`extendedBilinForm` is nondegenerate** whenever `Φ` is nondegenerate on `L`. -/
theorem extendedBilinForm_nondegenerate (hΦn : Φ.Nondegenerate) :
    (extendedBilinForm Φ hΦ hΦs).Nondegenerate := by
  have hleft : (extendedBilinForm Φ hΦ hΦs).SeparatingLeft := by
    intro x hx
    apply (extendedToProd Φ hΦ hΦs).injective
    have ha : (extendedToProd Φ hΦ hΦs x).2 = 0 := by
      have hK := hx (toExtendedResidueExtension Φ hΦ hΦs (centralElement c))
      rw [extendedBilinForm_apply_aux, extendedToProd_toExtendedResidueExtension] at hK
      simpa using hK
    have hz : ((ofProd c).symm (extendedToProd Φ hΦ hΦs x).1).2 = 0 := by
      have hd := hx (degreeElement Φ hΦ hΦs)
      rw [extendedBilinForm_apply_aux, extendedToProd_degreeElement] at hd
      apply (TrivialLieModule.equiv R P R).injective
      simpa using hd
    have hu : ((ofProd c).symm (extendedToProd Φ hΦ hΦs x).1).1 = 0 := by
      refine constantTermPairing_separatingLeft hΦn.1 _ fun v ↦ ?_
      have hv := hx (toExtendedResidueExtension Φ hΦ hΦs (ofProd c (v, 0)))
      rw [extendedBilinForm_apply_aux, extendedToProd_toExtendedResidueExtension] at hv
      simpa using hv
    rw [map_zero]
    refine Prod.ext ((ofProd c).symm.injective ?_) ha
    rw [Prod.fst_zero, of_symm_zero]
    exact Prod.ext hu hz
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

/-- Rescaling the level of the polynomial loop central extension: if `Ψ = r • Φ`, the Lie algebra
homomorphism `ofTwoCocycle cΦ →ₗ⁅R⁆ ofTwoCocycle cΨ` fixing loops and sending `K ↦ r • K`. -/
def levelHom {r : R} (h : Ψ = r • Φ) : ofTwoCocycle cΦ →ₗ⁅R⁆ ofTwoCocycle cΨ :=
  ofTwoCocycle.map cΦ LieHom.id (r • LinearMap.id) cΨ fun u v ↦ by
    subst h
    simp [twoCocycleOfBilinear_coe, twoCochainOfBilinear_smul r hΦs hΨs, smul_apply_apply]

@[simp]
theorem levelHom_ofProd {r : R} (h : Ψ = r • Φ) (u : P) (z : Z) :
    levelHom hΦ hΦs hΨ hΨs h (ofProd cΦ (u, z)) = ofProd cΨ (u, r • z) :=
  ofTwoCocycle.map_ofProd cΦ LieHom.id (r • LinearMap.id) cΨ _ u z

@[simp]
theorem ofProd_symm_levelHom {r : R} (h : Ψ = r • Φ) (v : ofTwoCocycle cΦ) :
    (ofProd cΨ).symm (levelHom hΦ hΦs hΨ hΨs h v) =
      (((ofProd cΦ).symm v).1, r • ((ofProd cΦ).symm v).2) :=
  ofTwoCocycle.ofProd_symm_map cΦ LieHom.id (r • LinearMap.id) cΨ _ v

@[simp]
theorem levelHom_centralElement {r : R} (h : Ψ = r • Φ) :
    levelHom hΦ hΦs hΨ hΨs h (centralElement cΦ) = r • centralElement cΨ := by
  apply (ofProd cΨ).symm.injective
  simp

/-- If `Ψ = u • Φ` for a unit `u`, the central extensions `ofTwoCocycle cΦ` and `ofTwoCocycle cΨ`
are isomorphic via `(v, z) ↦ (v, u • z)`. -/
def levelEquiv {u : Rˣ} (h : Ψ = (u : R) • Φ) : ofTwoCocycle cΦ ≃ₗ⁅R⁆ ofTwoCocycle cΨ :=
  ofTwoCocycle.mapEquiv cΦ (LieEquiv.refl : P ≃ₗ⁅R⁆ P) (LinearEquiv.smulOfUnit u) cΨ fun v w ↦ by
    subst h
    simp [twoCocycleOfBilinear_coe, twoCochainOfBilinear_smul (u : R) hΦs hΨs, smul_apply_apply,
      LinearEquiv.smulOfUnit, Units.smul_def]

@[simp]
theorem levelEquiv_ofProd {u : Rˣ} (h : Ψ = (u : R) • Φ) (v : P) (z : Z) :
    levelEquiv hΦ hΦs hΨ hΨs h (ofProd cΦ (v, z)) = ofProd cΨ (v, (u : R) • z) :=
  ofTwoCocycle.mapEquiv_ofProd cΦ LieEquiv.refl (LinearEquiv.smulOfUnit u) cΨ _ v z

@[simp]
theorem levelEquiv_centralElement {u : Rˣ} (h : Ψ = (u : R) • Φ) :
    levelEquiv hΦ hΦs hΨ hΨs h (centralElement cΦ) = (u : R) • centralElement cΨ := by
  apply (ofProd cΨ).symm.injective
  simp [levelEquiv, LinearEquiv.smulOfUnit, Units.smul_def]

/-- **Level transport on extended affine loop algebras**: if `Ψ = r • Φ`, the Lie algebra
homomorphism `extendedResidueExtension Φ →ₗ⁅R⁆ extendedResidueExtension Ψ` fixing all loop modes
and `d` while sending `K ↦ r • K`. -/
def extendedLevelHom {r : R} (h : Ψ = r • Φ) :
    extendedResidueExtension Φ hΦ hΦs →ₗ⁅R⁆ extendedResidueExtension Ψ hΨ hΨs :=
  let f := levelHom hΦ hΦs hΨ hΨs h
  { toFun x :=
      (extendedToProd Ψ hΨ hΨs).symm
        (f (extendedToProd Φ hΦ hΦs x).1, (extendedToProd Φ hΦ hΦs x).2)
    map_add' x y := by
      simp only [map_add, Prod.fst_add, Prod.snd_add, ← Prod.mk_add_mk]
    map_smul' a x := by
      simp only [map_smul, Prod.smul_fst, Prod.smul_snd, ← Prod.smul_mk, RingHom.id_apply]
    map_lie' {x y} := by
      apply (extendedToProd Ψ hΨ hΨs).injective
      rw [LinearEquiv.apply_symm_apply, extendedToProd_lie Ψ hΨ hΨs,
        extendedToProd_lie Φ hΦ hΦs]
      simp only [LinearEquiv.apply_symm_apply, ofProd_symm_levelHom, f, levelHom_ofProd]
      refine Prod.ext (congrArg (ofProd cΨ) (Prod.ext rfl ?_)) rfl
      apply (TrivialLieModule.equiv R P R).injective
      have hr (u v : P) : residuePairing R ℤ L Ψ u v = r * residuePairing R ℤ L Φ u v := by
        rw [← constantTermPairing_degreeDerivation_right,
          ← constantTermPairing_degreeDerivation_right, h, constantTermPairing_smul,
          LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
      simp [hr] }

@[simp]
theorem extendedToProd_extendedLevelHom {r : R} (h : Ψ = r • Φ)
    (x : extendedResidueExtension Φ hΦ hΦs) :
    extendedToProd Ψ hΨ hΨs (extendedLevelHom hΦ hΦs hΨ hΨs h x) =
      (levelHom hΦ hΦs hΨ hΨs h (extendedToProd Φ hΦ hΦs x).1,
        (extendedToProd Φ hΦ hΦs x).2) := by
  simp [extendedLevelHom]

/-- `extendedLevelHom` restricts to `levelHom` on the derived central extension. -/
@[simp]
theorem extendedLevelHom_toExtendedResidueExtension {r : R} (h : Ψ = r • Φ) (x : ofTwoCocycle cΦ) :
    extendedLevelHom hΦ hΦs hΨ hΨs h (toExtendedResidueExtension Φ hΦ hΦs x) =
      toExtendedResidueExtension Ψ hΨ hΨs (levelHom hΦ hΦs hΨ hΨs h x) := by
  apply (extendedToProd Ψ hΨ hΨs).injective
  simp

/-- `extendedLevelHom` fixes every loop mode `tⁿ ⊗ x`. -/
@[simp]
theorem extendedLevelHom_mode {r : R} (h : Ψ = r • Φ) (n : ℤ) (x : L) :
    extendedLevelHom hΦ hΦs hΨ hΨs h (mode Φ hΦ hΦs n x) = mode Ψ hΨ hΨs n x := by
  simp [mode_apply]

/-- `extendedLevelHom` scales the canonical central element by `r`. -/
theorem extendedLevelHom_centralElement {r : R} (h : Ψ = r • Φ) :
    extendedLevelHom hΦ hΦs hΨ hΨs h (toExtendedResidueExtension Φ hΦ hΦs (centralElement cΦ)) =
      r • toExtendedResidueExtension Ψ hΨ hΨs (centralElement cΨ) := by
  rw [extendedLevelHom_toExtendedResidueExtension, levelHom_centralElement, map_smul]

/-- `extendedLevelHom` preserves the degree element `d`. -/
@[simp]
theorem extendedLevelHom_degreeElement {r : R} (h : Ψ = r • Φ) :
    extendedLevelHom hΦ hΦs hΨ hΨs h (degreeElement Φ hΦ hΦs) = degreeElement Ψ hΨ hΨs := by
  apply (extendedToProd Ψ hΨ hΨs).injective
  simp

/-- **Level transport scales the invariant bilinear form by `r`**: for `Ψ = r • Φ`,
`B_Ψ(f x, f y) = r * B_Φ(x, y)`. -/
theorem extendedBilinForm_extendedLevelHom {r : R} (h : Ψ = r • Φ)
    (x y : extendedResidueExtension Φ hΦ hΦs) :
    extendedBilinForm Ψ hΨ hΨs (extendedLevelHom hΦ hΦs hΨ hΨs h x)
        (extendedLevelHom hΦ hΦs hΨ hΨs h y) =
      r * extendedBilinForm Φ hΦ hΦs x y := by
  have hct : constantTermPairing Ψ = r • constantTermPairing Φ := by
    rw [h, constantTermPairing_smul]
  rw [extendedBilinForm_apply_aux, extendedBilinForm_apply_aux, extendedToProd_extendedLevelHom,
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
  left_inv x := by
    apply (extendedToProd Φ hΦ hΦs).injective
    refine Prod.ext ((ofProd cΦ).symm.injective ?_) (by simp)
    simp [smul_smul]
  right_inv y := by
    apply (extendedToProd Ψ hΨ hΨs).injective
    refine Prod.ext ((ofProd cΨ).symm.injective ?_) (by simp)
    simp [smul_smul]

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

/-! ### Universal central extension property of the residue extension -/

section UniversalCentralExtension

variable {K L G : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [LieRing G] [LieAlgebra K G]

private theorem eq_bot_of_central_extension_of_loopAlgebra
    {K L Q : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [LieAlgebra.IsKilling K L] [LieRing Q] [LieAlgebra K Q]
    {Φ : LinearMap.BilinForm K L} (hΦs : Φ.IsSymm)
    (hspan : ∀ Ψ : LinearMap.BilinForm K L, Ψ.lieInvariant L → ∃ t : K, Ψ = t • Φ)
    (πQ : Q →ₗ⁅K⁆ loopAlgebra K ℤ L) (hπQ_surj : Function.Surjective πQ)
    (hker_central : ∀ z ∈ πQ.ker, ∀ y : Q, ⁅y, z⁆ = 0)
    (hQ_perf : (⁅(⊤ : LieIdeal K Q), (⊤ : LieIdeal K Q)⁆ : LieIdeal K Q) = ⊤)
    (Z : LieIdeal K Q) (hZ_le : Z ≤ πQ.ker)
    {cQ : Q} (hcQ_ker : cQ ∈ πQ.ker) (hcQ_not_Z : cQ ∉ Z)
    {ι : Type*} {s : Finset ι} {a : ι → K} {u v : ι → Q}
    (hcQ_sum : cQ = ∑ k ∈ s, a k • ⁅u k, v k⁆)
    (hpair : ∑ k ∈ s, a k * residuePairing K ℤ L Φ (πQ (u k)) (πQ (v k)) ≠ 0) :
    Z = ⊥ := by
  by_contra hZ_ne
  obtain ⟨z₀, hz₀Z, hz₀ne⟩ : ∃ z₀ ∈ Z, z₀ ≠ 0 := by
    by_contra! h
    exact hZ_ne (eq_bot_iff.mpr fun z hz ↦ by simp [h z hz])
  have hz₀_ker : z₀ ∈ πQ.ker := hZ_le hz₀Z
  -- Build a linear form `μ : πQ.ker →ₗ[K] K` killing `cQ` and nonzero at `z₀`.
  let U : Submodule K πQ.ker := K ∙ (⟨cQ, hcQ_ker⟩ : πQ.ker)
  have hz₀_not_U : (⟨z₀, hz₀_ker⟩ : πQ.ker) ∉ U := by
    rw [Submodule.mem_span_singleton]
    rintro ⟨r, hr⟩
    have hr' : r • cQ = z₀ := congrArg Subtype.val hr
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hr'
      exact hz₀ne hr'.symm
    apply hcQ_not_Z
    have : cQ = r⁻¹ • z₀ := by rw [← hr', smul_smul, inv_mul_cancel₀ hr0, one_smul]
    rw [this]
    exact Z.smul_mem r⁻¹ hz₀Z
  have hmk_ne : U.mkQ ⟨z₀, hz₀_ker⟩ ≠ 0 := fun h0 ↦
    hz₀_not_U ((Submodule.Quotient.mk_eq_zero U).mp h0)
  obtain ⟨ν, hν⟩ : ∃ ν : Module.Dual K (πQ.ker ⧸ U), ν (U.mkQ ⟨z₀, hz₀_ker⟩) ≠ 0 := by
    by_contra! h
    exact hmk_ne ((Module.forall_dual_apply_eq_zero_iff K _).mp h)
  let μ : πQ.ker →ₗ[K] K := ν ∘ₗ U.mkQ
  have hμ_cQ : μ ⟨cQ, hcQ_ker⟩ = 0 := by
    change ν (U.mkQ ⟨cQ, hcQ_ker⟩) = 0
    rw [Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero U).mpr (Submodule.mem_span_singleton_self _), map_zero]
  have hμ_z₀ : μ ⟨z₀, hz₀_ker⟩ ≠ 0 := hν
  -- Choose a `K`-linear section `sec` of `πQ` and form the associated 2-cocycle `ω`.
  obtain ⟨sec, hsec⟩ := LinearMap.exists_rightInverse_of_surjective πQ.toLinearMap
    (LinearMap.range_eq_top.mpr hπQ_surj)
  have hsec_apply (p : loopAlgebra K ℤ L) : πQ (sec p) = p :=
    congrArg (fun g : loopAlgebra K ℤ L →ₗ[K] loopAlgebra K ℤ L ↦ g p) hsec
  have hsec_ker (p₁ p₂ : loopAlgebra K ℤ L) : ⁅sec p₁, sec p₂⁆ - sec ⁅p₁, p₂⁆ ∈ πQ.ker := by
    rw [LieHom.mem_ker, map_sub, LieHom.map_lie, hsec_apply, hsec_apply, hsec_apply, sub_self]
  let e := TrivialLieModule.equiv K (loopAlgebra K ℤ L) K
  have hsmul_lie (r : K) (p₁ p₂ : loopAlgebra K ℤ L) : ⁅r • p₁, p₂⁆ = r • ⁅p₁, p₂⁆ :=
    calc ⁅r • p₁, p₂⁆ = -⁅p₂, r • p₁⁆ := (lie_skew (r • p₁) p₂).symm
      _ = -(r • ⁅p₂, p₁⁆) := congrArg Neg.neg (LieAlgebra.lie_smul r p₂ p₁)
      _ = r • (-⁅p₂, p₁⁆) := (smul_neg r ⁅p₂, p₁⁆).symm
      _ = r • ⁅p₁, p₂⁆ := congrArg (r • ·) (lie_skew p₁ p₂)
  let ωB : loopAlgebra K ℤ L →ₗ[K] loopAlgebra K ℤ L →ₗ[K]
      TrivialLieModule K (loopAlgebra K ℤ L) K :=
    LinearMap.mk₂ K (fun p₁ p₂ ↦ e.symm (μ ⟨⁅sec p₁, sec p₂⁆ - sec ⁅p₁, p₂⁆, hsec_ker p₁ p₂⟩))
      (fun p₁ p₂ p₃ ↦ by
        rw [← map_add, ← map_add]
        congr 2
        apply Subtype.ext
        rw [AddMemClass.coe_add]
        dsimp only
        rw [map_add, add_lie, LieRing.add_lie, map_add]
        abel)
      (fun r p₁ p₂ ↦ by
        rw [← map_smul, ← map_smul]
        congr 2
        apply Subtype.ext
        rw [SetLike.val_smul]
        dsimp only
        rw [map_smul, smul_lie, hsmul_lie, map_smul, smul_sub])
      (fun p₁ p₂ p₃ ↦ by
        rw [← map_add, ← map_add]
        congr 2
        apply Subtype.ext
        rw [AddMemClass.coe_add]
        dsimp only
        rw [map_add, lie_add, LieRing.lie_add, map_add]
        abel)
      (fun r p₁ p₂ ↦ by
        rw [← map_smul, ← map_smul]
        congr 2
        apply Subtype.ext
        rw [SetLike.val_smul]
        dsimp only
        rw [map_smul, lie_smul, LieAlgebra.lie_smul r p₁ p₂, map_smul, smul_sub])
  let ω : twoCochain K (loopAlgebra K ℤ L) (TrivialLieModule K (loopAlgebra K ℤ L) K) :=
    ⟨ωB, fun p ↦ by
      change e.symm (μ ⟨⁅sec p, sec p⁆ - sec ⁅p, p⁆, _⟩) = 0
      have h0 : (⟨⁅sec p, sec p⁆ - sec ⁅p, p⁆, hsec_ker p p⟩ : πQ.ker) = 0 :=
        Subtype.ext (by simp)
      rw [h0, map_zero, map_zero]⟩
  have hω_cocycle : ω ∈ twoCocycle K (loopAlgebra K ℤ L)
      (TrivialLieModule K (loopAlgebra K ℤ L) K) := by
    rw [mem_twoCocycle_iff_of_trivial]
    intro p₁ p₂ p₃
    change e.symm (μ ⟨⁅sec p₁, sec ⁅p₂, p₃⁆⁆ - sec ⁅p₁, ⁅p₂, p₃⁆⁆, _⟩) =
      e.symm (μ ⟨⁅sec ⁅p₁, p₂⁆, sec p₃⁆ - sec ⁅⁅p₁, p₂⁆, p₃⁆, _⟩) +
      e.symm (μ ⟨⁅sec p₂, sec ⁅p₁, p₃⁆⁆ - sec ⁅p₂, ⁅p₁, p₃⁆⁆, _⟩)
    rw [← map_add, ← map_add]
    congr 2
    apply Subtype.ext
    have hrep_r (x y z : loopAlgebra K ℤ L) : ⁅sec x, sec ⁅y, z⁆⁆ = ⁅sec x, ⁅sec y, sec z⁆⁆ := by
      have h0 := hker_central (⁅sec y, sec z⁆ - sec ⁅y, z⁆) (hsec_ker y z) (sec x)
      rw [lie_sub, sub_eq_zero] at h0
      exact h0.symm
    have hrep_l (x y z : loopAlgebra K ℤ L) : ⁅sec ⁅x, y⁆, sec z⁆ = ⁅⁅sec x, sec y⁆, sec z⁆ := by
      have h0 := hker_central (⁅sec x, sec y⁆ - sec ⁅x, y⁆) (hsec_ker x y) (sec z)
      rw [← lie_skew, neg_eq_zero, sub_lie, sub_eq_zero] at h0
      exact h0.symm
    rw [AddMemClass.coe_add]
    dsimp only
    rw [hrep_r p₁ p₂ p₃, hrep_l p₁ p₂ p₃, hrep_r p₂ p₁ p₃,
      leibniz_lie (sec p₁) (sec p₂) (sec p₃), LieRing.leibniz_lie p₁ p₂ p₃, map_add]
    abel
  -- Decompose `ω = t • twoCochainOfBilinear Φ + d₁₂ η`.
  have hdecomp : ω ∈ (K ∙ twoCochainOfBilinear K ℤ L Φ hΦs) ⊔
      LinearMap.range (d₁₂ K (loopAlgebra K ℤ L) (TrivialLieModule K (loopAlgebra K ℤ L) K)) := by
    rw [← twoCocycle_eq_span_sup_range_d₁₂ hΦs hspan]
    exact hω_cocycle
  obtain ⟨_, hmem_span, _, ⟨η, rfl⟩, hω_eq⟩ := Submodule.mem_sup.mp hdecomp
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hmem_span
  have hproj_ker (y : Q) : y - sec (πQ y) ∈ πQ.ker := by
    rw [LieHom.mem_ker, map_sub, hsec_apply, sub_self]
  let ψ : Q →ₗ[K] K :=
    { toFun y := μ ⟨y - sec (πQ y), hproj_ker y⟩ + e (η (πQ y))
      map_add' y₁ y₂ := by
        have hsub : (⟨y₁ + y₂ - sec (πQ (y₁ + y₂)), hproj_ker (y₁ + y₂)⟩ : πQ.ker) =
            ⟨y₁ - sec (πQ y₁), hproj_ker y₁⟩ + ⟨y₂ - sec (πQ y₂), hproj_ker y₂⟩ := by
          apply Subtype.ext
          simp only [AddMemClass.coe_add, map_add]
          abel
        rw [hsub, map_add, map_add, map_add, map_add]
        ring
      map_smul' r y := by
        have hsub : (⟨r • y - sec (πQ (r • y)), hproj_ker (r • y)⟩ : πQ.ker) =
            r • ⟨y - sec (πQ y), hproj_ker y⟩ := by
          apply Subtype.ext
          simp only [SetLike.val_smul, map_smul, smul_sub]
        rw [hsub, map_smul, map_smul, map_smul, map_smul]
        simp only [RingHom.id_apply, smul_eq_mul]
        ring }
  have hψ_lie (y₁ y₂ : Q) :
      ψ ⁅y₁, y₂⁆ = t * residuePairing K ℤ L Φ (πQ y₁) (πQ y₂) := by
    have hbra : ⁅y₁, y₂⁆ = ⁅sec (πQ y₁), sec (πQ y₂)⁆ := by
      have h1 := hker_central (y₁ - sec (πQ y₁)) (hproj_ker y₁) y₂
      rw [← lie_skew, neg_eq_zero, sub_lie, sub_eq_zero] at h1
      have h2 := hker_central (y₂ - sec (πQ y₂)) (hproj_ker y₂) (sec (πQ y₁))
      rw [lie_sub, sub_eq_zero] at h2
      exact h1.trans h2
    have hω_eval := congrArg
      (fun c : twoCochain K (loopAlgebra K ℤ L) (TrivialLieModule K (loopAlgebra K ℤ L) K) ↦
        e (c (πQ y₁) (πQ y₂))) hω_eq
    have he_inv (r : K) :
        e ((TrivialLieModule.equiv K (loopAlgebra K ℤ L) K).symm r) = r :=
      e.apply_symm_apply r
    simp only [add_apply_apply, smul_apply_apply, twoCochainOfBilinear_apply_apply,
      d₁₂_apply_apply_ofTrivial, map_add, map_smul, map_neg, he_inv, smul_eq_mul] at hω_eval
    change μ ⟨⁅y₁, y₂⁆ - sec (πQ ⁅y₁, y₂⁆), _⟩ + e (η (πQ ⁅y₁, y₂⁆)) = _
    have heq_sub : (⟨⁅y₁, y₂⁆ - sec (πQ ⁅y₁, y₂⁆), hproj_ker ⁅y₁, y₂⁆⟩ : πQ.ker) =
        ⟨⁅sec (πQ y₁), sec (πQ y₂)⁆ - sec ⁅πQ y₁, πQ y₂⁆, hsec_ker (πQ y₁) (πQ y₂)⟩ := by
      apply Subtype.ext
      change ⁅y₁, y₂⁆ - sec (πQ ⁅y₁, y₂⁆) = ⁅sec (πQ y₁), sec (πQ y₂)⁆ - sec ⁅πQ y₁, πQ y₂⁆
      rw [hbra, LieHom.map_lie, hsec_apply, hsec_apply]
    rw [heq_sub, LieHom.map_lie]
    have hω_val : e (ω (πQ y₁) (πQ y₂)) =
        μ ⟨⁅sec (πQ y₁), sec (πQ y₂)⁆ - sec ⁅πQ y₁, πQ y₂⁆, hsec_ker (πQ y₁) (πQ y₂)⟩ := by
      change e (e.symm _) = _
      exact e.apply_symm_apply _
    rw [hω_val] at hω_eval
    linear_combination -hω_eval
  -- Evaluate `ψ cQ` both directly (`0`) and via `hcQ_sum`, forcing `t = 0`.
  have hψ_cQ_zero : ψ cQ = 0 := by
    change μ ⟨cQ - sec (πQ cQ), _⟩ + e (η (πQ cQ)) = 0
    have hπc : πQ cQ = 0 := hcQ_ker
    have hsub : (⟨cQ - sec (πQ cQ), hproj_ker cQ⟩ : πQ.ker) = ⟨cQ, hcQ_ker⟩ :=
      Subtype.ext (by simp [hπc])
    rw [hsub, hμ_cQ, hπc, map_zero, map_zero, add_zero]
  have hψ_cQ_sum : ψ cQ = t * ∑ k ∈ s, a k * residuePairing K ℤ L Φ (πQ (u k)) (πQ (v k)) := by
    rw [hcQ_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_smul, smul_eq_mul, hψ_lie]
    ring
  have ht0 : t = 0 := (mul_eq_zero.mp (hψ_cQ_sum.symm.trans hψ_cQ_zero)).resolve_right hpair
  have hψ_lie0 (y₁ y₂ : Q) : ψ ⁅y₁, y₂⁆ = 0 := by rw [hψ_lie, ht0, zero_mul]
  -- Since `Q` is perfect, `ψ` vanishes identically on `Q`.
  have hψ_zero : ∀ y : Q, ψ y = 0 := by
    have hle : (↑(⁅(⊤ : LieIdeal K Q), (⊤ : LieIdeal K Q)⁆ : LieIdeal K Q) : Submodule K Q) ≤
        LinearMap.ker ψ := by
      rw [LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span',
        Submodule.span_le]
      rintro _ ⟨x₁, _, x₂, _, rfl⟩
      exact hψ_lie0 x₁ x₂
    intro y
    exact hle (by rw [hQ_perf]; trivial)
  -- Evaluate `ψ z₀ = μ ⟨z₀, hz₀_ker⟩` to obtain a contradiction.
  have hψ_z₀ : ψ z₀ = μ ⟨z₀, hz₀_ker⟩ := by
    change μ ⟨z₀ - sec (πQ z₀), _⟩ + e (η (πQ z₀)) = _
    have hπz : πQ z₀ = 0 := hz₀_ker
    have hsub : (⟨z₀ - sec (πQ z₀), hproj_ker z₀⟩ : πQ.ker) = ⟨z₀, hz₀_ker⟩ :=
      Subtype.ext (by simp [hπz])
    rw [hsub, hπz, map_zero, map_zero, add_zero]
  exact hμ_z₀ (hψ_z₀.symm.trans (hψ_zero z₀))

/-- **Universal central extension property of the residue central extension**:
let `L` be a Lie algebra with nondegenerate Killing form over a field `K` of characteristic zero
whose invariant bilinear forms are all scalar multiples of a symmetric invariant form `Φ`, and let
`c₀ = twoCocycleOfBilinear K ℤ L Φ hΦ hΦs`. Suppose `f : G →ₗ⁅K⁆ ofTwoCocycle c₀` is a surjective
Lie algebra homomorphism from a perfect Lie algebra `G` (`⁅⊤, ⊤⁆ = ⊤`) admitting a central element
`cG` with `f cG = centralElement c₀` that can be expressed as a finite linear combination
`∑ k ∈ s, a k • ⁅u k, v k⁆` whose residue pairing is nonzero. Then `⁅⊤, f.ker⁆ = f.ker`. -/
theorem lie_top_ker_eq_ker_of_surjective_ofTwoCocycle
    {Φ : LinearMap.BilinForm K L} (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)
    (hspan : ∀ Ψ : LinearMap.BilinForm K L, Ψ.lieInvariant L → ∃ t : K, Ψ = t • Φ)
    {f : G →ₗ⁅K⁆ ofTwoCocycle (twoCocycleOfBilinear K ℤ L Φ hΦ hΦs)}
    (hf : Function.Surjective f)
    (hperf : (⁅(⊤ : LieIdeal K G), (⊤ : LieIdeal K G)⁆ : LieIdeal K G) = ⊤)
    {cG : G} (hcG_cent : ∀ y : G, ⁅y, cG⁆ = 0)
    (hcG_map : f cG = centralElement (twoCocycleOfBilinear K ℤ L Φ hΦ hΦs))
    {ι : Type*} {s : Finset ι} {a : ι → K} {u v : ι → G}
    (hcG_sum : cG = ∑ k ∈ s, a k • ⁅u k, v k⁆)
    (hpair : ∑ k ∈ s, a k * residuePairing K ℤ L Φ
      (ofTwoCocycle.proj _ (f (u k))) (ofTwoCocycle.proj _ (f (v k))) ≠ 0) :
    ⁅(⊤ : LieIdeal K G), f.ker⁆ = f.ker := by
  let c₀ := twoCocycleOfBilinear K ℤ L Φ hΦ hΦs
  let I : LieIdeal K G := f.ker
  let J : LieIdeal K G := ⁅(⊤ : LieIdeal K G), I⁆
  let π : G →ₗ⁅K⁆ loopAlgebra K ℤ L := (ofTwoCocycle.proj c₀).comp f
  have hπ_surj : Function.Surjective π := (ofTwoCocycle.proj_surjective c₀).comp hf
  have hker_π (y : G) : y ∈ π.ker ↔ ∃ r : K, y - r • cG ∈ I := by
    rw [LieHom.mem_ker]
    change ofTwoCocycle.proj c₀ (f y) = 0 ↔ _
    constructor
    · intro h0
      set r := TrivialLieModule.equiv K (loopAlgebra K ℤ L) K ((ofProd c₀).symm (f y)).2
      refine ⟨r, LieHom.mem_ker.mpr ?_⟩
      rw [map_sub, map_smul, hcG_map, sub_eq_zero]
      have hdecomp := ofTwoCocycle.ofProd_eq_add_smul_centralElement c₀
        ((ofProd c₀).symm (f y)).1 ((ofProd c₀).symm (f y)).2
      rw [Prod.mk.eta, Equiv.apply_symm_apply] at hdecomp
      have h1 : ((ofProd c₀).symm (f y)).1 = 0 := by rwa [← ofTwoCocycle.proj_apply]
      have h00 : ofProd c₀ (0, 0) = 0 := of_zero c₀
      rw [h1, h00, zero_add] at hdecomp
      exact hdecomp
    · rintro ⟨r, hr⟩
      have hfy : f y = r • centralElement c₀ := by
        have hsub := LieHom.mem_ker.mp hr
        rw [map_sub, map_smul, hcG_map, sub_eq_zero] at hsub
        exact hsub
      rw [hfy, map_smul, ofTwoCocycle.proj_apply, ofTwoCocycle.ofProd_symm_centralElement,
        smul_zero]
  have hJ_le_I : J ≤ I := LieSubmodule.lie_le_right _ _
  have hI_le_ker : I ≤ π.ker := fun y hy ↦ (hker_π y).mpr ⟨0, by simpa using hy⟩
  let q : G →ₗ⁅K⁆ G ⧸ J := J.mkQ
  let πQ : G ⧸ J →ₗ⁅K⁆ loopAlgebra K ℤ L := J.liftQ π (le_trans hJ_le_I hI_le_ker)
  have hπQ_q (y : G) : πQ (q y) = π y := LieHom.congr_fun (J.liftQ_mkQ π _) y
  have hπQ_surj : Function.Surjective πQ := fun p ↦ by
    obtain ⟨y, rfl⟩ := hπ_surj p
    exact ⟨q y, hπQ_q y⟩
  let Z : LieIdeal K (G ⧸ J) := LieIdeal.map q I
  let cQ : G ⧸ J := q cG
  have hker_central : ∀ z ∈ πQ.ker, ∀ y : G ⧸ J, ⁅y, z⁆ = 0 := by
    intro z hz y
    obtain ⟨w, rfl⟩ := J.surjective_mkQ y
    obtain ⟨x, rfl⟩ := J.surjective_mkQ z
    have hx : x ∈ π.ker := by rwa [LieHom.mem_ker, ← hπQ_q]
    obtain ⟨r, hr⟩ := (hker_π x).mp hx
    have hbra : ⁅w, x⁆ ∈ J := by
      have hx_eq : x = (x - r • cG) + r • cG := by abel
      rw [hx_eq, lie_add, lie_smul, hcG_cent w, smul_zero, add_zero]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top w) hr
    rw [← LieHom.map_lie]
    exact LieSubmodule.Quotient.mk_eq_zero'.mpr hbra
  have hQ_perf : (⁅(⊤ : LieIdeal K (G ⧸ J)), (⊤ : LieIdeal K (G ⧸ J))⁆ :
      LieIdeal K (G ⧸ J)) = ⊤ := by
    refine eq_top_iff.mpr fun y _ ↦ ?_
    obtain ⟨w, rfl⟩ := J.surjective_mkQ y
    have hle : (↑(⁅(⊤ : LieIdeal K G), (⊤ : LieIdeal K G)⁆ : LieIdeal K G) : Submodule K G) ≤
        Submodule.comap q.toLinearMap
          (↑(⁅(⊤ : LieIdeal K (G ⧸ J)), (⊤ : LieIdeal K (G ⧸ J))⁆ : LieIdeal K (G ⧸ J))) := by
      rw [LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span',
        Submodule.span_le]
      rintro _ ⟨x₁, _, x₂, _, rfl⟩
      change q ⁅x₁, x₂⁆ ∈ (⁅(⊤ : LieIdeal K (G ⧸ J)), (⊤ : LieIdeal K (G ⧸ J))⁆ :
        LieIdeal K (G ⧸ J))
      rw [LieHom.map_lie]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _)
    exact hle (by rw [hperf]; trivial)
  have hZ_le : Z ≤ πQ.ker := by
    intro z hz
    obtain ⟨⟨x, hxI⟩, rfl⟩ := LieIdeal.mem_map_of_surjective J.surjective_mkQ hz
    rw [LieHom.mem_ker, hπQ_q]
    exact hI_le_ker hxI
  have hcQ_ker : cQ ∈ πQ.ker := by
    rw [LieHom.mem_ker, hπQ_q]
    exact (hker_π cG).mpr ⟨1, by simp⟩
  have hcQ_not_Z : cQ ∉ Z := by
    intro hcZ
    obtain ⟨⟨x, hxI⟩, hxq⟩ := LieIdeal.mem_map_of_surjective J.surjective_mkQ hcZ
    have hdiff : cG - x ∈ J := by
      have h0 : q (cG - x) = 0 := by rw [map_sub, hxq, sub_self]
      exact LieSubmodule.Quotient.mk_eq_zero'.mp h0
    have hcI : cG ∈ I := by
      have : cG = (cG - x) + x := by abel
      rw [this]
      exact add_mem (hJ_le_I hdiff) hxI
    have hc0 : centralElement c₀ = 0 := hcG_map ▸ LieHom.mem_ker.mp hcI
    exact ofTwoCocycle.centralElement_ne_zero c₀ hc0
  have hcQ_sum : cQ = ∑ k ∈ s, a k • ⁅q (u k), q (v k)⁆ := by
    change q cG = _
    rw [hcG_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_smul, LieHom.map_lie]
  have hπ_apply (y : G) : π y = ofTwoCocycle.proj c₀ (f y) := rfl
  have hpair' : ∑ k ∈ s, a k * residuePairing K ℤ L Φ (πQ (q (u k))) (πQ (q (v k))) ≠ 0 := by
    simpa only [hπQ_q, hπ_apply] using hpair
  have hZ : Z = ⊥ := eq_bot_of_central_extension_of_loopAlgebra hΦs hspan πQ hπQ_surj
    hker_central hQ_perf Z hZ_le hcQ_ker hcQ_not_Z hcQ_sum hpair'
  refine le_antisymm hJ_le_I fun y hy ↦ ?_
  have hqy : q y ∈ Z := LieIdeal.mem_map hy
  rw [hZ, LieSubmodule.mem_bot] at hqy
  exact LieSubmodule.Quotient.mk_eq_zero'.mp hqy

end UniversalCentralExtension

end TauCeti.LieAlgebra.LoopAlgebra
