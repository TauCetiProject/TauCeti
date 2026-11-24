/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import TauCeti.NumberTheory.HeckeRing.GL2.Delta0
public import TauCeti.NumberTheory.HeckeRing.GLn.OfIntMatrix

import Mathlib.Data.ZMod.Units
-- the `Γ₀(N)` divisibility and unit-entry lemmas, only inside proofs
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# The monoid `Σ₀(N)` of integral matrices

For a natural number `N`, `Σ₀(N)` is the submonoid of `Matrix (Fin 2) (Fin 2) ℤ` of matrices
`!![a, b; c, d]` with `ad - bc ≠ 0`, `N ∣ c` and `a` a unit modulo `N` (that is, `gcd(a, N) = 1`).
It contains `Γ₀(N)`, every `!![1, b; 0, ℓ]` with `ℓ ≠ 0`, and `!![ℓ, 0; 0, 1]` exactly when `ℓ` is
coprime to `N`. For `N = p` prime it is the monoid `S₀(p)` of Pollack and Stevens.

`Σ₀(N)` is the monoid that acts on the coefficients of modular symbols of level `Γ₀(N)` when Hecke
operators are defined: the operators `T_ℓ` for `ℓ ∤ N` and `U_q` for `q ∣ N` are sums of slashes by
matrices of `Σ₀(N)`, and `Σ₀(p)` acts on spaces of `p`-adic distributions with the weight-`k`
action. It differs from the semigroup `HeckeRing.GL2.Delta0 N` of the Hecke rings in two ways. Its
elements are integral matrices rather than elements of `GL₂(ℚ)`, so that it can act on modules
over rings in which `det` is not invertible. And it admits negative determinants: the involution
`ι = !![-1, 0; 0, 1]`, which splits modular symbols into their plus and minus parts, lies in
`Σ₀(N)` but not in `Δ₀(N)`. The two are related by
`HeckeRing.GL2.mem_Delta0_iff_exists_Sigma0`: `Δ₀(N)` is the image in `GL₂(ℚ)` of the
positive-determinant part of `Σ₀(N)`.

## Main definitions

* `HeckeRing.GL2.Sigma0 N`: the submonoid `Σ₀(N)` of `Matrix (Fin 2) (Fin 2) ℤ`.
* `HeckeRing.GL2.gamma0ToSigma0 N`: the inclusion `Γ₀(N) →* Σ₀(N)`.
* `HeckeRing.GL2.Sigma0.toGL N`: the monoid map `Σ₀(N) →* GL₂(ℚ)`, through which `Σ₀(N)` acts
  on the cusps.

## Main results

* `HeckeRing.GL2.mem_Sigma0_iff`, `HeckeRing.GL2.mem_Sigma0_iff_gcd`: membership, with the
  upper-left condition as a unit of `ZMod N` and as `gcd(a, N) = 1`.
* `HeckeRing.GL2.coe_mem_Sigma0_of_mem_Gamma0`: `Γ₀(N) ⊆ Σ₀(N)`.
* `HeckeRing.GL2.upperTriangular_mem_Sigma0_iff`: membership of upper-triangular matrices, with
  the special cases `HeckeRing.GL2.one_upperTriangular_mem_Sigma0`,
  `HeckeRing.GL2.diagonal_mem_Sigma0_iff` and `HeckeRing.GL2.iota_mem_Sigma0` for the matrices of
  the Hecke operators and of the involution.
* `HeckeRing.GL2.Sigma0.coe_toGL`, `HeckeRing.GL2.Sigma0.toGL_injective`,
  `HeckeRing.GL2.Sigma0.toGL_gamma0ToSigma0`: the map to `GL₂(ℚ)` is the entrywise cast, is
  injective, and restricts to `mapGL ℚ` on `Γ₀(N)`.
* `HeckeRing.GL2.Sigma0.toGL_mem_Delta0_iff`, `HeckeRing.GL2.mem_Delta0_iff_exists_Sigma0`: the
  comparison with `Δ₀(N)`.

## References

* R. Pollack and G. Stevens, *Overconvergent modular symbols and p-adic L-functions*,
  Ann. Sci. Éc. Norm. Supér. (4) **44** (2011), 1--42, §2.1.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing.GLn

open scoped MatrixGroups

namespace HeckeRing.GL2

variable (N : ℕ)

/-- **The monoid `Σ₀(N)`**: integral matrices `!![a, b; c, d]` of nonzero determinant with `N ∣ c`
and `a` a unit modulo `N`. -/
def Sigma0 : Submonoid (Matrix (Fin 2) (Fin 2) ℤ) where
  carrier := {A | A.det ≠ 0 ∧ (N : ℤ) ∣ A 1 0 ∧ IsUnit (A 0 0 : ZMod N)}
  one_mem' := ⟨by simp, by simp, by simp⟩
  mul_mem' {A B} := by
    rintro ⟨hA, hAN, hAu⟩ ⟨hB, hBN, hBu⟩
    refine ⟨by simpa [det_mul] using mul_ne_zero hA hB, ?_, ?_⟩
    · exact dvd_mul_apply_one_zero hAN hBN
    · rw [intCast_mul_apply_zero_zero hBN]
      exact hAu.mul hBu

variable {N}

/-- Membership in `Σ₀(N)`, unfolded. -/
@[simp]
theorem mem_Sigma0_iff {A : Matrix (Fin 2) (Fin 2) ℤ} :
    A ∈ Sigma0 N ↔ A.det ≠ 0 ∧ (N : ℤ) ∣ A 1 0 ∧ IsUnit (A 0 0 : ZMod N) :=
  (Iff.rfl)

/-- Membership in `Σ₀(N)` with the upper-left condition stated as `gcd(a, N) = 1`. -/
theorem mem_Sigma0_iff_gcd {A : Matrix (Fin 2) (Fin 2) ℤ} :
    A ∈ Sigma0 N ↔ A.det ≠ 0 ∧ (N : ℤ) ∣ A 1 0 ∧ Int.gcd (A 0 0) N = 1 := by
  rw [mem_Sigma0_iff, ZMod.isUnit_intCast_iff_isCoprime, isCoprime_comm,
    Int.isCoprime_iff_gcd_eq_one]

/-- An element of `Σ₀(N)` has nonzero determinant. -/
theorem det_ne_zero_of_mem_Sigma0 {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A ∈ Sigma0 N) :
    A.det ≠ 0 :=
  (mem_Sigma0_iff.mp hA).1

/-- **`Γ₀(N) ⊆ Σ₀(N)`.** -/
theorem coe_mem_Sigma0_of_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    (γ : Matrix (Fin 2) (Fin 2) ℤ) ∈ Sigma0 N :=
  ⟨by simp, mem_Gamma0_iff_dvd.mp hγ, isUnit_intCast_apply_zero_zero_of_mem_Gamma0 hγ⟩

variable (N) in
/-- The inclusion `Γ₀(N) →* Σ₀(N)` of `HeckeRing.GL2.coe_mem_Sigma0_of_mem_Gamma0`, sending
`γ` to its underlying integral matrix. -/
def gamma0ToSigma0 : Gamma0 N →* Sigma0 N where
  toFun γ := ⟨γ.val, coe_mem_Sigma0_of_mem_Gamma0 γ.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The matrix of the image of `γ ∈ Γ₀(N)` in `Σ₀(N)` is the matrix of `γ`. -/
@[simp]
theorem coe_gamma0ToSigma0 (γ : Gamma0 N) :
    (gamma0ToSigma0 N γ : Matrix (Fin 2) (Fin 2) ℤ) = ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) :=
  (rfl)

/-- The inclusion `Γ₀(N) →* Σ₀(N)` is injective. -/
theorem gamma0ToSigma0_injective : Function.Injective (gamma0ToSigma0 N) := fun γ δ h ↦
  Subtype.ext <| Subtype.ext <| by
    simpa only [coe_gamma0ToSigma0] using congrArg Subtype.val h

/-- An upper-triangular integral matrix `!![a, b; 0, d]` lies in `Σ₀(N)` exactly when `ad ≠ 0`
and `a` is coprime to `N`. -/
theorem upperTriangular_mem_Sigma0_iff {a b d : ℤ} :
    !![a, b; 0, d] ∈ Sigma0 N ↔ a * d ≠ 0 ∧ Int.gcd a N = 1 := by
  rw [mem_Sigma0_iff_gcd]
  simp

/-- The matrices `!![1, b; 0, ℓ]` with `ℓ ≠ 0`, which appear in the Hecke operators `T_ℓ` and
`U_ℓ`, lie in `Σ₀(N)` for every `N`. -/
theorem one_upperTriangular_mem_Sigma0 (b : ℤ) {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    !![1, b; 0, ℓ] ∈ Sigma0 N :=
  upperTriangular_mem_Sigma0_iff.mpr ⟨by simpa using hℓ, Int.gcd_one_left _⟩

/-- The diagonal matrix `!![ℓ, 0; 0, 1]` with `ℓ ≠ 0`, which appears in the Hecke operator `T_ℓ`,
lies in `Σ₀(N)` exactly when `ℓ` is coprime to `N`. -/
theorem diagonal_mem_Sigma0_iff {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    !![ℓ, 0; 0, 1] ∈ Sigma0 N ↔ Int.gcd ℓ N = 1 := by
  rw [upperTriangular_mem_Sigma0_iff]
  simp [hℓ]

/-- The involution `ι = !![-1, 0; 0, 1]` lies in `Σ₀(N)` for every `N`. -/
theorem iota_mem_Sigma0 : !![-1, 0; 0, 1] ∈ Sigma0 N :=
  upperTriangular_mem_Sigma0_iff.mpr ⟨by simp, by simp⟩

namespace Sigma0

variable (N) in
/-- **The map `Σ₀(N) →* GL₂(ℚ)`**, sending an integral matrix of nonzero determinant to its
entrywise cast. This is the restriction of `HeckeRing.GLn.ofIntMatrix 2` to `Σ₀(N)`, where it is
multiplicative. -/
noncomputable def toGL : Sigma0 N →* GL (Fin 2) ℚ where
  toFun A := ofIntMatrix 2 A
  map_one' := ofIntMatrix_one
  map_mul' A B := ofIntMatrix_mul (det_ne_zero_of_mem_Sigma0 A.property)
      (det_ne_zero_of_mem_Sigma0 B.property)

/-- `Sigma0.toGL N` is `HeckeRing.GLn.ofIntMatrix 2` on the underlying matrix. -/
theorem toGL_apply (A : Sigma0 N) : toGL N A = ofIntMatrix 2 A :=
  (rfl)

/-- The matrix of `Sigma0.toGL N A` is the entrywise cast of `A`. -/
@[simp]
theorem coe_toGL (A : Sigma0 N) :
    (toGL N A : Matrix (Fin 2) (Fin 2) ℚ) = (A : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) :=
  coe_ofIntMatrix (det_ne_zero_of_mem_Sigma0 A.property)

/-- The map `Σ₀(N) →* GL₂(ℚ)` is injective. -/
theorem toGL_injective : Function.Injective (toGL N) := fun A B h ↦
  Subtype.ext <| ofIntMatrix_injOn (det_ne_zero_of_mem_Sigma0 A.property)
    (det_ne_zero_of_mem_Sigma0 B.property) h

/-- On `Γ₀(N)` the map `Σ₀(N) →* GL₂(ℚ)` is the inclusion `mapGL ℚ` of `SL₂(ℤ)`. -/
@[simp]
theorem toGL_gamma0ToSigma0 (γ : Gamma0 N) :
    toGL N (gamma0ToSigma0 N γ) = mapGL ℚ (γ : SL(2, ℤ)) := by
  rw [toGL_apply, coe_gamma0ToSigma0, ofIntMatrix_coe_SL]

/-- The image of `Σ₀(N)` in `GL₂(ℚ)` has integer entries. -/
theorem toGL_mem_intEntries (A : Sigma0 N) : toGL N A ∈ intEntries 2 :=
  ofIntMatrix_mem_intEntries _

/-- The integral matrix of the image of `A ∈ Σ₀(N)` in `GL₂(ℚ)` is `A`. -/
@[simp]
theorem intMatrix_toGL (A : Sigma0 N) :
    intMatrix 2 ⟨toGL N A, toGL_mem_intEntries A⟩ = A :=
  intMatrix_ofIntMatrix (det_ne_zero_of_mem_Sigma0 A.property)

/-- The image of `A ∈ Σ₀(N)` lies in `Δ₀(N)` exactly when `det A > 0`. -/
theorem toGL_mem_Delta0_iff (A : Sigma0 N) :
    toGL N A ∈ Delta0 N ↔ 0 < (A : Matrix (Fin 2) (Fin 2) ℤ).det := by
  obtain ⟨-, hAN, hAu⟩ := A.property
  rw [mem_Delta0_iff, coe_toGL, ← Int.cast_det, Int.cast_pos]
  refine ⟨fun ⟨_, _, h, _⟩ ↦ h, fun h ↦ ⟨A, rfl, h, hAN, hAu⟩⟩

end Sigma0

/-- **`Δ₀(N)` is the image of the positive-determinant part of `Σ₀(N)`.** -/
theorem mem_Delta0_iff_exists_Sigma0 {g : GL (Fin 2) ℚ} :
    g ∈ Delta0 N ↔
      ∃ A : Sigma0 N, 0 < (A : Matrix (Fin 2) (Fin 2) ℤ).det ∧ Sigma0.toGL N A = g := by
  refine ⟨fun hg ↦ ?_, fun ⟨A, hA, hAg⟩ ↦ hAg ▸ (Sigma0.toGL_mem_Delta0_iff A).mpr hA⟩
  obtain ⟨A, hgA, hdet, hAN, hAu⟩ := (mem_Delta0_iff N).mp hg
  have hdetA : 0 < A.det := by rwa [hgA, ← Int.cast_det, Int.cast_pos] at hdet
  exact ⟨⟨A, hdetA.ne', hAN, hAu⟩, hdetA, Units.ext <| by rw [Sigma0.coe_toGL, hgA]⟩

/-- `ι = !![-1, 0; 0, 1]` has determinant `-1`, so its image in `GL₂(ℚ)` is not in `Δ₀(N)`:
`Σ₀(N)` is strictly larger than the integral form of `Δ₀(N)`. -/
theorem toGL_iota_notMem_Delta0 :
    Sigma0.toGL N ⟨!![-1, 0; 0, 1], iota_mem_Sigma0⟩ ∉ Delta0 N := by
  rw [Sigma0.toGL_mem_Delta0_iff]
  simp

end HeckeRing.GL2
