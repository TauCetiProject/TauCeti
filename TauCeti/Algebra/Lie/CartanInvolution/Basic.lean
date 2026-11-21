/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.Algebra.Lie.Subalgebra.Fixed.Basic

import TauCeti.Algebra.Lie.InvariantForm.Positive
import TauCeti.Algebra.Lie.Killing.Basic
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative
import TauCeti.LinearAlgebra.Eigenspace.Semisimple

/-!
# Cartan involutions and the Cartan decomposition of a Lie algebra

An involutive automorphism `θ : L ≃ₗ⁅R⁆ L` of a Lie algebra splits `L` (when `2` is invertible)
into its `+1`-eigenspace `𝔨 = θ.toLieHom.fixedSubalgebra` and its `-1`-eigenspace
`𝔭 = θ.cartanP = ker (θ + 1)`. The bracket satisfies `[𝔨, 𝔨] ⊆ 𝔨`, `[𝔨, 𝔭] ⊆ 𝔭`, and
`[𝔭, 𝔭] ⊆ 𝔨`, and the two summands are orthogonal for the Killing form `B = killingForm R L`.
The twisted bilinear form `θ.cartanForm`, given by `B_θ(x, y) = -B(x, θ y)`, is symmetric and
`θ`-invariant, invariant under every Lie automorphism commuting with `θ`, makes `ad x`
skew-adjoint for `x ∈ 𝔨` and self-adjoint for `x ∈ 𝔭`, and satisfies `B_θ(𝔨, 𝔭) = 0`.

Over a partially ordered commutative ring `R` (in particular any ordered field or `ℝ`), `θ` is a
**Cartan involution** (`LieEquiv.IsCartanInvolution`) when `θ` is involutive and `B_θ` is positive
definite. Positive definiteness of `B_θ` forces `B` to be negative definite on `𝔨`, positive
definite on `𝔭`, and nondegenerate on `L`; hence `L` is automatically Killing, finite-dimensional,
and (over a field) semisimple, and `θ` is uniquely determined by `𝔨` since `𝔭 = 𝔨^{⊥_B}`.
Restricting `B_θ` to `𝔨` gives a positive-definite `ad(𝔨)`-invariant symmetric form (minus `B|_𝔨`),
so by the invariant-form structure theorem (`TauCeti/Algebra/Lie/InvariantForm/Positive.lean`) the
subalgebra `𝔨` is reductive, splits as the `B|_𝔨`-orthogonal direct sum `Z(𝔨) ⊕ [𝔨, 𝔨]`, and has
semisimple derived algebra `[𝔨, 𝔨]` with negative-definite Killing form. Over `ℝ`, self-adjointness
of `ad x` for `x ∈ 𝔭` with respect to the inner product `B_θ` yields diagonalizability of `ad x`
over `ℝ`.

## Main definitions

* `LieEquiv.cartanP`: the `-1`-eigenspace `ker (θ + 1)` of a Lie algebra automorphism `θ`.
* `LieEquiv.cartanForm`: the twisted Killing form `B_θ(x, y) = -killingForm R L x (θ y)`.
* `LieEquiv.IsCartanInvolution`: predicate stating that `θ` is involutive and `θ.cartanForm` is
  positive definite.

## Main results

* `LieEquiv.isCompl_fixedSubalgebra_cartanP`: an involutive automorphism splits `L = 𝔨 ⊕ 𝔭`.
* `LieEquiv.lie_mem_cartanP_of_mem_fixedSubalgebra_of_mem_cartanP` and
  `LieEquiv.lie_mem_fixedSubalgebra_of_mem_cartanP`: the bracket relations `[𝔨, 𝔭] ⊆ 𝔭` and
  `[𝔭, 𝔭] ⊆ 𝔨`.
* `LieEquiv.killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP` and
  `LieEquiv.cartanP_eq_orthogonal_fixedSubalgebra`: `B(𝔨, 𝔭) = 0`, and `𝔭 = 𝔨^{⊥_B}` when `B` is
  nondegenerate, so `θ` is determined by `𝔨` (`LieEquiv.eq_of_fixedSubalgebra_eq`).
* `LieEquiv.cartanForm_isSymm`, `LieEquiv.cartanForm_apply_apply`, and
  `LieEquiv.cartanForm_apply_of_commute`: symmetry, `θ`-orthogonality, and invariance of `B_θ`
  under automorphisms commuting with `θ`.
* `LieEquiv.isSkewAdjoint_cartanForm_ad` and `LieEquiv.isSelfAdjoint_cartanForm_ad`: `ad x` is
  `B_θ`-skew-adjoint for `x ∈ 𝔨` and `B_θ`-self-adjoint for `x ∈ 𝔭`.
* `LieEquiv.IsCartanInvolution.isKilling`, `LieEquiv.IsCartanInvolution.finite`, and
  `LieEquiv.IsCartanInvolution.isSemisimple`: existence of a Cartan involution forces `L` to be
  Killing, finite, and semisimple.
* `LieEquiv.IsCartanInvolution.hasCentralRadical_fixedSubalgebra`,
  `LieEquiv.IsCartanInvolution.isCompl_center_derivedSeries_fixedSubalgebra`,
  `LieEquiv.IsCartanInvolution.isSemisimple_derivedSeries_fixedSubalgebra`, and
  `LieEquiv.IsCartanInvolution.killingForm_derivedSeries_fixedSubalgebra_self_neg`: reductivity
  and compact-type structure of the fixed subalgebra `𝔨`.
* `LieEquiv.IsCartanInvolution.iSup_eigenspace_ad_eq_top` and
  `LieEquiv.IsCartanInvolution.isSemisimple_ad`: over `ℝ`, `ad x` is diagonalizable for every
  `x ∈ 𝔭`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, §2.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Academic Press, 1978,
  Chapter III, §7.
-/

public section

open LieAlgebra

namespace LieEquiv

section Involutive

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L']

/-- The `-1`-eigenspace `𝔭 = ker (θ + 1)` of a Lie algebra automorphism `θ`. -/
def cartanP (θ : L ≃ₗ⁅R⁆ L) : Submodule R L :=
  LinearMap.ker ((θ : L →ₗ[R] L) + LinearMap.id)

/-- Membership in `θ.cartanP` is the `-1`-eigenvector equation `θ x = -x`. -/
@[simp]
theorem mem_cartanP (θ : L ≃ₗ⁅R⁆ L) {x : L} : x ∈ θ.cartanP ↔ θ x = -x := by
  simp only [cartanP, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply,
    LinearEquiv.coe_coe, coe_toLinearEquiv, add_eq_zero_iff_eq_neg]

/-- `θ.cartanP` is the `(-1)`-eigenspace of `θ` regarded as an endomorphism of `L`. -/
theorem cartanP_eq_eigenspace (θ : L ≃ₗ⁅R⁆ L) :
    θ.cartanP = Module.End.eigenspace (θ : L →ₗ[R] L) (-1) := by
  ext x
  simp

/-- The underlying submodule of `θ.toLieHom.fixedSubalgebra` is the `1`-eigenspace of `θ`. -/
theorem fixedSubalgebra_toSubmodule_eq_eigenspace (θ : L ≃ₗ⁅R⁆ L) :
    θ.toLieHom.fixedSubalgebra.toSubmodule = Module.End.eigenspace (θ : L →ₗ[R] L) 1 := by
  ext x
  simp

/-- The underlying submodule of `θ.toLieHom.fixedSubalgebra` is `ker (θ - 1)`. -/
theorem fixedSubalgebra_toSubmodule_eq_ker (θ : L ≃ₗ⁅R⁆ L) :
    θ.toLieHom.fixedSubalgebra.toSubmodule = LinearMap.ker ((θ : L →ₗ[R] L) - LinearMap.id) := by
  ext x
  simp [sub_eq_zero]

/-- The `-1`-eigenspace of the identity automorphism is `⊥` when `2` is invertible. -/
@[simp]
theorem cartanP_refl [Invertible (2 : R)] :
    (LieEquiv.refl : L ≃ₗ⁅R⁆ L).cartanP = ⊥ := by
  ext x
  simp only [mem_cartanP, refl_apply, Submodule.mem_bot]
  constructor
  · intro hx
    have h2 : (2 : R) • x = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp hx
    simpa using congrArg ((⅟2 : R) • ·) h2
  · rintro rfl
    simp

/-- An involutive Lie automorphism is its own inverse. -/
theorem symm_eq_self_of_involutive {θ : L ≃ₗ⁅R⁆ L} (hθ : Function.Involutive θ) :
    θ.symm = θ :=
  LieEquiv.ext fun x ↦ θ.symm_apply_eq.mpr (hθ x).symm

/-- An intertwining Lie equivalence maps `θ.cartanP` onto `θ'.cartanP`. -/
theorem map_cartanP (e : L ≃ₗ⁅R⁆ L') {θ : L ≃ₗ⁅R⁆ L} {θ' : L' ≃ₗ⁅R⁆ L'}
    (h : ∀ x, θ' (e x) = e (θ x)) :
    θ.cartanP.map (e : L →ₗ[R] L') = θ'.cartanP := by
  ext y
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_cartanP] at hx ⊢
    simp only [LinearEquiv.coe_coe, coe_toLinearEquiv, h, hx, map_neg]
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [mem_cartanP] at hy ⊢
    apply e.injective
    simp only [coe_toLieHom]
    rw [← h, e.apply_symm_apply, hy, map_neg, e.apply_symm_apply]

/-- `[𝔨, 𝔭] ⊆ 𝔭`: bracketing a fixed vector with a `-1`-eigenvector lands in `cartanP`. -/
theorem lie_mem_cartanP_of_mem_fixedSubalgebra_of_mem_cartanP (θ : L ≃ₗ⁅R⁆ L) {x y : L}
    (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hy : y ∈ θ.cartanP) :
    ⁅x, y⁆ ∈ θ.cartanP := by
  rw [mem_cartanP] at hy ⊢
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom] at hx
  rw [map_lie, hx, hy, lie_neg]

/-- `[𝔭, 𝔨] ⊆ 𝔭`: bracketing a `-1`-eigenvector with a fixed vector lands in `cartanP`. -/
theorem lie_mem_cartanP_of_mem_cartanP_of_mem_fixedSubalgebra (θ : L ≃ₗ⁅R⁆ L) {x y : L}
    (hx : x ∈ θ.cartanP) (hy : y ∈ θ.toLieHom.fixedSubalgebra) :
    ⁅x, y⁆ ∈ θ.cartanP := by
  rw [← lie_skew]
  exact neg_mem (θ.lie_mem_cartanP_of_mem_fixedSubalgebra_of_mem_cartanP hy hx)

/-- `[𝔭, 𝔭] ⊆ 𝔨`: bracketing two `-1`-eigenvectors lands in the fixed subalgebra. -/
theorem lie_mem_fixedSubalgebra_of_mem_cartanP (θ : L ≃ₗ⁅R⁆ L) {x y : L}
    (hx : x ∈ θ.cartanP) (hy : y ∈ θ.cartanP) :
    ⁅x, y⁆ ∈ θ.toLieHom.fixedSubalgebra := by
  rw [mem_cartanP] at hx hy
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom, map_lie, hx, hy, neg_lie, lie_neg, neg_neg]

section InvertibleTwo

variable [Invertible (2 : R)]

/-- The `+1`-eigenspace projection `x ↦ ⅟2 • (x + θ x)` of an involutive automorphism lands in
the fixed subalgebra. -/
theorem half_add_apply_mem_fixedSubalgebra {θ : L ≃ₗ⁅R⁆ L} (hθ : Function.Involutive θ) (x : L) :
    (⅟2 : R) • (x + θ x) ∈ θ.toLieHom.fixedSubalgebra := by
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom, map_smul, map_add, hθ x, add_comm]

/-- The `-1`-eigenspace projection `x ↦ ⅟2 • (x - θ x)` of an involutive automorphism lands in
`cartanP`. -/
theorem half_sub_apply_mem_cartanP {θ : L ≃ₗ⁅R⁆ L} (hθ : Function.Involutive θ) (x : L) :
    (⅟2 : R) • (x - θ x) ∈ θ.cartanP := by
  rw [mem_cartanP, map_smul, map_sub, hθ x, ← smul_neg, neg_sub]

/-- Every vector decomposes as `⅟2 • (x + θ x) + ⅟2 • (x - θ x)`. -/
theorem half_add_apply_add_half_sub_apply (θ : L ≃ₗ⁅R⁆ L) (x : L) :
    (⅟2 : R) • (x + θ x) + (⅟2 : R) • (x - θ x) = x := by
  rw [← smul_add, add_add_sub_cancel, ← two_smul R, invOf_smul_smul]

/-- **Eigenspace decomposition of an involutive Lie automorphism**: when `2` is invertible, `L` is
the direct sum of the fixed subalgebra `𝔨` and the `-1`-eigenspace `𝔭`. -/
theorem isCompl_fixedSubalgebra_cartanP {θ : L ≃ₗ⁅R⁆ L} (hθ : Function.Involutive θ) :
    IsCompl θ.toLieHom.fixedSubalgebra.toSubmodule θ.cartanP := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxk hxp
    rw [LieSubalgebra.mem_toSubmodule, LieHom.mem_fixedSubalgebra, coe_toLieHom] at hxk
    rw [mem_cartanP] at hxp
    have h2 : (2 : R) • x = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp (hxk.symm.trans hxp)
    simpa using congrArg ((⅟2 : R) • ·) h2
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    exact Submodule.mem_sup.mpr ⟨_, half_add_apply_mem_fixedSubalgebra hθ x,
      _, half_sub_apply_mem_cartanP hθ x, θ.half_add_apply_add_half_sub_apply x⟩

/-- The fixed subalgebra `𝔨` and the `-1`-eigenspace `𝔭` are orthogonal for the Killing form:
`B(𝔨, 𝔭) = 0`. -/
theorem killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP (θ : L ≃ₗ⁅R⁆ L) {x y : L}
    (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hy : y ∈ θ.cartanP) :
    killingForm R L x y = 0 := by
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom] at hx
  rw [mem_cartanP] at hy
  have hneg : killingForm R L x y = -killingForm R L x y := by
    calc
      killingForm R L x y = killingForm R L (θ x) (θ y) := (killingForm_of_equiv_apply θ x y).symm
      _ = killingForm R L x (-y) := by rw [hx, hy]
      _ = -killingForm R L x y := by rw [map_neg]
  have h2 : (2 : R) * killingForm R L x y = 0 := by
    rw [two_mul]
    exact eq_neg_iff_add_eq_zero.mp hneg
  simpa using congrArg ((⅟2 : R) * ·) h2

/-- Symmetric form of `B(𝔨, 𝔭) = 0`: `B(𝔭, 𝔨) = 0`. -/
theorem killingForm_eq_zero_of_mem_cartanP_of_mem_fixedSubalgebra (θ : L ≃ₗ⁅R⁆ L) {x y : L}
    (hx : x ∈ θ.cartanP) (hy : y ∈ θ.toLieHom.fixedSubalgebra) :
    killingForm R L x y = 0 := by
  rw [LieModule.traceForm_comm]
  exact θ.killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP hy hx

/-- When the Killing form is nondegenerate, the `-1`-eigenspace `𝔭` of an involutive automorphism
is the Killing orthogonal complement of its fixed subalgebra `𝔨`. -/
theorem cartanP_eq_orthogonal_fixedSubalgebra {θ : L ≃ₗ⁅R⁆ L} (hθ : Function.Involutive θ)
    (hnd : (killingForm R L).Nondegenerate) :
    θ.cartanP = (killingForm R L).orthogonal θ.toLieHom.fixedSubalgebra.toSubmodule := by
  refine le_antisymm ?_ ?_
  · intro y hy
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    exact θ.killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP hx hy
  · intro y hy
    set k : L := (⅟2 : R) • (y + θ y)
    set p : L := (⅟2 : R) • (y - θ y)
    have hk : k ∈ θ.toLieHom.fixedSubalgebra := half_add_apply_mem_fixedSubalgebra hθ y
    have hp : p ∈ θ.cartanP := half_sub_apply_mem_cartanP hθ y
    have hkp : k + p = y := θ.half_add_apply_add_half_sub_apply y
    have hk0 : k = 0 := by
      apply hnd.1
      intro z
      set kz : L := (⅟2 : R) • (z + θ z)
      set pz : L := (⅟2 : R) • (z - θ z)
      have hkz : kz ∈ θ.toLieHom.fixedSubalgebra := half_add_apply_mem_fixedSubalgebra hθ z
      have hpz : pz ∈ θ.cartanP := half_sub_apply_mem_cartanP hθ z
      have hkzpz : kz + pz = z := θ.half_add_apply_add_half_sub_apply z
      have hkz_k : killingForm R L k kz = 0 := by
        have hykz : killingForm R L kz y = 0 :=
          (LinearMap.BilinForm.mem_orthogonal_iff.mp hy) kz hkz
        have hpkz : killingForm R L kz p = 0 :=
          θ.killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP hkz hp
        rw [← hkp, map_add, hpkz, add_zero] at hykz
        rwa [LieModule.traceForm_comm]
      have hpz_k : killingForm R L k pz = 0 :=
        θ.killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP hk hpz
      rw [← hkzpz, map_add, hkz_k, hpz_k, add_zero]
    rw [← hkp, hk0, zero_add]
    exact hp

/-- **Uniqueness from the fixed subalgebra.** On a Lie algebra with nondegenerate Killing form
(and `2` invertible), an involutive automorphism is uniquely determined by its fixed subalgebra. -/
theorem eq_of_fixedSubalgebra_eq {θ₁ θ₂ : L ≃ₗ⁅R⁆ L} (h₁ : Function.Involutive θ₁)
    (h₂ : Function.Involutive θ₂) (hnd : (killingForm R L).Nondegenerate)
    (hK : θ₁.toLieHom.fixedSubalgebra = θ₂.toLieHom.fixedSubalgebra) :
    θ₁ = θ₂ := by
  have hP : θ₁.cartanP = θ₂.cartanP := by
    rw [cartanP_eq_orthogonal_fixedSubalgebra h₁ hnd, cartanP_eq_orthogonal_fixedSubalgebra h₂ hnd,
      hK]
  refine LieEquiv.ext fun x ↦ ?_
  have hk1 : (⅟2 : R) • (x + θ₁ x) ∈ θ₁.toLieHom.fixedSubalgebra :=
    half_add_apply_mem_fixedSubalgebra h₁ x
  have hk2 : (⅟2 : R) • (x + θ₁ x) ∈ θ₂.toLieHom.fixedSubalgebra := hK ▸ hk1
  have hp1 : (⅟2 : R) • (x - θ₁ x) ∈ θ₁.cartanP := half_sub_apply_mem_cartanP h₁ x
  have hp2 : (⅟2 : R) • (x - θ₁ x) ∈ θ₂.cartanP := hP ▸ hp1
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom] at hk1 hk2
  rw [mem_cartanP] at hp1 hp2
  rw [← θ₁.half_add_apply_add_half_sub_apply x, map_add, map_add, hk1, hk2, hp1, hp2]

end InvertibleTwo

/-! ### The twisted Killing form `B_θ(x, y) = -B(x, θ y)` -/

/-- The Cartan bilinear form `B_θ(x, y) = -B(x, θ y)` associated to a Lie automorphism `θ`. -/
noncomputable def cartanForm (θ : L ≃ₗ⁅R⁆ L) : LinearMap.BilinForm R L :=
  -((killingForm R L).compRight (θ : L →ₗ[R] L))

/-- Pointwise evaluation of the Cartan bilinear form: `B_θ(x, y) = -B(x, θ y)`. -/
@[simp]
theorem cartanForm_apply (θ : L ≃ₗ⁅R⁆ L) (x y : L) :
    θ.cartanForm x y = -killingForm R L x (θ y) := by
  simp [cartanForm]

/-- The Cartan form of the identity automorphism is minus the Killing form. -/
@[simp]
theorem cartanForm_refl :
    (LieEquiv.refl : L ≃ₗ⁅R⁆ L).cartanForm = -killingForm R L := by
  ext x y
  simp

/-- The Cartan bilinear form of an involutive automorphism is symmetric. -/
theorem cartanForm_isSymm {θ : L ≃ₗ⁅R⁆ L} (hθ : Function.Involutive θ) :
    θ.cartanForm.IsSymm := by
  refine ⟨fun x y ↦ ?_⟩
  simp only [cartanForm_apply, neg_inj]
  calc
    killingForm R L x (θ y) = killingForm R L (θ x) (θ (θ y)) :=
      (killingForm_of_equiv_apply θ x (θ y)).symm
    _ = killingForm R L (θ x) y := by rw [hθ y]
    _ = killingForm R L y (θ x) := LieModule.traceForm_comm R L L (θ x) y

/-- Every Lie automorphism `θ` preserves its own Cartan bilinear form:
`B_θ(θ x, θ y) = B_θ(x, y)`. -/
theorem cartanForm_apply_apply (θ : L ≃ₗ⁅R⁆ L) (x y : L) :
    θ.cartanForm (θ x) (θ y) = θ.cartanForm x y := by
  simp only [cartanForm_apply, killingForm_of_equiv_apply]

/-- An intertwining Lie equivalence is an isometry between the corresponding Cartan forms. -/
theorem cartanForm_map_map (e : L ≃ₗ⁅R⁆ L') {θ : L ≃ₗ⁅R⁆ L} {θ' : L' ≃ₗ⁅R⁆ L'}
    (h : ∀ x, θ' (e x) = e (θ x)) (x y : L) :
    θ'.cartanForm (e x) (e y) = θ.cartanForm x y := by
  simp only [cartanForm_apply, h, killingForm_of_equiv_apply]

/-- Every Lie automorphism commuting with `θ` preserves `θ.cartanForm`. -/
theorem cartanForm_apply_of_commute {θ φ : L ≃ₗ⁅R⁆ L} (h : ∀ x, θ (φ x) = φ (θ x)) (x y : L) :
    θ.cartanForm (φ x) (φ y) = θ.cartanForm x y :=
  cartanForm_map_map φ h x y

/-- On `𝔨` in the right argument, `B_θ(x, y) = -B(x, y)`. -/
theorem cartanForm_apply_of_mem_fixedSubalgebra_right (θ : L ≃ₗ⁅R⁆ L) {x y : L}
    (hy : y ∈ θ.toLieHom.fixedSubalgebra) :
    θ.cartanForm x y = -killingForm R L x y := by
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom] at hy
  simp [hy]

/-- On `𝔭` in the right argument, `B_θ(x, y) = B(x, y)`. -/
theorem cartanForm_apply_of_mem_cartanP_right (θ : L ≃ₗ⁅R⁆ L) {x y : L} (hy : y ∈ θ.cartanP) :
    θ.cartanForm x y = killingForm R L x y := by
  rw [mem_cartanP] at hy
  simp [hy]

/-- `𝔨` and `𝔭` are orthogonal for `B_θ` when `2` is invertible. -/
theorem cartanForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP [Invertible (2 : R)]
    (θ : L ≃ₗ⁅R⁆ L) {x y : L} (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hy : y ∈ θ.cartanP) :
    θ.cartanForm x y = 0 := by
  rw [θ.cartanForm_apply_of_mem_cartanP_right hy]
  exact θ.killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP hx hy

/-- Symmetric form of `B_θ(𝔨, 𝔭) = 0`: `B_θ(𝔭, 𝔨) = 0`. -/
theorem cartanForm_eq_zero_of_mem_cartanP_of_mem_fixedSubalgebra [Invertible (2 : R)]
    (θ : L ≃ₗ⁅R⁆ L) {x y : L} (hx : x ∈ θ.cartanP) (hy : y ∈ θ.toLieHom.fixedSubalgebra) :
    θ.cartanForm x y = 0 := by
  rw [θ.cartanForm_apply_of_mem_fixedSubalgebra_right hy,
    θ.killingForm_eq_zero_of_mem_cartanP_of_mem_fixedSubalgebra hx hy, neg_zero]

/-- For an involutive automorphism `θ`, the `B_θ`-adjoint of `ad x` is `-ad (θ x)`. -/
theorem isAdjointPair_cartanForm_ad {θ : L ≃ₗ⁅R⁆ L} (hθ : Function.Involutive θ) (x : L) :
    LinearMap.IsAdjointPair θ.cartanForm θ.cartanForm (ad R L x) (-ad R L (θ x)) := by
  intro y z
  simp only [cartanForm_apply, ad_apply, Pi.neg_apply, map_neg, neg_neg]
  have h1 : killingForm R L ⁅x, y⁆ (θ z) = -killingForm R L y ⁅x, θ z⁆ := by
    rw [← lie_skew x y, map_neg, LinearMap.neg_apply, LieModule.traceForm_apply_lie_apply]
  have h2 : ⁅x, θ z⁆ = θ ⁅θ x, z⁆ := by
    rw [map_lie, hθ x]
  rw [h1, neg_neg, h2]

/-- For `x ∈ 𝔨`, `ad x` is skew-adjoint with respect to `B_θ`. -/
theorem isSkewAdjoint_cartanForm_ad (θ : L ≃ₗ⁅R⁆ L) {x : L}
    (hx : x ∈ θ.toLieHom.fixedSubalgebra) :
    θ.cartanForm.IsSkewAdjoint (ad R L x) := by
  intro y z
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom] at hx
  simp only [cartanForm_apply, ad_apply, Pi.neg_apply, map_neg, neg_neg]
  have h1 : killingForm R L ⁅x, y⁆ (θ z) = -killingForm R L y ⁅x, θ z⁆ := by
    rw [← lie_skew x y, map_neg, LinearMap.neg_apply, LieModule.traceForm_apply_lie_apply]
  rw [h1, neg_neg, map_lie, hx]

/-- For `x ∈ 𝔨`, `ad x` lies in the `B_θ`-skew-adjoint submodule. -/
theorem ad_mem_skewAdjointSubmodule_cartanForm (θ : L ≃ₗ⁅R⁆ L) {x : L}
    (hx : x ∈ θ.toLieHom.fixedSubalgebra) :
    ad R L x ∈ θ.cartanForm.skewAdjointSubmodule := by
  intro y z
  have h := θ.isSkewAdjoint_cartanForm_ad hx y z
  simp only [LinearMap.neg_apply, Pi.neg_apply, map_neg] at h ⊢
  exact h

/-- For `x ∈ 𝔭`, `ad x` is self-adjoint with respect to `B_θ`. -/
theorem isSelfAdjoint_cartanForm_ad (θ : L ≃ₗ⁅R⁆ L) {x : L} (hx : x ∈ θ.cartanP) :
    θ.cartanForm.IsSelfAdjoint (ad R L x) := by
  intro y z
  rw [mem_cartanP] at hx
  simp only [cartanForm_apply, ad_apply]
  have h1 : killingForm R L ⁅x, y⁆ (θ z) = -killingForm R L y ⁅x, θ z⁆ := by
    rw [← lie_skew x y, map_neg, LinearMap.neg_apply, LieModule.traceForm_apply_lie_apply]
  have h2 : θ ⁅x, z⁆ = -⁅x, θ z⁆ := by
    rw [map_lie, hx, neg_lie]
  rw [h1, neg_neg, h2, map_neg, neg_neg]

/-- For `x ∈ 𝔭`, `ad x` lies in the `B_θ`-self-adjoint submodule. -/
theorem ad_mem_selfAdjointSubmodule_cartanForm (θ : L ≃ₗ⁅R⁆ L) {x : L} (hx : x ∈ θ.cartanP) :
    ad R L x ∈ θ.cartanForm.selfAdjointSubmodule :=
  θ.isSelfAdjoint_cartanForm_ad hx

/-- The restriction of `B_θ` to `𝔨` equals minus the restriction of the Killing form to `𝔨`. -/
theorem cartanForm_compl₁₂_fixedSubalgebra_eq (θ : L ≃ₗ⁅R⁆ L) :
    θ.cartanForm.compl₁₂ θ.toLieHom.fixedSubalgebra.incl.toLinearMap
        θ.toLieHom.fixedSubalgebra.incl.toLinearMap =
      -((killingForm R L).compl₁₂ θ.toLieHom.fixedSubalgebra.incl.toLinearMap
        θ.toLieHom.fixedSubalgebra.incl.toLinearMap) := by
  ext x y
  simp [θ.cartanForm_apply_of_mem_fixedSubalgebra_right y.2]

/-- The restriction of `B_θ` to `𝔨` is `ad(𝔨)`-invariant. -/
theorem lieInvariant_cartanForm_fixedSubalgebra (θ : L ≃ₗ⁅R⁆ L) :
    LinearMap.BilinForm.lieInvariant θ.toLieHom.fixedSubalgebra
      (θ.cartanForm.compl₁₂ θ.toLieHom.fixedSubalgebra.incl.toLinearMap
        θ.toLieHom.fixedSubalgebra.incl.toLinearMap) := by
  rw [cartanForm_compl₁₂_fixedSubalgebra_eq]
  intro x y z
  have h := (LieModule.traceForm_lieInvariant R L L).compl₁₂ θ.toLieHom.fixedSubalgebra.incl x y z
  simp only [LinearMap.neg_apply]
  exact congrArg Neg.neg h

end Involutive

/-! ### Cartan involutions -/

section CartanInvolution

variable {R L L' : Type*} [CommRing R] [PartialOrder R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

/-- A **Cartan involution** of a Lie algebra `L` over an ordered ring `R`: an involutive Lie
algebra automorphism `θ` whose Cartan form `B_θ(x, y) = -B(x, θ y)` is positive definite. -/
def IsCartanInvolution (θ : L ≃ₗ⁅R⁆ L) : Prop :=
  Function.Involutive θ ∧ θ.cartanForm.toQuadraticMap.PosDef

/-- Unfolded characterization of a Cartan involution. -/
theorem isCartanInvolution_iff (θ : L ≃ₗ⁅R⁆ L) :
    θ.IsCartanInvolution ↔
      Function.Involutive θ ∧ ∀ x : L, x ≠ 0 → 0 < -killingForm R L x (θ x) := by
  simp [IsCartanInvolution, QuadraticMap.PosDef]

/-- Transport of `IsCartanInvolution` along an intertwining Lie equivalence. -/
theorem isCartanInvolution_iff_of_intertwine (e : L ≃ₗ⁅R⁆ L') {θ : L ≃ₗ⁅R⁆ L} {θ' : L' ≃ₗ⁅R⁆ L'}
    (h : ∀ x, θ' (e x) = e (θ x)) :
    θ'.IsCartanInvolution ↔ θ.IsCartanInvolution := by
  constructor
  · rintro ⟨hinv, hpos⟩
    refine ⟨fun x ↦ e.injective ?_, fun x hx ↦ ?_⟩
    · simp only [coe_toLieHom]
      rw [← h, ← h, hinv (e x)]
    · rw [LinearMap.BilinMap.toQuadraticMap_apply, ← cartanForm_map_map e h x x]
      exact hpos (e x) (by simpa using hx)
  · rintro ⟨hinv, hpos⟩
    refine ⟨fun y ↦ ?_, fun y hy ↦ ?_⟩
    · obtain ⟨x, rfl⟩ := e.surjective y
      simp only [coe_toLieHom]
      rw [h, h, hinv x]
    · obtain ⟨x, rfl⟩ := e.surjective y
      simp only [coe_toLieHom, LinearMap.BilinMap.toQuadraticMap_apply]
      rw [cartanForm_map_map e h x x]
      exact hpos x (fun hx ↦ hy (by simp [hx]))

/-- Conjugating a Lie automorphism by a Lie equivalence preserves the Cartan-involution
property. -/
theorem isCartanInvolution_conj (e : L ≃ₗ⁅R⁆ L') (θ : L ≃ₗ⁅R⁆ L) :
    ((e.symm.trans θ).trans e).IsCartanInvolution ↔ θ.IsCartanInvolution :=
  isCartanInvolution_iff_of_intertwine e fun x ↦ by simp

namespace IsCartanInvolution

variable {θ : L ≃ₗ⁅R⁆ L}

/-- A Cartan involution is involutive. -/
theorem involutive (hθ : θ.IsCartanInvolution) : Function.Involutive θ :=
  hθ.1

/-- The Cartan form of a Cartan involution is positive definite. -/
theorem posDef_cartanForm (hθ : θ.IsCartanInvolution) : θ.cartanForm.toQuadraticMap.PosDef :=
  hθ.2

/-- `B_θ(x, x) > 0` for every nonzero `x`. -/
theorem cartanForm_self_pos (hθ : θ.IsCartanInvolution) {x : L} (hx : x ≠ 0) :
    0 < θ.cartanForm x x :=
  hθ.2 x hx

/-- `B_θ(x, x) ≥ 0` for every `x`. -/
theorem cartanForm_self_nonneg (hθ : θ.IsCartanInvolution) (x : L) :
    0 ≤ θ.cartanForm x x :=
  hθ.2.nonneg x

/-- The Cartan form of a Cartan involution is symmetric. -/
theorem cartanForm_isSymm (hθ : θ.IsCartanInvolution) : θ.cartanForm.IsSymm :=
  θ.cartanForm_isSymm hθ.1

/-- A Cartan involution is its own inverse. -/
theorem symm_eq (hθ : θ.IsCartanInvolution) : θ.symm = θ :=
  θ.symm_eq_self_of_involutive hθ.1

/-- The Cartan form of a Cartan involution is nondegenerate. -/
theorem cartanForm_nondegenerate (hθ : θ.IsCartanInvolution) : θ.cartanForm.Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_of_anisotropic θ.cartanForm hθ.2.anisotropic

/-- The Killing form is negative definite on the fixed subalgebra `𝔨`. -/
theorem killingForm_self_neg_of_mem_fixedSubalgebra [IsOrderedAddMonoid R]
    (hθ : θ.IsCartanInvolution) {x : L} (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hx0 : x ≠ 0) :
    killingForm R L x x < 0 := by
  have hpos := hθ.cartanForm_self_pos hx0
  rw [θ.cartanForm_apply_of_mem_fixedSubalgebra_right hx] at hpos
  exact neg_pos.mp hpos

/-- The Killing form is positive definite on the `-1`-eigenspace `𝔭`. -/
theorem killingForm_self_pos_of_mem_cartanP (hθ : θ.IsCartanInvolution) {x : L}
    (hx : x ∈ θ.cartanP) (hx0 : x ≠ 0) :
    0 < killingForm R L x x := by
  simpa [θ.cartanForm_apply_of_mem_cartanP_right hx] using hθ.cartanForm_self_pos hx0

/-- Positive definiteness of `B_θ` forces the Killing form to be nondegenerate. -/
theorem killingForm_nondegenerate (hθ : θ.IsCartanInvolution) :
    (killingForm R L).Nondegenerate := by
  refine (LieModule.traceForm_isSymm R L L).isRefl.nondegenerate_iff_separatingLeft.mpr ?_
  intro x hx
  by_contra hx0
  have hpos := hθ.cartanForm_self_pos hx0
  have hzero : θ.cartanForm x x = 0 := by
    simp [cartanForm_apply, hx (θ x)]
  exact hpos.ne' hzero

/-- A Lie algebra admitting a Cartan involution has nondegenerate Killing form (`IsKilling`). -/
theorem isKilling (hθ : θ.IsCartanInvolution) : LieAlgebra.IsKilling R L :=
  TauCeti.isKilling_of_killingForm_nondegenerate R L hθ.killingForm_nondegenerate

/-- A Lie algebra admitting a Cartan involution is automatically finite over the base ring. -/
theorem finite (hθ : θ.IsCartanInvolution) : Module.Finite R L :=
  have := hθ.isKilling
  TauCeti.finite_of_isKilling (R := R) (L := L)

/-- The Cartan decomposition `L = 𝔨 ⊕ 𝔭` for a Cartan involution. -/
theorem isCompl_fixedSubalgebra_cartanP [Invertible (2 : R)] (hθ : θ.IsCartanInvolution) :
    IsCompl θ.toLieHom.fixedSubalgebra.toSubmodule θ.cartanP :=
  LieEquiv.isCompl_fixedSubalgebra_cartanP hθ.1

/-- For a Cartan involution, `𝔭` is the Killing orthogonal complement of `𝔨`. -/
theorem cartanP_eq_orthogonal_fixedSubalgebra [Invertible (2 : R)] (hθ : θ.IsCartanInvolution) :
    θ.cartanP = (killingForm R L).orthogonal θ.toLieHom.fixedSubalgebra.toSubmodule :=
  LieEquiv.cartanP_eq_orthogonal_fixedSubalgebra hθ.1 hθ.killingForm_nondegenerate

/-- Two Cartan involutions with the same fixed subalgebra are equal. -/
theorem eq_of_fixedSubalgebra_eq [Invertible (2 : R)] {θ₁ θ₂ : L ≃ₗ⁅R⁆ L}
    (h₁ : θ₁.IsCartanInvolution) (h₂ : θ₂.IsCartanInvolution)
    (hK : θ₁.toLieHom.fixedSubalgebra = θ₂.toLieHom.fixedSubalgebra) :
    θ₁ = θ₂ :=
  LieEquiv.eq_of_fixedSubalgebra_eq h₁.1 h₂.1 h₁.killingForm_nondegenerate hK

/-- The restriction of `B_θ` to `𝔨` is positive definite. -/
theorem posDef_cartanForm_fixedSubalgebra (hθ : θ.IsCartanInvolution) :
    (LinearMap.BilinMap.toQuadraticMap
      (θ.cartanForm.compl₁₂ θ.toLieHom.fixedSubalgebra.incl.toLinearMap
        θ.toLieHom.fixedSubalgebra.incl.toLinearMap)).PosDef :=
  θ.cartanForm.posDef_toQuadraticMap_compl₁₂ hθ.2
    θ.toLieHom.fixedSubalgebra.incl.toLinearMap Subtype.val_injective

end IsCartanInvolution

end CartanInvolution

section Field

variable {K L : Type*} [Field K] [PartialOrder K] [LieRing L] [LieAlgebra K L]

namespace IsCartanInvolution

/-- **Semisimplicity from a Cartan involution.** Over a partially ordered field, a Lie algebra
admitting a Cartan involution is semisimple. -/
theorem isSemisimple {θ : L ≃ₗ⁅K⁆ L} (hθ : θ.IsCartanInvolution) :
    LieAlgebra.IsSemisimple K L :=
  have := hθ.isKilling
  have := hθ.finite
  inferInstance

/-- The fixed subalgebra `𝔨` of a Cartan involution splits as the direct sum of its centre and
its derived ideal. -/
theorem isCompl_center_derivedSeries_fixedSubalgebra {θ : L ≃ₗ⁅K⁆ L}
    (hθ : θ.IsCartanInvolution) :
    IsCompl (center K θ.toLieHom.fixedSubalgebra)
      (derivedSeries K θ.toLieHom.fixedSubalgebra 1) := by
  have : Module.Finite K L := hθ.finite
  let B : LinearMap.BilinForm K θ.toLieHom.fixedSubalgebra :=
    θ.cartanForm.compl₁₂ θ.toLieHom.fixedSubalgebra.incl.toLinearMap
      θ.toLieHom.fixedSubalgebra.incl.toLinearMap
  exact LinearMap.BilinForm.isCompl_center_derivedSeries_one_of_anisotropic B
    (hθ.cartanForm_isSymm.compl₁₂ _).isRefl
    hθ.posDef_cartanForm_fixedSubalgebra.anisotropic
    θ.lieInvariant_cartanForm_fixedSubalgebra

/-- The centre and derived ideal of `𝔨` are orthogonal for the ambient Killing form `B|_𝔨`. -/
theorem killingForm_eq_zero_of_mem_center_of_mem_derivedSeries_fixedSubalgebra {θ : L ≃ₗ⁅K⁆ L}
    (hθ : θ.IsCartanInvolution) {z d : θ.toLieHom.fixedSubalgebra}
    (hz : z ∈ center K θ.toLieHom.fixedSubalgebra)
    (hd : d ∈ derivedSeries K θ.toLieHom.fixedSubalgebra 1) :
    killingForm K L (z : L) (d : L) = 0 := by
  let B : LinearMap.BilinForm K θ.toLieHom.fixedSubalgebra :=
    θ.cartanForm.compl₁₂ θ.toLieHom.fixedSubalgebra.incl.toLinearMap
      θ.toLieHom.fixedSubalgebra.incl.toLinearMap
  have hnd : B.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_of_anisotropic B
      hθ.posDef_cartanForm_fixedSubalgebra.anisotropic
  have hortho := LinearMap.BilinForm.orthogonal_derivedSeries_one_eq_center B hnd.2
    θ.lieInvariant_cartanForm_fixedSubalgebra
  have hz' : z ∈ B.orthogonal (derivedSeries K θ.toLieHom.fixedSubalgebra 1).toSubmodule := by
    rw [← LieAlgebra.InvariantForm.orthogonal_toSubmodule (L := θ.toLieHom.fixedSubalgebra) B
      θ.lieInvariant_cartanForm_fixedSubalgebra, hortho]
    exact hz
  have h0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hz') d hd
  rw [LinearMap.compl₁₂_apply, LieHom.coe_toLinearMap, LieSubalgebra.coe_incl,
    θ.cartanForm_apply_of_mem_fixedSubalgebra_right z.2, neg_eq_zero,
    LieModule.traceForm_comm] at h0
  exact h0

/-- The derived algebra `[𝔨, 𝔨]` of the fixed subalgebra of a Cartan involution is semisimple. -/
theorem isSemisimple_derivedSeries_fixedSubalgebra {θ : L ≃ₗ⁅K⁆ L}
    (hθ : θ.IsCartanInvolution) :
    LieAlgebra.IsSemisimple K (derivedSeries K θ.toLieHom.fixedSubalgebra 1) := by
  have : Module.Finite K L := hθ.finite
  let B : LinearMap.BilinForm K θ.toLieHom.fixedSubalgebra :=
    θ.cartanForm.compl₁₂ θ.toLieHom.fixedSubalgebra.incl.toLinearMap
      θ.toLieHom.fixedSubalgebra.incl.toLinearMap
  exact LinearMap.BilinForm.isSemisimple_derivedSeries_one_of_anisotropic B
    (hθ.cartanForm_isSymm.compl₁₂ _).isRefl
    hθ.posDef_cartanForm_fixedSubalgebra.anisotropic
    θ.lieInvariant_cartanForm_fixedSubalgebra

/-- The fixed subalgebra `𝔨` of a Cartan involution is reductive (`HasCentralRadical`). -/
theorem hasCentralRadical_fixedSubalgebra {θ : L ≃ₗ⁅K⁆ L}
    (hθ : θ.IsCartanInvolution) :
    LieAlgebra.HasCentralRadical K θ.toLieHom.fixedSubalgebra := by
  have : Module.Finite K L := hθ.finite
  let B : LinearMap.BilinForm K θ.toLieHom.fixedSubalgebra :=
    θ.cartanForm.compl₁₂ θ.toLieHom.fixedSubalgebra.incl.toLinearMap
      θ.toLieHom.fixedSubalgebra.incl.toLinearMap
  exact LinearMap.BilinForm.hasCentralRadical_of_anisotropic B
    (hθ.cartanForm_isSymm.compl₁₂ _).isRefl
    hθ.posDef_cartanForm_fixedSubalgebra.anisotropic
    θ.lieInvariant_cartanForm_fixedSubalgebra

end IsCartanInvolution

end Field

section OrderedField

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [LieRing L] [LieAlgebra K L]

namespace IsCartanInvolution

/-- The derived algebra `[𝔨, 𝔨]` of the fixed subalgebra of a Cartan involution has
negative-definite Killing form. -/
theorem killingForm_derivedSeries_fixedSubalgebra_self_neg {θ : L ≃ₗ⁅K⁆ L}
    (hθ : θ.IsCartanInvolution) {x : derivedSeries K θ.toLieHom.fixedSubalgebra 1} (hx : x ≠ 0) :
    killingForm K (derivedSeries K θ.toLieHom.fixedSubalgebra 1) x x < 0 := by
  have : Module.Finite K L := hθ.finite
  let B : LinearMap.BilinForm K θ.toLieHom.fixedSubalgebra :=
    θ.cartanForm.compl₁₂ θ.toLieHom.fixedSubalgebra.incl.toLinearMap
      θ.toLieHom.fixedSubalgebra.incl.toLinearMap
  exact LinearMap.BilinForm.killingForm_derivedSeries_one_self_neg_of_posDef_of_ne_zero B
    (hθ.cartanForm_isSymm.compl₁₂ _)
    hθ.posDef_cartanForm_fixedSubalgebra
    θ.lieInvariant_cartanForm_fixedSubalgebra x hx

end IsCartanInvolution

end OrderedField

section Real

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

namespace IsCartanInvolution

/-- **Diagonalizability of `ad x` on `𝔭`.** For a Cartan involution of a real Lie algebra and
every `x ∈ 𝔭`, the eigenspaces of `ad x` over `ℝ` span `L`. -/
theorem iSup_eigenspace_ad_eq_top {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution)
    {x : L} (hx : x ∈ θ.cartanP) :
    ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ L x) μ = ⊤ := by
  have : FiniteDimensional ℝ L := hθ.finite
  exact LinearMap.BilinForm.iSup_eigenspace_eq_top_of_isSelfAdjoint
    hθ.cartanForm_isSymm (fun _ ↦ hθ.cartanForm_self_pos) (θ.isSelfAdjoint_cartanForm_ad hx)

/-- For a Cartan involution of a real Lie algebra and every `x ∈ 𝔭`, the adjoint operator `ad x`
is semisimple. -/
theorem isSemisimple_ad {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution)
    {x : L} (hx : x ∈ θ.cartanP) :
    (ad ℝ L x).IsSemisimple :=
  TauCeti.isSemisimple_of_iSup_eigenspace_eq_top (hθ.iSup_eigenspace_ad_eq_top hx)

end IsCartanInvolution

end Real

end LieEquiv
