/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import TauCeti.Algebra.Lie.Subalgebra.Fixed.Basic
import TauCeti.LinearAlgebra.Eigenspace.Separation
import TauCeti.LinearAlgebra.FixedSubmodule

/-!
# The Cartan decomposition of a Lie algebra automorphism

Let `θ` be an automorphism of a Lie algebra `L`. Its fixed vectors form the Lie subalgebra
`𝔨 = θ.toLieHom.fixedSubalgebra`, and its `-1`-eigenspace is the submodule `𝔭 = θ.cartanP`.
These satisfy `[𝔨, 𝔭] ⊆ 𝔭` and `[𝔭, 𝔭] ⊆ 𝔨`, and they are orthogonal for the Killing form as soon
as the base ring has no additive torsion. When `θ` is involutive and `2` is a unit,
`L = 𝔨 ⊕ 𝔭`: this is the Cartan decomposition when `θ` is a Cartan involution.

The *twisted Killing form* `B_θ(x, y) = -B(x, θ y)` is invariant under every automorphism
commuting with `θ`, in particular under `θ` itself, and it is symmetric when `θ` is involutive.
For `x ∈ 𝔨` the operator `ad x` is skew-adjoint for `B_θ`, and for `x ∈ 𝔭` it is self-adjoint.

## Main definitions

* `LieEquiv.cartanP`: the `-1`-eigenspace `𝔭` of a Lie algebra automorphism.
* `LieEquiv.twistedKillingForm`: the bilinear form `B_θ(x, y) = -B(x, θ y)`.

## Main results

* `LieEquiv.isCompl_fixedSubalgebra_cartanP`: `L = 𝔨 ⊕ 𝔭` for an involution when `2` is a unit.
* `LieEquiv.lie_mem_cartanP`, `LieEquiv.lie_mem_fixedSubalgebra_of_mem_cartanP`: the bracket
  relations `[𝔨, 𝔭] ⊆ 𝔭` and `[𝔭, 𝔭] ⊆ 𝔨`.
* `LieEquiv.killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP`: `B(𝔨, 𝔭) = 0`.
* `LieEquiv.twistedKillingForm_map_map_of_commute`: `B_θ` is invariant under automorphisms commuting
  with `θ`.
* `LieEquiv.isSymm_twistedKillingForm`: `B_θ` is symmetric when `θ` is involutive.
* `LieEquiv.ad_mem_skewAdjointSubmodule_twistedKillingForm`,
  `LieEquiv.ad_mem_selfAdjointSubmodule_twistedKillingForm`: `ad x` is `B_θ`-skew-adjoint for
  `x ∈ 𝔨` and `B_θ`-self-adjoint for `x ∈ 𝔭`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §2.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Chapter III, §7.
-/

public section

open LieAlgebra LieModule

namespace LieEquiv

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (θ : L ≃ₗ⁅R⁆ L)

/-! ### The eigenspaces `𝔨` and `𝔭` -/

/-- The `-1`-eigenspace `𝔭 = {x | θ x = -x}` of a Lie algebra automorphism `θ`. When `θ` is a
Cartan involution, `L = 𝔨 ⊕ 𝔭` with `𝔨 = θ.toLieHom.fixedSubalgebra` is the Cartan
decomposition. -/
def cartanP : Submodule R L :=
  Module.End.eigenspace (θ.toLinearEquiv : Module.End R L) (-1)

variable {θ}

@[simp]
theorem mem_cartanP {x : L} : x ∈ θ.cartanP ↔ θ x = -x := by
  simp [cartanP]

variable (θ) in
/-- `𝔭` is the `-1`-eigenspace of `θ`, viewed as a linear endomorphism of `L`. -/
theorem cartanP_eq_eigenspace :
    θ.cartanP = Module.End.eigenspace (θ.toLinearEquiv : Module.End R L) (-1) :=
  (rfl)

variable (θ) in
/-- An automorphism and its inverse have the same `-1`-eigenspace. -/
@[simp]
theorem cartanP_symm : θ.symm.cartanP = θ.cartanP := by
  ext x
  rw [mem_cartanP, mem_cartanP, θ.symm_apply_eq, map_neg, ← neg_eq_iff_eq_neg, eq_comm]

variable (θ) in
/-- For an involution of a Lie algebra over a ring in which `2` is a unit, the fixed subalgebra
`𝔨` and the `-1`-eigenspace `𝔭` are complementary: `L = 𝔨 ⊕ 𝔭`. -/
theorem isCompl_fixedSubalgebra_cartanP (h2 : IsUnit (2 : R)) (hθ : Function.Involutive θ) :
    IsCompl θ.toLieHom.fixedSubalgebra.toSubmodule θ.cartanP := by
  have := TauCeti.isCompl_eigenspace_one_neg_one h2
    (T := (θ.toLinearEquiv : Module.End R L)) hθ
  rw [Module.End.eigenspace_one_eq_fixedSubmodule] at this
  rw [LieHom.fixedSubalgebra_toSubmodule]
  exact this

/-- `[𝔨, 𝔭] ⊆ 𝔭`. -/
theorem lie_mem_cartanP {x y : L} (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hy : y ∈ θ.cartanP) :
    ⁅x, y⁆ ∈ θ.cartanP := by
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom] at hx
  rw [mem_cartanP] at hy ⊢
  rw [map_lie, hx, hy, lie_neg]

/-- `[𝔭, 𝔭] ⊆ 𝔨`. -/
theorem lie_mem_fixedSubalgebra_of_mem_cartanP {x y : L} (hx : x ∈ θ.cartanP)
    (hy : y ∈ θ.cartanP) : ⁅x, y⁆ ∈ θ.toLieHom.fixedSubalgebra := by
  rw [mem_cartanP] at hx hy
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom, map_lie, hx, hy, neg_lie, lie_neg, neg_neg]

/-- `𝔨` and `𝔭` are orthogonal for the Killing form, over a base ring without additive
torsion. -/
theorem killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP [IsAddTorsionFree R]
    {x y : L} (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hy : y ∈ θ.cartanP) :
    killingForm R L x y = 0 := by
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom] at hx
  rw [mem_cartanP] at hy
  refine self_eq_neg.mp ?_
  conv_lhs => rw [← killingForm_of_equiv_apply θ, hx, hy, map_neg]

/-! ### The twisted Killing form -/

variable (θ) in
/-- The twisted Killing form `B_θ(x, y) = -B(x, θ y)` of a Lie algebra automorphism `θ`, where
`B` is the Killing form. When `θ` is a Cartan involution it is an inner product. -/
noncomputable def twistedKillingForm : LinearMap.BilinForm R L :=
  -(killingForm R L).compl₂ (θ.toLinearEquiv : L →ₗ[R] L)

@[simp]
theorem twistedKillingForm_apply (x y : L) :
    θ.twistedKillingForm x y = -killingForm R L x (θ y) := by
  simp [twistedKillingForm]

/-- The twisted Killing form is invariant under every automorphism commuting with `θ`. -/
theorem twistedKillingForm_map_map_of_commute {φ : L ≃ₗ⁅R⁆ L} (hφ : ∀ x, θ (φ x) = φ (θ x))
    (x y : L) :
    θ.twistedKillingForm (φ x) (φ y) = θ.twistedKillingForm x y := by
  rw [twistedKillingForm_apply, twistedKillingForm_apply, hφ, killingForm_of_equiv_apply]

/-- `θ` is orthogonal for its twisted Killing form. -/
theorem twistedKillingForm_map_map (x y : L) :
    θ.twistedKillingForm (θ x) (θ y) = θ.twistedKillingForm x y :=
  twistedKillingForm_map_map_of_commute (fun _ ↦ rfl) x y

/-- The twisted Killing form of an involution is symmetric. -/
theorem isSymm_twistedKillingForm (hθ : Function.Involutive θ) : θ.twistedKillingForm.IsSymm := by
  refine ⟨fun x y ↦ ?_⟩
  rw [twistedKillingForm_apply, twistedKillingForm_apply,
    ← killingForm_of_equiv_apply θ y, hθ, traceForm_comm]

/-- For `x ∈ 𝔨`, `ad x` is skew-adjoint for the twisted Killing form. -/
theorem ad_mem_skewAdjointSubmodule_twistedKillingForm {x : L}
    (hx : x ∈ θ.toLieHom.fixedSubalgebra) :
    ad R L x ∈ θ.twistedKillingForm.skewAdjointSubmodule := by
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom] at hx
  rw [LinearMap.mem_skewAdjointSubmodule]
  intro y z
  simp only [twistedKillingForm_apply, Pi.neg_apply, ad_apply, map_neg, map_lie, hx, neg_neg,
    traceForm_apply_lie_apply']

/-- For `x ∈ 𝔭`, `ad x` is self-adjoint for the twisted Killing form. -/
theorem ad_mem_selfAdjointSubmodule_twistedKillingForm {x : L} (hx : x ∈ θ.cartanP) :
    ad R L x ∈ θ.twistedKillingForm.selfAdjointSubmodule := by
  rw [mem_cartanP] at hx
  rw [LinearMap.mem_selfAdjointSubmodule]
  intro y z
  simp only [twistedKillingForm_apply, ad_apply, map_lie, hx, neg_lie, map_neg,
    traceForm_apply_lie_apply']

end LieEquiv
