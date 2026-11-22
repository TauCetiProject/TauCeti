/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import TauCeti.Algebra.Lie.Subalgebra.Fixed.Basic
import TauCeti.Algebra.CharP.Invertible
import TauCeti.LinearAlgebra.Eigenspace.Separation
import TauCeti.LinearAlgebra.Eigenspace.Transport
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
* `LieEquiv.map_cartanP`, `LieEquiv.cartanP_conj`, `LieEquiv.map_maximal_abelian_cartanP`:
  transport of `θ.cartanP` and its maximal abelian subspaces under intertwining equivalences.
* `LieEquiv.cartanP_symm`, `LieEquiv.cartanP_refl`: `-1`-eigenspace of the inverse and identity.
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

/-! ### Transport and comparison lemmas -/

section Transport

variable {L' : Type*} [LieRing L'] [LieAlgebra R L']

/-- An intertwining equivalence maps `θ.cartanP` onto `θ'.cartanP`. -/
theorem map_cartanP {θ : L ≃ₗ⁅R⁆ L} {θ' : L' ≃ₗ⁅R⁆ L'} (e : L ≃ₗ⁅R⁆ L')
    (h : ∀ x, θ' (e x) = e (θ x)) :
    θ.cartanP.map (e : L →ₗ[R] L') = θ'.cartanP := by
  rw [cartanP_eq_eigenspace, cartanP_eq_eigenspace,
    TauCeti.eigenspace_eq_comap_of_intertwine (e := e.toLinearEquiv)
      (f := (θ.toLinearEquiv : Module.End R L)) (g := (θ'.toLinearEquiv : Module.End R L'))
      (fun x ↦ (h x).symm) (-1)]
  exact Submodule.map_comap_eq_of_surjective e.surjective _

/-- Conjugating `θ` by `e` transports `θ.cartanP` along `e`. -/
theorem cartanP_conj (θ : L ≃ₗ⁅R⁆ L) (e : L ≃ₗ⁅R⁆ L') :
    (e.symm.trans (θ.trans e)).cartanP = θ.cartanP.map (e : L →ₗ[R] L') :=
  (map_cartanP e fun x ↦ by simp).symm

/-- An intertwining Lie equivalence `e : L ≃ₗ⁅R⁆ L'` maps maximal abelian subspaces of
`θ.cartanP` to maximal abelian subspaces of `θ'.cartanP`. -/
theorem map_maximal_abelian_cartanP {θ : L ≃ₗ⁅R⁆ L} {θ' : L' ≃ₗ⁅R⁆ L'}
    (e : L ≃ₗ⁅R⁆ L') (he : ∀ x, θ' (e x) = e (θ x)) {𝔞 : Submodule R L}
    (h𝔞 : Maximal
      (fun 𝔟 : Submodule R L ↦ 𝔟 ≤ θ.cartanP ∧ ∀ x ∈ 𝔟, ∀ y ∈ 𝔟, ⁅x, y⁆ = 0) 𝔞) :
    Maximal
      (fun 𝔟 : Submodule R L' ↦ 𝔟 ≤ θ'.cartanP ∧ ∀ x ∈ 𝔟, ∀ y ∈ 𝔟, ⁅x, y⁆ = 0)
      (𝔞.map (e : L →ₗ[R] L')) := by
  let o := Submodule.orderIsoMapComap (e : L ≃ₗ[R] L')
  have hmax : Maximal
      (· ∈ o '' {𝔟 : Submodule R L | 𝔟 ≤ θ.cartanP ∧ ∀ x ∈ 𝔟, ∀ y ∈ 𝔟, ⁅x, y⁆ = 0})
      (o 𝔞) :=
    maximal_mem_image_monotone (fun _ _ _ _ ↦ o.map_rel_iff) h𝔞
  have himg : o '' {𝔟 : Submodule R L | 𝔟 ≤ θ.cartanP ∧ ∀ x ∈ 𝔟, ∀ y ∈ 𝔟, ⁅x, y⁆ = 0} =
      {𝔟' : Submodule R L' | 𝔟' ≤ θ'.cartanP ∧ ∀ x ∈ 𝔟', ∀ y ∈ 𝔟', ⁅x, y⁆ = 0} := by
    ext 𝔟'
    constructor
    · rintro ⟨𝔟, ⟨h𝔟P, h𝔟ab⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← map_cartanP e he]
        exact o.monotone h𝔟P
      · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        simp only [LinearEquiv.coe_coe, coe_toLinearEquiv, ← e.map_lie, h𝔟ab x hx y hy, map_zero]
    · rintro ⟨h𝔟'P, h𝔟'ab⟩
      refine ⟨o.symm 𝔟', ⟨?_, ?_⟩, o.apply_symm_apply 𝔟'⟩
      · rw [o.symm_apply_le]
        change 𝔟' ≤ θ.cartanP.map (e : L →ₗ[R] L')
        rwa [map_cartanP e he]
      · intro x hx y hy
        apply e.injective
        simpa only [coe_toLieHom, map_lie, map_zero] using h𝔟'ab (e x) hx (e y) hy
  exact (by simpa only [himg, Set.mem_ofPred_eq] using hmax : Maximal _ (o 𝔞))

/-- The inverse of a Lie automorphism has the same `-1`-eigenspace. -/
@[simp]
theorem cartanP_symm (θ : L ≃ₗ⁅R⁆ L) : θ.symm.cartanP = θ.cartanP := by
  ext x
  rw [mem_cartanP, mem_cartanP, symm_apply_eq, map_neg, eq_comm, neg_eq_iff_eq_neg]

/-- The twisted Killing form of the identity automorphism is the negative Killing form. -/
@[simp]
theorem twistedKillingForm_refl :
    (LieEquiv.refl : L ≃ₗ⁅R⁆ L).twistedKillingForm = -killingForm R L := by
  ext x y
  simp

/-- The twisted Killing form of a conjugate automorphism is the transport of the original twisted
Killing form. -/
theorem twistedKillingForm_conj_apply (θ : L ≃ₗ⁅R⁆ L) (e : L ≃ₗ⁅R⁆ L') (x y : L) :
    (e.symm.trans (θ.trans e)).twistedKillingForm (e x) (e y) = θ.twistedKillingForm x y := by
  simp

/-- On a fixed second argument, the Killing form is the negative of the twisted Killing form. -/
theorem killingForm_eq_neg_twistedKillingForm_of_mem_fixedSubalgebra {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hy : y ∈ θ.toLieHom.fixedSubalgebra) :
    killingForm R L x y = -θ.twistedKillingForm x y := by
  have hy' : θ y = y := LieHom.mem_fixedSubalgebra.mp hy
  rw [twistedKillingForm_apply, hy', neg_neg]

/-- On a second argument in `θ.cartanP`, the Killing form agrees with the twisted Killing
form. -/
theorem killingForm_eq_twistedKillingForm_of_mem_cartanP {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hy : y ∈ θ.cartanP) :
    killingForm R L x y = θ.twistedKillingForm x y := by
  rw [twistedKillingForm_apply, mem_cartanP.mp hy, map_neg, neg_neg]

/-- The fixed subalgebra and `θ.cartanP` are orthogonal for the twisted Killing form over a base
ring without additive torsion. -/
theorem twistedKillingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP [IsAddTorsionFree R]
    {θ : L ≃ₗ⁅R⁆ L} {x y : L} (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hy : y ∈ θ.cartanP) :
    θ.twistedKillingForm x y = 0 := by
  rw [twistedKillingForm_apply, mem_cartanP.mp hy, map_neg, neg_neg,
    killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP hx hy]

/-- The identity automorphism has trivial `-1`-eigenspace when `2` is invertible. -/
@[simp]
theorem cartanP_refl [Invertible (2 : R)] : (LieEquiv.refl : L ≃ₗ⁅R⁆ L).cartanP = ⊥ := by
  ext x
  simp only [mem_cartanP, refl_apply, Submodule.mem_bot]
  exact ⟨TauCeti.eq_zero_of_eq_neg_of_invertible_two (R := R), fun hx ↦ by simp [hx]⟩

end Transport

end LieEquiv
