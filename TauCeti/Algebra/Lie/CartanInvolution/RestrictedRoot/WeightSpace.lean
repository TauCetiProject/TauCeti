/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot
public import Mathlib.Algebra.Lie.Weights.Linear
import TauCeti.Algebra.Lie.Weights.SelfAdjoint

/-!
# Restricted root spaces as weight spaces

Let `𝔞` be a Lie subalgebra of a Lie algebra `L`, acting on `L` by `ad`. For a linear functional
`λ` on `𝔞`, the restricted root space `𝔤_λ = {x | [H, x] = λ(H) x for all H ∈ 𝔞}` is Mathlib's
weight space `LieModule.weightSpace L λ` of this action. When `L` carries a Cartan involution `θ`
and `𝔞` lies in the `-1`-eigenspace `𝔭` of `θ`, `𝔞` is abelian, and every `ad H`, `H ∈ 𝔞`, is
self-adjoint for the inner product `B_θ`, so it is semisimple and the generalized weight spaces
`LieModule.genWeightSpace L λ` are the weight spaces. Hence `𝔤_λ` is the generalized weight space
of `λ`, and the restricted roots `Σ` are the nonzero weights `LieModule.Weight` of `𝔞` on `L`.
An abelian submodule, such as a maximal abelian subspace of `𝔭`
(`LieEquiv.IsMaximalAbelianInP`), is a Lie subalgebra by `Submodule.toLieSubalgebraOfAbelian`.

## Main definitions

* `Submodule.toLieSubalgebraOfAbelian`: an abelian submodule as a Lie subalgebra.
* `LieEquiv.IsCartanInvolution.restrictedRootsEquivWeight`: for `𝔞 ⊆ 𝔭`, the restricted roots
  are the nonzero weights of `𝔞` acting on `L`.

## Main results

* `LieSubalgebra.toSubmodule_weightSpace_eq_restrictedRootSpace`: `𝔤_λ` is a weight space.
* `LieEquiv.IsCartanInvolution.isLieAbelian_of_le_cartanP`: a Lie subalgebra of `𝔭` is abelian.
* `LieEquiv.IsCartanInvolution.genWeightSpace_eq_weightSpace`: for `𝔞 ⊆ 𝔭`, generalized weight
  spaces are weight spaces.
* `LieEquiv.IsCartanInvolution.toSubmodule_genWeightSpace_eq_restrictedRootSpace`: for `𝔞 ⊆ 𝔭`,
  `𝔤_λ` is a generalized weight space.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §4.
-/

public section

open LieAlgebra LieModule Module

/-! ### Abelian submodules as Lie subalgebras -/

namespace Submodule

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- An abelian submodule `𝔞` of a Lie algebra, `[x, y] = 0` for `x, y ∈ 𝔞`, as a Lie
subalgebra. -/
@[expose] def toLieSubalgebraOfAbelian (𝔞 : Submodule R L) (h𝔞 : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0) :
    LieSubalgebra R L where
  toSubmodule := 𝔞
  lie_mem' hx hy := by rw [h𝔞 _ hx _ hy]; exact 𝔞.zero_mem

@[simp]
theorem toSubmodule_toLieSubalgebraOfAbelian (𝔞 : Submodule R L)
    (h𝔞 : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0) : (𝔞.toLieSubalgebraOfAbelian h𝔞).toSubmodule = 𝔞 :=
  rfl

/-- An abelian submodule is an abelian Lie subalgebra. -/
theorem isLieAbelian_toLieSubalgebraOfAbelian (𝔞 : Submodule R L)
    (h𝔞 : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0) : IsLieAbelian (𝔞.toLieSubalgebraOfAbelian h𝔞) :=
  ⟨fun x y ↦ Subtype.ext (h𝔞 _ x.property _ y.property)⟩

end Submodule

/-! ### Restricted root spaces are weight spaces -/

namespace LieSubalgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- **The restricted root space `𝔤_λ` of a Lie subalgebra `𝔞` is the weight space of `λ`** for
the action of `𝔞` on `L` by `ad`. -/
theorem toSubmodule_weightSpace_eq_restrictedRootSpace (𝔞 : LieSubalgebra R L)
    (μ : Dual R 𝔞.toSubmodule) :
    (weightSpace L fun H : 𝔞 ↦ μ ⟨H, H.property⟩).toSubmodule =
      𝔞.toSubmodule.restrictedRootSpace μ := by
  ext x
  simp only [LieSubmodule.mem_toSubmodule, mem_weightSpace, Submodule.mem_restrictedRootSpace,
    LieSubalgebra.coe_bracket_of_module]
  exact ⟨fun h H ↦ h ⟨H, H.property⟩, fun h H ↦ h ⟨H, H.property⟩⟩

end LieSubalgebra

/-! ### The case of a Cartan involution -/

namespace LieEquiv.IsCartanInvolution

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [LieRing L]
  [LieAlgebra K L] {θ : L ≃ₗ⁅K⁆ L} (hθ : θ.IsCartanInvolution)
  {𝔞 : LieSubalgebra K L} (h𝔞 : 𝔞.toSubmodule ≤ θ.cartanP)

/-- A Lie subalgebra contained in `𝔭` is abelian: `[𝔭, 𝔭] ⊆ 𝔨` and `𝔨 ∩ 𝔭 = 0`. -/
theorem isLieAbelian_of_le_cartanP (h𝔞 : 𝔞.toSubmodule ≤ θ.cartanP) : IsLieAbelian 𝔞 := by
  refine ⟨fun x y ↦ Subtype.ext ?_⟩
  have hk := lie_mem_fixedSubalgebra_of_mem_cartanP (h𝔞 x.property) (h𝔞 y.property)
  have hp := mem_cartanP.mp (h𝔞 (⁅x, y⁆ : 𝔞).property)
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom] at hk
  rw [LieSubalgebra.coe_bracket] at hp ⊢
  rw [hk, eq_neg_iff_add_eq_zero, ← two_smul K] at hp
  exact (smul_eq_zero.mp hp).resolve_left two_ne_zero

include hθ h𝔞

omit [LinearOrder K] [IsStrictOrderedRing K] hθ in
/-- For `𝔞 ⊆ 𝔭` and a Cartan involution `θ`, every `ad H`, `H ∈ 𝔞`, is self-adjoint for the
twisted Killing form `B_θ`. -/
private theorem isSelfAdjoint_toEnd (H : 𝔞) :
    θ.twistedKillingForm.IsSelfAdjoint (toEnd K 𝔞 L H) :=
  (LinearMap.mem_selfAdjointSubmodule _).mp
    (ad_mem_selfAdjointSubmodule_twistedKillingForm (h𝔞 H.property))

omit h𝔞 in
/-- The twisted Killing form of a Cartan involution is anisotropic. -/
private theorem twistedKillingForm_anisotropic (x : L) (hx : θ.twistedKillingForm x x = 0) :
    x = 0 := by
  by_contra hx₀
  have := hθ.killingForm_apply_apply_neg hx₀
  rw [twistedKillingForm_apply, neg_eq_zero] at hx
  exact this.ne hx

/-- **Generalized weight spaces of `𝔞 ⊆ 𝔭` are weight spaces.** For a Cartan involution `θ` and
a Lie subalgebra `𝔞` of `𝔭`, the operators `ad H`, `H ∈ 𝔞`, are self-adjoint for the
inner product `B_θ`, so the generalized weight spaces of `𝔞` acting on `L` are its weight
spaces. -/
theorem genWeightSpace_eq_weightSpace [LieRing.IsNilpotent 𝔞] (χ : 𝔞 → K) :
    genWeightSpace L χ = weightSpace L χ :=
  TauCeti.genWeightSpace_eq_weightSpace_of_isSelfAdjoint
    (twistedKillingForm_anisotropic hθ) (isSelfAdjoint_toEnd h𝔞) χ

/-- **The restricted root space `𝔤_λ` is the generalized weight space of `λ`** for a Lie
subalgebra `𝔞` of `𝔭` acting on `L` by `ad`. -/
theorem toSubmodule_genWeightSpace_eq_restrictedRootSpace [LieRing.IsNilpotent 𝔞]
    (μ : Dual K 𝔞.toSubmodule) :
    (genWeightSpace L fun H : 𝔞 ↦ μ ⟨H, H.property⟩).toSubmodule =
      𝔞.toSubmodule.restrictedRootSpace μ := by
  rw [genWeightSpace_eq_weightSpace hθ h𝔞, 𝔞.toSubmodule_weightSpace_eq_restrictedRootSpace]

/-- The weight of `𝔞` on `L` given by a restricted root. -/
private def weightOfRestrictedRoot [LieRing.IsNilpotent 𝔞] (μ : 𝔞.toSubmodule.restrictedRoots) :
    Weight K 𝔞 L where
  toFun H := μ.val ⟨H, H.property⟩
  genWeightSpace_ne_bot' := by
    rw [ne_eq, ← LieSubmodule.toSubmodule_eq_bot,
      toSubmodule_genWeightSpace_eq_restrictedRootSpace hθ h𝔞]
    exact (Submodule.mem_restrictedRoots.mp μ.property).2

/-- A nonzero weight of `𝔞` on `L` is linear and so a restricted root. -/
private def restrictedRootOfWeight [LieRing.IsNilpotent 𝔞]
    (α : {α : Weight K 𝔞 L // α.IsNonZero}) : 𝔞.toSubmodule.restrictedRoots :=
  have := isLieAbelian_of_le_cartanP h𝔞
  ⟨α.val.toLinear, Submodule.mem_restrictedRoots.mpr
    ⟨fun h ↦ α.property (funext fun H ↦ LinearMap.congr_fun h H), by
      have h := α.val.genWeightSpace_ne_bot
      rw [ne_eq, ← LieSubmodule.toSubmodule_eq_bot] at h
      rwa [← toSubmodule_genWeightSpace_eq_restrictedRootSpace hθ h𝔞]⟩⟩

/-- **The restricted roots are the nonzero weights.** For a Cartan involution `θ` and a Lie
subalgebra `𝔞` of `𝔭`, a restricted root `λ ∈ Σ` is the nonzero weight `H ↦ λ(H)` of `𝔞`
acting on `L` by `ad`, and every nonzero weight arises in this way. -/
noncomputable def restrictedRootsEquivWeight [LieRing.IsNilpotent 𝔞] :
    𝔞.toSubmodule.restrictedRoots ≃ {α : Weight K 𝔞 L // α.IsNonZero} where
  toFun μ := ⟨weightOfRestrictedRoot hθ h𝔞 μ, fun h ↦
    (Submodule.mem_restrictedRoots.mp μ.property).1 (LinearMap.ext fun H ↦
      congr_fun h (⟨H, H.property⟩ : 𝔞))⟩
  invFun α := restrictedRootOfWeight hθ h𝔞 α
  left_inv _ := rfl
  right_inv _ := rfl

/-- The weight attached to a restricted root `λ` is `H ↦ λ(H)`. -/
theorem restrictedRootsEquivWeight_apply_apply [LieRing.IsNilpotent 𝔞]
    (μ : 𝔞.toSubmodule.restrictedRoots) (H : 𝔞) :
    (restrictedRootsEquivWeight hθ h𝔞 μ).val H = μ.val ⟨H, H.property⟩ :=
  (rfl)

end LieEquiv.IsCartanInvolution
