/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import TauCeti.Geometry.Symplectic.Cotangent.Basic

/-!
# The normal quotient of a Lagrangian subspace is the dual of the subspace

Let `ω` be a symplectic form on a real vector space `V` and let `g : W →ₗ[ℝ] V` be a linear map.
Every vector `v` of `V` pairs with `W` through `g` and `ω`, giving the functional

`w ↦ ω(g w, v)`

(`TauCeti.SymplecticForm.normalPairing ω g`). Its kernel is the symplectic complement of the
range of `g` (`TauCeti.SymplecticForm.ker_normalPairing`). When `V` is finite-dimensional and `g`
is injective, every functional on `W` arises in this way: `ω` identifies `V` with its dual, and
restriction along an injective map is surjective on duals. Hence

`V ⧸ (range g)^ω ≃ Dual W`, `[v] ↦ ω(g ·, v)`

(`TauCeti.SymplecticForm.quotientOrthogonalEquivDual`).

When the range of `g` is isotropic, it lies in its symplectic complement, so the pairing descends
to the normal quotient `V ⧸ range g` (`TauCeti.SymplecticForm.IsIsotropic.normalPairingQuotient`).
The descended map is surjective, its kernel is the image of `(range g)^ω`, which is the
symplectic normal space `(range g)^ω ⧸ range g` (`LinearMap.SymplecticNormal`), and it is injective
exactly when the range is Lagrangian. So the quotient of `V` by a Lagrangian subspace, the normal
space of the subspace, is identified with the dual of `W`
(`TauCeti.SymplecticForm.IsLagrangian.quotientEquivDual`).

This is the pointwise linear algebra behind the identification of the normal bundle of a
Lagrangian submanifold `Q` with its cotangent bundle `T*Q`, the first step of Weinstein's
Lagrangian neighbourhood theorem.

## Main definitions

* `TauCeti.SymplecticForm.normalPairing ω g`: the linear map `v ↦ ω(g ·, v)` from `V` to the dual
  of `W`.
* `TauCeti.SymplecticForm.quotientOrthogonalEquivDual`: for injective `g` in finite dimension,
  the quotient of `V` by the symplectic complement of the range of `g` is the dual of `W`.
* `TauCeti.SymplecticForm.IsIsotropic.normalPairingQuotient`: for isotropic range, the pairing on
  the normal quotient `V ⧸ range g`.
* `TauCeti.SymplecticForm.IsLagrangian.quotientEquivDual`: for injective `g` with Lagrangian
  range, the quotient of `V` by that range is the dual of `W`.

## Main results

* `TauCeti.SymplecticForm.ker_normalPairing`: the kernel of the pairing is `(range g)^ω`.
* `TauCeti.SymplecticForm.normalPairing_surjective`: for injective `g` in finite dimension, the
  pairing is surjective.
* `TauCeti.SymplecticForm.IsIsotropic.ker_normalPairingQuotient`,
  `TauCeti.SymplecticForm.IsIsotropic.normalPairingQuotient_surjective`: for isotropic range, the
  descended pairing has kernel `(range g)^ω ⧸ range g` and is surjective.
* `TauCeti.SymplecticForm.IsIsotropic.normalPairingQuotient_injective_iff`: it is injective
  exactly when the range is Lagrangian.

## References

* A. Weinstein, *Symplectic manifolds and their Lagrangian submanifolds*, Advances in Mathematics
  6 (1971), 329–346.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 8 (the normal bundle of a Lagrangian submanifold).
-/

public section

noncomputable section

namespace TauCeti

namespace SymplecticForm

open Module

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  (ω : SymplecticForm V) (g : W →ₗ[ℝ] V)

/-- The pairing of `V` with `W` through `g` and `ω`: a vector `v` gives the functional
`w ↦ ω(g w, v)` on `W`. -/
def normalPairing : V →ₗ[ℝ] Dual ℝ W :=
  g.dualMap ∘ₗ ω.toBilinForm.flip

@[simp]
theorem normalPairing_apply (v : V) (w : W) : ω.normalPairing g v w = ω (g w) v :=
  (rfl)

/-- The kernel of the pairing is the symplectic complement of the range of `g`. -/
@[simp]
theorem ker_normalPairing :
    LinearMap.ker (ω.normalPairing g) = ω.orthogonal (LinearMap.range g) := by
  rw [normalPairing, LinearMap.ker_comp, LinearMap.ker_dualMap_eq_dualAnnihilator_range]
  exact Submodule.comap_dualAnnihilator_eq_orthogonalBilin _ _

/-- The range of `g` pairs to zero with `v` exactly when `v` lies in its symplectic complement. -/
theorem normalPairing_eq_zero_iff {v : V} :
    ω.normalPairing g v = 0 ↔ v ∈ ω.orthogonal (LinearMap.range g) := by
  rw [← ker_normalPairing, LinearMap.mem_ker]

/-- In finite dimension, every functional on `W` is `ω(g ·, v)` for some `v` when `g` is
injective. -/
theorem normalPairing_surjective [FiniteDimensional ℝ V] (hg : Function.Injective g) :
    Function.Surjective (ω.normalPairing g) := by
  intro φ
  -- First extend `φ` along the injective map `g`, then represent the extension through `ω`.
  obtain ⟨ψ, rfl⟩ := LinearMap.dualMap_surjective_of_injective hg φ
  have hflip : ω.toBilinForm.flip.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_flip_iff.mpr ω.nondegenerate
  obtain ⟨v, hv⟩ := (ω.toBilinForm.flip.toDual hflip).surjective ψ
  refine ⟨v, LinearMap.ext fun w ↦ ?_⟩
  rw [← hv, LinearMap.dualMap_apply, LinearMap.BilinForm.toDual_def]
  -- Both sides are `ω (g w) v`; the right one is stated through `LinearMap.flip`.
  rfl

variable {g}

/-- **The normal quotient is the dual.** For an injective linear map `g : W → V` into a
finite-dimensional symplectic vector space, `[v] ↦ ω(g ·, v)` identifies the quotient of `V` by
the symplectic complement of the range of `g` with the dual of `W`. -/
def quotientOrthogonalEquivDual [FiniteDimensional ℝ V] (hg : Function.Injective g) :
    (V ⧸ ω.orthogonal (LinearMap.range g)) ≃ₗ[ℝ] Dual ℝ W :=
  (Submodule.quotEquivOfEq _ _ (ω.ker_normalPairing g).symm).trans
    ((ω.normalPairing g).quotKerEquivOfSurjective (ω.normalPairing_surjective g hg))

@[simp]
theorem quotientOrthogonalEquivDual_mk [FiniteDimensional ℝ V] (hg : Function.Injective g)
    (v : V) :
    ω.quotientOrthogonalEquivDual hg (Submodule.Quotient.mk v) = ω.normalPairing g v :=
  (rfl)

/-- The class corresponding to a functional `φ` is the class of any `v` with `ω(g ·, v) = φ`. -/
theorem quotientOrthogonalEquivDual_symm_apply_eq_iff [FiniteDimensional ℝ V]
    (hg : Function.Injective g) (φ : Dual ℝ W) (v : V) :
    (ω.quotientOrthogonalEquivDual hg).symm φ = Submodule.Quotient.mk v ↔
      ω.normalPairing g v = φ := by
  rw [LinearEquiv.symm_apply_eq, quotientOrthogonalEquivDual_mk, eq_comm]

variable {ω}

/-! ### Isotropic subspaces -/

/-- For an isotropic range, the pairing vanishes on the range of `g` and descends to the normal
quotient: `[v] ↦ ω(g ·, v)` from `V ⧸ range g` to the dual of `W`. -/
def IsIsotropic.normalPairingQuotient (h : ω.IsIsotropic (LinearMap.range g)) :
    (V ⧸ LinearMap.range g) →ₗ[ℝ] Dual ℝ W :=
  (LinearMap.range g).liftQ (ω.normalPairing g)
    ((ω.ker_normalPairing g).symm ▸ isIsotropic_iff_le.mp h)

@[simp]
theorem IsIsotropic.normalPairingQuotient_mk (h : ω.IsIsotropic (LinearMap.range g)) (v : V) :
    h.normalPairingQuotient (Submodule.Quotient.mk v) = ω.normalPairing g v :=
  (rfl)

/-- The class of `v` pairs to zero with `W` exactly when `v` lies in the symplectic complement of
the range of `g`. -/
theorem IsIsotropic.normalPairingQuotient_mk_eq_zero_iff (h : ω.IsIsotropic (LinearMap.range g))
    {v : V} :
    h.normalPairingQuotient (Submodule.Quotient.mk v) = 0 ↔
      v ∈ ω.orthogonal (LinearMap.range g) := by
  rw [normalPairingQuotient_mk, normalPairing_eq_zero_iff]

/-- The kernel of the descended pairing is the image of the symplectic complement of the range of
`g`, that is, the quotient `(range g)^ω ⧸ range g`. -/
theorem IsIsotropic.ker_normalPairingQuotient (h : ω.IsIsotropic (LinearMap.range g)) :
    LinearMap.ker h.normalPairingQuotient =
      (ω.orthogonal (LinearMap.range g)).map (LinearMap.range g).mkQ := by
  rw [normalPairingQuotient, Submodule.ker_liftQ, ker_normalPairing]

/-- In finite dimension, every functional on `W` is the pairing of a normal class when `g` is
injective. -/
theorem IsIsotropic.normalPairingQuotient_surjective [FiniteDimensional ℝ V]
    (h : ω.IsIsotropic (LinearMap.range g)) (hg : Function.Injective g) :
    Function.Surjective h.normalPairingQuotient := by
  intro φ
  obtain ⟨v, rfl⟩ := ω.normalPairing_surjective g hg φ
  exact ⟨Submodule.Quotient.mk v, h.normalPairingQuotient_mk v⟩

/-- The descended pairing of an isotropic range is injective exactly when the range is
Lagrangian. -/
theorem IsIsotropic.normalPairingQuotient_injective_iff (h : ω.IsIsotropic (LinearMap.range g)) :
    Function.Injective h.normalPairingQuotient ↔ ω.IsLagrangian (LinearMap.range g) := by
  rw [isLagrangian_iff, isCoisotropic_iff, ← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  refine ⟨fun hinj ↦ ⟨h, fun v hv ↦ ?_⟩, fun hL q hq ↦ ?_⟩
  · exact (Submodule.Quotient.mk_eq_zero _).mp
      (hinj _ (h.normalPairingQuotient_mk_eq_zero_iff.mpr hv))
  · obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (hL.2 v (h.normalPairingQuotient_mk_eq_zero_iff.mp hq))

/-! ### Lagrangian subspaces -/

/-- **The normal space of a Lagrangian subspace is the dual.** For an injective linear map
`g : W → V` with Lagrangian range in a finite-dimensional symplectic vector space,
`[v] ↦ ω(g ·, v)` identifies the quotient of `V` by the range of `g` with the dual of `W`. -/
def IsLagrangian.quotientEquivDual [FiniteDimensional ℝ V]
    (h : ω.IsLagrangian (LinearMap.range g)) (hg : Function.Injective g) :
    (V ⧸ LinearMap.range g) ≃ₗ[ℝ] Dual ℝ W :=
  (Submodule.quotEquivOfEq _ _ (le_antisymm (isIsotropic_iff_le.mp h.isIsotropic)
    (isCoisotropic_iff_le.mp h.isCoisotropic))).trans (ω.quotientOrthogonalEquivDual hg)

@[simp]
theorem IsLagrangian.quotientEquivDual_mk [FiniteDimensional ℝ V]
    (h : ω.IsLagrangian (LinearMap.range g)) (hg : Function.Injective g) (v : V) :
    h.quotientEquivDual hg (Submodule.Quotient.mk v) = ω.normalPairing g v :=
  (rfl)

/-- As a linear map, the equivalence is the descended pairing. -/
@[simp]
theorem IsLagrangian.coe_quotientEquivDual [FiniteDimensional ℝ V]
    (h : ω.IsLagrangian (LinearMap.range g)) (hg : Function.Injective g) :
    (h.quotientEquivDual hg : (V ⧸ LinearMap.range g) →ₗ[ℝ] Dual ℝ W) =
      h.isIsotropic.normalPairingQuotient :=
  Submodule.linearMap_qext _ (LinearMap.ext fun v ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe,
      quotientEquivDual_mk, IsIsotropic.normalPairingQuotient_mk])

/-- The normal class corresponding to a functional `φ` is the class of any `v` with
`ω(g ·, v) = φ`. -/
theorem IsLagrangian.quotientEquivDual_symm_apply_eq_iff [FiniteDimensional ℝ V]
    (h : ω.IsLagrangian (LinearMap.range g)) (hg : Function.Injective g) (φ : Dual ℝ W) (v : V) :
    (h.quotientEquivDual hg).symm φ = Submodule.Quotient.mk v ↔ ω.normalPairing g v = φ := by
  rw [LinearEquiv.symm_apply_eq, quotientEquivDual_mk, eq_comm]

/-! ### The zero section of the linear cotangent model -/

section Cotangent

variable {U : Type*} [AddCommGroup U] [Module ℝ U]

/-- In the linear cotangent model `U × U*`, a vector pairs with the zero section `u ↦ (u, 0)`
through its covector component. -/
@[simp]
theorem normalPairing_cotangentSymplecticForm_inl (z : U × Dual ℝ U) :
    cotangentSymplecticForm.normalPairing (LinearMap.inl ℝ U (Dual ℝ U)) z = z.2 := by
  ext u
  simp

/-- **The normal space of the zero section is the fibre.** For finite-dimensional `U`, the
identification of the normal quotient of the zero section of `U × U*` with `U*` sends the class
of `(u, p)` to `p`. The hypothesis `h` is `isLagrangian_cotangentZeroSection`, transported along
`cotangentZeroSection_eq_range_inl`. -/
theorem quotientEquivDual_cotangentZeroSection_mk [FiniteDimensional ℝ U]
    (h : cotangentSymplecticForm.IsLagrangian (LinearMap.range (LinearMap.inl ℝ U (Dual ℝ U))))
    (z : U × Dual ℝ U) :
    h.quotientEquivDual LinearMap.inl_injective (Submodule.Quotient.mk z) = z.2 :=
  (IsLagrangian.quotientEquivDual_mk _ _ z).trans (normalPairing_cotangentSymplecticForm_inl z)

end Cotangent

end SymplecticForm

end TauCeti
