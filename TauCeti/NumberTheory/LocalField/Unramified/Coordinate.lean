/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Basic
public import TauCeti.NumberTheory.LocalField.Unramified.ZHat
public import TauCeti.Topology.Algebra.Group.TopologicalAbelianization.Lift

/-!
# The unramified coordinate of the abelianized absolute Galois group

Let `K` be a nonarchimedean local field, `G_K = Field.absoluteGaloisGroup K` its absolute Galois
group and `G_K^{ab} = Field.absoluteGaloisGroupAbelianization K` the topological abelianization.
This file defines the **unramified coordinate**

`TauCeti.unramifiedCoordinate K : G_K^{ab} →ₜ* ℤ̂`,

the continuous homomorphism induced by restriction to the maximal unramified extension `K^{ur}`
followed by the identification `Gal(K^{ur}/K) ≃ₜ* ℤ̂` carrying arithmetic Frobenius to the
canonical generator `zHat.gen`. Since `ℤ̂` is commutative, restriction factors through the
topological abelianization.

The coordinate is normalized arithmetically: the class of `σ` has coordinate `zHat.gen` exactly
when `σ` is an arithmetic Frobenius lift, and more generally coordinate `zHat.gen ^ n` exactly
when `σ` acts on `K^{ur}` as the `n`-th power of Frobenius, hence on every unramified extension
`K_f` of finite degree as the `n`-th power of its arithmetic Frobenius. It is surjective, and its
kernel is the image of the inertia subgroup. It is the coordinate in which the arithmetic
normalization of local class field theory is expressed: the local Artin map sends `x ∈ Kˣ` to an
element of unramified coordinate `zHat.gen ^ v_K(x)`, for `v_K` the normalized valuation.

## Main definition

* `TauCeti.unramifiedCoordinate K`: the continuous homomorphism `G_K^{ab} →ₜ* ℤ̂`.

## Main results

* `TauCeti.unramifiedCoordinate_mk`: the coordinate of the class of `σ` is the image in `ℤ̂` of
  the restriction of `σ` to `K^{ur}`.
* `TauCeti.unramifiedCoordinate_mk_eq_gen_zpow_iff`,
  `TauCeti.unramifiedCoordinate_mk_eq_gen_iff`: the class of `σ` has coordinate `zHat.gen ^ n`
  exactly when `σ` restricts to the `n`-th power of Frobenius on `K^{ur}`, and coordinate
  `zHat.gen` exactly when `σ` is an arithmetic Frobenius lift.
* `TauCeti.unramifiedCoordinate_mk_eq_unramifiedCoordinate_mk_iff`: two elements of `G_K` have
  the same coordinate exactly when they agree on every unramified extension `K_f`.
* `TauCeti.apply_of_unramifiedCoordinate_mk_eq_gen_zpow`: an element of coordinate `zHat.gen ^ n`
  acts on `K_f` as the `n`-th power of the arithmetic Frobenius of `K_f / K`.
* `TauCeti.unramifiedCoordinate_mk_eq_one_iff`, `TauCeti.ker_unramifiedCoordinate`: the kernel is
  the image of the inertia subgroup.
* `TauCeti.unramifiedCoordinate_surjective`: the coordinate is surjective.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter XIII, §4.
* J. Neukirch, *Algebraic Number Theory*, Chapter V, §1.
-/

public section

noncomputable section

namespace TauCeti

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

open scoped IsMulCommutative in
/-- **The unramified coordinate** `G_K^{ab} →ₜ* ℤ̂` of a nonarchimedean local field `K`:
restriction to the maximal unramified extension `K^{ur}`, followed by the identification
`Gal(K^{ur}/K) ≃ₜ* ℤ̂` sending arithmetic Frobenius to `zHat.gen`, factored through the
topological abelianization of the absolute Galois group. -/
def unramifiedCoordinate : Field.absoluteGaloisGroupAbelianization K →ₜ* zHat.{u} :=
  TopologicalAbelianization.lift
    ((maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K) : _ →ₜ* _).comp
      ⟨restrictMaximalUnramifiedHom K, continuous_restrictMaximalUnramifiedHom K⟩)

variable {K}

open scoped IsMulCommutative in
/-- The unramified coordinate of the class of `σ` is the image in `ℤ̂` of the restriction of `σ`
to the maximal unramified extension. -/
@[simp]
theorem unramifiedCoordinate_mk (σ : Field.absoluteGaloisGroup K) :
    unramifiedCoordinate K (σ : Field.absoluteGaloisGroupAbelianization K) =
      maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)
        (restrictMaximalUnramifiedHom K σ) :=
  TopologicalAbelianization.lift_mk _ σ

/-- **Integral coordinates.** The class of `σ` has unramified coordinate `zHat.gen ^ n` exactly
when `σ` acts on the maximal unramified extension as the `n`-th power of its arithmetic
Frobenius. -/
theorem unramifiedCoordinate_mk_eq_gen_zpow_iff (σ : Field.absoluteGaloisGroup K) (n : ℤ) :
    unramifiedCoordinate K (σ : Field.absoluteGaloisGroupAbelianization K) = zHat.gen ^ n ↔
      restrictMaximalUnramifiedHom K σ = maximalUnramifiedFrobenius K (AlgebraicClosure K) ^ n := by
  rw [unramifiedCoordinate_mk, ← maximalUnramifiedGaloisGroupEquivZHat_symm_apply_ofInt,
    zHat.ofInt_ofAdd, ContinuousMulEquiv.eq_symm_apply]

/-- **Arithmetic normalization.** The class of `σ` has unramified coordinate `zHat.gen` exactly
when `σ` is an arithmetic Frobenius lift. -/
theorem unramifiedCoordinate_mk_eq_gen_iff (σ : Field.absoluteGaloisGroup K) :
    unramifiedCoordinate K (σ : Field.absoluteGaloisGroupAbelianization K) = zHat.gen ↔
      IsArithFrobeniusLift K σ := by
  simpa using unramifiedCoordinate_mk_eq_gen_zpow_iff σ 1

/-- Two elements of the absolute Galois group have the same unramified coordinate exactly when they
agree on the unramified extension `K_f` of every degree `f`. -/
theorem unramifiedCoordinate_mk_eq_unramifiedCoordinate_mk_iff
    (σ τ : Field.absoluteGaloisGroup K) :
    unramifiedCoordinate K (σ : Field.absoluteGaloisGroupAbelianization K) =
        unramifiedCoordinate K (τ : Field.absoluteGaloisGroupAbelianization K) ↔
      ∀ (f : ℕ), ∀ x ∈ unramifiedExtension K (AlgebraicClosure K) f,
        DFunLike.coe (F := Gal(AlgebraicClosure K/K)) σ x =
          DFunLike.coe (F := Gal(AlgebraicClosure K/K)) τ x := by
  rw [unramifiedCoordinate_mk, unramifiedCoordinate_mk, EmbeddingLike.apply_eq_iff_eq]
  refine ⟨fun h f x hx ↦ ?_, fun h ↦ AlgEquiv.ext fun y ↦ Subtype.ext ?_⟩
  · have hy := congrArg Subtype.val (AlgEquiv.congr_fun h
      ⟨x, unramifiedExtension_le_maximalUnramifiedExtension K _ f hx⟩)
    rwa [restrictMaximalUnramifiedHom_coe_apply, restrictMaximalUnramifiedHom_coe_apply] at hy
  · obtain ⟨f, -, hf⟩ := mem_maximalUnramifiedExtension_iff.1 y.2
    rw [restrictMaximalUnramifiedHom_coe_apply, restrictMaximalUnramifiedHom_coe_apply]
    exact h f y hf

/-- **The unramified coordinate at finite level.** An element of the absolute Galois group whose
class has unramified coordinate `zHat.gen ^ n` acts on the unramified extension `K_f` of any degree
`f` as the `n`-th power of the arithmetic Frobenius of `K_f / K`. -/
theorem apply_of_unramifiedCoordinate_mk_eq_gen_zpow {f : ℕ}
    [ValuativeRel (unramifiedExtension K (AlgebraicClosure K) f)]
    [TopologicalSpace (unramifiedExtension K (AlgebraicClosure K) f)]
    [IsNonarchimedeanLocalField (unramifiedExtension K (AlgebraicClosure K) f)]
    [ValuativeExtension K (unramifiedExtension K (AlgebraicClosure K) f)]
    [IsUnramified K (unramifiedExtension K (AlgebraicClosure K) f)]
    {σ : Field.absoluteGaloisGroup K} {n : ℤ}
    (hσ : unramifiedCoordinate K (σ : Field.absoluteGaloisGroupAbelianization K) = zHat.gen ^ n)
    {x : AlgebraicClosure K} (hx : x ∈ unramifiedExtension K (AlgebraicClosure K) f) :
    DFunLike.coe (F := Gal(AlgebraicClosure K/K)) σ x =
      (frobeniusAlgEquiv (K := K) (L := unramifiedExtension K (AlgebraicClosure K) f) ^ n)
        ⟨x, hx⟩ := by
  rw [← coe_maximalUnramifiedFrobenius_zpow_apply_of_mem n hx,
    ← (unramifiedCoordinate_mk_eq_gen_zpow_iff σ n).1 hσ, restrictMaximalUnramifiedHom_coe_apply]

/-- The class of `σ` has trivial unramified coordinate exactly when `σ` lies in the inertia
subgroup. -/
theorem unramifiedCoordinate_mk_eq_one_iff (σ : Field.absoluteGaloisGroup K) :
    unramifiedCoordinate K (σ : Field.absoluteGaloisGroupAbelianization K) = 1 ↔
      σ ∈ inertiaSubgroup K := by
  rw [unramifiedCoordinate_mk, map_eq_one_iff _
    (maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)).injective,
    ← MonoidHom.mem_ker, ker_restrictMaximalUnramifiedHom]

variable (K)

/-- **The kernel of the unramified coordinate** is the image of the inertia subgroup in the
topological abelianization. -/
theorem ker_unramifiedCoordinate :
    (unramifiedCoordinate K).toMonoidHom.ker =
      (inertiaSubgroup K).map (QuotientGroup.mk' _) := by
  rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)
    (unramifiedCoordinate K).toMonoidHom.ker]
  congr 1
  ext σ
  exact unramifiedCoordinate_mk_eq_one_iff σ

/-- **The unramified coordinate is surjective**: every element of `ℤ̂` is the coordinate of some
element of the absolute Galois group. -/
theorem unramifiedCoordinate_surjective : Function.Surjective (unramifiedCoordinate K) := by
  intro z
  obtain ⟨σ, hσ⟩ := restrictMaximalUnramifiedHom_surjective K
    ((maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)).symm z)
  exact ⟨σ, by rw [unramifiedCoordinate_mk, hσ, ContinuousMulEquiv.apply_symm_apply]⟩

end TauCeti
