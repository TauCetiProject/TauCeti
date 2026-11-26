/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg
public import TauCeti.Algebra.Lie.Cohomology.FiniteDimensional
public import TauCeti.Algebra.Lie.InvariantForm.Basic

/-!
# The Cartan three-form of an invariant bilinear form

Let `L` be a Lie algebra over a commutative ring `R` and `B : L × L → M` a bilinear map which is
invariant under the adjoint action, `B ⁅x, y⁆ z = -B y ⁅x, z⁆`, as the Killing form is
(`LinearMap.BilinForm.lieInvariant`). Its **Cartan three-form** is the alternating trilinear map

`ω(x, y, z) = B(x, ⁅y, z⁆)`

(`LinearMap.BilinMap.cartanThreeForm`). On a Lie group with Lie algebra `L` and an `Ad`-invariant
form `B`, it is the value at the identity of the left-invariant three-form used to detect the
third homotopy group of compact simple Lie groups, by integrating it over the image of a
homomorphism from `SU(2)`. This file proves its algebraic properties, read in the
Chevalley–Eilenberg complex of `L` with coefficients in a module `M` on which `L` acts
trivially.

* It is invariant under the action of `L` on cochains (`LinearMap.BilinMap.lie_cartanThreeForm`):
  on a connected Lie group, a left-invariant form is right-invariant exactly when its value at the
  identity is killed by this action, so this is the bi-invariance of the Cartan three-form.
* Its interior products are exact: `ι_x ω = -d(B x)`, the coboundary of the one-cochain `B x`
  (`LinearMap.BilinMap.curryLeft_cartanThreeForm`).
* Hence it is a Chevalley–Eilenberg cocycle, `d ω = 0` (`LinearMap.BilinMap.d_cartanThreeForm`),
  by Cartan's formula `ι_x d ω = ⁅x, ω⁆ - d ι_x ω`. On a finite-dimensional topological Lie
  algebra the same holds for the Cartan three-form read as a continuous form, for the
  differential `TauCeti.LieModule.Cohomology.trivialD` that computes the exterior derivative of
  left-invariant forms on a Lie group (`LinearMap.BilinMap.trivialD_cartanThreeForm`).
* It is natural under pullback along Lie algebra morphisms
  (`LinearMap.BilinMap.cartanThreeForm_compl₁₂`), the pulled-back form being again invariant
  (`LinearMap.BilinMap.compl₁₂_lieInvariant`).
* On a triple with `⁅y, z⁆ = x` it takes the value `B x x`
  (`LinearMap.BilinMap.cartanThreeForm_apply_of_lie_eq`). So for an anisotropic form, such as the
  negative-definite Killing form of a compact semisimple Lie algebra, the Cartan three-form
  vanishes exactly when `L` is abelian (`LinearMap.BilinMap.cartanThreeForm_eq_zero_iff`). For
  the basis `e₁, e₂, e₃` of `𝔰𝔲(2)` with `⁅e₂, e₃⁆ = e₁` and its cyclic permutations, and a
  Lie algebra morphism `f` from `𝔰𝔲(2)`, the pulled-back form takes the value
  `B(f e₁, f e₁)` on `(e₁, e₂, e₃)`.

## Main definitions

* `LinearMap.BilinMap.cartanThreeForm`: the Cartan three-form `(x, y, z) ↦ B(x, ⁅y, z⁆)`.

## Main results

* `LinearMap.BilinMap.lie_cartanThreeForm`: the Cartan three-form is `L`-invariant.
* `LinearMap.BilinMap.curryLeft_cartanThreeForm`: its interior products are coboundaries.
* `LinearMap.BilinMap.d_cartanThreeForm`: it is a Chevalley–Eilenberg cocycle.
* `LinearMap.BilinMap.trivialD_cartanThreeForm`: so is its continuous version.
* `LinearMap.BilinMap.cartanThreeForm_compl₁₂`: naturality under Lie algebra morphisms.
* `LinearMap.BilinMap.cartanThreeForm_eq_zero_iff`: for an anisotropic form, it vanishes exactly
  on abelian Lie algebras.

## References

* C. Chevalley and S. Eilenberg, *Cohomology theory of Lie groups and Lie algebras*,
  Trans. Amer. Math. Soc. 63 (1948), 85–124.
-/

public section

open AlternatingMap Fin _root_.LieModule.Cohomology TauCeti.LieModule.Cohomology

namespace LinearMap.BilinMap

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  (B : LinearMap.BilinMap R L M) (hB : ∀ x y z : L, B ⁅x, y⁆ z = -B y ⁅x, z⁆)

/-- The two-cochain `(y, z) ↦ B(x, ⁅y, z⁆)`, the interior product of the Cartan three-form with
`x`. -/
private def cartanTwoForm : L →ₗ[R] L [⋀^Fin 2]→ₗ[R] M :=
  (twoCochainEquiv R L M).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (twoCochain R L M)
      ((LinearMap.llcomp R L L M ∘ₗ B).compl₂ (LieModule.toEnd R L L : L →ₗ[R] Module.End R L))
      fun x ↦ mem_twoCochain_iff.2 fun y ↦ by simp

private theorem cartanTwoForm_apply (x : L) (v : Fin 2 → L) :
    cartanTwoForm B x v = B x ⁅v 0, v 1⁆ := by
  simp [cartanTwoForm, ← twoCochain_val_apply, LinearMap.codRestrict_apply]

/-- **The Cartan three-form** `ω(x, y, z) = B(x, ⁅y, z⁆)` of a bilinear map `B` invariant under
the adjoint action, as an alternating trilinear map. The invariance `hB` makes it alternating:
`B(x, ⁅x, z⁆) = -B(⁅x, x⁆, z) = 0`. -/
def cartanThreeForm : L [⋀^Fin 3]→ₗ[R] M :=
  AlternatingMap.uncurryLeft (cartanTwoForm B) fun x ↦ by
    ext w
    have h := hB x x (w 0)
    rw [lie_self, LinearMap.map_zero₂, eq_comm, neg_eq_zero] at h
    simp [cartanTwoForm_apply, h]

variable {B hB}

@[simp]
theorem cartanThreeForm_apply (v : Fin 3 → L) :
    B.cartanThreeForm hB v = B (v 0) ⁅v 1, v 2⁆ := by
  simp [cartanThreeForm, cartanTwoForm_apply, tail]

/-- The Cartan three-form takes the value `B x x` on a triple `(x, y, z)` with `⁅y, z⁆ = x`. -/
theorem cartanThreeForm_apply_of_lie_eq {x y z : L} (h : ⁅y, z⁆ = x) :
    B.cartanThreeForm hB ![x, y, z] = B x x := by
  simp [h]

/-- **Naturality of the Cartan three-form.** Pulling the Cartan three-form of `B` back along a
Lie algebra morphism `φ` gives the Cartan three-form of the pulled-back form `B(φ ·, φ ·)`. -/
theorem cartanThreeForm_compl₁₂ {L' : Type*} [LieRing L'] [LieAlgebra R L'] (φ : L' →ₗ⁅R⁆ L) :
    cartanThreeForm (B.compl₁₂ φ.toLinearMap φ.toLinearMap) (compl₁₂_lieInvariant hB φ) =
      (B.cartanThreeForm hB).compLinearMap φ.toLinearMap := by
  ext v
  simp

/-- The Cartan three-form of a form on an abelian Lie algebra vanishes. -/
@[simp]
theorem cartanThreeForm_eq_zero_of_isLieAbelian [IsLieAbelian L] : B.cartanThreeForm hB = 0 := by
  ext v
  simp [trivial_lie_zero]

/-- **The Cartan three-form detects the bracket.** For an anisotropic form `B`, for instance the
negative-definite Killing form of a compact semisimple Lie algebra, the Cartan three-form vanishes
exactly when `L` is abelian: if `⁅y, z⁆ = x`, then `ω(x, y, z) = B(x, x)`. -/
theorem cartanThreeForm_eq_zero_iff (hani : B.toQuadraticMap.Anisotropic) :
    B.cartanThreeForm hB = 0 ↔ IsLieAbelian L := by
  refine ⟨fun h ↦ ⟨fun y z ↦ hani _ ?_⟩, fun _ ↦ cartanThreeForm_eq_zero_of_isLieAbelian⟩
  have hval := cartanThreeForm_apply_of_lie_eq (hB := hB) (rfl : ⁅y, z⁆ = ⁅y, z⁆)
  rw [h, zero_apply] at hval
  rw [toQuadraticMap_apply, ← hval]

section Trivial

variable [LieRingModule L M] [LieModule R L M] [LieModule.IsTrivial L M]

/-- **Bi-invariance of the Cartan three-form.** The Cartan three-form is killed by the action of
`L` on cochains with trivial coefficients: this is the invariance of `B` together with the
derivation property `⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆`. -/
@[simp]
theorem lie_cartanThreeForm (x : L) : ⁅x, B.cartanThreeForm hB⁆ = 0 := by
  ext v
  simp only [AlternatingMap.lie_apply, LieModule.IsTrivial.trivial, Fin.sum_univ_three,
    cartanThreeForm_apply, Function.update_self, ne_eq, Fin.reduceEq, not_false_eq_true,
    Function.update_of_ne, zero_apply, zero_sub, neg_eq_zero]
  -- Invariance moves the bracket with `x` off the first slot, and the derivation property of
  -- `ad x` cancels it against the other two.
  rw [hB, leibniz_lie, map_add]
  abel

/-- **The interior products of the Cartan three-form are exact**: `ι_x ω = -d(B x)`, where `B x`
is read as a one-cochain. With trivial coefficients `d(B x)(y, z) = -B(x, ⁅y, z⁆)`. -/
theorem curryLeft_cartanThreeForm (x : L) :
    (B.cartanThreeForm hB).curryLeft x = -d R L M 1 ((oneCochainEquiv R L M).symm (B x)) := by
  ext v
  simp [d_succ_apply, LieModule.IsTrivial.trivial]

/-- **The Cartan three-form is closed**: it is a three-cocycle of the Chevalley–Eilenberg complex
with trivial coefficients. By Cartan's formula `ι_x d ω = ⁅x, ω⁆ - d ι_x ω`, this follows from
the invariance of `ω` and the exactness of its interior products. -/
@[simp]
theorem d_cartanThreeForm : d R L M 3 (B.cartanThreeForm hB) = 0 := by
  refine curryLeft_injective (LinearMap.ext fun x ↦ ?_)
  simp [curryLeft_cartanThreeForm]

end Trivial

section Continuous

variable {𝕜 L N : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [LieRing L] [LieAlgebra 𝕜 L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul 𝕜 L] [T2Space L] [FiniteDimensional 𝕜 L]
  [AddCommGroup N] [Module 𝕜 N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [ContinuousSMul 𝕜 N] {B : LinearMap.BilinMap 𝕜 L N} {hB : ∀ x y z : L, B ⁅x, y⁆ z = -B y ⁅x, z⁆}

/-- **The continuous Cartan three-form is closed.** On a finite-dimensional Hausdorff topological
Lie algebra, the Cartan three-form, read as a continuous alternating form, is a cocycle for the
Chevalley–Eilenberg differential `trivialD` with trivial coefficients. -/
@[simp]
theorem trivialD_cartanThreeForm :
    trivialD 𝕜 L N 3 (AlternatingMap.toContinuousAlternatingMap (B.cartanThreeForm hB)) = 0 := by
  -- Transport `B` to the trivial Lie module `TrivialLieModule 𝕜 L N`, where `d_cartanThreeForm`
  -- applies.
  let e := TrivialLieModule.equiv 𝕜 L N
  have hB' : ∀ x y z : L, B.compr₂ e.symm.toLinearMap ⁅x, y⁆ z =
      -B.compr₂ e.symm.toLinearMap y ⁅x, z⁆ := fun x y z ↦ by simp [hB]
  have h : e.alternatingMapCongrRight.symm (B.cartanThreeForm hB) =
      cartanThreeForm (B.compr₂ e.symm.toLinearMap) hB' := by
    ext v
    simp
  ext v
  rw [trivialD_apply, ← AlternatingMap.toContinuousAlternatingMap_symm_apply,
    LinearEquiv.symm_apply_apply, h, d_cartanThreeForm]
  simp

end Continuous

end LinearMap.BilinMap
