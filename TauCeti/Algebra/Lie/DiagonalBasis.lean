/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basic
public import TauCeti.LinearAlgebra.Eigenspace.DiagonalBasis
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Basis.Bilinear
import TauCeti.Algebra.Lie.Hom

/-!
# Diagonal endomorphisms of Lie algebras

If a Lie algebra endomorphism `P : L →ₗ⁅R⁆ L` is diagonal in a basis `b` with eigenvalues `lam`,
then any diagonal endomorphism `b.diagMap (F ∘ lam)` acts on `⁅b i, b j⁆` by `F (lam i * lam j)`.
Consequently `b.diagMap (F ∘ lam)` is a Lie homomorphism when `F` is multiplicative on products
`lam i * lam j`, and a Lie derivation when `F` is additive on products `lam i * lam j`.

## Main results

* `Module.Basis.diagMap_lie_basis`:
  `b.diagMap (F ∘ lam) ⁅b i, b j⁆ = F (lam i * lam j) • ⁅b i, b j⁆`.
* `Module.Basis.diagMap_map_lie`: `b.diagMap (F ∘ lam)` preserves Lie brackets when
  `F (lam i * lam j) = F (lam i) * F (lam j)`.
* `Module.Basis.diagMap_leibniz`: `b.diagMap (F ∘ lam)` satisfies the Leibniz rule when
  `F (lam i * lam j) = F (lam i) + F (lam j)`.
-/

public section

open LieAlgebra

namespace Module.Basis

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R ι L : Type*} [CommRing R] [IsCancelMulZero R] [LieRing L] [LieAlgebra R L]
  (b : Module.Basis ι R L) (P : L →ₗ⁅R⁆ L) {lam : ι → R}
  (hb : ∀ i, P (b i) = lam i • b i) (F : R → R)
include P hb

/-- A diagonal endomorphism `b.diagMap (F ∘ lam)` associated with a diagonalizable Lie
endomorphism `P` acts on `⁅b i, b j⁆` by `F (lam i * lam j)`. -/
theorem diagMap_lie_basis (i j : ι) :
    b.diagMap (F ∘ lam) ⁅b i, b j⁆ = F (lam i * lam j) • ⁅b i, b j⁆ :=
  b.apply_eq_smul_of_apply_eq_smul (f := P.toLinearMap) hb (fun k hk ↦ by simp [hk])
    (P.map_lie_of_apply_eq_smul (hb i) (hb j))

/-- A diagonal endomorphism `b.diagMap (F ∘ lam)` associated with a diagonalizable Lie
endomorphism `P` preserves Lie brackets whenever `F` turns products `lam i * lam j` into products
`F (lam i) * F (lam j)`. -/
theorem diagMap_map_lie (hF : ∀ i j, F (lam i * lam j) = F (lam i) * F (lam j)) (x y : L) :
    b.diagMap (F ∘ lam) ⁅x, y⁆ = ⁅b.diagMap (F ∘ lam) x, b.diagMap (F ∘ lam) y⁆ := by
  let f := b.diagMap (F ∘ lam)
  have hbil : (LinearMap.llcomp R L L L f).comp (LieAlgebra.ad R L).toLinearMap =
      ((LieAlgebra.ad R L).toLinearMap.compl₂ f).comp f := by
    refine LinearMap.ext_basis b b fun i j ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.llcomp_apply, LinearMap.compl₂_apply,
      LieHom.coe_toLinearMap, ad_apply, f, b.diagMap_lie_basis P hb F i j, hF i j,
      Function.comp_apply, b.diagMap_apply_basis, smul_lie, lie_smul, smul_smul, mul_comm]
  exact LinearMap.congr_fun (LinearMap.congr_fun hbil x) y

/-- A diagonal endomorphism `b.diagMap (F ∘ lam)` associated with a diagonalizable Lie
endomorphism `P` satisfies the Leibniz rule whenever `F` turns products `lam i * lam j` into sums
`F (lam i) + F (lam j)`. -/
theorem diagMap_leibniz (hF : ∀ i j, F (lam i * lam j) = F (lam i) + F (lam j)) (x y : L) :
    b.diagMap (F ∘ lam) ⁅x, y⁆ = ⁅x, b.diagMap (F ∘ lam) y⁆ - ⁅y, b.diagMap (F ∘ lam) x⁆ := by
  let f := b.diagMap (F ∘ lam)
  rw [sub_eq_add_neg, lie_skew (f x) y, add_comm]
  have hbil : (LinearMap.llcomp R L L L f).comp (LieAlgebra.ad R L).toLinearMap =
      (LieAlgebra.ad R L).toLinearMap.comp f + (LieAlgebra.ad R L).toLinearMap.compl₂ f := by
    refine LinearMap.ext_basis b b fun i j ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.llcomp_apply, LinearMap.add_apply,
      LinearMap.compl₂_apply, LieHom.coe_toLinearMap, ad_apply, f, b.diagMap_lie_basis P hb F i j,
      hF i j, Function.comp_apply, b.diagMap_apply_basis, add_smul, smul_lie, lie_smul]
  exact LinearMap.congr_fun (LinearMap.congr_fun hbil x) y

end Module.Basis
