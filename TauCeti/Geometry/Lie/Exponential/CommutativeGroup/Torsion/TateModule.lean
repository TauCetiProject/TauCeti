/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.TateModule.Snake
public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Torsion.Lattice

/-!
# The Tate module of a commutative Lie group

For a preconnected commutative Lie group `G` the exponential gives a short exact sequence
`0 → Λ → 𝔤 → G → 0` of abelian groups, with `Λ` the exponential lattice. Multiplication by a
nonzero integer is bijective on the real vector space `𝔤`, so the Tate module of a cokernel
(`TauCeti.tateModuleδEquiv`) identifies the `p`-adic Tate module of `G` with the `p`-adic
completion `lim Λ ⧸ pⁿΛ` of `Λ`. A compatible family of points `exp(λₙ / pⁿ)` goes to the family
of classes of the `λₙ`. The lattice `Λ` is finitely generated (`TauCeti.finite_lieExpLattice`), so
for prime `p` the Tate module is `ℤ_[p] ⊗ Λ` as a `ℤ_[p]`-module (`TauCeti.tateModuleδPadicEquiv`).

These are the inverse limits of the level-`n` torsion isomorphisms `TauCeti.lieExpTorsionEquiv`.

## Main definitions

* `TauCeti.lieExpTateModuleEquiv`: `T_p G ≃ lim Λ ⧸ pⁿΛ` for `p ≠ 0`.
* `TauCeti.lieExpTateModulePadicEquiv`: `T_p G ≃ₗ[ℤ_[p]] ℤ_[p] ⊗ Λ` for prime `p`.

## Main statements

* `TauCeti.lieExpTateModuleEquiv_apply_val`: if `exp X` is the `n`-th level of `x` and
  `pⁿ X = λ ∈ Λ`, the `n`-th component of the image of `x` is the class of `λ`.
* `TauCeti.proj_lieExpTateModuleEquiv_symm`: the `n`-th level of the point with `n`-th component
  `[λ]` is `exp(λ / pⁿ)`.
* `TauCeti.lieExpTateModulePadicEquiv_symm_apply`: the inverse of the `ℤ_[p]`-linear form passes
  through the `p`-adic completion of `Λ`.

The Check for the circle is in `TauCeti.Examples.Geometry.Lie.Exponential.CircleTorsion`.
-/

public section

noncomputable section

namespace TauCeti

open scoped ContDiff Manifold TensorProduct IsMulCommutative

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

section Completion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  [IsMulCommutative G] [PreconnectedSpace G] (p : ℕ)

variable (I G) in
/-- **The Tate module of a preconnected commutative Lie group is the `p`-adic completion of its
exponential lattice**, for `p ≠ 0`: `TauCeti.tateModuleδEquiv` for `0 → Λ → 𝔤 → G → 0`. -/
def lieExpTateModuleEquiv (hp : p ≠ 0) :
    TateModule p (Additive G) ≃+
      AdicCompletion (Ideal.span {(p : ℤ)}) (lieExpLattice (I := I) (G := G)) :=
  tateModuleδEquiv p exact_subtype_lieExpLattice (lieExpLattice (I := I) (G := G)).injective_subtype
    surjective_toIntLinearMap_lieExpAddMonoidHom
    (bijective_zsmul_of_ne_zero ℝ (Int.natCast_ne_zero.mpr hp))

/-- **The components of the Tate-module isomorphism**: if `exp X` is the `n`-th level of `x` and
`pⁿ X = λ ∈ Λ`, then the `n`-th component of the image of `x` is the class of `λ`. -/
theorem lieExpTateModuleEquiv_apply_val (hp : p ≠ 0) (x : TateModule p (Additive G)) {n : ℕ}
    {X : LeftInvariantDerivation I G}
    (hX : Additive.ofMul (lieExp X) = (TateModule.proj n x : Additive G))
    {l : lieExpLattice (I := I) (G := G)}
    (hl : (l : LeftInvariantDerivation I G) = ((p ^ n : ℕ) : ℤ) • X) :
    (lieExpTateModuleEquiv I G p hp x).val n = Submodule.Quotient.mk l := by
  rw [lieExpTateModuleEquiv, tateModuleδEquiv_apply, tateModuleδ_apply_val]
  exact tateModuleLevelδ_eq p _ _ _ _
    (by rw [AddMonoidHom.coe_toIntLinearMap, lieExpAddMonoidHom_apply, hX]) hl

/-- **The inverse of the Tate-module isomorphism**: the `n`-th level of the point whose `n`-th
component is the class of `λ ∈ Λ` is `exp(λ / pⁿ)`. -/
theorem proj_lieExpTateModuleEquiv_symm (hp : p ≠ 0)
    (c : AdicCompletion (Ideal.span {(p : ℤ)}) (lieExpLattice (I := I) (G := G))) {n : ℕ}
    {l : lieExpLattice (I := I) (G := G)} (hc : c.val n = Submodule.Quotient.mk l) :
    (TateModule.proj n ((lieExpTateModuleEquiv I G p hp).symm c) : Additive G) =
      Additive.ofMul (lieExp (((p ^ n : ℕ) : ℝ)⁻¹ • (l : LeftInvariantDerivation I G))) := by
  have hpn : (((p ^ n : ℕ) : ℤ) : ℝ) ≠ 0 := by exact_mod_cast pow_ne_zero n hp
  have hl : (l : LeftInvariantDerivation I G) =
      ((p ^ n : ℕ) : ℤ) • (((p ^ n : ℕ) : ℤ) : ℝ)⁻¹ • (l : LeftInvariantDerivation I G) := by
    rw [← Int.cast_smul_eq_zsmul ℝ, smul_inv_smul₀ hpn]
  rw [lieExpTateModuleEquiv, proj_tateModuleδEquiv_symm_eq_of_tateModuleLevelδ_eq p _ _ _ _ c
    (y := ⟨_, lieExp_inv_smul_mem_torsionBy (I := I) _ (by exact_mod_cast hpn) l⟩)
    ((tateModuleLevelδ_eq p _ _ _ _
      (by rw [AddMonoidHom.coe_toIntLinearMap, lieExpAddMonoidHom_apply]) hl).trans hc.symm)]
  simp only [Int.cast_natCast]

end Completion

section Padic

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  [IsMulCommutative G] [PreconnectedSpace G] (p : ℕ) [Fact p.Prime]

variable (I G) in
/-- **The Tate module of a preconnected commutative Lie group is `ℤ_[p] ⊗ Λ`**, as a
`ℤ_[p]`-module, for prime `p`: `TauCeti.tateModuleδPadicEquiv` for `0 → Λ → 𝔤 → G → 0`. -/
def lieExpTateModulePadicEquiv :
    TateModule p (Additive G) ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] lieExpLattice (I := I) (G := G) :=
  tateModuleδPadicEquiv p exact_subtype_lieExpLattice
    (lieExpLattice (I := I) (G := G)).injective_subtype
    surjective_toIntLinearMap_lieExpAddMonoidHom
    (bijective_zsmul_of_ne_zero ℝ (Int.natCast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))

/-- `PadicInt.tensorAdicCompletionEquiv` turns the `ℤ_[p] ⊗ Λ` form into the `p`-adic completion
form `TauCeti.lieExpTateModuleEquiv`. -/
@[simp]
theorem tensorAdicCompletionEquiv_lieExpTateModulePadicEquiv (x : TateModule p (Additive G)) :
    PadicInt.tensorAdicCompletionEquiv p _ (lieExpTateModulePadicEquiv I G p x) =
      lieExpTateModuleEquiv I G p (Fact.out : p.Prime).ne_zero x :=
  tensorAdicCompletionEquiv_tateModuleδPadicEquiv p _ _ _ _ x

/-- The inverse equivalence is `PadicInt.tensorAdicCompletionEquiv` followed by the inverse of
`TauCeti.lieExpTateModuleEquiv`. -/
theorem lieExpTateModulePadicEquiv_symm_apply (t : ℤ_[p] ⊗[ℤ] lieExpLattice (I := I) (G := G)) :
    (lieExpTateModulePadicEquiv I G p).symm t =
      (lieExpTateModuleEquiv I G p (Fact.out : p.Prime).ne_zero).symm
        (PadicInt.tensorAdicCompletionEquiv p _ t) :=
  tateModuleδPadicEquiv_symm_apply p _ _ _ _ t

end Padic

end TauCeti
