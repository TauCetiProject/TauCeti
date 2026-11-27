/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.Module.LinearMap.DivisionRing
import TauCeti.Algebra.Category.GradedModuleCat.Free.Coordinates
import TauCeti.Algebra.Category.GradedModuleCat.Free.Head

/-!
# Degree-multiset uniqueness for homogeneous bases of graded endomorphism ranges

Let `A` be a connected nonnegatively `ℤ`-graded `k`-algebra (`𝒜 : ℤ → Submodule k A`), and view
the finite function module `I → A` (`[Finite I]`) as the shifted free graded `A`-module with `j`th
summand in shift `s j : ℤ`.

Using the coordinate transport of `TauCeti.Algebra.Category.GradedModuleCat.Free.Coordinates`
and the graded head-coordinate theory of `TauCeti.Algebra.Category.GradedModuleCat.Free.Head`,
this file proves PID-free uniqueness of shift multisets for homogeneous bases of ranges of
degree-zero endomorphisms on `I → A`:

* `TauCeti.GradedModuleCat.multiset_map_eq_of_homogeneous_basis_range`: over a nontrivial
  commutative base ring `k`, any two finite homogeneous `A`-bases of `LinearMap.range p` have
  the same multiset of shifts.
* `TauCeti.GradedModuleCat.multiset_map_eq_singleton_of_homogeneous_basis_range`: any rank-one
  homogeneous projection `p v = v i₀ • w` (`w i₀ = 1`, `∀ j, w j ∈ 𝒜 (s i₀ - s j)`) has unique
  basis degree multiset `{s i₀}`.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
* T. Y. Lam, *Serre's Problem on Projective Modules*, Chapter II, §4.
-/

public section

open CategoryTheory _root_.DirectSum

namespace TauCeti.GradedModuleCat

universe uk uA uI

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- Over a nontrivial commutative ring `k`, any two finite homogeneous bases of the range of a
degree-zero endomorphism `p : (I → A) →ₗ[A] (I → A)` (`[Finite I]`) have the same multiset of
degrees. -/
theorem multiset_map_eq_of_homogeneous_basis_range
    [Nontrivial k] [FaithfulSMul k A]
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} [Finite I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A))
    (hhom : ∀ (d : ℤ) (v : I → A),
      (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j))
    {n₁ n₂ : ℕ}
    (b₁ : Module.Basis (Fin n₁) A (LinearMap.range p)) (d₁ : Fin n₁ → ℤ)
    (hb₁ : ∀ i j, (b₁ i).val j ∈ 𝒜 (d₁ i - s j))
    (b₂ : Module.Basis (Fin n₂) A (LinearMap.range p)) (d₂ : Fin n₂ → ℤ)
    (hb₂ : ∀ i j, (b₂ i).val j ∈ 𝒜 (d₂ i - s j)) :
    Multiset.map d₁ Finset.univ.val = Multiset.map d₂ Finset.univ.val := by
  cases nonempty_fintype I
  let equivRange := rangeEquivRangeObj s p hhom
  let mkIso : ∀ {n : ℕ} (b : Module.Basis (Fin n) A (LinearMap.range p)) (d : Fin n → ℤ),
      (∀ i j, (b i).val j ∈ 𝒜 (d i - s j)) →
        (free 𝒜 (d ∘ ULift.down) ≅ rangeObjOfPiEnd s p hhom) :=
    fun b d hb ↦ ((b.reindex Equiv.ulift.symm).map equivRange).isoGradedFree fun i ↦ by
      rw [Module.Basis.map_apply, Module.Basis.reindex_apply]
      exact (mem_rangeObjOfPiEnd_piece_iff_coord s p hhom).mpr (hb i.down)
  have hU := multiset_map_eq_of_iso_free hneg hzero
    ((mkIso b₁ d₁ hb₁).trans (mkIso b₂ d₂ hb₂).symm)
  have huniv : ∀ {n : ℕ} (d : Fin n → ℤ),
      Multiset.map (d ∘ ULift.down) (Finset.univ : Finset (ULift.{uI} (Fin n))).val =
        Multiset.map d Finset.univ.val := fun d ↦ by
    rw [← Multiset.map_map]
    exact congrArg (Multiset.map d)
      (congrArg Finset.val (Finset.map_univ_equiv (Equiv.ulift (α := Fin _))))
  rwa [huniv d₁, huniv d₂] at hU

/-- Over a connected nonnegatively graded `k`-algebra (`Nontrivial k`), any finite homogeneous basis
of the range of a rank-one homogeneous projection `p v = v i₀ • w` (`w i₀ = 1`,
`∀ j, w j ∈ 𝒜 (s i₀ - s j)`) has degree multiset `{s i₀}`. -/
theorem multiset_map_eq_singleton_of_homogeneous_basis_range
    [Nontrivial k] [FaithfulSMul k A]
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} [Finite I] (s : I → ℤ)
    {p : (I → A) →ₗ[A] (I → A)} (i₀ : I) {w : I → A}
    (hp : ∀ v, p v = v i₀ • w) (hw₀ : w i₀ = 1) (hw : ∀ j, w j ∈ 𝒜 (s i₀ - s j))
    {n : ℕ} (b : Module.Basis (Fin n) A (LinearMap.range p))
    (d : Fin n → ℤ) (hb : ∀ i j, (b i).val j ∈ 𝒜 (d i - s j)) :
    Multiset.map d Finset.univ.val = {s i₀} := by
  have hp_eq : p = (LinearMap.proj i₀).smulRight w := LinearMap.ext fun v ↦ hp v
  have hleft : Function.LeftInverse (LinearMap.proj i₀ : (I → A) →ₗ[A] A)
      (LinearMap.toSpanSingleton A (I → A) w) := fun a ↦ by simp [hw₀]
  have hrange : LinearMap.range (LinearMap.toSpanSingleton A (I → A) w) = LinearMap.range p := by
    rw [LinearMap.range_toSpanSingleton, hp_eq,
      LinearMap.range_smulRight_apply_of_surjective (LinearMap.proj_surjective i₀)]
  let e₁ : A ≃ₗ[A] LinearMap.range p :=
    (LinearEquiv.ofLeftInverse hleft).trans (LinearEquiv.ofEq _ _ hrange)
  let b₀ : Module.Basis (Fin 1) A (LinearMap.range p) := (Module.Basis.singleton (Fin 1) A).map e₁
  have hb₀ : ∀ (i : Fin 1) (j : I), (b₀ i).val j ∈ 𝒜 (s i₀ - s j) := fun i j ↦ by
    have hval : (b₀ i).val = w := by
      rw [Module.Basis.map_apply, Module.Basis.singleton_apply]
      dsimp only [e₁]
      rw [LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
        LinearEquiv.ofLeftInverse_apply, LinearMap.toSpanSingleton_apply, one_smul]
    rw [hval]
    exact hw j
  have h := multiset_map_eq_of_homogeneous_basis_range hneg hzero s p
    (homogeneous_of_apply_eq_smul s i₀ hp hw) b d hb b₀ (fun _ ↦ s i₀) hb₀
  simpa using h

end TauCeti.GradedModuleCat
