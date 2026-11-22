/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.GradedAlgebra.Basic
import TauCeti.Algebra.Category.GradedModuleCat.Free.Coordinates
import TauCeti.Algebra.Category.GradedModuleCat.Free.Range

/-!
# Degree-multiset uniqueness for rank-one homogeneous projections

Let `A` be a connected nonnegatively `ℤ`-graded `k`-algebra (`𝒜 : ℤ → Submodule k A`), and view
the finite function module `I → A` (`[Finite I]`) as the shifted free graded `A`-module with `j`th
summand in shift `s j : ℤ`.

Using `TauCeti.GradedModuleCat.multiset_map_eq_of_homogeneous_basis_range`, this file records the
rank-one projection corollary:

* `TauCeti.multiset_map_eq_singleton_of_homogeneous_basis_range`: any rank-one homogeneous
  projection `p v = v i₀ • w` (`w i₀ = 1`, `∀ j, w j ∈ 𝒜 (s i₀ - s j)`) has unique basis degree
  multiset `{s i₀}`.

## References

* L.-H. Robert and E. Wagner, *Symmetric Khovanov–Rozansky link homologies*, J. Éc. polytech.
  Math. 7 (2020), 573–651, Lemma 3.30.
-/

public section

open CategoryTheory _root_.DirectSum

namespace TauCeti

universe uk uA uI

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

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
  let ι : (Fin 1 → A) →ₗ[A] (I → A) :=
    (LinearMap.proj (R := A) (φ := fun _ : Fin 1 ↦ A) 0).smulRight w
  have hleft : Function.LeftInverse (fun (v : I → A) (_ : Fin 1) ↦ v i₀) ι := fun u ↦
    funext fun t ↦ by
      rw [Fin.eq_zero t]
      simp [ι, hw₀]
  have hrange : LinearMap.range ι = LinearMap.range p := by
    ext x
    simp only [LinearMap.mem_range, ι, LinearMap.smulRight_apply, LinearMap.proj_apply, hp]
    exact ⟨fun ⟨u, hu⟩ ↦ ⟨Function.const I (u 0), hu⟩, fun ⟨v, hv⟩ ↦ ⟨fun _ ↦ v i₀, hv⟩⟩
  let e₁ : (Fin 1 → A) ≃ₗ[A] LinearMap.range p :=
    (LinearEquiv.ofLeftInverse hleft).trans (LinearEquiv.ofEq _ _ hrange)
  let b₀ : Module.Basis (Fin 1) A (LinearMap.range p) := (Pi.basisFun A (Fin 1)).map e₁
  have hb₀ : ∀ (i : Fin 1) (j : I), (b₀ i).val j ∈ 𝒜 (s i₀ - s j) := fun i j ↦ by
    rw [Fin.eq_zero i]
    have hval : (b₀ 0).val = w := by
      dsimp only [b₀]
      rw [Module.Basis.map_apply, Pi.basisFun_apply]
      change ι (Pi.single 0 1) = w
      simp [ι]
    rw [hval]
    exact hw j
  have h := GradedModuleCat.multiset_map_eq_of_homogeneous_basis_range hneg hzero s p
    (GradedModuleCat.homogeneous_of_apply_eq_smul s i₀ hp hw) b d hb b₀ (fun _ ↦ s i₀) hb₀
  simpa using h

end TauCeti
