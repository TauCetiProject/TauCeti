/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.RelationModule.Basic
public import TauCeti.NumberTheory.Padics.GroupAlgebra.Cancellation
import Mathlib.LinearAlgebra.TensorProduct.Prod
import TauCeti.Algebra.MonoidAlgebra.RelationModule.FractionRing
import TauCeti.NumberTheory.Padics.GroupAlgebra.Swan
import TauCeti.RingTheory.KrullSchmidt.FractionRing

/-!
# Surjections from relation modules over `ℤ_p[G]`

Let `G` be a finite group, `Λ = ℤ_p[G]` and `I_G ⊆ Λ` the augmentation ideal. Let
`0 → A → Y → I_G → 0` be an exact sequence of `Λ`-modules, and `φ : Λ^ι → Y` a surjection from a
free module of finite rank. For every generating family `g : ι → G` of the same size, the relation
module `relationModule ℤ_[p] G g`, the kernel of `Λ^ι → I_G`, `e_i ↦ g_i - 1`, maps onto `A` with
kernel isomorphic to the kernel of `φ`.

This is how an integral description of `Y` becomes a description of `A` by relation modules: the
two surjections `Λ^ι → I_G`, through `φ` and through `g`, have isomorphic kernels by Schanuel's
lemma and Krull–Schmidt cancellation over `ℤ_p[G]`
(`TauCeti.nonempty_ker_linearEquiv_of_range_eq`), and `φ` carries the first kernel onto `A`.
For `A` the `p`-adic completion of `Lˣ` of a finite Galois layer `L/K` of `p`-adic fields and `Y`
the Tate module of the layer, this gives the surjection `R^ab(p) ↠ A(L)` with kernel `ℤ_p[G]` in
the proof of NSW (7.4.1).

Conversely, a surjection `β` from the relation module of a generating family of size `n + 2` onto a
module `A` with `A ⊗ ℚ_p ≃ ℚ_p[G]^n ⊕ ℚ_p` has a kernel whose rationalization is `ℚ_p[G]`: the
rationalized relation module is `ℚ_p[G]^(n + 1) ⊕ ℚ_p`
(`TauCeti.MonoidAlgebra.nonempty_relationModule_tensor_linearEquiv`), and rational
representations cancel. If that kernel is projective, Swan's theorem
(`TauCeti.nonempty_linearEquiv_of_projective_of_tensorRat`) identifies it with `ℤ_p[G]`. For
`n = [K : ℚ_p]` and `A` the `p`-adic completion of `Lˣ`, whose rationalization is
`ℚ_p[G]^n ⊕ ℚ_p` (`TauCeti.nonempty_padicCompletionUnits_tensorRat_linearEquiv`), this is the
step of NSW (7.4.2)(i) that identifies the kernel of `R^ab(p) ↠ A(L)` with `ℤ_p[G]` once it is
known to be projective.

## Main results

* `TauCeti.exists_relationModule_surjective_of_exact`: the relation module of a generating family
  maps onto the kernel `A` of an extension `0 → A → Y → I_G → 0`, with kernel isomorphic to that of
  a given surjection `Λ^ι → Y`.
* `TauCeti.nonempty_ker_linearEquiv_of_relationModule_surjective`: a surjection from the relation
  module of `n + 2` generators onto a module with rationalization `ℚ_p[G]^n ⊕ ℚ_p` and projective
  kernel has kernel isomorphic to `ℤ_p[G]`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition, (5.6.6),
  (5.6.10)(ii), and the proofs of (7.4.1) and (7.4.2).
-/

public section

open scoped TensorProduct

namespace TauCeti

open _root_.MonoidAlgebra TauCeti.MonoidAlgebra

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] {ι : Type*} [Fintype ι]

local notation "Λ" => _root_.MonoidAlgebra ℤ_[p] G

/-- **The relation module maps onto the kernel of an extension of the augmentation ideal.** Let
`0 → A → Y → I_G → 0` be an exact sequence of `ℤ_p[G]`-modules, for `I_G` the augmentation ideal of
`ℤ_p[G]`, and let `φ : ℤ_p[G]^ι → Y` be onto. For every generating family `g : ι → G`, there is a
surjection from the relation module of `g` onto `A` whose kernel is isomorphic to the kernel of
`φ`. -/
theorem exists_relationModule_surjective_of_exact {A Y : Type*} [AddCommGroup A] [Module Λ A]
    [AddCommGroup Y] [Module Λ Y] {i : A →ₗ[Λ] Y} {π : Y →ₗ[Λ] RingHom.ker (augmentation ℤ_[p] G)}
    (hiπ : Function.Exact i π) (hi : Function.Injective i) (hπ : Function.Surjective π)
    {φ : (ι → Λ) →ₗ[Λ] Y} (hφ : Function.Surjective φ) {g : ι → G}
    (hg : Subgroup.closure (Set.range g) = ⊤) :
    ∃ β : relationModule ℤ_[p] G g →ₗ[Λ] A, Function.Surjective β ∧
      Nonempty (LinearMap.ker β ≃ₗ[Λ] LinearMap.ker φ) := by
  set c := Fintype.linearCombination Λ fun i ↦ single (g i) (1 : ℤ_[p]) - 1
  -- The presentation `c` of `I_G` by `g` and the presentation `π ∘ φ` have isomorphic kernels.
  let c' := c.codRestrict (RingHom.ker (augmentation ℤ_[p] G)) fun x ↦
    range_linearCombination_le_ker_augmentation g (LinearMap.mem_range_self c x)
  have hc' : LinearMap.range c' = ⊤ := by
    rw [LinearMap.range_codRestrict, range_linearCombination_eq_ker_augmentation hg,
      Submodule.comap_subtype_self]
  obtain ⟨e⟩ := nonempty_ker_linearEquiv_of_range_eq
    (hc'.trans ((LinearMap.range_eq_top (f := π ∘ₗ φ)).mpr (hπ.comp hφ)).symm)
  -- `φ` carries `ker (π ∘ φ)` into `ker π = range i ≅ A`.
  have hmem (x : LinearMap.ker (π ∘ₗ φ)) : φ x ∈ LinearMap.range i :=
    (hiπ (φ x)).mp (LinearMap.mem_ker.mp x.2)
  let β₀ : LinearMap.ker (π ∘ₗ φ) →ₗ[Λ] A :=
    (LinearEquiv.ofInjective i hi).symm.toLinearMap ∘ₗ (φ.restrict fun x hx ↦ hmem ⟨x, hx⟩)
  have hβ₀ (x : LinearMap.ker (π ∘ₗ φ)) : i (β₀ x) = φ x := by
    simp [β₀]
  have hkerβ₀ : LinearMap.ker β₀ = (LinearMap.ker φ).comap (LinearMap.ker (π ∘ₗ φ)).subtype := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    rw [← hi.eq_iff, hβ₀, map_zero]
  -- Read the presentation `c` through its kernel, the relation module of `g`.
  let E : relationModule ℤ_[p] G g ≃ₗ[Λ] LinearMap.ker (π ∘ₗ φ) :=
    .ofEq _ _ ((relationModule_def g).trans (LinearMap.ker_codRestrict _ _ _).symm) ≪≫ₗ e
  refine ⟨β₀ ∘ₗ E.toLinearMap, fun a ↦ ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hφ (i a)
    have hx' : x ∈ LinearMap.ker (π ∘ₗ φ) := by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, hx]
      exact (hiπ _).mpr ⟨a, rfl⟩
    exact ⟨E.symm ⟨x, hx'⟩, hi (by simp [hβ₀, hx])⟩
  · exact ⟨E.ofSubmodules _ _ (by rw [LinearMap.ker_comp E.toLinearMap β₀,
      Submodule.map_comap_eq_of_surjective E.surjective]) ≪≫ₗ .ofEq _ _ hkerβ₀ ≪≫ₗ
      Submodule.comapSubtypeEquivOfLe (LinearMap.ker_le_ker_comp φ π)⟩

/-- **A projective kernel of a relation-module surjection is free of rank one.** Let `G` be a finite
group, `g` a generating family of `G` with `n + 2` members, and `β` a surjection from the relation
module of `g` onto a `ℤ_p[G]`-module `A` whose rationalization is
`(ℤ_p[G]^n × ℤ_p[G] ⧸ I_G) ⊗ ℚ_p`, that is, `ℚ_p[G]^n ⊕ ℚ_p`. If the kernel of `β` is projective,
then it is isomorphic to `ℤ_p[G]`. -/
theorem nonempty_ker_linearEquiv_of_relationModule_surjective {A : Type*} [AddCommGroup A]
    [Module ℤ_[p] A] [Module Λ A] [IsScalarTower ℤ_[p] Λ A] {g : ι → G}
    (hg : Subgroup.closure (Set.range g) = ⊤) {n : ℕ} (hι : Fintype.card ι = n + 2)
    {β : relationModule ℤ_[p] G g →ₗ[Λ] A} (hβ : Function.Surjective β)
    [Module.Projective Λ (LinearMap.ker β)]
    (hA : Nonempty ((A ⊗[ℤ_[p]] ℚ_[p]) ≃ₗ[Λ]
      (((Fin n → Λ) × (Λ ⧸ RingHom.ker (augmentation ℤ_[p] G))) ⊗[ℤ_[p]] ℚ_[p]))) :
    Nonempty (LinearMap.ker β ≃ₗ[Λ] Λ) := by
  obtain ⟨eA⟩ := hA
  have : NeZero (Nat.card G : ℤ_[p]) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  -- Rationally, `relationModule ℤ_[p] G g ≃ ker β ⊕ A`, and it is `ℚ_p[G]^(n + 1) ⊕ ℚ_p`.
  obtain ⟨e₁⟩ := IsFractionRing.nonempty_tensor_linearEquiv_prod_of_exact ℚ_[p]
    (LinearMap.exact_subtype_ker_map β) (Submodule.injective_subtype _) hβ
  obtain ⟨e₂⟩ := nonempty_relationModule_tensor_linearEquiv (R := ℤ_[p]) ℚ_[p] hg hι
  let e₃ : ((Fin (n + 1) → Λ) × (Λ ⧸ RingHom.ker (augmentation ℤ_[p] G))) ≃ₗ[Λ]
      Λ × ((Fin n → Λ) × (Λ ⧸ RingHom.ker (augmentation ℤ_[p] G))) :=
    (Fin.consLinearEquiv Λ fun _ : Fin (n + 1) ↦ Λ).symm.prodCongr (.refl Λ _) ≪≫ₗ
      LinearEquiv.prodAssoc Λ _ _ _
  -- So `(ker β × X) ⊗ ℚ_p ≃ (ℤ_p[G] × X) ⊗ ℚ_p` for `X = ℤ_p[G]^n × ℤ_p[G] ⧸ I_G`, and
  -- `X ⊗ ℚ_p` cancels, as `X` is finitely generated over `ℤ_p`.
  obtain ⟨e⟩ := IsFractionRing.nonempty_tensor_linearEquiv_of_prod_tensor_linearEquiv ℚ_[p]
    (M := LinearMap.ker β) (N := Λ)
    ⟨TensorProduct.prodLeft _ _ _ _ _ ≪≫ₗ (LinearEquiv.refl Λ _).prodCongr eA.symm ≪≫ₗ
      (TensorProduct.prodLeft _ _ _ _ _).symm ≪≫ₗ e₁.symm ≪≫ₗ e₂ ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr e₃ (.refl ℤ_[p] ℚ_[p])⟩
  -- `ker β` is finitely generated, as a submodule of `ℤ_p[G]^ι`, so Swan's theorem applies.
  have : Module.Finite ℤ_[p] (LinearMap.ker β) := .of_injective
    ((relationModule ℤ_[p] G g).subtype.restrictScalars ℤ_[p] ∘ₗ
      (LinearMap.ker β).subtype.restrictScalars ℤ_[p])
    ((Submodule.injective_subtype _).comp (Submodule.injective_subtype _))
  have : Module.Finite Λ (LinearMap.ker β) := .of_restrictScalars_finite ℤ_[p] Λ _
  exact nonempty_linearEquiv_of_projective_of_tensorRat p (G := G) (LinearMap.ker β) Λ ⟨e⟩

end TauCeti
