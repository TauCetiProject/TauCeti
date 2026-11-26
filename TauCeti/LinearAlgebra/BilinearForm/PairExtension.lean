/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Extending a pair of maps compatible with a nondegenerate bilinear form

Let `B` be a nondegenerate bilinear form on a finite-dimensional vector space `V`, and let
`f₁ : W₁ → V` and `f₂ : W₂ → V` be injective linear maps from two subspaces with
`B (f₂ b) (f₁ a) = B b a`. Then `f₁` and `f₂` extend to linear automorphisms `g₁` and `g₂` of `V`
with `B (g₂ w) (g₁ v) = B w v` for all `w`, `v`: the automorphism `g₂` is the inverse of the
adjoint of `g₁`. This is Witt's extension theorem for the split quadratic algebra `F × F`, where a
hermitian space is a pair of spaces put in duality by `B` and its unitary group is `GL(V)` acting
on the second space through the contragredient
(`TauCeti/LinearAlgebra/SesquilinearForm/SignedHermitianSpace/SplitWitt.lean`). The subspaces
`W₁` and `W₂` are arbitrary: neither their dimensions nor the restriction of `B` to them is
constrained.

The proof builds `g₁` in three pieces. With `A` (resp. `A'`) the vectors orthogonal to `W₂`
(resp. to `f₂ W₂`), `g₁` is `f₁` on `W₁`, an isomorphism `A ≃ A'` extending `f₁` on `W₁ ⊓ A`, and
on a complement of `W₁ ⊔ A` a lift of the functional `B (·) v` on `W₂` through `f₂`. Then
`B (f₂ b) (g₁ v) = B b v` for all `v`, which forces `g₁` to be injective and determines `g₂`.

## Main statements

* `LinearMap.exists_linearEquiv_apply_eq_of_injective`: an injective linear map from a subspace
  of `M` into a space of the same finite dimension extends to a linear equivalence.
* `LinearMap.BilinForm.exists_linearEquiv_pair_extend`: the extension of a compatible pair.
-/

public section

open Module Function

namespace LinearMap

variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- An injective linear map from a subspace `S` of `M` into a space `N` of the same finite
dimension extends to a linear equivalence `M ≃ N`. -/
theorem exists_linearEquiv_apply_eq_of_injective [FiniteDimensional K M] [FiniteDimensional K N]
    {S : Submodule K M} (f : S →ₗ[K] N) (hf : Injective f) (h : finrank K M = finrank K N) :
    ∃ e : M ≃ₗ[K] N, ∀ s : S, e s = f s := by
  obtain ⟨S', hS'⟩ := S.exists_isCompl
  obtain ⟨T', hT'⟩ := (range f).exists_isCompl
  have h₁ := Submodule.finrank_add_eq_of_isCompl hS'
  have h₂ := Submodule.finrank_add_eq_of_isCompl hT'
  rw [finrank_range_of_inj hf] at h₂
  let j : S' ≃ₗ[K] T' := LinearEquiv.ofFinrankEq _ _ (by lia)
  refine ⟨(Submodule.prodEquivOfIsCompl S S' hS').symm ≪≫ₗ
    ((LinearEquiv.ofInjective f hf).prodCongr j) ≪≫ₗ Submodule.prodEquivOfIsCompl _ T' hT',
    fun s ↦ ?_⟩
  simp

namespace BilinForm

variable {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [FiniteDimensional K V] {B : LinearMap.BilinForm K V}

/-- For an injective `f : W → V`, the vectors `v` with `B (f b) v = 0` for every `b` form a
subspace of codimension `dim W`. -/
private theorem finrank_ker_flip_comp (hB : B.Nondegenerate) (f : W →ₗ[K] V) (hf : Injective f) :
    finrank K (ker (B ∘ₗ f).flip) = finrank K V - finrank K W := by
  have : ker (B ∘ₗ f).flip = B.orthogonal (range f) := by
    ext v
    rw [mem_ker, mem_orthogonal_iff]
    refine ⟨fun h _ ⟨b, hb⟩ ↦ hb ▸ by simpa using LinearMap.congr_fun h b,
      fun h ↦ LinearMap.ext fun b ↦ by simpa using h _ ⟨b, rfl⟩⟩
  rw [this, finrank_orthogonal hB, finrank_range_of_inj hf]

/-- For an injective `f : W → V`, every linear functional on `W` is `B (f ·) v` for some `v`. -/
private theorem range_flip_comp (hB : B.Nondegenerate) (f : W →ₗ[K] V) (hf : Injective f) :
    range (B ∘ₗ f).flip = ⊤ := by
  have : FiniteDimensional K W := Module.Finite.of_injective f hf
  refine Submodule.eq_top_of_finrank_eq ?_
  have h₁ := finrank_range_add_finrank_ker (B ∘ₗ f).flip
  have h₂ := finrank_ker_flip_comp hB f hf
  have h₃ : finrank K W ≤ finrank K V := finrank_le_finrank_of_injective hf
  rw [Subspace.dual_finrank_eq]
  lia

/-- With `A` and `A'` the vectors orthogonal to `W₂` and to `f₂ W₂`, an isomorphism `A ≃ A'`
extending `f₁` on `W₁ ⊓ A`. -/
private theorem exists_linearEquiv_ker (hB : B.Nondegenerate) {W₁ W₂ : Submodule K V}
    (f₁ : W₁ →ₗ[K] V) (f₂ : W₂ →ₗ[K] V) (hf₁ : Injective f₁) (hf₂ : Injective f₂)
    (hf : ∀ (a : W₁) (b : W₂), B (f₂ b) (f₁ a) = B b a) :
    ∃ φ : ker (B ∘ₗ W₂.subtype).flip ≃ₗ[K] ker (B ∘ₗ f₂).flip,
      ∀ (a : W₁) (ha : (a : V) ∈ ker (B ∘ₗ W₂.subtype).flip), (φ ⟨a, ha⟩ : V) = f₁ a := by
  set Φ := (B ∘ₗ W₂.subtype).flip
  set Φ' := (B ∘ₗ f₂).flip
  have hΦ (a : W₁) : Φ' (f₁ a) = Φ a := LinearMap.ext fun b ↦ hf a b
  have hA : finrank K (ker Φ) = finrank K (ker Φ') := by
    rw [finrank_ker_flip_comp hB _ W₂.injective_subtype, finrank_ker_flip_comp hB _ hf₂]
  let S : Submodule K (ker Φ) := W₁.comap (ker Φ).subtype
  let f₀ : S →ₗ[K] ker Φ' := codRestrict (ker Φ')
    (f₁ ∘ₗ (ker Φ).subtype.restrict (p := S) (q := W₁) fun _ hx ↦ hx)
    fun s ↦ by simp [mem_ker, hΦ]
  have hf₀ : Injective f₀ := fun s t hst ↦ by
    have := hf₁ (congrArg Subtype.val hst)
    exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val this))
  obtain ⟨φ, hφ⟩ := f₀.exists_linearEquiv_apply_eq_of_injective hf₀ hA
  exact ⟨φ, fun a ha ↦ congrArg Subtype.val (hφ ⟨⟨a, ha⟩, a.property⟩)⟩

/-- The automorphism `g₁` of `exists_linearEquiv_pair_extend`: it extends `f₁` and satisfies
`B (f₂ b) (g₁ v) = B b v`. -/
private theorem exists_linearEquiv_flip_comp_eq (hB : B.Nondegenerate) {W₁ W₂ : Submodule K V}
    (f₁ : W₁ →ₗ[K] V) (f₂ : W₂ →ₗ[K] V) (hf₁ : Injective f₁) (hf₂ : Injective f₂)
    (hf : ∀ (a : W₁) (b : W₂), B (f₂ b) (f₁ a) = B b a) :
    ∃ g₁ : V ≃ₗ[K] V, (∀ a : W₁, g₁ a = f₁ a) ∧ ∀ (b : W₂) v, B (f₂ b) (g₁ v) = B b v := by
  classical
  -- `Φ v = B (·) v` on `W₂` and `Φ' v = B (f₂ ·) v`, with kernels `A` and `A'`.
  set Φ := (B ∘ₗ W₂.subtype).flip
  set Φ' := (B ∘ₗ f₂).flip
  have hΦ (a : W₁) : Φ' (f₁ a) = Φ a := LinearMap.ext fun b ↦ hf a b
  obtain ⟨φ, hφ⟩ := exists_linearEquiv_ker hB f₁ f₂ hf₁ hf₂ hf
  -- Glue `f₁` on `W₁` and `φ` on `A`, then extend by a lift of `Φ` through `Φ'`.
  let g₀ : V →ₗ.[K] V := LinearPMap.sup ⟨W₁, f₁⟩ ⟨ker Φ, (ker Φ').subtype ∘ₗ φ.toLinearMap⟩
    fun x y hxy ↦ by
      simp only [LinearPMap.mk_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        Submodule.coe_subtype]
      have hy : y = ⟨x, hxy ▸ y.property⟩ := Subtype.ext hxy.symm
      rw [hy, hφ x]
  have hg₀ (a : W₁) (z : ker Φ) (y : g₀.domain) (h : (a : V) + z = y) :
      g₀ y = f₁ a + φ z := (LinearPMap.sup_apply _ a z y h).trans (by simp)
  obtain ⟨C, hC⟩ := g₀.domain.exists_isCompl
  obtain ⟨s, hs⟩ := Φ'.exists_rightInverse_of_surjective (range_flip_comp hB f₂ hf₂)
  let g : V →ₗ[K] V := ofIsCompl hC g₀.toFun (s ∘ₗ Φ ∘ₗ C.subtype)
  have hgdom (y : g₀.domain) : Φ' (g y) = Φ y := by
    obtain ⟨a, ha, z, hz, hy⟩ := Submodule.mem_sup.1 y.property
    rw [ofIsCompl_apply_left, LinearPMap.toFun_eq_coe, hg₀ ⟨a, ha⟩ ⟨z, hz⟩ y hy, map_add,
      hΦ, ← hy, map_add]
    simp [show Φ z = 0 from hz]
  have hgΦ (v : V) : Φ' (g v) = Φ v := by
    obtain ⟨y, hy, c, hc, rfl⟩ := Submodule.mem_sup.1 (hC.sup_eq_top ▸ Submodule.mem_top (x := v))
    rw [map_add, map_add, hgdom ⟨y, hy⟩, ofIsCompl_apply_right (v := ⟨c, hc⟩)]
    simpa using congr($hs (Φ c))
  have hinj : Injective g := (injective_iff_map_eq_zero g).2 fun v hv ↦ by
    have hvA : v ∈ ker Φ := by rw [mem_ker, ← hgΦ, hv, map_zero]
    have hvdom : v ∈ g₀.domain := Submodule.mem_sup_right hvA
    have h₁ : g v = φ ⟨v, hvA⟩ := by
      rw [show g v = g₀.toFun ⟨v, hvdom⟩ from ofIsCompl_apply_left hC ⟨v, hvdom⟩,
        LinearPMap.toFun_eq_coe, hg₀ 0 ⟨v, hvA⟩ ⟨v, hvdom⟩ (by simp)]
      simp
    rw [hv] at h₁
    simpa using congrArg Subtype.val (φ.map_eq_zero_iff.1 (Subtype.ext h₁.symm))
  refine ⟨LinearEquiv.ofInjectiveEndo g hinj, fun a ↦ ?_, fun b v ↦ ?_⟩
  · have hadom : (a : V) ∈ g₀.domain := Submodule.mem_sup_left a.property
    rw [LinearEquiv.coe_ofInjectiveEndo]
    have := ofIsCompl_apply_left hC (φ := g₀.toFun) (ψ := s ∘ₗ Φ ∘ₗ C.subtype) ⟨a, hadom⟩
    rw [this, LinearPMap.toFun_eq_coe, hg₀ a 0 ⟨a, hadom⟩ (by simp)]
    simp
  · rw [LinearEquiv.coe_ofInjectiveEndo]
    simpa [Φ, Φ'] using congr($(hgΦ v) b)

/-- **Extension of a compatible pair.** Let `B` be a nondegenerate bilinear form on a
finite-dimensional space `V`, and `f₁ : W₁ → V`, `f₂ : W₂ → V` injective linear maps from two
subspaces with `B (f₂ b) (f₁ a) = B b a`. Then there are linear automorphisms `g₁`, `g₂` of `V`
extending `f₁` and `f₂` with `B (g₂ w) (g₁ v) = B w v` for all `w`, `v`. -/
theorem exists_linearEquiv_pair_extend (hB : B.Nondegenerate) {W₁ W₂ : Submodule K V}
    (f₁ : W₁ →ₗ[K] V) (f₂ : W₂ →ₗ[K] V) (hf₁ : Injective f₁) (hf₂ : Injective f₂)
    (hf : ∀ (a : W₁) (b : W₂), B (f₂ b) (f₁ a) = B b a) :
    ∃ g₁ g₂ : V ≃ₗ[K] V, (∀ a : W₁, g₁ a = f₁ a) ∧ (∀ b : W₂, g₂ b = f₂ b) ∧
      ∀ w v, B (g₂ w) (g₁ v) = B w v := by
  obtain ⟨g₁, hg₁, hg₁B⟩ := exists_linearEquiv_flip_comp_eq hB f₁ f₂ hf₁ hf₂ hf
  -- `g₂` is the inverse of the adjoint of `g₁`: `B (g₂ w) x = B w (g₁⁻¹ x)`.
  let g₂ : V ≃ₗ[K] V := B.toDual hB ≪≫ₗ g₁.symm.dualMap ≪≫ₗ (B.toDual hB).symm
  have hg₂ (w x : V) : B (g₂ w) x = B w (g₁.symm x) := by
    rw [← toDual_def hB (m := g₂ w)]
    simp [g₂, toDual_def]
  refine ⟨g₁, g₂, hg₁, fun b ↦ sub_eq_zero.1 (hB.1 _ fun x ↦ ?_),
    fun w v ↦ by rw [hg₂, g₁.symm_apply_apply]⟩
  rw [map_sub, LinearMap.sub_apply, hg₂, ← hg₁B b (g₁.symm x), g₁.apply_symm_apply, sub_self]

end BilinForm

end LinearMap
