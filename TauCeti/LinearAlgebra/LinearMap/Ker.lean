/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Ker

/-!
# Kernels in commuting squares

Two commuting squares of linear maps whose horizontal sides are linear isomorphisms and which
share a vertical side paste to a commuting square. In a commuting square `f' ∘ d = e ∘ f` with
semilinear horizontal maps, `f` sends the kernel of `d` into the kernel of `e`; with `f' = f`,
this is how a chain map acts on cycles. If moreover `e ∘ e' = 0` and `f'` is injective, then
`e' c = f a` forces `d a = 0`. In a commuting square `g ∘ e₁ = e₂ ∘ f` whose source side `e₁`
is surjective and whose target side `e₂` is injective, `e₁` carries the kernel of `f` onto the
kernel of `g`. The restriction of an injective linear map to submodules is injective. The kernels
of finitely many nonzero linear maps are finitely many proper submodules covering every point at
which one of the maps vanishes.
-/

public section

namespace LinearMap

variable {R : Type*} [Semiring R] {M N M' N' : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']

/-- Pasting the commuting squares `g ∘ e₁ = e₂ ∘ f` and `k ∘ e₁' = e₂' ∘ g` gives the commuting
square `k ∘ (e₁' ∘ e₁) = (e₂' ∘ e₂) ∘ f`. -/
theorem comp_trans_eq_of_comp_eq {M'' N'' : Type*} [AddCommMonoid M''] [Module R M'']
    [AddCommMonoid N''] [Module R N''] {f : M →ₗ[R] N} {g : M' →ₗ[R] N'} {k : M'' →ₗ[R] N''}
    {e₁ : M ≃ₗ[R] M'} {e₂ : N ≃ₗ[R] N'} {e₁' : M' ≃ₗ[R] M''} {e₂' : N' ≃ₗ[R] N''}
    (h : g ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f)
    (h' : k ∘ₗ e₁'.toLinearMap = e₂'.toLinearMap ∘ₗ g) :
    k ∘ₗ (e₁.trans e₁').toLinearMap = (e₂.trans e₂').toLinearMap ∘ₗ f := by
  rw [LinearEquiv.coe_trans, LinearEquiv.coe_trans, ← comp_assoc, h', comp_assoc, h, comp_assoc]

/-- In a commuting square `f' ∘ d = e ∘ f` with semilinear horizontal maps, `f` sends
the kernel of the linear map `d` into the kernel of the linear map `e`. -/
theorem map_mem_ker_of_comp_eq {S : Type*} [Semiring S] {P Q : Type*}
    [AddCommMonoid P] [Module S P] [AddCommMonoid Q] [Module S Q] {σ : R →+* S}
    {d : M →ₗ[R] M'} {e : P →ₗ[S] Q} (f : M →ₛₗ[σ] P)
    {f' : M' →ₛₗ[σ] Q} (hf : f' ∘ₛₗ d = e ∘ₛₗ f) {x : M}
    (hx : x ∈ ker d) : f x ∈ ker e := by
  rw [mem_ker, ← comp_apply e f, ← hf, comp_apply, mem_ker.mp hx, map_zero]

/-- In a commuting square `f' ∘ d = e ∘ f` with `e ∘ e' = 0` and `f'` injective, if `e' c = f a`
then `d a = 0`. For a chain map `f' = f`, an element mapped to a boundary is a cycle. -/
theorem apply_eq_zero_of_apply_eq {N'' : Type*} [AddCommMonoid N''] [Module R N'']
    {d : M →ₗ[R] M'} {e : N →ₗ[R] N'} {e' : N'' →ₗ[R] N} {f : M →ₗ[R] N}
    {f' : M' →ₗ[R] N'} (he : e ∘ₗ e' = 0) (hf : f' ∘ₗ d = e ∘ₗ f)
    (hinj : Function.Injective f') {c : N''} {a : M} (hc : e' c = f a) : d a = 0 := by
  apply hinj
  rw [map_zero, ← comp_apply, hf, comp_apply, ← hc, ← comp_apply, he, LinearMap.zero_apply]

/-- In a commuting square `g ∘ e₁ = e₂ ∘ f` of linear maps with `e₁` surjective and `e₂`
injective, `e₁` carries the kernel of `f` onto that of `g`. -/
theorem map_ker_eq_ker_of_comp_eq (f : M →ₗ[R] N) {g : M' →ₗ[R] N'} {e₁ : M →ₗ[R] M'}
    {e₂ : N →ₗ[R] N'} (he₁ : Function.Surjective e₁) (he₂ : Function.Injective e₂)
    (h : g ∘ₗ e₁ = e₂ ∘ₗ f) :
    (ker f).map e₁ = ker g := by
  rw [← ker_comp_of_ker_eq_bot f (ker_eq_bot_of_injective he₂), ← h, ker_comp,
    Submodule.map_comap_eq_of_surjective he₁]

/-- The restriction of an injective linear map to submodules is injective. -/
theorem injective_restrict {f : M →ₗ[R] N} {p : Submodule R M} {q : Submodule R N}
    (hf : Function.Injective f) (h : ∀ x ∈ p, f x ∈ q) : Function.Injective (f.restrict h) :=
  fun _ _ hxy ↦ Subtype.ext (hf (congrArg Subtype.val hxy))

/-- The kernels of finitely many nonzero linear maps are finitely many proper submodules covering
every point at which one of the maps vanishes. -/
theorem exists_finset_ne_top_forall_exists_mem_of_apply_eq_zero {P : Type*} (s : Finset P)
    (f : P → M →ₗ[R] N) (hf : ∀ p ∈ s, f p ≠ 0) :
    ∃ U : Finset (Submodule R M), (∀ W ∈ U, W ≠ ⊤) ∧
      ∀ x : M, ∀ p ∈ s, f p x = 0 → ∃ W ∈ U, x ∈ W := by
  classical
  exact ⟨s.image fun p ↦ ker (f p), Finset.forall_mem_image.mpr fun p hp ↦
    ker_eq_top.not.mpr (hf p hp), fun x p hp hx ↦ ⟨_, Finset.mem_image_of_mem _ hp, mem_ker.mpr hx⟩⟩

end LinearMap
