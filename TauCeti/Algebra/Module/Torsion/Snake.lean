/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.SnakeLemma
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.QuotSMulTop

/-!
# The kernel–cokernel exact sequence of multiplication by a scalar

Let `r` be an element of a commutative ring `R`. Multiplication by `r` is an endomorphism of every
`R`-module `M`; its kernel is the `r`-torsion `M[r] = Submodule.torsionBy R M r` and its cokernel
is `M ⧸ rM = QuotSMulTop r M`. For a short exact sequence `0 → M₁ → M₂ → M₃ → 0` of `R`-modules the
snake lemma, applied to multiplication by `r` on the three terms, gives the six-term exact sequence

`0 → M₁[r] → M₂[r] → M₃[r] → M₁ ⧸ rM₁ → M₂ ⧸ rM₂ → M₃ ⧸ rM₃ → 0`.

The functor `QuotSMulTop r` and the right-exact half of this sequence are Mathlib's
(`QuotSMulTop.map`, `QuotSMulTop.map_exact`, `QuotSMulTop.map_surjective`). This file supplies the
torsion functor `TauCeti.torsionByMap`, the left-exact half, the connecting map
`TauCeti.torsionByδ` (Mathlib's `SnakeLemma.δ'` for this diagram), exactness at its two ends, and
its naturality in morphisms of short exact sequences.

Naturality is what makes the connecting map compatible with extra structure. For `R = ℤ`, `r = ℓ`
and a group `G` acting on the sequence by additive automorphisms, each `g : G` gives a morphism of
the sequence to itself, and `TauCeti.torsionByδ_comp_torsionByMap` says that the connecting map
commutes with the actions of `g` on `M₃[ℓ]` and on `M₁ ⧸ ℓM₁`. This is the form in which the
sequence enters the comparison of `M ⧸ ℓM` with `M[ℓ]` for `G`-modules in Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, (7.3.3).

## Main definitions

* `TauCeti.torsionByMap`: the restriction `M[r] →ₗ[R] N[r]` of a linear map.
* `TauCeti.torsionByδ`: the connecting map `M₃[r] →ₗ[R] M₁ ⧸ rM₁` of a short exact sequence.

## Main results

* `TauCeti.injective_torsionByMap`, `TauCeti.exact_torsionByMap`: `M[r]` is left exact.
* `TauCeti.torsionByδ_eq`: the connecting map sends `g y` to the class of `z` when `f z = r • y`.
* `TauCeti.exact_torsionByMap_torsionByδ`, `TauCeti.exact_torsionByδ_quotSMulTop_map`: exactness
  at `M₃[r]` and at `M₁ ⧸ rM₁`.
* `TauCeti.torsionByδ_comp_torsionByMap`: naturality of the connecting map.
-/

public section

open Function Submodule

open scoped Pointwise

namespace TauCeti

section Map

variable {R : Type*} [CommSemiring R] (r : R) {M N P : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

/-- A linear map carries `r`-torsion to `r`-torsion; this is its restriction `M[r] →ₗ[R] N[r]`,
the action on morphisms of the functor `M ↦ M[r]` dual to `QuotSMulTop.map`. -/
def torsionByMap (f : M →ₗ[R] N) : torsionBy R M r →ₗ[R] torsionBy R N r :=
  f.restrict fun x hx ↦ by
    rw [mem_torsionBy_iff] at hx ⊢
    rw [← map_smul, hx, map_zero]

@[simp]
theorem coe_torsionByMap_apply (f : M →ₗ[R] N) (x : torsionBy R M r) :
    (torsionByMap r f x : N) = f x :=
  (rfl)

@[simp]
theorem torsionByMap_id : torsionByMap r (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  ext
  rfl

theorem torsionByMap_comp (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    torsionByMap r (g ∘ₗ f) = torsionByMap r g ∘ₗ torsionByMap r f := by
  ext
  rfl

/-- The inclusion of the `r`-torsion intertwines `torsionByMap` with the map itself. -/
theorem subtype_comp_torsionByMap (f : M →ₗ[R] N) :
    (torsionBy R N r).subtype ∘ₗ torsionByMap r f = f ∘ₗ (torsionBy R M r).subtype := by
  ext
  rfl

variable (M) in
/-- The `r`-torsion is the kernel of multiplication by `r`. -/
theorem exact_subtype_torsionBy :
    Exact (torsionBy R M r).subtype (DistribSMul.toLinearMap R M r) := fun x ↦
  ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩

variable {r}

/-- The restriction of an injective linear map to the `r`-torsion is injective. -/
theorem injective_torsionByMap {f : M →ₗ[R] N} (hf : Injective f) :
    Injective (torsionByMap r f) := fun _ _ h ↦
  Subtype.ext <| hf <| congrArg Subtype.val h

/-- **Left exactness of `r`-torsion**: if `f` is injective and `f`, `g` are exact, then so are
`M[r] → N[r] → P[r]`. Only the injectivity of `f` is used, not the surjectivity of `g`. -/
theorem exact_torsionByMap {f : M →ₗ[R] N} {g : N →ₗ[R] P} (hfg : Exact f g) (hf : Injective f) :
    Exact (torsionByMap r f) (torsionByMap r g) := by
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (hfg y).1 (congrArg Subtype.val hy)
    have hrx : r • x = 0 := hf <| by
      rw [map_smul, hx, map_zero]
      exact (mem_torsionBy_iff _ _).1 y.2
    exact ⟨⟨x, (mem_torsionBy_iff _ _).2 hrx⟩, Subtype.ext hx⟩
  · rintro ⟨x, rfl⟩
    exact Subtype.ext <| hfg.apply_apply_eq_zero x

end Map

section Snake

variable {R : Type*} [CommRing R] (r : R) {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]

/-- `M ⧸ rM` is the cokernel of multiplication by `r`. -/
theorem exact_toLinearMap_mkQ (M : Type*) [AddCommGroup M] [Module R M] :
    Exact (DistribSMul.toLinearMap R M r) (r • (⊤ : Submodule R M)).mkQ := by
  rw [LinearMap.exact_iff, ker_mkQ, pointwise_smul_def, Submodule.map_top]

variable {r} {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃}

variable (r) in
/-- **The connecting map** `M₃[r] → M₁ ⧸ rM₁` of a short exact sequence `0 → M₁ → M₂ → M₃ → 0`:
Mathlib's snake-lemma map `SnakeLemma.δ'` for multiplication by `r` on the three terms. It is
characterized by `TauCeti.torsionByδ_eq`: lift `x` to `y ∈ M₂`, write `r • y = f z`, and take the
class of `z`. -/
noncomputable def torsionByδ (hfg : Exact f g) (hf : Injective f) (hg : Surjective g) :
    torsionBy R M₃ r →ₗ[R] QuotSMulTop r M₁ :=
  SnakeLemma.δ' (DistribSMul.toLinearMap R M₁ r) (DistribSMul.toLinearMap R M₂ r)
    (DistribSMul.toLinearMap R M₃ r) f g hfg f g hfg (LinearMap.ext fun x ↦ map_smul f r x)
    (LinearMap.ext fun x ↦ map_smul g r x) (torsionBy R M₃ r).subtype (exact_subtype_torsionBy r M₃)
    (r • (⊤ : Submodule R M₁)).mkQ (exact_toLinearMap_mkQ r M₁) hg hf

/-- **The characterization of the connecting map**: if `g y = x` and `f z = r • y`, then the
connecting map sends `x` to the class of `z`. -/
theorem torsionByδ_eq (hfg : Exact f g) (hf : Injective f) (hg : Surjective g)
    (x : torsionBy R M₃ r) {y : M₂} (hy : g y = x) {z : M₁} (hz : f z = r • y) :
    torsionByδ r hfg hf hg x = Submodule.Quotient.mk z :=
  SnakeLemma.δ'_eq _ _ _ _ _ hfg _ _ hfg _ _ _ _ _ _ hg hf x y hy z hz

/-- **Exactness at `M₃[r]`**: the kernel of the connecting map is the image of `M₂[r]`. -/
theorem exact_torsionByMap_torsionByδ (hfg : Exact f g) (hf : Injective f)
    (hg : Surjective g) : Exact (torsionByMap r g) (torsionByδ r hfg hf hg) :=
  SnakeLemma.exact_δ'_right _ _ _ _ _ hfg _ _ hfg _ _ _ (exact_subtype_torsionBy r M₂) _ _ _ _ hg
    hf _ (subtype_comp_torsionByMap r g).symm (torsionBy R M₃ r).injective_subtype

/-- **Exactness at `M₁ ⧸ rM₁`**: the kernel of `M₁ ⧸ rM₁ → M₂ ⧸ rM₂` is the image of the
connecting map. -/
theorem exact_torsionByδ_quotSMulTop_map (hfg : Exact f g) (hf : Injective f)
    (hg : Surjective g) :
    Exact (torsionByδ r hfg hf hg) (QuotSMulTop.map r f) :=
  SnakeLemma.exact_δ'_left _ _ _ _ _ hfg _ _ hfg _ _ _ _ _ _ _ (exact_toLinearMap_mkQ r M₂) hg hf
    _ (QuotSMulTop.map_comp_mkQ r f) (r • (⊤ : Submodule R M₁)).mkQ_surjective

variable {N₁ N₂ N₃ : Type*} [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
  [AddCommGroup N₃] [Module R N₃] {f' : N₁ →ₗ[R] N₂} {g' : N₂ →ₗ[R] N₃}

/-- **Naturality of the connecting map**: a morphism `(α, β, γ)` of short exact sequences
intertwines the two connecting maps, `δ' ∘ γ[r] = (α mod r) ∘ δ`. -/
theorem torsionByδ_comp_torsionByMap (hfg : Exact f g) (hf : Injective f) (hg : Surjective g)
    (hfg' : Exact f' g') (hf' : Injective f') (hg' : Surjective g') {α : M₁ →ₗ[R] N₁}
    {β : M₂ →ₗ[R] N₂} {γ : M₃ →ₗ[R] N₃} (hαβ : β ∘ₗ f = f' ∘ₗ α) (hβγ : γ ∘ₗ g = g' ∘ₗ β) :
    torsionByδ r hfg' hf' hg' ∘ₗ torsionByMap r γ =
      QuotSMulTop.map r α ∘ₗ torsionByδ r hfg hf hg := by
  ext x
  -- lift `x` to `y ∈ M₂`; then `g (r • y) = r • x = 0`, so `r • y = f z` for some `z ∈ M₁`
  obtain ⟨y, hy⟩ := hg x
  obtain ⟨z, hz⟩ := (hfg (r • y)).1 <| by
    rw [map_smul, hy]
    exact (mem_torsionBy_iff _ _).1 x.2
  have hy' : g' (β y) = torsionByMap r γ x := by
    simpa [hy] using (LinearMap.congr_fun hβγ y).symm
  have hz' : f' (α z) = r • β y := by
    simpa [hz] using (LinearMap.congr_fun hαβ z).symm
  rw [LinearMap.comp_apply, LinearMap.comp_apply, torsionByδ_eq hfg' hf' hg' _ hy' hz',
    torsionByδ_eq hfg hf hg x hy hz, QuotSMulTop.map_apply_mk]

end Snake

end TauCeti
