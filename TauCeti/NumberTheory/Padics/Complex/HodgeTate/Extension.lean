/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Complex.HodgeTate.Jump

import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Hodge–Tate jumps of extensions with trivial quotient action

Let `j : Γ →* Gal(PadicAlgCl p / ℚ_p)` have image a neighbourhood of `1`, and let `i : T →ₗ[R] E`
be a map between representations `ρ` and `σ` such that `σ g y - y ∈ LinearMap.range i` for `g`
near `1` (the quotient `E / i(T)` carries the trivial action near `1`). For any nonzero weight
`u ≠ 0`, any `f ∈ hodgeTateMaps j σ γ u` vanishing on `i(T)` satisfies `f (σ g y) = f y` near `1`,
and hence `f = 0` by Tate's vanishing theorem
(`PadicComplex.hodgeTateMaps_comp_injective_of_sub_mem`).

When `hodgeTateMaps j ρ γ u` is finite-dimensional over `PadicAlgCl p`, this yields the jump bound
`hodgeTateJump j σ γ u ≤ hodgeTateJump j ρ γ u` (`PadicComplex.hodgeTateJump_le_of_sub_mem`), and
in particular the corresponding bound for the cocycle extension `T × C` given by
`(y, c) ↦ (ρ g y + a c g, c)` (`PadicComplex.hodgeTateJump_cocycleExtensionRep_le`).

## Main definitions and results

* `PadicComplex.hodgeTateMaps_comp_injective_of_sub_mem`: restriction along `i` is injective on
  Hodge–Tate maps of nonzero weight when `σ g y - y ∈ range i` near `1`.
* `PadicComplex.hodgeTateJump_le_of_sub_mem`: `hodgeTateJump j σ γ u ≤ hodgeTateJump j ρ γ u` for
  `u ≠ 0`.
* `PadicComplex.cocycleExtensionRep`: the extension representation on `T × C` attached to an
  `R`-linear family of `1`-cocycles.
* `PadicComplex.hodgeTateJump_cocycleExtensionRep_le`: nonzero Hodge–Tate jumps of a cocycle
  extension are bounded by those of `ρ`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), `src/Lib/PadicHodge/BlochKato.lean`
(`New.Period.extensionRep`, `New.Period.jump_extensionRep_le`).
-/

public section

open Topology Filter Module

namespace PadicComplex

variable {p : ℕ} [Fact p.Prime] {Γ R T E : Type*} [Monoid Γ] [CommRing R] [AddCommGroup T]
  [Module R T] [AddCommGroup E] [Module R E] {j : Γ →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)}
  {ρ : Representation R Γ T} {σ : Representation R Γ E} {γ : R →+* ℂ_[p]}

/-- If `σ g y - y ∈ range i` near `1` and `u ≠ 0`, then a Hodge–Tate map of weight `u` on `E`
that vanishes on `i(T)` is identically zero. -/
theorem hodgeTateMaps_comp_injective_of_sub_mem (hj : Set.range j ∈ 𝓝 1) (i : T →ₗ[R] E)
    (hsub : ∀ y : E, ∀ᶠ g in comap j (𝓝 1), σ g y - y ∈ LinearMap.range i) {u : ℤ} (hu : u ≠ 0)
    {f : E →ₛₗ[γ] ℂ_[p]} (hf : f ∈ hodgeTateMaps j σ γ u) (hfi : f.comp i = 0) : f = 0 := by
  ext y
  have htwist : ∀ᶠ g in comap j (𝓝 1),
      twist (-u) (j g).toRingEquiv * j g • f y = twist 0 (j g).toRingEquiv * f y := by
    filter_upwards [mem_hodgeTateMaps.mp hf y, hsub y] with g hfg ⟨t, ht⟩
    have hfix : f (σ g y) = f y := by
      rw [← sub_eq_zero, ← map_sub, ← ht]
      exact LinearMap.congr_fun hfi t
    rw [twist_zero, one_mul, ← hfg, hfix]
  have htwist' : ∀ᶠ τ in 𝓝 (1 : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
      twist (-u) τ.toRingEquiv * τ • f y = twist 0 τ.toRingEquiv * f y := by
    rw [← map_comap_of_mem hj]
    exact htwist
  exact eq_zero_of_eventually_twist_mul_smul_eq (neg_ne_zero.mpr hu) htwist'

/-- If `i : T →ₗ[R] E` is equivariant near `1` with `σ g y - y ∈ range i` near `1`, then for every
nonzero weight `u ≠ 0`, `hodgeTateJump j σ γ u ≤ hodgeTateJump j ρ γ u`. -/
theorem hodgeTateJump_le_of_sub_mem (hj : Set.range j ∈ 𝓝 1) (i : T →ₗ[R] E)
    (hequiv : ∀ x : T, ∀ᶠ g in comap j (𝓝 1), σ g (i x) = i (ρ g x))
    (hsub : ∀ y : E, ∀ᶠ g in comap j (𝓝 1), σ g y - y ∈ LinearMap.range i) {u : ℤ} (hu : u ≠ 0)
    [Module.Finite (PadicAlgCl p) (hodgeTateMaps j ρ γ u)] :
    hodgeTateJump j σ γ u ≤ hodgeTateJump j ρ γ u := by
  let res : hodgeTateMaps j σ γ u →ₗ[PadicAlgCl p] hodgeTateMaps j ρ γ u :=
    { toFun := fun f ↦ ⟨f.val.comp i, mem_hodgeTateMaps.mpr fun x ↦ by
        filter_upwards [hequiv x, mem_hodgeTateMaps.mp f.property (i x)] with g hgx hfg
        simpa [LinearMap.comp_apply, hgx] using hfg⟩
      map_add' := fun f₁ f₂ ↦ by ext x; simp
      map_smul' := fun c f ↦ by ext x; simp }
  rw [hodgeTateJump_def, hodgeTateJump_def]
  refine LinearMap.finrank_le_finrank_of_injective (f := res) fun f g hfg ↦ ?_
  rw [← sub_eq_zero]
  refine Subtype.ext (hodgeTateMaps_comp_injective_of_sub_mem hj i hsub hu (f - g).property ?_)
  simpa [res, LinearMap.sub_comp, sub_eq_zero] using congrArg Subtype.val hfg

/-- The extension representation on `T × C` defined by `g • (y, c) = (ρ g y + a c g, c)` for an
`R`-linear family of `1`-cocycles `a : C →ₗ[R] (Γ → T)`. -/
def cocycleExtensionRep {C : Type*} [AddCommGroup C] [Module R C] (ρ : Representation R Γ T)
    (a : C →ₗ[R] (Γ → T)) (hone : ∀ c, a c 1 = 0)
    (hmul : ∀ c g h, a c (g * h) = ρ g (a c h) + a c g) : Representation R Γ (T × C) where
  toFun g :=
    { toFun := fun p ↦ (ρ g p.fst + a p.snd g, p.snd)
      map_add' := fun p q ↦ by ext <;> simp [add_add_add_comm]
      map_smul' := fun r p ↦ by ext <;> simp [smul_add] }
  map_one' := by ext p <;> simp [hone]
  map_mul' g h := by ext p <;> simp [hmul]

/-- For every nonzero weight `u ≠ 0`, the Hodge–Tate jump of a cocycle extension `T × C` is at most
that of `T`. -/
theorem hodgeTateJump_cocycleExtensionRep_le {C : Type*} [AddCommGroup C] [Module R C]
    (hj : Set.range j ∈ 𝓝 1) (a : C →ₗ[R] (Γ → T)) (hone : ∀ c, a c 1 = 0)
    (hmul : ∀ c g h, a c (g * h) = ρ g (a c h) + a c g) {u : ℤ} (hu : u ≠ 0)
    [Module.Finite (PadicAlgCl p) (hodgeTateMaps j ρ γ u)] :
    hodgeTateJump j (cocycleExtensionRep ρ a hone hmul) γ u ≤ hodgeTateJump j ρ γ u :=
  hodgeTateJump_le_of_sub_mem hj (LinearMap.inl R T C)
    (fun x ↦ Filter.Eventually.of_forall fun g ↦ by simp [cocycleExtensionRep])
    (fun ⟨y, c⟩ ↦ Filter.Eventually.of_forall fun g ↦
      ⟨ρ g y + a c g - y, by ext <;> simp [cocycleExtensionRep]⟩)
    hu

end PadicComplex
