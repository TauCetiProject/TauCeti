/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Decomposition
public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.LayerTateModule.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-!
# The integral decomposition of a Tate module of a local field layer

For a finite Galois layer, a Tate module is an extension of the augmentation ideal by the
completed multiplicative group, with projective dimension at most one. This file applies the
integral decomposition theorem to that bundled data, giving the module decomposition that yields
the generator bound in the proof of the full local absolute Galois group rank.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., proof of
  (7.4.1).
-/

public section

namespace TauCeti.LayerTateModule

open _root_.MonoidAlgebra

universe u

variable {p : ℕ} [Fact p.Prime] {L K : Type u} [Field L] [Field K] [Algebra K L]

local notation "Λ" => MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)

/-- **The integral decomposition of a Tate module.** For a finite Galois extension of `p`-adic
fields `L/K`, a Tate module of the layer is isomorphic to the tame-frame module of any generating
pair with sharp exponents, together with `N = [K : ℚ_p]` copies of the group algebra. -/
theorem nonempty_linearEquiv_tameFrameModule_prod
    [Algebra ℚ_[p] L] [Module.Finite ℚ_[p] L] [Algebra ℚ_[p] K]
    [IsScalarTower ℚ_[p] K L] [IsGalois K L]
    (Y : LayerTateModule p L K) (h : Finite (pPowerRootsOfUnity p L))
    (σ τ : L ≃ₐ[K] L) (hgen : Subgroup.closure {σ, τ} = ⊤) (a b : ℕ)
    (ha : ∀ ζ ∈ pPowerRootsOfUnity p L, Units.map (σ : L →* L) ζ = ζ ^ a)
    (hb : ∀ ζ ∈ pPowerRootsOfUnity p L, Units.map (τ : L →* L) ζ = ζ ^ b)
    (hcard : Nat.card (Λ ⧸ Ideal.span {single σ (1 : ℤ_[p]) - a,
      single τ (1 : ℤ_[p]) - b}) = localRootOfUnityOrder p L h) :
    Nonempty (Y.carrier ≃ₗ[Λ]
      (TameFrameModule ℤ_[p] (L ≃ₐ[K] L) σ τ (a : ℤ_[p]) (b : ℤ_[p]) ×
        (Fin (Module.finrank ℚ_[p] K) → Λ))) := by
  have := Module.Finite.right ℚ_[p] K L
  obtain ⟨n, f, hf, hker⟩ := Y.projdim
  let P₀ := Fin n → Λ
  let P₁ := LinearMap.ker f
  let d : P₁ →ₗ[Λ] P₀ := (LinearMap.ker f).subtype
  let ρ : P₀ →ₗ[Λ] Y.carrier := f
  have hdρ : Function.Exact d ρ := LinearMap.exact_subtype_ker_map f
  have hd : Function.Injective d := (LinearMap.ker f).subtype_injective
  have hρ : Function.Surjective ρ := hf
  let : IsNoetherianRing Λ := IsNoetherianRing.of_finite ℤ_[p] Λ
  let : Module.Projective Λ P₁ := hker
  exact TauCeti.nonempty_linearEquiv_tameFrameModule_prod
    hdρ hd hρ Y.exact_ι_π Y.ι_injective Y.π_surjective h σ τ hgen a b ha hb hcard

end TauCeti.LayerTateModule
