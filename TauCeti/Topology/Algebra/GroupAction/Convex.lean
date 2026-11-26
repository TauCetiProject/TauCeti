/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Topology.Algebra.MulAction

/-!
# Fixed-point transport from invariant convex subsets to ambient affine actions

Fixed-point theorems for continuous affine actions on convex sets (such as Markov–Kakutani,
Ryll-Nardzewski, and Day–Rickert) are often most naturally proved first for an intrinsic
`MulAction M K` on a convex subset `K ⊆ E` with `[ContinuousSMul M K]` preserving binary convex
combinations in `E`, whereas callers typically hold an ambient action `M →* Function.End E` or a
homomorphism `M →* (E →ᵃ[𝕜] E)` leaving `K` invariant and acting jointly continuously on `M × K`.

This module packages the subtype action construction so fixed-point existence transports directly
from intrinsic subtype actions on `K` to ambient endomorphism and affine-map actions leaving `K`
invariant.

## Main results

* `Convex.exists_fixedPoint_of_subtype`: deduce a fixed point in `K` for `ρ : M →* Function.End E`
  preserving `K` and binary convex combinations on `K` from a subtype fixed-point principle on `K`.
* `Convex.exists_fixedPoint_affineMap_of_subtype`: specialize to an affine action
  `π : M →* (E →ᵃ[𝕜] E)` leaving `K` invariant.
-/

public section

open Set

namespace Convex

universe u v w

/-- Equip an invariant convex subset `K ⊆ E` with the `MulAction M K` and `ContinuousSMul M K`
induced by `ρ : M →* Function.End E`, and deduce a `ρ`-fixed point in `K` from a subtype
fixed-point principle on `K`. -/
theorem exists_fixedPoint_of_subtype {𝕜 : Type w} [Semiring 𝕜] [PartialOrder 𝕜]
    {M : Type u} [Monoid M] [TopologicalSpace M]
    {E : Type v} [AddCommMonoid E] [SMul 𝕜 E] [TopologicalSpace E] {K : Set E} (hKc : Convex 𝕜 K)
    (ρ : M →* Function.End E) (hmaps : ∀ g : M, MapsTo (ρ g) K K)
    (hcont : Continuous fun p : M × K => ρ p.fst (p.snd : E))
    (hcomb : ∀ (g : M) {y : E}, y ∈ K → ∀ {z : E}, z ∈ K → ∀ {a b : 𝕜},
      0 ≤ a → 0 ≤ b → a + b = 1 → ρ g (a • y + b • z) = a • ρ g y + b • ρ g z)
    (hfp : ∀ [MulAction M K] [ContinuousSMul M K],
      (∀ (g : M) (y z : K) (a b : 𝕜) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
        ((g • (⟨a • (y : E) + b • (z : E), hKc y.property z.property ha hb hab⟩ : K) : K) : E) =
          a • ((g • y : K) : E) + b • ((g • z : K) : E)) →
      ∃ x : K, ∀ g : M, g • x = x) :
    ∃ x ∈ K, ∀ g : M, ρ g x = x := by
  let _ : SMul M K := ⟨fun g x => ⟨ρ g x, hmaps g x.property⟩⟩
  have hcoe (g : M) (x : K) : ((g • x : K) : E) = ρ g x := rfl
  let _ : MulAction M K :=
    { one_smul x := Subtype.ext (congrFun (map_one ρ) x)
      mul_smul g h x := Subtype.ext (congrFun (map_mul ρ g h) x) }
  have : ContinuousSMul M K := ⟨hcont.subtype_mk fun p => hmaps p.fst p.snd.property⟩
  obtain ⟨x, hx⟩ := hfp fun g y z a b ha hb hab => by
    rw [hcoe, hcoe, hcoe]
    exact hcomb g y.property z.property ha hb hab
  exact ⟨x, x.property, fun g => congrArg Subtype.val (hx g)⟩

/-- Deduce a fixed point of `π : M →* (E →ᵃ[𝕜] E)` on an invariant convex subset `K ⊆ E` from a
subtype fixed-point principle on `K`. -/
theorem exists_fixedPoint_affineMap_of_subtype {𝕜 : Type w} [Ring 𝕜] [PartialOrder 𝕜]
    {M : Type u} [Monoid M] [TopologicalSpace M]
    {E : Type v} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] {K : Set E} (hKc : Convex 𝕜 K)
    (π : M →* (E →ᵃ[𝕜] E)) (hmaps : ∀ g : M, MapsTo (π g) K K)
    (hcont : Continuous fun p : M × K => π p.fst (p.snd : E))
    (hfp : ∀ [MulAction M K] [ContinuousSMul M K],
      (∀ (g : M) (y z : K) (a b : 𝕜) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
        ((g • (⟨a • (y : E) + b • (z : E), hKc y.property z.property ha hb hab⟩ : K) : K) : E) =
          a • ((g • y : K) : E) + b • ((g • z : K) : E)) →
      ∃ x : K, ∀ g : M, g • x = x) :
    ∃ x ∈ K, ∀ g : M, π g x = x :=
  hKc.exists_fixedPoint_of_subtype
    { toFun := fun g => (π g : E → E)
      map_one' := funext fun x => DFunLike.congr_fun (map_one π) x
      map_mul' := fun g h => funext fun x => DFunLike.congr_fun (map_mul π g h) x }
    hmaps hcont (fun _ _ _ _ _ _ _ _ _ hab => Convex.combo_affine_apply hab) hfp

end Convex
