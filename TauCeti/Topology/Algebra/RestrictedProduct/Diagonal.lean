/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.RestrictedProduct.Congr.Right

/-!
# Diagonal homomorphisms into restricted products

A family of homomorphisms `φ i : Γ →* G i` whose values at each `γ` lie in the reference
subgroup `U i` for all but finitely many `i` assembles into a homomorphism from `Γ` into the
restricted product `Πʳ i, [G i, U i]`, the *diagonal*. The eventual-integrality evidence is an
argument of the construction: for the classical example `Γ = G(K)` and `G i = G(K_v)` it is an
arithmetic theorem about `Γ`, and nothing here manufactures it.

This file records the diagonal, its coordinate formula, its kernel and the resulting injectivity
criterion, its compatibility with componentwise maps and with a change of factors, and the
continuity criterion. Continuity does not follow from continuity of the coordinate maps, because
the restricted-product topology is finer than the topology induced from `Π i, G i`. The criterion
asks for one cofinite set `S` of indices at which every `γ` is integral. Such a uniform set is
what the restricted-product topology rewards: on the subset `{x | ∀ i ∈ S, x i ∈ U i}`, which
then contains the image of the diagonal, it coincides with the topology induced from
`Π i, G i`, so continuity there is decided by the coordinates.

## References

* A. Weil, *Basic Number Theory*.
-/

public section

namespace TauCeti

open Filter
open scoped RestrictedProduct

universe u v w z

variable {ι : Type u} {G : ι → Type v}
variable [∀ i, Group (G i)]

/-- The diagonal homomorphism into a restricted product induced by a family of homomorphisms
whose values are eventually in the reference subgroups. The eventual-integrality evidence `h` is
an argument, not a consequence of the construction. -/
def rationalDiagonal {Γ : Type w} [MulOneClass Γ] (φ : ∀ i, Γ →* G i)
    (U : ∀ i, Subgroup (G i))
    (h : ∀ γ : Γ, ∀ᶠ i in cofinite, φ i γ ∈ U i) :
    Γ →* Πʳ i, [G i, (U i : Set (G i))] where
  toFun γ := ⟨fun i ↦ φ i γ, h γ⟩
  map_one' := by
    ext i
    exact map_one (φ i)
  map_mul' a b := by
    ext i
    exact map_mul (φ i) a b

/-- The `i`-th coordinate of the diagonal at `γ` is `φ i γ`. -/
@[simp]
theorem rationalDiagonal_apply {Γ : Type w} [MulOneClass Γ] (φ : ∀ i, Γ →* G i)
    (U : ∀ i, Subgroup (G i))
    (h : ∀ γ : Γ, ∀ᶠ i in cofinite, φ i γ ∈ U i) (γ : Γ) (i : ι) :
    rationalDiagonal φ U h γ i = φ i γ := by
  rfl

/-- The kernel of the diagonal is the intersection of the kernels of the coordinate maps. -/
@[simp]
theorem ker_rationalDiagonal {Γ : Type w} [Group Γ] (φ : ∀ i, Γ →* G i)
    (U : ∀ i, Subgroup (G i))
    (h : ∀ γ : Γ, ∀ᶠ i in cofinite, φ i γ ∈ U i) :
    (rationalDiagonal φ U h).ker = ⨅ i, (φ i).ker := by
  ext γ
  simp only [MonoidHom.mem_ker, Subgroup.mem_iInf, RestrictedProduct.ext_iff,
    rationalDiagonal_apply, RestrictedProduct.one_apply]

/-- The diagonal is injective exactly when the coordinate maps jointly separate points. -/
theorem injective_rationalDiagonal_iff {Γ : Type w} [Group Γ] (φ : ∀ i, Γ →* G i)
    (U : ∀ i, Subgroup (G i))
    (h : ∀ γ : Γ, ∀ᶠ i in cofinite, φ i γ ∈ U i) :
    Function.Injective (rationalDiagonal φ U h) ↔ ⨅ i, (φ i).ker = ⊥ := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_rationalDiagonal]

/-- The diagonal is injective as soon as one coordinate map is. -/
theorem injective_rationalDiagonal {Γ : Type w} [MulOneClass Γ] (φ : ∀ i, Γ →* G i)
    (U : ∀ i, Subgroup (G i))
    (h : ∀ γ : Γ, ∀ᶠ i in cofinite, φ i γ ∈ U i)
    (hsep : ∃ i, Function.Injective (φ i)) :
    Function.Injective (rationalDiagonal φ U h) := by
  obtain ⟨i, hi⟩ := hsep
  intro a b hab
  exact hi (by simpa using congrArg (fun x ↦ x i) hab)

/-- A componentwise map applied after the diagonal is the diagonal of the composed coordinate
maps, whose eventual integrality follows from that of the original coordinates together with the
hypothesis `hψ` that `ψ i` eventually maps `U i` into `V i`. -/
theorem restrictedProductMap_comp_rationalDiagonal {Γ : Type w} [MulOneClass Γ]
    {H : ι → Type z} [∀ i, Group (H i)]
    (φ : ∀ i, Γ →* G i) (ψ : ∀ i, G i →* H i)
    (U : ∀ i, Subgroup (G i)) (V : ∀ i, Subgroup (H i))
    (hU : ∀ γ : Γ, ∀ᶠ i in cofinite, φ i γ ∈ U i)
    (hψ : ∀ᶠ i in cofinite, Set.MapsTo (ψ i) (U i) (V i)) :
    (restrictedProductMap U V ψ hψ).comp (rationalDiagonal φ U hU) =
      rationalDiagonal (fun i ↦ (ψ i).comp (φ i)) V
        (fun γ ↦ by filter_upwards [hU γ, hψ] with i hi hψi using hψi hi) := by
  ext γ i
  simp

/-- A change of factors applied after the diagonal is the diagonal of the transported coordinate
maps, whose eventual integrality follows from that of the original coordinates together with the
hypothesis `hψ` that `ψ i` eventually maps `U i` bijectively onto `V i`. The change of reference
family is the case in which every `ψ i` is the identity. -/
theorem restrictedProductCongrRight_comp_rationalDiagonal {Γ : Type w} [MulOneClass Γ]
    {H : ι → Type z} [∀ i, Group (H i)]
    (φ : ∀ i, Γ →* G i) (ψ : ∀ i, G i ≃* H i)
    (U : ∀ i, Subgroup (G i)) (V : ∀ i, Subgroup (H i))
    (hU : ∀ γ : Γ, ∀ᶠ i in cofinite, φ i γ ∈ U i)
    (hψ : ∀ᶠ i in cofinite, Set.BijOn (ψ i) (U i) (V i)) :
    (restrictedProductCongrRight U V ψ hψ).toMonoidHom.comp (rationalDiagonal φ U hU) =
      rationalDiagonal (fun i ↦ (ψ i).toMonoidHom.comp (φ i)) V
        (fun γ ↦ by filter_upwards [hU γ, hψ] with i hi hψi using hψi.mapsTo hi) := by
  ext γ i
  simp

/-- The diagonal is continuous when the coordinate maps are continuous and there is one cofinite
set of indices at which every `γ` is integral. Pointwise eventual integrality alone builds the
map but is not enough for continuity, because the restricted-product topology is finer than the
topology induced from the full product. -/
theorem continuous_rationalDiagonal {Γ : Type w} [MulOneClass Γ] [TopologicalSpace Γ]
    [∀ i, TopologicalSpace (G i)]
    (φ : ∀ i, Γ →* G i) (U : ∀ i, Subgroup (G i))
    (h : ∀ γ : Γ, ∀ᶠ i in cofinite, φ i γ ∈ U i)
    (hcont : ∀ i, Continuous (φ i))
    (S : Set ι) (hS : S ∈ cofinite) (huniform : ∀ γ : Γ, ∀ i ∈ S, φ i γ ∈ U i) :
    Continuous (rationalDiagonal φ U h) := by
  have hS' : (cofinite : Filter ι) ≤ 𝓟 S := le_principal_iff.mpr hS
  -- The diagonal factors through the principal stage at `S`, into which it lands by `huniform`;
  -- Mathlib's `RestrictedProduct.continuous_rng_of_principal` reduces continuity there to the
  -- coordinates.
  have hf : Continuous fun γ : Γ ↦
      (RestrictedProduct.mk (fun i ↦ φ i γ) (eventually_principal.mpr (huniform γ)) :
        Πʳ i, [G i, (U i : Set (G i))]_[𝓟 S]) :=
    RestrictedProduct.continuous_rng_of_principal.mpr (continuous_pi fun i ↦ hcont i)
  have hfactor : ⇑(rationalDiagonal φ U h) =
      RestrictedProduct.inclusion (fun i ↦ G i) (fun i ↦ (U i : Set (G i))) hS' ∘
        fun γ ↦ RestrictedProduct.mk (fun i ↦ φ i γ) (eventually_principal.mpr (huniform γ)) := by
    funext γ
    ext i
    rw [rationalDiagonal_apply, Function.comp_apply, RestrictedProduct.inclusion_apply,
      RestrictedProduct.mk_apply]
  rw [hfactor]
  exact (RestrictedProduct.continuous_inclusion hS').comp hf

end TauCeti
