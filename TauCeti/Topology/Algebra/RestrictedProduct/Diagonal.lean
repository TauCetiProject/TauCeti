/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.RestrictedProduct.Congr.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Diagonal homomorphisms into restricted products

A family of homomorphisms `φ i : Γ →* G i` whose values at each `γ` lie in the reference
subgroup `U i` for all but finitely many `i` assembles into a homomorphism from `Γ` into the
restricted product `Πʳ i, [G i, U i]`, the *diagonal*. The eventual-integrality evidence is an
argument of the construction: for the classical example `Γ = G(K)` and `G i = G(K_v)` it is an
arithmetic theorem about `Γ`, and nothing here manufactures it.

This file records the diagonal, its coordinate formula, its kernel and the resulting injectivity
criterion, its compatibility with componentwise maps, with a change of factors and with a
change of reference family, and the continuity criterion. Continuity does not follow from
continuity of the coordinate maps, because the restricted-product topology is finer than the
topology induced from `Π i, G i`. The criterion asks for one cofinite set `S` of indices at which
every `γ` is integral. Such a uniform set is what the restricted-product topology rewards: on the
subset `{x | ∀ i ∈ S, x i ∈ U i}`, which then contains the image of the diagonal, it coincides
with the topology induced from `Π i, G i`, so continuity there is decided by the coordinates.

The uniform integrality set cannot be dispensed with. For discrete groups with trivial reference
subgroups, infinitely many of them nontrivial, take for `Γ` the finitely supported elements of the
full product, topologised as a subspace of it. Its coordinate maps are continuous and each of its
elements is eventually integral, yet the diagonal into the restricted product, which is discrete,
is not continuous (`continuous_eval_and_not_continuous_rationalDiagonal_range_coeMonoidHom`).

The general statements have additive counterparts: `addRationalDiagonal` is the diagonal of a
family of additive homomorphisms `Γ →+ G i`, with coordinate formula `addRationalDiagonal_apply`.

## References

* A. Weil, *Basic Number Theory*.
-/

public section

namespace TauCeti

open Filter Topology
open scoped RestrictedProduct

universe u v w z

variable {ι : Type u} {G : ι → Type v}
variable [∀ i, Group (G i)]

/-- The diagonal homomorphism into a restricted product induced by a family of homomorphisms
whose values are eventually in the reference subgroups. The eventual-integrality evidence `h` is
an argument, not a consequence of the construction. -/
@[to_additive addRationalDiagonal /-- The diagonal additive homomorphism into a restricted product
induced by a family of additive homomorphisms whose values are eventually in the reference
subgroups. The eventual-integrality evidence `h` is an argument, not a consequence of the
construction. -/]
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
@[to_additive (attr := simp) addRationalDiagonal_apply]
theorem rationalDiagonal_apply {Γ : Type w} [MulOneClass Γ] (φ : ∀ i, Γ →* G i)
    (U : ∀ i, Subgroup (G i))
    (h : ∀ γ : Γ, ∀ᶠ i in cofinite, φ i γ ∈ U i) (γ : Γ) (i : ι) :
    rationalDiagonal φ U h γ i = φ i γ := by
  rfl

/-- The kernel of the diagonal is the intersection of the kernels of the coordinate maps. -/
@[to_additive (attr := simp) ker_addRationalDiagonal]
theorem ker_rationalDiagonal {Γ : Type w} [Group Γ] (φ : ∀ i, Γ →* G i)
    (U : ∀ i, Subgroup (G i))
    (h : ∀ γ : Γ, ∀ᶠ i in cofinite, φ i γ ∈ U i) :
    (rationalDiagonal φ U h).ker = ⨅ i, (φ i).ker := by
  ext γ
  simp only [MonoidHom.mem_ker, Subgroup.mem_iInf, RestrictedProduct.ext_iff,
    rationalDiagonal_apply, RestrictedProduct.one_apply]

/-- The diagonal is injective exactly when the coordinate maps jointly separate points. -/
@[to_additive injective_addRationalDiagonal_iff]
theorem injective_rationalDiagonal_iff {Γ : Type w} [Group Γ] (φ : ∀ i, Γ →* G i)
    (U : ∀ i, Subgroup (G i))
    (h : ∀ γ : Γ, ∀ᶠ i in cofinite, φ i γ ∈ U i) :
    Function.Injective (rationalDiagonal φ U h) ↔ ⨅ i, (φ i).ker = ⊥ := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_rationalDiagonal]

/-- The diagonal is injective as soon as one coordinate map is. -/
@[to_additive injective_addRationalDiagonal]
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
@[to_additive addRestrictedProductMap_comp_addRationalDiagonal]
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
@[to_additive addRestrictedProductCongrRight_comp_addRationalDiagonal]
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

/-- A change of reference family applied after the diagonal is the diagonal with respect to the
new family. The eventual-integrality evidence for the new family is an argument, so that the
statement applies to whichever such evidence a consumer holds. -/
@[to_additive (attr := simp) addRationalDiagonal_change_family]
theorem rationalDiagonal_change_family {Γ : Type w} [MulOneClass Γ] (φ : ∀ i, Γ →* G i)
    (U U' : ∀ i, Subgroup (G i))
    (hU : ∀ γ : Γ, ∀ᶠ i in cofinite, φ i γ ∈ U i)
    (hU' : ∀ γ : Γ, ∀ᶠ i in cofinite, φ i γ ∈ U' i)
    (h : ∀ᶠ i in cofinite, U i = U' i) :
    (restrictedProductCongr U U' h : _ →* _).comp (rationalDiagonal φ U hU) =
      rationalDiagonal φ U' hU' := by
  ext γ i
  simp

/-- The diagonal is continuous when the coordinate maps are continuous and there is one cofinite
set of indices at which every `γ` is integral. Pointwise eventual integrality alone builds the
map but is not enough for continuity, because the restricted-product topology is finer than the
topology induced from the full product. -/
@[to_additive continuous_addRationalDiagonal]
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

/-- The uniform integrality set in `continuous_rationalDiagonal` cannot be dropped. Take
discrete groups with trivial reference subgroups, infinitely many of them nontrivial, and for `Γ`
the range of the coercion from the restricted product to the full product, that is, the finitely
supported elements, with the topology induced from the full product. The coordinate maps are
continuous and every element of `Γ` is eventually integral (it is the coercion of an element of
the restricted product), but the diagonal is not continuous:
it would make the restricted-product topology the one induced from the full product,
contradicting `not_isInducing_coe_bot`. -/
theorem continuous_eval_and_not_continuous_rationalDiagonal_range_coeMonoidHom
    [∀ i, TopologicalSpace (G i)] [∀ i, DiscreteTopology (G i)]
    (hG : {i | Nontrivial (G i)}.Infinite) :
    (∀ i, Continuous ((Pi.evalMonoidHom G i).comp (Subgroup.subtype
      (RestrictedProduct.coeMonoidHom :
        Πʳ i, [G i, ((⊥ : Subgroup (G i)) : Set (G i))] →* ∀ i, G i).range))) ∧
    ¬ Continuous (rationalDiagonal
      (fun i ↦ (Pi.evalMonoidHom G i).comp (Subgroup.subtype (RestrictedProduct.coeMonoidHom :
        Πʳ i, [G i, ((⊥ : Subgroup (G i)) : Set (G i))] →* ∀ i, G i).range))
      (fun _ ↦ ⊥) fun γ ↦ by obtain ⟨_, x, rfl⟩ := γ; exact x.2) := by
  refine ⟨fun i ↦ (continuous_apply i).comp continuous_subtype_val, fun hd ↦ ?_⟩
  refine not_isInducing_coe_bot hG ?_
  -- The coercion is the range restriction of `coeMonoidHom` followed by the inclusion of the
  -- range into the full product.
  have hcomp : ((↑) : Πʳ i, [G i, ((⊥ : Subgroup (G i)) : Set (G i))] → ∀ i, G i) =
      Subtype.val ∘ ⇑(RestrictedProduct.coeMonoidHom :
        Πʳ i, [G i, ((⊥ : Subgroup (G i)) : Set (G i))] →* ∀ i, G i).rangeRestrict := by
    ext x i
    simp
  have hf : Continuous ⇑(RestrictedProduct.coeMonoidHom :
      Πʳ i, [G i, ((⊥ : Subgroup (G i)) : Set (G i))] →* ∀ i, G i).rangeRestrict :=
    continuous_induced_rng.2 (hcomp ▸ RestrictedProduct.continuous_coe)
  -- The diagonal is a continuous left inverse of the range restriction, which is therefore an
  -- embedding, and so the coercion is inducing.
  have hid : ⇑(rationalDiagonal
      (fun i ↦ (Pi.evalMonoidHom G i).comp (Subgroup.subtype (RestrictedProduct.coeMonoidHom :
        Πʳ i, [G i, ((⊥ : Subgroup (G i)) : Set (G i))] →* ∀ i, G i).range))
      (fun _ ↦ ⊥) fun γ ↦ by obtain ⟨_, x, rfl⟩ := γ; exact x.2) ∘
        ⇑(RestrictedProduct.coeMonoidHom :
          Πʳ i, [G i, ((⊥ : Subgroup (G i)) : Set (G i))] →* ∀ i, G i).rangeRestrict = id := by
    ext x i
    simp
  rw [hcomp]
  refine IsEmbedding.subtypeVal.isInducing.comp (IsEmbedding.of_comp hf hd ?_).isInducing
  rw [hid]
  exact IsEmbedding.id

end TauCeti
