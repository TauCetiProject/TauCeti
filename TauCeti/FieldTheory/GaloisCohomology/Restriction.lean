/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialF2.Basic

/-!
# Restriction across a finite extension of fields

A finite extension `L/K` and an embedding `σ : L →ₐ[K] Kˢ` identify `G_L` with the open
subgroup of `G_K` fixing `σ(L)`. This file transports continuous cohomology with trivial
`𝔽₂` coefficients across that identification and defines restriction from `G_K` to `G_L`.

The formula for `galoisRes` is restriction to `galoisSubgroup K L σ`, followed by transport
along `galoisSubgroupEquiv K L σ`. Its direct compatible-pair form pulls back along the
composite `G_L → G_K`. The chosen embedding is part of both formulas, but not of the resulting
map: another embedding, or another extension of `σ` to the separable closures, changes the
composite `G_L → G_K` by an inner automorphism of `G_K`, and inner automorphisms act trivially on
cohomology. So `galoisRes` is a map attached to `L/K` alone, and it is functorial in towers.

## Main definitions

* `TauCeti.galoisF2Iso`: transport of trivial-coefficient cohomology from the fixing subgroup
  to `G_L`.
* `TauCeti.galoisRes`: restriction from `G_K` to `G_L`.

## Main results

* `TauCeti.galoisF2Iso_hom_cup`, `TauCeti.galoisF2Iso_inv_cup`: the transport preserves the
  `𝔽₂`-valued cup product.
* `TauCeti.galoisRes_cup`: restriction preserves the `𝔽₂`-valued cup product.
* `TauCeti.galoisRes_embedding_independent`: restriction does not depend on the embedding.
* `TauCeti.galoisRes_comp`, `TauCeti.galoisRes_galoisRes`: restriction is functorial in a tower
  `K ⊆ L ⊆ M`.

## Reference

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  Chapter I, §5, for restriction through the open subgroup associated to a finite extension,
  and (1.5.3)(i) for its compatibility with cup products.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory

universe u

variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K) [FiniteDimensional K L]

/-- Cohomology of the fixing subgroup of `σ(L)` identified with cohomology of `G_L`,
with trivial `𝔽₂` coefficients, in every degree. -/
def galoisF2Iso (n : ℕ) :
    continuousCohomology n (trivialF2 ↥(galoisSubgroup K L σ).toSubgroup) ≅
      continuousCohomology n (trivialF2 (AbsoluteGaloisGroup L)) :=
  trivialF2Iso (galoisSubgroupEquiv K L σ).symm n

/-- The forward transport is cohomological pullback along `G_L ≃ galoisSubgroup K L σ`. -/
@[simp]
theorem galoisF2Iso_hom (n : ℕ) :
    (galoisF2Iso K L σ n).hom =
      trivialF2Map (ContinuousMonoidHom.toContinuousMonoidHom
        (galoisSubgroupEquiv K L σ)) n := by
  rw [galoisF2Iso, trivialF2Iso_hom]
  rfl

/-- The inverse transport is pullback along the inverse topological group isomorphism. -/
@[simp]
theorem galoisF2Iso_inv (n : ℕ) :
    (galoisF2Iso K L σ n).inv =
      trivialF2Map (ContinuousMonoidHom.toContinuousMonoidHom
        (galoisSubgroupEquiv K L σ).symm) n := by
  rw [galoisF2Iso, trivialF2Iso_inv]

/-- The forward transport `galoisF2Iso` preserves the cup product on `𝔽₂`-cohomology. -/
theorem galoisF2Iso_hom_cup (m n : ℕ)
    (x : continuousCohomology m (trivialF2 ↥(galoisSubgroup K L σ).toSubgroup))
    (y : continuousCohomology n (trivialF2 ↥(galoisSubgroup K L σ).toSubgroup)) :
    (galoisF2Iso K L σ (m + n)).hom
        ((trivialF2TopPairing (galoisSubgroup K L σ).toSubgroup).cup m n x y) =
      (trivialF2TopPairing (AbsoluteGaloisGroup L)).cup m n
        ((galoisF2Iso K L σ m).hom x) ((galoisF2Iso K L σ n).hom y) := by
  simp only [galoisF2Iso_hom, trivialF2Map_cup]

/-- The inverse transport `galoisF2Iso` preserves the cup product on `𝔽₂`-cohomology. -/
theorem galoisF2Iso_inv_cup (m n : ℕ)
    (x : continuousCohomology m (trivialF2 (AbsoluteGaloisGroup L)))
    (y : continuousCohomology n (trivialF2 (AbsoluteGaloisGroup L))) :
    (galoisF2Iso K L σ (m + n)).inv ((trivialF2TopPairing (AbsoluteGaloisGroup L)).cup m n x y) =
      (trivialF2TopPairing (galoisSubgroup K L σ).toSubgroup).cup m n
        ((galoisF2Iso K L σ m).inv x) ((galoisF2Iso K L σ n).inv y) := by
  simp only [galoisF2Iso_inv, trivialF2Map_cup]

/-- Restriction on `𝔽₂`-cohomology for the finite extension `L/K`, relative to `σ`.
It is subgroup restriction followed by the canonical identification with `G_L`. -/
def galoisRes (n : ℕ) :
    continuousCohomology n (trivialF2 (AbsoluteGaloisGroup K)) ⟶
      continuousCohomology n (trivialF2 (AbsoluteGaloisGroup L)) :=
  trivialF2ResMap (AbsoluteGaloisGroup K) (galoisSubgroup K L σ).toSubgroup n ≫
    (galoisF2Iso K L σ n).hom

/-- The definition of field-extension restriction as subgroup restriction followed by
transport to the absolute Galois group of `L`. -/
theorem galoisRes_def (n : ℕ) :
    galoisRes K L σ n =
      trivialF2ResMap (AbsoluteGaloisGroup K) (galoisSubgroup K L σ).toSubgroup n ≫
        (galoisF2Iso K L σ n).hom :=
  (rfl)

/-- Field-extension restriction is the compatible-pair map along the composite
`G_L → galoisSubgroup K L σ → G_K`. -/
theorem galoisRes_eq_map (n : ℕ) :
    galoisRes K L σ n =
      trivialF2Map
        ((ContinuousMonoidHom.subgroupSubtype (galoisSubgroup K L σ).toSubgroup).comp
          (ContinuousMonoidHom.toContinuousMonoidHom (galoisSubgroupEquiv K L σ))) n := by
  rw [galoisRes_def, ← trivialF2Map_subgroupSubtype, galoisF2Iso_hom,
    ← trivialF2Map_comp]

/-- **Restriction preserves the cup product** on `𝔽₂`-cohomology, in every bidegree:
`res (x ⌣ y) = res x ⌣ res y`. -/
@[simp]
theorem galoisRes_cup (m n : ℕ)
    (x : continuousCohomology m (trivialF2 (AbsoluteGaloisGroup K)))
    (y : continuousCohomology n (trivialF2 (AbsoluteGaloisGroup K))) :
    galoisRes K L σ (m + n) ((trivialF2TopPairing (AbsoluteGaloisGroup K)).cup m n x y) =
      (trivialF2TopPairing (AbsoluteGaloisGroup L)).cup m n
        (galoisRes K L σ m x) (galoisRes K L σ n y) := by
  simp only [galoisRes_eq_map, trivialF2Map_cup]

/-! ### Independence of the embedding and towers -/

/-- Field-extension restriction is pullback along conjugation `x ↦ E ∘ x ∘ E⁻¹` by any ring
isomorphism `E : Lˢ ≃+* Kˢ` fixing `K`: such an `E` differs from the one underlying
`galoisSubgroupEquiv K L σ` by an element `γ` of `G_K`, so the two homomorphisms `G_L → G_K`
differ by conjugation by `γ`. -/
private theorem galoisRes_eq_trivialF2Map_of_ringEquiv
    (E : SeparableClosure L ≃+* SeparableClosure K)
    (hE : ∀ c : K, E (algebraMap K (SeparableClosure L) c) = algebraMap K (SeparableClosure K) c)
    (φ : AbsoluteGaloisGroup L →ₜ* AbsoluteGaloisGroup K)
    (hφ : ∀ x y, φ x y = E (x (E.symm y))) (n : ℕ) :
    galoisRes K L σ n = trivialF2Map φ n := by
  let e := separableClosureRingEquiv K L σ
  -- `γ = E ∘ e⁻¹` fixes `K`, so it is an element of `G_K`.
  let γ : AbsoluteGaloisGroup K := AlgEquiv.ofRingEquiv (f := e.symm.trans E) fun c => by
    rw [RingEquiv.trans_apply, e.symm_apply_eq.2 (separableClosureRingEquiv_algebraMap_base
      K L σ c).symm, hE]
  have hγ (w : SeparableClosure L) : γ (e w) = E w := by simp [γ]
  have hγ' (w : SeparableClosure L) : γ⁻¹ (E w) = e w := by
    rw [← hγ, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  rw [galoisRes_eq_map]
  refine (trivialF2Map_eq_of_conj _ φ γ (fun x => ?_) n).symm
  ext y
  obtain ⟨w, rfl⟩ := E.surjective y
  simp [hφ, AlgEquiv.mul_apply, hγ', galoisSubgroupEquiv_apply, e, hγ]

/-- **Field-extension restriction does not depend on the embedding**: two `K`-embeddings
`σ τ : L →ₐ[K] Kˢ` induce the same restriction `Hⁿ(G_K, 𝔽₂) ⟶ Hⁿ(G_L, 𝔽₂)`, in every degree.
The two homomorphisms `G_L → G_K` differ by an inner automorphism of `G_K`. -/
theorem galoisRes_embedding_independent (τ : L →ₐ[K] SeparableClosure K) (n : ℕ) :
    galoisRes K L σ n = galoisRes K L τ n := by
  rw [galoisRes_eq_trivialF2Map_of_ringEquiv K L σ (separableClosureRingEquiv K L τ)
    (separableClosureRingEquiv_algebraMap_base K L τ)
    ((ContinuousMonoidHom.subgroupSubtype (galoisSubgroup K L τ).toSubgroup).comp
      (ContinuousMonoidHom.toContinuousMonoidHom (galoisSubgroupEquiv K L τ)))
    (fun x y => galoisSubgroupEquiv_apply K L τ x y), galoisRes_eq_map]

variable (M : Type u) [Field M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional L M] [FiniteDimensional K M]
  (τ : M →ₐ[L] SeparableClosure L) (ρ : M →ₐ[K] SeparableClosure K)

/-- **Restriction is functorial in a tower** `K ⊆ L ⊆ M`: restricting from `G_K` to `G_L` and
then to `G_M` is restriction from `G_K` to `G_M`. The three embeddings `σ`, `τ` and `ρ` are
arbitrary and need not be compatible with one another. -/
theorem galoisRes_comp (n : ℕ) :
    galoisRes K L σ n ≫ galoisRes L M τ n = galoisRes K M ρ n := by
  rw [galoisRes_eq_map K L, galoisRes_eq_map L M, ← trivialF2Map_comp]
  refine (galoisRes_eq_trivialF2Map_of_ringEquiv K M ρ
    ((separableClosureRingEquiv L M τ).trans (separableClosureRingEquiv K L σ))
    (fun c => ?_) _ (fun x y => ?_) n).symm
  · rw [IsScalarTower.algebraMap_apply K M (SeparableClosure M),
      IsScalarTower.algebraMap_apply K L M,
      ← IsScalarTower.algebraMap_apply L M (SeparableClosure M), RingEquiv.trans_apply,
      separableClosureRingEquiv_algebraMap_base, ← IsScalarTower.algebraMap_apply,
      separableClosureRingEquiv_algebraMap_base]
  · simp [galoisSubgroupEquiv_apply]

/-- **`res (res x) = res x`** along a tower `K ⊆ L ⊆ M`, for every class `x ∈ Hⁿ(G_K, 𝔽₂)` and
arbitrary embeddings. -/
theorem galoisRes_galoisRes (n : ℕ)
    (x : continuousCohomology n (trivialF2 (AbsoluteGaloisGroup K))) :
    galoisRes L M τ n (galoisRes K L σ n x) = galoisRes K M ρ n x := by
  rw [← galoisRes_comp K L σ M τ ρ n, ConcreteCategory.comp_apply]

end TauCeti
