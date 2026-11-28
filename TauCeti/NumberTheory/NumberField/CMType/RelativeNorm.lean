/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMType.Basic
import TauCeti.NumberTheory.NumberField.InfinitePlace.ComplexExtension

/-!
# Relative norms and induced CM types

The representatives in an induced CM type over a fixed base place are exactly the
extensions of the representative selected at that place. Their product evaluates the
relative norm. Multiplying over all base places gives the norm formula for an induced
CM type, in the infinite-place coordinates used in archimedean character factors.

The one-place formula is `New.Parameters.prod_phi_eq_norm` in
`New/Reduction/Data/FieldsAndPlaces.lean` of [lsernau/grh-lean][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/New/Reduction/Data/FieldsAndPlaces.lean
-/

public section

open NumberField InfinitePlace

namespace TauCeti.CMType

variable {K L : Type*} [Field K] [Field L]

/-- Restricting the representative of an induced CM type gives the representative at the
underlying place in the base CM type. -/
@[simp] theorem embedding_induced_comp (Φ : CMType K) (f : K →+* L) (w : InfinitePlace L) :
    ((Φ.induced f).embedding w).comp f = Φ.embedding (w.comap f) := by
  symm
  exact Φ.embedding_eq_iff.mpr ⟨mem_induced.mp ((Φ.induced f).embedding_mem w), by
    rw [← comap_mk, mk_embedding]⟩

variable [Algebra K L]

/-- The product of the induced CM representatives above a base place evaluates the relative
norm at that place's chosen embedding. -/
theorem finprod_embedding_induced_eq_norm [FiniteDimensional K L] (Φ : CMType K)
    (v : InfinitePlace K) (x : L) :
    (∏ᶠ w ∈ placesOver L v, (Φ.induced (algebraMap K L)).embedding w x) =
      Φ.embedding v (Algebra.norm K x) := by
  let σ := Φ.embedding v
  have hσ : ¬ ComplexEmbedding.IsReal σ := fun h ↦
    Φ.ringHom_star_ne_self σ (ComplexEmbedding.isReal_iff.mp h)
  have hemb (w : placesOver L (InfinitePlace.mk σ)) :
      (Φ.induced (algebraMap K L)).embedding w.val =
        ((ComplexEmbedding.Extension.equivPlacesOver hσ).symm w).val := by
    have hw : w.val.comap (algebraMap K L) = v := by
      have h := liesOver_iff_comap_eq.mp w.property
      simpa only [σ, mk_embedding] using h
    let τ : ComplexEmbedding.Extension L σ :=
      ⟨(Φ.induced (algebraMap K L)).embedding w.val, by
        rw [ComplexEmbedding.liesOver_iff, embedding_induced_comp, hw]⟩
    have hτ : ComplexEmbedding.Extension.equivPlacesOver hσ τ = w := by
      apply Subtype.ext
      rw [ComplexEmbedding.Extension.coe_equivPlacesOver_apply]
      exact (Φ.induced (algebraMap K L)).mk_embedding w.val
    exact congrArg Subtype.val
      ((ComplexEmbedding.Extension.equivPlacesOver hσ).eq_symm_apply.mpr hτ)
  calc
    _ = ∏ᶠ w ∈ placesOver L (InfinitePlace.mk σ),
        (Φ.induced (algebraMap K L)).embedding w x := by simp only [σ, mk_embedding]
    _ = σ (Algebra.norm K x) := by
      rw [← finprod_set_coe_eq_finprod_mem]
      simp_rw [hemb]
      exact ComplexEmbedding.Extension.prod_equivPlacesOver_symm_apply hσ x

/-- The product over all representatives of an induced CM type equals the product over the
base CM type evaluated on the relative norm. -/
theorem finprod_embedding_induced_eq_finprod_norm [Finite (InfinitePlace L)] [FiniteDimensional K L]
    (Φ : CMType K) (x : L) :
    (∏ᶠ w : InfinitePlace L, (Φ.induced (algebraMap K L)).embedding w x) =
      ∏ᶠ v : InfinitePlace K, Φ.embedding v (Algebra.norm K x) := by
  have hfib : ∀ v : InfinitePlace K,
      placesOver L v = (fun w : InfinitePlace L ↦ w.comap (algebraMap K L)) ⁻¹' {v} := by
    intro v
    ext w
    exact liesOver_iff_comap_eq
  have hall : (⋃ v : InfinitePlace K, placesOver L v) = Set.univ := by
    ext w
    simp [hfib]
  have : Finite (InfinitePlace K) := Finite.of_surjective _ (comap_surjective (k := K) (K := L))
  rw [← finprod_mem_univ, ← hall, finprod_mem_iUnion, finprod_congr]
  · intro v
    exact Φ.finprod_embedding_induced_eq_norm v x
  · rw [funext hfib]
    exact fun v v' h ↦ Set.pairwiseDisjoint_fiber _ Set.univ (Set.mem_univ v) (Set.mem_univ v') h
  · exact fun _ ↦ Set.toFinite _

/-- If the base has just one infinite place, the product of the chosen embeddings on the
extension evaluates the relative norm at the selected base embedding. -/
theorem finprod_embedding_induced_eq_norm_of_subsingleton [Subsingleton (InfinitePlace K)]
    [FiniteDimensional K L] (Φ : CMType K) {σ : K →+* ℂ} (hσ : σ ∈ Φ) (x : L) :
    (∏ᶠ w : InfinitePlace L, (Φ.induced (algebraMap K L)).embedding w x) =
      σ (Algebra.norm K x) := by
  have hall : placesOver L (InfinitePlace.mk σ) = Set.univ := by
    ext w
    simp only [Set.mem_univ, iff_true]
    exact liesOver_iff_comap_eq.mpr (Subsingleton.elim _ _)
  have h := Φ.finprod_embedding_induced_eq_norm (L := L) (InfinitePlace.mk σ) x
  simpa only [hall, finprod_mem_univ, Φ.embedding_mk hσ] using h

end TauCeti.CMType
