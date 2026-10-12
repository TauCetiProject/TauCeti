/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.ArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Local.ClassFormation
public import TauCeti.NumberTheory.ClassFieldTheory.UnitsLayer

/-!
# Finite local reciprocity

Let `K` be a nonarchimedean local field and `L/K` a finite Galois extension, embedded in the
separable closure `Kˢ` by `ι : L →ₐ[K] Kˢ`. The local class formation
`TauCeti.ClassFieldTheory.localClassFormation K` has an abstract Artin reciprocity isomorphism
`ClassFormation.artinEquiv` on the layer `V ◁ G_K` of `L`, from the norm quotient of the layer to
the abelianized Galois group of the layer. Reading its two ends through the identifications of
`TauCeti.ClassFieldTheory.UnitsLayer`,

* the norm quotient of the layer with `Kˣ / N_{L/K}(Lˣ)` (`layerNormQuotientEquiv`), and
* the Galois group of the layer with `Gal(L/K)`, by restriction along `ι` (`layerGalEquiv ι`),

gives **finite local reciprocity** `localArtinEquiv K L ι : Kˣ / N_{L/K}(Lˣ) ≃ Gal(L/K)^ab`,
written additively, and the **local Artin map** `localArtinMap K L ι : Kˣ → Gal(L/K)^ab`.
They are the abstract Artin equivalence and Artin map of the local class formation transported
along these identifications, and nothing else (`localArtinEquiv_mk`); in particular the kernel of
the local Artin map is the norm group `N_{L/K}(Lˣ)` (`ker_localArtinMap`) and it is surjective.

The layer of `L` does not depend on `ι`, and changing `ι` changes `layerGalEquiv ι` only by an
inner automorphism of `Gal(L/K)`, which is trivial on the abelianization. So finite local
reciprocity does not depend on the embedding (`localArtinEquiv_eq_of_iota`), and its
multiplicative form `normResidue K L : Kˣ / N_{L/K}(Lˣ) ≃* Gal(L/K)^ab` is canonical
(`toAdditive_normResidue`).

## Main definitions

* `TauCeti.ClassFieldTheory.localArtinEquiv K L ι`: finite local reciprocity
  `Kˣ / N_{L/K}(Lˣ) ≃ Gal(L/K)^ab`, written additively.
* `TauCeti.ClassFieldTheory.localArtinMap K L ι`: the local Artin map `Kˣ → Gal(L/K)^ab`.
* `TauCeti.ClassFieldTheory.normResidue K L`: the norm residue isomorphism, the multiplicative
  form of finite local reciprocity.

## Main results

* `TauCeti.ClassFieldTheory.localArtinEquiv_mk`: finite local reciprocity is the Artin map of the
  local class formation, read through the identifications of the layer of `L`.
* `TauCeti.ClassFieldTheory.localArtinEquiv_eq_of_iota`: finite local reciprocity does not
  depend on the embedding of `L` into `Kˢ`.
* `TauCeti.ClassFieldTheory.ker_localArtinMap`,
  `TauCeti.ClassFieldTheory.localArtinMap_eq_zero_iff`: the kernel of the local Artin map is the
  norm group `N_{L/K}(Lˣ)`.
* `TauCeti.ClassFieldTheory.surjective_localArtinMap`: the local Artin map is surjective.
* `TauCeti.ClassFieldTheory.toAdditive_normResidue`: `normResidue` is finite local reciprocity
  for every embedding.
* `TauCeti.ClassFieldTheory.index_normGroup_of_isMulCommutative`: the norm group of a finite
  abelian extension has index equal to the degree.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§4–5.
* J.-P. Serre, *Local Fields*, Chapter XI, §3.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-! ### Finite local reciprocity -/

/-- **Finite local reciprocity** `Kˣ / N_{L/K}(Lˣ) ≃ Gal(L/K)^ab` for a finite Galois extension
`L/K` of a nonarchimedean local field, embedded in the separable closure by `ι`: the abstract
Artin reciprocity isomorphism `ClassFormation.artinEquiv` of the local class formation on the
layer of `L`, read through `layerNormQuotientEquiv K L` and `layerGalEquiv ι`. It does not depend
on `ι` (`localArtinEquiv_eq_of_iota`). -/
def localArtinEquiv (ι : L →ₐ[K] SeparableClosure K) :
    Additive (Kˣ ⧸ normGroup K L) ≃+ Additive (Abelianization Gal(L/K)) :=
  (layerNormQuotientEquiv K L).trans <|
    ((localClassFormation K).artinEquiv
        (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L))).trans
      (MulEquiv.toAdditive (layerGalEquiv ι).abelianizationCongr)

/-- **Finite local reciprocity is the abstract Artin map**: the image of the class of `a ∈ Kˣ` is
the Artin symbol, for the local class formation, of `a` regarded as an element of the ground level
of the layer of `L`, carried to `Gal(L/K)^ab` by restriction along `ι`. -/
@[simp]
theorem localArtinEquiv_mk (ι : L →ₐ[K] SeparableClosure K) (a : Kˣ) :
    localArtinEquiv K L ι (Additive.ofMul (a : Kˣ ⧸ normGroup K L)) =
      MulEquiv.toAdditive (layerGalEquiv ι).abelianizationCongr
        ((localClassFormation K).artinMap
          (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L))
          (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
            (fixedField_ground_ofOpenNormal K (fixingOpenNormalSubgroup K L))
            (Additive.ofMul a))) := by
  rw [localArtinEquiv, AddEquiv.trans_apply, AddEquiv.trans_apply, layerNormQuotientEquiv_mk,
    ClassFormation.artinMap_apply]

/-- **Finite local reciprocity does not depend on the embedding** of `L` into the separable
closure: the layer of `L` is the same for every embedding, and two embeddings change the
identification of its Galois group with `Gal(L/K)` by an inner automorphism, which is trivial on
`Gal(L/K)^ab`. -/
theorem localArtinEquiv_eq_of_iota (ι ι' : L →ₐ[K] SeparableClosure K) :
    localArtinEquiv K L ι = localArtinEquiv K L ι' := by
  rw [localArtinEquiv, localArtinEquiv, abelianizationCongr_layerGalEquiv ι ι']

/-! ### The local Artin map -/

/-- The **local Artin map** `Kˣ → Gal(L/K)^ab` of a finite Galois extension `L/K` of a
nonarchimedean local field: the class modulo `N_{L/K}(Lˣ)` followed by finite local reciprocity
`localArtinEquiv K L ι`. -/
def localArtinMap (ι : L →ₐ[K] SeparableClosure K) :
    Additive Kˣ →+ Additive (Abelianization Gal(L/K)) :=
  (localArtinEquiv K L ι).toAddMonoidHom.comp
    (MonoidHom.toAdditive (QuotientGroup.mk' (normGroup K L)))

/-- The local Artin map is finite local reciprocity applied to the class modulo norms. -/
theorem localArtinMap_apply (ι : L →ₐ[K] SeparableClosure K) (a : Kˣ) :
    localArtinMap K L ι (Additive.ofMul a) =
      localArtinEquiv K L ι (Additive.ofMul (a : Kˣ ⧸ normGroup K L)) :=
  (rfl)

/-- The local Artin map does not depend on the embedding of `L` into the separable closure. -/
theorem localArtinMap_eq_of_iota (ι ι' : L →ₐ[K] SeparableClosure K) :
    localArtinMap K L ι = localArtinMap K L ι' := by
  rw [localArtinMap, localArtinMap, localArtinEquiv_eq_of_iota K L ι ι']

/-- **The kernel of the local Artin map is the norm group**: the Artin symbol of `a ∈ Kˣ` is
trivial exactly when `a` is a norm from `L`. -/
@[simp]
theorem localArtinMap_eq_zero_iff (ι : L →ₐ[K] SeparableClosure K) (a : Kˣ) :
    localArtinMap K L ι (Additive.ofMul a) = 0 ↔ a ∈ normGroup K L := by
  rw [localArtinMap_apply, EmbeddingLike.map_eq_zero_iff, ofMul_eq_zero, QuotientGroup.eq_one_iff]

/-- **The kernel of the local Artin map is the norm group** `N_{L/K}(Lˣ)`, written additively. -/
theorem ker_localArtinMap (ι : L →ₐ[K] SeparableClosure K) :
    (localArtinMap K L ι).ker = (normGroup K L).toAddSubgroup := by
  ext a
  rw [AddMonoidHom.mem_ker, ← ofMul_toMul a, localArtinMap_eq_zero_iff,
    Additive.mem_toAddSubgroup, toMul_ofMul]

/-- **The local Artin map is surjective.** -/
theorem surjective_localArtinMap (ι : L →ₐ[K] SeparableClosure K) :
    Function.Surjective (localArtinMap K L ι) :=
  (localArtinEquiv K L ι).surjective.comp (QuotientGroup.mk'_surjective (normGroup K L))

/-! ### The norm residue isomorphism -/

/-- The **norm residue isomorphism** `Kˣ / N_{L/K}(Lˣ) ≃* Gal(L/K)^ab`: the multiplicative form of
finite local reciprocity `localArtinEquiv`, for the embedding of `L` into the separable closure
supplied by `IsSepClosed.lift`. Since finite local reciprocity does not depend on the embedding,
it is the multiplicative form of `localArtinEquiv K L ι` for every `ι` (`toAdditive_normResidue`).
-/
def normResidue : (Kˣ ⧸ normGroup K L) ≃* Abelianization Gal(L/K) :=
  MulEquiv.toAdditive.symm (localArtinEquiv K L (IsSepClosed.lift : L →ₐ[K] SeparableClosure K))

/-- **The norm residue isomorphism is finite local reciprocity** for every embedding `ι` of `L`
into the separable closure. -/
theorem toAdditive_normResidue (ι : L →ₐ[K] SeparableClosure K) :
    MulEquiv.toAdditive (normResidue K L) = localArtinEquiv K L ι := by
  rw [normResidue, Equiv.apply_symm_apply, localArtinEquiv_eq_of_iota]

/-- The norm residue symbol of the class of `a ∈ Kˣ` is its local Artin symbol, for any
embedding `ι` of `L` into the separable closure. -/
theorem normResidue_mk (ι : L →ₐ[K] SeparableClosure K) (a : Kˣ) :
    normResidue K L (a : Kˣ ⧸ normGroup K L) =
      (localArtinMap K L ι (Additive.ofMul a)).toMul := by
  rw [localArtinMap_apply, ← toAdditive_normResidue K L ι, MulEquiv.toAdditive_apply_apply,
    toMul_ofMul, toMul_ofMul]

open scoped IsMulCommutative in
/-- **The norm index of a finite abelian extension**: if `Gal(L/K)` is commutative, then
`[Kˣ : N_{L/K}(Lˣ)] = [L : K]`, since the norm residue isomorphism identifies the norm quotient
with `Gal(L/K)^ab`, which is `Gal(L/K)` itself. -/
theorem index_normGroup_of_isMulCommutative [IsMulCommutative Gal(L/K)] :
    (normGroup K L).index = Module.finrank K L := by
  rw [Subgroup.index, Nat.card_congr (normResidue K L).toEquiv,
    ← Nat.card_congr (Abelianization.equivOfComm (H := Gal(L/K))).toEquiv,
    IsGalois.card_aut_eq_finrank]

end TauCeti.ClassFieldTheory
