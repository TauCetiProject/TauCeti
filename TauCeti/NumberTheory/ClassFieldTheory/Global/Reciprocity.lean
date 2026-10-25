/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.ArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Global.ClassFormation
public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.Norm
public import TauCeti.NumberTheory.ClassFieldTheory.UnitsLayer

/-!
# Finite global reciprocity

Let `K` be a number field and `L/K` a finite Galois extension, embedded in the separable closure
`Kˢ` by `ι : L →ₐ[K] Kˢ`. The global class formation `globalClassFormation K`, whose invariant is
the sum of the local invariants, has an abstract Artin reciprocity isomorphism
`ClassFormation.artinEquiv` on the layer `V ◁ G_K` of `L`, from the norm quotient of the layer to
the abelianized Galois group of the layer. Reading its two ends through

* the identification of the norm quotient of the layer with `C_K / N_{L/K}(C_L)`
  (`globalLayerNormQuotientEquiv`), and
* the identification of the Galois group of the layer with `Gal(L/K)`, by restriction along `ι`
  (`layerGalEquiv ι`),

gives **finite global reciprocity** `globalArtinEquiv K L ι : C_K / N_{L/K}(C_L) ≃ Gal(L/K)^ab`,
written additively, and the **global Artin map** `globalArtinMap K L ι : C_K → Gal(L/K)^ab`. They
are the abstract Artin equivalence and Artin map of the global class formation transported along
these identifications, and nothing else (`globalArtinEquiv_mk`). In particular the kernel of the
global Artin map is the idele-class norm group `N_{L/K}(C_L)` (`ker_globalArtinMap`), the map is
surjective, and, being defined on `C_K = 𝕀_K / Kˣ`, it kills the classes of principal ideles
(`globalArtinMap_principal`), which is the reciprocity law in idelic form. For an
abelian extension, the norm index `[C_K : N_{L/K}(C_L)]` is the degree `[L : K]`
(`card_ideleClassNormQuotient`).

As in the local case, the layer of `L` does not depend on `ι`, and changing `ι` changes
`layerGalEquiv ι` only by an inner automorphism of `Gal(L/K)`, which is trivial on the
abelianization, so finite global reciprocity does not depend on the embedding
(`globalArtinEquiv_eq_of_iota`).

The global Artin maps of the different finite Galois extensions are compatible in towers. The
global class formation has an absolute Artin map `C_K → G_K^ab` whose finite restrictions are the
Artin maps of its layers (`ClassFormation.abelianizationRestrict_absoluteArtinMap`). So if
`g ∈ G_K` represents the absolute Artin symbol of `c ∈ C_K`, then the global Artin symbol of `c`
in `Gal(L/K)^ab` is the class of the restriction of `g` to `L`, for every `L`
(`globalArtinMap_eq_of_mk_eq_absoluteArtinMap`). In particular, for a `K`-embedding `M → L` of
finite Galois extensions, restricting the global Artin symbol from `L` to `M` gives the global
Artin symbol of `M/K` (`globalArtinMap_comp`).

## Main definitions

* `TauCeti.ClassFieldTheory.globalArtinEquiv K L ι`: finite global reciprocity
  `C_K / N_{L/K}(C_L) ≃ Gal(L/K)^ab`, written additively.
* `TauCeti.ClassFieldTheory.globalArtinMap K L ι`: the global Artin map `C_K → Gal(L/K)^ab`.

## Main results

* `TauCeti.ClassFieldTheory.globalArtinEquiv_mk`: finite global reciprocity is the Artin map of
  the global class formation, read through the identifications of the layer of `L`.
* `TauCeti.ClassFieldTheory.globalArtinEquiv_eq_of_iota`: finite global reciprocity does not
  depend on the embedding of `L` into `Kˢ`.
* `TauCeti.ClassFieldTheory.ker_globalArtinMap`,
  `TauCeti.ClassFieldTheory.globalArtinMap_eq_zero_iff`: the kernel of the global Artin map is the
  idele-class norm group `N_{L/K}(C_L)`.
* `TauCeti.ClassFieldTheory.surjective_globalArtinMap`: the global Artin map is surjective.
* `TauCeti.ClassFieldTheory.globalArtinMap_principal`: the global Artin map kills principal
  ideles.
* `TauCeti.ClassFieldTheory.globalArtinMap_eq_of_mk_eq_absoluteArtinMap`: the global Artin symbol
  in `Gal(L/K)^ab` is the restriction of any representative of the absolute Artin symbol.
* `TauCeti.ClassFieldTheory.globalArtinMap_comp`: the global Artin map is compatible with
  restriction to a Galois subextension.
* `TauCeti.ClassFieldTheory.card_ideleClassNormQuotient`: the norm index theorem
  `[C_K : N_{L/K}(C_L)] = [L : K]` for a finite abelian extension.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §4.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §5 (including the compatibility of the
  norm residue symbol in towers).
* J. S. Milne, *Class Field Theory*, v4.03, Chapter VIII.
-/

public section

noncomputable section

open NumberField

namespace TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]

section Galois

variable [IsGalois K L]

/-! ### Finite global reciprocity -/

/-- **Finite global reciprocity** `C_K / N_{L/K}(C_L) ≃ Gal(L/K)^ab` for a finite Galois extension
`L/K` of number fields, embedded in the separable closure of `K` by `ι`: the abstract Artin
reciprocity isomorphism `ClassFormation.artinEquiv` of the global class formation on the layer of
`L`, read through `globalLayerNormQuotientEquiv K L` and `layerGalEquiv ι`. It does not depend on
`ι` (`globalArtinEquiv_eq_of_iota`). -/
def globalArtinEquiv (ι : L →ₐ[K] SeparableClosure K) :
    Additive (IdeleClassGroup (𝓞 K) K ⧸ (GlobalNumberFields.ideleClassNormMap K L :
        IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range) ≃+
      Additive (Abelianization Gal(L/K)) :=
  (globalLayerNormQuotientEquiv K L).trans <|
    ((globalClassFormation K).artinEquiv
        (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L))).trans
      (MulEquiv.toAdditive (layerGalEquiv ι).abelianizationCongr)

/-- **Finite global reciprocity is the abstract Artin map**: the image of the class of
`c ∈ C_K` is the Artin symbol, for the global class formation, of `c` regarded as an element of
the ground level of the layer of `L`, carried to `Gal(L/K)^ab` by restriction along `ι`. -/
@[simp]
theorem globalArtinEquiv_mk (ι : L →ₐ[K] SeparableClosure K) (c : IdeleClassGroup (𝓞 K) K) :
    globalArtinEquiv K L ι (.ofMul (c : IdeleClassGroup (𝓞 K) K ⧸
        (GlobalNumberFields.ideleClassNormMap K L :
          IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range)) =
      MulEquiv.toAdditive (layerGalEquiv ι).abelianizationCongr
        ((globalClassFormation K).artinMap
          (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L))
          (NormalLayer.groundEquivOfOpenNormal (globalFormation K) (fixingOpenNormalSubgroup K L)
            (globalGroundEquiv K (.ofMul c)))) := by
  rw [globalArtinEquiv, AddEquiv.trans_apply, AddEquiv.trans_apply,
    globalLayerNormQuotientEquiv_mk, ClassFormation.artinMap_apply]

/-- **Finite global reciprocity does not depend on the embedding** of `L` into the separable
closure: the layer of `L` is the same for every embedding, and two embeddings change the
identification of its Galois group with `Gal(L/K)` by an inner automorphism, which is trivial on
`Gal(L/K)^ab`. -/
theorem globalArtinEquiv_eq_of_iota (ι ι' : L →ₐ[K] SeparableClosure K) :
    globalArtinEquiv K L ι = globalArtinEquiv K L ι' := by
  rw [globalArtinEquiv, globalArtinEquiv, abelianizationCongr_layerGalEquiv ι ι']

/-! ### The global Artin map -/

/-- The **global Artin map** `C_K → Gal(L/K)^ab` of a finite Galois extension `L/K` of number
fields: the class modulo `N_{L/K}(C_L)` followed by finite global reciprocity
`globalArtinEquiv K L ι`. -/
def globalArtinMap (ι : L →ₐ[K] SeparableClosure K) :
    Additive (IdeleClassGroup (𝓞 K) K) →+ Additive (Abelianization Gal(L/K)) :=
  (globalArtinEquiv K L ι).toAddMonoidHom.comp
    (MonoidHom.toAdditive (QuotientGroup.mk' (GlobalNumberFields.ideleClassNormMap K L :
      IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range))

/-- The global Artin map is finite global reciprocity applied to the class modulo norms. -/
theorem globalArtinMap_apply (ι : L →ₐ[K] SeparableClosure K) (c : IdeleClassGroup (𝓞 K) K) :
    globalArtinMap K L ι (.ofMul c) =
      globalArtinEquiv K L ι (.ofMul (c : IdeleClassGroup (𝓞 K) K ⧸
        (GlobalNumberFields.ideleClassNormMap K L :
          IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range)) :=
  (rfl)

/-- The global Artin map does not depend on the embedding of `L` into the separable closure. -/
theorem globalArtinMap_eq_of_iota (ι ι' : L →ₐ[K] SeparableClosure K) :
    globalArtinMap K L ι = globalArtinMap K L ι' := by
  rw [globalArtinMap, globalArtinMap, globalArtinEquiv_eq_of_iota K L ι ι']

/-- **The kernel of the global Artin map is the idele-class norm group**: the Artin symbol of
`c ∈ C_K` is trivial exactly when `c` is the norm of an idele class of `L`. -/
@[simp]
theorem globalArtinMap_eq_zero_iff (ι : L →ₐ[K] SeparableClosure K)
    (c : IdeleClassGroup (𝓞 K) K) :
    globalArtinMap K L ι (.ofMul c) = 0 ↔
      c ∈ (GlobalNumberFields.ideleClassNormMap K L :
        IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range := by
  rw [globalArtinMap_apply, EmbeddingLike.map_eq_zero_iff, ofMul_eq_zero, QuotientGroup.eq_one_iff]

/-- **The kernel of the global Artin map is the idele-class norm group** `N_{L/K}(C_L)`, written
additively. -/
theorem ker_globalArtinMap (ι : L →ₐ[K] SeparableClosure K) :
    (globalArtinMap K L ι).ker =
      (GlobalNumberFields.ideleClassNormMap K L :
        IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range.toAddSubgroup := by
  ext c
  rw [AddMonoidHom.mem_ker, ← ofMul_toMul c, globalArtinMap_eq_zero_iff,
    Additive.mem_toAddSubgroup, toMul_ofMul]

/-- **The global Artin map is surjective.** -/
theorem surjective_globalArtinMap (ι : L →ₐ[K] SeparableClosure K) :
    Function.Surjective (globalArtinMap K L ι) :=
  (globalArtinEquiv K L ι).surjective.comp <| QuotientGroup.mk'_surjective
    (GlobalNumberFields.ideleClassNormMap K L :
      IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range

/-- **The global Artin map kills principal ideles**: the class in `C_K` of the principal idele of
`x ∈ Kˣ` is trivial, so its Artin symbol vanishes. This is the reciprocity law in idelic form. -/
@[simp]
theorem globalArtinMap_principal (ι : L →ₐ[K] SeparableClosure K) (x : Kˣ) :
    globalArtinMap K L ι
        (.ofMul (IdeleGroup.unitEmbedding (𝓞 K) K x : IdeleClassGroup (𝓞 K) K)) = 0 := by
  rw [(QuotientGroup.eq_one_iff (N := IdeleGroup.principalSubgroup (𝓞 K) K) _).2 ⟨x, rfl⟩,
    ofMul_one, map_zero]

/-! ### Compatibility in towers -/

/-- **The global Artin map through a representative of the absolute Artin symbol.** If
`g ∈ G_K` represents the absolute Artin symbol of `c ∈ C_K` for the global class formation, then
for every finite Galois extension `L/K`, embedded in the separable closure by `ι`, the Artin
symbol of `c` in `Gal(L/K)^ab` is the class of the restriction of `g` along `ι`. -/
theorem globalArtinMap_eq_of_mk_eq_absoluteArtinMap (ι : L →ₐ[K] SeparableClosure K)
    {c : IdeleClassGroup (𝓞 K) K} (g : AbsoluteGaloisGroup K)
    (hg : Additive.ofMul (g : TopologicalAbelianization (AbsoluteGaloisGroup K)) =
      (globalClassFormation K).absoluteArtinMap (globalGroundEquiv K (.ofMul c))) :
    globalArtinMap K L ι (.ofMul c) = .ofMul (Abelianization.of (ι.restrictNormalHom g)) := by
  have hmem : g ∈ (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).ground := by simp
  rw [globalArtinMap_apply, globalArtinEquiv_mk,
    ← (globalClassFormation K).abelianizationRestrict_absoluteArtinMap, ← hg,
    NormalLayer.abelianizationRestrict_mk _ ⟨g, hmem⟩, MulEquiv.toAdditive_apply_apply,
    toMul_ofMul, abelianizationCongr_of, layerGalEquiv_mk]

/-- **The global Artin map is compatible in towers**: for a `K`-embedding `f : M → L` of a
finite Galois extension `M/K` into `L`, restricting the global Artin symbol in `Gal(L/K)^ab` to
`M` along `f` gives the global Artin symbol in `Gal(M/K)^ab`. -/
theorem globalArtinMap_comp {M : Type*} [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (f : M →ₐ[K] L) (ι : L →ₐ[K] SeparableClosure K) :
    (Abelianization.map f.restrictNormalHom).toAdditive.comp (globalArtinMap K L ι) =
      globalArtinMap K M (ι.comp f) := by
  refine AddMonoidHom.ext fun c ↦ ?_
  -- Represent the absolute Artin symbol of `c` by some `g ∈ G_K`; both symbols restrict `g`.
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective
    ((globalClassFormation K).absoluteArtinMap (globalGroundEquiv K c)).toMul
  have hg' : Additive.ofMul (g : TopologicalAbelianization (AbsoluteGaloisGroup K)) =
      (globalClassFormation K).absoluteArtinMap (globalGroundEquiv K (.ofMul c.toMul)) :=
    congrArg Additive.ofMul hg
  rw [AddMonoidHom.comp_apply, ← ofMul_toMul c,
    globalArtinMap_eq_of_mk_eq_absoluteArtinMap K L ι g hg',
    globalArtinMap_eq_of_mk_eq_absoluteArtinMap K M (ι.comp f) g hg',
    MonoidHom.toAdditive_apply_apply, toMul_ofMul, Abelianization.map_of,
    AlgHom.restrictNormalHom_restrictNormalHom]

end Galois

/-! ### The norm index of an abelian extension -/

open scoped IsMulCommutative in
/-- **The norm index theorem**: for a finite abelian extension `L/K` of number fields,
`[C_K : N_{L/K}(C_L)] = [L : K]`, since finite global reciprocity identifies the norm quotient with
`Gal(L/K)^ab`, which is `Gal(L/K)` itself. -/
theorem card_ideleClassNormQuotient [IsAbelianGalois K L] :
    Nat.card (IdeleClassGroup (𝓞 K) K ⧸ (GlobalNumberFields.ideleClassNormMap K L :
        IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range) = Module.finrank K L := by
  rw [Nat.card_congr (MulEquiv.toAdditive.symm (globalArtinEquiv K L IsSepClosed.lift)).toEquiv,
    ← Nat.card_congr (Abelianization.equivOfComm (H := Gal(L/K))).toEquiv,
    IsGalois.card_aut_eq_finrank]

end TauCeti.ClassFieldTheory
