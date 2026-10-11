/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MappingTorus.FiberPair

/-!
# The Wang sequence of a mapping torus

Let `T` be the mapping torus of a homeomorphism `φ : F ≃ₜ F`, with fibre inclusion
`i : F ⟶ T` at height zero.  Its singular homology fits into the **Wang long exact sequence**
```
⋯ ⟶ Hₙ₊₁(T) ⟶ Hₙ(F) ⟶ Hₙ(F) ⟶ Hₙ(T) ⟶ Hₙ₋₁(F) ⟶ ⋯ ⟶ H₀(F) ⟶ H₀(F) ⟶ H₀(T) ⟶ 0
```
whose maps are the Wang connecting morphism `Hₙ₊₁(T) ⟶ Hₙ(F)`
(`TauCeti.MappingTorus.wangδ`), the endomorphism `id - φ_*` of `Hₙ(F)`, and the map `i_*`
induced by the fibre inclusion.  Coefficients are an object of an abelian category with
coproducts.

The sequence is the long exact sequence of the pair `(T, F)`, with `Hₙ₊₁(T, F)` replaced by
`Hₙ(F)` through `TauCeti.MappingTorus.singularHomologyFiberPairIso`.  Under that isomorphism the
connecting morphism of the pair is `id - φ_*` followed by the fibre inclusion
(`TauCeti.MappingTorus.singularHomologyδ_fiberPair`), and the Wang connecting morphism is the
quotient map `Hₙ₊₁(T) ⟶ Hₙ₊₁(T, F)` followed by the isomorphism.

A map `g : F ⟶ G` intertwining `φ` with a homeomorphism `ψ : G ≃ₜ G` induces a map of mapping
tori, and the Wang sequence is natural for it: the square through `i_*` commutes by
`TauCeti.MappingTorus.map_comp_incl`, the square through `id - φ_*` by
`TauCeti.MappingTorus.sub_monodromy_naturality`, and the square through the connecting morphism by
`TauCeti.MappingTorus.wangδ_naturality`.

## Main declarations

* `TauCeti.MappingTorus.wangδ`: the connecting morphism `Hₙ₊₁(T) ⟶ Hₙ(F)`.
* `TauCeti.MappingTorus.wang_exact₁`, `TauCeti.MappingTorus.wang_exact₂`,
  `TauCeti.MappingTorus.wang_exact₃`: exactness at the target of `id - φ_*`, at `Hₙ₊₁(T)`, and at
  the source of `id - φ_*`.
* `TauCeti.MappingTorus.epi_map_incl_zero`: `H₀(F) ⟶ H₀(T)` is an epimorphism.
* `TauCeti.MappingTorus.wangδ_naturality`: naturality of the connecting morphism.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2 (the long exact sequence of a mapping torus).
* H.-C. Wang, *The homology groups of the fibre bundles over a sphere*, Duke Math. J. 16 (1949).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe w v u

namespace TauCeti.MappingTorus

variable {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F)
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-! The maps of the long exact sequence of the pair `(T, F)` have the homology of the singular
simplicial sets as sources and targets, while the Wang sequence is stated with
`singularHomologyFunctor`.  The two agree definitionally but not syntactically, so the three maps
are first restated with the types used below; rewriting then sees one form only. -/

/-- The quotient map `Hₙ(T) ⟶ Hₙ(T, F)`, with its source written as singular homology of `T`. -/
private def fiberPairπ (n : ℕ) :
    ((singularHomologyFunctor A n).obj R).obj (TopCat.of (MappingTorus φ)) ⟶
      (fiberPair φ).singularHomology R n :=
  (fiberPair φ).singularHomologyπ R n

/-- The connecting morphism `Hₙ₊₁(T, F) ⟶ Hₙ(F)` of the pair, with its target written as singular
homology of the fibre. -/
private def fiberPairδ (n : ℕ) :
    (fiberPair φ).singularHomology R (n + 1) ⟶
      ((singularHomologyFunctor A n).obj R).obj (fiberPair φ).snd :=
  (fiberPair φ).singularHomologyδ R (n + 1) n

/-- The map `Hₙ(F) ⟶ Hₙ(T)` induced by the inclusion of the subspace of the pair `(T, F)`, with
its target written as singular homology of `T`. -/
private def fiberPairι (n : ℕ) :
    ((singularHomologyFunctor A n).obj R).obj (fiberPair φ).snd ⟶
      ((singularHomologyFunctor A n).obj R).obj (TopCat.of (MappingTorus φ)) :=
  ((singularHomologyFunctor A n).obj R).map (fiberPair φ).map

@[reassoc]
private lemma fiberPairι_comp_fiberPairπ (n : ℕ) : fiberPairι φ R n ≫ fiberPairπ φ R n = 0 :=
  (fiberPair φ).homologyMap_comp_singularHomologyπ R n

@[reassoc]
private lemma fiberPairδ_comp_fiberPairι (n : ℕ) : fiberPairδ φ R n ≫ fiberPairι φ R n = 0 :=
  (fiberPair φ).singularHomologyδ_comp R (n + 1) n

@[reassoc]
private lemma fiberPairπ_comp_fiberPairδ (n : ℕ) :
    fiberPairπ φ R (n + 1) ≫ fiberPairδ φ R n = 0 :=
  (fiberPair φ).singularHomologyπ_comp_singularHomologyδ R (n + 1) n

/-- The map induced on homology by the fibre inclusion of the pair `(T, F)`, followed by the map
induced by the inclusion of the fibre, is the map induced by `MappingTorus.incl`. -/
private lemma map_fiberPairIncl_comp_fiberPairι (n : ℕ) :
    ((singularHomologyFunctor A n).obj R).map (fiberPairIncl φ) ≫ fiberPairι φ R n =
      ((singularHomologyFunctor A n).obj R).map (TopCat.ofHom (incl φ)) :=
  (Functor.map_comp _ _ _).symm.trans (congrArg _ (fiberPairIncl_comp_map φ))

/-- The connecting morphism of `(T, F)`, after `Hₙ(F) ≅ Hₙ₊₁(T, F)`, is `id - φ_*` followed by
the fibre inclusion. -/
private lemma singularHomologyFiberPairIso_inv_comp_fiberPairδ (n : ℕ) :
    (singularHomologyFiberPairIso φ R n).inv ≫ fiberPairδ φ R n =
      (𝟙 _ - ((singularHomologyFunctor A n).obj R).map
          (TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F)))) ≫
        ((singularHomologyFunctor A n).obj R).map (fiberPairIncl φ) := by
  have h : fiberPairδ φ R n = (singularHomologyFiberPairIso φ R n).hom ≫
      (𝟙 _ - ((singularHomologyFunctor A n).obj R).map
          (TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F)))) ≫
        ((singularHomologyFunctor A n).obj R).map (fiberPairIncl φ) :=
    singularHomologyδ_fiberPair φ R n
  rw [h, Iso.inv_hom_id_assoc]

/-- The **Wang connecting morphism** `Hₙ₊₁(T) ⟶ Hₙ(F)` of the mapping torus `T` of `φ`: the
quotient map `Hₙ₊₁(T) ⟶ Hₙ₊₁(T, F)` followed by the isomorphism `Hₙ₊₁(T, F) ≅ Hₙ(F)`. -/
def wangδ (n : ℕ) :
    ((singularHomologyFunctor A (n + 1)).obj R).obj (TopCat.of (MappingTorus φ)) ⟶
      ((singularHomologyFunctor A n).obj R).obj (TopCat.of F) :=
  fiberPairπ φ R (n + 1) ≫ (singularHomologyFiberPairIso φ R n).hom

lemma wangδ_def (n : ℕ) :
    wangδ φ R n =
      (fiberPair φ).singularHomologyπ R (n + 1) ≫ (singularHomologyFiberPairIso φ R n).hom :=
  (rfl)

/-- The Wang connecting morphism followed by `Hₙ(F) ≅ Hₙ₊₁(T, F)` is the quotient map
`Hₙ₊₁(T) ⟶ Hₙ₊₁(T, F)`. -/
@[reassoc (attr := simp)]
lemma wangδ_comp_singularHomologyFiberPairIso_inv (n : ℕ) :
    wangδ φ R n ≫ (singularHomologyFiberPairIso φ R n).inv =
      (fiberPair φ).singularHomologyπ R (n + 1) := by
  rw [wangδ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  -- `fiberPairπ` is `(fiberPair φ).singularHomologyπ`, with its source restated.
  rfl

/-- The fibre inclusion followed by the Wang connecting morphism vanishes. -/
@[reassoc (attr := simp)]
lemma map_incl_comp_wangδ (n : ℕ) :
    ((singularHomologyFunctor A (n + 1)).obj R).map (TopCat.ofHom (incl φ)) ≫ wangδ φ R n = 0 := by
  rw [← map_fiberPairIncl_comp_fiberPairι, wangδ, Category.assoc,
    fiberPairι_comp_fiberPairπ_assoc, zero_comp, Limits.comp_zero]

/-- The Wang connecting morphism followed by `id - φ_*` vanishes. -/
@[reassoc]
lemma wangδ_comp_sub_monodromy (n : ℕ) :
    wangδ φ R n ≫ (𝟙 _ - ((singularHomologyFunctor A n).obj R).map
      (TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F)))) = 0 := by
  rw [← cancel_mono (((singularHomologyFunctor A n).obj R).map (fiberPairIncl φ)), zero_comp,
    Category.assoc, ← singularHomologyFiberPairIso_inv_comp_fiberPairδ, wangδ, Category.assoc,
    Iso.hom_inv_id_assoc, fiberPairπ_comp_fiberPairδ]

/-- The endomorphism `id - φ_*` followed by the fibre inclusion vanishes. -/
@[reassoc]
lemma sub_monodromy_comp_map_incl (n : ℕ) :
    (𝟙 _ - ((singularHomologyFunctor A n).obj R).map
        (TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F)))) ≫
      ((singularHomologyFunctor A n).obj R).map (TopCat.ofHom (incl φ)) = 0 := by
  rw [← map_fiberPairIncl_comp_fiberPairι, ← Category.assoc,
    ← singularHomologyFiberPairIso_inv_comp_fiberPairδ, Category.assoc,
    fiberPairδ_comp_fiberPairι, Limits.comp_zero]

/-- **Exactness of the Wang sequence at the target of `id - φ_*`**: the kernel of
`i_* : Hₙ(F) ⟶ Hₙ(T)` is the image of `id - φ_*`. -/
lemma wang_exact₁ (n : ℕ) : (ShortComplex.mk _ _ (sub_monodromy_comp_map_incl φ R n)).Exact := by
  have h : (ShortComplex.mk _ _ (fiberPairδ_comp_fiberPairι φ R n)).Exact :=
    (fiberPair φ).singularHomology_exact_subspace R (n + 1) n
  refine (ShortComplex.exact_iff_of_iso ?_).2 h
  refine ShortComplex.isoMk (singularHomologyFiberPairIso φ R n).symm
    (((singularHomologyFunctor A n).obj R).mapIso (asIso (fiberPairIncl φ))) (Iso.refl _) ?_ ?_
  · exact singularHomologyFiberPairIso_inv_comp_fiberPairδ φ R n
  · exact (map_fiberPairIncl_comp_fiberPairι φ R n).trans (Category.comp_id _).symm

/-- **Exactness of the Wang sequence at `Hₙ₊₁(T)`**: the kernel of the Wang connecting morphism
is the image of `i_* : Hₙ₊₁(F) ⟶ Hₙ₊₁(T)`. -/
lemma wang_exact₂ (n : ℕ) : (ShortComplex.mk _ _ (map_incl_comp_wangδ φ R n)).Exact := by
  have h : (ShortComplex.mk _ _ (fiberPairι_comp_fiberPairπ φ R (n + 1))).Exact :=
    (fiberPair φ).singularHomology_exact_space R (n + 1)
  refine (ShortComplex.exact_iff_of_iso ?_).2 h
  refine ShortComplex.isoMk
    (((singularHomologyFunctor A (n + 1)).obj R).mapIso (asIso (fiberPairIncl φ))) (Iso.refl _)
    (singularHomologyFiberPairIso φ R n).symm ?_ ?_
  · exact (map_fiberPairIncl_comp_fiberPairι φ R (n + 1)).trans
      (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (wangδ_comp_singularHomologyFiberPairIso_inv φ R n).symm

/-- **Exactness of the Wang sequence at the source of `id - φ_*`**: the kernel of `id - φ_*` on
`Hₙ(F)` is the image of the Wang connecting morphism. -/
lemma wang_exact₃ (n : ℕ) : (ShortComplex.mk _ _ (wangδ_comp_sub_monodromy φ R n)).Exact := by
  have h : (ShortComplex.mk _ _ (fiberPairπ_comp_fiberPairδ φ R n)).Exact :=
    (fiberPair φ).singularHomology_exact_relative R (n + 1) n
  refine (ShortComplex.exact_iff_of_iso ?_).2 h
  refine ShortComplex.isoMk (Iso.refl _) (singularHomologyFiberPairIso φ R n).symm
    (((singularHomologyFunctor A n).obj R).mapIso (asIso (fiberPairIncl φ))) ?_ ?_
  · exact (Category.id_comp _).trans (wangδ_comp_singularHomologyFiberPairIso_inv φ R n).symm
  · exact singularHomologyFiberPairIso_inv_comp_fiberPairδ φ R n

/-- The Wang sequence ends with an epimorphism `i_* : H₀(F) ⟶ H₀(T)`, because `H₀(T, F) = 0`. -/
lemma epi_map_incl_zero :
    Epi (((singularHomologyFunctor A 0).obj R).map (TopCat.ofHom (incl φ))) := by
  have h : (ShortComplex.mk _ _ (fiberPairι_comp_fiberPairπ φ R 0)).Exact :=
    (fiberPair φ).singularHomology_exact_space R 0
  have : Epi (fiberPairι φ R 0) :=
    h.epi_f ((isZero_singularHomology_fiberPair_zero φ R).eq_of_tgt _ _)
  rw [← map_fiberPairIncl_comp_fiberPairι]
  infer_instance

section Naturality

variable {G : Type w} [TopologicalSpace G] (ψ : G ≃ₜ G) (g : C(F, G))
  (h : Function.Semiconj g φ ψ)

include h in
/-- A map `g` intertwining the monodromies `φ` and `ψ` intertwines the endomorphisms `id - φ_*`
and `id - ψ_*` on homology. -/
@[reassoc]
lemma sub_monodromy_naturality (n : ℕ) :
    (𝟙 _ - ((singularHomologyFunctor A n).obj R).map
        (TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F)))) ≫
        ((singularHomologyFunctor A n).obj R).map (TopCat.ofHom g) =
      ((singularHomologyFunctor A n).obj R).map (TopCat.ofHom g) ≫
        (𝟙 _ - ((singularHomologyFunctor A n).obj R).map
          (TopCat.ofHom (⟨ψ, ψ.continuous⟩ : C(G, G)))) := by
  have hg : TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F)) ≫ TopCat.ofHom g =
      TopCat.ofHom g ≫ TopCat.ofHom (⟨ψ, ψ.continuous⟩ : C(G, G)) :=
    TopCat.ext h
  rw [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id,
    ← Functor.map_comp, ← Functor.map_comp, hg]

/-- **Naturality of the Wang connecting morphism** under a map `g` intertwining the
monodromies: `Hₙ₊₁(T_φ) ⟶ Hₙ₊₁(T_ψ) ⟶ Hₙ(G)` agrees with `Hₙ₊₁(T_φ) ⟶ Hₙ(F) ⟶ Hₙ(G)`. -/
@[reassoc]
theorem wangδ_naturality (n : ℕ) :
    ((singularHomologyFunctor A (n + 1)).obj R).map (TopCat.ofHom (map φ ψ g h)) ≫ wangδ ψ R n =
      wangδ φ R n ≫ ((singularHomologyFunctor A n).obj R).map (TopCat.ofHom g) := by
  have hπ : ((singularHomologyFunctor A (n + 1)).obj R).map (TopCat.ofHom (map φ ψ g h)) ≫
      fiberPairπ ψ R (n + 1) =
        fiberPairπ φ R (n + 1) ≫ TopPair.singularHomologyMap (fiberPairMap φ ψ g h) R (n + 1) := by
    rw [← fiberPairMap_fst]
    exact SSetPair.homologyπ_naturality (TopPair.toSSetPair.map (fiberPairMap φ ψ g h)) R (n + 1)
  rw [wangδ, wangδ, ← Category.assoc, hπ, Category.assoc,
    singularHomologyFiberPairIso_hom_naturality, Category.assoc]

end Naturality

end TauCeti.MappingTorus
