/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures
public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.Topology.Sets.Compacts

/-!
# Singular cohomology with compact supports

For a space `X`, the relative singular cohomology groups `Hⁿ(X, X ∖ K)` of the pairs given by the
complements of the compact subsets `K ⊆ X` form a diagram over the compact subsets ordered by
inclusion: for `K ⊆ L` the identity of `X` is a map of pairs `(X, X ∖ L) ⟶ (X, X ∖ K)`, inducing
`Hⁿ(X, X ∖ K) ⟶ Hⁿ(X, X ∖ L)`. Its colimit is the singular cohomology with compact supports
`Hⁿ_c(X) = colim_K Hⁿ(X, X ∖ K)` (`TopCat.compactSupportCohomology`). The compact subsets are
directed (the union of two compact sets is compact), so this is a filtered colimit of modules:
every class with compact support comes from some `Hⁿ(X, X ∖ K)`, and a class of `Hⁿ(X, X ∖ K)`
dies in `Hⁿ_c(X)` exactly when it dies in some `Hⁿ(X, X ∖ L)` with `K ⊆ L`.

This is the source of the duality map of an oriented manifold `M` of dimension `m`: capping with
the fundamental classes `μ_K ∈ Hₘ(M, M ∖ K)` of the compact subsets of `M` is compatible with the
maps of the diagram, so induces `Hⁿ_c(M) ⟶ H_{m-n}(M)`, which Poincaré duality asserts is an
isomorphism. For compact `X` the whole space is the largest compact subset, so `Hⁿ_c(X)` is the
ordinary singular cohomology `Hⁿ(X)` (`TopCat.compactSupportCohomologyIsoOfCompactSpace`).

A proper map `f : X ⟶ Y` pulls compact sets back to compact sets, and a class of `Hⁿ(Y, Y ∖ K)`
back to a class of `Hⁿ(X, X ∖ f⁻¹(K))`, so cohomology with compact supports is contravariant
along proper maps (`TopCat.compactSupportCohomologyMap`).

## Main definitions and results

* `TopCat.complCompactsPair`: the pairs `(X, X ∖ K)`, as a functor `Compacts X ⥤ TopPairᵒᵖ`.
* `TopCat.compactSupportCohomology`: singular cohomology with compact supports `Hⁿ_c(X)`, with
  the maps `TopCat.compactSupportCohomologyι : Hⁿ(X, X ∖ K) ⟶ Hⁿ_c(X)`, the extensionality lemma
  `TopCat.compactSupportCohomology_hom_ext` and the maps out of it
  `TopCat.compactSupportCohomologyDesc`.
* `TopCat.exists_compactSupportCohomologyι_eq` and `TopCat.compactSupportCohomologyι_eq_zero_iff`:
  the description of the elements of the filtered colimit.
* `TopCat.compactSupportCohomologyIsoOfCompactSpace`: `Hⁿ_c(X) ≅ Hⁿ(X)` for compact `X`.
* `TopCat.compactSupportCohomologyMap`: the pullback `f^* : Hⁿ_c(Y) ⟶ Hⁿ_c(X)` along a proper map,
  with `TopCat.compactSupportCohomologyMap_id` and `TopCat.compactSupportCohomologyMap_comp`.

## Implementation notes

The space `X : TopCat.{v}`, the coefficient category `C` (with `Category.{v} C`) and the ring
`k : Type v` share one universe: the compact subsets of `X` then index colimits that exist in
`ModuleCat.{v} k`, and the forgetful functor of `ModuleCat.{v} k` preserves them, which is what
the description of the elements uses.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, cohomology with compact supports as the direct limit of the groups `Hⁿ(X, X ∖ K)`,
  and the duality map `D_M : Hⁿ_c(M) ⟶ H_{m-n}(M)` of Theorem 3.35.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe v u

namespace TopCat

/-! ### The pairs `(X, X ∖ K)` -/

/-- For compact subsets `K ⊆ L` of `X`, the identity of `X` carries `X ∖ L` into `X ∖ K`. -/
lemma mapsTo_id_compl_compacts {X : TopCat.{v}} {K L : Compacts X} (h : K ≤ L) :
    Set.MapsTo (𝟙 X) (L : Set X)ᶜ (K : Set X)ᶜ := by
  simpa [Set.MapsTo] using fun _ hx hK ↦ hx (h hK)

/-- The pairs `(X, X ∖ K)` for the compact subsets `K` of a space `X`, as a functor
`Compacts X ⥤ TopPairᵒᵖ`: enlarging `K` shrinks `X ∖ K`, and the identity of `X` is a map of
pairs `(X, X ∖ L) ⟶ (X, X ∖ K)` for `K ⊆ L`. -/
@[expose, simps]
def complCompactsPair (X : TopCat.{v}) : Compacts X ⥤ TopPair.{v}ᵒᵖ where
  obj K := op (TopPair.ofSubset (K : Set X)ᶜ)
  map h := (TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl_compacts h.le)).op
  map_id _ := Quiver.Hom.unop_inj (TopPair.ofSubsetMap_id _)
  map_comp _ _ := Quiver.Hom.unop_inj
    (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (Category.id_comp _)).symm

/-- A proper map `f : X ⟶ Y` carries `X ∖ f⁻¹(K)` into `Y ∖ K`, for every compact `K ⊆ Y`. -/
lemma mapsTo_compl_compacts_comap {X Y : TopCat.{v}} (f : X ⟶ Y) (hf : IsProperMap f)
    (K : Compacts Y) :
    Set.MapsTo f (Compacts.comap f hf K : Set X)ᶜ (K : Set Y)ᶜ :=
  fun _ hx hK ↦ hx (by simpa using hK)

variable {C : Type u} [Category.{v} C] [HasCoproducts.{v} C] [Abelian C] (X : TopCat.{v}) (R : C)
  (k : Type v) [Ring k] [Linear k C] (M : C)

/-! ### Definition -/

/-- The diagram `K ↦ Hⁿ(X, X ∖ K)` of relative singular cohomology groups over the compact subsets
of `X`, along the maps induced by the identity of `X`. -/
abbrev compactSupportCohomologyDiagram (n : ℕ) : Compacts X ⥤ ModuleCat.{v} k :=
  X.complCompactsPair ⋙ TopPair.singularCohomologyFunctor R k M n

/-- **Singular cohomology with compact supports**, `Hⁿ_c(X) = colim_K Hⁿ(X, X ∖ K)`, the colimit
of the relative singular cohomology groups `Hⁿ(X, X ∖ K)` over the compact subsets `K` of `X`,
directed by inclusion. -/
def compactSupportCohomology (n : ℕ) : ModuleCat.{v} k :=
  colimit (X.compactSupportCohomologyDiagram R k M n)

variable {X R k M}

/-- The map `Hⁿ(X, X ∖ K) ⟶ Hⁿ_c(X)` into singular cohomology with compact supports: a relative
class vanishing on chains outside the compact set `K` is a class with compact support. -/
def compactSupportCohomologyι (n : ℕ) (K : Compacts X) :
    (TopPair.ofSubset (K : Set X)ᶜ).singularCohomology R k M n ⟶
      X.compactSupportCohomology R k M n :=
  colimit.ι (X.compactSupportCohomologyDiagram R k M n) K

private lemma compactSupportCohomologyι_def (n : ℕ) (K : Compacts X) :
    compactSupportCohomologyι (R := R) (k := k) (M := M) n K =
      colimit.ι (X.compactSupportCohomologyDiagram R k M n) K :=
  (rfl)

/-- The maps into cohomology with compact supports are compatible with enlarging the support. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma singularCohomologyMap_comp_compactSupportCohomologyι (n : ℕ) {K L : Compacts X}
    (h : K ≤ L) :
    TopPair.singularCohomologyMap (TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl_compacts h)) n ≫
        compactSupportCohomologyι (R := R) (k := k) (M := M) n L =
      compactSupportCohomologyι n K :=
  colimit.w (X.compactSupportCohomologyDiagram R k M n) (homOfLE h)

/-- Restricting from `X ∖ K` to `X ∖ L` and then to `X ∖ N` is the restriction from `X ∖ K` to
`X ∖ N`. -/
@[reassoc]
lemma singularCohomologyMap_ofSubsetMap_id_trans {K L N : Compacts X} (h₁ : K ≤ L) (h₂ : L ≤ N)
    (n : ℕ) :
    TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
        (TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl_compacts h₁)) n ≫
      TopPair.singularCohomologyMap (TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl_compacts h₂)) n =
    TopPair.singularCohomologyMap
      (TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl_compacts (h₁.trans h₂))) n :=
  ((X.compactSupportCohomologyDiagram R k M n).map_comp (homOfLE h₁) (homOfLE h₂)).symm

/-- Two maps out of cohomology with compact supports agree if they agree on each `Hⁿ(X, X ∖ K)`. -/
@[ext]
lemma compactSupportCohomology_hom_ext {n : ℕ} {N : ModuleCat.{v} k}
    {f g : X.compactSupportCohomology R k M n ⟶ N}
    (h : ∀ K, compactSupportCohomologyι n K ≫ f = compactSupportCohomologyι n K ≫ g) : f = g :=
  colimit.hom_ext h

/-- A map out of cohomology with compact supports, from maps out of the groups `Hⁿ(X, X ∖ K)`
that are compatible with enlarging `K`. -/
def compactSupportCohomologyDesc {n : ℕ} {N : ModuleCat.{v} k}
    (f : ∀ K : Compacts X, (TopPair.ofSubset (K : Set X)ᶜ).singularCohomology R k M n ⟶ N)
    (hf : ∀ (K L : Compacts X) (h : K ≤ L),
      TopPair.singularCohomologyMap (TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl_compacts h)) n ≫
        f L = f K) :
    X.compactSupportCohomology R k M n ⟶ N :=
  colimit.desc (X.compactSupportCohomologyDiagram R k M n)
    { pt := N
      ι := { app := f
             naturality := fun K L h ↦ (hf K L h.le).trans (Category.comp_id (f K)).symm } }

@[reassoc (attr := simp)]
lemma compactSupportCohomologyι_desc {n : ℕ} {N : ModuleCat.{v} k}
    (f : ∀ K : Compacts X, (TopPair.ofSubset (K : Set X)ᶜ).singularCohomology R k M n ⟶ N)
    (hf : ∀ (K L : Compacts X) (h : K ≤ L),
      TopPair.singularCohomologyMap (TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl_compacts h)) n ≫
        f L = f K) (K : Compacts X) :
    compactSupportCohomologyι n K ≫ compactSupportCohomologyDesc f hf = f K :=
  colimit.ι_desc _ K

/-! ### Elements -/

/-- Every class with compact support comes from `Hⁿ(X, X ∖ K)` for some compact `K` containing a
given compact set. -/
lemma exists_compactSupportCohomologyι_eq {n : ℕ} (x : X.compactSupportCohomology R k M n)
    (K₀ : Compacts X) :
    ∃ (K : Compacts X) (_ : K₀ ≤ K)
      (y : (TopPair.ofSubset (K : Set X)ᶜ).singularCohomology R k M n),
        compactSupportCohomologyι n K y = x := by
  obtain ⟨K, h, y, hy⟩ := Concrete.exists_hom_ι_eq_of_isColimit _ (colimit.isColimit _) x K₀
  exact ⟨K, h.le, y, by rw [compactSupportCohomologyι_def]; exact hy⟩

/-- A class of `Hⁿ(X, X ∖ K)` has zero image with compact supports exactly when it restricts to
zero in `Hⁿ(X, X ∖ L)` for some compact `L ⊇ K`. -/
lemma compactSupportCohomologyι_eq_zero_iff {n : ℕ} {K : Compacts X}
    (y : (TopPair.ofSubset (K : Set X)ᶜ).singularCohomology R k M n) :
    compactSupportCohomologyι n K y = 0 ↔ ∃ (L : Compacts X) (h : K ≤ L),
      TopPair.singularCohomologyMap (TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl_compacts h)) n y =
        0 := by
  constructor
  · intro hy
    rw [compactSupportCohomologyι_def] at hy
    obtain ⟨L, i, hL⟩ := Concrete.colimit_rep_eq_zero k
      (X.compactSupportCohomologyDiagram R k M n) K y hy
    exact ⟨L, i.le, hL⟩
  · rintro ⟨L, h, hL⟩
    rw [← singularCohomologyMap_comp_compactSupportCohomologyι_apply n h, hL, map_zero]

/-! ### Compact spaces -/

/-- For a compact space `X`, the map `Hⁿ(X, ∅) ⟶ Hⁿ_c(X)` from the cohomology relative to the
complement of the largest compact set is an isomorphism. -/
instance isIso_compactSupportCohomologyι_top [CompactSpace X] (n : ℕ) :
    IsIso (compactSupportCohomologyι (R := R) (k := k) (M := M) (X := X) n ⊤) :=
  isIso_ι_of_isTerminal isTerminalTop _

/-- In a compact space, the complement of the largest compact set is empty. -/
instance isEmpty_complCompactsPair_top_snd [CompactSpace X] :
    IsEmpty ((TopPair.ofSubset ((⊤ : Compacts X) : Set X)ᶜ).snd) :=
  Set.isEmpty_coe_sort.2 (by simp)

/-- For a compact space, singular cohomology with compact supports is singular cohomology:
`Hⁿ_c(X) ≅ Hⁿ(X, ∅) ≅ Hⁿ(X)`. -/
def compactSupportCohomologyIsoOfCompactSpace [CompactSpace X] (n : ℕ) :
    X.compactSupportCohomology R k M n ≅ X.singularCohomology R k M n :=
  (asIso (compactSupportCohomologyι n ⊤)).symm ≪≫
    @asIso _ _ _ _ ((TopPair.ofSubset ((⊤ : Compacts X) : Set X)ᶜ).singularCohomologyπ R k M n)
      (TopPair.isIso_singularCohomologyπ_of_isEmpty _ R k M n)

@[reassoc (attr := simp)]
lemma compactSupportCohomologyι_compactSupportCohomologyIsoOfCompactSpace_hom [CompactSpace X]
    (n : ℕ) :
    compactSupportCohomologyι n ⊤ ≫ (compactSupportCohomologyIsoOfCompactSpace n).hom =
      (TopPair.ofSubset ((⊤ : Compacts X) : Set X)ᶜ).singularCohomologyπ R k M n := by
  simp only [compactSupportCohomologyIsoOfCompactSpace, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    IsIso.hom_inv_id_assoc]
  -- `asIso_hom` does not fire here: the definition supplies the `IsIso` instance explicitly,
  -- because the target of `singularCohomologyπ` is the cohomology of `(TopPair.ofSubset _).fst`,
  -- which is `X` only after unfolding, so instance search does not find it.
  rfl

/-! ### Pullback along proper maps -/

variable {Y Z : TopCat.{v}}

/-- The pullback `f^* : Hⁿ_c(Y) ⟶ Hⁿ_c(X)` along a proper map `f : X ⟶ Y`: a class of
`Hⁿ(Y, Y ∖ K)` pulls back to a class of `Hⁿ(X, X ∖ f⁻¹(K))`, and `f⁻¹(K)` is compact. -/
def compactSupportCohomologyMap (f : X ⟶ Y) (hf : IsProperMap f) (n : ℕ) :
    Y.compactSupportCohomology R k M n ⟶ X.compactSupportCohomology R k M n :=
  compactSupportCohomologyDesc
    (fun K ↦ TopPair.singularCohomologyMap
      (TopPair.ofSubsetMap f (mapsTo_compl_compacts_comap f hf K)) n ≫
        compactSupportCohomologyι n (Compacts.comap f hf K))
    (fun K L h ↦ by
      rw [← TopPair.singularCohomologyMap_comp_assoc,
        TopPair.ofSubsetMap_comp_ofSubsetMap_eq (mapsTo_compl_compacts_comap f hf L)
          (mapsTo_id_compl_compacts h)
          (mapsTo_id_compl_compacts (K := Compacts.comap f hf K) (L := Compacts.comap f hf L)
            (Compacts.comap_mono f hf h))
          (mapsTo_compl_compacts_comap f hf K) (by simp),
        TopPair.singularCohomologyMap_comp_assoc,
        singularCohomologyMap_comp_compactSupportCohomologyι n (Compacts.comap_mono f hf h)])

@[reassoc (attr := simp)]
lemma compactSupportCohomologyι_compactSupportCohomologyMap (f : X ⟶ Y) (hf : IsProperMap f)
    (n : ℕ) (K : Compacts Y) :
    compactSupportCohomologyι n K ≫ compactSupportCohomologyMap (R := R) (k := k) (M := M) f hf n =
      TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap f (mapsTo_compl_compacts_comap f hf K)) n ≫
          compactSupportCohomologyι n (Compacts.comap f hf K) :=
  compactSupportCohomologyι_desc _ _ K

/-- The pullback along the identity is the identity. -/
@[simp]
lemma compactSupportCohomologyMap_id (n : ℕ)
    (h : IsProperMap (𝟙 X) := by simpa using isProperMap_id) :
    compactSupportCohomologyMap (R := R) (k := k) (M := M) (𝟙 X) h n = 𝟙 _ := by
  refine compactSupportCohomology_hom_ext fun K ↦ ?_
  rw [compactSupportCohomologyι_compactSupportCohomologyMap, Category.comp_id]
  exact singularCohomologyMap_comp_compactSupportCohomologyι n (K := K)
    (L := Compacts.comap (𝟙 X) h K) fun x hx ↦ by simpa using hx

/-- Pullback along proper maps is contravariantly functorial: `(g ∘ f)^* = f^* ∘ g^*`. -/
@[reassoc]
lemma compactSupportCohomologyMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsProperMap f)
    (hg : IsProperMap g) (n : ℕ) :
    compactSupportCohomologyMap (R := R) (k := k) (M := M) (f ≫ g) (hg.comp hf) n =
      compactSupportCohomologyMap g hg n ≫ compactSupportCohomologyMap f hf n := by
  refine compactSupportCohomology_hom_ext fun K ↦ ?_
  have hle : Compacts.comap (f ≫ g) (hg.comp hf) K ≤
      Compacts.comap f hf (Compacts.comap g hg K) := fun x hx ↦ by simpa using hx
  rw [compactSupportCohomologyι_compactSupportCohomologyMap,
    compactSupportCohomologyι_compactSupportCohomologyMap_assoc,
    compactSupportCohomologyι_compactSupportCohomologyMap,
    ← singularCohomologyMap_comp_compactSupportCohomologyι n hle,
    ← TopPair.singularCohomologyMap_comp_assoc, ← TopPair.singularCohomologyMap_comp_assoc,
    TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ (mapsTo_compl_compacts_comap f hf _)
      (mapsTo_compl_compacts_comap g hg K) (by simp)]

end TopCat
