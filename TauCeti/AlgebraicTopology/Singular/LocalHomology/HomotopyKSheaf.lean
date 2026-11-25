/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.MapExtend
public import TauCeti.Algebra.Homology.HomotopyCategory.ShortExact
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Chains
public import TauCeti.Topology.Sheaves.KSheaf.Homotopy

/-!
# Relative singular chains as a homotopy K-sheaf

Let `X` be a Hausdorff space and `Z` a monotone assignment of a subset `Z K` of a space `M` to
each compact subset `K` of `X`. For an integer `p`, the K-presheaf of cochain complexes
`K ↦ C_(p - •)(M, M ∖ Z K)` (`TauCeti.localChainKPresheaf`) places the relative singular chains
`C_n(M, M ∖ Z K)` in cochain degree `p - n`, through Mathlib's embedding
`ComplexShape.embeddingUpIntLE p`, and restricts along the maps induced by the identity of `M`.

This file proves that it is a homotopy K-sheaf (`TopCat.KPresheaf.IsHomotopyKSheaf`, Pardon,
Definition A.2.5) when `Z` takes `⊥` to `∅`, unions to unions and intersections to intersections,
its values are closed, and a compact subset of `M` disjoint from `Z K` is disjoint from `Z L` for
some compact neighbourhood `L` of `K` (`TauCeti.isHomotopyKSheaf_localChainKPresheaf`). The three
axioms are the chain-level properties of relative singular chains along closed sets (Pardon,
Lemma A.6.3), proved in `TauCeti.AlgebraicTopology.Singular.LocalHomology.Chains`:

* the chains along `Z ⊥ = ∅` vanish (`TauCeti.acyclic_localChainKPresheaf_obj_bot`);
* the Mayer–Vietoris map `mappingCone φ ⟶ F(K₂ ∩ K₃)` is a quasi-isomorphism
  (`TauCeti.quasiIso_localChainKPresheaf_mayerVietorisDesc`): the Mayer–Vietoris sequence of
  relative chains along the closed sets `Z K₂` and `Z K₃` is short exact up to a quasi-isomorphism,
  and the mapping cone of the monomorphism of a short exact sequence maps quasi-isomorphically to
  its cokernel (`CochainComplex.mappingCone.quasiIso_desc_of_shortExact`);
* `F(K)` is the colimit of the `F(L)` over the compact neighbourhoods `L` of `K`
  (`TauCeti.localChainKPresheaf.isColimitCoconeOfCompacts`), already as complexes, since a
  singular simplex of `M ∖ Z K` has compact image.

For `M = X` and `Z K = K`, on a locally compact Hausdorff space, this is the homotopy K-sheaf
`K ↦ C_(p - •)(X, X ∖ K)` (`TauCeti.isHomotopyKSheaf_localChainKPresheaf_coe`), whose cohomology
in degree `p - n` is the local homology `Hₙ(X, X ∖ K)` (Mathlib's
`HomologicalComplex.extendHomologyIso`). A general `Z` covers relative chains supported along
preimages: in Pardon's construction of virtual fundamental cycles, the partial virtual complexes
of an implicit atlas are built from relative chains `C(D, D ∖ Z_K)` on a deformation space `D`,
along the closed sets `Z_K ⊆ D` lying over the compact sets `K` of the base, and their homotopy
K-sheaf property is the input to the comparison of virtual and Čech cohomology.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Definition A.2.5 (homotopy
  K-sheaves) and Lemma A.6.3 (relative singular chains).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Set TopologicalSpace HomologicalComplex CochainComplex

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {X : TopCat.{w}} {M : Type w} [TopologicalSpace M]

-- The body is exposed so that the values are definitionally the extended chain complexes: the
-- statement of `localChainKPresheaf_map`, a map between values, typechecks only then.
/-- The K-presheaf of relative singular chains `K ↦ C_(p - •)(M, M ∖ Z K)` along a monotone
assignment `Z` of subsets of `M` to the compact subsets of `X`: the chains `C_n(M, M ∖ Z K)` sit in
cochain degree `p - n`, and the restriction maps are induced by the identity of `M`. -/
@[expose]
def localChainKPresheaf (Z : Compacts X →o Set M) (p : ℤ) :
    TopCat.KPresheaf (CochainComplex A ℤ) X where
  obj K := (localChainComplex R (Z K.unop)).extend (ComplexShape.embeddingUpIntLE p)
  map h := extendMap (localChainRestriction R (Z.monotone (leOfHom h.unop))) _
  map_id _ := by rw [localChainRestriction_refl, extendMap_id]
  map_comp _ _ := by rw [← extendMap_comp, localChainRestriction_comp]

variable (Z : Compacts X →o Set M) (p : ℤ)

@[simp]
lemma localChainKPresheaf_obj (K : (Compacts X)ᵒᵖ) :
    (localChainKPresheaf R Z p).obj K =
      (localChainComplex R (Z K.unop)).extend (ComplexShape.embeddingUpIntLE p) :=
  (rfl)

@[simp]
lemma localChainKPresheaf_map {K L : (Compacts X)ᵒᵖ} (h : K ⟶ L) :
    (localChainKPresheaf R Z p).map h =
      extendMap (localChainRestriction R (Z.monotone (leOfHom h.unop))) _ :=
  (rfl)

/-- **The empty-set axiom.** If `Z ⊥ = ∅`, the chains `C(M, M ∖ Z ⊥) = C(M, M)` vanish. -/
theorem acyclic_localChainKPresheaf_obj_bot (hZ : Z ⊥ = ∅) :
    ((localChainKPresheaf R Z p).obj (op ⊥)).Acyclic :=
  acyclic_of_isZero _ <| ((ComplexShape.embeddingUpIntLE p).extendFunctor A).map_isZero
    (hZ ▸ isZero_localChainComplex_empty R)

variable [T2Space X]

/-- **The Mayer–Vietoris axiom.** Let `K₁ = K₂ ⊓ K₃` and `K₄ = K₂ ⊔ K₃` for compact sets, and
suppose `Z K₂` and `Z K₃` are closed, `Z K₄ ⊆ Z K₂ ∪ Z K₃` and `Z K₂ ∩ Z K₃ ⊆ Z K₁`. Then the map
`mappingCone φ ⟶ F(K₁)` of the Mayer–Vietoris sequence
`F(K₄) ⟶ F(K₂) ⊞ F(K₃) ⟶ F(K₁)` of `F = localChainKPresheaf R Z p` is a quasi-isomorphism. -/
theorem quasiIso_localChainKPresheaf_mayerVietorisDesc {K₁ K₂ K₃ K₄ : Compacts X}
    (h : Lattice.BicartSq K₁ K₂ K₃ K₄) (h₂ : IsClosed (Z K₂)) (h₃ : IsClosed (Z K₃))
    (h₄ : Z K₄ ⊆ Z K₂ ∪ Z K₃) (h₁ : Z K₂ ∩ Z K₃ ⊆ Z K₁) :
    QuasiIso ((localChainKPresheaf R Z p).mayerVietorisDesc h) := by
  -- the Mayer–Vietoris sequence `C₄ ⟶ C₂ ⊞ C₃ ⟶ C₁` of chains along `Z K₂` and `Z K₃`: its first
  -- map is a monomorphism, and the second map is a quasi-isomorphism from its cokernel
  have hc : ∀ {K L : Compacts X}, K ≤ L → (Z L)ᶜ ⊆ (Z K)ᶜ :=
    fun h ↦ compl_subset_compl.2 (Z.monotone h)
  have hW : (Z K₂)ᶜ ∩ (Z K₃)ᶜ ⊆ (Z K₄)ᶜ := by
    rw [← compl_union]
    exact compl_subset_compl.2 h₄
  have hZ : (Z K₁)ᶜ ⊆ (Z K₂)ᶜ ∪ (Z K₃)ᶜ := by
    rw [← compl_inter]
    exact compl_subset_compl.2 h₁
  have hab := TopCat.relativeMayerVietorisChainToBiprod_fromBiprod R (X := TopCat.of M)
    (hc h.le₂₄) (hc h.le₃₄) (hc h.le₁₂) (hc h.le₁₃)
  have := TopCat.mono_relativeMayerVietorisChainToBiprod R (X := TopCat.of M) (U := (Z K₂)ᶜ)
    (V := (Z K₃)ᶜ) (W := (Z K₄)ᶜ) (hc h.le₂₄) (hc h.le₃₄) hW
  have := TopCat.quasiIso_cokernelDesc_relativeMayerVietorisChainFromBiprod R (X := TopCat.of M)
    (U := (Z K₂)ᶜ) (V := (Z K₃)ᶜ) (W := (Z K₄)ᶜ) (Z := (Z K₁)ᶜ) h₂.isOpen_compl
    h₃.isOpen_compl (hc h.le₂₄) (hc h.le₃₄) (hc h.le₁₂) (hc h.le₁₃) hW hZ
  rw [TopCat.KPresheaf.mayerVietorisDesc_eq_desc]
  exact mappingCone.quasiIso_desc_extendMap_of_quasiIso_cokernelDesc _ hab
    (by rw [localChainRestriction_def, localChainRestriction_def])
    (by rw [localChainRestriction_def, localChainRestriction_def]) _

/-- **The continuity axiom.** Suppose every compact subset of `M` disjoint from `Z K` is disjoint
from `Z L` for some compact neighbourhood `L` of `K`. Then the relative chains
`C_(p - •)(M, M ∖ Z K)` are the colimit of the complexes `C_(p - •)(M, M ∖ Z L)` over the compact
neighbourhoods `L` of `K`, through the restriction maps. -/
def localChainKPresheaf.isColimitCoconeOfCompacts (K : Compacts X)
    (hK : ∀ T : Set M, IsCompact T → Disjoint T (Z K) → ∃ L ∈ K.compactNhds, Disjoint T (Z L)) :
    IsColimit ((localChainKPresheaf R Z p).coconeOfCompacts K) := by
  -- `K` has a compact neighbourhood, as the empty set is disjoint from `Z K`
  have : Nonempty K.compactNhds :=
    let ⟨L, hL, _⟩ := hK ∅ isCompact_empty (empty_disjoint _)
    ⟨⟨L, hL⟩⟩
  have : HasColimitsOfSize.{w, w} A := has_colimits_of_hasCoequalizers_and_coproducts
  have hL : ∀ ⦃L L' : (K.compactNhds)ᵒᵖ⦄, (L ⟶ L') → Z L'.unop.val ⊆ Z L.unop.val :=
    fun _ _ h ↦ Z.monotone (leOfHom h.unop)
  -- relative chains along `Z K` are the colimit of those along the `Z L`, already as complexes
  have hc := isColimitOfPreserves ((ComplexShape.embeddingUpIntLE p).extendFunctor A)
    (isColimitMapCoconeSingularChainComplexComplPairCocone R hL
      (fun L ↦ Z.monotone (Compacts.subset_of_mem_compactNhds L.unop.property))
      fun T hT hTK ↦
        let ⟨L, hLK, hLT⟩ := hK T hT hTK
        ⟨op ⟨L, hLK⟩, hLT⟩)
  -- `TopPair.singularChainComplexFunctor` is a `def`; rewriting it through `toSSetPair` exposes
  -- the values `((SSetPair.chainComplexFunctor A).obj R).obj (toSSetPair.obj _)` of `hc`
  rw [TopPair.singularChainComplexFunctor_obj_eq_toSSetPair_comp] at hc
  -- the diagram and the cocone of `hc` are those of the K-presheaf: the components below are
  -- `Iso.refl`, because `localChainComplex R S` unfolds, through the `abbrev`s
  -- `localChainComplex`, `TopPair.singularChainComplex` and `SSetPair.chainComplex`, to
  -- `((SSetPair.chainComplexFunctor A).obj R).obj (toSSetPair.obj (TopPair.ofSubset Sᶜ))`, already
  -- at reducible transparency; only the maps need `localChainRestriction_def`, through `hR`
  have hR : ∀ {S T : Set M} (h : S ⊆ T), extendMap (TopPair.singularChainComplexMap
      (TopPair.ofSubsetMap (𝟙 (TopCat.of M)) (compl_subset_compl.2 h)) R) _ =
        extendMap (localChainRestriction R h) (ComplexShape.embeddingUpIntLE p) :=
    fun h ↦ congrArg (extendMap · _) (localChainRestriction_def R h).symm
  let α : (complPairDiagram hL ⋙ TopPair.toSSetPair ⋙ (SSetPair.chainComplexFunctor A).obj R) ⋙
      (ComplexShape.embeddingUpIntLE p).extendFunctor A ≅
        (Set.mono_coe K.compactNhds).functor.op ⋙ localChainKPresheaf R Z p :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) fun h ↦
      (Category.comp_id _).trans ((hR (hL h)).trans (Category.id_comp _).symm)
  exact IsColimit.precomposeHomEquiv α _ (hc.ofIsoColimit (Cocone.ext (Iso.refl _) fun L ↦
    (Category.comp_id _).trans ((hR (Z.monotone (Compacts.subset_of_mem_compactNhds
      L.unop.property))).trans (Category.id_comp _).symm)))

/-- **Relative singular chains form a homotopy K-sheaf** (Pardon, Lemma A.6.3). Let `Z` assign to
each compact subset `K` of a Hausdorff space `X` a closed subset `Z K` of `M`, monotonically, with
`Z ⊥ = ∅`, `Z (K ⊔ L) ⊆ Z K ∪ Z L` and `Z K ∩ Z L ⊆ Z (K ⊓ L)` (so that `Z` preserves `⊔` and
`⊓`), such that every compact subset of `M` disjoint from `Z K` is disjoint from `Z L` for some
compact neighbourhood `L` of `K`. Then `K ↦ C_(p - •)(M, M ∖ Z K)` is a homotopy K-sheaf. -/
theorem isHomotopyKSheaf_localChainKPresheaf (hbot : Z ⊥ = ∅)
    (hsup : ∀ K L, Z (K ⊔ L) ⊆ Z K ∪ Z L) (hinf : ∀ K L, Z K ∩ Z L ⊆ Z (K ⊓ L))
    (hclosed : ∀ K, IsClosed (Z K))
    (hnhds : ∀ (K : Compacts X) (T : Set M), IsCompact T → Disjoint T (Z K) →
      ∃ L ∈ K.compactNhds, Disjoint T (Z L)) :
    (localChainKPresheaf R Z p).IsHomotopyKSheaf where
  acyclic_bot := acyclic_localChainKPresheaf_obj_bot R Z p hbot
  quasiIso_mayerVietorisDesc h :=
    quasiIso_localChainKPresheaf_mayerVietorisDesc R Z p h (hclosed _) (hclosed _)
      (h.sup_eq ▸ hsup _ _) (h.inf_eq ▸ hinf _ _)
  exists_isColimit_quasiIso_desc K :=
    ⟨_, localChainKPresheaf.isColimitCoconeOfCompacts R Z p K (hnhds K), by
      rw [IsColimit.desc_self]
      infer_instance⟩

/-- **Local chains form a homotopy K-sheaf.** On a locally compact Hausdorff space `M`, the relative
singular chains `K ↦ C_(p - •)(M, M ∖ K)` on the compact subsets of `M` form a homotopy K-sheaf. -/
theorem isHomotopyKSheaf_localChainKPresheaf_coe [T2Space M] [LocallyCompactSpace M] :
    (localChainKPresheaf R (X := TopCat.of M) ⟨fun K ↦ (K : Set M), fun _ _ ↦ id⟩ p
      ).IsHomotopyKSheaf :=
  isHomotopyKSheaf_localChainKPresheaf R _ p rfl (fun _ _ ↦ subset_rfl) (fun _ _ ↦ subset_rfl)
    (fun K ↦ K.isCompact.isClosed) fun K _ hT hTK ↦
      let ⟨L, hL, hLT⟩ := K.exists_mem_compactNhds_disjoint hT.isClosed hTK.symm
      ⟨L, hL, hLT.symm⟩

end TauCeti
