/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.CommSq
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import TauCeti.Algebra.Homology.ShortComplex.Colimit
public import TauCeti.Topology.Sheaves.KSheaf.Basic

/-!
# Homotopy K-sheaves

A *homotopy K-sheaf* (Pardon, Definition A.2.5) is a K-presheaf `F` of cochain complexes on a
Hausdorff space `X` which satisfies the K-sheaf axioms up to quasi-isomorphism:

* `F(∅)` is acyclic;
* for compact sets `K₂` and `K₃`, the total complex of the three-term sequence
  `F(K₂ ∪ K₃) ⟶ F(K₂) ⊞ F(K₃) ⟶ F(K₂ ∩ K₃)`, whose maps are the restrictions and the
  difference of the restrictions, is acyclic;
* for a compact set `K`, the map to `F(K)` from a colimit of the `F(K')` over the compact
  neighbourhoods `K'` of `K` is a quasi-isomorphism.

The second axiom is stated as follows. Write `φ : F(K₂ ∪ K₃) ⟶ F(K₂) ⊞ F(K₃)` and
`ψ : F(K₂) ⊞ F(K₃) ⟶ F(K₂ ∩ K₃)` for the two maps; since `φ ≫ ψ = 0`, the map `ψ` extends by
zero to a map `mappingCone φ ⟶ F(K₂ ∩ K₃)` (`TopCat.KPresheaf.mayerVietorisDesc`). Its mapping
cone is, in degree `n`, `F(K₂ ∪ K₃)ⁿ⁺² ⊕ (F(K₂) ⊞ F(K₃))ⁿ⁺¹ ⊕ F(K₂ ∩ K₃)ⁿ`, the total complex
of the three-term sequence up to a shift and the signs of the differential. A morphism of cochain
complexes in an abelian category is a quasi-isomorphism exactly when its mapping cone is acyclic,
so the total complex is acyclic exactly when this map is a quasi-isomorphism, which is the form
of the axiom used here.

In Pardon's construction of virtual fundamental cycles, the virtual cochain complexes of implicit
atlases are homotopy K-sheaves, and their cohomology is related to sheaf cohomology through the
lowest cohomology, which is an honest K-sheaf. This file proves the latter (Pardon,
Lemma A.2.12): if the cohomology of every `F(K)` vanishes in degree `i`, then
`K ↦ H^(i + 1)(F(K))` is a K-sheaf. The pullback axiom comes from the long exact cohomology
sequence of the mapping cone of `φ`, and the colimit axiom from the exactness of filtered colimits,
which makes cohomology commute with them; the latter needs `X` to be weakly locally compact, so
that every compact set has a compact neighbourhood.

## Main definitions

* `TopCat.KPresheaf.mayerVietorisDesc`: the map from the mapping cone of
  `F(K₂ ∪ K₃) ⟶ F(K₂) ⊞ F(K₃)` to `F(K₂ ∩ K₃)`.
* `TopCat.KPresheaf.IsHomotopyKSheaf`: the homotopy K-sheaf condition.

## Main results

* `TopCat.KPresheaf.IsHomotopyKSheaf.quasiIso_desc`: in a homotopy K-sheaf, the map to `F(K)`
  from any colimit over the compact neighbourhoods of `K` is a quasi-isomorphism.
* `TopCat.KPresheaf.isPullback_homologyMap`: where `mayerVietorisDesc` is a quasi-isomorphism,
  the cohomology squares are pullbacks in the degree above a degree where `F(K₂ ∩ K₃)` has no
  cohomology.
* `TopCat.KPresheaf.nonempty_isColimit_coconeOfCompacts_homology`: the colimit axiom passes to
  cohomology.
* `TopCat.KPresheaf.IsHomotopyKSheaf.isKSheaf_homology`: the cohomology of a homotopy K-sheaf in
  the degree above a degree where it vanishes is a K-sheaf.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Appendix A.2, Definition A.2.5 and
  Lemma A.2.12.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace HomologicalComplex CochainComplex

universe w v u

namespace TopCat.KPresheaf

variable {X : TopCat.{w}} [T2Space X]

variable {C : Type u} [Category.{v} C] [Abelian C] (F : KPresheaf (CochainComplex C ℤ) X)

/-- For a bicartesian square `K₁ = K₂ ⊓ K₃`, `K₄ = K₂ ⊔ K₃` of compact sets, the map
`mappingCone φ ⟶ F(K₁)` extending the difference `ψ : F(K₂) ⊞ F(K₃) ⟶ F(K₁)` of the restrictions
by zero, where `φ : F(K₄) ⟶ F(K₂) ⊞ F(K₃)` is the pair of restrictions. Its mapping cone is the
total complex of the Mayer–Vietoris sequence `F(K₄) ⟶ F(K₂) ⊞ F(K₃) ⟶ F(K₁)`, up to a shift. -/
noncomputable def mayerVietorisDesc {K₁ K₂ K₃ K₄ : Compacts X}
    (h : Lattice.BicartSq K₁ K₂ K₃ K₄) :
    mappingCone (biprod.lift (F.map (opHomOfLE h.le₂₄)) (F.map (opHomOfLE h.le₃₄))) ⟶
      F.obj (op K₁) :=
  mappingCone.desc _ 0 (biprod.desc (F.map (opHomOfLE h.le₁₂)) (-F.map (opHomOfLE h.le₁₃)))
    (by simp [(F.commSq_map h).w])

theorem mayerVietorisDesc_eq_desc {K₁ K₂ K₃ K₄ : Compacts X} (h : Lattice.BicartSq K₁ K₂ K₃ K₄) :
    F.mayerVietorisDesc h =
      mappingCone.desc _ 0 (biprod.desc (F.map (opHomOfLE h.le₁₂)) (-F.map (opHomOfLE h.le₁₃)))
        (by simp [(F.commSq_map h).w]) :=
  (rfl)

@[reassoc (attr := simp)]
theorem inl_v_mayerVietorisDesc_f {K₁ K₂ K₃ K₄ : Compacts X} (h : Lattice.BicartSq K₁ K₂ K₃ K₄)
    (p q : ℤ) (hpq : p + (-1) = q) :
    (mappingCone.inl _).v p q hpq ≫ (F.mayerVietorisDesc h).f q = 0 := by
  simp [mayerVietorisDesc_eq_desc]

@[reassoc (attr := simp)]
theorem inr_f_mayerVietorisDesc_f {K₁ K₂ K₃ K₄ : Compacts X} (h : Lattice.BicartSq K₁ K₂ K₃ K₄)
    (p : ℤ) :
    (mappingCone.inr _).f p ≫ (F.mayerVietorisDesc h).f p =
      (biprod.desc (F.map (opHomOfLE h.le₁₂)) (-F.map (opHomOfLE h.le₁₃))).f p :=
  mappingCone.inr_f_desc_f ..

@[reassoc (attr := simp)]
theorem inr_mayerVietorisDesc {K₁ K₂ K₃ K₄ : Compacts X} (h : Lattice.BicartSq K₁ K₂ K₃ K₄) :
    mappingCone.inr _ ≫ F.mayerVietorisDesc h =
      biprod.desc (F.map (opHomOfLE h.le₁₂)) (-F.map (opHomOfLE h.le₁₃)) :=
  mappingCone.inr_desc ..

@[simp]
theorem inl_mayerVietorisDesc {K₁ K₂ K₃ K₄ : Compacts X} (h : Lattice.BicartSq K₁ K₂ K₃ K₄) :
    (mappingCone.inl _).comp (HomComplex.Cochain.ofHom (F.mayerVietorisDesc h)) (add_zero _) =
      0 :=
  mappingCone.inl_desc ..

/-- A K-presheaf `F` of cochain complexes is a *homotopy K-sheaf* (Pardon, Definition A.2.5) if
`F(∅)` is acyclic, the total complex of `F(K₂ ∪ K₃) ⟶ F(K₂) ⊞ F(K₃) ⟶ F(K₂ ∩ K₃)` is acyclic for
all compact `K₂` and `K₃`, and for every compact `K` the map to `F(K)` from a colimit of the
`F(K')` over the compact neighbourhoods `K'` of `K` is a quasi-isomorphism. -/
structure IsHomotopyKSheaf : Prop where
  acyclic_bot : (F.obj (op ⊥)).Acyclic
  quasiIso_mayerVietorisDesc {K₁ K₂ K₃ K₄ : Compacts X} (h : Lattice.BicartSq K₁ K₂ K₃ K₄) :
    QuasiIso (F.mayerVietorisDesc h)
  exists_isColimit_quasiIso_desc (K : Compacts X) :
    ∃ (c : Cocone ((Set.mono_coe K.compactNhds).functor.op ⋙ F)) (hc : IsColimit c),
      QuasiIso (hc.desc (F.coconeOfCompacts K))

/-- In a homotopy K-sheaf, the map to `F(K)` from any colimit of the `F(K')` over the compact
neighbourhoods `K'` of `K` is a quasi-isomorphism. -/
theorem IsHomotopyKSheaf.quasiIso_desc (hF : F.IsHomotopyKSheaf) (K : Compacts X)
    {c : Cocone ((Set.mono_coe K.compactNhds).functor.op ⋙ F)} (hc : IsColimit c) :
    QuasiIso (hc.desc (F.coconeOfCompacts K)) := by
  obtain ⟨c', hc', _⟩ := hF.exists_isColimit_quasiIso_desc K
  rw [← hc.coconePointUniqueUpToIso_hom_desc hc']
  infer_instance

/-- If the map `mappingCone φ ⟶ F(K₁)` of a bicartesian square is a quasi-isomorphism and `F(K₁)`
has vanishing cohomology in degree `i`, then the square of cohomology groups in degree `i + 1` is
a pullback square. -/
theorem isPullback_homologyMap {K₁ K₂ K₃ K₄ : Compacts X} (h : Lattice.BicartSq K₁ K₂ K₃ K₄)
    [QuasiIso (F.mayerVietorisDesc h)] {i j : ℤ} (hij : i + 1 = j)
    (hi : (F.obj (op K₁)).ExactAt i) :
    IsPullback (homologyMap (F.map (opHomOfLE h.le₂₄)) j)
      (homologyMap (F.map (opHomOfLE h.le₃₄)) j) (homologyMap (F.map (opHomOfLE h.le₁₂)) j)
      (homologyMap (F.map (opHomOfLE h.le₁₃)) j) := by
  let φ := biprod.lift (F.map (opHomOfLE h.le₂₄)) (F.map (opHomOfLE h.le₃₄))
  let ψ := biprod.desc (F.map (opHomOfLE h.le₁₂)) (-F.map (opHomOfLE h.le₁₃))
  -- the long exact cohomology sequence of `F(K₄) ⟶ F(K₂) ⊞ F(K₃) ⟶ mappingCone φ`
  let := HasDerivedCategory.standard C
  have hT := DerivedCategory.mappingCone_triangle_distinguished φ
  -- `H^i (mappingCone φ) ≅ H^i (F K₁) = 0`, so `H^j φ` is injective
  have hφ : Mono (homologyMap φ j) := by
    refine (homologyMap_exact₁_of_distTriang _ hT i j hij).mono_g (IsZero.eq_of_src ?_ _ _)
    rw [exactAt_iff_isZero_homology] at hi
    exact hi.of_iso (asIso (homologyMap (F.mayerVietorisDesc h) i))
  -- `H^j (mappingCone φ) ≅ H^j (F K₁)`, so `H(F K₄) ⟶ H(F K₂ ⊞ F K₃) ⟶ H(F K₁)` is exact
  let S := ShortComplex.mk (homologyMap φ j) (homologyMap ψ j)
    (by simp [φ, ψ, ← homologyMap_comp, (F.commSq_map h).w])
  have hex : S.Exact := ShortComplex.exact_of_iso
    (ShortComplex.isoMk
      (S₁ := ShortComplex.mk _ _ (homologyMap_comp_eq_zero_of_distTriang _ hT j)) (S₂ := S)
      (Iso.refl _) (Iso.refl _) (asIso (homologyMap (F.mayerVietorisDesc h) j))
      (by simp [S]) (by simp [S, φ, ψ, ← homologyMap_comp]))
    (homologyMap_exact₂_of_distTriang _ hT j)
  -- `sq` and `he` restate Mathlib facts about `homologyFunctor C _ j`, whose action on morphisms is
  -- `homologyMap · j` by definition (`HomologicalComplex.homologyFunctor_map`), with the objects
  -- written `homology K j`, so that the biproduct lemmas below match syntactically
  have sq : CommSq (homologyMap (F.map (opHomOfLE h.le₂₄)) j)
      (homologyMap (F.map (opHomOfLE h.le₃₄)) j) (homologyMap (F.map (opHomOfLE h.le₁₂)) j)
      (homologyMap (F.map (opHomOfLE h.le₁₃)) j) :=
    commSq_map (F ⋙ homologyFunctor C (ComplexShape.up ℤ) j) h
  -- cohomology commutes with the biproduct, which identifies the sequence with that of `sq`
  have := preservesBinaryBiproducts_of_preservesBiproducts
    (homologyFunctor C (ComplexShape.up ℤ) j)
  let e₂ : homology (F.obj (op K₂) ⊞ F.obj (op K₃)) j ≅
      homology (F.obj (op K₂)) j ⊞ homology (F.obj (op K₃)) j :=
    (homologyFunctor C (ComplexShape.up ℤ) j).mapBiprod _ _
  have he : e₂.hom = biprod.lift (homologyMap biprod.fst j) (homologyMap biprod.snd j) :=
    Functor.mapBiprod_hom ..
  obtain ⟨hS, _⟩ := (ShortComplex.exact_and_mono_f_iff_of_iso (ShortComplex.isoMk (S₁ := S)
    (S₂ := sq.shortComplex') (Iso.refl _) e₂ (Iso.refl _)
      (by dsimp [CommSq.shortComplex']; ext <;> simp [S, he, φ, ← homologyMap_comp])
      (by
        dsimp [CommSq.shortComplex']
        simp [S, he, ψ, ← homologyMap_comp, biprod.desc_eq, homologyMap_add]))).1
    ⟨hex, hφ⟩
  exact IsPullback.of_isLimit (sq.isLimitEquivIsLimitKernelFork.symm hS.fIsKernel)

section Colimit

variable [HasFilteredColimitsOfSize.{w, w} C] [AB5OfSize.{w, w} C] [WeaklyLocallyCompactSpace X]

/-- If the map to `F(K)` from a colimit of the `F(K')` over the compact neighbourhoods `K'` of
`K` is a quasi-isomorphism, then the cohomology of `F(K)` in each degree is the colimit of the
cohomology of the `F(K')`, since cohomology commutes with filtered colimits. -/
theorem nonempty_isColimit_coconeOfCompacts_homology (K : Compacts X)
    {c : Cocone ((Set.mono_coe K.compactNhds).functor.op ⋙ F)} (hc : IsColimit c)
    [QuasiIso (hc.desc (F.coconeOfCompacts K))] (n : ℤ) :
    Nonempty (IsColimit (coconeOfCompacts (F ⋙ homologyFunctor C (ComplexShape.up ℤ) n) K)) := by
  -- the compact neighbourhoods of `K` form a nonempty cofiltered family
  have : Nonempty K.compactNhds :=
    let ⟨L, hL, hKL⟩ := exists_compact_superset K.isCompact
    ⟨⟨⟨L, hL⟩, fun x ↦ mem_interior_iff_mem_nhds.1 (hKL x.property)⟩⟩
  let e := asIso (homologyMap (hc.desc (F.coconeOfCompacts K)) n)
  -- the goal's cocone `coconeOfCompacts (F ⋙ G) K` (with `G` the degree `n` cohomology functor)
  -- is `G.mapCocone (F.coconeOfCompacts K)` by definition: both have point `G.obj (F.obj (op K))`
  -- and legs `G.map (F.map _)`, and their diagrams differ by the definitional reassociation
  -- `(_ ⋙ F) ⋙ G = _ ⋙ (F ⋙ G)`; `G.map` is `homologyMap · n` by definition
  -- (`HomologicalComplex.homologyFunctor_map`), which the leg compatibility below uses
  exact ⟨(isColimitOfPreserves (homologyFunctor C (ComplexShape.up ℤ) n) hc).ofIsoColimit
      (Cocone.ext (c' := (homologyFunctor C (ComplexShape.up ℤ) n).mapCocone
        (F.coconeOfCompacts K)) e (fun L ↦
          (homologyMap_comp _ _ n).symm.trans (congrArg (homologyMap · n) (hc.fac _ _))))⟩

/-- **Pardon, Lemma A.2.12.** If `F` is a homotopy K-sheaf whose cohomology vanishes in degree
`i` on every compact set, then its cohomology in degree `i + 1`, `K ↦ H^(i + 1)(F(K))`, is a
K-sheaf. In particular, if the cohomology of `F` vanishes in all degrees below `i₀`, then its
cohomology in degree `i₀` is a K-sheaf. -/
theorem IsHomotopyKSheaf.isKSheaf_homology (hF : F.IsHomotopyKSheaf) {i j : ℤ} (hij : i + 1 = j)
    (hi : ∀ K : Compacts X, (F.obj (op K)).ExactAt i) :
    IsKSheaf (F ⋙ homologyFunctor C (ComplexShape.up ℤ) j) where
  nonempty_isTerminal := ⟨((hF.acyclic_bot j).isZero_homology).isTerminal⟩
  isPullback h :=
    have := hF.quasiIso_mayerVietorisDesc h
    F.isPullback_homologyMap h hij (hi _)
  nonempty_isColimit_coconeOfCompacts K :=
    let ⟨_, hc, _⟩ := hF.exists_isColimit_quasiIso_desc K
    F.nonempty_isColimit_coconeOfCompacts_homology K hc j

end Colimit

end TopCat.KPresheaf
