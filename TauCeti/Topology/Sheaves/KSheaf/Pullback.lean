/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sets.Compacts
public import TauCeti.Topology.Sheaves.KSheaf.Homotopy

/-!
# Pullback of K-sheaves along injective maps

A K-presheaf on a space `Y` (`TopCat.KPresheaf`) is a contravariant functor on the compact
subsets of `Y`. A continuous map `f : X ⟶ Y` takes compact subsets of `X` to compact subsets of
`Y` (`TopologicalSpace.Compacts.map`), so a K-presheaf `P` on `Y` pulls back to the K-presheaf
`f^* P` on `X` with

`(f^* P)(K) = P(f(K))`

(`TopCat.KPresheaf.pullback`). When `f` is injective, `X` is Hausdorff and locally compact and
`Y` is Hausdorff, this pullback preserves K-sheaves (`TopCat.KPresheaf.IsKSheaf.pullback`), and,
when `Y` is moreover weakly locally compact, homotopy K-sheaves of cochain complexes
(`TopCat.KPresheaf.IsHomotopyKSheaf.pullback`), which is Pardon's Definition A.3.6.

Taking images preserves `⊥` and `⊔`, and, for an injective map, `⊓`; so the first two axioms for
`f^* P` are those of `P` at the images. Injectivity is needed: for the map from a two-point
discrete space `{a, b}` to a point, the pullback of the K-sheaf `ℤ` on the point takes the value
`ℤ` on `{a}`, `{b}` and `{a, b}` and `0` on `∅`, and the diagonal `ℤ ⟶ ℤ ⊕ ℤ` is not onto the
kernel of the map to the value `0` on `{a} ∩ {b} = ∅`.

The third axiom, that `(f^* P)(K)` is the colimit of `(f^* P)(K')` over the compact
neighbourhoods `K'` of `K`, holds for every continuous `f` out of a Hausdorff, locally compact
space as soon as `P` satisfies it
(`TopCat.KPresheaf.nonempty_isColimit_coconeOfCompacts_pullback`). The images `f(K')` are not
neighbourhoods of `f(K)`, so this is not a cofinality statement; instead, every
compact neighbourhood `L` of `f(K)` is a neighbourhood of `f(K')` for some compact neighbourhood
`K'` of `K` (`TopologicalSpace.Compacts.exists_mem_compactNhds_mem_compactNhds_map`), and the
colimit property of `P` at `f(K)` and at the `f(K')` combine. For homotopy K-sheaves the colimit
axiom is checked on cohomology, which commutes with filtered colimits.

Pullback of K-sheaves along an injective map is the functor `TopCat.KSheaf.pullback`.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Appendix A.3, Definition A.3.6.
-/

public section

universe w v u

open CategoryTheory Limits Opposite TopologicalSpace

namespace TopCat

variable {A : Type u} [Category.{v} A] {X Y : TopCat.{w}}

namespace KPresheaf

/-- The pullback of K-presheaves along a continuous map `f : X ⟶ Y`: the value of the pullback
of `P` on a compact `K ⊆ X` is the value of `P` on the compact image `f(K)`. For injective `f`
it preserves K-sheaves (`TopCat.KPresheaf.IsKSheaf.pullback`) and homotopy K-sheaves
(`TopCat.KPresheaf.IsHomotopyKSheaf.pullback`). -/
@[expose] def pullback (f : X ⟶ Y) : KPresheaf A Y ⥤ KPresheaf A X :=
  (Functor.whiskeringLeft _ _ A).obj (Compacts.map_mono f f.hom.continuous).functor.op

variable (f : X ⟶ Y)

@[simp]
lemma pullback_obj_obj (P : KPresheaf A Y) (K : (Compacts X)ᵒᵖ) :
    ((pullback f).obj P).obj K = P.obj (op (Compacts.map f f.hom.continuous K.unop)) :=
  (rfl)

@[simp]
lemma pullback_obj_map (P : KPresheaf A Y) {K L : (Compacts X)ᵒᵖ} (g : K ⟶ L) :
    ((pullback f).obj P).map g =
      P.map (opHomOfLE (Compacts.map_mono f f.hom.continuous (leOfHom g.unop))) :=
  (rfl)

@[simp]
lemma pullback_map_app {P Q : KPresheaf A Y} (φ : P ⟶ Q) (K : (Compacts X)ᵒᵖ) :
    ((pullback f).map φ).app K = φ.app (op (Compacts.map f f.hom.continuous K.unop)) :=
  (rfl)

variable [T2Space X]

omit [T2Space X] in
/-- For a cocone `s` over the values of `f^* P` on the compact neighbourhoods of `K`, its legs at
two compact neighbourhoods `K₂ ⊆ K₁` of `K` agree after restriction from a compact set `L`
containing `f(K₁)`. -/
private lemma map_comp_ι_eq_of_le (P : KPresheaf A Y) {K : Compacts X}
    (s : Cocone ((Set.mono_coe K.compactNhds).functor.op ⋙ (pullback f).obj P))
    {K₁ K₂ : K.compactNhds} (h : K₂ ≤ K₁) {L : Compacts Y}
    (h₁ : Compacts.map f f.hom.continuous K₁.val ≤ L) :
    P.map (opHomOfLE h₁) ≫ s.ι.app (op K₁) =
      P.map (opHomOfLE ((Compacts.map_mono f f.hom.continuous h).trans h₁)) ≫ s.ι.app (op K₂) := by
  rw [← s.w (homOfLE h).op]
  -- the leg of the diagram from `K₁` to `K₂` is the restriction of `P` from `f(K₁)` to `f(K₂)`
  exact (P.map_comp_assoc _ _ _).symm

/-- For a cocone `s` over the values of `f^* P` on the compact neighbourhoods of `K`, its legs at
any two compact neighbourhoods `K₁`, `K₂` of `K` agree after restriction from a compact set `L`
containing `f(K₁)` and `f(K₂)`. -/
private lemma map_comp_ι_eq (P : KPresheaf A Y) {K : Compacts X}
    (s : Cocone ((Set.mono_coe K.compactNhds).functor.op ⋙ (pullback f).obj P))
    {K₁ K₂ : K.compactNhds} {L : Compacts Y} (h₁ : Compacts.map f f.hom.continuous K₁.val ≤ L)
    (h₂ : Compacts.map f f.hom.continuous K₂.val ≤ L) :
    P.map (opHomOfLE h₁) ≫ s.ι.app (op K₁) = P.map (opHomOfLE h₂) ≫ s.ι.app (op K₂) := by
  rw [map_comp_ι_eq_of_le f P s (inf_le_left : K₁ ⊓ K₂ ≤ K₁),
    map_comp_ι_eq_of_le f P s (inf_le_right : K₁ ⊓ K₂ ≤ K₂)]

variable [LocallyCompactSpace X]

/-- **The colimit axiom for a pullback.** If `X` is Hausdorff and locally compact and `P` is a
K-presheaf on `Y` whose value on every compact set is the colimit of its values on the compact
neighbourhoods, then the same holds for its pullback `K ↦ P(f(K))` along any continuous map
`f : X ⟶ Y`. -/
theorem nonempty_isColimit_coconeOfCompacts_pullback {P : KPresheaf A Y}
    (hP : ∀ L : Compacts Y, Nonempty (IsColimit (P.coconeOfCompacts L))) (K : Compacts X) :
    Nonempty (IsColimit (((pullback f).obj P).coconeOfCompacts K)) := by
  let fK (K' : Compacts X) : Compacts Y := Compacts.map f f.hom.continuous K'
  -- every compact neighbourhood `L` of `f(K)` is one of `f(g L)` for a compact neighbourhood
  -- `g L` of `K`
  choose g hg hLg using fun L : (fK K).compactNhds ↦
    Compacts.exists_mem_compactNhds_mem_compactNhds_map f.hom.continuous L.property
  have hle (L : (fK K).compactNhds) : fK (g L) ≤ L.val :=
    Compacts.subset_of_mem_compactNhds (hLg L)
  -- a compact neighbourhood of `f(K')` is one of `f(K)` when `K ⊆ K'`
  have hmem {K' : Compacts X} (hK' : K' ∈ K.compactNhds) {L : Compacts Y}
      (hL : L ∈ (fK K').compactNhds) : L ∈ (fK K).compactNhds := fun y ↦
    hL ⟨y.val, Set.image_mono (Compacts.subset_of_mem_compactNhds hK') y.property⟩
  -- a cocone over `L ↦ P(L)`, `L` a compact neighbourhood of `f(K)`, from one over
  -- `K' ↦ P(f(K'))`: restrict from `L` to `f(g L)`
  let t (s : Cocone ((Set.mono_coe K.compactNhds).functor.op ⋙ (pullback f).obj P)) :
      Cocone ((Set.mono_coe (fK K).compactNhds).functor.op ⋙ P) :=
    { pt := s.pt
      ι :=
        { app L := P.map (opHomOfLE (hle L.unop)) ≫ s.ι.app (op ⟨g L.unop, hg L.unop⟩)
          -- restricting from `L₁` through `L₂` to `f(g L₂)` and restricting from `L₁` to
          -- `f(g L₁)` give the same map to `s.pt`
          naturality L₁ L₂ h := by
            refine ((P.map_comp_assoc _ _ _).symm.trans ?_).trans (Category.comp_id _).symm
            exact map_comp_ι_eq f P s (K₁ := ⟨g L₂.unop, hg _⟩) (K₂ := ⟨g L₁.unop, hg _⟩) _
              (hle L₁.unop) } }
  have hc := (hP (fK K)).some
  refine ⟨{ desc s := hc.desc (t s), fac s K' := ?_, uniq s m hm := hc.hom_ext fun L ↦ ?_ }⟩
  · -- both sides agree after restriction from each compact neighbourhood `L` of `f(K')`, where
    -- the left side is the leg of `t s` at `L`
    refine (hP (fK K'.unop)).some.hom_ext fun L ↦ ?_
    let L' : (fK K).compactNhds := ⟨L.unop.val, hmem K'.unop.property L.unop.property⟩
    -- the composite of the two restrictions is, by definition, the leg of `P.coconeOfCompacts`
    -- at `L'`; `rw` cannot match it through `coconeOfCompacts`, so the steps are chained
    refine (P.map_comp_assoc _ _ _).symm.trans ((hc.fac (t s) (op L')).trans ?_)
    exact map_comp_ι_eq f P s (K₁ := ⟨g L', hg L'⟩) (hle L')
      (Compacts.subset_of_mem_compactNhds L.unop.property)
  · -- `m` restricted from `L` factors through `f(g L)`, where it is the leg of `s`
    rw [hc.fac]
    -- the leg of `P.coconeOfCompacts` at `L` is, by definition, the restriction through `f(g L)`
    refine (P.map_comp_assoc (opHomOfLE (hle L.unop)) (opHomOfLE (Compacts.map_mono f
      f.hom.continuous (Compacts.subset_of_mem_compactNhds (hg L.unop)))) m).trans ?_
    exact congrArg (P.map _ ≫ ·) (hm (op ⟨g L.unop, hg L.unop⟩))

variable [T2Space Y]

/-- **Pullback along an injective map preserves K-sheaves** (Pardon, Definition A.3.6). If `X`
and `Y` are Hausdorff, `X` is locally compact and `P` is a K-sheaf on `Y`, then its pullback
`K ↦ P(f(K))` along an injective continuous map `f : X ⟶ Y` is a K-sheaf on `X`. -/
theorem IsKSheaf.pullback (hf : Function.Injective f) {P : KPresheaf A Y} (hP : P.IsKSheaf) :
    ((KPresheaf.pullback f).obj P).IsKSheaf where
  nonempty_isTerminal := by
    simpa only [pullback_obj_obj, unop_op, Compacts.map_bot] using hP.nonempty_isTerminal
  -- The square of the pullback is, by definition, the square of `P` at the images.
  isPullback {K₁ K₂ K₃ K₄} h :=
    hP.isPullback (K₁ := Compacts.map f f.hom.continuous K₁)
      (K₂ := Compacts.map f f.hom.continuous K₂) (K₃ := Compacts.map f f.hom.continuous K₃)
      (K₄ := Compacts.map f f.hom.continuous K₄)
      ⟨by rw [← Compacts.map_sup, h.sup_eq],
        by rw [← Compacts.map_inf _ f.hom.continuous hf, h.inf_eq]⟩
  nonempty_isColimit_coconeOfCompacts :=
    nonempty_isColimit_coconeOfCompacts_pullback f hP.nonempty_isColimit_coconeOfCompacts

section Homotopy

variable {C : Type u} [Category.{v} C] [Abelian C] [HasFilteredColimitsOfSize.{w, w} C]
  [AB5OfSize.{w, w} C] [WeaklyLocallyCompactSpace Y]

/-- **Pullback along an injective map preserves homotopy K-sheaves** (Pardon, Definition A.3.6).
If `X` is Hausdorff and locally compact, `Y` is Hausdorff and weakly locally compact, and `F` is
a homotopy K-sheaf of cochain complexes on `Y`, then its pullback `K ↦ F(f(K))` along an
injective continuous map `f : X ⟶ Y` is a homotopy K-sheaf on `X`. -/
theorem IsHomotopyKSheaf.pullback (hf : Function.Injective f)
    {F : KPresheaf (CochainComplex C ℤ) Y} (hF : F.IsHomotopyKSheaf) :
    ((KPresheaf.pullback f).obj F).IsHomotopyKSheaf where
  acyclic_bot := by
    simpa only [pullback_obj_obj, unop_op, Compacts.map_bot] using hF.acyclic_bot
  quasiIso_mayerVietorisDesc {K₁ K₂ K₃ K₄} h := by
    have := hF.quasiIso_mayerVietorisDesc (K₁ := Compacts.map f f.hom.continuous K₁)
      (K₂ := Compacts.map f f.hom.continuous K₂) (K₃ := Compacts.map f f.hom.continuous K₃)
      (K₄ := Compacts.map f f.hom.continuous K₄)
      ⟨by rw [← Compacts.map_sup, h.sup_eq],
        by rw [← Compacts.map_inf _ f.hom.continuous hf, h.inf_eq]⟩
    -- The Mayer–Vietoris map of the pullback is, by definition of `pullback`, that of `F` at the
    -- images.
    rw [F.mayerVietorisDesc_eq_desc] at this
    rw [mayerVietorisDesc_eq_desc]
    exact this
  exists_isColimit_quasiIso_desc K := by
    refine ⟨_, colimit.isColimit _, (quasiIso_iff _).2 fun n ↦ ?_⟩
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let H := HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n
    -- the cohomology of `F` in degree `n` satisfies the colimit axiom, hence so does its pullback
    have hH (L : Compacts Y) : Nonempty (IsColimit (coconeOfCompacts (F ⋙ H) L)) :=
      let ⟨_, hc, _⟩ := hF.exists_isColimit_quasiIso_desc L
      F.nonempty_isColimit_coconeOfCompacts_homology L hc n
    obtain ⟨ht⟩ := nonempty_isColimit_coconeOfCompacts_pullback f hH K
    -- cohomology commutes with the filtered colimit over the compact neighbourhoods of `K`, so the
    -- cohomology of the comparison map is the comparison map of two colimits
    let s := ((KPresheaf.pullback f).obj F).coconeOfCompacts K
    let hc := isColimitOfPreserves H (colimit.isColimit
      ((Set.mono_coe K.compactNhds).functor.op ⋙ (KPresheaf.pullback f).obj F))
    -- the image of `s` under `H` is, by definition, the cocone of the pullback of `F ⋙ H` at `K`:
    -- both have point `H(F(f(K)))` and legs `H` applied to the restrictions of `F`, and their
    -- diagrams differ by the definitional reassociation of the composite functors
    have ht' : IsColimit (H.mapCocone s) := ht
    have : HomologicalComplex.homologyMap ((colimit.isColimit _).desc s) n =
        (hc.coconePointUniqueUpToIso ht').hom :=
      (preserves_desc_mapCocone (G := H) (c₂ := s) (t := colimit.isColimit _)).symm.trans
        (hc.hom_ext fun L ↦ by rw [IsColimit.comp_coconePointUniqueUpToIso_hom, hc.fac])
    rw [this]
    infer_instance

end Homotopy

end KPresheaf

namespace KSheaf

variable [T2Space X] [LocallyCompactSpace X] [T2Space Y]

/-- The pullback of K-sheaves along an injective continuous map `f : X ⟶ Y` of Hausdorff spaces
with `X` locally compact: the K-sheaf `K ↦ P(f(K))` (`TopCat.KPresheaf.IsKSheaf.pullback`). -/
@[expose] def pullback (f : X ⟶ Y) (hf : Function.Injective f) : KSheaf A Y ⥤ KSheaf A X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ KPresheaf.pullback f)
    fun P ↦ P.property.pullback f hf

variable (f : X ⟶ Y) (hf : Function.Injective f)

@[simp]
lemma pullback_obj_obj (P : KSheaf A Y) :
    ((pullback f hf).obj P).obj = (KPresheaf.pullback f).obj P.obj :=
  (rfl)

@[simp]
lemma pullback_map_hom {P Q : KSheaf A Y} (φ : P ⟶ Q) :
    ((pullback f hf).map φ).hom = (KPresheaf.pullback f).map φ.hom :=
  (rfl)

end KSheaf

end TopCat
