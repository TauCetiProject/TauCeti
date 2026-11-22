/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import TauCeti.AlgebraicGeometry.Modules.StrictlyPerfect.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import TauCeti.Algebra.Homology.HomotopyCategory.MappingCone
import TauCeti.Algebra.Homology.HomotopyCategory.ShiftSequence
import TauCeti.AlgebraicGeometry.Modules.Sections
import TauCeti.AlgebraicGeometry.Modules.Sheaf
import TauCeti.Topology.Sheaves.Exact

/-!
# Local lifting and local derived maps from strictly perfect complexes

A strictly perfect complex `P` of `𝒪_X`-modules behaves locally on `X` like a bounded complex of
projectives: every morphism from a finite locally free sheaf lifts locally across an epimorphism
(`exists_restrict_lift_of_epi`), and consequently every chain map from `P` into a complex exact
in degrees `≥ a` (where `P^i = 0` for `i < a`) is locally nullhomotopic
(`exists_restrict_homotopy_zero`).

Applying this to mapping cones yields the two fundamental local lifting results for strictly
perfect complexes:

* **Local lifting of chain maps** (Stacks Tag 08C8): if `P` is strictly perfect with `P^i = 0` for
  `i < a` and `φ : M ⟶ N` induces epimorphisms on `H^j` and monomorphisms on `H^{j+1}` for all
  `j ≥ a` (in particular, an epimorphism on `H^a` and isomorphisms on `H^j` for `j > a`, or a
  quasi-isomorphism), then every chain map `α : P ⟶ N` lifts locally on `X` to a chain map
  `β : P|_U ⟶ M|_U` such that `β ≫ φ|_U` is chain homotopic to `α|_U`
  (`exists_restrict_lift_homotopy_of_epi_mono`, `exists_restrict_lift_homotopy`,
  `exists_restrict_lift_homotopy_of_quasiIso`).
* **Local representatives and uniqueness of derived maps** (Stacks Tag 08C9): any two chain maps
  `f₁, f₂ : P ⟶ M` with equal image in `D(X.Modules)` are locally chain homotopic
  (`exists_restrict_homotopy_of_Q_map_eq`), and every derived morphism
  `DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj M` is locally represented by an actual chain map
  `P|_U ⟶ M|_U` (`exists_restrict_mapDerivedCategory_eq`).

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.exists_restrict_section_of_epi`: local lifting of sections
  along an epimorphism of `𝒪_X`-modules;
* `AlgebraicGeometry.Scheme.Modules.exists_restrict_lift_of_epi`: local lifting of morphisms out of
  a finite locally free `𝒪_X`-module along an epimorphism;
* `AlgebraicGeometry.Scheme.Modules.exists_restrict_homotopy_zero` and
  `AlgebraicGeometry.Scheme.Modules.exists_restrict_homotopy_zero_of_acyclic`: local nullhomotopy
  of chain maps from strictly perfect complexes into locally exact or acyclic complexes;
* `AlgebraicGeometry.Scheme.Modules.exists_restrict_lift_homotopy_of_epi_mono`,
  `AlgebraicGeometry.Scheme.Modules.exists_restrict_lift_homotopy`, and
  `AlgebraicGeometry.Scheme.Modules.exists_restrict_lift_homotopy_of_quasiIso`: local lifting of
  chain maps up to homotopy (Stacks Tag 08C8);
* `AlgebraicGeometry.Scheme.Modules.exists_restrict_homotopy_of_Q_map_eq` and
  `AlgebraicGeometry.Scheme.Modules.exists_restrict_mapDerivedCategory_eq`: local homotopy
  uniqueness and local chain representatives for derived morphisms out of strictly perfect
  complexes (Stacks Tag 08C9).

## References

* [The Stacks Project, Tag 08C8](https://stacks.math.columbia.edu/tag/08C8)
* [The Stacks Project, Tag 08C9](https://stacks.math.columbia.edu/tag/08C9)
-/

public section

open CategoryTheory Limits ZeroObject Opposite HomologicalComplex AlgebraicGeometry
open CochainComplex.HomComplex

namespace AlgebraicGeometry.Scheme.Modules

universe v v' u

noncomputable section

section HelperRestriction

/-- Passing from an open `W` of an open subscheme `V` of `X` back to the open
`U = (W.ι ≫ V.ι).opensRange` of `X` identifies `restrictFunctor U.ι` with the composition of
restrictions along `V.ι`, `W.ι`, and the isomorphism `U ≅ W`. -/
private def restrictOpensRangeIso {X : Scheme.{u}} (V : X.Opens) (W : V.toScheme.Opens) :
    restrictFunctor (W.ι ≫ V.ι).opensRange.ι ≅
      restrictFunctor V.ι ⋙ restrictFunctor W.ι ⋙
        restrictFunctor (W.ι ≫ V.ι).isoOpensRange.inv :=
  restrictFunctorCongr (show (W.ι ≫ V.ι).opensRange.ι =
      (W.ι ≫ V.ι).isoOpensRange.inv ≫ (W.ι ≫ V.ι) by
    rw [Iso.eq_inv_comp]
    exact (W.ι ≫ V.ι).isoOpensRange_hom_ι) ≪≫
    restrictFunctorComp (W.ι ≫ V.ι).isoOpensRange.inv (W.ι ≫ V.ι) ≪≫
    Functor.isoWhiskerRight (restrictFunctorComp W.ι V.ι)
      (restrictFunctor (W.ι ≫ V.ι).isoOpensRange.inv)

/-- If `x ∈ V` and `⟨x, hxV⟩ ∈ W`, then `x` lies in the open image `(W.ι ≫ V.ι).opensRange`. -/
private lemma mem_opensRange_comp_ι {X : Scheme.{u}} {V : X.Opens} {W : V.toScheme.Opens}
    {x : X} (hxV : x ∈ V) (hxW : (⟨x, hxV⟩ : V.toScheme) ∈ W) :
    x ∈ (W.ι ≫ V.ι).opensRange :=
  ⟨⟨⟨x, hxV⟩, hxW⟩, rfl⟩

/-- Transport a nullhomotopy across a natural isomorphism of additive functors. -/
private def homotopyZeroOfNatIso {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] {F₁ F₂ : C ⥤ D} [F₁.Additive] [F₂.Additive]
    (e : F₁ ≅ F₂) {P K : CochainComplex C ℤ} {f : P ⟶ K}
    (H : Homotopy ((F₂.mapHomologicalComplex (.up ℤ)).map f) 0) :
    Homotopy ((F₁.mapHomologicalComplex (.up ℤ)).map f) 0 :=
  let eC := NatIso.mapHomologicalComplex e (.up ℤ)
  (Homotopy.ofEq (by
    rw [Category.assoc, eC.inv.naturality f, Iso.hom_inv_id_app_assoc])).trans
    (((H.compLeft (eC.hom.app P)).compRight (eC.inv.app K)).trans
      (Homotopy.ofEq (by simp)))

/-- Transport a local nullhomotopy from an open `W` of an open subscheme `V` back to an open of
`X`. -/
private lemma exists_restrict_homotopy_zero_of_open {X : Scheme.{u}} {V : X.Opens}
    {W : V.toScheme.Opens} {x : X} (hxV : x ∈ V) (hxW : (⟨x, hxV⟩ : V.toScheme) ∈ W)
    {P K : CochainComplex X.Modules ℤ} {f : P ⟶ K}
    (H : Homotopy (((restrictFunctor W.ι).mapHomologicalComplex (.up ℤ)).map
      (((restrictFunctor V.ι).mapHomologicalComplex (.up ℤ)).map f)) 0) :
    ∃ (U : X.Opens), x ∈ U ∧
      Nonempty (Homotopy (((restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).map f) 0) := by
  let U := (W.ι ≫ V.ι).opensRange
  let e := restrictOpensRangeIso V W
  have H' : Homotopy (((restrictFunctor V.ι ⋙ restrictFunctor W.ι ⋙
      restrictFunctor (W.ι ≫ V.ι).isoOpensRange.inv).mapHomologicalComplex (.up ℤ)).map f) 0 :=
    ((restrictFunctor (W.ι ≫ V.ι).isoOpensRange.inv).mapHomotopy H).trans
      (Homotopy.ofEq (by simp))
  exact ⟨U, mem_opensRange_comp_ι hxV hxW, ⟨homotopyZeroOfNatIso e H'⟩⟩

end HelperRestriction

section LocalEpiLifting

/-- Along an epimorphism `p : M ⟶ N` of `𝒪_X`-modules, every section of `N` over an open `V`
lifts to a section of `M` over an open neighbourhood `W ≤ V` of any given point `x ∈ V`. -/
theorem exists_restrict_section_of_epi {X : Scheme.{u}} {M N : X.Modules} (p : M ⟶ N) [Epi p]
    {V : X.Opens} (s : Γ(N, V)) (x : X) (hx : x ∈ V) :
    ∃ (W : X.Opens), x ∈ W ∧ ∃ hWV : W ≤ V, ∃ t : Γ(M, W),
      p.app W t = N.presheaf.map (homOfLE hWV).op s := by
  have : Epi ((TauCeti.AlgebraicGeometry.Scheme.Modules.toSheaf X).map p) :=
    (TauCeti.AlgebraicGeometry.Scheme.Modules.toSheaf X).map_epi p
  obtain ⟨W, -, hxW, hWV, t, ht⟩ := TopCat.Sheaf.exists_mem_lift_of_epi (B := Set.univ)
    (fun _ _ U _ y hy ↦ ⟨U, trivial, hy, le_rfl⟩)
    ((TauCeti.AlgebraicGeometry.Scheme.Modules.toSheaf X).map p) (Set.mem_univ V) s x hx
  exact ⟨W, hxW, hWV, t, ht⟩

/-- Along an epimorphism `p : M ⟶ N` of `𝒪_X`-modules, any morphism from a finite free
`𝒪_X`-module `free I ⟶ N` lifts to `M` over an open neighbourhood of any given point `x : X`. -/
private theorem exists_restrict_lift_of_epi_free {X : Scheme.{u}} {M N : X.Modules} (p : M ⟶ N)
    [Epi p] {I : Type u} [Finite I] (f : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ N) (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U)
      (g : restrict (SheafOfModules.free (R := X.ringCatSheaf) I) U.ι ⟶ M.restrict U.ι),
      g ≫ (restrictFunctor U.ι).map p = (restrictFunctor U.ι).map f := by
  have : Fintype I := Fintype.ofFinite I
  -- Lift the global section corresponding to each basis generator near `x`.
  have hlift : ∀ i : I, ∃ (W : X.Opens), x ∈ W ∧ ∃ t : Γ(M, W),
      p.app W t = N.presheaf.map W.leTop.op (N.sectionsEquivTop (N.freeHomEquiv f i)) := by
    intro i
    obtain ⟨W, hxW, _, t, ht⟩ := exists_restrict_section_of_epi p
      (V := ⊤) (N.sectionsEquivTop (N.freeHomEquiv f i)) x trivial
    exact ⟨W, hxW, t, ht⟩
  choose W hxW t ht using hlift
  let U : X.Opens := Finset.univ.inf W
  have hxU : x ∈ U := by
    change x ∈ (U : Set X)
    rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_eq_iInf]
    simpa using hxW
  have hU_le (i : I) : U ≤ W i := Finset.inf_le (Finset.mem_univ i)
  have htop : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  -- Work in `SheafOfModules` so `freeHomEquiv` rewrites without unfolding `X.Modules`.
  let G : SheafOfModules.{u} X.ringCatSheaf ⥤ SheafOfModules.{u} U.toScheme.ringCatSheaf :=
    restrictFunctor U.ι
  have : PreservesColimitsOfShape (Discrete I) G :=
    (restrictAdjunction U.ι).leftAdjoint_preservesColimits.preservesColimitsOfShape
  let eU : G.obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf :=
    restrictUnitIso U.ι
  let eF : SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅
      G.obj (SheafOfModules.free (R := X.ringCatSheaf) I) :=
    SheafOfModules.mapFreeIso G I eU.symm
  let MX : SheafOfModules.{u} X.ringCatSheaf := M
  let NX : SheafOfModules.{u} X.ringCatSheaf := N
  let MU : SheafOfModules.{u} U.toScheme.ringCatSheaf := M.restrict U.ι
  let NU : SheafOfModules.{u} U.toScheme.ringCatSheaf := N.restrict U.ι
  let p' : MX ⟶ NX := p
  let f' : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ NX := f
  let u (i : I) : Γ(M.restrict U.ι, ⊤) :=
    (M.restrictAppIso U.ι ⊤).inv
      (M.presheaf.map (eqToHom htop ≫ homOfLE (hU_le i)).op (t i))
  let g₀ : SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ⟶ MU :=
    MU.freeHomEquiv.symm fun i ↦ (M.restrict U.ι).sectionsEquivTop.symm (u i)
  refine ⟨U, hxU, eF.inv ≫ g₀, ?_⟩
  change (eF.inv ≫ g₀) ≫ G.map p' = G.map f'
  rw [Category.assoc, eF.inv_comp_eq]
  refine NU.freeHomEquiv.injective ?_
  ext i : 1
  apply (N.restrict U.ι).sectionsEquivTop.injective
  rw [sectionsEquivTop_apply, sectionsEquivTop_apply]
  have hLHS : (NU.freeHomEquiv (g₀ ≫ G.map p') i).val (op ⊤) =
      (N.restrictAppIso U.ι ⊤).inv
        (N.presheaf.map (U.ι ''ᵁ ⊤).leTop.op ((NX.freeHomEquiv f' i).val (op ⊤))) := by
    rw [SheafOfModules.freeHomEquiv_comp_apply]
    simp only [g₀, Equiv.apply_symm_apply]
    have hu : ((M.restrict U.ι).sectionsEquivTop.symm (u i)).val (op ⊤) = u i :=
      (sectionsEquivTop_apply _ _).symm.trans ((M.restrict U.ι).sectionsEquivTop.apply_symm_apply _)
    change (G.map p').val.app (op ⊤)
        (((M.restrict U.ι).sectionsEquivTop.symm (u i)).val (op ⊤)) = _
    rw [hu]
    change p.app (U.ι ''ᵁ ⊤)
      (M.presheaf.map (eqToHom htop ≫ homOfLE (hU_le i)).op (t i)) =
      N.presheaf.map (U.ι ''ᵁ ⊤).leTop.op ((NX.freeHomEquiv f' i).val (op ⊤))
    have hnat := p.mapPresheaf.naturality_apply (eqToHom htop ≫ homOfLE (hU_le i)).op (t i)
    change p.app (U.ι ''ᵁ ⊤) (M.presheaf.map (eqToHom htop ≫ homOfLE (hU_le i)).op (t i)) =
      N.presheaf.map (eqToHom htop ≫ homOfLE (hU_le i)).op (p.app (W i) (t i)) at hnat
    rw [hnat, ht i, ← ConcreteCategory.comp_apply, ← N.presheaf.map_comp, sectionsEquivTop_apply]
    rfl
  have hRHS : (NU.freeHomEquiv (eF.hom ≫ G.map f') i).val (op ⊤) =
      (N.restrictAppIso U.ι ⊤).inv
        (N.presheaf.map (U.ι ''ᵁ ⊤).leTop.op ((NX.freeHomEquiv f' i).val (op ⊤))) := by
    have hfree : NU.freeHomEquiv (eF.hom ≫ G.map f') i =
        NU.unitHomEquiv (SheafOfModules.ιFree i ≫ eF.hom ≫ G.map f') := by
      apply NU.unitHomEquiv.symm.injective
      rw [Equiv.symm_apply_apply]
      exact SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply (M := NU) _ i
    have hgf : eU.symm.hom ≫ G.map (SheafOfModules.ιFree i) ≫ G.map f' =
        eU.inv ≫ G.map (SheafOfModules.ιFree i ≫ f') :=
      congrArg (eU.inv ≫ ·) (G.map_comp (SheafOfModules.ιFree i) f').symm
    rw [hfree, ← Category.assoc, SheafOfModules.ιFree_mapFreeIso_hom, Category.assoc,
      hgf, SheafOfModules.unitHomEquiv_apply_coe]
    -- `eU.inv` on `⊤` is `(U.ι.appIso ⊤).inv`, which is a ring isomorphism sending `1` to `1`.
    have h1 : (eU.inv.val.app (op ⊤)) (1 : Γ(U.toScheme, ⊤)) = (1 : Γ(X, U.ι ''ᵁ ⊤)) := by
      have hhom : (eU.hom.val.app (op ⊤)) (1 : Γ(X, U.ι ''ᵁ ⊤)) =
          (1 : Γ(U.toScheme, ⊤)) := map_one (U.ι.appIso ⊤).hom.hom
      have hinv := congr_arg (eU.inv.val.app (op ⊤)) hhom
      have hid : (eU.inv.val.app (op ⊤)) ((eU.hom.val.app (op ⊤)) (1 : Γ(X, U.ι ''ᵁ ⊤))) =
          (1 : Γ(X, U.ι ''ᵁ ⊤)) :=
        congrArg (fun φ ↦ φ.val.app (op ⊤) (1 : Γ(X, U.ι ''ᵁ ⊤))) eU.hom_inv_id
      exact hinv.symm.trans hid
    change (G.map (SheafOfModules.ιFree i ≫ f')).val.app (op ⊤)
        ((eU.inv.val.app (op ⊤)) (1 : Γ(U.toScheme, ⊤))) = _
    rw [h1]
    have hfreeX : NX.freeHomEquiv f' i = NX.unitHomEquiv (SheafOfModules.ιFree i ≫ f') := by
      apply NX.unitHomEquiv.symm.injective
      rw [Equiv.symm_apply_apply]
      exact SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply (M := NX) f' i
    exact (SheafOfModules.unitHomEquiv_apply_coe NX (SheafOfModules.ιFree i ≫ f')
      (op (U.ι ''ᵁ ⊤))).symm.trans
        ((congrArg (fun s ↦ s.val (op (U.ι ''ᵁ ⊤))) hfreeX.symm).trans
          (PresheafOfModules.sections_property (NX.freeHomEquiv f' i)
            (U.ι ''ᵁ ⊤).leTop.op).symm)
  exact hLHS.trans hRHS.symm

/-- Along an epimorphism `p : M ⟶ N` of `𝒪_X`-modules, any morphism `f : E ⟶ N` from a finite
locally free `𝒪_X`-module `E` lifts to `M` over an open neighbourhood of any given point `x : X`. -/
theorem exists_restrict_lift_of_epi {X : Scheme.{u}} {E M N : X.Modules}
    (hE : isFiniteLocallyFree X E) (p : M ⟶ N) [Epi p] (f : E ⟶ N) (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U) (g : E.restrict U.ι ⟶ M.restrict U.ι),
      g ≫ (restrictFunctor U.ι).map p = (restrictFunctor U.ι).map f := by
  obtain ⟨V, hxV, I, hI, ⟨e⟩⟩ := (isFiniteLocallyFree_iff_forall_exists_iso_free E).mp hE x
  have : Finite I := hI
  have : Epi ((restrictFunctor V.ι).map p) := (restrictFunctor V.ι).map_epi p
  obtain ⟨W, hxW, gW, hgW⟩ := exists_restrict_lift_of_epi_free
    ((restrictFunctor V.ι).map p) (e.inv ≫ (restrictFunctor V.ι).map f) (⟨x, hxV⟩ : V.toScheme)
  let U := (W.ι ≫ V.ι).opensRange
  let α := restrictOpensRangeIso V W
  let gV : (E.restrict V.ι).restrict W.ι ⟶ (M.restrict V.ι).restrict W.ι :=
    (restrictFunctor W.ι).map e.hom ≫ gW
  have hgV : gV ≫ (restrictFunctor W.ι).map ((restrictFunctor V.ι).map p) =
      (restrictFunctor W.ι).map ((restrictFunctor V.ι).map f) := by
    calc gV ≫ (restrictFunctor W.ι).map ((restrictFunctor V.ι).map p)
      _ = (restrictFunctor W.ι).map e.hom ≫
            (gW ≫ (restrictFunctor W.ι).map ((restrictFunctor V.ι).map p)) :=
          Category.assoc _ _ _
      _ = (restrictFunctor W.ι).map e.hom ≫
            (restrictFunctor W.ι).map (e.inv ≫ (restrictFunctor V.ι).map f) :=
          congrArg ((restrictFunctor W.ι).map e.hom ≫ ·) hgW
      _ = (restrictFunctor W.ι).map (e.hom ≫ e.inv ≫ (restrictFunctor V.ι).map f) :=
          ((restrictFunctor W.ι).map_comp _ _).symm
      _ = (restrictFunctor W.ι).map ((restrictFunctor V.ι).map f) :=
          congrArg (restrictFunctor W.ι).map (Iso.hom_inv_id_assoc e _)
  let g : E.restrict U.ι ⟶ M.restrict U.ι :=
    α.hom.app E ≫ (restrictFunctor (W.ι ≫ V.ι).isoOpensRange.inv).map gV ≫ α.inv.app M
  refine ⟨U, mem_opensRange_comp_ι hxV hxW, g, ?_⟩
  simp only [g, Category.assoc]
  rw [← α.inv.naturality p]
  dsimp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc, hgV]
  have hnat := α.hom.naturality f
  dsimp only [Functor.comp_map] at hnat
  rw [← reassoc_of% hnat, Iso.hom_inv_id_app, Category.comp_id]

end LocalEpiLifting

section LocalNullhomotopy

/-- A chain map `f : P ⟶ K` that vanishes in all degrees `> k` factors through the brutal
truncation projection `P ⟶ P.stupidTrunc (embeddingUpIntLE k)`. -/
private def descStupidTruncLE {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
    {P K : CochainComplex C ℤ} (k : ℤ) (f : P ⟶ K) (hf : ∀ i : ℤ, k < i → f.f i = 0) :
    P.stupidTrunc (ComplexShape.embeddingUpIntLE k) ⟶ K where
  f i :=
    if hi : i ≤ k then
      (P.stupidTruncXIso (ComplexShape.embeddingUpIntLE k)
        (i := (k - i).natAbs) (i' := i)
        (by simp [Int.natAbs_of_nonneg (sub_nonneg.mpr hi)])).hom ≫ f.f i
    else 0
  comm' i j hij := by
    by_cases hj : j ≤ k
    · have hij' : i + 1 = j := hij
      have hi : i ≤ k := by omega
      rw [dite_eq_left hi, dite_eq_left hj]
      let π := P.πStupidTrunc (ComplexShape.embeddingUpIntLE k)
      have hπi : π.f i = (P.stupidTruncXIso (ComplexShape.embeddingUpIntLE k)
          (i := (k - i).natAbs) (i' := i)
          (by simp [Int.natAbs_of_nonneg (sub_nonneg.mpr hi)])).inv :=
        P.πStupidTruncLE_f k hi
      have hπj : π.f j = (P.stupidTruncXIso (ComplexShape.embeddingUpIntLE k)
          (i := (k - j).natAbs) (i' := j)
          (by simp [Int.natAbs_of_nonneg (sub_nonneg.mpr hj)])).inv :=
        P.πStupidTruncLE_f k hj
      have : IsIso (π.f i) := hπi ▸ inferInstance
      rw [← cancel_epi (π.f i), π.comm_assoc i j, hπj, Iso.inv_hom_id_assoc,
        Category.assoc, hπi, Iso.inv_hom_id_assoc, f.comm]
    · have hkj : k < j := by omega
      rw [dite_eq_right hj, comp_zero]
      split_ifs with hi
      · rw [Category.assoc, f.comm i j, hf j hkj, comp_zero, comp_zero]
      · rw [zero_comp]

private lemma πStupidTruncLE_comp_descStupidTruncLE {C : Type*} [Category* C]
    [HasZeroMorphisms C] [HasZeroObject C] {P K : CochainComplex C ℤ} (k : ℤ) (f : P ⟶ K)
    (hf : ∀ i : ℤ, k < i → f.f i = 0) :
    P.πStupidTrunc (ComplexShape.embeddingUpIntLE k) ≫ descStupidTruncLE k f hf = f := by
  refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
  simp only [HomologicalComplex.comp_f, descStupidTruncLE]
  by_cases hi : i ≤ k
  · rw [dite_eq_left hi, P.πStupidTruncLE_f k hi, Iso.inv_hom_id_assoc]
  · rw [dite_eq_right hi, comp_zero, hf i (by omega)]

/-- Restriction along an open immersion preserves `ExactAt` because `restrictFunctor` is exact. -/
private lemma exactAt_restrict {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    {K : CochainComplex X.Modules ℤ} {j : ℤ} (hK : K.ExactAt j) :
    (((restrictFunctor f).mapHomologicalComplex (.up ℤ)).obj K).ExactAt j := by
  rw [HomologicalComplex.exactAt_iff] at hK ⊢
  exact hK.map (restrictFunctor f)

/-- Restriction along an open immersion preserves `IsStrictlyGE`. -/
private lemma isStrictlyGE_restrict {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (P : CochainComplex X.Modules ℤ) (a : ℤ) [P.IsStrictlyGE a] :
    CochainComplex.IsStrictlyGE (((restrictFunctor f).mapHomologicalComplex (.up ℤ)).obj P) a :=
  (CochainComplex.isStrictlyGE_iff _ a).mpr fun i hi ↦
    (restrictFunctor f).map_isZero (P.isZero_of_isStrictlyGE a i hi)

/-- Restriction along an open immersion preserves `IsStrictlyLE`. -/
private lemma isStrictlyLE_restrict {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (P : CochainComplex X.Modules ℤ) (b : ℤ) [P.IsStrictlyLE b] :
    CochainComplex.IsStrictlyLE (((restrictFunctor f).mapHomologicalComplex (.up ℤ)).obj P) b :=
  (CochainComplex.isStrictlyLE_iff _ b).mpr fun i hi ↦
    (restrictFunctor f).map_isZero (P.isZero_of_isStrictlyLE b i hi)

/-- Induction core for `exists_restrict_homotopy_zero`, inducting on the width `n` of
`[a, a + n]`. -/
private lemma exists_restrict_homotopy_zero_aux :
    ∀ (n : ℕ) {X : Scheme.{u}} {P K : CochainComplex X.Modules ℤ}
      (_hP : isStrictlyPerfect X P) (a : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE (a + n)]
      (_hK : ∀ j ≥ a, K.ExactAt j) (f : P ⟶ K) (x : X),
      ∃ (U : X.Opens), x ∈ U ∧
        Nonempty (Homotopy (((restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).map f) 0)
  | n, X, P, K, hP, a, hge, hle, hK, f, x => by
    let b : ℤ := a + n
    -- In the top degree `b`, `f.f b` lands in `cycles b` and lifts locally along `K.d (b - 1) b`.
    let S := K.sc' (b - 1) b (b + 1)
    have hS : S.Exact :=
      (K.exactAt_iff' (b - 1) b (b + 1) (by simp) (by simp)).mp (hK b (by omega))
    have : Epi S.toCycles := hS.epi_toCycles
    have hfb : f.f b ≫ S.g = 0 := by
      change f.f b ≫ K.d b (b + 1) = 0
      rw [f.comm b (b + 1),
        (P.isZero_of_isStrictlyLE b (b + 1) (by omega)).eq_of_tgt (P.d b (b + 1)) 0, zero_comp]
    let g : P.X b ⟶ S.cycles := S.liftCycles (f.f b) hfb
    obtain ⟨V, hxV, s, hs⟩ :=
      exists_restrict_lift_of_epi (((isStrictlyPerfect_iff P).mp hP).2 b) S.toCycles g x
    let RV := (restrictFunctor V.ι).mapHomologicalComplex (.up ℤ)
    let PV : CochainComplex V.toScheme.Modules ℤ := RV.obj P
    let KV : CochainComplex V.toScheme.Modules ℤ := RV.obj K
    let fV : PV ⟶ KV := RV.map f
    let s' : PV.X b ⟶ KV.X (b - 1) := s
    have hs' : s' ≫ KV.d (b - 1) b = fV.f b := by
      have hcomp := congr_arg (· ≫ (restrictFunctor V.ι).map S.iCycles) hs
      simp only [g, Category.assoc, ← Functor.map_comp, ShortComplex.toCycles_i,
        ShortComplex.liftCycles_i] at hcomp
      exact hcomp
    -- Build the single-degree homotopy supported at `(b, b - 1)` over `V`.
    let homTop : ∀ i j : ℤ, PV.X i ⟶ KV.X j := fun i j ↦
      if h : i = b ∧ j = b - 1 then
        (PV.XIsoOfEq h.1).hom ≫ s' ≫ (KV.XIsoOfEq h.2).inv
      else 0
    have hzeroTop : ∀ i j : ℤ, ¬(ComplexShape.up ℤ).Rel j i → homTop i j = 0 := by
      intro i j hij
      dsimp only [homTop]
      rw [dite_eq_right]
      rintro ⟨rfl, rfl⟩
      exact hij (by simp)
    let Htop : Homotopy (Homotopy.nullHomotopicMap homTop) 0 :=
      Homotopy.nullHomotopy homTop hzeroTop
    let f' : PV ⟶ KV := fV - Homotopy.nullHomotopicMap homTop
    have hf'_b : f'.f b = 0 := by
      have hprev : prevD b homTop = s' ≫ KV.d (b - 1) b := by
        rw [prevD_eq homTop (show (ComplexShape.up ℤ).Rel (b - 1) b by simp)]
        simp [homTop]
      have hnext : dNext b homTop = 0 := by
        rw [dNext_eq homTop (show (ComplexShape.up ℤ).Rel b (b + 1) by simp)]
        simp [homTop]
      change fV.f b - (dNext b homTop + prevD b homTop) = 0
      rw [hnext, hprev, zero_add, hs', sub_self]
    have : PV.IsStrictlyGE a := isStrictlyGE_restrict V.ι P a
    have : PV.IsStrictlyLE b := isStrictlyLE_restrict V.ι P b
    cases n with
    | zero =>
      -- When `n = 0`, `b = a`, so `f'` vanishes in every degree and `Htop` kills `fV`.
      have hf'_zero : f' = 0 := by
        refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
        rcases lt_trichotomy i b with hlt | rfl | hgt
        · exact (PV.isZero_of_isStrictlyGE a i (by omega)).eq_of_src _ _
        · exact hf'_b
        · exact (PV.isZero_of_isStrictlyLE b i hgt).eq_of_src _ _
      have hfV_eq : fV = Homotopy.nullHomotopicMap homTop := sub_eq_zero.mp hf'_zero
      exact ⟨V, hxV, ⟨(Homotopy.ofEq hfV_eq).trans Htop⟩⟩
    | succ m =>
      -- Factor `f'` through the brutal truncation `PV^{≤ a + m}` and apply the IH.
      have hf'_gt : ∀ i : ℤ, a + m < i → f'.f i = 0 := by
        intro i hi
        by_cases hib : i = b
        · exact hib ▸ hf'_b
        · exact (PV.isZero_of_isStrictlyLE b i (by omega)).eq_of_src _ _
      let QV : CochainComplex V.toScheme.Modules ℤ :=
        PV.stupidTrunc (ComplexShape.embeddingUpIntLE (a + m))
      let π : PV ⟶ QV := PV.πStupidTrunc (ComplexShape.embeddingUpIntLE (a + m))
      let fTrunc : QV ⟶ KV := descStupidTruncLE (a + m) f' hf'_gt
      have hπf : π ≫ fTrunc = f' := πStupidTruncLE_comp_descStupidTruncLE (a + m) f' hf'_gt
      have hQV_perf : isStrictlyPerfect V.toScheme QV :=
        isStrictlyPerfect_stupidTrunc_embeddingUpIntLE
          (isStrictlyPerfect_restrict V.ι hP) (a + m)
      have : QV.IsStrictlyGE a := inferInstance
      have : QV.IsStrictlyLE (a + m) := inferInstance
      have hKV_exact : ∀ j ≥ a, KV.ExactAt j := fun j hj ↦ exactAt_restrict V.ι (hK j hj)
      obtain ⟨W, hxW, ⟨Htrunc⟩⟩ := exists_restrict_homotopy_zero_aux m hQV_perf a hKV_exact
        fTrunc (⟨x, hxV⟩ : V.toScheme)
      let RW := (restrictFunctor W.ι).mapHomologicalComplex (.up ℤ)
      have H' : Homotopy (RW.map f') 0 :=
        (Homotopy.ofEq (by rw [← hπf, Functor.map_comp])).trans
          ((Htrunc.compLeft (RW.map π)).trans (Homotopy.ofEq (comp_zero)))
      have HtopW : Homotopy (RW.map (Homotopy.nullHomotopicMap homTop)) 0 :=
        ((restrictFunctor W.ι).mapHomotopy Htop).trans (Homotopy.ofEq (by simp))
      have HfVW : Homotopy (RW.map fV) 0 :=
        (Homotopy.ofEq (show RW.map fV = RW.map f' + RW.map (Homotopy.nullHomotopicMap homTop) by
          rw [← Functor.map_add]; congr 1; simp [f'])).trans
          ((H'.add HtopW).trans (Homotopy.ofEq (add_zero 0)))
      exact exists_restrict_homotopy_zero_of_open hxV hxW HfVW

/-- Every chain map from a strictly perfect complex `P` with `P^i = 0` for `i < a` into a complex
`K` exact in degrees `≥ a` is locally nullhomotopic on `X`. -/
theorem exists_restrict_homotopy_zero {X : Scheme.{u}} {P K : CochainComplex X.Modules ℤ}
    (hP : isStrictlyPerfect X P) (a : ℤ) [P.IsStrictlyGE a]
    (hK : ∀ j ≥ a, K.ExactAt j) (f : P ⟶ K) (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧
      Nonempty (Homotopy (((restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).map f) 0) := by
  obtain ⟨⟨_, b', _, hb'⟩, _⟩ := (isStrictlyPerfect_iff_exists_isStrictlyGE_isStrictlyLE P).mp hP
  let b : ℤ := max a b'
  let n : ℕ := (b - a).toNat
  have hbn : a + n = b := by omega
  have : P.IsStrictlyLE (a + n) :=
    (CochainComplex.isStrictlyLE_iff P (a + n)).mpr fun i hi ↦
      P.isZero_of_isStrictlyLE b' i (by omega)
  exact exists_restrict_homotopy_zero_aux n hP a hK f x

/-- Every chain map from a strictly perfect complex into an acyclic complex is locally
nullhomotopic on `X`. -/
theorem exists_restrict_homotopy_zero_of_acyclic {X : Scheme.{u}} {P K : CochainComplex X.Modules ℤ}
    (hP : isStrictlyPerfect X P) (hK : K.Acyclic) (f : P ⟶ K) (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧
      Nonempty (Homotopy (((restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).map f) 0) := by
  obtain ⟨⟨a, _, ha, _⟩, _⟩ := (isStrictlyPerfect_iff_exists_isStrictlyGE_isStrictlyLE P).mp hP
  exact exists_restrict_homotopy_zero hP a (fun j _ ↦ hK j) f x

end LocalNullhomotopy

section LocalLifting

/-- If `α ≫ mappingCone.inr φ` is nullhomotopic, then `α` lifts up to homotopy along `φ`. -/
private lemma exists_lift_homotopy_of_homotopy_comp_inr {C : Type*} [Category* C] [Preadditive C]
    [HasBinaryBiproducts C] {P M N : CochainComplex C ℤ} {φ : M ⟶ N} {α : P ⟶ N}
    (H : Homotopy (α ≫ CochainComplex.mappingCone.inr φ) 0) :
    ∃ β : P ⟶ M, Nonempty (Homotopy (β ≫ φ) α) := by
  let z : Cochain P (CochainComplex.mappingCone φ) (-1) := Cochain.ofHomotopy H
  have hz : δ (-1) 0 z = Cochain.ofHom (α ≫ CochainComplex.mappingCone.inr φ) := by
    simp [z]
  have hδβ : δ 0 1 (z.comp (CochainComplex.mappingCone.fst φ).val (neg_add_cancel 1)) = 0 := by
    rw [δ_comp z (CochainComplex.mappingCone.fst φ).val (neg_add_cancel 1) 0 2 1
      (zero_add 1) (neg_add_cancel 1) rfl]
    simp [hz]
  let β : P ⟶ M := Cocycle.homOf
    (Cocycle.mk (z.comp (CochainComplex.mappingCone.fst φ).val (neg_add_cancel 1)) 1
      (zero_add 1) hδβ)
  have hβ_ofHom : Cochain.ofHom β =
      z.comp (CochainComplex.mappingCone.fst φ).val (neg_add_cancel 1) := by
    simp [β]
  let h : Cochain P N (-1) := z.comp (CochainComplex.mappingCone.snd φ) (add_zero (-1))
  have hinr_snd : (Cochain.ofHom (α ≫ CochainComplex.mappingCone.inr φ)).comp
      (CochainComplex.mappingCone.snd φ) (add_zero 0) = Cochain.ofHom α := by
    ext p
    simp
  have hα : Cochain.ofHom α = δ (-1) 0 h + Cochain.ofHom (β ≫ φ) := by
    have hδh : δ (-1) 0 h = -Cochain.ofHom (β ≫ φ) + Cochain.ofHom α := by
      rw [δ_comp_zero_cochain z (CochainComplex.mappingCone.snd φ) 0 (neg_add_cancel 1),
        CochainComplex.mappingCone.δ_snd, hz, Cochain.comp_neg, hinr_snd,
        ← Cochain.comp_assoc_of_third_is_zero_cochain z
          (CochainComplex.mappingCone.fst φ).val (Cochain.ofHom φ) (neg_add_cancel 1),
        ← hβ_ofHom, ← Cochain.ofHom_comp]
    rw [hδh]
    abel
  exact ⟨β, ⟨((Cochain.equivHomotopy α (β ≫ φ)).symm ⟨h, hα⟩).symm⟩⟩

/-- **Local lifting of chain maps, sharp form**: if `P` is strictly perfect with `P^i = 0` for
`i < a` and `φ : M ⟶ N` induces epimorphisms on `H^j` and monomorphisms on `H^{j+1}` for every
`j ≥ a`, then every chain map `α : P ⟶ N` lifts locally on `X` to a chain map `β : P|_U ⟶ M|_U`
such that `β ≫ φ|_U` is chain homotopic to `α|_U`. -/
theorem exists_restrict_lift_homotopy_of_epi_mono {X : Scheme.{u}}
    {P M N : CochainComplex X.Modules ℤ} (hP : isStrictlyPerfect X P) (a : ℤ) [P.IsStrictlyGE a]
    (φ : M ⟶ N)
    (hφ : ∀ j ≥ a, Epi (HomologicalComplex.homologyMap φ j) ∧
      Mono (HomologicalComplex.homologyMap φ (j + 1)))
    (α : P ⟶ N) (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U)
      (β : ((restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P ⟶
        ((restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj M),
      Nonempty (Homotopy (β ≫ ((restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).map φ)
        (((restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).map α)) := by
  have hcone : ∀ j ≥ a, (CochainComplex.mappingCone φ).ExactAt j := fun j hj ↦
    (CochainComplex.exactAt_mappingCone_iff φ j).mpr (hφ j hj)
  obtain ⟨U, hxU, ⟨H⟩⟩ := exists_restrict_homotopy_zero hP a hcone
    (α ≫ CochainComplex.mappingCone.inr φ) x
  let RU := (restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)
  have H' : Homotopy (RU.map α ≫ CochainComplex.mappingCone.inr (RU.map φ)) 0 := by
    have hcomp : RU.map α ≫ CochainComplex.mappingCone.inr (RU.map φ) =
        RU.map (α ≫ CochainComplex.mappingCone.inr φ) ≫
          (CochainComplex.mappingCone.mapHomologicalComplexIso φ (restrictFunctor U.ι)).hom := by
      rw [Functor.map_comp, Category.assoc, CochainComplex.mappingCone.map_inr]
    exact (Homotopy.ofEq hcomp).trans ((H.compRight _).trans (Homotopy.ofEq (zero_comp)))
  obtain ⟨β, hβ⟩ := exists_lift_homotopy_of_homotopy_comp_inr H'
  exact ⟨U, hxU, β, hβ⟩

/-- **Local lifting of chain maps** (Stacks Tag 08C8): if `P` is strictly perfect with `P^i = 0`
for `i < a` and `φ : M ⟶ N` induces an epimorphism on `H^a` and isomorphisms on `H^j` for all
`j > a`, then every chain map `α : P ⟶ N` lifts locally on `X` to a chain map `β : P|_U ⟶ M|_U`
such that `β ≫ φ|_U` is chain homotopic to `α|_U`. -/
theorem exists_restrict_lift_homotopy {X : Scheme.{u}}
    {P M N : CochainComplex X.Modules ℤ} (hP : isStrictlyPerfect X P) (a : ℤ) [P.IsStrictlyGE a]
    (φ : M ⟶ N)
    (hφ_epi : Epi (HomologicalComplex.homologyMap φ a))
    (hφ_iso : ∀ j > a, IsIso (HomologicalComplex.homologyMap φ j))
    (α : P ⟶ N) (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U)
      (β : ((restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P ⟶
        ((restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj M),
      Nonempty (Homotopy (β ≫ ((restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).map φ)
        (((restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).map α)) := by
  refine exists_restrict_lift_homotopy_of_epi_mono hP a φ (fun j hj ↦ ?_) α x
  have : IsIso (HomologicalComplex.homologyMap φ (j + 1)) := hφ_iso (j + 1) (by omega)
  refine ⟨?_, inferInstance⟩
  rcases eq_or_lt_of_le hj with rfl | hlt
  · exact hφ_epi
  · have := hφ_iso j hlt
    infer_instance

/-- Every chain map from a strictly perfect complex lifts locally up to homotopy across any
quasi-isomorphism. -/
theorem exists_restrict_lift_homotopy_of_quasiIso {X : Scheme.{u}}
    {P M N : CochainComplex X.Modules ℤ} (hP : isStrictlyPerfect X P)
    (φ : M ⟶ N) [QuasiIso φ] (α : P ⟶ N) (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U)
      (β : ((restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P ⟶
        ((restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj M),
      Nonempty (Homotopy (β ≫ ((restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).map φ)
        (((restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).map α)) := by
  obtain ⟨⟨a, _, ha, _⟩, _⟩ := (isStrictlyPerfect_iff_exists_isStrictlyGE_isStrictlyLE P).mp hP
  exact exists_restrict_lift_homotopy hP a φ inferInstance (fun _ _ ↦ inferInstance) α x

end LocalLifting

section LocalDerivedMaps

/-- If `f ≫ s` is nullhomotopic for a quasi-isomorphism `s : M ⟶ M'`, then `f : P ⟶ M` factors
through the acyclic complex `(mappingCone s)⟦-1⟧`. -/
private lemma exists_acyclic_factorization_of_homotopy_comp_zero {C : Type*} [Category* C]
    [Abelian C] {P M M' : CochainComplex C ℤ} {f : P ⟶ M} {s : M ⟶ M'} [QuasiIso s]
    (H : Homotopy (f ≫ s) 0) :
    ∃ (A : CochainComplex C ℤ), A.Acyclic ∧ ∃ (γ : P ⟶ A) (p : A ⟶ M), γ ≫ p = f := by
  have heq : δ (-1) 0 (-Cochain.ofHomotopy H) +
      (Cocycle.ofHom f).val.comp (Cochain.ofHom s) (add_zero 0) = 0 := by
    simp [Cochain.ofHom_comp]
  let γ₀ : Cocycle P (CochainComplex.mappingCone s) (-1) :=
    CochainComplex.mappingCone.liftCocycle s (Cocycle.ofHom f) (-Cochain.ofHomotopy H)
      (neg_add_cancel 1) heq
  let γ : P ⟶ (CochainComplex.mappingCone s)⟦(-1 : ℤ)⟧ :=
    -(Cocycle.equivHomShift.symm γ₀)
  let p : (CochainComplex.mappingCone s)⟦(-1 : ℤ)⟧ ⟶ M :=
    (Cocycle.equivHomShift' (-1) 1 (add_neg_cancel 1)).symm (CochainComplex.mappingCone.fst s)
  refine ⟨(CochainComplex.mappingCone s)⟦(-1 : ℤ)⟧,
    ((CochainComplex.mappingCone s).acyclic_shift_iff (-1)).2
      ((CochainComplex.quasiIso_iff_acyclic_mappingCone s).mp inferInstance),
    γ, p, ?_⟩
  refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
  have hγ : γ.f i = -(γ₀.val.v i (i - 1) (by omega) ≫
      ((CochainComplex.mappingCone s).shiftFunctorObjXIso (-1) i (i - 1) (by omega)).inv) := by
    simp only [γ, HomologicalComplex.neg_f_apply, Cocycle.equivHomShift_symm_apply,
      Cocycle.homOf_f, Cocycle.rightShift_coe]
    rw [Cochain.rightShift_v _ (-1) 0 (zero_add (-1)) i i (add_zero i) (i - 1) (by omega)]
  have hp : p.f i = -(((CochainComplex.mappingCone s).shiftFunctorObjXIso (-1) i (i - 1)
      (by omega)).hom ≫ (CochainComplex.mappingCone.fst s).val.v (i - 1) i (by omega)) := by
    simp only [p, Cocycle.equivHomShift'_symm_apply, Cocycle.homOf_f, Cocycle.leftShift_coe]
    rw [Cochain.leftShift_v _ (-1) 0 (add_neg_cancel 1) i i (add_zero i) (i - 1) (by omega)]
    have hsign : ((-1 : ℤ) * 0 + (-1 : ℤ) * (-1 - 1) / 2).negOnePow = -1 := by decide
    rw [hsign, Units.neg_smul, one_smul]
  rw [HomologicalComplex.comp_f, hγ, hp, Preadditive.neg_comp, Preadditive.comp_neg, neg_neg,
    Category.assoc, Iso.inv_hom_id_assoc]
  simp [γ₀]

/-- **Local homotopy uniqueness** (Stacks Tag 08C9, first half): if two chain maps
`f₁, f₂ : P ⟶ M` from a strictly perfect complex `P` have the same image in `D(X.Modules)`, then
they are locally chain homotopic on `X`. -/
theorem exists_restrict_homotopy_of_Q_map_eq {X : Scheme.{u}} [HasDerivedCategory.{v} X.Modules]
    {P M : CochainComplex X.Modules ℤ} (hP : isStrictlyPerfect X P) (f₁ f₂ : P ⟶ M)
    (hf : DerivedCategory.Q.map f₁ = DerivedCategory.Q.map f₂) (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧
      Nonempty (Homotopy
        (((restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).map f₁)
        (((restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).map f₂)) := by
  -- Pass to `HomotopyCategory` and use the left calculus of fractions for `DerivedCategory.Qh`.
  let K := HomotopyCategory.quotient X.Modules (.up ℤ)
  have hQh : DerivedCategory.Qh.map (K.map (f₁ - f₂)) = 0 := by
    have hnat := (DerivedCategory.quotientCompQhIso X.Modules).hom.naturality (f₁ - f₂)
    have hQ0 : DerivedCategory.Q.map (f₁ - f₂) = 0 := by
      rw [Functor.map_sub, hf, sub_self]
    simp only [Functor.comp_map, hQ0] at hnat
    exact (cancel_mono ((DerivedCategory.quotientCompQhIso X.Modules).hom.app M)).mp
      (hnat.trans (by simp))
  rw [← DerivedCategory.Qh.map_zero] at hQh
  obtain ⟨M'h, sh, hsh, hfac⟩ := (MorphismProperty.map_eq_iff_postcomp DerivedCategory.Qh
    (HomotopyCategory.quasiIso X.Modules (.up ℤ)) (K.map (f₁ - f₂)) 0).mp hQh
  obtain ⟨M', rfl⟩ := HomotopyCategory.quotient_obj_surjective M'h
  obtain ⟨s, rfl⟩ := K.map_surjective sh
  have : QuasiIso s := by
    rwa [← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff]
  have H : Homotopy ((f₁ - f₂) ≫ s) 0 := HomotopyCategory.homotopyOfEq _ _ (by
    simpa [K] using hfac)
  obtain ⟨A, hA, γ, p, hγp⟩ := exists_acyclic_factorization_of_homotopy_comp_zero H
  obtain ⟨U, hxU, ⟨Hγ⟩⟩ := exists_restrict_homotopy_zero_of_acyclic hP hA γ x
  let RU := (restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)
  have Hsub : Homotopy (RU.map f₁ - RU.map f₂) 0 :=
    (Homotopy.ofEq (by rw [← Functor.map_sub, ← hγp, Functor.map_comp])).trans
      ((Hγ.compRight (RU.map p)).trans (Homotopy.ofEq zero_comp))
  refine ⟨U, hxU, ⟨(Homotopy.ofEq (show RU.map f₁ = (RU.map f₁ - RU.map f₂) + RU.map f₂ by
    abel)).trans ((Hsub.add (Homotopy.refl (RU.map f₂))).trans (Homotopy.ofEq (zero_add _)))⟩⟩

/-- **Local chain representatives of derived maps** (Stacks Tag 08C9, second half): every morphism
`g : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj M` in `D(X.Modules)` from a strictly perfect
complex `P` is locally on `X` represented by an actual morphism of cochain complexes
`β : P|_U ⟶ M|_U`. -/
theorem exists_restrict_mapDerivedCategory_eq {X : Scheme.{u}} [HasDerivedCategory.{v} X.Modules]
    {P M : CochainComplex X.Modules ℤ} (hP : isStrictlyPerfect X P)
    (g : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj M) (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U)
      (β : ((restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P ⟶
        ((restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj M),
      ∀ [HasDerivedCategory.{v'} U.toScheme.Modules],
        (restrictFunctor U.ι).mapDerivedCategory.map g =
          (restrictFunctor U.ι).mapDerivedCategoryFactors.hom.app P ≫
            DerivedCategory.Q.map β ≫
            (restrictFunctor U.ι).mapDerivedCategoryFactors.inv.app M := by
  obtain ⟨M', h, s, hs, rfl⟩ := DerivedCategory.left_fac g
  rw [DerivedCategory.isIso_Q_map_iff_quasiIso] at hs
  obtain ⟨U, hxU, β, ⟨H⟩⟩ := exists_restrict_lift_homotopy_of_quasiIso hP s h x
  refine ⟨U, hxU, β, ?_⟩
  intro _
  let F := restrictFunctor U.ι
  let RU := F.mapHomologicalComplex (.up ℤ)
  have hQβ : DerivedCategory.Q.map β ≫ DerivedCategory.Q.map (RU.map s) =
      DerivedCategory.Q.map (RU.map h) := by
    rw [← DerivedCategory.Q.map_comp]
    exact DerivedCategory.Q_map_eq_of_homotopy U.toScheme.Modules H
  have : IsIso (F.mapDerivedCategory.map (DerivedCategory.Q.map s)) := inferInstance
  rw [Functor.map_comp, Functor.map_inv, ← cancel_mono (F.mapDerivedCategory.map
      (DerivedCategory.Q.map s)), Category.assoc, IsIso.inv_hom_id, Category.comp_id,
    ← cancel_mono (F.mapDerivedCategoryFactors.hom.app M'), Category.assoc, Category.assoc,
    Category.assoc]
  rw [F.mapDerivedCategoryFactors_hom_naturality s, Iso.inv_hom_id_app_assoc,
    hQβ, F.mapDerivedCategoryFactors_hom_naturality h]

end LocalDerivedMaps

end

end AlgebraicGeometry.Scheme.Modules
