/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import TauCeti.AlgebraicGeometry.LineBundle.Endomorphisms
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.AlgebraicGeometry.Modules.Restriction.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.Limit

/-!
# Equalities of line-bundle morphisms over a limit of schemes

Let `F : I ⥤ Scheme` be a cofiltered diagram with affine transition morphisms and limit cone `c`,
and let `i` be a stage with `F i` quasi-compact. Two morphisms `a b : M ⟶ N` of line bundles on
`F i` whose pullbacks to the limit agree already have equal pullbacks to some later stage
`j ⟶ i`. The same holds simultaneously for any finite family of such equalities, at one common
stage. Equality need not hold at the stage `i` itself: on `Spec k[ε]/(ε²)`, multiplication by
`1 + ε` and by `1` on the trivial bundle differ, yet both pull back to the identity along
`Spec k ⟶ Spec k[ε]/(ε²)`.

This is the uniqueness half of the finite-stage description of line bundles on a limit
(Stacks, Lemma 32.10.2, 01ZR): it lets a construction on the limit that is descended to a
stage be compared with any other descended construction after passing to a common refinement.
Conversely, every morphism between the pullbacks to the limit of two line bundles on a stage
of a cofiltered limit of quasi-compact quasi-separated schemes with affine transitions descends
to a refinement; this is the existence half (Stacks, Lemma 32.10.2, 01ZR, part (2)), and it
applies to arbitrary module maps, not only isomorphisms.

The proof reduces to functions. Each point of `F i` has an affine open neighbourhood `U` on which
both `M` and `N` are trivial, and the trivializations identify `a` and `b` over `U` with
multiplication by functions on `U`; pulling back along any morphism pulls back these functions.
Mathlib's `AlgebraicGeometry.exists_app_map_eq_map_of_isLimit` makes functions on the
quasi-compact `U` that agree on the limit agree at some stage, and finitely many such `U` cover
`F i`.

## Main results

* `TauCeti.AlgebraicGeometry.InvertibleSheaf.exists_pullback_map_eq_of_isLimit`: morphisms of
  line bundles with equal pullbacks to the limit have equal pullbacks to some stage;
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.exists_forall_pullback_map_eq_of_isLimit`: the same
  for a finite family of pairs of morphisms, at one common stage.
* `CategoryTheory.Limits.IsLimit.exists_pullback_map_eq_of_invertibleSheaf`: every morphism
  between pullbacks to the limit of line bundles on a stage comes from some later stage.

## References

* The Stacks Project, Lemma 32.10.2 (01ZR).
* A. Grothendieck, *EGA IV₃*, §8.5.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

open _root_.AlgebraicGeometry.Scheme.Modules hiding pullback pullbackComp pullbackId
open MonoidalCategory

variable {I : Type u} [SmallCategory I] [IsCofiltered I] {F : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (F.map f)] {c : Cone F} (hc : IsLimit c)

include hc in
/-- **Equalities of line-bundle morphisms descend to a finite stage.** For a cofiltered diagram
`F` of schemes with affine transition morphisms and a limit cone `c`, two morphisms of line bundles
on a quasi-compact stage `F i` whose pullbacks to the limit agree already have equal pullbacks to
`F j` along `F.map f` for some `f : j ⟶ i`. -/
@[stacks 01ZR "injectivity on morphisms, for invertible modules"]
theorem exists_pullback_map_eq_of_isLimit {i : I} [CompactSpace (F.obj i)]
    {M N : InvertibleSheaf (F.obj i)} {a b : M ⟶ N}
    (hab : (pullback (c.π.app i)).map a = (pullback (c.π.app i)).map b) :
    ∃ (j : I) (f : j ⟶ i), (pullback (F.map f)).map a = (pullback (F.map f)).map b := by
  rw [pullback_map_eq_pullback_map_iff] at hab
  -- Around every point, trivialize `M` and `N` on an affine open `U`, so that `a` and `b` become
  -- multiplication by functions on `U`; these agree at the limit, hence at some stage.
  have key (x : F.obj i) : ∃ (U : (F.obj i).Opens) (_ : x ∈ U)
      (eM : 𝟙_ U.toScheme.Modules ≅ M.obj.restrict U.ι)
      (eN : 𝟙_ U.toScheme.Modules ≅ N.obj.restrict U.ι) (ra rb : Γ(U, ⊤))
      (_ : (restrictFunctor U.ι).map a.hom = eM.inv ≫ globalSectionsSmul _ ra ≫ eN.hom)
      (_ : (restrictFunctor U.ι).map b.hom = eM.inv ≫ globalSectionsSmul _ rb ≫ eN.hom)
      (j : I) (f : j ⟶ i),
        (F.map f).app U (U.topIso.hom ra) = (F.map f).app U (U.topIso.hom rb) := by
    obtain ⟨U, hU, hxU, ⟨eM⟩, ⟨eN⟩⟩ := exists_isAffineOpen_mem_trivializations M.obj N.obj x
    obtain ⟨ra, ha, -⟩ :=
      existsUnique_eq_inv_comp_globalSectionsSmul_comp_hom eM eN ((restrictFunctor U.ι).map a.hom)
    obtain ⟨rb, hb, -⟩ :=
      existsUnique_eq_inv_comp_globalSectionsSmul_comp_hom eM eN ((restrictFunctor U.ι).map b.hom)
    obtain ⟨j, f, hf⟩ := exists_app_map_eq_map_of_isLimit F c hc hU.isCompact _ _
      ((restrictFunctor_map_pullback_map_eq_iff (c.π.app i) eM eN ha hb).mp (by rw [hab]))
    exact ⟨U, hxU, eM, eN, ra, rb, ha, hb, j, f, hf⟩
  choose U hxU eM eN ra rb ha hb j f hf using key
  -- Finitely many of these opens cover the quasi-compact `F i`; pass to a common stage `k`.
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun x ↦ (U x : Set (F.obj i)))
    fun x ↦ (U x).isOpen.mem_nhds (hxU x)
  have hcov : ⨆ x : t, U x = ⊤ := by
    refine top_unique fun y _ ↦ ?_
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp (ht.ge (Set.mem_univ y))
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hy⟩
  obtain ⟨k, fk, g, hg⟩ := IsCofiltered.wideCospan fun x : t ↦ f x.val
  refine ⟨k, fk, (pullback_map_eq_pullback_map_iff _).mpr ?_⟩
  refine hom_ext_of_iSup_eq_top (fun x : t ↦ F.map fk ⁻¹ᵁ U x)
    (by rw [← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]) fun x ↦ ?_
  rw [restrictFunctor_map_pullback_map_eq_iff _ (eM x) (eN x) (ha x) (hb x), ← hg x, F.map_comp,
    Scheme.Hom.comp_app]
  -- The composite acts on functions on `U x` by `F.map (f x)` followed by a further pullback.
  exact congrArg (fun s ↦ (F.map _).app _ s) (hf x)

include hc in
/-- **Finitely many equalities of line-bundle morphisms descend to one common stage.** For a
cofiltered diagram `F` of schemes with affine transition morphisms and a limit cone `c`, a finite
family of pairs of morphisms of line bundles on a quasi-compact stage `F i`, each pair with equal
pullbacks to the limit, has equal pullbacks to `F j` along `F.map f` for one `f : j ⟶ i`. For the
empty family any stage over `i` works. -/
theorem exists_forall_pullback_map_eq_of_isLimit {i : I} [CompactSpace (F.obj i)] {ι : Type*}
    [Finite ι] {M N : ι → InvertibleSheaf (F.obj i)} {a b : ∀ k, M k ⟶ N k}
    (hab : ∀ k, (pullback (c.π.app i)).map (a k) = (pullback (c.π.app i)).map (b k)) :
    ∃ (j : I) (f : j ⟶ i),
      ∀ k, (pullback (F.map f)).map (a k) = (pullback (F.map f)).map (b k) := by
  choose j f hf using fun k ↦ exists_pullback_map_eq_of_isLimit hc (hab k)
  obtain ⟨l, fl, g, hg⟩ := IsCofiltered.wideCospan f
  refine ⟨l, fl, fun k ↦ ?_⟩
  rw [← hg k, F.map_comp,
    ← NatIso.naturality_1 (pullbackComp _ _) (a k),
    ← NatIso.naturality_1 (pullbackComp _ _) (b k),
    Functor.comp_map, Functor.comp_map, hf k]

end TauCeti.AlgebraicGeometry.InvertibleSheaf

namespace CategoryTheory.Limits.IsLimit

open AlgebraicGeometry TauCeti.AlgebraicGeometry

local notation "PB" => InvertibleSheaf.pullback

/-- Every morphism between line bundles pulled back from stage `i` of a cofiltered limit of
qcqs schemes with affine transitions comes from a refinement `j ⟶ i`. The equality at the
limit uses the canonical comparison of the two pullbacks on the underlying modules. -/
theorem exists_pullback_map_eq_of_invertibleSheaf {I : Type u} [Category.{u} I] [IsCofiltered I]
    {D : I ⥤ Scheme.{u}} [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {c : Cone D} (hc : IsLimit c) {i : I} {L M : InvertibleSheaf (D.obj i)}
    (a : (PB (c.π.app i)).obj L ⟶ (PB (c.π.app i)).obj M) :
    ∃ (j : I) (f : j ⟶ i) (b : (PB (D.map f)).obj L ⟶ (PB (D.map f)).obj M),
      let e := Scheme.Modules.pullbackComp (c.π.app j) (D.map f) ≪≫
        Scheme.Modules.pullbackCongr (c.w f)
      e.inv.app L.obj ≫ ((PB (c.π.app j)).map b).hom ≫ e.hom.app M.obj = a.hom := by
  obtain ⟨j, f, b, hb⟩ := hc.exists_pullback_map_eq_of_finiteLocallyFree
    ((InvertibleSheaf.toFiniteLocallyFree _).obj L) ((InvertibleSheaf.toFiniteLocallyFree _).obj M)
    a.hom
  exact ⟨j, f, ObjectProperty.homMk b, hb⟩

end CategoryTheory.Limits.IsLimit
