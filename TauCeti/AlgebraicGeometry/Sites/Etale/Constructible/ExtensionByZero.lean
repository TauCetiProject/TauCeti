/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import TauCeti.AlgebraicGeometry.Sites.Etale.Constructible
public import TauCeti.AlgebraicGeometry.Sites.Etale.ExtensionByZero
public import TauCeti.AlgebraicGeometry.Sites.Etale.FiniteLisse.Products
public import TauCeti.AlgebraicGeometry.Sites.Etale.GeometricPoint
public import TauCeti.CategoryTheory.Sites.Point.ConstantSheaf

/-!
# Constructibility of extensions by zero

Let `j : Y ⟶ X` be a quasi-compact open immersion and `F` a constructible étale sheaf of
`Λ`-modules on `Y`. The extension by zero `j_! F` is constructible on `X`. On an affine open `V`
of `X`, the trace `j(Y) ∩ V` is a retrocompact open of `V`; on it `j_! F` restricts to `F`
(`j^* j_! ≅ 𝟭`), and on the closed complement it pulls back to zero, which is finite lisse. This
open–closed gluing is `CategoryTheory.Sheaf.IsConstructibleOn.of_isFiniteLisse_sdiffι`.

Extension by zero does not preserve finite lisse sheaves: when the image of `j` is not closed,
`j_!` of a nonzero constant sheaf is not finite lisse, since an étale neighbourhood of a point in
the closure of the image but outside it has a stratum where the stalks are zero and one where
they are not.

## Main results

* `CategoryTheory.Sheaf.IsConstructibleOn.of_isFiniteLisse_sdiffι`: **open–closed gluing.** A sheaf
  constructible on a retrocompact open `W ≤ U` and finite lisse on the reduced closed complement
  `U \ W` is constructible on `U`.
* `AlgebraicGeometry.Scheme.constructibleSheaf_smallEtaleExtensionByZero`: extension by zero along
  a quasi-compact open immersion preserves constructible sheaves.
* `AlgebraicGeometry.Scheme.not_isFiniteLisse_smallEtaleExtensionByZero_constantSheaf`: if a point
  lies in the closure of the image of an open immersion `j` but not in the image, then `j_!` of a
  nonzero constant sheaf is not finite lisse.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IX, §2.
* The Stacks Project, Section 59.71, Constructible sheaves.
-/

public section

universe u

open CategoryTheory Limits Topology Set.Notation AlgebraicGeometry Scheme

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}} {Λ : Type u} [Ring Λ]
  {F : Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ)} {U W : X.Opens}

/-- **Open–closed gluing of constructibility.** Let `W ≤ U` be opens of `X` with the trace of `W`
on `U` retrocompact. A sheaf constructible on `W` whose pullback to the reduced closed subscheme
on `U \ W` is finite lisse is constructible on `U`. -/
theorem IsConstructibleOn.of_isFiniteLisse_sdiffι (hWU : W ≤ U)
    (hW : IsRetrocompact ((U : Set X) ↓∩ (W : Set X))) (hF : F.IsConstructibleOn W)
    (hC : (((ConstructibleStratification.sdiffι U W).smallEtalePullback
      (ModuleCat.{u} Λ)).obj F).IsFiniteLisse) :
    F.IsConstructibleOn U := by
  obtain ⟨T, hT⟩ := isConstructibleOn_iff.mp hF
  exact isConstructibleOn_iff.mpr ⟨T.extend hWU hW, fun | none => hC | some i => hT i⟩

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme

open CategoryTheory.Sheaf TauCeti.AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} {Λ : Type u} [Ring Λ]

/-- **Extension by zero preserves constructibility.** For a quasi-compact open immersion
`j : Y ⟶ X` and a constructible étale sheaf of `Λ`-modules `F` on `Y`, the extension by zero
`j_! F` is constructible on `X`. -/
theorem constructibleSheaf_smallEtaleExtensionByZero (j : Y ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] {F : Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)}
    (hF : Y.constructibleSheaf Λ F) :
    X.constructibleSheaf Λ ((j.smallEtaleExtensionByZero (ModuleCat.{u} Λ)).obj F) := by
  refine constructibleSheaf_iff.mpr fun V hV ↦ ?_
  have hWV : j ''ᵁ (j ⁻¹ᵁ V) ≤ V := j.image_preimage_le V
  have hc : IsCompact (j ⁻¹ᵁ V : Set Y) := j.isCompact_preimage hV.isCompact
  -- `F` is constructible on the quasi-compact quasi-separated open `j⁻¹(V)`.
  have hFV : F.IsConstructibleOn (j ⁻¹ᵁ V) := by
    refine isConstructibleOn_of_isCompact hc
      (j.isOpenEmbedding.isQuasiSeparated_iff.mpr (hV.isQuasiSeparated.of_subset hWV))
      fun y hy ↦ ?_
    obtain ⟨W, hW, hyW, hWV⟩ := exists_isAffineOpen_mem_and_subset hy
    exact ⟨W, hyW, hWV, constructibleSheaf_iff.mp hF W hW⟩
  have : QuasiSeparatedSpace (V : Set X) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ V.isOpen).mp hV.isQuasiSeparated
  refine IsConstructibleOn.of_isFiniteLisse_sdiffι hWV ?_
    ((isConstructibleOn_image_iff j _).mpr (hFV.of_iso
      ((j.smallEtaleExtensionByZeroCompSmallEtalePullbackIso _).app F).symm)) ?_
  · refine IsCompact.isRetrocompact ?_ ((j ''ᵁ (j ⁻¹ᵁ V)).isOpen.preimage continuous_subtypeVal)
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, Set.inter_eq_right.mpr hWV]
    exact hc.image j.continuous
  · -- On the closed complement of `j(Y) ∩ V` in `V`, the pullback of `j_! F` is zero.
    refine ObjectProperty.prop_of_isZero _
      (j.isZero_smallEtalePullback_smallEtaleExtensionByZero_obj _ ?_ F)
    rw [ConstructibleStratification.range_sdiffι]
    refine Set.disjoint_left.mpr fun x hx ⟨y, hy⟩ ↦ hx.2 ⟨y, ?_, hy⟩
    subst hy
    exact hx.1

/-- **Extension by zero is not lisse across the boundary.** Let `j : Y ⟶ X` be an open immersion
and `x` a point in the closure of the image of `j` but not in the image. For a nonzero
`Λ`-module `M`, the extension by zero `j_! M` of the constant sheaf on `M` is not finite lisse:
an étale neighbourhood of `x` on which it were constant would have zero stalk over `x` and stalk
`M` over a point of the image of `j`. -/
theorem not_isFiniteLisse_smallEtaleExtensionByZero_constantSheaf (j : Y ⟶ X)
    [IsOpenImmersion j] {x : X} (hx : x ∈ closure (Set.range j)) (hxj : x ∉ Set.range j)
    (M : ModuleCat.{u} Λ) [Nontrivial M] :
    ¬ ((j.smallEtaleExtensionByZero (ModuleCat.{u} Λ)).obj
      ((constantSheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)).obj M)).IsFiniteLisse := by
  intro h
  set G := (j.smallEtaleExtensionByZero (ModuleCat.{u} Λ)).obj
    ((constantSheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)).obj M)
  obtain ⟨ι, U, u, _, hu, hU⟩ := (isFiniteLisse_iff G).mp h
  obtain ⟨i, p₀, hp₀⟩ := Set.mem_iUnion.mp (hu.symm ▸ Set.mem_univ x)
  obtain ⟨N, -, ⟨e⟩⟩ := hU i
  have hopen : IsOpen (Set.range (u i)) :=
    (isOpenMap_of_generalizingMap (u i) (Flat.generalizingMap (u i))).isOpen_range
  obtain ⟨_, ⟨p₁, hp₁⟩, ⟨y, rfl⟩⟩ := mem_closure_iff.mp hx _ hopen ⟨p₀, hp₀⟩
  -- At the geometric point over any `p : U i`, the stalk of `G` is `N`.
  have hN (p : U i) :
      Nonempty ((etaleStalk Λ ((GeometricPoint.ofPoint p).hom ≫ u i)).obj G ≅ N) :=
    ⟨(((u i).smallEtalePullbackCompEtaleStalkIso Λ (GeometricPoint.ofPoint p).hom).app G).symm ≪≫
      (etaleStalk Λ (GeometricPoint.ofPoint p).hom).mapIso e ≪≫
      (pointSmallEtale (GeometricPoint.ofPoint p).hom).sheafFiberConstantSheafIso N⟩
  -- Over `p₀`, which maps to `x`, the stalk of `G` vanishes.
  have hN0 : IsZero N := by
    refine IsZero.of_iso ?_ (hN p₀).some.symm
    refine j.isZero_sheafFiber_smallEtaleExtensionByZero_obj _ (fun s' h ↦ hxj ⟨s' default, ?_⟩) _
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply, GeometricPoint.ofPoint_hom_apply, hp₀]
  -- Over `p₁`, the geometric point factors through `j`, where the stalk of `G` is `M`.
  have hrange : Set.range ((GeometricPoint.ofPoint p₁).hom ≫ u i) ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply, GeometricPoint.ofPoint_hom_apply, hp₁]
    exact ⟨y, rfl⟩
  have ht : IsOpenImmersion.lift j _ hrange ≫ j = (GeometricPoint.ofPoint p₁).hom ≫ u i :=
    IsOpenImmersion.lift_fac _ _ _
  have eM : (etaleStalk Λ (IsOpenImmersion.lift j _ hrange ≫ j)).obj G ≅ M :=
    (j.smallEtaleExtensionByZeroCompSheafFiberIso (ModuleCat.{u} Λ) _).app _ ≪≫
      (pointSmallEtale (IsOpenImmersion.lift j _ hrange)).sheafFiberConstantSheafIso M
  rw [ht] at eM
  exact not_subsingleton M
    (ModuleCat.isZero_iff_subsingleton.mp (hN0.of_iso (eM.symm ≪≫ (hN p₁).some)))

end AlgebraicGeometry.Scheme
