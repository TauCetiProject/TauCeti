/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.Cohomology.Affine
public import TauCeti.AlgebraicGeometry.Cohomology.PushforwardAcyclic.Affine
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import TauCeti.AlgebraicGeometry.Scheme.Opens
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Functor
public import TauCeti.Topology.Sheaves.Leray.Basic
import Mathlib.Algebra.Category.Grp.Zero
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Colimits

/-!
# Čech cohomology of quasi-coherent sheaves for affine covers

Let `X` be a scheme and let `M` be a quasi-coherent sheaf of modules on `X`. Then `M` has no
cohomology in positive degrees on affine opens
(`AlgebraicGeometry.Scheme.Modules.subsingleton_cohomologyOn_succ_of_isAffineOpen`). So every
finite open cover `U` of `X` whose nonempty finite intersections are affine is a Leray cover for
`M`, and by Leray's theorem (`TauCeti.Topology.homologyCechComplexIsoH`) the Čech cohomology
`Hⁿ(U, M)` of the underlying abelian sheaf of `M` is isomorphic to the cohomology `Hⁿ(X, M)`.
When `X` has affine diagonal, for instance when it is separated, finite intersections of affine
opens are affine (`AlgebraicGeometry.IsAffineOpen.biInf`), so `Hⁿ(X, M)` can be computed from the
Čech complex of any finite affine open cover.

The isomorphism is natural in the quasi-coherent sheaf `M`. In particular it intertwines the map
on Čech cohomology induced by multiplication by a global function `r` on `M` with the action of
`r` on `Hⁿ(X, M)` (`Scheme.Modules.cohomologyModule`), so it is compatible with the module
structures of both sides over the ring of global functions, and hence over any base ring.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.homologyCechComplexIsoCohomology`: for a finite open cover `U`
  of `X` with affine nonempty finite intersections, `Hⁿ(U, M) ≅ Hⁿ(X, M)` for every `n`;
* `AlgebraicGeometry.Scheme.Modules.homologyMap_comp_homologyCechComplexIsoCohomology_hom`: its
  naturality in `M`;
* `AlgebraicGeometry.Scheme.Modules.homologyCechComplexIsoCohomology_hom_globalSectionsSmul`: its
  compatibility with the action of global functions;
* `AlgebraicGeometry.Scheme.Modules.exists_mono_isQuasicoherent_subsingleton_cohomology`: on a
  quasi-compact scheme with affine diagonal, every quasi-coherent sheaf embeds into a
  quasi-coherent sheaf with no cohomology in positive degrees, the step of a dimension-shifting
  argument.

## References

* R. Hartshorne, *Algebraic Geometry*, Theorem III.4.5 and Exercise III.4.1.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
  (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (s.inf U))

include hU in
/-- A quasi-coherent sheaf has no cohomology in positive degrees on a nonempty finite intersection
of members of `U`, which is affine. -/
private lemma subsingleton_cohomologyOn_inf_succ (M : X.Modules) [M.IsQuasicoherent]
    (s : Finset ι) (hs : s.Nonempty) (k : ℕ) : Subsingleton (cohomologyOn M (k + 1) (s.inf U)) :=
  subsingleton_cohomologyOn_succ_of_isAffineOpen M (hU s hs) k

variable [Finite ι] (hcover : ⨆ i, U i = ⊤)

/-- **Čech cohomology computes the cohomology of a quasi-coherent sheaf.** Let `X` be a scheme,
`M` a quasi-coherent sheaf of modules on `X`, and `U` a finite family of opens
covering `X` whose nonempty finite intersections are affine, for instance a finite affine open
cover when `X` has affine diagonal. Then the Čech cohomology `Hⁿ(U, M)` of the underlying abelian
sheaf of `M` is isomorphic to `Hⁿ(X, M)`, for every `n`, naturally in `M`
(`homologyMap_comp_homologyCechComplexIsoCohomology_hom`). -/
def homologyCechComplexIsoCohomology (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    ((cechComplexFunctor U).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj).homology n ≅
      AddCommGrpCat.of (Cohomology M n) :=
  TauCeti.Topology.homologyCechComplexIsoH U hcover _
    (subsingleton_cohomologyOn_inf_succ U hU M) n

/-- The comparison of Čech cohomology for a finite cover with affine intersections with the
cohomology of a quasi-coherent sheaf is natural in the sheaf. -/
@[reassoc]
theorem homologyMap_comp_homologyCechComplexIsoCohomology_hom {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((cechComplexFunctor U).map ((SheafOfModules.toSheaf X.ringCatSheaf).map f).hom) n ≫
        (homologyCechComplexIsoCohomology U hU hcover N n).hom =
      (homologyCechComplexIsoCohomology U hU hcover M n).hom ≫ (cohomologyFunctor X n).map f :=
  TauCeti.Topology.homologyMap_comp_homologyCechComplexIsoH_hom U hcover _ _ _ n

/-- The comparison of Čech cohomology for a finite cover with affine intersections with the
cohomology of a quasi-coherent sheaf `M` is linear over the global functions: it carries the map
on Čech cohomology induced by multiplication by `r` on `M` to scalar multiplication by `r` on
`Hⁿ(X, M)`. -/
theorem homologyCechComplexIsoCohomology_hom_globalSectionsSmul (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) (r : Γ(X, ⊤))
    (x : ((cechComplexFunctor U).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj).homology n) :
    (homologyCechComplexIsoCohomology U hU hcover M n).hom
        (HomologicalComplex.homologyMap ((cechComplexFunctor U).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map (M.globalSectionsSmul r)).hom) n x) =
      r • (homologyCechComplexIsoCohomology U hU hcover M n).hom x := by
  rw [cohomology_smul]
  exact ConcreteCategory.congr_hom
    (homologyMap_comp_homologyCechComplexIsoCohomology_hom U hU hcover (M.globalSectionsSmul r) n) x

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

open TauCeti.AlgebraicGeometry in
/-- Every quasi-coherent sheaf `M` on a quasi-compact scheme with affine diagonal embeds into a
quasi-coherent sheaf with no cohomology in positive degrees, namely the direct sum of the
pushforwards of the restrictions of `M` to the members of a finite affine open cover. -/
lemma exists_mono_isQuasicoherent_subsingleton_cohomology [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (M : X.Modules) [M.IsQuasicoherent] :
    ∃ (I : X.Modules) (i : M ⟶ I), I.IsQuasicoherent ∧ Mono i ∧
      ∀ k, Subsingleton (Cohomology I (k + 1)) := by
  let 𝒰 := X.affineCover.finiteSubcover
  let U : 𝒰.I₀ → X.Opens := fun i ↦ (𝒰.f i).opensRange
  have hU (i : 𝒰.I₀) : IsAffineOpen (U i) := isAffineOpen_opensRange (𝒰.f i)
  have hcover : ⨆ i, U i = ⊤ := 𝒰.iSup_opensRange
  -- An affine open of a scheme with affine diagonal is an affine morphism.
  have hι (i : 𝒰.I₀) : IsAffineHom (U i).ι := ⟨fun V hV ↦
    (U i).ι.isAffineOpen_iff_of_isOpenImmersion.mp (by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact (hU i).inf hV)⟩
  have : HasFiniteBiproducts X.Modules := .of_hasFiniteProducts
  let F : 𝒰.I₀ → X.Modules := fun i ↦
    (pushforward (U i).ι).obj ((restrictFunctor (U i).ι).obj M)
  have hF (i : 𝒰.I₀) : (F i).IsQuasicoherent := by
    have := isQuasicoherent_restrictFunctor (U i).ι M
    infer_instance
  refine ⟨⨁ F, biproduct.lift fun i ↦ (restrictAdjunction (U i).ι).unit.app M,
    isQuasicoherent_of_isColimit (K := Discrete.functor F) (fun j ↦ hF j.as)
      (biproduct.isColimit F), ⟨fun {T} a b hab ↦ ?_⟩, fun k ↦ ?_⟩
  · -- A section of `M` is determined by its restrictions to the members of the cover.
    ext W t
    refine TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
      (fun i ↦ (U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ W)) W (fun i ↦ homOfLE ((U i).ι.image_preimage_le W))
      ?_ _ _ fun i ↦ ?_
    · intro x hx
      have hx' : x ∈ ⨆ i, U i := hcover.symm ▸ trivial
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx'
      refine Opens.mem_iSup.mpr ⟨i, ?_⟩
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact ⟨hi, hx⟩
    · have := congrArg (fun φ ↦ (φ ≫ biproduct.π F i).app W t) hab
      simp only [Category.assoc, biproduct.lift_π, Scheme.Modules.Hom.comp_app,
        restrictAdjunction_unit_app_app] at this
      exact this
  · -- Each summand has no higher cohomology, being pushed forward from an affine scheme along an
    -- affine morphism; so neither has their direct sum.
    have hzero (i : 𝒰.I₀) : IsZero ((cohomologyFunctor X (k + 1)).obj (F i)) := by
      have : IsAffine (U i).toScheme := hU i
      have := isQuasicoherent_restrictFunctor (U i).ι M
      have : Subsingleton (Cohomology (F i) (k + 1)) :=
        ((U i).ι.cohomologyPushforwardIsoOfIsAffineHom _
          (k + 1)).addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mpr
            (subsingleton_cohomology_succ_of_isAffine _ k)
      exact @AddCommGrpCat.isZero_of_subsingleton _ this
    refine AddCommGrpCat.subsingleton_of_isZero (G := (cohomologyFunctor X (k + 1)).obj (⨁ F)) ?_
    rw [IsZero.iff_id_eq_zero, ← CategoryTheory.Functor.map_id, ← biproduct.total,
      Functor.map_sum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [CategoryTheory.Functor.map_comp, (hzero i).eq_of_tgt ((cohomologyFunctor X (k + 1)).map
      (biproduct.π F i)) 0, zero_comp]

end AlgebraicGeometry.Scheme.Modules
