/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Colimits
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.AlgebraicGeometry.Sites.Big.Sheaf

/-!
# Epimorphisms of modules give locally surjective maps of big-site modules

Let `S` be a scheme and `φ : F ⟶ G` an epimorphism of `𝒪_S`-modules. This file proves that the
induced map of big-site modules `F^a ⟶ G^a`, `(T, h) ↦ (Γ(T, h^* F) ⟶ Γ(T, h^* G))`, is locally
surjective for the Zariski topology on the big site `Over S`
(`AlgebraicGeometry.Scheme.Modules.isLocallySurjective_bigPresheafFunctor_map`), hence for every
finer topology, such as the étale, fppf and fpqc topologies
(`AlgebraicGeometry.Scheme.Modules.isLocallySurjective_bigPresheafFunctor_map_of_le`). For
quasi-coherent modules the map of big fpqc sheaves `bigSheaf F ⟶ bigSheaf G` is therefore
locally surjective (`AlgebraicGeometry.Scheme.isLocallySurjective_bigSheafFunctor_map`). This is
the surjectivity half of the right exactness of `F ↦ F^a`: right exact sequences of modules end
in a locally surjective map of big-site modules.

The proof uses no quasi-coherence. For an `S`-scheme `(T, h)`, the pullback `h^* φ` is again an
epimorphism, as `h^*` is a left adjoint, so it is locally surjective on the opens of `T`. The
inclusions of the opens of `T` on which a section of `h^* G` lifts are morphisms of `S`-schemes,
and they form a Zariski covering of `(T, h)`; over the `S`-scheme given by such an open `V`, the
lift is a section of `F^a` mapping to the restriction of the given section, through the
identification of sections of `h^* F` over `V` with global sections of the pullback of `F` to `V`
(`AlgebraicGeometry.Scheme.Modules.bigSectionsRestrictLE`).

## Main results

* `AlgebraicGeometry.Scheme.Modules.imageSieve_bigPresheafFunctor_map_mem_of_forall_exists`: a
  section of `G^a` over `T` whose restrictions lift on the members of an open cover of `T` has a
  Zariski-covering image sieve under `F^a ⟶ G^a`.
* `AlgebraicGeometry.Scheme.Modules.isLocallySurjective_bigPresheafFunctor_map`: for an
  epimorphism `φ` of `𝒪_S`-modules, `bigPresheaf F ⟶ bigPresheaf G` is locally surjective for the
  Zariski topology on `Over S`.
* `AlgebraicGeometry.Scheme.isLocallySurjective_bigSheafFunctor_map`: for an epimorphism of
  quasi-coherent modules, the map of big fpqc sheaves is locally surjective.
-/

public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme

namespace Modules

variable {S : Scheme.{u}} {F G : S.Modules}

/-- **Local lifts on an open cover give a Zariski-covering image sieve.** Let `φ : F ⟶ G` be a
map of `𝒪_S`-modules and `s` a section of `G^a` over an `S`-scheme `T`, that is a global section
of the pullback of `G` to `T`. If every point of `T` has an open neighbourhood `V` on which the
restriction of `s` lifts along the pullback of `φ`, then the image sieve of `s` under
`F^a ⟶ G^a` is a Zariski covering sieve of `T` in `Over S`. -/
theorem imageSieve_bigPresheafFunctor_map_mem_of_forall_exists (φ : F ⟶ G) {T : Over S}
    (s : Γ((pullback T.hom).obj G, ⊤))
    (h : ∀ x : T.left, ∃ (V : T.left.Opens) (i : V ⟶ ⊤) (m : Γ((pullback T.hom).obj F, V)),
      x ∈ V ∧ ((pullback T.hom).map φ).app V m = ((pullback T.hom).obj G).presheaf.map i.op s) :
    Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map ((bigPresheafFunctor S).map φ))
      (U := T) s ∈ (zariskiTopology.over S) T := by
  choose V i m hxV hm using h
  have hV : TopologicalSpace.IsOpenCover V :=
    .mk (top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩)
  rw [GrothendieckTopology.mem_over_iff, mem_grothendieckTopology_iff]
  refine ⟨T.left.openCoverOfIsOpenCover V hV, ?_⟩
  rintro _ _ ⟨x⟩
  rw [Sieve.overEquiv_iff]
  -- Over the `S`-scheme `V x`, the lift is the section `m x` read as a global section.
  refine ⟨bigSectionsRestrictLE F (V x).ι rfl (V x) ⊤ (by simp) (m x), ?_⟩
  -- Unfold the maps of `bigPresheaf` and `bigPresheafFunctor` (`bigPresheaf_map_apply`,
  -- `bigPresheafFunctor_map_app_apply`); `rw` cannot, as the index `x` of the cover is a point
  -- of `T` only up to definitional equality.
  change ((pullback ((V x).ι ≫ T.hom)).map φ).app ⊤
      (bigSectionsRestrictLE F (V x).ι rfl (V x) ⊤ (by simp) (m x)) =
    bigSectionsRestrict G (Over.homMk (V x).ι : Over.mk ((V x).ι ≫ T.hom) ⟶ T) s
  refine (bigSectionsRestrictLE_naturality φ (V x).ι rfl (V x) ⊤ (by simp) (m x)).symm.trans ?_
  rw [hm x, Subsingleton.elim (i x) (homOfLE le_top)]
  exact (bigSectionsRestrict_homMk_ι G T (V x) s).symm

/-- **Epimorphisms give locally surjective maps of big-site modules.** For an epimorphism
`φ : F ⟶ G` of `𝒪_S`-modules, the induced map `bigPresheaf F ⟶ bigPresheaf G` of presheaves of
modules on the big site `Over S` is locally surjective for the Zariski topology: every section of
`G^a` over an `S`-scheme `T` lifts to `F^a` on the members of an open cover of `T`. -/
theorem isLocallySurjective_bigPresheafFunctor_map (φ : F ⟶ G) [Epi φ] :
    PresheafOfModules.IsLocallySurjective (zariskiTopology.over S)
      ((bigPresheafFunctor S).map φ) where
  imageSieve_mem {T} s := by
    -- The pullback of `φ` to `T` is an epimorphism, hence locally surjective on the opens of `T`.
    let ψ := (pullback T.hom).map φ
    have hψ : Sheaf.IsLocallySurjective ((TauCeti.AlgebraicGeometry.Scheme.Modules.toSheaf
        T.left).map ψ) := (Sheaf.isLocallySurjective_iff_epi' (φ := _)).mpr inferInstance
    refine imageSieve_bigPresheafFunctor_map_mem_of_forall_exists φ s fun x ↦ ?_
    -- A section of `bigPresheaf G` over `T` is by definition a global section of `h^* G`
    -- (`bigPresheaf_obj`), so `s` is a section of `toSheaf T.left` over `⊤`.
    obtain ⟨V, j, ⟨m, hm⟩, hxV⟩ := Presheaf.imageSieve_mem (Opens.grothendieckTopology T.left)
      ((TauCeti.AlgebraicGeometry.Scheme.Modules.toSheaf T.left).map ψ).hom s x trivial
    rw [TauCeti.AlgebraicGeometry.Scheme.Modules.toSheaf_map_hom, mapPresheaf_app] at hm
    exact ⟨V, j, m, hxV, hm⟩

/-- For an epimorphism `φ : F ⟶ G` of `𝒪_S`-modules, the map `bigPresheaf F ⟶ bigPresheaf G` is
locally surjective for every topology on schemes finer than the Zariski topology, such as the
étale, fppf and fpqc topologies. -/
theorem isLocallySurjective_bigPresheafFunctor_map_of_le {J : GrothendieckTopology Scheme.{u}}
    (hJ : zariskiTopology ≤ J) (φ : F ⟶ G) [Epi φ] :
    PresheafOfModules.IsLocallySurjective (J.over S) ((bigPresheafFunctor S).map φ) :=
  Presheaf.isLocallySurjective_of_le (GrothendieckTopology.over_mono hJ S) _
    (isLocallySurjective_bigPresheafFunctor_map φ)

end Modules

open TauCeti.AlgebraicGeometry in
/-- **The big-site module functor sends epimorphisms to locally surjective maps.** For an
epimorphism `φ` of quasi-coherent `𝒪_S`-modules, the map of big fpqc sheaves
`bigSheaf F ⟶ bigSheaf G` is locally surjective. -/
theorem isLocallySurjective_bigSheafFunctor_map {S : Scheme.{u}} {F G : QuasicoherentSheaf S}
    (φ : F ⟶ G) [Epi φ] :
    PresheafOfModules.IsLocallySurjective (fpqcTopology.over S)
      ((bigSheafFunctor S).map φ).val := by
  have := ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory
    (SheafOfModules.isQuasicoherent S.ringCatSheaf)
  have : Epi (C := S.Modules) φ.hom := (ObjectProperty.ι _).map_epi φ
  rw [bigSheafFunctor_map_val]
  exact Modules.isLocallySurjective_bigPresheafFunctor_map_of_le zariskiTopology_le_fpqcTopology
    φ.hom

end AlgebraicGeometry.Scheme
