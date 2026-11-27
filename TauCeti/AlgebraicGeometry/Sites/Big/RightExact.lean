/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Big.LocallySurjective
public import TauCeti.CategoryTheory.Sites.ExactImageSieve

/-!
# Right exact sequences of modules give right exact sequences of big-site modules

Let `S` be a scheme and `F' ⟶ F ⟶ F'' ⟶ 0` a right exact sequence of `𝒪_S`-modules. The map of
big-site modules `F^a ⟶ F''^a` is locally surjective
(`AlgebraicGeometry.Scheme.Modules.isLocallySurjective_bigPresheafFunctor_map`). This file
proves exactness in the middle: a section of `F^a` over an `S`-scheme `T` whose image in `F''^a`
vanishes comes from `F'^a` locally on `T`, for the Zariski topology on the big site `Over S`
(`AlgebraicGeometry.Scheme.Modules.imageSieve_bigPresheafFunctor_map_mem_of_exact`), hence for
every finer topology. Together these are the roadmap's `bigSheaf_rightExact` for the presheaves
`F ↦ F^a`, with no quasi-coherence hypothesis.

For an `S`-scheme `(T, h)`, the pullback `h^*` is a left adjoint, so it carries the right exact
sequence to a right exact sequence `h^* F' ⟶ h^* F ⟶ h^* F''` of `𝒪_T`-modules
(`AlgebraicGeometry.Scheme.Modules.exact_map_pullback`). Forgetting the module structures keeps it
exact, and in the abelian category of sheaves on the opens of `T` a section killed by the second
map lifts locally (`CategoryTheory.ShortComplex.Exact.imageSieve_mem`). The opens of `T` on which
the section lifts form a Zariski covering of `(T, h)` by `S`-schemes, as in the proof of local
surjectivity.

## Main results

* `AlgebraicGeometry.Scheme.Modules.exact_map_pullback`: pullback of modules along a morphism of
  schemes preserves right exact sequences.
* `AlgebraicGeometry.Scheme.Modules.exists_app_eq_of_exact`: in an exact sequence of
  `𝒪_X`-modules, a section of the middle term killed by the second map lifts locally.
* `AlgebraicGeometry.Scheme.Modules.imageSieve_bigPresheafFunctor_map_mem_of_exact`: for a right
  exact sequence `F' ⟶ F ⟶ F'' ⟶ 0` of `𝒪_S`-modules, `F'^a ⟶ F^a ⟶ F''^a` is exact in the
  middle locally for the Zariski topology on `Over S`; `_of_le` for finer topologies.
-/

public section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **Pullback is right exact.** For a morphism of schemes `f : Y ⟶ X`, the pullback `f^*` of
modules carries an exact sequence `F' ⟶ F ⟶ F''` of `𝒪_X`-modules whose second map is an
epimorphism to an exact sequence of `𝒪_Y`-modules, since `f^*` is a left adjoint and so preserves
cokernels. -/
theorem exact_map_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) {K : ShortComplex X.Modules}
    (hK : K.Exact) [Epi K.g] : (K.map (pullback f)).Exact :=
  hK.map_of_epi_of_preservesCokernel _ inferInstance inferInstance

open TauCeti.AlgebraicGeometry in
/-- **Kernel sections lift locally.** In an exact sequence `F' ⟶ F ⟶ F''` of `𝒪_X`-modules, a
section of `F` over `U` with image zero in `F''` comes from `F'` near every point of `U`. -/
theorem exists_app_eq_of_exact {X : Scheme.{u}} {K : ShortComplex X.Modules} (hK : K.Exact)
    {U : X.Opens} (s : Γ(K.X₂, U)) (hs : K.g.app U s = 0) {x : X} (hx : x ∈ U) :
    ∃ (V : X.Opens) (i : V ⟶ U) (t : Γ(K.X₁, V)), x ∈ V ∧
      K.f.app V t = K.X₂.presheaf.map i.op s := by
  obtain ⟨V, i, ⟨t, ht⟩, hxV⟩ := (hK.map (Scheme.Modules.toSheaf X)).imageSieve_mem s hs x hx
  exact ⟨V, i, t, hxV, ht⟩

/-- **Exactness in the middle of `F ↦ F^a`.** For an exact sequence `F' ⟶ F ⟶ F''` of
`𝒪_S`-modules whose second map is an epimorphism, a section `s` of `F^a` over an `S`-scheme `T`
with image zero in `F''^a` comes from `F'^a` locally on `T` for the Zariski topology: its image
sieve under `F'^a ⟶ F^a` is a Zariski covering sieve of `T` in `Over S`. -/
theorem imageSieve_bigPresheafFunctor_map_mem_of_exact {S : Scheme.{u}}
    {K : ShortComplex S.Modules} (hK : K.Exact) [Epi K.g] {T : Over S}
    (s : Γ((pullback T.hom).obj K.X₂, ⊤)) (hs : ((pullback T.hom).map K.g).app ⊤ s = 0) :
    Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map ((bigPresheafFunctor S).map K.f))
      (U := T) s ∈ (zariskiTopology.over S) T := by
  have hK' := exact_map_pullback T.hom hK
  have hlift (x : T.left) : ∃ (V : T.left.Opens) (m : Γ((pullback T.hom).obj K.X₁, V)),
      x ∈ V ∧ ((pullback T.hom).map K.f).app V m =
        ((pullback T.hom).obj K.X₂).presheaf.map (homOfLE le_top).op s := by
    obtain ⟨V, i, m, hxV, hm⟩ := exists_app_eq_of_exact hK' s hs (Set.mem_univ x)
    exact ⟨V, m, hxV, hm.trans (congrArg (fun k ↦ ((pullback T.hom).obj K.X₂).presheaf.map k s)
      (Subsingleton.elim _ _))⟩
  choose V m hxV hm using hlift
  have hV : TopologicalSpace.IsOpenCover V :=
    .mk (top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩)
  rw [GrothendieckTopology.mem_over_iff, mem_grothendieckTopology_iff]
  refine ⟨T.left.openCoverOfIsOpenCover V hV, ?_⟩
  rintro _ _ ⟨x⟩
  rw [Sieve.overEquiv_iff]
  -- Over the `S`-scheme `V x`, the lift is the section `m x` read as a global section.
  refine ⟨bigSectionsRestrictLE K.X₁ (V x).ι rfl (V x) ⊤ (by simp) (m x), ?_⟩
  change ((pullback ((V x).ι ≫ T.hom)).map K.f).app ⊤
      (bigSectionsRestrictLE K.X₁ (V x).ι rfl (V x) ⊤ (by simp) (m x)) =
    bigSectionsRestrict K.X₂ (Over.homMk (V x).ι : Over.mk ((V x).ι ≫ T.hom) ⟶ T) s
  refine (bigSectionsRestrictLE_naturality K.f (V x).ι rfl (V x) ⊤ (by simp) (m x)).symm.trans ?_
  exact (congrArg (bigSectionsRestrictLE K.X₂ (V x).ι rfl (V x) ⊤ (by simp)) (hm x)).trans
    (bigSectionsRestrict_homMk_ι K.X₂ T (V x) s).symm

/-- Exactness in the middle of `F ↦ F^a` holds locally for every topology on schemes finer than
the Zariski topology, such as the étale, fppf and fpqc topologies. -/
theorem imageSieve_bigPresheafFunctor_map_mem_of_exact_of_le {J : GrothendieckTopology Scheme.{u}}
    (hJ : zariskiTopology ≤ J) {S : Scheme.{u}} {K : ShortComplex S.Modules} (hK : K.Exact)
    [Epi K.g] {T : Over S} (s : Γ((pullback T.hom).obj K.X₂, ⊤))
    (hs : ((pullback T.hom).map K.g).app ⊤ s = 0) :
    Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map ((bigPresheafFunctor S).map K.f))
      (U := T) s ∈ (J.over S) T :=
  GrothendieckTopology.over_mono hJ S T (imageSieve_bigPresheafFunctor_map_mem_of_exact hK s hs)

end AlgebraicGeometry.Scheme.Modules
