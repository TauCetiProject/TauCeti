/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.ExactSections
public import TauCeti.AlgebraicGeometry.Modules.Pullback.RightExact
public import TauCeti.AlgebraicGeometry.Sites.Big.LocallySurjective

/-!
# Exactness in the middle of big-site modules, locally

Let `S` be a scheme and `F' ⟶ F ⟶ F'' ⟶ 0` a right exact sequence of `𝒪_S`-modules. This file
proves that a section of `F^a` over an `S`-scheme `T` whose image in `F''^a` vanishes comes from
`F'^a` locally on `T`, for the Zariski topology on the big site `Over S`
(`AlgebraicGeometry.Scheme.Modules.imageSieve_bigPresheafFunctor_map_mem_of_exact`), hence for
every finer topology. Together with the local surjectivity of `F^a ⟶ F''^a`
(`AlgebraicGeometry.Scheme.Modules.isLocallySurjective_bigPresheafFunctor_map`), this local
lifting of kernel sections is an ingredient of the right exactness of `F ↦ F^a`. No
quasi-coherence hypothesis is used.

For an `S`-scheme `(T, h)`, the pullback `h^*` carries the right exact sequence to a right exact
sequence `h^* F' ⟶ h^* F ⟶ h^* F''` of `𝒪_T`-modules
(`AlgebraicGeometry.Scheme.Modules.exact_map_pullback`), in which a section killed by the second
map lifts near every point (`AlgebraicGeometry.Scheme.Modules.exists_app_eq_of_exact`). The opens
of `T` on which the section lifts form a Zariski covering of `(T, h)` by `S`-schemes
(`AlgebraicGeometry.Scheme.Modules.imageSieve_bigPresheafFunctor_map_mem_of_forall_exists`).

## Main results

* `AlgebraicGeometry.Scheme.Modules.imageSieve_bigPresheafFunctor_map_mem_of_exact`: for a right
  exact sequence `F' ⟶ F ⟶ F'' ⟶ 0` of `𝒪_S`-modules, a section of `F^a` killed by
  `F^a ⟶ F''^a` lifts to `F'^a` locally for the Zariski topology on `Over S`; `_of_le` for finer
  topologies.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **Exactness in the middle of `F ↦ F^a`.** For an exact sequence `F' ⟶ F ⟶ F''` of
`𝒪_S`-modules whose second map is an epimorphism, a section `s` of `F^a` over an `S`-scheme `T`
with image zero in `F''^a` comes from `F'^a` locally on `T` for the Zariski topology: its image
sieve under `F'^a ⟶ F^a` is a Zariski covering sieve of `T` in `Over S`. -/
theorem imageSieve_bigPresheafFunctor_map_mem_of_exact {S : Scheme.{u}}
    {K : ShortComplex S.Modules} (hK : K.Exact) [Epi K.g] {T : Over S}
    (s : Γ((pullback T.hom).obj K.X₂, ⊤)) (hs : ((pullback T.hom).map K.g).app ⊤ s = 0) :
    Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map ((bigPresheafFunctor S).map K.f))
      (U := T) s ∈ (zariskiTopology.over S) T :=
  imageSieve_bigPresheafFunctor_map_mem_of_forall_exists K.f s fun x ↦
    exists_app_eq_of_exact (exact_map_pullback T.hom hK) s hs (Set.mem_univ x)

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
