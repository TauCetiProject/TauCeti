/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
import TauCeti.AlgebraicGeometry.FormalScheme.Spf.FromSpec
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Noetherian topological spaces and scheme immersions into formal spectra

Let `A` be a noetherian topological ring. Then `Spf A` has a noetherian underlying topological space
(`TauCeti.FormalScheme.Spf.noetherianSpace_carrier`, as a subspace of `PrimeSpectrum A`);
noetherianity of its local stalks is `TauCeti.FormalScheme.Spf.isNoetherianRing_stalk` in
`TauCeti.AlgebraicGeometry.FormalScheme.Spf.Stalk`.

Moreover, if an affine scheme `Spec R` maps into `Spf C` (for a noetherian adic ring `C`) via a
morphism of locally ringed spaces whose base map is an open embedding and whose stalk maps are
surjective, then `R` is itself a noetherian ring
(`TauCeti.FormalScheme.Spf.isNoetherianRing_of_isOpenEmbedding_fromSpec`): factoring
`Spec R ⟶ Spf C` through a thickening `Spec (C ⧸ I ^ (m + 1))` produces a scheme immersion into a
noetherian affine scheme, which is locally of finite type.

## Main results

* `TauCeti.FormalScheme.Spf.noetherianSpace_carrier`: `Spf.carrier A` is a `NoetherianSpace` when
  `A` is noetherian.
* `TauCeti.FormalScheme.Spf.isNoetherianRing_of_isOpenEmbedding_fromSpec`: a morphism
  `Spec R ⟶ Spf C` with open-embedding base and surjective stalk maps from an affine scheme into a
  noetherian formal spectrum forces `IsNoetherianRing R`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, 10.4.2 and 10.6.5.
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY) and
  [Tag 01OU](https://stacks.math.columbia.edu/tag/01OU).
-/

public section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace TauCeti.FormalScheme.Spf

/-- The underlying space of `Spf A` for a noetherian topological ring `A` is a noetherian
topological space. -/
instance noetherianSpace_carrier {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsNoetherianRing A] : NoetherianSpace (carrier A) :=
  have : NoetherianSpace (PrimeSpectrum A) := PrimeSpectrum.instNoetherianSpace A
  TopologicalSpace.NoetherianSpace.set (carrier A)

/-- If `α : Spec R ⟶ Spf C` has an open-embedding base map and surjective stalk maps, and `C` is a
noetherian adic ring, then `R` is a noetherian ring. -/
theorem isNoetherianRing_of_isOpenEmbedding_fromSpec {C R : Type u} [CommRing C]
    [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C] [IsNoetherianRing C] [CommRing R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C)
    (hα_open : Topology.IsOpenEmbedding α.base)
    (hα_stalk : ∀ q, Function.Surjective (α.stalkMap q)) :
    IsNoetherianRing R := by
  obtain ⟨m, hm⟩ := exists_ideal_pow_le_ker_fromSpecGlobalMap α
  let K := IsAdicRing.ideal C ^ (m + 1)
  have hK : IsAdic K := is_ideal_adic_pow (IsAdicRing.ideal_spec C).2.1 m.succ_pos
  let ψbar := fromSpecLift α hm
  let g : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (C ⧸ K)) :=
    Spec.map (CommRingCat.ofHom ψbar)
  have hopen : Topology.IsOpenEmbedding (PrimeSpectrum.comap ψbar) :=
    isOpenEmbedding_comap_fromSpecLift α hα_open hK hm
  have hpre : IsPreimmersion g :=
    { isEmbedding := hopen.isEmbedding
      stalkMap_surjective := stalkMap_fromSpecLift_surjective α hα_stalk hK hm }
  have : IsImmersion g := { hpre with isLocallyClosed_range := hopen.isOpen_range.isLocallyClosed }
  have : AlgebraicGeometry.IsLocallyNoetherian (Spec (CommRingCat.of R)) :=
    LocallyOfFiniteType.isLocallyNoetherian g
  exact (isLocallyNoetherian_Spec (R := CommRingCat.of R)).mp inferInstance

end TauCeti.FormalScheme.Spf
