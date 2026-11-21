/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.Basic
public import TauCeti.CategoryTheory.Sites.ComparableTopologies

/-!
# The comparison morphism from étale sheaves to Nisnevich sheaves

Let `X` be a scheme. The small Nisnevich topology on the category `X.Etale` of étale `X`-schemes
is coarser than the small étale topology
(`AlgebraicGeometry.Scheme.smallNisnevichTopology_le_smallEtaleTopology`), so every étale sheaf
is a Nisnevich sheaf and the identity of `X.Etale` is continuous from the Nisnevich to the étale
topology. This defines the comparison morphism of topoi `Sh(X_ét) → Sh(X_Nis)` through its two
functors:

* its direct image `AlgebraicGeometry.Scheme.etaleToNisnevichPushforward X A`, Mathlib's
  pushforward of sheaves along the identity, which regards an étale sheaf as a Nisnevich sheaf
  and is fully faithful;
* its inverse image `AlgebraicGeometry.Scheme.etaleToNisnevichPullback X A`, étale
  sheafification of a Nisnevich sheaf, which is left adjoint to the direct image
  (`AlgebraicGeometry.Scheme.etaleToNisnevichAdjunction`).

The inverse image preserves colimits as a left adjoint. It preserves finite limits when `A` has
finite limits and étale sheafification preserves them
(`[HasFiniteLimits A] [HasSheafify (smallEtaleTopology X) A]`), for instance for sheaves of
`Λ`-modules, so it is then exact. Composing the direct image with the inverse image gives back the
étale sheaf, since the counit of the adjunction is an isomorphism.

## Main declarations

* `AlgebraicGeometry.Scheme.etaleToNisnevichPushforward`: étale sheaves as Nisnevich sheaves.
* `AlgebraicGeometry.Scheme.etaleToNisnevichPullback`: étale sheafification of Nisnevich
  sheaves.
* `AlgebraicGeometry.Scheme.etaleToNisnevichAdjunction`: the inverse image is left adjoint to the
  direct image.

## References

* The Stacks Project, Chapter *Étale Cohomology*, Section *Comparing topologies*.
* F. Morel, V. Voevodsky, *A¹-homotopy theory of schemes*, Publ. Math. IHÉS 90 (1999), §3.1.
-/

public section

universe v' u u'

open CategoryTheory Limits TauCeti.CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (A : Type u') [Category.{v'} A]

instance : (𝟭 X.Etale).IsContinuous (smallNisnevichTopology X) (smallEtaleTopology X) :=
  isContinuous_id_of_le (smallNisnevichTopology_le_smallEtaleTopology X)

/-- The direct image of the comparison morphism of topoi `Sh(X_ét) → Sh(X_Nis)`: an étale sheaf
on `X` is a Nisnevich sheaf. -/
abbrev etaleToNisnevichPushforward :
    Sheaf (smallEtaleTopology X) A ⥤ Sheaf (smallNisnevichTopology X) A :=
  (𝟭 X.Etale).sheafPushforwardContinuous A (smallNisnevichTopology X) (smallEtaleTopology X)

variable [HasWeakSheafify (smallEtaleTopology X) A]

/-- The inverse image of the comparison morphism of topoi `Sh(X_ét) → Sh(X_Nis)`: the étale
sheafification of a Nisnevich sheaf on `X`. -/
noncomputable abbrev etaleToNisnevichPullback :
    Sheaf (smallNisnevichTopology X) A ⥤ Sheaf (smallEtaleTopology X) A :=
  sheafToPresheaf (smallNisnevichTopology X) A ⋙ presheafToSheaf (smallEtaleTopology X) A

/-- The inverse image of the comparison morphism `Sh(X_ét) → Sh(X_Nis)`, étale sheafification,
is left adjoint to its direct image, the inclusion of étale sheaves into Nisnevich sheaves. -/
noncomputable abbrev etaleToNisnevichAdjunction :
    etaleToNisnevichPullback X A ⊣ etaleToNisnevichPushforward X A :=
  sheafifyAdjunctionPushforwardId (smallNisnevichTopology X) (smallEtaleTopology X) A

noncomputable instance : (etaleToNisnevichPullback X A).IsLeftAdjoint :=
  (etaleToNisnevichAdjunction X A).isLeftAdjoint

/- For sheaves of `Λ`-modules, the inverse image of `Sh(X_ét) → Sh(X_Nis)` is exact. -/
example (Λ : Type u) [Ring Λ] :
    PreservesFiniteLimits (etaleToNisnevichPullback X (ModuleCat.{u} Λ)) :=
  inferInstance

example (Λ : Type u) [Ring Λ] :
    PreservesColimits (etaleToNisnevichPullback X (ModuleCat.{u} Λ)) :=
  inferInstance

end AlgebraicGeometry.Scheme
