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
is a Nisnevich sheaf. This defines the comparison morphism of topoi `Sh(X_ét) → Sh(X_Nis)`
through its two functors:

* its direct image `AlgebraicGeometry.Scheme.etaleToNisnevichPushforward X A`, which regards an
  étale sheaf as a Nisnevich sheaf and is fully faithful;
* its inverse image `AlgebraicGeometry.Scheme.etaleToNisnevichInverseImage X A`, étale
  sheafification of a Nisnevich sheaf, which is left adjoint to the direct image
  (`AlgebraicGeometry.Scheme.etaleToNisnevichAdjunction`).

The inverse image is exact: it preserves finite limits whenever étale sheafification does, for
instance for sheaves of `Λ`-modules
(`AlgebraicGeometry.Scheme.preservesFiniteLimits_etaleToNisnevichInverseImage`), and it preserves
colimits as a left adjoint. Composing the direct image with the inverse image gives back the
étale sheaf, since the counit of the adjunction is an isomorphism.

## Main declarations

* `AlgebraicGeometry.Scheme.etaleToNisnevichPushforward`: étale sheaves as Nisnevich sheaves.
* `AlgebraicGeometry.Scheme.etaleToNisnevichInverseImage`: étale sheafification of Nisnevich
  sheaves.
* `AlgebraicGeometry.Scheme.etaleToNisnevichAdjunction`: the inverse image is left adjoint to the
  direct image.

## References

* The Stacks Project, Chapter *Étale Cohomology*, Section *Comparing topologies*.
* F. Morel, V. Voevodsky, *A¹-homotopy theory of schemes*, Publ. Math. IHÉS 90 (1999), §3.1.
-/

@[expose] public section

universe v' u u'

open CategoryTheory Limits GrothendieckTopology

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (A : Type u') [Category.{v'} A]

/-- The direct image of the comparison morphism of topoi `Sh(X_ét) → Sh(X_Nis)`: an étale sheaf
on `X` is a Nisnevich sheaf. -/
abbrev etaleToNisnevichPushforward :
    Sheaf (smallEtaleTopology X) A ⥤ Sheaf (smallNisnevichTopology X) A :=
  sheafInclusionOfLE (smallNisnevichTopology_le_smallEtaleTopology X) A

variable [HasWeakSheafify (smallEtaleTopology X) A]

/-- The inverse image of the comparison morphism of topoi `Sh(X_ét) → Sh(X_Nis)`: the étale
sheafification of a Nisnevich sheaf on `X`. -/
noncomputable abbrev etaleToNisnevichInverseImage :
    Sheaf (smallNisnevichTopology X) A ⥤ Sheaf (smallEtaleTopology X) A :=
  sheafToPresheaf (smallNisnevichTopology X) A ⋙ presheafToSheaf (smallEtaleTopology X) A

/-- The inverse image of the comparison morphism `Sh(X_ét) → Sh(X_Nis)`, étale sheafification,
is left adjoint to its direct image, the inclusion of étale sheaves into Nisnevich sheaves. -/
noncomputable def etaleToNisnevichAdjunction :
    etaleToNisnevichInverseImage X A ⊣ etaleToNisnevichPushforward X A :=
  sheafifyAdjunctionOfLE (smallNisnevichTopology_le_smallEtaleTopology X) A

/-- **The inverse image is exact.** For sheaves of `Λ`-modules, the inverse image of the
comparison morphism `Sh(X_ét) → Sh(X_Nis)` preserves finite limits. -/
theorem preservesFiniteLimits_etaleToNisnevichInverseImage (Λ : Type u) [Ring Λ] :
    PreservesFiniteLimits (etaleToNisnevichInverseImage X (ModuleCat.{u} Λ)) :=
  inferInstance

end AlgebraicGeometry.Scheme
