/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.WeaklyFiniteType
import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyHuberStandard
import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.StronglyNoetherian

/-!
# Examples for adic spaces locally of Huber's standing class

These examples exercise `TauCeti.AdicSpace.IsLocallyHuberStandard` across all main entry points:

* Affinoid adic spaces attached to strongly noetherian Tate pairs are locally of Huber's standing
  class.
* Over a discrete ring (noetherian or not), the whole of `Spa(A, A⁺)` is an open affinoid of
  Huber's standing class and `huberStandardAffinoidOpens` forms a basis.
* For any locally noetherian adic space `X`, the analytic locus `X_a` is locally of Huber's
  standing class, and when `X` is analytic (`X.obj.analyticPoints = Set.univ`),
  `IsLocallyNoetherian` and `IsLocallyHuberStandard` coincide.
* Being locally of Huber's standing class descends along open immersions and ascends along
  morphisms locally of weakly finite type.
-/

open CategoryTheory TopologicalSpace

namespace TauCeti.ValuationSpectrum

open Huber

section Tate

variable {A : Type} [CommRing A] [UniformSpace A] [IsTopologicalRing A] [IsTateRing A]
  [IsStronglyNoetherian A] (P : PairOfDefinition A) (Aplus : Subring A)
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)

/-- The adic spectrum of a strongly noetherian Tate pair is locally of Huber's standing class. -/
example :
    AdicSpace.IsLocallyHuberStandard ⟨presentationLimitPreAdicSpace P Aplus hAplus hP,
      isAdic_presentationLimitPreAdicSpace_of_isStronglyNoetherian P hP hAplus⟩ :=
  AdicSpace.IsLocallyHuberStandard.spa P Aplus hAplus hP
    (isSheaf_presentationLimitPresheaf_of_isStronglyNoetherian P hP hAplus)

end Tate

section Discrete

variable {A : Type} [CommRing A] [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (Aplus : Subring A) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
  (hP : P.ringOfDefinition ≤ Aplus)

/-- Over a discrete ring, noetherian or not, the whole of `Spa(A, A⁺)` is an open affinoid of
Huber's standing class. -/
example :
    ⊤ ∈ (presentationLimitPreAdicSpace P Aplus hAplus hP).huberStandardAffinoidOpens := by
  have h : spaBasicOpen Aplus ({1} : Finset A) 1 = ⊤ := by
    ext y
    simp [mem_spaBasicOpen, rationalSubset_singleton_one]
  exact h ▸ spaBasicOpen_mem_huberStandardAffinoidOpens P Aplus hAplus hP (isOpen_discrete _)

/-- Over a discrete ring, open affinoids of Huber's standing class form a basis of `Spa(A, A⁺)`. -/
example :
    Opens.IsBasis (presentationLimitPreAdicSpace P Aplus hAplus hP).huberStandardAffinoidOpens :=
  isBasis_huberStandardAffinoidOpens_presentationLimitPreAdicSpace P Aplus hAplus hP

end Discrete

end TauCeti.ValuationSpectrum

namespace TauCeti.AdicSpace

/-- The analytic locus of any locally noetherian adic space is locally of Huber's standing class. -/
example (X : AdicSpace) (hX : X.IsLocallyNoetherian) :
    X.analyticLocus.IsLocallyHuberStandard :=
  hX.isLocallyHuberStandard_analyticLocus

/-- On an analytic adic space, being locally of Huber's standing class is equivalent to being
locally noetherian. -/
example (X : AdicSpace) (han : X.obj.analyticPoints = Set.univ) :
    X.IsLocallyHuberStandard ↔ X.IsLocallyNoetherian :=
  isLocallyHuberStandard_iff_isLocallyNoetherian_of_analyticPoints_eq_univ han

/-- Being locally of Huber's standing class passes across an open immersion followed by a morphism
locally of weakly finite type. -/
example {U X Y : AdicSpace} {j : U ⟶ Y} {f : X ⟶ U} [PreAdicSpace.IsOpenImmersion j.hom]
    (hf : LocallyOfWeaklyFiniteType f) (hY : Y.IsLocallyHuberStandard) :
    X.IsLocallyHuberStandard :=
  (hY.of_isOpenImmersion j).of_locallyOfWeaklyFiniteType hf

end TauCeti.AdicSpace
