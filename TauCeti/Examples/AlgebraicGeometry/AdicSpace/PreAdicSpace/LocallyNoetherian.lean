/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyNoetherian
import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.StronglyNoetherian

/-!
# Tests for locally noetherian adic spaces

The adic spectrum of a strongly noetherian Tate pair, for instance of an affinoid algebra over a
complete nonarchimedean field, is a locally noetherian adic space. Over a discrete ring every
rational open of `Spa(A, A⁺)` is an open affinoid of noetherian type, also when `A` is not
noetherian.
-/

open CategoryTheory TopologicalSpace

namespace TauCeti.ValuationSpectrum

open Huber

section Tate

variable {A : Type} [CommRing A] [UniformSpace A] [IsTopologicalRing A] [IsTateRing A]
  [IsStronglyNoetherian A] (P : PairOfDefinition A) (Aplus : Subring A)
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)

/-- *locallyNoetherian_test_tate*: the adic spectrum of a strongly noetherian Tate pair is a
locally noetherian adic space. -/
example :
    AdicSpace.IsLocallyNoetherian ⟨presentationLimitPreAdicSpace P Aplus hAplus hP,
      isAdic_presentationLimitPreAdicSpace_of_isStronglyNoetherian P hP hAplus⟩ :=
  AdicSpace.IsLocallyNoetherian.spa P Aplus hAplus hP
    (isSheaf_presentationLimitPresheaf_of_isStronglyNoetherian P hP hAplus)

end Tate

section Discrete

variable {A : Type} [CommRing A] [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (Aplus : Subring A) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
  (hP : P.ringOfDefinition ≤ Aplus)

/-- *locallyNoetherian_test_discrete*: over a discrete ring, noetherian or not, the whole of
`Spa(A, A⁺)` is an open affinoid of noetherian type, the prime subring being a noetherian ring of
definition. -/
example :
    ⊤ ∈ (presentationLimitPreAdicSpace P Aplus hAplus hP).noetherianAffinoidOpens :=
  spaBasicOpen_singleton_one Aplus ▸
    spaBasicOpen_mem_noetherianAffinoidOpens P Aplus hAplus hP (isOpen_discrete _)

/-- *locallyNoetherian_test_discrete*: over a discrete ring the open affinoids of noetherian type
form a basis of `Spa(A, A⁺)`. -/
example :
    Opens.IsBasis (presentationLimitPreAdicSpace P Aplus hAplus hP).noetherianAffinoidOpens :=
  isBasis_noetherianAffinoidOpens_presentationLimitPreAdicSpace P Aplus hAplus hP

end Discrete

end TauCeti.ValuationSpectrum
