/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.SupportedKernel.Basic
public import TauCeti.AlgebraicGeometry.Modules.Restriction.Basic

/-!
# The supported kernel along a surjective or an empty open immersion

Let `j : V ⟶ Y` be an open immersion and `N` an `𝒪_Y`-module. The two extreme cases of the
supported kernel `ker(N ⟶ j_* (N|_V))`, the sections of `N` vanishing on `V`:

* if `j` is surjective (its image is `Y`, as for an open cut out by the unit ideal), the unit
  `N ⟶ j_* (N|_V)` is an isomorphism, so the supported kernel is zero and the supported quotient
  is `N` itself (`isZero_supportedKernel_of_opensRange_eq_top`,
  `isIso_supportedQuotientπ_of_opensRange_eq_top`);
* if `V` is empty (as for an open cut out by the zero ideal), every section vanishes on `V`, so
  the supported kernel is all of `N` and the supported quotient is zero
  (`isIso_supportedKernelι_of_isEmpty`, `isZero_supportedQuotient_of_isEmpty`).
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {Y V : Scheme.{u}} (N : Y.Modules) (j : V ⟶ Y) [IsOpenImmersion j]

/-- **The supported kernel along a surjective open immersion is zero**: no nonzero section
vanishes on all of `Y`. -/
theorem isZero_supportedKernel_of_opensRange_eq_top (h : j.opensRange = ⊤) :
    IsZero (N.supportedKernel j) :=
  have := isIso_restrictAdjunction_unit_app_of_opensRange_eq_top j N h
  (supportedKernel_def N j).symm ▸ isZero_kernel_of_mono _

/-- **The supported quotient along a surjective open immersion is the module itself**: the
projection `N ⟶ N.supportedQuotient j` is an isomorphism. -/
theorem isIso_supportedQuotientπ_of_opensRange_eq_top (h : j.opensRange = ⊤) :
    IsIso (N.supportedQuotientπ j) := by
  have := isIso_restrictAdjunction_unit_app_of_opensRange_eq_top j N h
  rw [supportedQuotientπ_def]
  -- The coimage of a monomorphism is its source: the kernel inclusion is zero.
  exact cokernel.π_of_zero (kernel.ι_of_mono _)

/-- **The supported kernel along an empty open is the whole module**: every section vanishes on
the empty set, so the inclusion `N.supportedKernel j ⟶ N` is an isomorphism. -/
instance isIso_supportedKernelι_of_isEmpty [IsEmpty V] : IsIso (N.supportedKernelι j) :=
  have : IsSplitEpi (N.supportedKernelι j) :=
    ⟨⟨⟨N.supportedKernelLift j (𝟙 N) (by simp), supportedKernelLift_ι ..⟩⟩⟩
  isIso_of_mono_of_isSplitEpi _

/-- **The supported quotient along an empty open is zero.** -/
theorem isZero_supportedQuotient_of_isEmpty [IsEmpty V] : IsZero (N.supportedQuotient j) :=
  have := kernel.ι_of_zero (restrictAdjunction_unit_app_eq_zero_of_isEmpty j N)
  isZero_cokernel_of_epi _

end AlgebraicGeometry.Scheme.Modules
