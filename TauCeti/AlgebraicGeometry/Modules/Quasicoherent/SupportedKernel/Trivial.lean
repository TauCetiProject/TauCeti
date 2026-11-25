/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.SupportedKernel
public import TauCeti.AlgebraicGeometry.Modules.Restriction.Basic
public import Mathlib.Algebra.Category.Grp.Zero

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

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {Y V : Scheme.{u}} (N : Y.Modules) (j : V ⟶ Y) [IsOpenImmersion j]

/-- Along an open immersion with image `Y`, the unit `N ⟶ j_* (N|_V)` is an isomorphism. -/
theorem isIso_restrictAdjunction_unit_app_of_opensRange_eq_top (h : j.opensRange = ⊤) :
    IsIso ((restrictAdjunction j).unit.app N) :=
  Hom.isIso_iff_isIso_app.mpr fun _ ↦
    isIso_restrictAdjunction_unit_app_app j N (h ▸ le_top)

/-- **The supported kernel along a surjective open immersion is zero**: no nonzero section
vanishes on all of `Y`. -/
theorem isZero_supportedKernel_of_opensRange_eq_top (h : j.opensRange = ⊤) :
    IsZero (N.supportedKernel j) :=
  have := isIso_restrictAdjunction_unit_app_of_opensRange_eq_top N j h
  (supportedKernel_def N j).symm ▸ isZero_kernel_of_mono _

/-- **The supported quotient along a surjective open immersion is the module itself**: the
projection `N ⟶ N.supportedQuotient j` is an isomorphism. -/
theorem isIso_supportedQuotientπ_of_opensRange_eq_top (h : j.opensRange = ⊤) :
    IsIso (N.supportedQuotientπ j) := by
  have := isIso_restrictAdjunction_unit_app_of_opensRange_eq_top N j h
  rw [supportedQuotientπ_def]
  -- The coimage of a monomorphism is its source: the kernel inclusion is zero.
  have : kernel.ι ((restrictAdjunction j).unit.app N : N ⟶ (pushforward j).obj (N.restrict j)) =
      0 := kernel.ι_of_mono _
  change IsIso (cokernel.π _)
  rw [this]
  infer_instance

/-- Along an open immersion from an empty scheme, the unit `N ⟶ j_* (N|_V)` is zero: its target
has no nonzero sections. -/
theorem restrictAdjunction_unit_app_eq_zero_of_isEmpty [IsEmpty V] :
    (restrictAdjunction j).unit.app N = 0 := by
  refine hom_ext _ _ fun W ↦ ?_
  ext s
  -- The sections of `j_* (N|_V)` over `W` are sections of `N|_V` over the empty open `j⁻¹ W`.
  have hW : j ⁻¹ᵁ W = ⊥ := Subsingleton.elim _ _
  have : Subsingleton Γ(N.restrict j, j ⁻¹ᵁ W) := by
    rw [hW]
    exact AddCommGrpCat.subsingleton_of_isZero
      (TopCat.Sheaf.isTerminalOfEmpty
        (⟨(N.restrict j).presheaf, (N.restrict j).isSheaf⟩ : TopCat.Sheaf AddCommGrpCat V)).isZero
  exact Subsingleton.elim (α := Γ(N.restrict j, j ⁻¹ᵁ W)) _ _

/-- **The supported kernel along an empty open is the whole module**: every section vanishes on
the empty set, so the inclusion `N.supportedKernel j ⟶ N` is an isomorphism. -/
theorem isIso_supportedKernelι_of_isEmpty [IsEmpty V] : IsIso (N.supportedKernelι j) := by
  have h := restrictAdjunction_unit_app_eq_zero_of_isEmpty N j
  let l := N.supportedKernelLift j (𝟙 N) (by rw [Category.id_comp, h])
  refine ⟨l, ?_, supportedKernelLift_ι N j _ _⟩
  rw [← cancel_mono (N.supportedKernelι j), Category.assoc, supportedKernelLift_ι,
    Category.comp_id, Category.id_comp]

/-- **The supported quotient along an empty open is zero.** -/
theorem isZero_supportedQuotient_of_isEmpty [IsEmpty V] : IsZero (N.supportedQuotient j) := by
  have : IsIso (kernel.ι ((restrictAdjunction j).unit.app N)) :=
    KernelFork.IsLimit.isIso_ι _ (limit.isLimit _)
      (restrictAdjunction_unit_app_eq_zero_of_isEmpty N j)
  exact isZero_cokernel_of_epi _

end AlgebraicGeometry.Scheme.Modules
