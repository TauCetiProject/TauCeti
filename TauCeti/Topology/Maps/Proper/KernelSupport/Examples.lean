/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import TauCeti.Topology.Maps.Proper.KernelSupport

/-!
# Gaussian non-examples of properly supported kernels

On any noncompact seminormed additive group (for instance any nontrivial real normed space), the
Gaussian kernel `(x, y) ↦ exp (-‖x - y‖²)` is everywhere nonzero and therefore fails to have proper
input support, proper output support, or proper support, despite its rapid off-diagonal decay.
-/

public section

namespace TauCeti

/-- On any noncompact seminormed additive group (for instance any nontrivial real normed space),
the Gaussian kernel `(x, y) ↦ exp (-‖x - y‖²)` does not have proper input support. -/
theorem not_hasProperInputSupport_exp_neg_norm_sub_sq {E : Type*} [SeminormedAddCommGroup E]
    [NoncompactSpace E] :
    ¬HasProperInputSupport fun x y : E ↦ Real.exp (-‖x - y‖ ^ 2) := by
  have : Nonempty E := ⟨0⟩
  exact not_hasProperInputSupport_of_tsupport_eq_univ
    (tsupport_eq_univ_of_forall_ne_zero fun _ ↦ Real.exp_ne_zero _)

/-- On any noncompact seminormed additive group (for instance any nontrivial real normed space),
the Gaussian kernel `(x, y) ↦ exp (-‖x - y‖²)` does not have proper output support. -/
theorem not_hasProperOutputSupport_exp_neg_norm_sub_sq {E : Type*} [SeminormedAddCommGroup E]
    [NoncompactSpace E] :
    ¬HasProperOutputSupport fun x y : E ↦ Real.exp (-‖x - y‖ ^ 2) := by
  have : Nonempty E := ⟨0⟩
  exact not_hasProperOutputSupport_of_tsupport_eq_univ
    (tsupport_eq_univ_of_forall_ne_zero fun _ ↦ Real.exp_ne_zero _)

/-- On any noncompact seminormed additive group (for instance any nontrivial real normed space),
the Gaussian kernel `(x, y) ↦ exp (-‖x - y‖²)` is not properly supported, despite its rapid
off-diagonal decay. -/
theorem not_hasProperSupport_exp_neg_norm_sub_sq {E : Type*} [SeminormedAddCommGroup E]
    [NoncompactSpace E] :
    ¬HasProperSupport fun x y : E ↦ Real.exp (-‖x - y‖ ^ 2) := by
  have : Nonempty E := ⟨0⟩
  exact not_hasProperSupport_of_tsupport_eq_univ
    (tsupport_eq_univ_of_forall_ne_zero fun _ ↦ Real.exp_ne_zero _)

end TauCeti
