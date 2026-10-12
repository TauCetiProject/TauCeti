/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contraction.TensorTrick
public import TauCeti.LinearAlgebra.TensorCoalgebra.Filtration

/-!
# Tensor length and the tensor-trick homotopy

The tensor-trick homotopy acts on one letter at a time and therefore preserves tensor length.
Together with the length-lowering higher bar differential, this makes their composite locally
nilpotent, the hypothesis of the basic perturbation lemma.

The construction follows Gugenheim--Lambe--Stasheff, *Perturbation theory in differential
homological algebra II*.
-/

public section

open scoped DirectSum TensorProduct

universe uR uM uN

namespace TauCeti.LinearSpecialContraction

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {dM : Module.End R M} {dN : Module.End R N}

/-- The tensor-trick homotopy preserves the filtration by tensor length. -/
theorem reducedTensorWordsHomotopy_filtration (c : LinearSpecialContraction dM dN)
    (G : InternalGrading R M) (n : ℕ) :
    Submodule.map (c.reducedTensorWordsHomotopy G)
      (ReducedTensorWords.filtration R M n) ≤ ReducedTensorWords.filtration R M n := by
  rw [Submodule.map_le_iff_le_comap, ReducedTensorWords.filtration_le_iff]
  intro k hk
  rintro _ ⟨z, rfl⟩
  simp only [Submodule.mem_comap]
  rw [c.reducedTensorWordsHomotopy_of]
  exact ReducedTensorWords.of_mem_filtration R M hk _

end TauCeti.LinearSpecialContraction
