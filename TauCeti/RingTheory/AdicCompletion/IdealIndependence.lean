/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.UniformCompletion

/-!
# Independence of the ideal defining an adic completion

Two finitely generated ideals defining the same topology give canonically isomorphic adic
completions. The comparison fixes the original ring, is bicontinuous for the extended-ideal
topologies, and satisfies identity and composition laws. This allows completed localisations
to be used without retaining a choice of ideal of definition.

The construction uses `IsAdic.completionEquivAdicCompletion`: both algebraic completions are
the Hausdorff uniform completion of the same topological ring.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0,
  §§7.1.8–7.1.9 and 7.2.2.
-/

public section

open UniformSpace

namespace IsAdic

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [IsTopologicalRing R] {I J K : Ideal R}

/-- The canonical algebra isomorphism between completions along finitely generated ideals
of definition of the same topological ring. -/
noncomputable def adicCompletionEquiv (hI : IsAdic I) (hJ : IsAdic J)
    (hIfg : I.FG) (hJfg : J.FG) : AdicCompletion I R ≃ₐ[R] AdicCompletion J R :=
  AlgEquiv.ofRingEquiv (f := (hI.completionEquivAdicCompletion hIfg).symm.trans
    (hJ.completionEquivAdicCompletion hJfg)) fun x ↦ by simp

/-- The comparison is a homeomorphism for the adic topologies of the extended ideals. -/
theorem isHomeomorph_adicCompletionEquiv (hI : IsAdic I) (hJ : IsAdic J)
    (hIfg : I.FG) (hJfg : J.FG) :
    @IsHomeomorph _ _ (I.map (algebraMap R (AdicCompletion I R))).adicTopology
      (J.map (algebraMap R (AdicCompletion J R))).adicTopology
      (hI.adicCompletionEquiv hJ hIfg hJfg) := by
  let := (I.map (algebraMap R (AdicCompletion I R))).adicTopology
  let := (J.map (algebraMap R (AdicCompletion J R))).adicTopology
  have h := (hI.completionEquivAdicCompletion hIfg).toEquiv.isHomeomorph_iff.mp
    (hI.isHomeomorph_completionEquivAdicCompletion hIfg)
  exact (hJ.isHomeomorph_completionEquivAdicCompletion hJfg).comp
    (Homeomorph.mk (hI.completionEquivAdicCompletion hIfg).toEquiv h.1 h.2).symm.isHomeomorph

/-- Reversing the ideals gives the inverse comparison. -/
@[simp]
theorem adicCompletionEquiv_symm (hI : IsAdic I) (hJ : IsAdic J)
    (hIfg : I.FG) (hJfg : J.FG) :
    (hI.adicCompletionEquiv hJ hIfg hJfg).symm = hJ.adicCompletionEquiv hI hJfg hIfg := by
  ext x
  rfl

/-- Comparing a completion with itself gives the identity. -/
@[simp]
theorem adicCompletionEquiv_self (hI : IsAdic I) (hIfg : I.FG) :
    hI.adicCompletionEquiv hI hIfg hIfg = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro x
  exact (hI.completionEquivAdicCompletion hIfg).apply_symm_apply x

/-- Changes of ideal of definition compose canonically. -/
theorem adicCompletionEquiv_trans (hI : IsAdic I) (hJ : IsAdic J) (hK : IsAdic K)
    (hIfg : I.FG) (hJfg : J.FG) (hKfg : K.FG) :
    (hI.adicCompletionEquiv hJ hIfg hJfg).trans (hJ.adicCompletionEquiv hK hJfg hKfg) =
      hI.adicCompletionEquiv hK hIfg hKfg := by
  apply AlgEquiv.ext
  intro x
  exact congrArg (hK.completionEquivAdicCompletion hKfg)
    ((hJ.completionEquivAdicCompletion hJfg).symm_apply_apply _)

end IsAdic
