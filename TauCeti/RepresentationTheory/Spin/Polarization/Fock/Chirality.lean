/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Chirality
public import TauCeti.LinearAlgebra.Dimension.FactFinrank
public import TauCeti.RepresentationTheory.Spin.Polarization.Fock.Spinors
import TauCeti.LinearAlgebra.CliffordAlgebra.HalfSpinor

/-!
# Chirality eigenspace dimensions of four-dimensional Fock spinors

On an oriented four-dimensional real inner product space `(V, o)` with `Q v = -‖v‖²`, every
`Q`-orthogonal complex structure `J` endows `TauCeti.AlmostComplexStructure.FockSpinors` with a
four-dimensional complex Clifford representation (`J.fockSpinorAction`). Unlike
`TauCeti.AlmostComplexStructure.finrank_positiveHalfSpinors_realFockAction` in
`TauCeti.RepresentationTheory.Spin.Polarization.Chirality`, which identifies the `±1` chirality
eigenspaces with even and odd exterior forms when `o` is the orientation induced by `J`,
`Orientation.finrank_eigenspace_fockSpinorAction_chirality` shows that both `±1` chirality
eigenspaces of `J.FockSpinors` have complex dimension two for **every** orientation `o` of `V` and
every `Q`-orthogonal `J`.

## Main results

* `Orientation.finrank_eigenspace_fockSpinorAction_chirality`: in dimension four with
  `Q v = -‖v‖²`, both `±1` chirality eigenspaces of `J.FockSpinors` have complex dimension two.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

namespace Orientation

open CliffordAlgebra Module Module.End TauCeti
open scoped TauCeti.FactFinrank

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (finrank ℝ V = 4)] {Q : QuadraticForm ℝ V}
  (o : Orientation ℝ V (Fin 4)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)

include hQ in
/-- In dimension four with `Q v = -‖v‖²`, both chirality eigenspaces (`ε = 1` and `ε = -1`) of
`J.FockSpinors` have complex dimension two for every `Q`-orthogonal complex structure `J`. -/
theorem finrank_eigenspace_fockSpinorAction_chirality
    (J : AlmostComplexStructure V) (hQJ : ∀ v, Q (J v) = Q v) (hQnd : Q.Nondegenerate)
    {ε : ℂ} (hε : ε = 1 ∨ ε = -1) :
    finrank ℂ (eigenspace (J.fockSpinorAction hQJ hQnd (chirality Q o)) ε) = 2 := by
  have hpos_two : finrank ℂ (positiveHalfSpinors o (J.fockSpinorAction hQJ hQnd)) = 2 := by
    have h4 : finrank ℂ (J.FockSpinors hQJ hQnd) = 4 := by
      rw [J.finrank_fockSpinors hQJ hQnd, (Fact.out : finrank ℝ V = 4)]
      norm_num
    rw [finrank_eq_two_mul_finrank_positiveHalfSpinors o (J.fockSpinorAction hQJ hQnd) hQ] at h4
    omega
  rcases hε with rfl | rfl
  · rwa [← positiveHalfSpinors_eq_eigenspace]
  · rw [finrank_eigenspace_chirality_neg o (J.fockSpinorAction hQJ hQnd) 1,
      ← positiveHalfSpinors_eq_eigenspace]
    exact hpos_two

end Orientation

end
