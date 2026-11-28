/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.SupportedCohomology.DegreeZero
public import TauCeti.Examples.Algebra.Homology.LocalCohomology.DegreeZero

/-!
# Non-Noetherian counterexample for geometric vs. algebraic local cohomology

Without finite generation of `I`, geometric `H⁰_{V(I)}(Spec A, M~)` can differ from algebraic
`H⁰_I(M)`. For `A = k[x₀, x₁, …] ⧸ (x_j ^ (j + 2))` (`TruncatedRing k`) and
`I = (x₀, x₁, …)` (`ideal k`), `TauCeti.Examples.Algebra.Homology.LocalCohomology.DegreeZero`
shows `V(I) = Spec A` and `H⁰_I(A) = 0`, whereas `1` gives a nontrivial element of
`H⁰_{V(I)}(Spec A, 𝒪_{Spec A})`, recovering that `I` is not finitely generated.

## Main results

* `TauCeti.AlgebraicGeometry.zeroLocusClosed_truncatedRing_ideal`: `V(I) = Spec A`.
* `TauCeti.AlgebraicGeometry.nontrivial_supportedModuleH_zero_truncatedRing`:
  `H⁰_{V(I)}(Spec A, 𝒪_{Spec A})` is nontrivial.
* `TauCeti.AlgebraicGeometry.not_fg_truncatedRing_ideal`: `I` is not finitely generated.

## References

* [The Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
* A. Grothendieck, *Local Cohomology*, Lecture Notes in Mathematics 41, Proposition 2.2.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry
open TauCeti.LocalCohomologyDegreeZeroExample

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry

section NonNoetherianCounterexample

variable (k : Type u) [CommRing k]

/-- Every generator of `LocalCohomologyDegreeZeroExample.ideal k` is nilpotent, so
`V(I) = Spec A`. -/
theorem zeroLocusClosed_truncatedRing_ideal :
    Spec.zeroLocusClosed (R := CommRingCat.of (TruncatedRing k))
      (ideal k : Set (TruncatedRing k)) = ⊤ := by
  rw [← Closeds.coe_eq_univ, Spec.coe_zeroLocusClosed]; exact zeroLocus_ideal

variable [Nontrivial k]

/-- On `A = LocalCohomologyDegreeZeroExample.TruncatedRing k`, geometric
`H⁰_{V(I)}(Spec A, 𝒪_{Spec A})` is nontrivial because the unit global section `1` is killed
locally on `Spec A \ V(I) = ∅`. -/
theorem nontrivial_supportedModuleH_zero_truncatedRing :
    Nontrivial ((modulesSpecToSheaf.obj
      (tilde (.of (CommRingCat.of (TruncatedRing k)) (TruncatedRing k)))).supportedModuleH
      (Spec.zeroLocusClosed (R := CommRingCat.of (TruncatedRing k))
        (ideal k : Set (TruncatedRing k))) ⊤ 0) := by
  let A := CommRingCat.of (TruncatedRing k); let F := modulesSpecToSheaf.obj (tilde (.of A A))
  let Z : Closeds (Spec A) := Spec.zeroLocusClosed (ideal k : Set A)
  have : Nontrivial A := Ideal.Quotient.nontrivial_iff.mpr fun htop ↦
    one_notMem_relations (htop ▸ Submodule.mem_top)
  have h1 : tilde.toOpen (.of A A) ⊤ (1 : A) ∈ F.supportedSubmodule Z ⊤ := by
    rw [F.mem_supportedSubmodule_iff]
    have hZ : Z = ⊤ := zeroLocusClosed_truncatedRing_ideal k
    have hU : (⊤ ⊓ Z.compl : Opens (Spec A)) = ⊥ := by rw [hZ]; ext x; simp
    rw [(TopCat.Sheaf.isTerminalOfEqEmpty F hU).isZero.eq_of_tgt
      (F.obj.map (Z.complInclusion ⊤).op) 0]; rfl
  have hne : (⟨tilde.toOpen (.of A A) ⊤ (1 : A), h1⟩ : F.supportedSubmodule Z ⊤) ≠ 0 :=
    fun h0 ↦ one_ne_zero (α := A) <| by
      have hval : tilde.toOpen (.of A A) ⊤ (1 : A) = 0 := congr(Subtype.val $h0)
      have hinv := ConcreteCategory.congr_hom (tilde.isoTop (.of A A)).hom_inv_id (1 : A)
      simpa [hval] using hinv.symm
  have : Nontrivial (F.supportedSubmodule Z ⊤) := ⟨⟨_, h1⟩, 0, hne⟩
  exact (F.supportedModuleHZeroEquiv Z ⊤).toEquiv.nontrivial

/-- `LocalCohomologyDegreeZeroExample.ideal k` is not finitely generated; otherwise degree-zero
geometric and algebraic local cohomology would agree. -/
theorem not_fg_truncatedRing_ideal : ¬ (ideal k).FG := fun hfg ↦ by
  let A := CommRingCat.of (TruncatedRing k)
  have : Subsingleton ((ideal k).primaryComponent A) :=
    primaryComponent_ideal_eq_bot (k := k) ▸ inferInstance
  have : Subsingleton ((modulesSpecToSheaf.obj (tilde (.of A A))).supportedModuleH
      (Spec.zeroLocusClosed (R := A) (ideal k : Set A)) ⊤ 0) :=
    ((primaryComponentEquivSupportedSubmoduleTop hfg (.of A A)).trans
      ((modulesSpecToSheaf.obj (tilde (.of A A))).supportedModuleHZeroEquiv _ ⊤).symm).toEquiv
        |>.symm.subsingleton
  have := nontrivial_supportedModuleH_zero_truncatedRing k
  exact false_of_nontrivial_of_subsingleton ((modulesSpecToSheaf.obj (tilde (.of A A)))
    |>.supportedModuleH (Spec.zeroLocusClosed (R := A) (ideal k : Set A)) ⊤ 0)

end NonNoetherianCounterexample

end TauCeti.AlgebraicGeometry
