/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CyclicTwo
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.PGroup
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LatticeDefect.Basic

/-!
# Two rationally isomorphic lattices with nonisomorphic reductions

The integral regular representation of `C₂` and the sum of the integral trivial and sign
lines become isomorphic over `ℚ`. Over every field of characteristic two their reductions
are nonisomorphic: the latter is trivial, whereas the former is a non-split extension of
two trivial lines. Both nevertheless have exact Grothendieck class `2[k]`.

This example distinguishes the exact-sequence relations in the Grothendieck group from
isomorphism after reduction. It uses the existing scalar-extension dictionary and the
dimension characterization of classes for a finite `p`-group in characteristic `p`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §16.1.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, §VII.3, (7.3.3).
-/

public noncomputable section

open scoped MonoidAlgebra

namespace TauCeti

/-- The integral regular lattice of `C₂` and the trivial-plus-sign lattice have
isomorphic rationalizations. -/
theorem cyclicTwoLattices_nonempty_equiv_rat :
    Nonempty ((Representation.baseChange ℚ
      (Representation.ofMulAction ℤ (Multiplicative (ZMod 2))
        (Multiplicative (ZMod 2)))).Equiv
      (Representation.baseChange ℚ
        ((Representation.trivial ℤ (Multiplicative (ZMod 2)) ℤ).prod
          (Representation.ofLinearCharacter (cyclicTwoSign ℤˣ))))) := by
  let : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  exact ⟨(baseChangeOfMulActionEquiv ℤ ℚ _ _).trans
    ((cyclicTwoRegularEquivTrivialSign ℚ).trans
      (cyclicTwoTrivialSignBaseChangeEquiv ℤ ℚ).symm)⟩

section Nonisomorphism

variable (k : Type*) [CommRing k] [Nontrivial k] [CharP k 2]

/-- Despite their isomorphic rationalizations, the regular and trivial-plus-sign
integral lattices have nonisomorphic reductions in characteristic two. -/
theorem cyclicTwoLattices_not_equiv_charTwo :
    ¬ Nonempty ((Representation.baseChange k
      (Representation.ofMulAction ℤ (Multiplicative (ZMod 2))
        (Multiplicative (ZMod 2)))).Equiv
      (Representation.baseChange k
        ((Representation.trivial ℤ (Multiplicative (ZMod 2)) ℤ).prod
          (Representation.ofLinearCharacter (cyclicTwoSign ℤˣ))))) := by
  rintro ⟨e⟩
  have h := (baseChangeOfMulActionEquiv ℤ k _ _).symm.trans
    (e.trans (cyclicTwoTrivialSignBaseChangeEquiv ℤ k))
  have htriv : (Representation.trivial k (Multiplicative (ZMod 2)) k).prod
      (Representation.ofLinearCharacter (cyclicTwoSign kˣ)) =
      Representation.trivial k (Multiplicative (ZMod 2)) (k × k) := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro x
    simp [Representation.prod_apply_apply]
  rw [htriv] at h
  exact cyclicTwoRegular_not_equiv_trivial ⟨h⟩

end Nonisomorphism

variable (k : Type) [Field k] [CharP k 2]

/-- The reduction of the integral regular lattice of `C₂` has class twice the
trivial line in characteristic two. -/
@[simp]
theorem reductionK0_cyclicTwo_regular :
    reductionK0 k (Representation.ofMulAction ℤ (Multiplicative (ZMod 2))
      (Multiplicative (ZMod 2))) =
      2 • (1 : ExactK0 (finiteModulesExactStructure k[Multiplicative (ZMod 2)])) := by
  rw [reductionK0_def]
  have h := eq_finrankK0_smul_trivial_of_isPGroup (k := k) 2
    (by simpa using (IsPGroup.card (G := Multiplicative (ZMod 2))))
    (ExactK0.of (FGModuleCat.of k[Multiplicative (ZMod 2)]
      (Representation.baseChange k (Representation.ofMulAction ℤ (Multiplicative (ZMod 2))
        (Multiplicative (ZMod 2)))).asModule))
  rw [finrankK0_of, Representation.finrank_moduleCat_asModule,
    Module.finrank_baseChange, Module.finrank_eq_card_basis
      (MonoidAlgebra.basis (Multiplicative (ZMod 2)) ℤ)] at h
  simpa [exactK0_one_eq_of_trivial] using h

/-- The reduction of the integral trivial-plus-sign lattice has the same class
`2[k]`, although it is not isomorphic to the reduced regular lattice. -/
@[simp]
theorem reductionK0_cyclicTwo_trivial_sign :
    reductionK0 k ((Representation.trivial ℤ (Multiplicative (ZMod 2)) ℤ).prod
      (Representation.ofLinearCharacter (cyclicTwoSign ℤˣ))) =
      2 • (1 : ExactK0 (finiteModulesExactStructure k[Multiplicative (ZMod 2)])) := by
  rw [reductionK0_def]
  have h := eq_finrankK0_smul_trivial_of_isPGroup (k := k) 2
    (by simpa using (IsPGroup.card (G := Multiplicative (ZMod 2))))
    (ExactK0.of (FGModuleCat.of k[Multiplicative (ZMod 2)]
      (Representation.baseChange k
        ((Representation.trivial ℤ (Multiplicative (ZMod 2)) ℤ).prod
          (Representation.ofLinearCharacter (cyclicTwoSign ℤˣ)))).asModule))
  rw [finrankK0_of, Representation.finrank_moduleCat_asModule,
    Module.finrank_baseChange, Module.finrank_prod, Module.finrank_self] at h
  simpa [exactK0_one_eq_of_trivial] using h

end TauCeti
