/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Compactification.DenseReplacement.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Dense replacement at a special fibre

The open immersion `D(t) ⟶ Spec R[t]` has a compactification with ambient scheme
`Spec R[t]` and proper structure map the identity. Its interior is schematically dense,
even when `R` is nonreduced. After base change along `t = 0`, the interior is empty,
whereas the ambient scheme is `Spec R`. Dense replacement of this special fibre is
therefore empty. For nonzero `R`, this shows that the canonical dense-replacement
base-change comparison need not be an isomorphism.

We use the principal-open compactification from `Compactification.Basic` and its
pullback-emptiness theorem from `Compactification.BaseChange`. The special-fibre calculation
uses the invertibility of the defining element after localization and Mathlib's criterion
for an empty scheme pullback.

## References

* The Stacks Project, Section 29.7, *Scheme theoretic closure and density* (tag 01RA).
* The Stacks Project, Section 38.32, *Compactifications* (tag 0ATT).
-/

public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace TauCeti.Compactification

noncomputable section

variable {R : CommRingCat.{u}}

/-- Dense replacement of the special fibre at `t = 0` of `D(t) ⟶ Spec R[t]` is empty. -/
theorem denseReplacement_specialFiber_empty :
    IsEmpty (denseReplacement
      ((localizationAway (R := CommRingCat.of (Polynomial R)) Polynomial.X).baseChange
        (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))))).obj.Xbar := by
  have : IsEmpty ↑(pullback (localizationAway
      (R := CommRingCat.of (Polynomial R)) Polynomial.X).j
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))))) :=
    isEmpty_pullback_localizationAway _ _ (by simp)
  refine ⟨fun x ↦ ?_⟩
  let C := (localizationAway (R := CommRingCat.of (Polynomial R)) Polynomial.X).baseChange
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))))
  have : Nonempty (denseReplacement C).obj.Xbar := ⟨x⟩
  exact isEmptyElim (denseReplacement C).obj.j.denseRange.nonempty.some

/-- For a nonzero coefficient ring, dense replacement does not commute with the special
fibre at `t = 0`: its canonical base-change comparison is not an isomorphism. -/
theorem not_isIso_denseReplacementBaseChange_specialFiber [Nontrivial R] :
    ¬ IsIso (denseReplacementBaseChange
      (localizationAway (R := CommRingCat.of (Polynomial R)) Polynomial.X)
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))))) := by
  let C := localizationAway (R := CommRingCat.of (Polynomial R)) Polynomial.X
  let g := Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
  have : IsSchemeTheoreticallyDominant C.j :=
    isSchemeTheoreticallyDominant_localizationAway _ Polynomial.isRegular_X
  have : IsIso (denseReplacementMap C) := (isIso_denseReplacementMap_iff C).mpr inferInstance
  have : IsIso (baseChangeMap (denseReplacementMap C) g) :=
    (baseChangeFunctor g).map_isIso (denseReplacementMap C)
  have : IsEmpty (denseReplacement (C.baseChange g)).obj.Xbar :=
    denseReplacement_specialFiber_empty
  intro h
  have : IsIso (denseReplacementBaseChange C g) := h
  let q : Spec (CommRingCat.of R) ⟶ (C.baseChange g).Xbar :=
    pullback.lift g (𝟙 _) (by simp [C])
  let q' := q ≫ inv (baseChangeMap (denseReplacementMap C) g).hom.h ≫
    inv (denseReplacementBaseChange C g).hom.h
  exact isEmptyElim (q' (Classical.arbitrary (Spec (CommRingCat.of R))))

end

end TauCeti.Compactification
