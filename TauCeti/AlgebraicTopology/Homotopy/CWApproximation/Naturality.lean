/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Basic
public import TauCeti.AlgebraicTopology.Homotopy.Whitehead

/-!
# Naturality of CW approximation up to homotopy

A map `φ : X → Y` of path-connected spaces lifts to a map `Γφ` between their CW approximations
`ΓX = TauCeti.cwApproximation X x` and `ΓY = TauCeti.cwApproximation Y y`
(`TauCeti.cwApproximationLift x y φ`), for which the square

```
ΓX --Γφ--> ΓY
 |          |
 v          v
 X ---φ---> Y
```

commutes up to homotopy (`TauCeti.comp_cwApproximationLift_homotopic`), and `Γφ` is determined up
to homotopy by this property (`TauCeti.homotopic_cwApproximationLift`). This is Hatcher's
Proposition 4.18: the vertical maps are weak homotopy equivalences out of spaces of CW type, so
`Γφ` exists by the surjectivity half and is unique by the injectivity half of Proposition 4.22
(`ContinuousMap.IsWeakHomotopyEquivalence.exists_comp_homotopic`,
`ContinuousMap.IsWeakHomotopyEquivalence.homotopic_of_comp_homotopic`).

Uniqueness makes the construction functorial up to homotopy: homotopic maps have homotopic lifts
(`TauCeti.cwApproximationLift_homotopic_of_homotopic`), the identity lifts to a map homotopic to the
identity (`TauCeti.cwApproximationLift_id_homotopic`), and a composite lifts to the composite of
the lifts (`TauCeti.cwApproximationLift_comp_homotopic`). By two out of three, `Γφ` is a weak
homotopy equivalence exactly when `φ` is
(`TauCeti.isWeakHomotopyEquivalence_cwApproximationLift_iff`), so for a weak homotopy equivalence
`φ` it is a homotopy equivalence by Whitehead's theorem; applied to the identity of `X`, this
compares the CW approximations of `X` at two base points.

More generally, any two CW approximations of a space, that is weak homotopy equivalences
`a : A → X` and `a' : A' → X` out of spaces of CW type, are related by a homotopy equivalence
`e : A ≃ₕ A'` with `a' ∘ e ≃ a`
(`ContinuousMap.IsWeakHomotopyEquivalence.exists_homotopyEquiv_comp_homotopic`), the uniqueness of
CW approximation up to homotopy equivalence.

## Main definitions

* `TauCeti.cwApproximationLift x y φ`: the map of CW approximations induced by `φ`.

## Main results

* `TauCeti.comp_cwApproximationLift_homotopic` and `TauCeti.homotopic_cwApproximationLift`: the
  square commutes up to homotopy, and this determines `Γφ` up to homotopy.
* `TauCeti.cwApproximationLift_id_homotopic` and `TauCeti.cwApproximationLift_comp_homotopic`:
  functoriality up to homotopy.
* `TauCeti.isWeakHomotopyEquivalence_cwApproximationLift_iff`: `Γφ` is a weak homotopy equivalence
  exactly when `φ` is.
* `ContinuousMap.IsWeakHomotopyEquivalence.exists_homotopyEquiv_comp_homotopic`: CW approximations
  are unique up to homotopy equivalence.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Proposition 4.18 and the uniqueness of CW approximations stated after it, and
  Proposition 4.22.
-/

public section

noncomputable section

universe u

open ContinuousMap

/-- **CW approximations are unique up to homotopy equivalence** (Hatcher, after Proposition 4.18).
If `a : A → X` and `a' : A' → X` are weak homotopy equivalences out of spaces of CW type, there is
a homotopy equivalence `e : A ≃ₕ A'` with `a' ∘ e ≃ a`. -/
theorem ContinuousMap.IsWeakHomotopyEquivalence.exists_homotopyEquiv_comp_homotopic
    {A A' X : Type*} [TopologicalSpace A] [TopologicalSpace A'] [TopologicalSpace X]
    [TauCeti.CWType A] [TauCeti.CWType A'] {a : C(A, X)} {a' : C(A', X)}
    (ha : a.IsWeakHomotopyEquivalence) (ha' : a'.IsWeakHomotopyEquivalence) :
    ∃ e : A ≃ₕ A', (a'.comp e.toFun).Homotopic a := by
  obtain ⟨g, hg⟩ := ha'.exists_comp_homotopic a
  -- `a' ∘ g ≃ a` is a weak homotopy equivalence, so `g` is one by two out of three.
  have hg' : g.IsWeakHomotopyEquivalence := ha'.of_postcomp (ha.of_homotopic hg.symm)
  exact ⟨hg'.homotopyEquiv, by rwa [IsWeakHomotopyEquivalence.homotopyEquiv_toFun]⟩

namespace TauCeti

variable {X Y Z : TopCat.{u}} (x : X) (y : Y) (z : Z)

/-- The map `Γφ : ΓX → ΓY` of CW approximations induced by a map `φ : X → Y` into a path-connected
space: a lift of `φ ∘ cwApproximationMap X x` through the weak homotopy equivalence
`cwApproximationMap Y y`, so that the square of `φ` and `Γφ` with the two CW approximation maps
commutes up to homotopy (`TauCeti.comp_cwApproximationLift_homotopic`). It is determined up to
homotopy by this property (`TauCeti.homotopic_cwApproximationLift`). -/
def cwApproximationLift [PathConnectedSpace Y] (φ : C(X, Y)) :
    C(cwApproximation X x, cwApproximation Y y) :=
  ((isWeakHomotopyEquivalence_cwApproximationMap Y y).exists_comp_homotopic
    (φ.comp (cwApproximationMap X x).hom)).choose

/-- **The CW approximation square commutes up to homotopy** (Hatcher, Proposition 4.18):
`cwApproximationMap Y y ∘ Γφ ≃ φ ∘ cwApproximationMap X x`. -/
theorem comp_cwApproximationLift_homotopic [PathConnectedSpace Y] (φ : C(X, Y)) :
    ((cwApproximationMap Y y).hom.comp (cwApproximationLift x y φ)).Homotopic
      (φ.comp (cwApproximationMap X x).hom) :=
  ((isWeakHomotopyEquivalence_cwApproximationMap Y y).exists_comp_homotopic
    (φ.comp (cwApproximationMap X x).hom)).choose_spec

/-- **Uniqueness of the induced map** (Hatcher, Proposition 4.18). Every map `ψ : ΓX → ΓY` for
which the CW approximation square of `φ` commutes up to homotopy is homotopic to `Γφ`. -/
theorem homotopic_cwApproximationLift [PathConnectedSpace Y] {φ : C(X, Y)}
    {ψ : C(cwApproximation X x, cwApproximation Y y)}
    (hψ : ((cwApproximationMap Y y).hom.comp ψ).Homotopic (φ.comp (cwApproximationMap X x).hom)) :
    ψ.Homotopic (cwApproximationLift x y φ) :=
  (isWeakHomotopyEquivalence_cwApproximationMap Y y).homotopic_of_comp_homotopic
    (hψ.trans (comp_cwApproximationLift_homotopic x y φ).symm)

/-- Homotopic maps induce homotopic maps of CW approximations. -/
theorem cwApproximationLift_homotopic_of_homotopic [PathConnectedSpace Y] {φ φ' : C(X, Y)}
    (h : φ.Homotopic φ') : (cwApproximationLift x y φ).Homotopic (cwApproximationLift x y φ') :=
  homotopic_cwApproximationLift x y ((comp_cwApproximationLift_homotopic x y φ).trans
    (h.comp (Homotopic.refl _)))

/-- **The identity induces the identity up to homotopy.** -/
theorem cwApproximationLift_id_homotopic [PathConnectedSpace X] :
    (cwApproximationLift x x (ContinuousMap.id X)).Homotopic (ContinuousMap.id _) :=
  (homotopic_cwApproximationLift x x (φ := ContinuousMap.id X) (ψ := ContinuousMap.id _)
    (by rw [comp_id, id_comp])).symm

/-- **Composites induce composites up to homotopy**: `Γ(χ ∘ φ) ≃ Γχ ∘ Γφ`. -/
theorem cwApproximationLift_comp_homotopic [PathConnectedSpace Y] [PathConnectedSpace Z]
    (χ : C(Y, Z)) (φ : C(X, Y)) :
    (cwApproximationLift x z (χ.comp φ)).Homotopic
      ((cwApproximationLift y z χ).comp (cwApproximationLift x y φ)) := by
  refine (homotopic_cwApproximationLift x z ?_).symm
  -- `c_Z ∘ Γχ ∘ Γφ ≃ χ ∘ c_Y ∘ Γφ ≃ χ ∘ φ ∘ c_X`.
  have h₁ := (comp_cwApproximationLift_homotopic y z χ).comp
    (Homotopic.refl (cwApproximationLift x y φ))
  have h₂ := (Homotopic.refl χ).comp (comp_cwApproximationLift_homotopic x y φ)
  rw [comp_assoc] at h₁ ⊢
  exact h₁.trans h₂

/-- **`Γφ` is a weak homotopy equivalence exactly when `φ` is**, for path-connected `X` and `Y`.
Since the CW approximations have CW type, `Γφ` is then a homotopy equivalence by Whitehead's
theorem (`ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquiv`). -/
theorem isWeakHomotopyEquivalence_cwApproximationLift_iff [PathConnectedSpace X]
    [PathConnectedSpace Y] {φ : C(X, Y)} :
    (cwApproximationLift x y φ).IsWeakHomotopyEquivalence ↔ φ.IsWeakHomotopyEquivalence := by
  have hX := isWeakHomotopyEquivalence_cwApproximationMap X x
  have hY := isWeakHomotopyEquivalence_cwApproximationMap Y y
  have h := comp_cwApproximationLift_homotopic x y φ
  refine ⟨fun hψ ↦ hX.of_precomp ((hY.comp hψ).of_homotopic h), fun hφ ↦ ?_⟩
  exact hY.of_postcomp ((hφ.comp hX).of_homotopic h.symm)

end TauCeti
