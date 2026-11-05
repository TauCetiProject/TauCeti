/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Basic
public import TauCeti.AlgebraicTopology.Homotopy.Whitehead
public import TauCeti.Topology.CWComplex.Classical.Sigma
public import TauCeti.Topology.Homotopy.HomotopyGroup.PathComponent

/-!
# CW approximation of an arbitrary space

Every space `X`, path-connected or not, is the target of a weak homotopy equivalence from a CW
complex (Hatcher, Proposition 4.13). The CW complex `TauCeti.sigmaCWApproximation X` is the
disjoint union, over the path components `c` of `X`, of the CW approximations
`TauCeti.cwApproximation X x_c` built from a chosen point `x_c` of each component, and
`TauCeti.sigmaCWApproximationMap X` is the map `cwApproximationMap X x_c` on the summand of `c`.

It is a weak homotopy equivalence
(`TauCeti.isWeakHomotopyEquivalence_sigmaCWApproximationMap`):

* it is a bijection on path components, since each summand is path-connected and is sent into the
  path component it approximates (`TauCeti.zerothHomotopyMk_sigmaCWApproximationMap`);
* on `πₖ`, `k ≥ 1`, at a point of the summand of `c`, it is the inverse of the bijection on `πₖ`
  induced by the inclusion of the summand (`HomotopyGroup.bijective_map_sigmaMk`), followed by the
  map induced by `cwApproximationMap X x_c`, which is bijective on `πₖ` although `X` need not be
  path-connected (`TauCeti.bijective_homotopyGroupMap_cwApproximationMap`).

The disjoint union of CW complexes is a CW complex
(`Topology.CWComplex.sigmaUniv`), so `TauCeti.sigmaCWApproximation X` has CW type. The lift through
an arbitrary weak homotopy equivalence (`ContinuousMap.IsWeakHomotopyEquivalence.lift`) then makes
the construction natural up to homotopy, with no connectedness hypothesis: a map `φ : X → Y`
induces `Γφ = TauCeti.sigmaCWApproximationLift φ`, for which the square

```
ΓX --Γφ--> ΓY
 |          |
 v          v
 X ---φ---> Y
```

commutes up to homotopy (`TauCeti.comp_sigmaCWApproximationLift_homotopic`, Hatcher,
Proposition 4.18), `Γφ` is determined up to homotopy by this
(`TauCeti.homotopic_sigmaCWApproximationLift`), and `Γ` is functorial up to homotopy. Any other CW
approximation of `X` is homotopy equivalent to this one compatibly with the maps to `X`
(`ContinuousMap.IsWeakHomotopyEquivalence.exists_homotopyEquiv_comp_homotopic`).

## Main definitions

* `TauCeti.sigmaCWApproximation X`: the CW approximation of `X`, one summand for each path
  component.
* `TauCeti.sigmaCWApproximationMap X`: its map to `X`.
* `TauCeti.sigmaCWApproximationLift φ`: the map of CW approximations induced by `φ : X → Y`.

## Main results

* `TauCeti.cwType_sigmaCWApproximation`: the approximation has CW type.
* `TauCeti.isWeakHomotopyEquivalence_sigmaCWApproximationMap`: **CW approximation** of an
  arbitrary space.
* `TauCeti.comp_sigmaCWApproximationLift_homotopic` and
  `TauCeti.homotopic_sigmaCWApproximationLift`: naturality up to homotopy, and uniqueness of the
  induced map.
* `TauCeti.sigmaCWApproximationLift_id_homotopic` and
  `TauCeti.sigmaCWApproximationLift_comp_homotopic`: functoriality up to homotopy.
* `TauCeti.isWeakHomotopyEquivalence_sigmaCWApproximationLift_iff`: `Γφ` is a weak homotopy
  equivalence exactly when `φ` is.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Propositions 4.13 and 4.18 and Corollary 4.19.
-/

public section

noncomputable section

universe u

open CategoryTheory ContinuousMap

namespace TauCeti

section Construction

variable (X : TopCat.{u})

/-- The **CW approximation** of an arbitrary space `X`: the disjoint union, over the path
components `c` of `X`, of the CW approximations `TauCeti.cwApproximation X x_c` built from the
point `x_c = Quotient.out c` of the component. The body is exposed so that points of the summands
are points of this space by definition. -/
@[expose] def sigmaCWApproximation : TopCat.{u} :=
  TopCat.of (Σ c : ZerothHomotopy X, cwApproximation X (Quotient.out c))

/-- The map from the CW approximation `TauCeti.sigmaCWApproximation X` to `X`: on the summand of a
path component `c`, the map `TauCeti.cwApproximationMap X x_c`. -/
def sigmaCWApproximationMap : sigmaCWApproximation X ⟶ X :=
  TopCat.ofHom (ContinuousMap.sigma fun c ↦ (cwApproximationMap X (Quotient.out c)).hom)

/-- On the summand of `c`, the map `TauCeti.sigmaCWApproximationMap X` is
`TauCeti.cwApproximationMap X x_c`. -/
@[simp]
lemma sigmaCWApproximationMap_mk (c : ZerothHomotopy X) (p : cwApproximation X (Quotient.out c)) :
    sigmaCWApproximationMap X ⟨c, p⟩ = cwApproximationMap X (Quotient.out c) p :=
  (rfl)

/-- The inclusion of the summand of `c` followed by `TauCeti.sigmaCWApproximationMap X` is
`TauCeti.cwApproximationMap X x_c`. -/
lemma sigmaCWApproximationMap_comp_sigmaMk (c : ZerothHomotopy X) :
    (sigmaCWApproximationMap X).hom.comp (ContinuousMap.sigmaMk c) =
      (cwApproximationMap X (Quotient.out c)).hom :=
  (rfl)

/-- The map `TauCeti.sigmaCWApproximationMap X` sends the summand of a path component `c` into
`c`. -/
@[simp]
lemma zerothHomotopyMk_sigmaCWApproximationMap (p : sigmaCWApproximation X) :
    ZerothHomotopy.mk (sigmaCWApproximationMap X p) = p.1 := by
  obtain ⟨c, p⟩ := p
  -- `p` is joined to the base point of its summand, which goes to `x_c`.
  have h : Joined (cwApproximationMap X (Quotient.out c) (cwApproximationBasepoint X _))
      (cwApproximationMap X (Quotient.out c) p) :=
    (PathConnectedSpace.joined _ p).map (cwApproximationMap X (Quotient.out c)).hom.continuous
  rw [cwApproximationMap_cwApproximationBasepoint] at h
  rw [sigmaCWApproximationMap_mk, ← ZerothHomotopy.sound h.somePath]
  exact Quotient.out_eq c

/-- `TauCeti.sigmaCWApproximation X` is Hausdorff. -/
instance instT2SpaceSigmaCWApproximation : T2Space (sigmaCWApproximation X) :=
  -- Instance search does not find the summand instances through `Quotient.out c` on its own.
  have (c : ZerothHomotopy X) : T2Space (cwApproximation X (Quotient.out c)) := inferInstance
  inferInstanceAs (T2Space (Σ c : ZerothHomotopy X, cwApproximation X (Quotient.out c)))

/-- **The CW approximation of an arbitrary space has CW type**: a disjoint union of CW complexes is
a CW complex. -/
instance cwType_sigmaCWApproximation : CWType (sigmaCWApproximation X) :=
  letI (c : ZerothHomotopy X) :
      Topology.CWComplex (Set.univ : Set (cwApproximation X (Quotient.out c))) :=
    (cwApproximationCWComplex X (Quotient.out c)).toCWComplex
  haveI : T2Space (Σ c : ZerothHomotopy X, cwApproximation X (Quotient.out c)) :=
    instT2SpaceSigmaCWApproximation X
  CWType.of_cwComplex_univ (Σ c : ZerothHomotopy X, cwApproximation X (Quotient.out c))

/-- **CW approximation** (Hatcher, Proposition 4.13). For every space `X`, the map
`TauCeti.sigmaCWApproximationMap X` from the CW complex `TauCeti.sigmaCWApproximation X` to `X` is a
weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_sigmaCWApproximationMap :
    (sigmaCWApproximationMap X).hom.IsWeakHomotopyEquivalence := by
  refine isWeakHomotopyEquivalence_iff_joined.2 ⟨fun y ↦ ?_, fun a b hab ↦ ?_, fun n p ↦ ?_⟩
  · -- The base point of the summand of the path component of `y` goes to a point joined to `y`.
    refine ⟨⟨ZerothHomotopy.mk y, cwApproximationBasepoint X _⟩, ?_⟩
    have h : Joined (Quotient.out (ZerothHomotopy.mk y)) y := Quotient.mk_out (s := pathSetoid X) y
    rwa [← cwApproximationMap_cwApproximationBasepoint X (Quotient.out (ZerothHomotopy.mk y))] at h
  · -- Points with joined images lie in the same summand, which is path-connected.
    have hc : ZerothHomotopy.mk (sigmaCWApproximationMap X a) =
        ZerothHomotopy.mk (sigmaCWApproximationMap X b) :=
      ZerothHomotopy.sound hab.somePath
    rw [zerothHomotopyMk_sigmaCWApproximationMap, zerothHomotopyMk_sigmaCWApproximationMap] at hc
    obtain ⟨c, a⟩ := a
    obtain ⟨c', b⟩ := b
    obtain rfl : c = c' := hc
    exact (PathConnectedSpace.joined a b).map continuous_sigmaMk
  · -- On `πₙ₊₁` the map is the inverse of the inclusion of the summand of `p`, a bijection,
    -- followed by the CW approximation of the path component of that summand.
    obtain ⟨c, p⟩ := p
    have hcomp : HomotopyGroup.map (N := Fin (n + 1)) (x := (⟨c, p⟩ : sigmaCWApproximation X))
          (sigmaCWApproximationMap X).hom rfl ∘
        HomotopyGroup.map (x := p)
          (ContinuousMap.sigmaMk (X := fun c ↦ cwApproximation X (Quotient.out c)) c) rfl =
        HomotopyGroup.map (cwApproximationMap X (Quotient.out c)).hom
          (rfl : _ = (sigmaCWApproximationMap X).hom ⟨c, p⟩) :=
      HomotopyGroup.map_comp_map_of_comp_eq (sigmaCWApproximationMap_comp_sigmaMk X c) _ _ _
    have h : Function.Bijective (HomotopyGroup.map (N := Fin (n + 1))
        (cwApproximationMap X (Quotient.out c)).hom
          (rfl : _ = (sigmaCWApproximationMap X).hom ⟨c, p⟩)) :=
      bijective_homotopyGroupMap_cwApproximationMap X (Quotient.out c) n p
    rw [← hcomp] at h
    exact (Function.Bijective.of_comp_iff _ (HomotopyGroup.bijective_map_sigmaMk
      (Z := fun c ↦ cwApproximation X (Quotient.out c)) c p)).1 h

end Construction

section Naturality

variable {X Y Z : TopCat.{u}}

/-- The map `Γφ : ΓX → ΓY` of CW approximations induced by a map `φ : X → Y`: a lift of
`φ ∘ sigmaCWApproximationMap X` through the weak homotopy equivalence
`sigmaCWApproximationMap Y` (`ContinuousMap.IsWeakHomotopyEquivalence.lift`), so that the square of
`φ` and `Γφ` with the two CW approximation maps commutes up to homotopy
(`TauCeti.comp_sigmaCWApproximationLift_homotopic`). It is determined up to homotopy by this
property (`TauCeti.homotopic_sigmaCWApproximationLift`). -/
def sigmaCWApproximationLift (φ : C(X, Y)) : C(sigmaCWApproximation X, sigmaCWApproximation Y) :=
  (isWeakHomotopyEquivalence_sigmaCWApproximationMap Y).lift (sigmaCWApproximationMap X).hom φ

/-- **CW approximation is natural up to homotopy** (Hatcher, Proposition 4.18):
`sigmaCWApproximationMap Y ∘ Γφ ≃ φ ∘ sigmaCWApproximationMap X`. -/
theorem comp_sigmaCWApproximationLift_homotopic (φ : C(X, Y)) :
    ((sigmaCWApproximationMap Y).hom.comp (sigmaCWApproximationLift φ)).Homotopic
      (φ.comp (sigmaCWApproximationMap X).hom) :=
  (isWeakHomotopyEquivalence_sigmaCWApproximationMap Y).comp_lift_homotopic _ φ

/-- **Uniqueness of the induced map** (Hatcher, Proposition 4.18). Every map `ψ : ΓX → ΓY` for
which the CW approximation square of `φ` commutes up to homotopy is homotopic to `Γφ`. -/
theorem homotopic_sigmaCWApproximationLift {φ : C(X, Y)}
    {ψ : C(sigmaCWApproximation X, sigmaCWApproximation Y)}
    (hψ : ((sigmaCWApproximationMap Y).hom.comp ψ).Homotopic
      (φ.comp (sigmaCWApproximationMap X).hom)) :
    ψ.Homotopic (sigmaCWApproximationLift φ) :=
  (isWeakHomotopyEquivalence_sigmaCWApproximationMap Y).homotopic_lift hψ

/-- Homotopic maps induce homotopic maps of CW approximations. -/
theorem sigmaCWApproximationLift_homotopic_of_homotopic {φ φ' : C(X, Y)} (h : φ.Homotopic φ') :
    (sigmaCWApproximationLift φ).Homotopic (sigmaCWApproximationLift φ') :=
  (isWeakHomotopyEquivalence_sigmaCWApproximationMap Y).lift_homotopic_of_homotopic _ h

/-- **The identity induces the identity up to homotopy.** -/
theorem sigmaCWApproximationLift_id_homotopic :
    (sigmaCWApproximationLift (ContinuousMap.id X)).Homotopic (ContinuousMap.id _) :=
  (isWeakHomotopyEquivalence_sigmaCWApproximationMap X).lift_id_homotopic

/-- **Composites induce composites up to homotopy**: `Γ(χ ∘ φ) ≃ Γχ ∘ Γφ`. -/
theorem sigmaCWApproximationLift_comp_homotopic (χ : C(Y, Z)) (φ : C(X, Y)) :
    (sigmaCWApproximationLift (χ.comp φ)).Homotopic
      ((sigmaCWApproximationLift χ).comp (sigmaCWApproximationLift φ)) :=
  (isWeakHomotopyEquivalence_sigmaCWApproximationMap Y).lift_comp_homotopic
    (isWeakHomotopyEquivalence_sigmaCWApproximationMap Z) _ χ φ

/-- **`Γφ` is a weak homotopy equivalence exactly when `φ` is.** Since the CW approximations have
CW type, `Γφ` is then a homotopy equivalence by Whitehead's theorem
(`ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquiv`). -/
@[simp]
theorem isWeakHomotopyEquivalence_sigmaCWApproximationLift_iff {φ : C(X, Y)} :
    (sigmaCWApproximationLift φ).IsWeakHomotopyEquivalence ↔ φ.IsWeakHomotopyEquivalence :=
  (isWeakHomotopyEquivalence_sigmaCWApproximationMap X).isWeakHomotopyEquivalence_lift_iff
    (isWeakHomotopyEquivalence_sigmaCWApproximationMap Y)

end Naturality

end TauCeti
