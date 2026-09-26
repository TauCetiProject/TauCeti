/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import TauCeti.KnotTheory.Grid.Stabilization.PolynomialExtension
public import TauCeti.KnotTheory.Grid.Stabilization.XHomotopy

/-!
# The chain map of an `X`-stabilization

Let `G` be a grid diagram of size `n`, let `s` be a column, and let
`G' = G.stabilizeX s.castSucc (G.X s).castSucc s` be the stabilization splitting the `X`-marking
of column `s`. Write `A = R[V₀, …, V_{n-1}]` and `S = R[V₀, …, V_n]` for the coefficient rings of
`GC⁻(G)` and `GC⁻(G')`, with `S` an `A`-algebra through the renaming of the columns of `G` into
those of `G'`.

This file assembles the comparison map `GC⁻(G') ⟶ GC⁻(G)` of complexes of `A`-modules from the
three pieces already available:

* `GC⁻(G')` is the mapping cone of the connecting map `∂_I^N` from the center complex `I` to the
  off-center complex `N` (`unblockedComplexStabilizeXIsoHomotopyCofiber`);
* the component `H_I^N : N ⟶ I` of the `X`-marking homotopy satisfies
  `∂_I^N ≫ H_I^N = V_{s.succ} + V_{s.castSucc}`
  (`stabilizeXConnectingHom_comp_offCenterToCenterHom`), so the pair `(𝟙, H_I^N)` is a
  morphism from the arrow `∂_I^N` to the arrow given by multiplication by
  `V_{s.succ} + V_{s.castSucc}` on `I`, and induces a map of mapping cones (`stabilizeXConeMap`);
* after restricting scalars to `A`, the mapping cone of multiplication by
  `V_{s.succ} + V_{s.castSucc}` on `I` is homotopy equivalent to `GC⁻(G)`
  (`stabilizeXCenterConeHomotopyEquiv`).

On off-center chains the composite `stabilizeXMap` is `H_I^N` followed by the evaluation
`V_{s.castSucc} ↦ V_s` that merges the two variables of the new block
(`map_offCenterInclusion_comp_stabilizeXMap`). It vanishes on center chains
(`map_centerInclusion_comp_stabilizeXMap`). Since maps of mapping cones induced by
quasi-isomorphisms are quasi-isomorphisms
(`HomologicalComplex.homotopyCofiber.quasiIso_mapArrowHom`), `stabilizeXMap` is a
quasi-isomorphism as soon as `H_I^N` is (`quasiIso_stabilizeXMap`). This reduces the
stabilization invariance of `GH⁻` for this stabilization to the statement that `H_I^N` is a
quasi-isomorphism, which is not proved here.

## Main definitions

* `TauCeti.GridDiagram.stabilizeXConeMap`: the map of mapping cones induced by `(𝟙, H_I^N)`.
* `TauCeti.GridDiagram.stabilizeXMap`: the chain map `GC⁻(G') ⟶ GC⁻(G)` of complexes of
  `A`-modules.

## Main results

* `TauCeti.GridDiagram.quasiIso_stabilizeXConeMap` and `TauCeti.GridDiagram.quasiIso_stabilizeXMap`:
  both maps are quasi-isomorphisms if `H_I^N` is.
* `TauCeti.GridDiagram.map_offCenterInclusion_comp_stabilizeXMap`: on off-center chains,
  `stabilizeXMap` is `H_I^N` followed by evaluation at `V_s`.
* `TauCeti.GridDiagram.inlX_stabilizeXConeMap` and
  `TauCeti.GridDiagram.map_centerInclusion_comp_stabilizeXMap`: the cone map is the identity on
  the center summand, while `stabilizeXMap` vanishes there.

## References

This is the comparison of the stabilized complex with the mapping cone of `V₁ - V₂` in
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.2, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.2.
-/

public section

open CategoryTheory HomologicalComplex MvPolynomial

namespace TauCeti

namespace GridDiagram

universe u

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type u) [CommRing R] [CharP R 2]

local notation "A" => MvPolynomial (Fin n) R
local notation "S" => MvPolynomial (Fin (n + 1)) R

/-- The square `(𝟙, H_I^N)` from the connecting map `∂_I^N` to multiplication by
`V_{s.succ} + V_{s.castSucc}` on the center complex. -/
private noncomputable def stabilizeXConeArrowHom :
    Arrow.mk (G.stabilizeXConnectingHom s R) ⟶
      Arrow.mk ((MvPolynomial.X s.succ + MvPolynomial.X s.castSucc : S) •
        𝟙 (G.stabilizeXCenterComplex s R)) :=
  Arrow.homMk' (𝟙 _) (G.stabilizeXOffCenterToCenterHom s R)
    (by rw [Category.id_comp, G.stabilizeXConnectingHom_comp_offCenterToCenterHom s R])

/-- **The map of mapping cones induced by `H_I^N`.** The pair `(𝟙, H_I^N)` maps the connecting
map `∂_I^N` from the center complex to the off-center complex to multiplication by
`V_{s.succ} + V_{s.castSucc}` on the center complex, and so induces a map from the mapping cone of
`∂_I^N`, which is `GC⁻(G')`, to the mapping cone of `V_{s.succ} + V_{s.castSucc}`. -/
noncomputable def stabilizeXConeMap :
    homotopyCofiber (G.stabilizeXConnectingHom s R) ⟶
      homotopyCofiber ((MvPolynomial.X s.succ + MvPolynomial.X s.castSucc : S) •
        𝟙 (G.stabilizeXCenterComplex s R)) :=
  homotopyCofiber.mapArrowHom _ _ (fun j => ⟨j, ComplexShape.refl_rel j⟩)
    (G.stabilizeXConeArrowHom s R)

/-- On the off-center summand of the cone, `stabilizeXConeMap` is `H_I^N` followed by the
inclusion of the center complex into the cone of `V_{s.succ} + V_{s.castSucc}`. -/
@[reassoc (attr := simp)]
theorem inr_stabilizeXConeMap :
    homotopyCofiber.inr _ ≫ G.stabilizeXConeMap s R =
      G.stabilizeXOffCenterToCenterHom s R ≫ homotopyCofiber.inr _ := by
  simp [stabilizeXConeMap, stabilizeXConeArrowHom]

/-- On the center summand, `stabilizeXConeMap` is the identity into the center summand of
the target cone. -/
@[reassoc (attr := simp)]
theorem inlX_stabilizeXConeMap :
    homotopyCofiber.inlX (G.stabilizeXConnectingHom s R) () ()
        (ComplexShape.refl_rel ()) ≫ (G.stabilizeXConeMap s R).f () =
      homotopyCofiber.inlX
        ((MvPolynomial.X s.succ + MvPolynomial.X s.castSucc : S) •
          𝟙 (G.stabilizeXCenterComplex s R)) () () (ComplexShape.refl_rel ()) := by
  simp [stabilizeXConeMap, stabilizeXConeArrowHom]

/-- The map of cones `stabilizeXConeMap` is a quasi-isomorphism if `H_I^N` is. -/
theorem quasiIso_stabilizeXConeMap [QuasiIso (G.stabilizeXOffCenterToCenterHom s R)] :
    QuasiIso (G.stabilizeXConeMap s R) := by
  have : QuasiIso (G.stabilizeXConeArrowHom s R).left := inferInstanceAs (QuasiIso (𝟙 _))
  have : QuasiIso (G.stabilizeXConeArrowHom s R).right :=
    inferInstanceAs (QuasiIso (G.stabilizeXOffCenterToCenterHom s R))
  exact homotopyCofiber.quasiIso_mapArrowHom _ _ _ _

/-- **The chain map of an `X`-stabilization.** The map `GC⁻(G') ⟶ GC⁻(G)` of complexes of
`A`-modules obtained by presenting `GC⁻(G')` as the mapping cone of `∂_I^N`, applying the map of
cones induced by `(𝟙, H_I^N)`, and comparing the mapping cone of `V_{s.succ} + V_{s.castSucc}` on
the center complex with `GC⁻(G)`. The source is `GC⁻(G')` with scalars restricted to `A`. -/
noncomputable def stabilizeXMap :
    ((ModuleCat.restrictScalars
      (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).mapHomologicalComplex
        _).obj ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex R) ⟶
      G.unblockedComplex R :=
  ((ModuleCat.restrictScalars
      (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).mapHomologicalComplex
        _).map ((G.unblockedComplexStabilizeXIsoHomotopyCofiber s R).hom ≫
      G.stabilizeXConeMap s R) ≫
    (G.stabilizeXCenterConeHomotopyEquiv s R).hom

/-- **Stabilization invariance reduces to `H_I^N`.** The chain map `GC⁻(G') ⟶ GC⁻(G)` of an
`X`-stabilization is a quasi-isomorphism if the component `H_I^N` of the `X`-marking homotopy
from off-center states to center states is. -/
theorem quasiIso_stabilizeXMap [QuasiIso (G.stabilizeXOffCenterToCenterHom s R)] :
    QuasiIso (G.stabilizeXMap s R) := by
  have := G.quasiIso_stabilizeXConeMap s R
  rw [stabilizeXMap]
  infer_instance

/-- On off-center chains, the chain map of an `X`-stabilization is `H_I^N` followed by the
evaluation `V_{s.castSucc} ↦ V_s` of the polynomial extension of `GC⁻(G)`. Here
`homotopyCofiber.inr _ ≫ (unblockedComplexStabilizeXIsoHomotopyCofiber G s R).inv` is the
inclusion of the off-center complex into `GC⁻(G')`. -/
@[simp] theorem map_offCenterInclusion_comp_stabilizeXMap :
    ((ModuleCat.restrictScalars
      (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).mapHomologicalComplex
        _).map (homotopyCofiber.inr (G.stabilizeXConnectingHom s R)) ≫
          (((ModuleCat.restrictScalars
            (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).mapHomologicalComplex
              _).map (G.unblockedComplexStabilizeXIsoHomotopyCofiber s R).inv ≫
            G.stabilizeXMap s R) =
      ((ModuleCat.restrictScalars
        (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).mapHomologicalComplex
          _).map (G.stabilizeXOffCenterToCenterHom s R) ≫
        (G.polynomialExtensionIsoStabilizeXCenter s R).inv ≫
          (G.unblockedComplex R).polynomialExtensionEval (MvPolynomial.X s) := by
  calc
    _ = ((ModuleCat.restrictScalars
        (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).mapHomologicalComplex
          _).map (homotopyCofiber.inr (G.stabilizeXConnectingHom s R) ≫
            (G.unblockedComplexStabilizeXIsoHomotopyCofiber s R).inv) ≫
          G.stabilizeXMap s R := by rw [← Category.assoc, ← Functor.map_comp]
    _ = _ := by
      rw [stabilizeXMap, ← Category.assoc, ← Functor.map_comp, Category.assoc,
        Iso.inv_hom_id_assoc, inr_stabilizeXConeMap, Functor.map_comp, Category.assoc,
        map_inr_comp_stabilizeXCenterConeHomotopyEquiv_hom]

/-- On center states, `stabilizeXMap` vanishes. The first factor includes the center summand
of the cone into `GC⁻(G')`, with scalars restricted to `A`. -/
@[simp] theorem map_centerInclusion_comp_stabilizeXMap :
    (ModuleCat.restrictScalars
      (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).map
        (eqToHom (G.stabilizeXCenterComplex_X s R ())) ≫
      (ModuleCat.restrictScalars
        (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).map
        (ModuleCat.ofHom (G.stabilizeXCenterInclusion s R)) ≫
      (ModuleCat.restrictScalars
        (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).map
        (eqToHom ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex_X R ()).symm) ≫
        (G.stabilizeXMap s R).f () = 0 := by
  have h : homotopyCofiber.inlX (G.stabilizeXConnectingHom s R) () ()
      (ComplexShape.refl_rel ()) ≫ (G.unblockedComplexStabilizeXIsoHomotopyCofiber s R).inv.f () =
      eqToHom (G.stabilizeXCenterComplex_X s R ()) ≫
        ModuleCat.ofHom (G.stabilizeXCenterInclusion s R) ≫
          eqToHom ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex_X R ()).symm := by
    rw [unblockedComplexStabilizeXIsoHomotopyCofiber_inv_f]
    simp
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, ← h]
  rw [stabilizeXMap]
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  simp only [← Category.assoc, ← Functor.map_comp]
  simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
    HomologicalComplex.id_f]
  simp [inlX_stabilizeXConeMap, map_inlX_comp_stabilizeXCenterConeHomotopyEquiv_hom]

end GridDiagram

end TauCeti
