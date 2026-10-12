/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Tau
public import TauCeti.KnotTheory.Grid.Stabilization.Comparison
public import TauCeti.KnotTheory.Grid.Stabilization.Components
public import TauCeti.KnotTheory.Grid.Stabilization.Map.Grading

/-!
# Stabilization invariance of `GH⁻` and of `τ`

Let `G` be a grid diagram of size `n`, let `s` be a column, and let
`G' = G.stabilizeX s.castSucc (G.X s).castSucc s` be the stabilization splitting the `X`-marking
of column `s`. Write `A = R[V₀, …, V_{n-1}]` and `S = R[V₀, …, V_n]` for the coefficient rings of
`GC⁻(G)` and `GC⁻(G')`, and `σ : S → A` for the renaming of variables along `s.predAbove`, which
merges the two variables `V_{s.castSucc}` and `V_{s.succ}` of the new block into `V_s`.

The stabilization chain map `GC⁻(G') ⟶ GC⁻(G)` (`GridDiagram.stabilizeXMap`) is a
quasi-isomorphism of complexes of `A`-modules (`GridDiagram.quasiIso_stabilizeXMap`, with
`GridDiagram.quasiIso_stabilizeXOffCenterToCenterHom`). On chains it is `H_I^N` of the off-center
part followed by `σ` on coefficients, so it is even `σ`-semilinear over `S`
(`GridDiagram.stabilizeXChainMap`). This file descends it to a `σ`-semilinear map
`GH⁻(G') → GH⁻(G)` on unblocked grid homology (`GridDiagram.stabilizeXHomologyMap`), sending the
class of a cycle `z` to the class of its image, and shows that this map is bijective and, for a
diagram with an odd number of components, preserves the Alexander grading.

For a knot grid `G`, the diagram `G'` is again a knot grid, and `U` acts on both homologies as
any one variable. Since `σ` commutes with the evaluation `V_j ↦ U`, the map on homology is an
isomorphism of graded `R[U]`-modules of Alexander degree zero, and therefore the invariants `τ` of
`G'` and `G` agree (`GridDiagram.IsKnot.tau_stabilizeX`). Only this one stabilization type is
treated here; the other stabilization types and commutation moves are not.

## Main definitions

* `TauCeti.GridDiagram.stabilizeXChainMap`: the stabilization chain map `GC⁻(G') → GC⁻(G)` as a
  `σ`-semilinear map.
* `TauCeti.GridDiagram.stabilizeXHomologyMap`: the induced `σ`-semilinear map
  `GH⁻(G') → GH⁻(G)`.

## Main results

* `TauCeti.GridDiagram.stabilizeXChainMap_unblockedDifferential`: `stabilizeXChainMap` commutes
  with the unblocked differentials.
* `TauCeti.GridDiagram.stabilizeXHomologyMap_unblockedHomologyClass`: the class of a cycle `z`
  goes to the class of `stabilizeXChainMap z`.
* `TauCeti.GridDiagram.stabilizeXHomologyMap_bijective`: **stabilization invariance of `GH⁻`**,
  the map on homology is bijective.
* `OddComponentGridDiagram.stabilizeXHomologyMap_mem_alexanderUnblockedHomologyGrading_piece`:
  it preserves the Alexander grading.
* `TauCeti.GridDiagram.IsKnot.tau_stabilizeX`: `τ(G') = τ(G)`.

## References

This is stabilization invariance of `GH⁻` for this stabilization type, and its consequence for
`τ`, in Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.2 and
Chapter 6; see also Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer
homology*, Geom. Topol. 11 (2007), Section 3.2.
-/

public section

open CategoryTheory MvPolynomial

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R]

local notation "A" => MvPolynomial (Fin n) R
local notation "S" => MvPolynomial (Fin (n + 1)) R

/-! ### The chain map as a semilinear map -/

/-- **The chain map of an `X`-stabilization, as a semilinear map.** On a chain `c` of `GC⁻(G')`
it is `H_I^N` of the off-center part of `c`, followed by renaming every coefficient along
`s.predAbove`. It is semilinear along that renaming `S → A`, and its underlying function is the
unique component of `stabilizeXMap` (`stabilizeXMap_f_apply`). -/
noncomputable def stabilizeXChainMap :
    GridChainMinus R (n + 1) →ₛₗ[(↑(rename (R := R) s.predAbove) : S →+* A)] GridChainMinus R n :=
  (Finsupp.mapRange.linearMap (↑(rename (R := R) s.predAbove) : S →+* A).toSemilinearMap).comp
    (G.stabilizeXOffCenterToCenter s R ∘ₗ G.stabilizeXOffCenterProjection s R)

/-- `stabilizeXChainMap` renames the coefficients of `H_I^N` of the off-center part. -/
theorem stabilizeXChainMap_apply (c : GridChainMinus R (n + 1)) :
    G.stabilizeXChainMap s R c = Finsupp.mapRange (rename s.predAbove) (map_zero _)
      (G.stabilizeXOffCenterToCenter s R (G.stabilizeXOffCenterProjection s R c)) :=
  (rfl)

variable [CharP R 2]

/-- `GC⁻(G')` with scalars restricted to `A`, with its object and differential spelled out. -/
private noncomputable abbrev stabilizeXSourceComplex :
    HomologicalComplex (ModuleCat A) (ComplexShape.refl Unit) where
  X _ := (ModuleCat.restrictScalars
    (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).obj
      (ModuleCat.of S (GridChainMinus R (n + 1)))
  d _ _ := (ModuleCat.restrictScalars
    (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).map
      (ModuleCat.ofHom ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R))
  d_comp_d' _ _ _ _ _ := by
    rw [← Functor.map_comp, ← ModuleCat.ofHom_comp, unblockedDifferential_comp_self_eq_zero,
      ModuleCat.ofHom_zero, Functor.map_zero]

/-- `GC⁻(G)` with its object and differential spelled out. -/
private noncomputable abbrev stabilizeXTargetComplex :
    HomologicalComplex (ModuleCat A) (ComplexShape.refl Unit) where
  X _ := ModuleCat.of A (GridChainMinus R n)
  d _ _ := ModuleCat.ofHom (G.unblockedDifferential R)
  d_comp_d' _ _ _ _ _ := by
    rw [← ModuleCat.ofHom_comp, unblockedDifferential_comp_self_eq_zero, ModuleCat.ofHom_zero]

/-- The source of `stabilizeXMap` is isomorphic to its spelled-out form. -/
private noncomputable def stabilizeXSourceComplexIso :
    ((ModuleCat.restrictScalars
      (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).mapHomologicalComplex
        _).obj ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex R) ≅
      G.stabilizeXSourceComplex s R :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ ↦ (ModuleCat.restrictScalars
      (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).mapIso
        (eqToIso ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex_X R ()))) (by
    rintro ⟨⟩ ⟨⟩ -
    simp [← Functor.map_comp])

/-- The target of `stabilizeXMap` is isomorphic to its spelled-out form. -/
private noncomputable def stabilizeXTargetComplexIso :
    G.unblockedComplex R ≅ G.stabilizeXTargetComplex R :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ eqToIso (G.unblockedComplex_X R ())) (by
    rintro ⟨⟩ ⟨⟩ -
    simp)

/-- `stabilizeXMap` between the spelled-out complexes. -/
private noncomputable def stabilizeXMap' :
    G.stabilizeXSourceComplex s R ⟶ G.stabilizeXTargetComplex R :=
  (G.stabilizeXSourceComplexIso s R).inv ≫ G.stabilizeXMap s R ≫
    (G.stabilizeXTargetComplexIso R).hom

private instance quasiIso_stabilizeXMap' : QuasiIso (G.stabilizeXMap' s R) := by
  rw [stabilizeXMap']
  infer_instance

/-- The component of `stabilizeXMap'` is `stabilizeXChainMap`. -/
private theorem stabilizeXMap'_f_apply (c : GridChainMinus R (n + 1)) :
    ((G.stabilizeXMap' s R).f ()).hom c = G.stabilizeXChainMap s R c := by
  rw [stabilizeXChainMap_apply, ← stabilizeXMap_f_apply]
  simp [stabilizeXMap', stabilizeXSourceComplexIso, stabilizeXTargetComplexIso]

/-- **`stabilizeXChainMap` is a chain map**: it intertwines the unblocked differentials of `G'`
and `G`. -/
theorem stabilizeXChainMap_unblockedDifferential (c : GridChainMinus R (n + 1)) :
    G.stabilizeXChainMap s R
        ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R c) =
      G.unblockedDifferential R (G.stabilizeXChainMap s R c) := by
  have h := LinearMap.congr_fun (G.stabilizeXMap' s R).hom_f_comp_hom_d c
  simp only [LinearMap.coe_comp] at h
  rw [← stabilizeXMap'_f_apply, ← stabilizeXMap'_f_apply]
  exact h

/-- `stabilizeXChainMap` sends cycles of `GC⁻(G')` to cycles of `GC⁻(G)`. -/
theorem stabilizeXChainMap_mem_ker {c : GridChainMinus R (n + 1)}
    (hc : c ∈ LinearMap.ker
      ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R)) :
    G.stabilizeXChainMap s R c ∈ LinearMap.ker (G.unblockedDifferential R) := by
  rw [LinearMap.mem_ker] at hc ⊢
  rw [← stabilizeXChainMap_unblockedDifferential, hc, map_zero]

/-- Every cycle of `GC⁻(G)` differs from the image of a cycle of `GC⁻(G')` by a boundary. -/
private theorem exists_sub_stabilizeXChainMap_mem_range {c : GridChainMinus R n}
    (hc : c ∈ LinearMap.ker (G.unblockedDifferential R)) :
    ∃ m ∈ LinearMap.ker ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R),
      c - G.stabilizeXChainMap s R m ∈ LinearMap.range (G.unblockedDifferential R) := by
  have h := ((HomologicalComplex.quasiIso_iff_bijective_homologyMap _).mp
    (G.quasiIso_stabilizeXMap' s R)).2
  rw [LinearMap.homologyMap_surjective_iff] at h
  obtain ⟨m, hm, hcm⟩ := h c hc
  exact ⟨m, hm, G.stabilizeXMap'_f_apply s R m ▸ hcm⟩

/-- A cycle of `GC⁻(G')` whose image in `GC⁻(G)` is a boundary is itself a boundary. -/
private theorem mem_range_of_stabilizeXChainMap_mem_range {m : GridChainMinus R (n + 1)}
    (hm : m ∈ LinearMap.ker ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R))
    (h : G.stabilizeXChainMap s R m ∈ LinearMap.range (G.unblockedDifferential R)) :
    m ∈ LinearMap.range ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R) := by
  have hinj := ((HomologicalComplex.quasiIso_iff_bijective_homologyMap _).mp
    (G.quasiIso_stabilizeXMap' s R)).1
  rw [LinearMap.homologyMap_injective_iff] at hinj
  exact hinj m hm (by rwa [stabilizeXMap'_f_apply])

/-! ### The map on homology -/

/-- **The map of an `X`-stabilization on unblocked grid homology**, `GH⁻(G') → GH⁻(G)`: the class
of a cycle `z` goes to the class of `stabilizeXChainMap z`. It is semilinear along the renaming
`S → A` along `s.predAbove`. -/
noncomputable def stabilizeXHomologyMap :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedHomology R →ₛₗ[
      (↑(rename (R := R) s.predAbove) : S →+* A)] G.unblockedHomology R :=
  (G.unblockedHomologyIso R).toLinearEquiv.symm.toLinearMap.comp <|
    (Submodule.mapQ _ _ ((G.stabilizeXChainMap s R).restrict
        fun _ hc ↦ G.stabilizeXChainMap_mem_ker s R hc) (by
      rintro z ⟨w, hw⟩
      refine ⟨G.stabilizeXChainMap s R w, ?_⟩
      simp only [Submodule.subtype_apply, LinearMap.restrict_apply] at hw ⊢
      rw [← stabilizeXChainMap_unblockedDifferential, hw])).comp
    ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedHomologyIso R).toLinearEquiv.toLinearMap

/-- `stabilizeXHomologyMap` sends the class of a cycle `z` to the class of
`stabilizeXChainMap z`. -/
@[simp]
theorem stabilizeXHomologyMap_unblockedHomologyClass
    (z : LinearMap.ker ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R)) :
    G.stabilizeXHomologyMap s R
        ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedHomologyClass R z) =
      G.unblockedHomologyClass R
        ⟨G.stabilizeXChainMap s R z, G.stabilizeXChainMap_mem_ker s R z.2⟩ := by
  simp only [stabilizeXHomologyMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_eq]
  rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply,
    unblockedHomologyIso_hom_unblockedHomologyClass,
    unblockedHomologyIso_hom_unblockedHomologyClass]
  simp [LinearMap.restrict_apply]

/-- **Stabilization invariance of `GH⁻`.** The map `GH⁻(G') → GH⁻(G)` induced by the
stabilization chain map is bijective. -/
theorem stabilizeXHomologyMap_bijective : Function.Bijective (G.stabilizeXHomologyMap s R) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun y hy ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := unblockedHomologyClass_surjective _ R y
    rw [stabilizeXHomologyMap_unblockedHomologyClass, unblockedHomologyClass_eq_zero_iff] at hy
    rw [unblockedHomologyClass_eq_zero_iff]
    exact G.mem_range_of_stabilizeXChainMap_mem_range s R z.2 hy
  · obtain ⟨c, rfl⟩ := unblockedHomologyClass_surjective _ R y
    obtain ⟨m, hm, hcm⟩ := G.exists_sub_stabilizeXChainMap_mem_range s R c.2
    refine ⟨_, (G.stabilizeXHomologyMap_unblockedHomologyClass s R ⟨m, hm⟩).trans ?_⟩
    rw [← sub_eq_zero, ← map_sub, unblockedHomologyClass_eq_zero_iff, Submodule.coe_sub,
      ← neg_sub]
    exact neg_mem hcm

end GridDiagram

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (s : Fin n) (R : Type*) [CommRing R] [CharP R 2]

/-- **The map of an `X`-stabilization on `GH⁻` preserves the Alexander grading.** The
stabilization `G'` of `G` again has an odd number of components, and a class of `GH⁻(G')` of
Alexander degree `a` goes to a class of `GH⁻(G)` of Alexander degree `a`. -/
theorem stabilizeXHomologyMap_mem_alexanderUnblockedHomologyGrading_piece {a : ℤ}
    {y : (G.1.stabilizeX s.castSucc (G.1.X s).castSucc s).unblockedHomology R}
    (hy : y ∈ (alexanderUnblockedHomologyGrading
      ⟨G.1.stabilizeX s.castSucc (G.1.X s).castSucc s,
        (G.1.componentCount_stabilizeX _ _ _).symm ▸ G.2⟩ R).piece a) :
    G.1.stabilizeXHomologyMap s R y ∈ (G.alexanderUnblockedHomologyGrading R).piece a := by
  rw [mem_alexanderUnblockedHomologyGrading_piece_iff, mem_alexanderHomologyGrading_piece_iff]
    at hy ⊢
  obtain ⟨z, hz, hzy⟩ := hy
  obtain rfl : y = (G.1.stabilizeX s.castSucc (G.1.X s).castSucc s).unblockedHomologyClass R z := by
    apply ((ModuleCat.mono_iff_injective
      ((G.1.stabilizeX s.castSucc (G.1.X s).castSucc s).unblockedHomologyIso R).hom).mp
        inferInstance)
    rw [GridDiagram.unblockedHomologyIso_hom_unblockedHomologyClass, hzy]
  refine ⟨_, ?_, (GridDiagram.unblockedHomologyIso_hom_unblockedHomologyClass _ _ _).symm.trans
    (congrArg _ (G.1.stabilizeXHomologyMap_unblockedHomologyClass s R z).symm)⟩
  have hG' : G.stabilizeX s = ⟨G.1.stabilizeX s.castSucc (G.1.X s).castSucc s,
      (G.1.componentCount_stabilizeX _ _ _).symm ▸ G.2⟩ :=
    Subtype.ext (G.val_stabilizeX s)
  have key : ∀ c, c ∈ alexanderChainMinusPiece ⟨G.1.stabilizeX s.castSucc (G.1.X s).castSucc s,
      (G.1.componentCount_stabilizeX _ _ _).symm ▸ G.2⟩ R a →
        G.1.stabilizeXChainMap s R c ∈ G.alexanderChainMinusPiece R a := by
    rw [← hG']
    intro c hc
    have h := G.stabilizeXMap_mem_alexanderChainMinusPiece s R hc
    rwa [GridDiagram.stabilizeXMap_f_apply] at h
  exact key _ hz

end OddComponentGridDiagram

namespace GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (s : Fin n)
  (K : Type*) [CommRing K] [CharP K 2]

/-- **`τ` is invariant under `X`-stabilization.** The stabilization of a knot grid `G` splitting
the `X`-marking of column `s` is a knot grid with the same invariant `τ`. -/
theorem tau_stabilizeX :
    ((G.isKnot_stabilizeX s.castSucc (G.X s).castSucc s).mpr hG).tau K = hG.tau K := by
  refine ((G.isKnot_stabilizeX s.castSucc (G.X s).castSucc s).mpr hG).tau_eq_of_semilinearMap K hG
    (fun p ↦ by rw [AlgHom.coe_toRingHom, aeval_rename, Function.comp_def])
    (G.stabilizeXHomologyMap s K) (G.stabilizeXHomologyMap_bijective s K) fun a y hy ↦ ?_
  rw [mem_alexanderUnblockedHomologyGrading_piece_iff,
    ← OddComponentGridDiagram.mem_alexanderUnblockedHomologyGrading_piece_iff]
  rw [mem_alexanderUnblockedHomologyGrading_piece_iff,
    ← OddComponentGridDiagram.mem_alexanderUnblockedHomologyGrading_piece_iff] at hy
  exact OddComponentGridDiagram.stabilizeXHomologyMap_mem_alexanderUnblockedHomologyGrading_piece
    _ s K hy

end GridDiagram.IsKnot

end TauCeti
