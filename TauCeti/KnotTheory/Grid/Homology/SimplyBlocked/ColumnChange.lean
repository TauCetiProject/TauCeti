/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
public import TauCeti.KnotTheory.Grid.Homology.Series.SimplyBlocked
public import TauCeti.KnotTheory.Grid.XHomotopy.Grading
import TauCeti.Algebra.CharP.Two

/-!
# Simply blocked grid homology does not depend on the blocked `O`-marking

Simply blocked grid homology `G-hat` is the homology of the unblocked grid complex `GC⁻` with one
variable `V_i` set to zero. For a knot grid it does not depend on the choice of the blocked column
`i`: this file constructs, for any two columns `i` and `j`, an isomorphism between the homologies
of the two specializations which preserves the (`O`-Maslov, Alexander) bigrading, so the bigraded
Poincaré series and the Alexander-graded Euler characteristic of `G-hat` are independent of `i`.

The comparison is the one obtained from the mapping cones of `V_i` and `V_j`. Write `π_i` for
specialization at `V_i = 0` and `L_i` for the lift of a specialized chain including its surviving
variables (`simplyBlockedLift`). Since `π_i` intertwines the differentials and kills exactly the
multiples of `V_i`, on which `V_i` acts injectively,

`∂⁻ (L_i c) - L_i (∂_i c) = V_i • ρ_i c`

for a unique unblocked chain `ρ_i c`, the *connecting map* (`simplyBlockedConnectingMap`), named
after the connecting map of the long exact sequence of `V_i` that it describes on cycles. Given a
map `H`
on `GC⁻` with `∂⁻ H + H ∂⁻ = V_i + V_j`, the semilinear map

`Φ c = π_j (L_i c + H (ρ_i c))`

intertwines the two specialized differentials
(`simplyBlockedColumnChangeMap_simplyBlockedDifferential`)
and induces a bijection on homology
(`oneVariableSpecializationColumnChangeHomologyMap_bijective`). In characteristic two this is the
composite `Cone(V_i) ≅ Cone(V_j)` of the isomorphism of mapping cones `(a, b) ↦ (a + H b, b)`
with the quasi-isomorphisms between a mapping cone of an injective map and its cokernel; here the
cones are never formed, and bijectivity is checked directly on cycles. No knot hypothesis is
needed for this part: two columns on the same component of a link are related by such a homotopy
as well.

On a knot grid the variables of all columns are homotopic through the `X`-marking homotopies
(`GridDiagram.IsKnot.XSmulHomotopy`), which have bidegree `(-1, -1)`. With this homotopy `Φ`
preserves bidegrees, giving the degree-zero equivalence
`GridDiagram.IsKnot.simplyBlockedHomologyColumnChangeEquiv` of the bigraded simply blocked
homologies for the blocked columns `i` and `j`.

## Main definitions

* `TauCeti.GridDiagram.simplyBlockedConnectingMap`: the connecting map `ρ_i`.
* `TauCeti.GridDiagram.simplyBlockedColumnChangeMap`: the chain map `Φ` from the specialization
  at `V_i = 0` to the specialization at `V_j = 0`.
* `TauCeti.GridDiagram.oneVariableSpecializationColumnChangeHomologyMap`: the map it induces on
  homology.
* `TauCeti.GridDiagram.IsKnot.simplyBlockedHomologyColumnChangeEquiv`: for a knot grid, the
  coefficient-linear equivalence of simply blocked homologies blocking the columns `i` and `j`.

## Main results

* `TauCeti.GridDiagram.oneVariableSpecializationColumnChangeHomologyMap_bijective`: the change of
  blocked column induces a bijection on homology.
* `GridDiagram.IsKnot.simplyBlockedHomologyColumnChangeEquiv_mem_bigradedHatHomologyPiece_iff`:
  for a knot grid it preserves and reflects both homology degrees.
* `TauCeti.GridDiagram.IsKnot.bigradedSimplyBlockedHomologyPoincareSeries_columnChange` and
  `TauCeti.GridDiagram.IsKnot.gradedSimplyBlockedHomologyEulerChar_columnChange`: over a field of
  characteristic two, the bigraded Poincaré series and the Alexander-graded Euler characteristic of
  `G-hat` do not depend on the blocked column.

## References

* Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 4.6: simply blocked grid
  homology, defined by blocking one `O`-marking, and the `X`-marking homotopies of Lemma 4.6.9.
* Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Geom. Topol. 11
  (2007), Section 2 (arXiv:math/0610559).
-/

public section

open CategoryTheory MvPolynomial

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-! ### The connecting map -/

section Connecting

variable (R : Type*) [CommRing R] (i : Fin n)

/-- The lift of a specialized chain commutes with the differentials up to a multiple of `V_i`. -/
private theorem exists_X_smul_eq_unblockedDifferential_simplyBlockedLift_sub
    (c : GridChainHat R n i) :
    ∃ r : GridChainMinus R n, (MvPolynomial.X i : MvPolynomial (Fin n) R) • r =
      G.unblockedDifferential R (simplyBlockedLift R i c) -
        simplyBlockedLift R i (G.simplyBlockedDifferential R i c) :=
  (exact_X_smul_simplyBlockedSpecialization R i _).mp (by
    rw [map_sub, simplyBlockedSpecialization_unblockedDifferential,
      simplyBlockedSpecialization_simplyBlockedLift, simplyBlockedSpecialization_simplyBlockedLift,
      sub_self])

/-- The *connecting map* `ρ_i` of the specialization at `V_i = 0`: a specialized chain `c` goes to
the unique unblocked chain `ρ_i c` with `V_i • ρ_i c = ∂⁻ (L_i c) - L_i (∂_i c)`
(`X_smul_simplyBlockedConnectingMap`), where `L_i` is the lift `simplyBlockedLift`. On cycles this
is the usual chain-level description of the connecting map of the long exact sequence of
multiplication by `V_i`; that identification is not used or proved here. -/
noncomputable def simplyBlockedConnectingMap : GridChainHat R n i →ₗ[R] GridChainMinus R n :=
  (LinearEquiv.ofInjective (DistribSMul.toLinearMap R (GridChainMinus R n)
      (MvPolynomial.X i : MvPolynomial (Fin n) R))
        (X_smul_gridChainMinus_injective R i)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict _
      ((G.unblockedDifferential R).restrictScalars R ∘ₗ simplyBlockedLift R i -
        simplyBlockedLift R i ∘ₗ (G.simplyBlockedDifferential R i).restrictScalars R)
      fun c => G.exists_X_smul_eq_unblockedDifferential_simplyBlockedLift_sub R i c

/-- The defining equation of the connecting map: `V_i • ρ_i c = ∂⁻ (L_i c) - L_i (∂_i c)`. -/
theorem X_smul_simplyBlockedConnectingMap (c : GridChainHat R n i) :
    (MvPolynomial.X i : MvPolynomial (Fin n) R) • G.simplyBlockedConnectingMap R i c =
      G.unblockedDifferential R (simplyBlockedLift R i c) -
        simplyBlockedLift R i (G.simplyBlockedDifferential R i c) := by
  rw [simplyBlockedConnectingMap, LinearMap.comp_apply, LinearEquiv.coe_coe]
  -- Up to definitional unfolding, the goal is `ofInjective_symm_apply`: `V_i • x` is
  -- `DistribSMul.toLinearMap R _ V_i x`, and the coercion of the `codRestrict` value at `c` is
  -- `(∂⁻.restrictScalars R ∘ₗ L_i - L_i ∘ₗ ∂_i.restrictScalars R) c`, which is the right side.
  -- A `rw` with these lemmas fails, since the proof arguments of `ofInjective` and `codRestrict`
  -- in the definition are typed by the unfolded forms.
  exact LinearEquiv.ofInjective_symm_apply (f := DistribSMul.toLinearMap R (GridChainMinus R n)
    (MvPolynomial.X i : MvPolynomial (Fin n) R)) _

/-- The connecting map is semilinear along the inclusion of the surviving variables. -/
theorem simplyBlockedConnectingMap_smul (a : MvPolynomial {c : Fin n // c ≠ i} R)
    (c : GridChainHat R n i) :
    G.simplyBlockedConnectingMap R i (a • c) =
      rename Subtype.val a • G.simplyBlockedConnectingMap R i c := by
  apply X_smul_gridChainMinus_injective R i
  dsimp only
  rw [X_smul_simplyBlockedConnectingMap, smul_comm, X_smul_simplyBlockedConnectingMap,
    LinearMap.map_smul, simplyBlockedLift_smul, LinearMap.map_smul, simplyBlockedLift_smul,
    smul_sub]

/-- In characteristic two the connecting map commutes with the differentials: the sign `-1` of
the general identity `∂⁻ ∘ ρ_i = -ρ_i ∘ ∂_i` disappears. -/
theorem unblockedDifferential_simplyBlockedConnectingMap [CharP R 2] (c : GridChainHat R n i) :
    G.unblockedDifferential R (G.simplyBlockedConnectingMap R i c) =
      G.simplyBlockedConnectingMap R i (G.simplyBlockedDifferential R i c) := by
  apply X_smul_gridChainMinus_injective R i
  dsimp only
  have hd : G.unblockedDifferential R (G.unblockedDifferential R (simplyBlockedLift R i c)) = 0 :=
    LinearMap.congr_fun (G.unblockedDifferential_comp_self_eq_zero R) _
  have hd' : G.simplyBlockedDifferential R i (G.simplyBlockedDifferential R i c) = 0 :=
    LinearMap.congr_fun (G.simplyBlockedDifferential_comp_self_eq_zero R i) _
  rw [← LinearMap.map_smul, X_smul_simplyBlockedConnectingMap, X_smul_simplyBlockedConnectingMap,
    map_sub, hd, hd', map_zero, sub_zero, zero_sub,
    neg_eq_of_add_eq_zero_left (add_self_eq_zero_of_charTwo R _)]

end Connecting

/-! ### The change of blocked column on chains -/

section ColumnChange

variable (R : Type*) [CommRing R] (i j : Fin n)
  (H : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n)

/-- **Changing the blocked column.** Given a map `H` on `GC⁻`, the map
`c ↦ π_j (L_i c + H (ρ_i c))` from the specialization at `V_i = 0` to the specialization at
`V_j = 0`. It is semilinear along the inclusion of the variables `V_c`, `c ≠ i`, followed by
setting `V_j` to zero. When `∂⁻ H + H ∂⁻ = V_i + V_j` in characteristic two it is a chain map
inducing a bijection on homology (`oneVariableSpecializationColumnChangeHomologyMap_bijective`). -/
noncomputable def simplyBlockedColumnChangeMap :
    GridChainHat R n i →ₛₗ[simplyBlockedRingHomAlong R id j i] GridChainHat R n j where
  toFun c := simplyBlockedSpecialization R j
    (simplyBlockedLift R i c + H (G.simplyBlockedConnectingMap R i c))
  map_add' c d := by
    simp only [map_add]
    abel
  map_smul' a c := by
    rw [simplyBlockedConnectingMap_smul, simplyBlockedLift_smul, LinearMap.map_smul, ← smul_add,
      LinearMap.map_smulₛₗ, simplyBlockedRingHomAlong_apply, Function.id_comp]

/-- The change of blocked column applies `π_j` to `L_i c + H (ρ_i c)`. -/
theorem simplyBlockedColumnChangeMap_apply (c : GridChainHat R n i) :
    G.simplyBlockedColumnChangeMap R i j H c = simplyBlockedSpecialization R j
      (simplyBlockedLift R i c + H (G.simplyBlockedConnectingMap R i c)) :=
  (rfl)

variable [CharP R 2] {i j H}
  (hH : G.unblockedDifferential R ∘ₗ H + H ∘ₗ G.unblockedDifferential R =
    (MvPolynomial.X i + MvPolynomial.X j : MvPolynomial (Fin n) R) • LinearMap.id)

include hH in
/-- The homotopy identity `∂⁻ (H a) = (V_i + V_j) • a + H (∂⁻ a)`, in characteristic two. -/
private theorem unblockedDifferential_apply_of_homotopy (a : GridChainMinus R n) :
    G.unblockedDifferential R (H a) =
      (MvPolynomial.X i + MvPolynomial.X j : MvPolynomial (Fin n) R) • a +
        H (G.unblockedDifferential R a) := by
  have h := LinearMap.congr_fun hH a
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at h
  rw [← h, add_cancel_right_of_charTwo R]

include hH in
/-- **The change of blocked column is a chain map.** -/
theorem simplyBlockedColumnChangeMap_simplyBlockedDifferential (c : GridChainHat R n i) :
    G.simplyBlockedColumnChangeMap R i j H (G.simplyBlockedDifferential R i c) =
      G.simplyBlockedDifferential R j (G.simplyBlockedColumnChangeMap R i j H c) := by
  set r := G.simplyBlockedConnectingMap R i c
  have hL : G.unblockedDifferential R (simplyBlockedLift R i c) =
      simplyBlockedLift R i (G.simplyBlockedDifferential R i c) +
        (MvPolynomial.X i : MvPolynomial (Fin n) R) • r := by
    rw [X_smul_simplyBlockedConnectingMap, add_sub_cancel]
  -- `∂⁻ (L_i c + H r) = (L_i (∂_i c) + H (ρ_i (∂_i c))) + V_j • r` in characteristic two.
  have key : G.unblockedDifferential R (simplyBlockedLift R i c + H r) =
      (simplyBlockedLift R i (G.simplyBlockedDifferential R i c) +
        H (G.simplyBlockedConnectingMap R i (G.simplyBlockedDifferential R i c))) +
        (MvPolynomial.X j : MvPolynomial (Fin n) R) • r := by
    rw [map_add, hL, G.unblockedDifferential_apply_of_homotopy R hH,
      unblockedDifferential_simplyBlockedConnectingMap, add_smul]
    simp only [add_assoc, add_cancel_left_of_charTwo R]
    abel
  rw [simplyBlockedColumnChangeMap_apply, simplyBlockedColumnChangeMap_apply,
    ← simplyBlockedSpecialization_unblockedDifferential, key,
    map_add _ _ ((MvPolynomial.X j : MvPolynomial (Fin n) R) • r),
    simplyBlockedSpecialization_X_smul, add_zero]

include hH in
/-- The change of blocked column may be computed from any unblocked chain `Y` with
`∂⁻ Y = V_i • t`, not only from the lift: up to a boundary it sends `π_i Y` to `π_j (Y + H t)`. -/
private theorem simplyBlockedColumnChangeMap_simplyBlockedSpecialization_sub_mem_range
    {Y t : GridChainMinus R n}
    (hY : G.unblockedDifferential R Y = (MvPolynomial.X i : MvPolynomial (Fin n) R) • t) :
    G.simplyBlockedColumnChangeMap R i j H (simplyBlockedSpecialization R i Y) -
        simplyBlockedSpecialization R j (Y + H t) ∈
      LinearMap.range (G.simplyBlockedDifferential R j) := by
  -- The lift of `π_i Y` is `Y + V_i • u`, and then `ρ_i (π_i Y) = t + ∂⁻ u`.
  obtain ⟨u, hu⟩ := (exact_X_smul_simplyBlockedSpecialization R i
    (simplyBlockedLift R i (simplyBlockedSpecialization R i Y) - Y)).mp (by
      rw [map_sub, simplyBlockedSpecialization_simplyBlockedLift, sub_self])
  dsimp only at hu
  have hLY : simplyBlockedLift R i (simplyBlockedSpecialization R i Y) =
      Y + (MvPolynomial.X i : MvPolynomial (Fin n) R) • u := by
    rw [hu, add_sub_cancel]
  have hρ : G.simplyBlockedConnectingMap R i (simplyBlockedSpecialization R i Y) =
      t + G.unblockedDifferential R u := by
    apply X_smul_gridChainMinus_injective R i
    dsimp only
    rw [X_smul_simplyBlockedConnectingMap, hLY, ← simplyBlockedSpecialization_unblockedDifferential,
      hY, simplyBlockedSpecialization_X_smul, map_zero, sub_zero, map_add, hY, LinearMap.map_smul,
      smul_add]
  have hHu := G.unblockedDifferential_apply_of_homotopy R hH u
  refine ⟨simplyBlockedSpecialization R j (H u), ?_⟩
  -- Both sides are `π_j (V_i • u + H (∂⁻ u))`, since `π_j` kills `V_j • u`.
  rw [← simplyBlockedSpecialization_unblockedDifferential, simplyBlockedColumnChangeMap_apply, hLY,
    hρ, ← map_sub, hHu, add_smul, add_right_comm, map_add _ _ ((MvPolynomial.X j) • u),
    simplyBlockedSpecialization_X_smul, add_zero, map_add H]
  congr 1
  abel

include hH in
/-- A cycle whose image under the change of blocked column is a boundary is itself a boundary.
With `r = ρ_i x`, lifting `π_j (L_i x + H r - ∂⁻ (L_j z)) = 0` gives `W` with `∂⁻ W = r` and
`L_i x = ∂⁻ (L_j z + H W) + V_i • W`. -/
theorem mem_range_of_simplyBlockedColumnChangeMap_mem_range {x : GridChainHat R n i}
    (hx : G.simplyBlockedDifferential R i x = 0)
    (hΦx : G.simplyBlockedColumnChangeMap R i j H x ∈
      LinearMap.range (G.simplyBlockedDifferential R j)) :
    x ∈ LinearMap.range (G.simplyBlockedDifferential R i) := by
  obtain ⟨z, hz⟩ := hΦx
  set r := G.simplyBlockedConnectingMap R i x
  have hLx : G.unblockedDifferential R (simplyBlockedLift R i x) =
      (MvPolynomial.X i : MvPolynomial (Fin n) R) • r := by
    rw [X_smul_simplyBlockedConnectingMap, hx, map_zero, sub_zero]
  have hr : G.unblockedDifferential R r = 0 := by
    rw [unblockedDifferential_simplyBlockedConnectingMap, hx, map_zero]
  obtain ⟨W, hW⟩ := (exact_X_smul_simplyBlockedSpecialization R j
    (simplyBlockedLift R i x + H r - G.unblockedDifferential R (simplyBlockedLift R j z))).mp (by
      rw [map_sub, ← simplyBlockedColumnChangeMap_apply, ← hz,
        simplyBlockedSpecialization_unblockedDifferential,
        simplyBlockedSpecialization_simplyBlockedLift, sub_self])
  dsimp only at hW
  have hdd : G.unblockedDifferential R
      (G.unblockedDifferential R (simplyBlockedLift R j z)) = 0 :=
    LinearMap.congr_fun (G.unblockedDifferential_comp_self_eq_zero R) _
  have hrW : r = G.unblockedDifferential R W := by
    apply X_smul_gridChainMinus_injective R j
    dsimp only
    have h := congrArg (G.unblockedDifferential R) hW
    rw [LinearMap.map_smul, map_sub, map_add, hLx, G.unblockedDifferential_apply_of_homotopy R hH,
      hr, map_zero, add_zero, hdd, sub_zero, add_smul, add_cancel_left_of_charTwo R] at h
    exact h.symm
  have hxW : simplyBlockedLift R i x = (MvPolynomial.X j : MvPolynomial (Fin n) R) • W - H r +
      G.unblockedDifferential R (simplyBlockedLift R j z) := by
    rw [hW]
    abel
  refine ⟨simplyBlockedSpecialization R i (simplyBlockedLift R j z + H W), ?_⟩
  rw [← simplyBlockedSpecialization_unblockedDifferential, ← sub_eq_zero,
    ← simplyBlockedSpecialization_simplyBlockedLift R i x, ← map_sub]
  refine (exact_X_smul_simplyBlockedSpecialization R i _).mpr ⟨W, ?_⟩
  dsimp only
  rw [map_add, G.unblockedDifferential_apply_of_homotopy R hH, ← hrW, hxW, add_smul]
  exact (add_cancel_right_of_charTwo R _ (H r)).symm.trans (by abel)

include hH in
/-- Every cycle `y` of the specialization at `V_j = 0` is the image of a cycle up to a boundary:
with `t = ρ_j y`, the chain `Y = L_j y + H t` satisfies `∂⁻ Y = V_i • t`, and `π_i Y` is sent to
`π_j (Y + H t) = y`. -/
theorem exists_sub_simplyBlockedColumnChangeMap_mem_range {y : GridChainHat R n j}
    (hy : G.simplyBlockedDifferential R j y = 0) :
    ∃ x, G.simplyBlockedDifferential R i x = 0 ∧
      y - G.simplyBlockedColumnChangeMap R i j H x ∈
        LinearMap.range (G.simplyBlockedDifferential R j) := by
  set t := G.simplyBlockedConnectingMap R j y
  have hLy : G.unblockedDifferential R (simplyBlockedLift R j y) =
      (MvPolynomial.X j : MvPolynomial (Fin n) R) • t := by
    rw [X_smul_simplyBlockedConnectingMap, hy, map_zero, sub_zero]
  have ht : G.unblockedDifferential R t = 0 := by
    rw [unblockedDifferential_simplyBlockedConnectingMap, hy, map_zero]
  have hY : G.unblockedDifferential R (simplyBlockedLift R j y + H t) =
      (MvPolynomial.X i : MvPolynomial (Fin n) R) • t := by
    rw [map_add, hLy, G.unblockedDifferential_apply_of_homotopy R hH, ht, map_zero, add_zero,
      add_smul, add_comm, add_cancel_right_of_charTwo R]
  refine ⟨simplyBlockedSpecialization R i (simplyBlockedLift R j y + H t), ?_, ?_⟩
  · rw [← simplyBlockedSpecialization_unblockedDifferential, hY,
      simplyBlockedSpecialization_X_smul]
  · have h := G.simplyBlockedColumnChangeMap_simplyBlockedSpecialization_sub_mem_range R hH hY
    rw [add_cancel_right_of_charTwo R, simplyBlockedSpecialization_simplyBlockedLift] at h
    rw [← neg_sub]
    exact neg_mem h

end ColumnChange

/-! ### Homology -/

section Homology

variable (R : Type*) [CommRing R] [CharP R 2] {i j : Fin n}
  {H : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n}
  (hH : G.unblockedDifferential R ∘ₗ H + H ∘ₗ G.unblockedDifferential R =
    (MvPolynomial.X i + MvPolynomial.X j : MvPolynomial (Fin n) R) • LinearMap.id)

include hH in
/-- The map on cycles induced by changing the blocked column from `i` to `j`. -/
noncomputable def oneVariableSpecializationColumnChangeCyclesMap :
    LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom →ₛₗ[simplyBlockedRingHomAlong R id j i]
      LinearMap.ker ((G.simplyBlockedComplex R j).d () ()).hom :=
  oneVariableSpecializationCyclesMapOfIntertwining R i j _
    (G.simplyBlockedColumnChangeMap R i j H)
    (G.simplyBlockedColumnChangeMap_simplyBlockedDifferential R hH)

/-- Under the explicit chain identifications, the map of cycles is the change of blocked
column. -/
@[simp]
theorem simplyBlockedChainEquiv_oneVariableSpecializationColumnChangeCyclesMap
    (z : LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom) :
    G.simplyBlockedChainEquiv R j (G.oneVariableSpecializationColumnChangeCyclesMap R hH z) =
      G.simplyBlockedColumnChangeMap R i j H (G.simplyBlockedChainEquiv R i z) :=
  simplyBlockedChainEquiv_oneVariableSpecializationCyclesMapOfIntertwining R i j _ _ _ z

include hH in
/-- The map on the homology of the one-variable specializations induced by changing the blocked
column from `i` to `j`. -/
noncomputable def oneVariableSpecializationColumnChangeHomologyMap :
    (G.simplyBlockedComplex R i).homology () →ₛₗ[simplyBlockedRingHomAlong R id j i]
      (G.simplyBlockedComplex R j).homology () :=
  oneVariableSpecializationHomologyMapOfIntertwining R i j _
    (G.simplyBlockedColumnChangeMap R i j H)
    (G.simplyBlockedColumnChangeMap_simplyBlockedDifferential R hH)

/-- The change of blocked column sends a cycle class to the class of the image cycle. -/
@[simp]
theorem oneVariableSpecializationColumnChangeHomologyMap_oneVariableSpecializationHomologyClass
    (z : LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom) :
    G.oneVariableSpecializationColumnChangeHomologyMap R hH
        (G.oneVariableSpecializationHomologyClass R i z) =
      G.oneVariableSpecializationHomologyClass R j
        (G.oneVariableSpecializationColumnChangeCyclesMap R hH z) :=
  oneVariableSpecializationHomologyMapOfIntertwining_oneVariableSpecializationHomologyClass
    R i j _ _ _ z

/-- **The change of blocked column is bijective on homology.** If `∂⁻ H + H ∂⁻ = V_i + V_j` on
`GC⁻` in characteristic two, the map `c ↦ π_j (L_i c + H (ρ_i c))` induces a bijection from the
homology of the specialization at `V_i = 0` to that of the specialization at `V_j = 0`. -/
theorem oneVariableSpecializationColumnChangeHomologyMap_bijective :
    Function.Bijective (G.oneVariableSpecializationColumnChangeHomologyMap R hH) := by
  exact oneVariableSpecializationHomologyMapOfIntertwining_bijective R i j _ _ _
    (G.mem_range_of_simplyBlockedColumnChangeMap_mem_range R hH)
    (G.exists_sub_simplyBlockedColumnChangeMap_mem_range R hH)

end Homology

end TauCeti.GridDiagram

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ}

/-! ### Bidegrees -/

/-- With a homotopy `H` of bidegree `(-1, -1)`, the change of blocked column preserves the
bidegree of specialized chains. -/
theorem simplyBlockedColumnChangeMap_mem_bigradedChainHatPiece (G : OddComponentGridDiagram n)
    (R : Type*) [CommRing R] {i j : Fin n}
    {H : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n}
    (hHdeg : ∀ {g : ℤ × ℤ} {a : GridChainMinus R n}, a ∈ G.bigradedChainMinusPiece R g →
      H a ∈ G.bigradedChainMinusPiece R (g - (1, 1)))
    {g : ℤ × ℤ} {c : GridChainHat R n i} (hc : c ∈ G.bigradedChainHatPiece R i g) :
    G.1.simplyBlockedColumnChangeMap R i j H c ∈ G.bigradedChainHatPiece R j g := by
  have hL := G.simplyBlockedLift_mem_bigradedChainMinusPiece_iff.mpr hc
  -- `V_i • ρ_i c` has bidegree `g - (1, 0)`, so `ρ_i c` has bidegree `g + (1, 1)`.
  have hρ : G.1.simplyBlockedConnectingMap R i c ∈ G.bigradedChainMinusPiece R (g + (1, 1)) := by
    have hg : g + (1, 1) - (2, 1) = g - (1, 0) := by
      ext <;> simp only [Prod.fst_sub, Prod.fst_add, Prod.snd_sub, Prod.snd_add] <;> omega
    rw [← G.X_smul_mem_bigradedChainMinusPiece_iff i, GridDiagram.X_smul_simplyBlockedConnectingMap,
      hg]
    exact sub_mem (G.unblockedDifferential_mem_bigradedChainMinusPiece hL)
      (G.simplyBlockedLift_mem_bigradedChainMinusPiece_iff.mpr
        (G.simplyBlockedDifferential_mem_bigradedChainHatPiece hc))
  rw [GridDiagram.simplyBlockedColumnChangeMap_apply]
  refine G.simplyBlockedSpecialization_mem_bigradedChainHatPiece j (add_mem hL ?_)
  simpa only [add_sub_cancel_right] using hHdeg hρ

end TauCeti.OddComponentGridDiagram

namespace TauCeti.GridDiagram

variable {n : ℕ} {G : GridDiagram n}

/-! ### Knot grids -/

namespace IsKnot

variable (hG : G.IsKnot) (R : Type*) [CommRing R] [CharP R 2] (i j : Fin n)

local notation "Base" i => ModuleCat.restrictScalars
  (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)

/-- **Simply blocked knot grid homology does not depend on the blocked column.** The change of
blocked column, with the chosen homotopy `hG.XSmulHomotopy R i j` between `V_i` and `V_j`, as a
coefficient-linear equivalence between the simply blocked homologies blocking the columns `i` and
`j`. -/
noncomputable def simplyBlockedHomologyColumnChangeEquiv :
    (Base i).obj (hG.simplyBlockedHomology R i) ≃ₗ[R] (Base j).obj (hG.simplyBlockedHomology R j) :=
  ModuleCat.restrictScalarsLinearEquivOfBijective _ _
    (G.oneVariableSpecializationColumnChangeHomologyMap R
      (hG.unblockedDifferential_comp_XSmulHomotopy_add_XSmulHomotopy_comp R i j))
    (fun r => simplyBlockedRingHomAlong_C R id j i r)
    (G.oneVariableSpecializationColumnChangeHomologyMap_bijective R
      (hG.unblockedDifferential_comp_XSmulHomotopy_add_XSmulHomotopy_comp R i j))

/-- The equivalence sends the class of a cycle `z` to the class of its image under the change of
blocked column. -/
theorem simplyBlockedHomologyColumnChangeEquiv_oneVariableSpecializationHomologyClass
    (z : hG.simplyBlockedCycles R i) :
    hG.simplyBlockedHomologyColumnChangeEquiv R i j
        (G.oneVariableSpecializationHomologyClass R i z) =
      G.oneVariableSpecializationHomologyClass R j
        (G.oneVariableSpecializationColumnChangeCyclesMap R
          (hG.unblockedDifferential_comp_XSmulHomotopy_add_XSmulHomotopy_comp R i j) z) :=
  (ModuleCat.restrictScalarsLinearEquivOfBijective_apply _ _ _ _ _ _).trans
    (G.oneVariableSpecializationColumnChangeHomologyMap_oneVariableSpecializationHomologyClass
      R _ z)

/-- The change of blocked column on knot grid homology has bidegree zero. -/
theorem isHomogeneous_simplyBlockedHomologyColumnChangeEquiv :
    LinearMap.IsHomogeneous (hG.simplyBlockedHomologyColumnChangeEquiv R i j).toLinearMap
      (hG.toOddComponentGridDiagram.bigradedHatHomologyGrading R i).piece
      (hG.toOddComponentGridDiagram.bigradedHatHomologyGrading R j).piece 0 :=
  hG.toOddComponentGridDiagram.isHomogeneous_bigradedHatHomologyGrading_of_cycles R i
    hG.toOddComponentGridDiagram j _ _
    (hG.simplyBlockedHomologyColumnChangeEquiv_oneVariableSpecializationHomologyClass R i j)
    fun g z hz => by
      rw [add_zero, simplyBlockedChainEquiv_oneVariableSpecializationColumnChangeCyclesMap]
      exact hG.toOddComponentGridDiagram.simplyBlockedColumnChangeMap_mem_bigradedChainHatPiece R
        (hG.XSmulHomotopy_mem_bigradedChainMinusPiece i j) hz

/-- The change of blocked column preserves and reflects both homology degrees. -/
@[simp]
theorem simplyBlockedHomologyColumnChangeEquiv_mem_bigradedHatHomologyPiece_iff
    {g : ℤ × ℤ} {y : (Base i).obj (hG.simplyBlockedHomology R i)} :
    hG.simplyBlockedHomologyColumnChangeEquiv R i j y ∈
        hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R j g ↔
      y ∈ hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g :=
  hG.toOddComponentGridDiagram.linearEquiv_mem_bigradedHatHomologyPiece_iff R i
    hG.toOddComponentGridDiagram j _ (hG.isHomogeneous_simplyBlockedHomologyColumnChangeEquiv R i j)
    g y

/-- The change of blocked column restricted to the homology pieces of bidegree `g`. -/
noncomputable def simplyBlockedHomologyColumnChangePieceEquiv (g : ℤ × ℤ) :
    hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g ≃ₗ[R]
      hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R j g :=
  hG.toOddComponentGridDiagram.bigradedHatHomologyPieceEquiv R i hG.toOddComponentGridDiagram j
    _ (hG.isHomogeneous_simplyBlockedHomologyColumnChangeEquiv R i j) g

section Field

variable (K : Type*) [Field K] [CharP K 2]

/-- **Independence of the blocked column.** Over a field of characteristic two, the bigraded
Poincaré series of the simply blocked homology `G-hat` of a knot grid is the same for every choice
of the blocked column. -/
theorem bigradedSimplyBlockedHomologyPoincareSeries_columnChange :
    hG.bigradedSimplyBlockedHomologyPoincareSeries K i =
      hG.bigradedSimplyBlockedHomologyPoincareSeries K j := by
  ext g
  simp only [coeff_bigradedSimplyBlockedHomologyPoincareSeries]
  exact (hG.simplyBlockedHomologyColumnChangePieceEquiv K i j g).finrank_eq

/-- Over a field of characteristic two, the Alexander-graded Euler characteristic of the simply
blocked homology `G-hat` of a knot grid is the same for every choice of the blocked column. -/
theorem gradedSimplyBlockedHomologyEulerChar_columnChange :
    hG.gradedSimplyBlockedHomologyEulerChar K i = hG.gradedSimplyBlockedHomologyEulerChar K j := by
  rw [gradedSimplyBlockedHomologyEulerChar_eq_euler, gradedSimplyBlockedHomologyEulerChar_eq_euler,
    hG.bigradedSimplyBlockedHomologyPoincareSeries_columnChange i j K]

end Field

end IsKnot

end TauCeti.GridDiagram
