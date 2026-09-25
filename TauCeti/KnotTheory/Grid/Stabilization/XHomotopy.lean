/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Stabilization.Cone
public import TauCeti.KnotTheory.Grid.XHomotopy.Complex

/-!
# The `X`-marking homotopy of a stabilized grid

Let `G` be a grid diagram of size `n`, let `s` be a column, and let
`G' = G.stabilizeX s.castSucc (G.X s).castSucc s` be the stabilization splitting the `X`-marking
of column `s`. Its new `2 × 2` block is centered at `c = (s.succ, (G.X s).succ)`: the two
`X`-markings of the block lie northwest and southeast of `c` and the new `O`-marking southwest of
it. Write `X₂` for the southeast `X`-marking, the one in column `s.succ`, and
`S = R[V₀, …, V_n]` for the coefficient ring of `GC⁻(G')`. The row of `X₂` also carries the new
`O`-marking, in column `s.castSucc`.

By `TauCeti.KnotTheory.Grid.Stabilization.Cone`, `GC⁻(G')` is the mapping cone of the connecting
map `∂_I^N` from the center complex `I` (states containing `c`) to the off-center complex `N`.
This file studies the component `H_I^N : N → I` of the `X`-marking homotopy `H_{X₂}` of `G'`,
which counts the empty rectangles from an off-center state to a center state whose only covered
`X`-marking is `X₂`.

The `X`-marking homotopy satisfies `∂⁻ ∘ H_{X₂} + H_{X₂} ∘ ∂⁻ = V_{s.succ} + V_{s.castSucc}` on
`GC⁻(G')` in characteristic two. The component of `H_{X₂}` between center states vanishes
(`XHomotopyCoefficient_stabilizeX_succ_insertPoint`): a rectangle between states containing `c`
that covers the square of `X₂` also covers the square of the other `X`-marking of the block.
Together with the vanishing of the `N`-to-`I` block of `∂⁻`, reading off the two blocks of the
homotopy identity with target `I` gives:

* `H_I^N ∘ ∂_I^N = V_{s.succ} + V_{s.castSucc}` on `I`
  (`stabilizeXOffCenterToCenter_comp_connecting`);
* `H_I^N` intertwines the off-center and the center differentials
  (`stabilizeXOffCenterToCenter_comp_offCenterDifferential`), so it is a chain map
  `N ⟶ I` (`stabilizeXOffCenterToCenterHom`).

In characteristic two, `V_{s.succ} + V_{s.castSucc}` is the difference of the variable of the new
`O`-marking and the variable of the old `O`-marking of column `s`. By the first identity, the pair
`(𝟙, H_I^N)` maps the mapping cone of `∂_I^N`, that is `GC⁻(G')`, to the mapping cone of
multiplication by this difference on `I`; the latter is the cone that
`HomologicalComplex.polynomialExtensionMulXSubCHomotopyEquiv` compares with `GC⁻(G)`, once `I` is
identified with the polynomial extension of `GC⁻(G)` in the new variable. The map of cones is a
quasi-isomorphism when `H_I^N` is; both steps are carried out in
`TauCeti.KnotTheory.Grid.Stabilization.Map`.

## Main definitions

* `TauCeti.GridDiagram.stabilizeXOffCenterToCenter`: the component `H_I^N` of the `X`-marking
  homotopy of `X₂`, from off-center states to center states.
* `TauCeti.GridDiagram.stabilizeXOffCenterToCenterHom`: `H_I^N` as a chain map from the
  off-center complex to the center complex.

## Main results

* `TauCeti.GridDiagram.XHomotopyCoefficient_stabilizeX_succ_insertPoint`: the homotopy `H_{X₂}`
  has no matrix coefficient between center states.
* `TauCeti.GridDiagram.stabilizeXOffCenterToCenter_comp_connecting`: `H_I^N ∘ ∂_I^N` is
  multiplication by `V_{s.succ} + V_{s.castSucc}`.
* `TauCeti.GridDiagram.stabilizeXOffCenterToCenter_comp_offCenterDifferential`: `H_I^N` is a
  chain map.
* `TauCeti.GridDiagram.stabilizeXConnectingHom_comp_offCenterToCenterHom`: the composite of the
  connecting chain map and `H_I^N` is multiplication by `V_{s.succ} + V_{s.castSucc}`.

## References

In Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.2, the fully blocked
version of `H_I^N`, counting the rectangles from `N` to `I` whose only marking is `X₂`, compares the
two halves of the mapping cone in the proof of stabilization invariance. The mapping cone of
`V₁ - V₂` is the one of Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer
homology*, Section 3.2.
-/

public section

open CategoryTheory MvPolynomial

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

section Blocks

variable (R : Type*) [CommSemiring R]

local notation "S" => MvPolynomial (Fin (n + 1)) R

/-- **The center block of the `X₂`-homotopy vanishes.** The `X`-marking homotopy of the southeast
`X`-marking of the new block has no matrix coefficient between two grid states containing the
center `c = (s.succ, (G.X s).succ)`: such a rectangle is transported from a rectangle of `G`, and
if it covers the square of that `X`-marking it also covers the square of the northwest one. -/
@[simp]
theorem XHomotopyCoefficient_stabilizeX_succ_insertPoint (x y : GridState n) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).XHomotopyCoefficient R s.succ
        (x.insertPoint s.succ (G.X s).succ) (y.insertPoint s.succ (G.X s).succ) = 0 := by
  rw [XHomotopyCoefficient_def]
  refine Finset.sum_eq_zero fun r' hr' => absurd hr' fun hr' => ?_
  obtain ⟨r, rfl⟩ := GridRectangleBetween.exists_insertPoint_eq r'
  have hX := ((G.stabilizeX s.castSucc (G.X s).castSucc s).mem_XHomotopyRectangles s.succ _).mp
    hr' |>.2
  -- The two `X`-markings of the block collapse onto the same square of `G`.
  have hSE : (s.succ, (G.X s).castSucc) ∈
      (r.insertPoint s.succ (G.X s).succ).toGridRectangle.coveredSquares := by
    have := Finset.mem_of_mem_inter_left (hX ▸ Finset.mem_singleton_self _)
    simpa using this
  have hNW : (s.castSucc, (G.X s).succ) ∈
      (r.insertPoint s.succ (G.X s).succ).toGridRectangle.coveredSquares := by
    rw [GridRectangleBetween.mem_coveredSquares_insertPoint_succ_succ] at hSE ⊢
    simpa using hSE
  have hmem : (s.castSucc, (G.X s).succ) ∈
      (r.insertPoint s.succ (G.X s).succ).toGridRectangle.coveredSquares ∩
        (G.stabilizeX s.castSucc (G.X s).castSucc s).XSet :=
    Finset.mem_inter.mpr ⟨hNW, (mem_XSet _ _).mpr (by simp)⟩
  rw [hX, Finset.mem_singleton, Prod.mk.injEq] at hmem
  exact Fin.castSucc_lt_succ.ne hmem.1

/-- The component of the `X₂`-homotopy from center states to center states vanishes. -/
@[simp]
theorem stabilizeXCenterProjection_XHomotopy_centerInclusion (f : GridState n →₀ S) :
    G.stabilizeXCenterProjection s R
      ((G.stabilizeX s.castSucc (G.X s).castSucc s).XHomotopy R s.succ
        (G.stabilizeXCenterInclusion s R f)) = 0 := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg, add_zero]
  | single x a =>
    refine Finsupp.ext fun y => ?_
    rw [stabilizeXCenterInclusion_single, ← mul_one a, ← smul_eq_mul, ← Finsupp.smul_single,
      map_smul]
    simp

/-- The component `H_I^N` of the `X`-marking homotopy of the southeast `X`-marking `X₂` of the new
block, from off-center states to center states. It counts the empty rectangles from a state not
containing the center of the block to one containing it whose only covered `X`-marking is `X₂`. -/
noncomputable def stabilizeXOffCenterToCenter :
    (G.StabilizeXOffCenterState s →₀ S) →ₗ[S] (GridState n →₀ S) :=
  G.stabilizeXCenterProjection s R ∘ₗ
    (G.stabilizeX s.castSucc (G.X s).castSucc s).XHomotopy R s.succ ∘ₗ
      G.stabilizeXOffCenterInclusion s R

/-- The matrix coefficients of `H_I^N` are those of the `X₂`-homotopy of the stabilization, from
an off-center state to a center state. -/
@[simp]
theorem stabilizeXOffCenterToCenter_single_apply (y : G.StabilizeXOffCenterState s)
    (x : GridState n) :
    G.stabilizeXOffCenterToCenter s R (Finsupp.single y 1) x =
      (G.stabilizeX s.castSucc (G.X s).castSucc s).XHomotopyCoefficient R s.succ y
        (x.insertPoint s.succ (G.X s).succ) := by
  simp [stabilizeXOffCenterToCenter]

/-- The `X₂`-homotopy of an off-center chain has center part `H_I^N`. -/
private theorem XHomotopy_offCenterInclusion (f : G.StabilizeXOffCenterState s →₀ S) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).XHomotopy R s.succ
        (G.stabilizeXOffCenterInclusion s R f) =
      G.stabilizeXCenterInclusion s R (G.stabilizeXOffCenterToCenter s R f) +
        G.stabilizeXOffCenterInclusion s R
          (G.stabilizeXOffCenterProjection s R
            ((G.stabilizeX s.castSucc (G.X s).castSucc s).XHomotopy R s.succ
              (G.stabilizeXOffCenterInclusion s R f))) :=
  (G.stabilizeXCenterInclusion_projection_add_offCenter s R _).symm

/-- The `X₂`-homotopy of a center chain is an off-center chain. -/
private theorem XHomotopy_centerInclusion (f : GridState n →₀ S) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).XHomotopy R s.succ
        (G.stabilizeXCenterInclusion s R f) =
      G.stabilizeXOffCenterInclusion s R
        (G.stabilizeXOffCenterProjection s R
          ((G.stabilizeX s.castSucc (G.X s).castSucc s).XHomotopy R s.succ
            (G.stabilizeXCenterInclusion s R f))) := by
  conv_lhs => rw [← G.stabilizeXCenterInclusion_projection_add_offCenter s R
    ((G.stabilizeX s.castSucc (G.X s).castSucc s).XHomotopy R s.succ
      (G.stabilizeXCenterInclusion s R f))]
  rw [stabilizeXCenterProjection_XHomotopy_centerInclusion, map_zero, zero_add]

variable [CharP R 2]

/-- The homotopy identity `∂⁻ ∘ H_{X₂} + H_{X₂} ∘ ∂⁻ = V_{s.succ} + V_{s.castSucc}` on the
unblocked complex of the stabilization, applied to a chain. -/
private theorem unblockedDifferential_XHomotopy_add_XHomotopy_unblockedDifferential
    (v : GridChainMinus R (n + 1)) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R
        ((G.stabilizeX s.castSucc (G.X s).castSucc s).XHomotopy R s.succ v) +
      (G.stabilizeX s.castSucc (G.X s).castSucc s).XHomotopy R s.succ
        ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R v) =
      (MvPolynomial.X s.succ + MvPolynomial.X s.castSucc : S) • v := by
  -- The `O`-marking in the row of the southeast `X`-marking is the new one, in column
  -- `s.castSucc`.
  have hj : (G.stabilizeX s.castSucc (G.X s).castSucc s).O.columnOfRow
      ((G.stabilizeX s.castSucc (G.X s).castSucc s).X s.succ) = s.castSucc := by
    rw [stabilizeX_X, GridState.splitPoint_castSucc_apply_succ, stabilizeX_O]
    simpa using (G.O.insertPoint s.castSucc (G.X s).castSucc).columnOfRow_apply s.castSucc
  have h := LinearMap.congr_fun (unblockedDifferential_comp_XHomotopy_add_XHomotopy_comp
    (G.stabilizeX s.castSucc (G.X s).castSucc s) R s.succ) v
  rwa [hj] at h

/-- **`H_I^N` inverts the connecting map up to `V_{s.succ} + V_{s.castSucc}`.** Following the
connecting map from center states to off-center states by `H_I^N` is multiplication by
`V_{s.succ} + V_{s.castSucc}`, the sum of the variables of the old `O`-marking of column `s` and
of the new `O`-marking. -/
theorem stabilizeXOffCenterToCenter_comp_connecting :
    G.stabilizeXOffCenterToCenter s R ∘ₗ G.stabilizeXConnecting s R =
      (MvPolynomial.X s.succ + MvPolynomial.X s.castSucc : S) • LinearMap.id := by
  refine LinearMap.ext fun f => ?_
  have h := congrArg (G.stabilizeXCenterProjection s R)
    (G.unblockedDifferential_XHomotopy_add_XHomotopy_unblockedDifferential s R
      (G.stabilizeXCenterInclusion s R f))
  have hD : (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R
      (G.stabilizeXCenterInclusion s R f) =
        G.stabilizeXCenterInclusion s R (G.stabilizeXCenterDifferential s R f) +
          G.stabilizeXOffCenterInclusion s R (G.stabilizeXConnecting s R f) :=
    LinearMap.congr_fun (G.unblockedDifferential_comp_stabilizeXCenterInclusion s R) f
  -- The first term of the homotopy identity has no center part, and the second has center part
  -- `H_I^N (∂_I^N f)`.
  rw [G.XHomotopy_centerInclusion s R, map_add,
    stabilizeXCenterProjection_unblockedDifferential_offCenterInclusion, zero_add, hD, map_add,
    map_add, stabilizeXCenterProjection_XHomotopy_centerInclusion, zero_add, map_smul,
    stabilizeXCenterProjection_inclusion] at h
  exact h

end Blocks

variable (R : Type*) [CommRing R] [CharP R 2]

local notation "S" => MvPolynomial (Fin (n + 1)) R

/-- **`H_I^N` is a chain map.** It intertwines the off-center differential with the center
differential. -/
theorem stabilizeXOffCenterToCenter_comp_offCenterDifferential :
    G.stabilizeXOffCenterToCenter s R ∘ₗ G.stabilizeXOffCenterDifferential s R =
      G.stabilizeXCenterDifferential s R ∘ₗ G.stabilizeXOffCenterToCenter s R := by
  refine LinearMap.ext fun f => ?_
  have h := congrArg (G.stabilizeXCenterProjection s R)
    (G.unblockedDifferential_XHomotopy_add_XHomotopy_unblockedDifferential s R
      (G.stabilizeXOffCenterInclusion s R f))
  have hD : (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R
      (G.stabilizeXOffCenterInclusion s R f) =
        G.stabilizeXOffCenterInclusion s R (G.stabilizeXOffCenterDifferential s R f) :=
    LinearMap.congr_fun (G.unblockedDifferential_comp_stabilizeXOffCenterInclusion s R) f
  -- Take center parts: the right-hand side has none.
  rw [G.XHomotopy_offCenterInclusion s R, map_add, map_add, map_add,
    stabilizeXCenterProjection_unblockedDifferential_offCenterInclusion, add_zero, hD, map_smul,
    stabilizeXCenterProjection_offCenterInclusion, smul_zero] at h
  -- The two center parts are `∂_I^I (H_I^N f)` and `H_I^N (∂_N^N f)`; in characteristic two they
  -- sum to zero exactly when they are equal.
  have h' : G.stabilizeXCenterDifferential s R (G.stabilizeXOffCenterToCenter s R f) +
      G.stabilizeXOffCenterToCenter s R (G.stabilizeXOffCenterDifferential s R f) = 0 := by
    have hDI := LinearMap.congr_fun (G.unblockedDifferential_comp_stabilizeXCenterInclusion s R)
      (G.stabilizeXOffCenterToCenter s R f)
    rw [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.comp_apply] at hDI
    rwa [hDI, map_add, stabilizeXCenterProjection_inclusion,
      stabilizeXCenterProjection_offCenterInclusion, add_zero] at h
  rw [LinearMap.comp_apply, LinearMap.comp_apply, eq_neg_of_add_eq_zero_right h',
    ← neg_one_smul S, CharTwo.neg_eq, one_smul]

/-! ### The chain map -/

/-- The component `H_I^N` of the `X₂`-homotopy, as a chain map from the off-center complex to the
center complex. -/
noncomputable def stabilizeXOffCenterToCenterHom :
    G.stabilizeXOffCenterComplex s R ⟶ G.stabilizeXCenterComplex s R where
  f i := eqToHom (G.stabilizeXOffCenterComplex_X s R i) ≫
    ModuleCat.ofHom (G.stabilizeXOffCenterToCenter s R) ≫
      eqToHom (G.stabilizeXCenterComplex_X s R i).symm
  comm' := by
    rintro ⟨⟩ ⟨⟩ -
    simp only [stabilizeXCenterComplex_d, stabilizeXOffCenterComplex_d, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (ModuleCat.ofHom _), ← Category.assoc (ModuleCat.ofHom _),
      ← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp,
      G.stabilizeXOffCenterToCenter_comp_offCenterDifferential s R]

/-- The component of the chain map `H_I^N` is `stabilizeXOffCenterToCenter`. -/
@[simp]
theorem stabilizeXOffCenterToCenterHom_f (i : Unit) :
    (G.stabilizeXOffCenterToCenterHom s R).f i =
      eqToHom (G.stabilizeXOffCenterComplex_X s R i) ≫
        ModuleCat.ofHom (G.stabilizeXOffCenterToCenter s R) ≫
          eqToHom (G.stabilizeXCenterComplex_X s R i).symm :=
  (rfl)

/-- **The connecting chain map followed by `H_I^N` is multiplication by
`V_{s.succ} + V_{s.castSucc}`** on the center complex. -/
theorem stabilizeXConnectingHom_comp_offCenterToCenterHom :
    G.stabilizeXConnectingHom s R ≫ G.stabilizeXOffCenterToCenterHom s R =
      (MvPolynomial.X s.succ + MvPolynomial.X s.castSucc : S) •
        𝟙 (G.stabilizeXCenterComplex s R) := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.smul_f_apply, HomologicalComplex.id_f,
    stabilizeXConnectingHom_f, stabilizeXOffCenterToCenterHom_f]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc (ModuleCat.ofHom _), ← ModuleCat.ofHom_comp,
    G.stabilizeXOffCenterToCenter_comp_connecting s R]
  cases i
  ext : 1
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_smul,
    LinearMap.comp_id, LinearMap.smul_comp, ← ModuleCat.hom_comp, eqToHom_trans, eqToHom_refl]
  simp

end GridDiagram

end TauCeti
