/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.MvPolynomial.Basic
public import TauCeti.Algebra.Homology.HomotopyCofiber
public import TauCeti.KnotTheory.Grid.Chain.Complex
public import TauCeti.KnotTheory.Grid.Stabilization.Unblocked

/-!
# The unblocked complex of a stabilized grid as a mapping cone

Let `G` be a grid diagram of size `n`, let `s` be a column, and let
`G' = G.stabilizeX s.castSucc (G.X s).castSucc s` be the stabilization splitting the `X`-marking
of column `s`, whose new `2 × 2` block is centered at the grid point `c = (s.succ, (G.X s).succ)`
(see `TauCeti.KnotTheory.Grid.Stabilization.Unblocked`). Write `S = R[V₀, …, V_n]` for the
coefficient ring of `GC⁻(G')`.

The grid states of `G'` split into the *center states*, those containing `c`, and the
*off-center states* (the sets `I` and `N` of Ozsváth--Stipsicz--Szabó). The center states are the
states `x.insertPoint s.succ (G.X s).succ` for `x` a grid state of `G`, so as an `S`-module

`GC⁻(G') = (GridState n →₀ S) ⊕ (off-center states →₀ S)`.

The unblocked differential has no component from off-center states to center states
(`unblockedCoefficient_stabilizeX_eq_zero`), so the off-center states span a subcomplex, and in
characteristic two `GC⁻(G')` is the mapping cone of the component of `∂⁻` from the center block to
the off-center block. This file packages that statement with Mathlib's `homotopyCofiber`.

* The *center complex* has the grid states of `G` as generators and, by
  `unblockedCoefficient_stabilizeX_insertPoint`, the differential of `GC⁻(G)` with its variables
  renamed into `S` (`stabilizeXCenterDifferential_single_apply`). The variable of the new
  `O`-marking never occurs, so this is `GC⁻(G)` with one free variable adjoined.
* The *off-center complex* is the subcomplex spanned by the off-center states.
* The *connecting map* is the component of `∂⁻` from center states to off-center states.

The stabilization invariance of `GH⁻` then reduces to comparing the off-center complex and the
connecting map with `GC⁻(G)` and multiplication by `V₁ - V₂`; that comparison is not made here.

## Main definitions

* `TauCeti.GridDiagram.stabilizeXCenterComplex`: the complex of center states.
* `TauCeti.GridDiagram.stabilizeXOffCenterComplex`: the complex of off-center states.
* `TauCeti.GridDiagram.stabilizeXConnectingHom`: the connecting chain map between them.
* `TauCeti.GridDiagram.unblockedComplexStabilizeXIsoHomotopyCofiber`: the isomorphism of
  `GC⁻(G')` with the mapping cone of the connecting chain map.

## Main results

* `TauCeti.GridDiagram.unblockedDifferential_comp_stabilizeXCenterInclusion` and
  `TauCeti.GridDiagram.unblockedDifferential_comp_stabilizeXOffCenterInclusion`: the block
  lower-triangular form of `∂⁻` on `GC⁻(G')`.

## References

This is the decomposition of the stabilized complex as a mapping cone in
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.2.
-/

public section

open CategoryTheory HomologicalComplex MvPolynomial

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- The grid states of the `X`-stabilization `G.stabilizeX s.castSucc (G.X s).castSucc s` that do
not contain the center `(s.succ, (G.X s).succ)` of its new block. -/
abbrev StabilizeXOffCenterState : Type :=
  {y : GridState (n + 1) // y s.succ ≠ (G.X s).succ}

section Blocks

variable (R : Type*) [CommSemiring R]

local notation "S" => MvPolynomial (Fin (n + 1)) R

/-- The inclusion of the center block: a grid state `x` of `G` goes to the state of the
stabilization obtained by inserting the center of the new block. -/
noncomputable def stabilizeXCenterInclusion :
    (GridState n →₀ S) →ₗ[S] GridChainMinus R (n + 1) :=
  Finsupp.lmapDomain S S fun x => x.insertPoint s.succ (G.X s).succ

/-- The projection onto the center block, reading off the coefficients of the states containing
the center of the new block. -/
noncomputable def stabilizeXCenterProjection :
    GridChainMinus R (n + 1) →ₗ[S] (GridState n →₀ S) :=
  Finsupp.lcomapDomain _ (GridState.insertPoint_injective s.succ (G.X s).succ)

/-- The inclusion of the off-center block. -/
noncomputable def stabilizeXOffCenterInclusion :
    (G.StabilizeXOffCenterState s →₀ S) →ₗ[S] GridChainMinus R (n + 1) :=
  Finsupp.lmapDomain S S Subtype.val

/-- The projection onto the off-center block. -/
noncomputable def stabilizeXOffCenterProjection :
    GridChainMinus R (n + 1) →ₗ[S] (G.StabilizeXOffCenterState s →₀ S) :=
  Finsupp.lcomapDomain _ Subtype.val_injective

/-- The center inclusion inserts the center of the new block into a generator. -/
@[simp]
theorem stabilizeXCenterInclusion_single (x : GridState n) (a : S) :
    G.stabilizeXCenterInclusion s R (Finsupp.single x a) =
      Finsupp.single (x.insertPoint s.succ (G.X s).succ) a :=
  Finsupp.mapDomain_single

/-- The center projection reads off the coefficient of the state with the center inserted. -/
@[simp]
theorem stabilizeXCenterProjection_apply (f : GridChainMinus R (n + 1)) (x : GridState n) :
    G.stabilizeXCenterProjection s R f x = f (x.insertPoint s.succ (G.X s).succ) :=
  (rfl)

/-- The off-center inclusion sends a generator to the same grid state. -/
@[simp]
theorem stabilizeXOffCenterInclusion_single (y : G.StabilizeXOffCenterState s) (a : S) :
    G.stabilizeXOffCenterInclusion s R (Finsupp.single y a) = Finsupp.single y.1 a :=
  Finsupp.mapDomain_single

/-- The off-center projection restricts a chain to the off-center states. -/
@[simp]
theorem stabilizeXOffCenterProjection_apply (f : GridChainMinus R (n + 1))
    (y : G.StabilizeXOffCenterState s) :
    G.stabilizeXOffCenterProjection s R f y = f y :=
  (rfl)

private theorem stabilizeXCenterInclusion_projection_apply (f : GridChainMinus R (n + 1))
    (y : GridState (n + 1)) :
    G.stabilizeXCenterInclusion s R (G.stabilizeXCenterProjection s R f) y =
      if y s.succ = (G.X s).succ then f y else 0 := by
  split_ifs with h
  · obtain ⟨x, rfl⟩ := GridState.exists_insertPoint_eq h
    simp [stabilizeXCenterInclusion, stabilizeXCenterProjection,
      Finsupp.mapDomain_apply (GridState.insertPoint_injective _ _)]
  · refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨x, rfl⟩
    exact h (GridState.insertPoint_apply_newColumn _ _ _)

private theorem stabilizeXOffCenterInclusion_projection_apply (f : GridChainMinus R (n + 1))
    (y : GridState (n + 1)) :
    G.stabilizeXOffCenterInclusion s R (G.stabilizeXOffCenterProjection s R f) y =
      if y s.succ = (G.X s).succ then 0 else f y := by
  split_ifs with h
  · refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨y, rfl⟩
    exact y.2 h
  · exact Finsupp.mapDomain_apply Subtype.val_injective _ (⟨y, h⟩ : G.StabilizeXOffCenterState s)

/-- Every chain of the stabilization is the sum of its center and off-center parts. -/
@[simp] theorem stabilizeXCenterInclusion_projection_add_offCenter (f : GridChainMinus R (n + 1)) :
    G.stabilizeXCenterInclusion s R (G.stabilizeXCenterProjection s R f) +
      G.stabilizeXOffCenterInclusion s R (G.stabilizeXOffCenterProjection s R f) = f := by
  ext y
  rw [Finsupp.add_apply, stabilizeXCenterInclusion_projection_apply,
    stabilizeXOffCenterInclusion_projection_apply]
  split_ifs <;> simp

/-- The center projection is a retraction of the center inclusion. -/
@[simp]
theorem stabilizeXCenterProjection_inclusion (f : GridState n →₀ S) :
    G.stabilizeXCenterProjection s R (G.stabilizeXCenterInclusion s R f) = f :=
  Finsupp.leftInverse_lcomapDomain_mapDomain _ _ f

/-- The off-center projection is a retraction of the off-center inclusion. -/
@[simp]
theorem stabilizeXOffCenterProjection_inclusion (f : G.StabilizeXOffCenterState s →₀ S) :
    G.stabilizeXOffCenterProjection s R (G.stabilizeXOffCenterInclusion s R f) = f :=
  Finsupp.leftInverse_lcomapDomain_mapDomain _ _ f

/-- An off-center chain has no center part. -/
@[simp]
theorem stabilizeXCenterProjection_offCenterInclusion (f : G.StabilizeXOffCenterState s →₀ S) :
    G.stabilizeXCenterProjection s R (G.stabilizeXOffCenterInclusion s R f) = 0 := by
  refine Finsupp.ext fun x => Finsupp.mapDomain_of_notMem_range _ _ ?_
  rintro ⟨y, hy⟩
  exact y.2 (hy ▸ GridState.insertPoint_apply_newColumn _ _ _)

/-- A center chain has no off-center part. -/
@[simp]
theorem stabilizeXOffCenterProjection_centerInclusion (f : GridState n →₀ S) :
    G.stabilizeXOffCenterProjection s R (G.stabilizeXCenterInclusion s R f) = 0 := by
  refine Finsupp.ext fun y => Finsupp.mapDomain_of_notMem_range _ _ ?_
  rintro ⟨x, hx⟩
  exact y.2 (hx ▸ GridState.insertPoint_apply_newColumn _ _ _)

/-- The unblocked differential of the stabilization has no component from off-center states to
center states. -/
@[simp]
theorem stabilizeXCenterProjection_unblockedDifferential_offCenterInclusion
    (f : G.StabilizeXOffCenterState s →₀ S) :
    G.stabilizeXCenterProjection s R
      ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R
        (G.stabilizeXOffCenterInclusion s R f)) = 0 := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg, add_zero]
  | single y a =>
    refine Finsupp.ext fun x => ?_
    rw [stabilizeXOffCenterInclusion_single, ← mul_one a, ← smul_eq_mul, ← Finsupp.smul_single,
      map_smul]
    simp [G.unblockedCoefficient_stabilizeX_eq_zero s R y.2]

/-- The center block of the unblocked differential of the stabilization. -/
noncomputable def stabilizeXCenterDifferential : (GridState n →₀ S) →ₗ[S] (GridState n →₀ S) :=
  G.stabilizeXCenterProjection s R ∘ₗ
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R ∘ₗ
      G.stabilizeXCenterInclusion s R

/-- The off-center block of the unblocked differential of the stabilization. -/
noncomputable def stabilizeXOffCenterDifferential :
    (G.StabilizeXOffCenterState s →₀ S) →ₗ[S] (G.StabilizeXOffCenterState s →₀ S) :=
  G.stabilizeXOffCenterProjection s R ∘ₗ
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R ∘ₗ
      G.stabilizeXOffCenterInclusion s R

/-- The connecting map: the component of the unblocked differential of the stabilization from
center states to off-center states. -/
noncomputable def stabilizeXConnecting :
    (GridState n →₀ S) →ₗ[S] (G.StabilizeXOffCenterState s →₀ S) :=
  G.stabilizeXOffCenterProjection s R ∘ₗ
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R ∘ₗ
      G.stabilizeXCenterInclusion s R

/-- **The center block is `GC⁻(G)` over one more variable.** The matrix coefficients of the center
differential are those of the unblocked differential of `G`, with the variable of each column
renamed to the variable of the corresponding column of the stabilization. -/
@[simp]
theorem stabilizeXCenterDifferential_single_apply (x y : GridState n) :
    G.stabilizeXCenterDifferential s R (Finsupp.single x 1) y =
      rename s.castSucc.succAbove (G.unblockedCoefficient R x y) := by
  simp [stabilizeXCenterDifferential]

/-- The matrix coefficients of the off-center differential are those of the unblocked
differential of the stabilization. -/
@[simp]
theorem stabilizeXOffCenterDifferential_single_apply (y z : G.StabilizeXOffCenterState s) :
    G.stabilizeXOffCenterDifferential s R (Finsupp.single y 1) z =
      (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedCoefficient R y z := by
  simp [stabilizeXOffCenterDifferential]

/-- The matrix coefficients of the connecting map are those of the unblocked differential of the
stabilization, from a center state to an off-center state. -/
@[simp]
theorem stabilizeXConnecting_single_apply (x : GridState n) (z : G.StabilizeXOffCenterState s) :
    G.stabilizeXConnecting s R (Finsupp.single x 1) z =
      (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedCoefficient R
        (x.insertPoint s.succ (G.X s).succ) z := by
  simp [stabilizeXConnecting]

/-- **The block form of `∂⁻` on center states.** On the center block, the unblocked differential
of the stabilization is the center differential plus the connecting map. -/
theorem unblockedDifferential_comp_stabilizeXCenterInclusion :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R ∘ₗ
        G.stabilizeXCenterInclusion s R =
      G.stabilizeXCenterInclusion s R ∘ₗ G.stabilizeXCenterDifferential s R +
        G.stabilizeXOffCenterInclusion s R ∘ₗ G.stabilizeXConnecting s R :=
  LinearMap.ext fun _ => (G.stabilizeXCenterInclusion_projection_add_offCenter s R _).symm

/-- **The off-center states span a subcomplex.** On the off-center block, the unblocked
differential of the stabilization is the off-center differential. -/
theorem unblockedDifferential_comp_stabilizeXOffCenterInclusion :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R ∘ₗ
        G.stabilizeXOffCenterInclusion s R =
      G.stabilizeXOffCenterInclusion s R ∘ₗ G.stabilizeXOffCenterDifferential s R :=
  LinearMap.ext fun y => by
    simpa [stabilizeXOffCenterDifferential] using
      (G.stabilizeXCenterInclusion_projection_add_offCenter s R
        ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R
          (G.stabilizeXOffCenterInclusion s R y))).symm

variable [CharP R 2]

private theorem unblockedDifferential_stabilizeX_unblockedDifferential
    (v : GridChainMinus R (n + 1)) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R
      ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R v) = 0 :=
  LinearMap.congr_fun
    ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential_comp_self_eq_zero R) v

/-- The center differential squares to zero. -/
theorem stabilizeXCenterDifferential_comp_self_eq_zero :
    G.stabilizeXCenterDifferential s R ∘ₗ G.stabilizeXCenterDifferential s R = 0 := by
  refine LinearMap.ext fun x => ?_
  have h := congrArg (G.stabilizeXCenterProjection s R ∘ₗ
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R)
    (LinearMap.congr_fun (G.unblockedDifferential_comp_stabilizeXCenterInclusion s R) x)
  simpa [unblockedDifferential_stabilizeX_unblockedDifferential,
    stabilizeXCenterDifferential] using h.symm

/-- The off-center differential squares to zero. -/
theorem stabilizeXOffCenterDifferential_comp_self_eq_zero :
    G.stabilizeXOffCenterDifferential s R ∘ₗ G.stabilizeXOffCenterDifferential s R = 0 := by
  refine LinearMap.ext fun y => ?_
  have h := congrArg (G.stabilizeXOffCenterProjection s R ∘ₗ
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R)
    (LinearMap.congr_fun (G.unblockedDifferential_comp_stabilizeXOffCenterInclusion s R) y)
  simpa [unblockedDifferential_stabilizeX_unblockedDifferential,
    stabilizeXOffCenterDifferential] using h.symm

end Blocks

variable (R : Type*) [CommRing R] [CharP R 2]

local notation "S" => MvPolynomial (Fin (n + 1)) R

/-- The connecting map intertwines the center and off-center differentials. -/
theorem stabilizeXConnecting_comp_centerDifferential :
    G.stabilizeXConnecting s R ∘ₗ G.stabilizeXCenterDifferential s R =
      G.stabilizeXOffCenterDifferential s R ∘ₗ G.stabilizeXConnecting s R := by
  refine LinearMap.ext fun x => ?_
  have h := congrArg (G.stabilizeXOffCenterProjection s R ∘ₗ
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R)
    (LinearMap.congr_fun (G.unblockedDifferential_comp_stabilizeXCenterInclusion s R) x)
  simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add,
    unblockedDifferential_stabilizeX_unblockedDifferential, map_zero] at h
  -- `h` says that the two composites sum to zero; in characteristic two they are equal.
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  conv_lhs => rw [stabilizeXConnecting, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [stabilizeXOffCenterDifferential, LinearMap.comp_apply, LinearMap.comp_apply,
    eq_neg_of_add_eq_zero_left h.symm, ← neg_one_smul S, CharTwo.neg_eq, one_smul]

/-! ### The mapping cone -/

/-- The complex of center states: the center block of the unblocked complex of the
stabilization, as a one-object complex over `R[V₀, …, V_n]`. Its generators are the grid states
of `G`, and its differential is that of `GC⁻(G)` with the variables renamed
(`stabilizeXCenterDifferential_single_apply`). -/
noncomputable def stabilizeXCenterComplex :
    HomologicalComplex (ModuleCat S) (ComplexShape.refl Unit) :=
  oneObjectHomologicalComplex (ModuleCat.of S (GridState n →₀ S))
    (ModuleCat.ofHom (G.stabilizeXCenterDifferential s R)) (by
      rw [← ModuleCat.ofHom_comp, G.stabilizeXCenterDifferential_comp_self_eq_zero s R,
        ModuleCat.ofHom_zero])

/-- The unique object of the center complex is the free module on the grid states of `G`. -/
@[simp]
theorem stabilizeXCenterComplex_X (i : Unit) :
    (G.stabilizeXCenterComplex s R).X i = ModuleCat.of S (GridState n →₀ S) :=
  oneObjectHomologicalComplex_X _ _ _ _

/-- The unique differential of the center complex is the center differential. -/
@[simp]
theorem stabilizeXCenterComplex_d :
    (G.stabilizeXCenterComplex s R).d () () =
      eqToHom (G.stabilizeXCenterComplex_X s R ()) ≫
        ModuleCat.ofHom (G.stabilizeXCenterDifferential s R) ≫
          eqToHom (G.stabilizeXCenterComplex_X s R ()).symm := by
  unfold stabilizeXCenterComplex
  exact oneObjectHomologicalComplex_d _ _ _

/-- The complex of off-center states: the subcomplex of the unblocked complex of the
stabilization spanned by the grid states not containing the center of the new block. -/
noncomputable def stabilizeXOffCenterComplex :
    HomologicalComplex (ModuleCat S) (ComplexShape.refl Unit) :=
  oneObjectHomologicalComplex (ModuleCat.of S (G.StabilizeXOffCenterState s →₀ S))
    (ModuleCat.ofHom (G.stabilizeXOffCenterDifferential s R)) (by
      rw [← ModuleCat.ofHom_comp, G.stabilizeXOffCenterDifferential_comp_self_eq_zero s R,
        ModuleCat.ofHom_zero])

/-- The unique object of the off-center complex is the free module on the off-center states. -/
@[simp]
theorem stabilizeXOffCenterComplex_X (i : Unit) :
    (G.stabilizeXOffCenterComplex s R).X i =
      ModuleCat.of S (G.StabilizeXOffCenterState s →₀ S) :=
  oneObjectHomologicalComplex_X _ _ _ _

/-- The unique differential of the off-center complex is the off-center differential. -/
@[simp]
theorem stabilizeXOffCenterComplex_d :
    (G.stabilizeXOffCenterComplex s R).d () () =
      eqToHom (G.stabilizeXOffCenterComplex_X s R ()) ≫
        ModuleCat.ofHom (G.stabilizeXOffCenterDifferential s R) ≫
          eqToHom (G.stabilizeXOffCenterComplex_X s R ()).symm := by
  unfold stabilizeXOffCenterComplex
  exact oneObjectHomologicalComplex_d _ _ _

/-- The connecting map as a chain map from the center complex to the off-center complex. -/
noncomputable def stabilizeXConnectingHom :
    G.stabilizeXCenterComplex s R ⟶ G.stabilizeXOffCenterComplex s R where
  f i := eqToHom (G.stabilizeXCenterComplex_X s R i) ≫
    ModuleCat.ofHom (G.stabilizeXConnecting s R) ≫
      eqToHom (G.stabilizeXOffCenterComplex_X s R i).symm
  comm' := by
    rintro ⟨⟩ ⟨⟩ -
    simp only [stabilizeXCenterComplex_d, stabilizeXOffCenterComplex_d, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (ModuleCat.ofHom _), ← Category.assoc (ModuleCat.ofHom _),
      ← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp,
      G.stabilizeXConnecting_comp_centerDifferential s R]

/-- The component of the connecting chain map is the connecting map. -/
@[simp]
theorem stabilizeXConnectingHom_f (i : Unit) :
    (G.stabilizeXConnectingHom s R).f i =
      eqToHom (G.stabilizeXCenterComplex_X s R i) ≫
        ModuleCat.ofHom (G.stabilizeXConnecting s R) ≫
          eqToHom (G.stabilizeXOffCenterComplex_X s R i).symm :=
  (rfl)

/-- The splitting of the unblocked chain module of the stabilization into its off-center and
center summands: the off-center inclusion and the center projection, split by the off-center
projection and the center inclusion. -/
private noncomputable def stabilizeXSplitting :
    (ShortComplex.mk
      (eqToHom (G.stabilizeXOffCenterComplex_X s R ()) ≫
        ModuleCat.ofHom (G.stabilizeXOffCenterInclusion s R) ≫
          eqToHom ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex_X R ()).symm)
      (eqToHom ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex_X R ()) ≫
        ModuleCat.ofHom (G.stabilizeXCenterProjection s R) ≫
          eqToHom (G.stabilizeXCenterComplex_X s R ()).symm) (by
        have h : G.stabilizeXCenterProjection s R ∘ₗ G.stabilizeXOffCenterInclusion s R = 0 :=
          LinearMap.ext (G.stabilizeXCenterProjection_offCenterInclusion s R)
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        rw [← Category.assoc (ModuleCat.ofHom _), ← ModuleCat.ofHom_comp, h, ModuleCat.ofHom_zero,
          Limits.zero_comp, Limits.comp_zero])).Splitting where
  r := eqToHom ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex_X R ()) ≫
    ModuleCat.ofHom (G.stabilizeXOffCenterProjection s R) ≫
      eqToHom (G.stabilizeXOffCenterComplex_X s R ()).symm
  s := eqToHom (G.stabilizeXCenterComplex_X s R ()) ≫
    ModuleCat.ofHom (G.stabilizeXCenterInclusion s R) ≫
      eqToHom ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex_X R ()).symm
  f_r := by
    have h : G.stabilizeXOffCenterProjection s R ∘ₗ G.stabilizeXOffCenterInclusion s R =
        LinearMap.id := LinearMap.ext (G.stabilizeXOffCenterProjection_inclusion s R)
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (ModuleCat.ofHom _), ← ModuleCat.ofHom_comp, h, ModuleCat.ofHom_id,
      Category.id_comp, eqToHom_trans, eqToHom_refl]
  s_g := by
    have h : G.stabilizeXCenterProjection s R ∘ₗ G.stabilizeXCenterInclusion s R =
        LinearMap.id := LinearMap.ext (G.stabilizeXCenterProjection_inclusion s R)
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (ModuleCat.ofHom _), ← ModuleCat.ofHom_comp, h, ModuleCat.ofHom_id,
      Category.id_comp, eqToHom_trans, eqToHom_refl]
  id := by
    have h : G.stabilizeXOffCenterInclusion s R ∘ₗ G.stabilizeXOffCenterProjection s R +
        G.stabilizeXCenterInclusion s R ∘ₗ G.stabilizeXCenterProjection s R = LinearMap.id :=
      LinearMap.ext fun v =>
        (add_comm _ _).trans (G.stabilizeXCenterInclusion_projection_add_offCenter s R v)
    simpa only [ModuleCat.ofHom_add, ModuleCat.ofHom_comp, ModuleCat.ofHom_id,
      Preadditive.comp_add, Preadditive.add_comp, Category.assoc, eqToHom_trans_assoc,
      eqToHom_trans, eqToHom_refl, Category.id_comp] using congrArg
        (fun f =>
          eqToHom ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex_X R ()) ≫
            ModuleCat.ofHom f ≫
              eqToHom
                ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex_X R ()).symm) h

/-- **The unblocked complex of an `X`-stabilization is a mapping cone.** The unblocked complex
`GC⁻` of the stabilization `G.stabilizeX s.castSucc (G.X s).castSucc s` is isomorphic to the
mapping cone of the connecting chain map from the center complex (the states containing the
center of the new block) to the off-center complex (the other states). -/
noncomputable def unblockedComplexStabilizeXIsoHomotopyCofiber :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex R ≅
      homotopyCofiber (G.stabilizeXConnectingHom s R) :=
  (homotopyCofiber.isoOfSplitting (G.stabilizeXConnectingHom s R) (G.stabilizeXSplitting s R) (by
      -- In characteristic two, `∂⁻` on the center block is the connecting map minus the center
      -- differential, which is the sign convention of the mapping cone.
      have h : (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R ∘ₗ
          G.stabilizeXCenterInclusion s R =
            G.stabilizeXOffCenterInclusion s R ∘ₗ G.stabilizeXConnecting s R -
              G.stabilizeXCenterInclusion s R ∘ₗ G.stabilizeXCenterDifferential s R := by
        refine (G.unblockedDifferential_comp_stabilizeXCenterInclusion s R).trans
          (LinearMap.ext fun x => ?_)
        have hneg (v : GridChainMinus R (n + 1)) : -v = v := by
          rw [← neg_one_smul S v, CharTwo.neg_eq, one_smul]
        rw [LinearMap.add_apply, LinearMap.sub_apply, sub_eq_add_neg, hneg]
        exact add_comm _ _
      simp only [stabilizeXSplitting, unblockedComplex_d, stabilizeXCenterComplex_d,
        stabilizeXConnectingHom_f, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
      rw [← Category.assoc (ModuleCat.ofHom _), ← ModuleCat.ofHom_comp,
        ← Category.assoc (ModuleCat.ofHom _), ← ModuleCat.ofHom_comp,
        ← Category.assoc (ModuleCat.ofHom _), ← ModuleCat.ofHom_comp, ← Preadditive.comp_sub,
        ← Preadditive.sub_comp, h]
      exact congrArg (_ ≫ · ≫ _) (ModuleCat.hom_ext (by simp))) (by
      simp only [unblockedComplex_d, stabilizeXOffCenterComplex_d, Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← Category.assoc (ModuleCat.ofHom _), ← ModuleCat.ofHom_comp,
        ← Category.assoc (ModuleCat.ofHom _), ← ModuleCat.ofHom_comp,
        unblockedDifferential_comp_stabilizeXOffCenterInclusion])).symm

/-- The isomorphism with the mapping cone sends a chain to its center part in the first summand
of the cone and to its off-center part in the second. -/
@[simp]
theorem unblockedComplexStabilizeXIsoHomotopyCofiber_hom_f :
    (G.unblockedComplexStabilizeXIsoHomotopyCofiber s R).hom.f () =
      (eqToHom ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex_X R ()) ≫
          ModuleCat.ofHom (G.stabilizeXCenterProjection s R) ≫
            eqToHom (G.stabilizeXCenterComplex_X s R ()).symm) ≫
        homotopyCofiber.inlX (G.stabilizeXConnectingHom s R) () () (ComplexShape.refl_rel ()) +
      (eqToHom ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex_X R ()) ≫
          ModuleCat.ofHom (G.stabilizeXOffCenterProjection s R) ≫
            eqToHom (G.stabilizeXOffCenterComplex_X s R ()).symm) ≫
        homotopyCofiber.inrX (G.stabilizeXConnectingHom s R) () :=
  homotopyCofiber.isoOfSplitting_inv_f _ _ _ _

/-- The inverse isomorphism includes the first summand of the cone as the center states and the
second as the off-center states. -/
@[simp]
theorem unblockedComplexStabilizeXIsoHomotopyCofiber_inv_f :
    (G.unblockedComplexStabilizeXIsoHomotopyCofiber s R).inv.f () =
      homotopyCofiber.fstX (G.stabilizeXConnectingHom s R) () () (ComplexShape.refl_rel ()) ≫
          eqToHom (G.stabilizeXCenterComplex_X s R ()) ≫
            ModuleCat.ofHom (G.stabilizeXCenterInclusion s R) ≫
              eqToHom ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex_X R ()).symm +
        homotopyCofiber.sndX (G.stabilizeXConnectingHom s R) () ≫
          eqToHom (G.stabilizeXOffCenterComplex_X s R ()) ≫
            ModuleCat.ofHom (G.stabilizeXOffCenterInclusion s R) ≫
              eqToHom ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex_X R ()).symm :=
  homotopyCofiber.isoOfSplitting_hom_f _ _ _ _

end GridDiagram

end TauCeti
