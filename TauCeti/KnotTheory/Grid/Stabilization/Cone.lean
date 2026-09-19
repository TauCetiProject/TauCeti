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
of column `s`, whose new `2 × 2` block is centred at the grid point `c = (s.succ, (G.X s).succ)`
(see `TauCeti.KnotTheory.Grid.Stabilization.Unblocked`). Write `S = R[V₀, …, V_n]` for the
coefficient ring of `GC⁻(G')`.

The grid states of `G'` split into the *centre states*, those containing `c`, and the
*off-centre states* (the sets `I` and `N` of Ozsváth--Stipsicz--Szabó). The centre states are the
states `x.insertPoint s.succ (G.X s).succ` for `x` a grid state of `G`, so as an `S`-module

`GC⁻(G') = (GridState n →₀ S) ⊕ (off-centre states →₀ S)`.

The unblocked differential has no component from off-centre states to centre states
(`unblockedCoefficient_stabilizeX_eq_zero`), so the off-centre states span a subcomplex, and in
characteristic two `GC⁻(G')` is the mapping cone of the component of `∂⁻` from the centre block to
the off-centre block. This file packages that statement with Mathlib's `homotopyCofiber`.

* The *centre complex* has the grid states of `G` as generators and, by
  `unblockedCoefficient_stabilizeX_insertPoint`, the differential of `GC⁻(G)` with its variables
  renamed into `S` (`stabilizeXCentreDifferential_single_apply`). The variable of the new
  `O`-marking never occurs, so this is `GC⁻(G)` with one free variable adjoined.
* The *off-centre complex* is the subcomplex spanned by the off-centre states.
* The *connecting map* is the component of `∂⁻` from centre states to off-centre states.

The stabilization invariance of `GH⁻` then reduces to comparing the off-centre complex and the
connecting map with `GC⁻(G)` and multiplication by `V₁ - V₂`; that comparison is not made here.

## Main definitions

* `TauCeti.GridDiagram.stabilizeXCentreComplex`: the complex of centre states.
* `TauCeti.GridDiagram.stabilizeXOffCentreComplex`: the complex of off-centre states.
* `TauCeti.GridDiagram.stabilizeXConnectingHom`: the connecting chain map between them.
* `TauCeti.GridDiagram.unblockedComplexStabilizeXIsoHomotopyCofiber`: the isomorphism of
  `GC⁻(G')` with the mapping cone of the connecting chain map.

## Main results

* `TauCeti.GridDiagram.unblockedDifferential_comp_stabilizeXCentreInclusion` and
  `TauCeti.GridDiagram.unblockedDifferential_comp_stabilizeXOffCentreInclusion`: the block
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
not contain the centre `(s.succ, (G.X s).succ)` of its new block. -/
abbrev StabilizeXOffCentreState : Type :=
  {y : GridState (n + 1) // y s.succ ≠ (G.X s).succ}

section Blocks

variable (R : Type*) [CommSemiring R]

local notation "S" => MvPolynomial (Fin (n + 1)) R

/-- The inclusion of the centre block: a grid state `x` of `G` goes to the state of the
stabilization obtained by inserting the centre of the new block. -/
noncomputable def stabilizeXCentreInclusion :
    (GridState n →₀ S) →ₗ[S] GridChainMinus R (n + 1) :=
  Finsupp.lmapDomain S S fun x => x.insertPoint s.succ (G.X s).succ

/-- The projection onto the centre block, reading off the coefficients of the states containing
the centre of the new block. -/
noncomputable def stabilizeXCentreProjection :
    GridChainMinus R (n + 1) →ₗ[S] (GridState n →₀ S) :=
  Finsupp.lcomapDomain _ (GridState.insertPoint_injective s.succ (G.X s).succ)

/-- The inclusion of the off-centre block. -/
noncomputable def stabilizeXOffCentreInclusion :
    (G.StabilizeXOffCentreState s →₀ S) →ₗ[S] GridChainMinus R (n + 1) :=
  Finsupp.lmapDomain S S Subtype.val

/-- The projection onto the off-centre block. -/
noncomputable def stabilizeXOffCentreProjection :
    GridChainMinus R (n + 1) →ₗ[S] (G.StabilizeXOffCentreState s →₀ S) :=
  Finsupp.lcomapDomain _ Subtype.val_injective

/-- The centre inclusion inserts the centre of the new block into a generator. -/
@[simp]
theorem stabilizeXCentreInclusion_single (x : GridState n) (a : S) :
    G.stabilizeXCentreInclusion s R (Finsupp.single x a) =
      Finsupp.single (x.insertPoint s.succ (G.X s).succ) a :=
  Finsupp.mapDomain_single

/-- The centre projection reads off the coefficient of the state with the centre inserted. -/
@[simp]
theorem stabilizeXCentreProjection_apply (f : GridChainMinus R (n + 1)) (x : GridState n) :
    G.stabilizeXCentreProjection s R f x = f (x.insertPoint s.succ (G.X s).succ) :=
  (rfl)

/-- The off-centre inclusion sends a generator to the same grid state. -/
@[simp]
theorem stabilizeXOffCentreInclusion_single (y : G.StabilizeXOffCentreState s) (a : S) :
    G.stabilizeXOffCentreInclusion s R (Finsupp.single y a) = Finsupp.single y.1 a :=
  Finsupp.mapDomain_single

/-- The off-centre projection restricts a chain to the off-centre states. -/
@[simp]
theorem stabilizeXOffCentreProjection_apply (f : GridChainMinus R (n + 1))
    (y : G.StabilizeXOffCentreState s) :
    G.stabilizeXOffCentreProjection s R f y = f y :=
  (rfl)

private theorem stabilizeXCentreInclusion_projection_apply (f : GridChainMinus R (n + 1))
    (y : GridState (n + 1)) :
    G.stabilizeXCentreInclusion s R (G.stabilizeXCentreProjection s R f) y =
      if y s.succ = (G.X s).succ then f y else 0 := by
  split_ifs with h
  · obtain ⟨x, rfl⟩ := GridState.exists_insertPoint_eq h
    simp [stabilizeXCentreInclusion, stabilizeXCentreProjection,
      Finsupp.mapDomain_apply (GridState.insertPoint_injective _ _)]
  · refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨x, rfl⟩
    exact h (GridState.insertPoint_apply_newColumn _ _ _)

private theorem stabilizeXOffCentreInclusion_projection_apply (f : GridChainMinus R (n + 1))
    (y : GridState (n + 1)) :
    G.stabilizeXOffCentreInclusion s R (G.stabilizeXOffCentreProjection s R f) y =
      if y s.succ = (G.X s).succ then 0 else f y := by
  split_ifs with h
  · refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨y, rfl⟩
    exact y.2 h
  · exact Finsupp.mapDomain_apply Subtype.val_injective _ (⟨y, h⟩ : G.StabilizeXOffCentreState s)

/-- Every chain of the stabilization is the sum of its centre and off-centre parts. -/
theorem stabilizeXCentreInclusion_projection_add_offCentre (f : GridChainMinus R (n + 1)) :
    G.stabilizeXCentreInclusion s R (G.stabilizeXCentreProjection s R f) +
      G.stabilizeXOffCentreInclusion s R (G.stabilizeXOffCentreProjection s R f) = f := by
  ext y
  rw [Finsupp.add_apply, stabilizeXCentreInclusion_projection_apply,
    stabilizeXOffCentreInclusion_projection_apply]
  split_ifs <;> simp

/-- The centre projection is a retraction of the centre inclusion. -/
@[simp]
theorem stabilizeXCentreProjection_inclusion (f : GridState n →₀ S) :
    G.stabilizeXCentreProjection s R (G.stabilizeXCentreInclusion s R f) = f :=
  Finsupp.leftInverse_lcomapDomain_mapDomain _ _ f

/-- The off-centre projection is a retraction of the off-centre inclusion. -/
@[simp]
theorem stabilizeXOffCentreProjection_inclusion (f : G.StabilizeXOffCentreState s →₀ S) :
    G.stabilizeXOffCentreProjection s R (G.stabilizeXOffCentreInclusion s R f) = f :=
  Finsupp.leftInverse_lcomapDomain_mapDomain _ _ f

/-- An off-centre chain has no centre part. -/
@[simp]
theorem stabilizeXCentreProjection_offCentreInclusion (f : G.StabilizeXOffCentreState s →₀ S) :
    G.stabilizeXCentreProjection s R (G.stabilizeXOffCentreInclusion s R f) = 0 := by
  refine Finsupp.ext fun x => Finsupp.mapDomain_of_notMem_range _ _ ?_
  rintro ⟨y, hy⟩
  exact y.2 (hy ▸ GridState.insertPoint_apply_newColumn _ _ _)

/-- A centre chain has no off-centre part. -/
@[simp]
theorem stabilizeXOffCentreProjection_centreInclusion (f : GridState n →₀ S) :
    G.stabilizeXOffCentreProjection s R (G.stabilizeXCentreInclusion s R f) = 0 := by
  refine Finsupp.ext fun y => Finsupp.mapDomain_of_notMem_range _ _ ?_
  rintro ⟨x, hx⟩
  exact y.2 (hx ▸ GridState.insertPoint_apply_newColumn _ _ _)

/-- The unblocked differential of the stabilization has no component from off-centre states to
centre states. -/
@[simp]
theorem stabilizeXCentreProjection_unblockedDifferential_offCentreInclusion
    (f : G.StabilizeXOffCentreState s →₀ S) :
    G.stabilizeXCentreProjection s R
      ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R
        (G.stabilizeXOffCentreInclusion s R f)) = 0 := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg, add_zero]
  | single y a =>
    refine Finsupp.ext fun x => ?_
    rw [stabilizeXOffCentreInclusion_single, ← mul_one a, ← smul_eq_mul, ← Finsupp.smul_single,
      map_smul]
    simp [G.unblockedCoefficient_stabilizeX_eq_zero s R y.2]

/-- The centre block of the unblocked differential of the stabilization. -/
noncomputable def stabilizeXCentreDifferential : (GridState n →₀ S) →ₗ[S] (GridState n →₀ S) :=
  G.stabilizeXCentreProjection s R ∘ₗ
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R ∘ₗ
      G.stabilizeXCentreInclusion s R

/-- The off-centre block of the unblocked differential of the stabilization. -/
noncomputable def stabilizeXOffCentreDifferential :
    (G.StabilizeXOffCentreState s →₀ S) →ₗ[S] (G.StabilizeXOffCentreState s →₀ S) :=
  G.stabilizeXOffCentreProjection s R ∘ₗ
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R ∘ₗ
      G.stabilizeXOffCentreInclusion s R

/-- The connecting map: the component of the unblocked differential of the stabilization from
centre states to off-centre states. -/
noncomputable def stabilizeXConnecting :
    (GridState n →₀ S) →ₗ[S] (G.StabilizeXOffCentreState s →₀ S) :=
  G.stabilizeXOffCentreProjection s R ∘ₗ
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R ∘ₗ
      G.stabilizeXCentreInclusion s R

/-- **The centre block is `GC⁻(G)` over one more variable.** The matrix coefficients of the centre
differential are those of the unblocked differential of `G`, with the variable of each column
renamed to the variable of the corresponding column of the stabilization. -/
@[simp]
theorem stabilizeXCentreDifferential_single_apply (x y : GridState n) :
    G.stabilizeXCentreDifferential s R (Finsupp.single x 1) y =
      rename s.castSucc.succAbove (G.unblockedCoefficient R x y) := by
  simp [stabilizeXCentreDifferential]

/-- The matrix coefficients of the off-centre differential are those of the unblocked
differential of the stabilization. -/
@[simp]
theorem stabilizeXOffCentreDifferential_single_apply (y z : G.StabilizeXOffCentreState s) :
    G.stabilizeXOffCentreDifferential s R (Finsupp.single y 1) z =
      (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedCoefficient R y z := by
  simp [stabilizeXOffCentreDifferential]

/-- The matrix coefficients of the connecting map are those of the unblocked differential of the
stabilization, from a centre state to an off-centre state. -/
@[simp]
theorem stabilizeXConnecting_single_apply (x : GridState n) (z : G.StabilizeXOffCentreState s) :
    G.stabilizeXConnecting s R (Finsupp.single x 1) z =
      (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedCoefficient R
        (x.insertPoint s.succ (G.X s).succ) z := by
  simp [stabilizeXConnecting]

/-- **The block form of `∂⁻` on centre states.** On the centre block, the unblocked differential
of the stabilization is the centre differential plus the connecting map. -/
theorem unblockedDifferential_comp_stabilizeXCentreInclusion :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R ∘ₗ
        G.stabilizeXCentreInclusion s R =
      G.stabilizeXCentreInclusion s R ∘ₗ G.stabilizeXCentreDifferential s R +
        G.stabilizeXOffCentreInclusion s R ∘ₗ G.stabilizeXConnecting s R :=
  LinearMap.ext fun _ => (G.stabilizeXCentreInclusion_projection_add_offCentre s R _).symm

/-- **The off-centre states span a subcomplex.** On the off-centre block, the unblocked
differential of the stabilization is the off-centre differential. -/
theorem unblockedDifferential_comp_stabilizeXOffCentreInclusion :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R ∘ₗ
        G.stabilizeXOffCentreInclusion s R =
      G.stabilizeXOffCentreInclusion s R ∘ₗ G.stabilizeXOffCentreDifferential s R :=
  LinearMap.ext fun y => by
    simpa [stabilizeXOffCentreDifferential] using
      (G.stabilizeXCentreInclusion_projection_add_offCentre s R
        ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R
          (G.stabilizeXOffCentreInclusion s R y))).symm

variable [CharP R 2]

private theorem unblockedDifferential_stabilizeX_unblockedDifferential
    (v : GridChainMinus R (n + 1)) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R
      ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R v) = 0 :=
  LinearMap.congr_fun
    ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential_comp_self_eq_zero R) v

/-- The centre differential squares to zero. -/
theorem stabilizeXCentreDifferential_comp_self :
    G.stabilizeXCentreDifferential s R ∘ₗ G.stabilizeXCentreDifferential s R = 0 := by
  refine LinearMap.ext fun x => ?_
  have h := congrArg (G.stabilizeXCentreProjection s R ∘ₗ
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R)
    (LinearMap.congr_fun (G.unblockedDifferential_comp_stabilizeXCentreInclusion s R) x)
  simpa [unblockedDifferential_stabilizeX_unblockedDifferential,
    stabilizeXCentreDifferential] using h.symm

/-- The off-centre differential squares to zero. -/
theorem stabilizeXOffCentreDifferential_comp_self :
    G.stabilizeXOffCentreDifferential s R ∘ₗ G.stabilizeXOffCentreDifferential s R = 0 := by
  refine LinearMap.ext fun y => ?_
  have h := congrArg (G.stabilizeXOffCentreProjection s R ∘ₗ
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R)
    (LinearMap.congr_fun (G.unblockedDifferential_comp_stabilizeXOffCentreInclusion s R) y)
  simpa [unblockedDifferential_stabilizeX_unblockedDifferential,
    stabilizeXOffCentreDifferential] using h.symm

end Blocks

variable (R : Type*) [CommRing R] [CharP R 2]

local notation "S" => MvPolynomial (Fin (n + 1)) R

/-- The connecting map intertwines the centre and off-centre differentials. -/
theorem stabilizeXConnecting_comp_centreDifferential :
    G.stabilizeXConnecting s R ∘ₗ G.stabilizeXCentreDifferential s R =
      G.stabilizeXOffCentreDifferential s R ∘ₗ G.stabilizeXConnecting s R := by
  refine LinearMap.ext fun x => ?_
  have h := congrArg (G.stabilizeXOffCentreProjection s R ∘ₗ
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R)
    (LinearMap.congr_fun (G.unblockedDifferential_comp_stabilizeXCentreInclusion s R) x)
  simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add,
    unblockedDifferential_stabilizeX_unblockedDifferential, map_zero] at h
  -- `h` says that the two composites sum to zero; in characteristic two they are equal.
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  conv_lhs => rw [stabilizeXConnecting, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [stabilizeXOffCentreDifferential, LinearMap.comp_apply, LinearMap.comp_apply,
    eq_neg_of_add_eq_zero_left h.symm, ← neg_one_smul S, CharTwo.neg_eq, one_smul]

/-! ### The mapping cone -/

/-- The complex of centre states: the centre block of the unblocked complex of the
stabilization, as a one-object complex over `R[V₀, …, V_n]`. Its generators are the grid states
of `G`, and its differential is that of `GC⁻(G)` with the variables renamed
(`stabilizeXCentreDifferential_single_apply`). -/
noncomputable def stabilizeXCentreComplex :
    HomologicalComplex (ModuleCat S) (ComplexShape.refl Unit) :=
  oneObjectHomologicalComplex (ModuleCat.of S (GridState n →₀ S))
    (ModuleCat.ofHom (G.stabilizeXCentreDifferential s R)) (by
      rw [← ModuleCat.ofHom_comp, G.stabilizeXCentreDifferential_comp_self s R,
        ModuleCat.ofHom_zero])

/-- The unique object of the centre complex is the free module on the grid states of `G`. -/
@[simp]
theorem stabilizeXCentreComplex_X (i : Unit) :
    (G.stabilizeXCentreComplex s R).X i = ModuleCat.of S (GridState n →₀ S) :=
  oneObjectHomologicalComplex_X _ _ _ _

/-- The unique differential of the centre complex is the centre differential. -/
@[simp]
theorem stabilizeXCentreComplex_d :
    (G.stabilizeXCentreComplex s R).d () () =
      eqToHom (G.stabilizeXCentreComplex_X s R ()) ≫
        ModuleCat.ofHom (G.stabilizeXCentreDifferential s R) ≫
          eqToHom (G.stabilizeXCentreComplex_X s R ()).symm := by
  unfold stabilizeXCentreComplex
  exact oneObjectHomologicalComplex_d _ _ _

/-- The complex of off-centre states: the subcomplex of the unblocked complex of the
stabilization spanned by the grid states not containing the centre of the new block. -/
noncomputable def stabilizeXOffCentreComplex :
    HomologicalComplex (ModuleCat S) (ComplexShape.refl Unit) :=
  oneObjectHomologicalComplex (ModuleCat.of S (G.StabilizeXOffCentreState s →₀ S))
    (ModuleCat.ofHom (G.stabilizeXOffCentreDifferential s R)) (by
      rw [← ModuleCat.ofHom_comp, G.stabilizeXOffCentreDifferential_comp_self s R,
        ModuleCat.ofHom_zero])

/-- The unique object of the off-centre complex is the free module on the off-centre states. -/
@[simp]
theorem stabilizeXOffCentreComplex_X (i : Unit) :
    (G.stabilizeXOffCentreComplex s R).X i =
      ModuleCat.of S (G.StabilizeXOffCentreState s →₀ S) :=
  oneObjectHomologicalComplex_X _ _ _ _

/-- The unique differential of the off-centre complex is the off-centre differential. -/
@[simp]
theorem stabilizeXOffCentreComplex_d :
    (G.stabilizeXOffCentreComplex s R).d () () =
      eqToHom (G.stabilizeXOffCentreComplex_X s R ()) ≫
        ModuleCat.ofHom (G.stabilizeXOffCentreDifferential s R) ≫
          eqToHom (G.stabilizeXOffCentreComplex_X s R ()).symm := by
  unfold stabilizeXOffCentreComplex
  exact oneObjectHomologicalComplex_d _ _ _

/-- The connecting map as a chain map from the centre complex to the off-centre complex. -/
noncomputable def stabilizeXConnectingHom :
    G.stabilizeXCentreComplex s R ⟶ G.stabilizeXOffCentreComplex s R where
  f i := eqToHom (G.stabilizeXCentreComplex_X s R i) ≫
    ModuleCat.ofHom (G.stabilizeXConnecting s R) ≫
      eqToHom (G.stabilizeXOffCentreComplex_X s R i).symm
  comm' := by
    rintro ⟨⟩ ⟨⟩ -
    simp only [stabilizeXCentreComplex_d, stabilizeXOffCentreComplex_d, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (ModuleCat.ofHom _), ← Category.assoc (ModuleCat.ofHom _),
      ← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp,
      G.stabilizeXConnecting_comp_centreDifferential s R]

/-- The component of the connecting chain map is the connecting map. -/
@[simp]
theorem stabilizeXConnectingHom_f (i : Unit) :
    (G.stabilizeXConnectingHom s R).f i =
      eqToHom (G.stabilizeXCentreComplex_X s R i) ≫
        ModuleCat.ofHom (G.stabilizeXConnecting s R) ≫
          eqToHom (G.stabilizeXOffCentreComplex_X s R i).symm :=
  (rfl)

/-- The splitting of the unblocked chain module of the stabilization into its off-centre and
centre summands: the off-centre inclusion and the centre projection, split by the off-centre
projection and the centre inclusion. -/
noncomputable def stabilizeXSplitting :
    (ShortComplex.mk
      (eqToHom (G.stabilizeXOffCentreComplex_X s R ()) ≫
        ModuleCat.ofHom (G.stabilizeXOffCentreInclusion s R) ≫
          eqToHom ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex_X R ()).symm)
      (eqToHom ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex_X R ()) ≫
        ModuleCat.ofHom (G.stabilizeXCentreProjection s R) ≫
          eqToHom (G.stabilizeXCentreComplex_X s R ()).symm) (by
        have h : G.stabilizeXCentreProjection s R ∘ₗ G.stabilizeXOffCentreInclusion s R = 0 :=
          LinearMap.ext (G.stabilizeXCentreProjection_offCentreInclusion s R)
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        rw [← Category.assoc (ModuleCat.ofHom _), ← ModuleCat.ofHom_comp, h, ModuleCat.ofHom_zero,
          Limits.zero_comp, Limits.comp_zero])).Splitting where
  r := eqToHom ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex_X R ()) ≫
    ModuleCat.ofHom (G.stabilizeXOffCentreProjection s R) ≫
      eqToHom (G.stabilizeXOffCentreComplex_X s R ()).symm
  s := eqToHom (G.stabilizeXCentreComplex_X s R ()) ≫
    ModuleCat.ofHom (G.stabilizeXCentreInclusion s R) ≫
      eqToHom ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex_X R ()).symm
  f_r := by
    have h : G.stabilizeXOffCentreProjection s R ∘ₗ G.stabilizeXOffCentreInclusion s R =
        LinearMap.id := LinearMap.ext (G.stabilizeXOffCentreProjection_inclusion s R)
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (ModuleCat.ofHom _), ← ModuleCat.ofHom_comp, h, ModuleCat.ofHom_id,
      Category.id_comp, eqToHom_trans, eqToHom_refl]
  s_g := by
    have h : G.stabilizeXCentreProjection s R ∘ₗ G.stabilizeXCentreInclusion s R =
        LinearMap.id := LinearMap.ext (G.stabilizeXCentreProjection_inclusion s R)
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (ModuleCat.ofHom _), ← ModuleCat.ofHom_comp, h, ModuleCat.ofHom_id,
      Category.id_comp, eqToHom_trans, eqToHom_refl]
  id := by
    have h : G.stabilizeXOffCentreInclusion s R ∘ₗ G.stabilizeXOffCentreProjection s R +
        G.stabilizeXCentreInclusion s R ∘ₗ G.stabilizeXCentreProjection s R = LinearMap.id :=
      LinearMap.ext fun v =>
        (add_comm _ _).trans (G.stabilizeXCentreInclusion_projection_add_offCentre s R v)
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (ModuleCat.ofHom _), ← ModuleCat.ofHom_comp,
      ← Category.assoc (ModuleCat.ofHom _), ← ModuleCat.ofHom_comp, ← Preadditive.comp_add,
      ← Preadditive.add_comp, ← ModuleCat.ofHom_add, h, ModuleCat.ofHom_id, Category.id_comp,
      eqToHom_trans, eqToHom_refl]

/-- **The unblocked complex of an `X`-stabilization is a mapping cone.** The unblocked complex
`GC⁻` of the stabilization `G.stabilizeX s.castSucc (G.X s).castSucc s` is isomorphic to the
mapping cone of the connecting chain map from the centre complex (the states containing the
centre of the new block) to the off-centre complex (the other states). -/
noncomputable def unblockedComplexStabilizeXIsoHomotopyCofiber :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex R ≅
      homotopyCofiber (G.stabilizeXConnectingHom s R) :=
  (homotopyCofiber.isoOfSplitting (G.stabilizeXConnectingHom s R) (G.stabilizeXSplitting s R) (by
      -- In characteristic two, `∂⁻` on the centre block is the connecting map minus the centre
      -- differential, which is the sign convention of the mapping cone.
      have h : (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedDifferential R ∘ₗ
          G.stabilizeXCentreInclusion s R =
            G.stabilizeXOffCentreInclusion s R ∘ₗ G.stabilizeXConnecting s R -
              G.stabilizeXCentreInclusion s R ∘ₗ G.stabilizeXCentreDifferential s R := by
        refine (G.unblockedDifferential_comp_stabilizeXCentreInclusion s R).trans
          (LinearMap.ext fun x => ?_)
        have hneg (v : GridChainMinus R (n + 1)) : -v = v := by
          rw [← neg_one_smul S v, CharTwo.neg_eq, one_smul]
        rw [LinearMap.add_apply, LinearMap.sub_apply, sub_eq_add_neg, hneg]
        exact add_comm _ _
      simp only [stabilizeXSplitting, unblockedComplex_d, stabilizeXCentreComplex_d,
        stabilizeXConnectingHom_f, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
      rw [← Category.assoc (ModuleCat.ofHom _), ← ModuleCat.ofHom_comp,
        ← Category.assoc (ModuleCat.ofHom _), ← ModuleCat.ofHom_comp,
        ← Category.assoc (ModuleCat.ofHom _), ← ModuleCat.ofHom_comp, ← Preadditive.comp_sub,
        ← Preadditive.sub_comp, h]
      exact congrArg (_ ≫ · ≫ _) (ModuleCat.hom_ext (by simp))) (by
      simp only [unblockedComplex_d, stabilizeXOffCentreComplex_d, Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← Category.assoc (ModuleCat.ofHom _), ← ModuleCat.ofHom_comp,
        ← Category.assoc (ModuleCat.ofHom _), ← ModuleCat.ofHom_comp,
        unblockedDifferential_comp_stabilizeXOffCentreInclusion])).symm

/-- The isomorphism with the mapping cone sends a chain to its centre part in the first summand
of the cone and to its off-centre part in the second. -/
@[simp]
theorem unblockedComplexStabilizeXIsoHomotopyCofiber_hom_f :
    (G.unblockedComplexStabilizeXIsoHomotopyCofiber s R).hom.f () =
      (eqToHom ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex_X R ()) ≫
          ModuleCat.ofHom (G.stabilizeXCentreProjection s R) ≫
            eqToHom (G.stabilizeXCentreComplex_X s R ()).symm) ≫
        homotopyCofiber.inlX (G.stabilizeXConnectingHom s R) () () (ComplexShape.refl_rel ()) +
      (eqToHom ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex_X R ()) ≫
          ModuleCat.ofHom (G.stabilizeXOffCentreProjection s R) ≫
            eqToHom (G.stabilizeXOffCentreComplex_X s R ()).symm) ≫
        homotopyCofiber.inrX (G.stabilizeXConnectingHom s R) () :=
  homotopyCofiber.isoOfSplitting_inv_f _ _ _ _

/-- The inverse isomorphism includes the first summand of the cone as the centre states and the
second as the off-centre states. -/
@[simp]
theorem unblockedComplexStabilizeXIsoHomotopyCofiber_inv_f :
    (G.unblockedComplexStabilizeXIsoHomotopyCofiber s R).inv.f () =
      homotopyCofiber.fstX (G.stabilizeXConnectingHom s R) () () (ComplexShape.refl_rel ()) ≫
          eqToHom (G.stabilizeXCentreComplex_X s R ()) ≫
            ModuleCat.ofHom (G.stabilizeXCentreInclusion s R) ≫
              eqToHom ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex_X R ()).symm +
        homotopyCofiber.sndX (G.stabilizeXConnectingHom s R) () ≫
          eqToHom (G.stabilizeXOffCentreComplex_X s R ()) ≫
            ModuleCat.ofHom (G.stabilizeXOffCentreInclusion s R) ≫
              eqToHom ((G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedComplex_X R ()).symm :=
  homotopyCofiber.isoOfSplitting_hom_f _ _ _ _

end GridDiagram

end TauCeti
