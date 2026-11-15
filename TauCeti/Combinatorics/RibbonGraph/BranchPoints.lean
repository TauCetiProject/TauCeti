/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.RibbonGraph.Genus
public import TauCeti.Combinatorics.PermutationTriple.BranchPoints
public import Mathlib.Algebra.Group.Action.TransferInstance

/-!
# Branch-point exchanges on bipartite ribbon graphs

The exchange `swap01` renames the two colours, retaining the cyclic orders at every vertex.
The exchange `swap1Inf` retains the black vertices and replaces the white vertices by faces.
Its white endpoint sends an edge `e` to the old face of `rotW e`; its white rotation is
`rotW⁻¹ * facePerm * rotW`. Thus its new faces are exactly the old white vertices.
Both operations preserve the ribbon orientation: they implement exchanges of branch points,
with the product-one convention, rather than reversing all cyclic orders.

Numbering the unchanged edge set identifies these constructions with the corresponding
operations on permutation triples. Connectedness and genus are preserved, and the exchanges
induce the right action of the permutations of the three branch points on graph isomorphism
classes. The second exchange is an involution only up to isomorphism.

## Implementation notes

The graph constructors are exposed because their edge and vertex carriers are data fields:
consumers need to use the original edges and black vertices, and the original face quotient
as the new white vertices. The characteristic lemmas describe the remaining fields.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.3 and §1.5.
* The formal triple operations are `TauCeti.PermutationTriple.swap01` and
  `TauCeti.PermutationTriple.swap1Inf`.
-/

open Equiv Equiv.Perm

public section

namespace TauCeti

universe u

namespace BipartiteRibbonGraph

variable (Γ : BipartiteRibbonGraph.{u})

/-- Exchange black and white vertices, retaining their cyclic orders and the edge set. -/
@[expose] def swap01 : BipartiteRibbonGraph.{u} where
  E := Γ.E
  B := Γ.W
  W := Γ.B
  fintypeE := inferInstance
  fintypeB := inferInstance
  fintypeW := inferInstance
  decidableEqE := inferInstance
  decidableEqB := inferInstance
  decidableEqW := inferInstance
  blackEnd := Γ.whiteEnd
  whiteEnd := Γ.blackEnd
  rotB := Γ.rotW
  rotW := Γ.rotB
  blackEnd_surjective := Γ.whiteEnd_surjective
  whiteEnd_surjective := Γ.blackEnd_surjective
  isCycleOn_rotB := Γ.isCycleOn_rotW
  isCycleOn_rotW := Γ.isCycleOn_rotB

/-- The new black endpoint is the old white endpoint. -/
@[simp] theorem blackEnd_swap01 (e : Γ.E) : Γ.swap01.blackEnd e = Γ.whiteEnd e := (rfl)

/-- The new white endpoint is the old black endpoint. -/
@[simp] theorem whiteEnd_swap01 (e : Γ.E) : Γ.swap01.whiteEnd e = Γ.blackEnd e := (rfl)

/-- The new black rotation is the old white rotation. -/
@[simp] theorem rotB_swap01 : Γ.swap01.rotB = Γ.rotW := (rfl)

/-- The new white rotation is the old black rotation. -/
@[simp] theorem rotW_swap01 : Γ.swap01.rotW = Γ.rotB := (rfl)

/-- Exchanging the colours twice returns the original graph, including its carriers. -/
@[simp] theorem swap01_swap01 : Γ.swap01.swap01 = Γ := (rfl)

/-- Exchange white vertices with faces, keeping the black vertices and the edge set.
The endpoint shift by the old white rotation realizes the conjugator in the product-one
branch-point exchange. -/
@[expose] noncomputable def swap1Inf : BipartiteRibbonGraph.{u} where
  E := Γ.E
  B := Γ.B
  W := Γ.Face
  fintypeE := inferInstance
  fintypeB := inferInstance
  fintypeW := inferInstance
  decidableEqE := inferInstance
  decidableEqB := inferInstance
  decidableEqW := Classical.decEq _
  blackEnd := Γ.blackEnd
  whiteEnd e := Quotient.mk (SameCycle.setoid Γ.facePerm) (Γ.rotW e)
  rotB := Γ.rotB
  rotW := Γ.rotW⁻¹ * Γ.facePerm * Γ.rotW
  blackEnd_surjective := Γ.blackEnd_surjective
  whiteEnd_surjective := Quotient.mk_surjective.comp Γ.rotW.surjective
  isCycleOn_rotB := Γ.isCycleOn_rotB
  isCycleOn_rotW w := by
    have h := (isCycleOn_preimage_quotientMk Γ.facePerm w).conj (g := Γ.rotW⁻¹)
    rw [inv_inv, Perm.inv_def, image_symm_eq_preimage] at h
    exact h

/-- Exchanging white vertices and faces retains the black endpoint. -/
@[simp] theorem blackEnd_swap1Inf (e : Γ.E) : Γ.swap1Inf.blackEnd e = Γ.blackEnd e := (rfl)

/-- The new white endpoint is the old face of the edge after white rotation. -/
@[simp] theorem whiteEnd_swap1Inf (e : Γ.E) :
    Γ.swap1Inf.whiteEnd e = Quotient.mk (SameCycle.setoid Γ.facePerm) (Γ.rotW e) := (rfl)

/-- Exchanging white vertices and faces retains the black rotation. -/
@[simp] theorem rotB_swap1Inf : Γ.swap1Inf.rotB = Γ.rotB := (rfl)

/-- The new white rotation is the conjugated old face permutation. -/
@[simp] theorem rotW_swap1Inf :
    Γ.swap1Inf.rotW = Γ.rotW⁻¹ * Γ.facePerm * Γ.rotW := (rfl)

/-- The face permutation after colour exchange is the conjugated old face permutation. -/
@[simp] theorem facePerm_swap01 : Γ.swap01.facePerm = Γ.rotW⁻¹ * Γ.facePerm * Γ.rotW := by
  rw [facePerm_def, rotB_swap01, rotW_swap01, facePerm_def]
  exact (by simp [mul_inv_rev, mul_assoc] :
    (Γ.rotB * Γ.rotW)⁻¹ = Γ.rotW⁻¹ * (Γ.rotW * Γ.rotB)⁻¹ * Γ.rotW)

/-- After white-face exchange the face permutation is the original white rotation. -/
@[simp] theorem facePerm_swap1Inf : Γ.swap1Inf.facePerm = Γ.rotW := by
  rw [facePerm_def, rotB_swap1Inf, rotW_swap1Inf, facePerm_def]
  exact (by simp [mul_inv_rev, mul_assoc] :
    ((Γ.rotW⁻¹ * (Γ.rotW * Γ.rotB)⁻¹ * Γ.rotW) * Γ.rotB)⁻¹ = Γ.rotW)

/-- The faces after white-face exchange correspond to the original white vertices. -/
noncomputable def swap1InfFaceEquivWhite : Γ.swap1Inf.Face ≃ Γ.W :=
  (Quotient.congrRight fun e e' ↦ by
    rw [facePerm_swap1Inf]
    exact Γ.whiteEnd_eq_whiteEnd_iff.symm).trans
      (Setoid.quotientKerEquivOfSurjective Γ.whiteEnd Γ.whiteEnd_surjective)

/-- The new face of an edge corresponds to its old white endpoint. -/
@[simp] theorem swap1InfFaceEquivWhite_mk (e : Γ.E) :
    Γ.swap1InfFaceEquivWhite (Quotient.mk _ e) = Γ.whiteEnd e := (rfl)

/-- Under any numbering of the unchanged edges, colour exchange is the triple exchange. -/
@[simp] theorem toPermutationTriple_swap01 {n : ℕ} (ν : Γ.E ≃ Fin n) :
    Γ.swap01.toPermutationTriple ν = (Γ.toPermutationTriple ν).swap01 := by
  apply PermutationTriple.ext_of_two
  · rw [toPermutationTriple_σ0 Γ.swap01 ν, PermutationTriple.swap01_σ0,
      toPermutationTriple_σ1, rotB_swap01]
    rfl
  · rw [toPermutationTriple_σ1 Γ.swap01 ν, PermutationTriple.swap01_σ1,
      toPermutationTriple_σ0, rotW_swap01]
    rfl

/-- Under any numbering, white-face exchange realizes the prescribed triple exchange. -/
@[simp] theorem toPermutationTriple_swap1Inf {n : ℕ} (ν : Γ.E ≃ Fin n) :
    Γ.swap1Inf.toPermutationTriple ν = (Γ.toPermutationTriple ν).swap1Inf := by
  apply PermutationTriple.ext_of_two
  · rw [toPermutationTriple_σ0 Γ.swap1Inf ν, PermutationTriple.swap1Inf_σ0,
      toPermutationTriple_σ0, rotB_swap1Inf]
    rfl
  · rw [toPermutationTriple_σ1 Γ.swap1Inf ν, rotW_swap1Inf, PermutationTriple.swap1Inf_σ1,
      toPermutationTriple_σ1, toPermutationTriple_σinf]
    -- `permCongrHom` is the same transport as `permCongr`, expressed as a group homomorphism.
    change ν.permCongrHom (Γ.rotW⁻¹ * Γ.facePerm * Γ.rotW) =
      (ν.permCongrHom Γ.rotW)⁻¹ * ν.permCongrHom Γ.facePerm * ν.permCongrHom Γ.rotW
    simp only [map_mul, map_inv]

/-- Colour exchange preserves connectedness, including the nonempty-edge condition. -/
@[simp] theorem isConnected_swap01_iff : Γ.swap01.IsConnected ↔ Γ.IsConnected := by
  let ν := Fintype.equivFin Γ.E
  rw [← isConnected_toPermutationTriple Γ.swap01 ν, toPermutationTriple_swap01,
    PermutationTriple.isConnected_swap01_iff, isConnected_toPermutationTriple]

/-- White-face exchange preserves connectedness. -/
@[simp] theorem isConnected_swap1Inf_iff : Γ.swap1Inf.IsConnected ↔ Γ.IsConnected := by
  let ν := Fintype.equivFin Γ.E
  rw [← isConnected_toPermutationTriple Γ.swap1Inf ν, toPermutationTriple_swap1Inf,
    PermutationTriple.isConnected_swap1Inf_iff, isConnected_toPermutationTriple]

/-- Colour exchange preserves the Euler characteristic. -/
@[simp] theorem eulerChar_swap01 : Γ.swap01.eulerChar = Γ.eulerChar := by
  let ν := Fintype.equivFin Γ.E
  rw [← eulerChar_toPermutationTriple Γ.swap01 ν, toPermutationTriple_swap01,
    PermutationTriple.eulerChar_swap01, eulerChar_toPermutationTriple]

/-- White-face exchange preserves the Euler characteristic. -/
@[simp] theorem eulerChar_swap1Inf : Γ.swap1Inf.eulerChar = Γ.eulerChar := by
  let ν := Fintype.equivFin Γ.E
  rw [← eulerChar_toPermutationTriple Γ.swap1Inf ν, toPermutationTriple_swap1Inf,
    PermutationTriple.eulerChar_swap1Inf, eulerChar_toPermutationTriple]

/-- Colour exchange preserves the combinatorial genus. -/
@[simp] theorem genus_swap01 : Γ.swap01.genus = Γ.genus := by
  rw [genus_def, genus_def, eulerChar_swap01]

/-- White-face exchange preserves the combinatorial genus. -/
@[simp] theorem genus_swap1Inf : Γ.swap1Inf.genus = Γ.genus := by
  rw [genus_def, genus_def, eulerChar_swap1Inf]

/-- Applying white-face exchange twice returns an isomorphic graph. Its edge equivalence
undoes the simultaneous conjugation by the black rotation on the numbered triple. -/
noncomputable def swap1InfSwap1InfIso : Γ.swap1Inf.swap1Inf.Iso Γ := by
  let ν := Fintype.equivFin Γ.E
  exact isoOfToPermutationTripleEq (ν := ν)
    (μ := ν.trans (Γ.toPermutationTriple ν).σ0) (by
      calc
        _ = (Γ.swap1Inf.toPermutationTriple ν).swap1Inf :=
          toPermutationTriple_swap1Inf Γ.swap1Inf ν
        _ = (Γ.toPermutationTriple ν).swap1Inf.swap1Inf :=
          congrArg PermutationTriple.swap1Inf (toPermutationTriple_swap1Inf Γ ν)
        _ = (Γ.toPermutationTriple ν).σ0 • Γ.toPermutationTriple ν :=
          PermutationTriple.swap1Inf_swap1Inf _
        _ = _ := (toPermutationTriple_trans Γ ν _).symm)

/-- The isomorphism after two white-face exchanges maps edges by the inverse black rotation. -/
@[simp] theorem swap1InfSwap1InfIso_edge_apply (e : Γ.E) :
    Γ.swap1InfSwap1InfIso.edge e = Γ.rotB⁻¹ e := by
  unfold swap1InfSwap1InfIso
  dsimp only
  refine (congrArg (fun φ : Γ.swap1Inf.swap1Inf.E ≃ Γ.E ↦ φ e)
    (isoOfToPermutationTripleEq_edge (Γ := Γ.swap1Inf.swap1Inf) (Δ := Γ) _)).trans ?_
  rw [toPermutationTriple_σ0]
  -- The source carrier reduces to `Γ.E`, but transport lemmas otherwise infer it as the
  -- unreduced field `Γ.swap1Inf.swap1Inf.E`; state the calculation on the original carrier.
  exact (by simp [Equiv.permCongr_def] :
    ((Fintype.equivFin Γ.E).trans
      ((Fintype.equivFin Γ.E).trans ((Fintype.equivFin Γ.E).permCongr Γ.rotB)).symm) e =
        Γ.rotB⁻¹ e)

/-- The isomorphism after two white-face exchanges fixes every black vertex. -/
@[simp] theorem swap1InfSwap1InfIso_black_apply (b : Γ.B) :
    Γ.swap1InfSwap1InfIso.black b = b := by
  obtain ⟨e, rfl⟩ := Γ.blackEnd_surjective b
  have h := Γ.swap1InfSwap1InfIso.map_blackEnd e
  -- Express endpoint compatibility on the original edge carrier `Γ.E`.
  change Γ.blackEnd (Γ.swap1InfSwap1InfIso.edge e) =
    Γ.swap1InfSwap1InfIso.black (Γ.blackEnd e) at h
  rw [swap1InfSwap1InfIso_edge_apply] at h
  exact h.symm.trans (by
    simpa only [Perm.inv_def, apply_symm_apply] using (Γ.blackEnd_rotB (Γ.rotB⁻¹ e)).symm)

/-- The isomorphism after two white-face exchanges sends the new white vertex represented
by an edge to its original white endpoint. -/
@[simp] theorem swap1InfSwap1InfIso_white_apply (e : Γ.E) :
    Γ.swap1InfSwap1InfIso.white
        (Quotient.mk (SameCycle.setoid Γ.swap1Inf.facePerm) e) = Γ.whiteEnd e := by
  have h := Γ.swap1InfSwap1InfIso.map_whiteEnd (Γ.rotB (Γ.rotW e))
  -- Read the exposed source endpoint on `Γ.E` to simplify its quotient representative.
  change Γ.whiteEnd (Γ.swap1InfSwap1InfIso.edge (Γ.rotB (Γ.rotW e))) =
    Γ.swap1InfSwap1InfIso.white
      (Quotient.mk _ ((Γ.rotW⁻¹ * Γ.facePerm * Γ.rotW) (Γ.rotB (Γ.rotW e)))) at h
  simpa only [swap1InfSwap1InfIso_edge_apply,
    facePerm_def, mul_inv_rev, Perm.mul_apply, Perm.inv_def, symm_apply_apply,
    whiteEnd_rotW] using h.symm

variable {n : ℕ}

/-- Branch-point permutations act on graph isomorphism classes on the right, written as a
left action of the opposite group. Transport along `isoClassEquiv` retains the existing
product-one convention and all six triple operations. -/
noncomputable instance : MulAction (Perm (Fin 3))ᵐᵒᵖ (Quotient (isoSetoid.{u} n)) :=
  (isoClassEquiv n).mulAction (Perm (Fin 3))ᵐᵒᵖ

/-- The correspondence between graph and triple isomorphism classes respects branch-point
exchange, with contravariant composition expressed by the opposite group. -/
@[simp] theorem isoClassEquiv_smul (ρ : (Perm (Fin 3))ᵐᵒᵖ)
    (c : Quotient (isoSetoid.{u} n)) :
    isoClassEquiv n (ρ • c) = ρ • isoClassEquiv n c := by
  exact (isoClassEquiv n).apply_symm_apply _

/-- On a representative, the transposition of `0` and `1` exchanges the two colours. -/
@[simp] theorem op_swap_zero_one_smul_mk (h : Fintype.card Γ.E = n) :
    MulOpposite.op (Equiv.swap (0 : Fin 3) 1) •
        (⟦⟨Γ, h⟩⟧ : Quotient (isoSetoid.{u} n)) =
      ⟦⟨Γ.swap01, h⟩⟧ := by
  let ν := Fintype.equivFinOfCardEq h
  apply (isoClassEquiv n).injective
  rw [isoClassEquiv_smul, isoClassEquiv_mk _ ν, PermutationTriple.IsoClass.op_smul_mk,
    PermutationTriple.reindexBranchPoints_swap_zero_one, isoClassEquiv_mk _ ν,
    toPermutationTriple_swap01]

/-- On a representative, the transposition of `1` and `∞` exchanges white vertices and faces. -/
@[simp] theorem op_swap_one_two_smul_mk (h : Fintype.card Γ.E = n) :
    MulOpposite.op (Equiv.swap (1 : Fin 3) 2) •
        (⟦⟨Γ, h⟩⟧ : Quotient (isoSetoid.{u} n)) =
      ⟦⟨Γ.swap1Inf, h⟩⟧ := by
  let ν := Fintype.equivFinOfCardEq h
  apply (isoClassEquiv n).injective
  rw [isoClassEquiv_smul, isoClassEquiv_mk _ ν, PermutationTriple.IsoClass.op_smul_mk,
    PermutationTriple.reindexBranchPoints_swap_one_two, isoClassEquiv_mk _ ν,
    toPermutationTriple_swap1Inf]

end BipartiteRibbonGraph

end TauCeti
