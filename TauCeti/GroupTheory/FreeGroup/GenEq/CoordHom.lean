/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.EqIneqSystem.AlgebraicSet
public import TauCeti.GroupTheory.FreeGroup.GenEq.CancellationFamily

/-!
# The homomorphism from the coordinate group of a system to that of a generalised equation

Let `S` be a finite system of equations and inequations over `F(A)` in finitely many variables `X`
and `T` a partition table of its words, with generalised equation `Ω_T` and word maps `P_x` for
`x ∈ X`. In every group `H` over `F(A)` the word maps send the solutions of the system `Ω_T*` to
solutions of the equations of `S`. Hence `x ↦ P_x` induces a homomorphism over `F(A)` of
coordinate groups

`π_Ω : F_{R(S)} → F_{R(Ω_T)}`,

where `F_{R(S)}` is the coordinate group of the equations of `S` (`TauCeti.EqIneqSystem.eqSet`;
the inequations do not enter its radical). Composing a homomorphism `F_{R(Ω_T)} → H` over `F(A)`
with `π_Ω` corresponds, on points, to applying the word maps: evaluation at a solution `v` of
`Ω_T*` becomes evaluation at `P(v)`. For a solution `U` of `Ω_T` in `F(A)` the composite of `π_Ω`
with the homomorphism of `U` is the homomorphism of the point `P(U)`, a solution of the equations
of `S`.

## Main definitions

* `TauCeti.EqIneqSystem.coordHom`: the homomorphism `π_Ω`.

## Main results

* `TauCeti.EqIneqSystem.eval_wordMap_mem_V_eqSet`, `TauCeti.EqIneqSystem.mapsToWordMap_wordMap`:
  the word maps send solutions of `Ω_T*` to solutions of the equations of the system.
* `TauCeti.EqIneqSystem.evalGHom_comp_coordHom`, `TauCeti.EqIneqSystem.homEquiv_comp_coordHom`:
  composing a homomorphism `F_{R(Ω_T)} → H` with `π_Ω` corresponds, on points, to applying the
  word maps.
* `TauCeti.EqIneqSystem.toHom_comp_coordHom`: the composite of `π_Ω` with the homomorphism of a
  solution `U` is the homomorphism of `P(U)`.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.4 (coordinate groups) and §4.2, Lemma 14(2), (4) and Corollary 8.
-/

public section

namespace TauCeti

namespace EqIneqSystem

open GenEq GroupAlgGeom
open FreeGroup (substituteVars)

variable {X Z A : Type*} [Finite X] [DecidableEq X] [DecidableEq A] {S : EqIneqSystem X A}
  {T : Occurrence S.toWords → List ((Z ⊕ A) × Bool)} {H : Type*} [Group H]

/-- **Kharlampovich–Myasnikov, Lemma 14(4).** If `v` is a solution of `Ω_T*` in a group `H` over
`F(A)`, for a partition table `T` of the words of a system, then `x ↦ P_x(v)` is a solution of
the equations of the system in `H`. -/
theorem eval_wordMap_mem_V_eqSet {ι : FreeGroup A →* H} (hT : IsPartitionTable S.toWords T)
    {v : Fin (S.genEq T).numItems → H} (hv : v ∈ V ι (S.genEq T).toSystem) :
    (fun x => eval v (ι ∘ FreeGroup.of) (FreeGroup.mk (S.wordMap T x))) ∈ V ι S.eqSet :=
  mem_V_eqSet_iff.2 fun _ => eval_eq_one_of_mem_V hT hv

/-- For a solution `U` of the generalised equation of a partition table of the words of a system,
`x ↦ P_x(U)` is a solution of the equations of the system in `F(A)`. -/
theorem mk_substituteVars_wordMap_mem_V_eqSet (hT : IsPartitionTable S.toWords T)
    (U : (S.genEq T).Solution) :
    (fun x => FreeGroup.mk (substituteVars U.word (S.wordMap T x))) ∈
      V (MonoidHom.id (FreeGroup A)) S.eqSet := by
  simpa using eval_wordMap_mem_V_eqSet hT U.point_mem_V

/-- **Kharlampovich–Myasnikov, Lemma 14(4).** In every group over `F(A)`, the word maps of a
partition table of the words of a system map the algebraic set of `Ω_T*` into the algebraic set of
the equations of the system. -/
theorem mapsToWordMap_wordMap (ι : FreeGroup A →* H) (hT : IsPartitionTable S.toWords T) :
    CoordGroup.MapsToWordMap ι (S.genEq T).toSystem S.eqSet
      fun x => toGX _ FreeGroup.of (FreeGroup.mk (S.wordMap T x)) :=
  (CoordGroup.mapsToWordMap_iff ..).2 fun v hv => by
    convert eval_wordMap_mem_V_eqSet hT hv using 1
    exact funext fun x => by rw [GroupAlgGeom.wordMap_apply, eval_toGX]

/-- **Kharlampovich–Myasnikov, Lemma 14(2).** The homomorphism `π_Ω : F_{R(S)} → F_{R(Ω_T)}` over
`F(A)` induced by the word maps `x ↦ P_x` of a partition table of the words of a system, the
coordinate groups being taken with respect to a group `H` over `F(A)`. -/
noncomputable def coordHom (ι : FreeGroup A →* H) (hT : IsPartitionTable S.toWords T) :
    GHom (CoordGroup.coeff ι S.eqSet) (CoordGroup.coeff ι (S.genEq T).toSystem) :=
  CoordGroup.homOfMapsToWordMap ι _ _ _ (mapsToWordMap_wordMap ι hT)

theorem coordHom_def (ι : FreeGroup A →* H) (hT : IsPartitionTable S.toWords T) :
    coordHom ι hT = CoordGroup.homOfMapsToWordMap ι (S.genEq T).toSystem S.eqSet
      (fun x => toGX _ FreeGroup.of (FreeGroup.mk (S.wordMap T x))) (mapsToWordMap_wordMap ι hT) :=
  (rfl)

/-- The homomorphism `π_Ω` sends the class of a word to the class of its image under the word
maps. -/
@[simp]
theorem coordHom_mk (ι : FreeGroup A →* H) (hT : IsPartitionTable S.toWords T)
    (w : GX (FreeGroup A) X) : coordHom ι hT (w : CoordGroup ι S.eqSet) =
      (GroupAlgGeom.eval (Monoid.Coprod.inl : FreeGroup A →* GX (FreeGroup A) _)
        (fun x => toGX _ FreeGroup.of (FreeGroup.mk (S.wordMap T x))) w :
        CoordGroup ι (S.genEq T).toSystem) :=
  CoordGroup.homOfMapsToWordMap_mk ..

/-- Evaluation at a solution `v` of `Ω_T*` in a group over `F(A)`, composed with `π_Ω`, is
evaluation at the solution `x ↦ P_x(v)` of the equations of the system. -/
@[simp]
theorem evalGHom_comp_coordHom {ι : FreeGroup A →* H} (hT : IsPartitionTable S.toWords T)
    {v : Fin (S.genEq T).numItems → H} (hv : v ∈ V ι (S.genEq T).toSystem) :
    (CoordGroup.evalGHom v hv).comp (coordHom ι hT) =
      CoordGroup.evalGHom _ (eval_wordMap_mem_V_eqSet hT hv) :=
  CoordGroup.gHom_ext fun _ => by simp

/-- Composing a homomorphism `F_{R(Ω_T)} → H` over `F(A)` with `π_Ω` corresponds, on points, to
applying the word maps. -/
theorem homEquiv_comp_coordHom (ι : FreeGroup A →* H) (hT : IsPartitionTable S.toWords T)
    (φ : GHom (CoordGroup.coeff ι (S.genEq T).toSystem) ι) :
    (CoordGroup.homEquiv ι S.eqSet (φ.comp (coordHom ι hT)) : X → H) = fun x =>
      eval (CoordGroup.homEquiv ι (S.genEq T).toSystem φ : Fin (S.genEq T).numItems → H)
        (ι ∘ FreeGroup.of) (FreeGroup.mk (S.wordMap T x)) := by
  funext x
  rw [← eval_toGX, CoordGroup.eval_homEquiv]
  simp

/-- For a solution `U` of the generalised equation of a partition table of the words of a system,
the composite of `π_Ω` with the homomorphism `F_{R(Ω_T)} → F(A)` of `U` is the homomorphism
`F_{R(S)} → F(A)` of the point `x ↦ P_x(U)`. When `P(U)` is a given solution `W`, this is the
commutative triangle of Kharlampovich–Myasnikov, Corollary 8. -/
@[simp]
theorem toHom_comp_coordHom (hT : IsPartitionTable S.toWords T) (U : (S.genEq T).Solution) :
    U.toHom.comp (coordHom (MonoidHom.id (FreeGroup A)) hT) =
      CoordGroup.evalGHom _ (mk_substituteVars_wordMap_mem_V_eqSet hT U) :=
  CoordGroup.gHom_ext fun _ => by simp

/-- For a solution `U` of the generalised equation of a partition table of the words of a system,
the composite of `π_Ω` with the homomorphism `F_{R(Ω_T)} → F(A)` of `U` corresponds to the point
`x ↦ P_x(U)`. -/
theorem homEquiv_toHom_comp_coordHom (hT : IsPartitionTable S.toWords T)
    (U : (S.genEq T).Solution) :
    (CoordGroup.homEquiv (MonoidHom.id (FreeGroup A)) S.eqSet
      (U.toHom.comp (coordHom (MonoidHom.id (FreeGroup A)) hT)) : X → FreeGroup A) =
      fun x => FreeGroup.mk (substituteVars U.word (S.wordMap T x)) := by
  funext x
  simp

end EqIneqSystem

end TauCeti
