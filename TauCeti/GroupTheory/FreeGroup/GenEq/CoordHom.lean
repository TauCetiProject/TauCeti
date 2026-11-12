/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.CancellationFamily

/-!
# The homomorphism from the coordinate group of a system to that of a generalised equation

Let `S` be a finite system of equations and inequations over `F(A)` in finitely many variables `X`
and `T` a partition table of its words, with generalised equation `Ω_T` and word maps `P_x` for
`x ∈ X`. In every group `H` over `F(A)` the word maps send the solutions of the system `Ω_T*` to
solutions of the equations of `S`. Hence `x ↦ P_x` induces a homomorphism over `F(A)` of
coordinate groups

`π_Ω : F_{R(S)} → F_{R(Ω_T)}`,

where `F_{R(S)}` is the coordinate group of the equations of `S` (the inequations do not enter
its radical). Composing a homomorphism `F_{R(Ω_T)} → H` over `F(A)` with `π_Ω` corresponds, on
points, to applying the word maps. For a solution `U` of `Ω_T` in `F(A)` the composite of `π_Ω`
with the homomorphism of `U` is the homomorphism of the point `P(U)`, a solution of the equations
of `S`.

## Main definitions

* `TauCeti.EqIneqSystem.eqSet`: the equations of a system as elements of `F(A)[X]`.
* `TauCeti.EqIneqSystem.coordHom`: the homomorphism `π_Ω`.

## Main results

* `TauCeti.EqIneqSystem.mapsToWordMap_wordMap`: the word maps send solutions of `Ω_T*` to
  solutions of the equations of the system.
* `TauCeti.EqIneqSystem.homEquiv_comp_coordHom`: composing a homomorphism `F_{R(Ω_T)} → H` with
  `π_Ω` corresponds, on points, to applying the word maps.
* `TauCeti.EqIneqSystem.homEquiv_toHom_comp_coordHom`: the composite of `π_Ω` with the
  homomorphism of a solution `U` is the homomorphism of `P(U)`.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.4 (coordinate groups) and §4.2, Lemma 14(2), (4) and Corollary 8.
-/

public section

namespace TauCeti

namespace EqIneqSystem

open GenEq GroupAlgGeom
open FreeGroup (substituteVars)

variable {X Z A : Type*}

/-- The equations of a system as elements of `F(A)[X]`: a system of equations of algebraic
geometry over `F(A)`. -/
def eqSet (S : EqIneqSystem X A) : Set (GX (FreeGroup A) X) :=
  toGX X FreeGroup.of '' {e | e ∈ S.eqs}

/-- The elements of the set of equations of a system are the images in `F(A)[X]` of its
equations. -/
theorem mem_eqSet_iff {S : EqIneqSystem X A} {w : GX (FreeGroup A) X} :
    w ∈ S.eqSet ↔ ∃ e ∈ S.eqs, toGX X FreeGroup.of e = w :=
  Iff.rfl

/-- The solutions of the equations of a system in a group over `F(A)` are the points of its set
of equations. -/
theorem mem_V_eqSet_iff {S : EqIneqSystem X A} {H : Type*} [Group H] {ι : FreeGroup A →* H}
    {v : X → H} : v ∈ V ι S.eqSet ↔ ∀ e ∈ S.eqs, eval v (ι ∘ FreeGroup.of) e = 1 := by
  simp [eqSet, mem_V]

variable [Finite X] [DecidableEq X] [DecidableEq A] {S : EqIneqSystem X A}
  {T : Occurrence S.toWords → List ((Z ⊕ A) × Bool)} {H : Type*} [Group H]

/-- **Kharlampovich–Myasnikov, Lemma 14(4).** In every group over `F(A)`, the word maps of a
partition table of the words of a system map the algebraic set of `Ω_T*` into the algebraic set of
the equations of the system. -/
theorem mapsToWordMap_wordMap (ι : FreeGroup A →* H) (hT : IsPartitionTable S.toWords T) :
    CoordGroup.MapsToWordMap ι (S.genEq T).toSystem S.eqSet
      fun x => toGX _ FreeGroup.of (FreeGroup.mk (S.wordMap T x)) :=
  (CoordGroup.mapsToWordMap_iff ..).2 fun v hv => mem_V_eqSet_iff.2 fun _ he => by
    convert eval_eq_one_of_mem_V hT hv he using 3
    exact funext fun x => by rw [GroupAlgGeom.wordMap_apply, eval_toGX]

/-- **Kharlampovich–Myasnikov, Lemma 14(2).** The homomorphism `π_Ω : F_{R(S)} → F_{R(Ω_T)}` over
`F(A)` induced by the word maps `x ↦ P_x` of a partition table of the words of a system, the
coordinate groups being taken with respect to a group `H` over `F(A)`. -/
noncomputable def coordHom (ι : FreeGroup A →* H) (hT : IsPartitionTable S.toWords T) :
    GHom (CoordGroup.coeff ι S.eqSet) (CoordGroup.coeff ι (S.genEq T).toSystem) :=
  CoordGroup.homOfMapsToWordMap ι _ _ _ (mapsToWordMap_wordMap ι hT)

/-- The homomorphism `π_Ω` sends the class of a word to the class of its image under the word
maps. -/
@[simp]
theorem coordHom_mk (ι : FreeGroup A →* H) (hT : IsPartitionTable S.toWords T)
    (w : GX (FreeGroup A) X) : coordHom ι hT (w : CoordGroup ι S.eqSet) =
      (GroupAlgGeom.eval (Monoid.Coprod.inl : FreeGroup A →* GX (FreeGroup A) _)
        (fun x => toGX _ FreeGroup.of (FreeGroup.mk (S.wordMap T x))) w :
        CoordGroup ι (S.genEq T).toSystem) :=
  CoordGroup.homOfMapsToWordMap_mk ..

/-- Composing a homomorphism `F_{R(Ω_T)} → H` over `F(A)` with `π_Ω` corresponds, on points, to
applying the word maps. -/
theorem homEquiv_comp_coordHom (ι : FreeGroup A →* H) (hT : IsPartitionTable S.toWords T)
    (φ : GHom (CoordGroup.coeff ι (S.genEq T).toSystem) ι) (x : X) :
    (CoordGroup.homEquiv ι S.eqSet (φ.comp (coordHom ι hT)) : X → H) x =
      eval (CoordGroup.homEquiv ι (S.genEq T).toSystem φ : Fin (S.genEq T).numItems → H)
        (ι ∘ FreeGroup.of) (FreeGroup.mk (S.wordMap T x)) := by
  rw [← eval_toGX, CoordGroup.eval_homEquiv]
  simp

/-- For a solution `U` of the generalised equation of a partition table of the words of a system,
the composite of `π_Ω` with the homomorphism `F_{R(Ω_T)} → F(A)` of `U` is the homomorphism
`F_{R(S)} → F(A)` of the point `x ↦ P_x(U)`. When `P(U)` is a given solution `W`, this is the
commutative triangle of Kharlampovich–Myasnikov, Corollary 8. -/
theorem homEquiv_toHom_comp_coordHom (hT : IsPartitionTable S.toWords T) (U : (S.genEq T).Solution)
    (x : X) : (CoordGroup.homEquiv (MonoidHom.id (FreeGroup A)) S.eqSet
      (U.toHom.comp (coordHom (MonoidHom.id (FreeGroup A)) hT)) : X → FreeGroup A) x =
      FreeGroup.mk (substituteVars U.word (S.wordMap T x)) := by
  simp [Solution.eval_point_mk]

end EqIneqSystem

end TauCeti
