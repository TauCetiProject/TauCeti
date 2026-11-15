/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.KanComplex.HomotopyGroup
public import TauCeti.AlgebraicTopology.SimplicialSet.ULift

/-!
# Homotopy groups and universe lifts

Universe lifting does not change the positive homotopy groups of a Kan complex.
The comparison is induced by the bijection on pointed simplices and preserves products.
This allows mapping spaces in a large universe to be compared with complexes of modules
in a smaller universe.

The proof uses the descriptions of homotopies and products by faces of a simplex;
these descriptions are unchanged by `ULift`.

## References

* J. P. May, *Simplicial Objects in Algebraic Topology*, Chapter I, §§3–4.
-/

public noncomputable section

open CategoryTheory Simplicial

universe u v

namespace SSet

variable {X : SSet.{u}} {x : (uliftFunctor.{v}.obj X) _⦋0⦌} {n : ℕ}

/-- Pointed simplices of a universe lift are pointed simplices of the original
simplicial set. -/
def PtSimplex.uliftEquiv :
    (uliftFunctor.{v}.obj X).PtSimplex n x ≃ X.PtSimplex n x.down where
  toFun p :=
    { map := uliftFunctorHomEquiv X ⦋n⦌ p.map
      comm := by
        obtain _ | n := n
        · ext
        · apply boundary.hom_ext
          intro i
          simp only [← Category.assoc, boundary.ι_ι, const_comp, comp_const]
          exact (uliftFunctorHomEquiv_δ_comp i p.map).symm.trans
            ((congrArg (uliftFunctorHomEquiv X ⦋n⦌) (p.δ_map i)).trans
              (uliftFunctorHomEquiv_const x)) }
  invFun p :=
    { map := (uliftFunctorHomEquiv X ⦋n⦌).symm p.map
      comm := by
        obtain _ | n := n
        · ext
        · apply boundary.hom_ext
          intro i
          simp only [← Category.assoc, boundary.ι_ι, const_comp, comp_const]
          apply (uliftFunctorHomEquiv X ⦋n⦌).injective
          erw [uliftFunctorHomEquiv_δ_comp, Equiv.apply_symm_apply, p.δ_map,
            uliftFunctorHomEquiv_const]
          rfl }
  left_inv p := by ext; simp
  right_inv p := by ext; simp

@[simp]
lemma PtSimplex.uliftEquiv_map (p : (uliftFunctor.{v}.obj X).PtSimplex n x) :
    (PtSimplex.uliftEquiv p).map = uliftFunctorHomEquiv X ⦋n⦌ p.map := (rfl)

@[simp]
lemma PtSimplex.uliftEquiv_symm_map (p : X.PtSimplex n x.down) :
    (PtSimplex.uliftEquiv.symm p).map =
      (uliftFunctorHomEquiv.{u, v} X ⦋n⦌).symm p.map := (rfl)

/-- The face description of a homotopy is preserved when lowering the universe. -/
def PtSimplex.RelStruct.unlift
    {p q : (uliftFunctor.{v}.obj X).PtSimplex n x} {i : Fin (n + 1)}
    (h : p.RelStruct q i) : (PtSimplex.uliftEquiv p).RelStruct (PtSimplex.uliftEquiv q) i where
  map := uliftFunctorHomEquiv X ⦋n + 1⦌ h.map
  δ_castSucc_map := by rw [← uliftFunctorHomEquiv_δ_comp, h.δ_castSucc_map]; rfl
  δ_succ_map := by rw [← uliftFunctorHomEquiv_δ_comp, h.δ_succ_map]; rfl
  δ_map_of_lt j hj := by
    rw [← uliftFunctorHomEquiv_δ_comp, h.δ_map_of_lt j hj, uliftFunctorHomEquiv_const]
  δ_map_of_gt j hj := by
    rw [← uliftFunctorHomEquiv_δ_comp, h.δ_map_of_gt j hj, uliftFunctorHomEquiv_const]

@[simp]
lemma PtSimplex.RelStruct.unlift_map
    {p q : (uliftFunctor.{v}.obj X).PtSimplex n x} {i : Fin (n + 1)}
    (h : p.RelStruct q i) :
    h.unlift.map = uliftFunctorHomEquiv X ⦋n + 1⦌ h.map := (rfl)

/-- The face description of a homotopy is preserved when raising the universe. -/
def PtSimplex.RelStruct.ulift {p q : X.PtSimplex n x.down} {i : Fin (n + 1)}
    (h : p.RelStruct q i) :
    (PtSimplex.uliftEquiv.{u, v}.symm p).RelStruct (PtSimplex.uliftEquiv.symm q) i where
  map := (uliftFunctorHomEquiv X ⦋n + 1⦌).symm h.map
  δ_castSucc_map := by
    apply (uliftFunctorHomEquiv X ⦋n⦌).injective
    simp [uliftFunctorHomEquiv_δ_comp]
  δ_succ_map := by
    apply (uliftFunctorHomEquiv X ⦋n⦌).injective
    simp [uliftFunctorHomEquiv_δ_comp]
  δ_map_of_lt j hj := by
    apply (uliftFunctorHomEquiv X ⦋n⦌).injective
    simp [uliftFunctorHomEquiv_δ_comp, h.δ_map_of_lt j hj]
  δ_map_of_gt j hj := by
    apply (uliftFunctorHomEquiv X ⦋n⦌).injective
    simp [uliftFunctorHomEquiv_δ_comp, h.δ_map_of_gt j hj]

@[simp]
lemma PtSimplex.RelStruct.ulift_map {p q : X.PtSimplex n x.down} {i : Fin (n + 1)}
    (h : p.RelStruct q i) :
    (h.ulift (x := x)).map = (uliftFunctorHomEquiv X ⦋n + 1⦌).symm h.map := (rfl)

/-- The face description of a product is preserved when lowering the universe. -/
def PtSimplex.MulStruct.unlift
    {p q pq : (uliftFunctor.{v}.obj X).PtSimplex n x} {i : Fin n}
    (h : PtSimplex.MulStruct p q pq i) :
    PtSimplex.MulStruct (PtSimplex.uliftEquiv p) (PtSimplex.uliftEquiv q)
      (PtSimplex.uliftEquiv pq) i where
  map := uliftFunctorHomEquiv X ⦋n + 1⦌ h.map
  δ_castSucc_castSucc_map := by
    rw [← uliftFunctorHomEquiv_δ_comp, h.δ_castSucc_castSucc_map]; rfl
  δ_succ_castSucc_map := by
    rw [← uliftFunctorHomEquiv_δ_comp, h.δ_succ_castSucc_map]; rfl
  δ_succ_succ_map := by rw [← uliftFunctorHomEquiv_δ_comp, h.δ_succ_succ_map]; rfl
  δ_map_of_lt j hj := by
    rw [← uliftFunctorHomEquiv_δ_comp, h.δ_map_of_lt j hj, uliftFunctorHomEquiv_const]
  δ_map_of_gt j hj := by
    rw [← uliftFunctorHomEquiv_δ_comp, h.δ_map_of_gt j hj, uliftFunctorHomEquiv_const]

@[simp]
lemma PtSimplex.MulStruct.unlift_map
    {p q pq : (uliftFunctor.{v}.obj X).PtSimplex n x} {i : Fin n}
    (h : PtSimplex.MulStruct p q pq i) :
    h.unlift.map = uliftFunctorHomEquiv X ⦋n + 1⦌ h.map := (rfl)

namespace KanComplex.π

variable [KanComplex X]

/-- Positive homotopy groups are unchanged by universe lifting. -/
def uliftEquiv (n : ℕ) (x : (uliftFunctor.{v}.obj X) _⦋0⦌) :
    π (n + 1) (uliftFunctor.{v}.obj X) x ≃ π (n + 1) X x.down where
  toFun := lift (fun p ↦ mk (PtSimplex.uliftEquiv p))
    (fun _ _ h ↦ mk_eq_mk_iff.2 ⟨h.relStruct₀.unlift⟩)
  invFun := lift (fun p ↦ mk (PtSimplex.uliftEquiv.symm p))
    (fun _ _ h ↦ mk_eq_mk_iff.2 ⟨h.relStruct₀.ulift⟩)
  left_inv a := by
    induction a with | mk p =>
      erw [lift_mk, lift_mk, Equiv.symm_apply_apply]
  right_inv a := by
    induction a with | mk p =>
      erw [lift_mk, lift_mk, Equiv.apply_symm_apply]

@[simp]
lemma uliftEquiv_mk (p : (uliftFunctor.{v}.obj X).PtSimplex (n + 1) x) :
    uliftEquiv n x (mk p) = mk (PtSimplex.uliftEquiv p) := by
  exact lift_mk _ _ _

@[simp]
lemma uliftEquiv_symm_mk (p : X.PtSimplex (n + 1) x.down) :
    (uliftEquiv.{u, v} n x).symm (mk p) = mk (PtSimplex.uliftEquiv.symm p) := by
  exact lift_mk _ _ _

/-- The universe comparison preserves the group operation, not just homotopy classes. -/
def uliftMulEquiv (n : ℕ) (x : (uliftFunctor.{v}.obj X) _⦋0⦌) :
    π (n + 1) (uliftFunctor.{v}.obj X) x ≃* π (n + 1) X x.down where
  __ := uliftEquiv n x
  map_mul' a b := by
    induction a with | mk p
    induction b with | mk q
    obtain ⟨pq, ⟨h⟩⟩ := PtSimplex.MulStruct.nonempty p q (Fin.last n)
    rw [mul_mk_eq_iff.2 ⟨h⟩]
    simpa only [uliftEquiv, lift_mk] using (mul_mk_eq_iff.2 ⟨h.unlift⟩).symm

@[simp]
lemma uliftMulEquiv_apply (a : π (n + 1) (uliftFunctor.{v}.obj X) x) :
    uliftMulEquiv n x a = uliftEquiv n x a := (rfl)

@[simp]
lemma uliftMulEquiv_symm_apply (a : π (n + 1) X x.down) :
    (uliftMulEquiv.{u, v} n x).symm a = (uliftEquiv n x).symm a := (rfl)

end KanComplex.π

end SSet
