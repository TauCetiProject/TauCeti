/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: `IsSemisimpleRing` and `IsReduced` are the two clauses of the definition below, and
-- Artin--Wedderburn supplies the shape of the main equivalence.
public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
-- Non-public: used only inside proofs.  A reduced matrix ring has at most one index, a
-- one-by-one matrix ring collapses to its base ring, and an equivalence of rings carries the
-- Jacobson radical onto the Jacobson radical and so descends to the quotients.
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.Nilpotent.Reduced

/-!
# Basic algebras

A ring `A` is **basic** when its quotient by the Jacobson radical, `A ⧸ Ring.jacobson A`, is a
finite product of division rings.  The definition states this as the quotient being *semisimple* and
*reduced*, which says the same thing (`TauCeti.isBasic_iff_pi_divisionRing`): Artin--Wedderburn
writes a semisimple ring as a finite product of matrix algebras over division rings, one block for
each simple module, and a matrix algebra of size at least two is never reduced, the matrix unit
`Eᵢⱼ` with `i ≠ j` being nonzero and square-zero (`Matrix.isReduced_iff_subsingleton`).  So over
a semisimple ring reducedness says exactly that **every block has size one**, that is, that the
ring is a product of division rings rather than of matrix algebras over them; equivalently, that no
indecomposable projective is repeated in a decomposition of the regular module.

That reformulation is the main result.  Its ring-level form,
`TauCeti.isReduced_iff_pi_divisionRing`, holds for an arbitrary semisimple ring and mentions no
algebra structure.

The condition is aimed at a finite-dimensional algebra over a field, where the quotient by the
radical is semisimple because the algebra is Artinian.  Whenever that quotient is semisimple -- in
particular for every Artinian, or more generally semiprimary, ring -- the semisimplicity clause is
automatic and basicness is reducedness alone (`TauCeti.isBasic_iff_isReduced`).  Outside that
setting the clause has to be asked for: `ℤ` has zero Jacobson radical and is reduced, but is not a
product of division rings and is not a basic ring.

Basicness is the normalization step of Morita theory: every finite-dimensional algebra is Morita
equivalent to a basic one, obtained by keeping one indecomposable projective per simple module.
That reduction is `TauCeti.IsSemiperfectRing.exists_isBasic_isMoritaEquivalent`, in
`TauCeti.RingTheory.Morita.BasicAlgebra`.  The model example is on the quiver side: the path
algebra of a finite acyclic quiver is basic (`TauCeti.PathAlgebra.isBasic`).

## Main definitions

* `TauCeti.IsBasic`: a ring whose quotient by the Jacobson radical is semisimple and reduced.

## Main results

* `TauCeti.isBasic_def`: unfolding lemma for `TauCeti.IsBasic`.
* `RingEquiv.isBasic_iff`: basicness is invariant under a ring equivalence.
* `TauCeti.isReduced_iff_pi_divisionRing`: a semisimple ring is reduced if and only if it is a
  finite product of division rings.
* `TauCeti.isBasic_iff_pi_divisionRing`: a ring is basic if and only if its quotient by the
  Jacobson radical is a finite product of division rings.
* `TauCeti.isBasic_iff_isReduced`: a ring whose quotient by the Jacobson radical is semisimple is
  basic if and only if that quotient is reduced.
* `TauCeti.isBasic_of_commRing`: a commutative ring whose quotient by the Jacobson radical is
  semisimple is basic.
* `TauCeti.IsBasic.exists_completeOrthogonalIdempotents`: a finite-dimensional basic algebra over
  an algebraically closed field has a complete family of nonzero orthogonal idempotents whose
  classes span the quotient by the Jacobson radical.

## Implementation notes

Mathlib's `Matrix.uniqueRingEquiv` fixes the `Fintype` structure on the one-element index type to
the one manufactured from `Unique`, so its type does not match a matrix ring formed with a `Fintype`
structure coming from elsewhere -- the two are equal but not definitionally so, and the
multiplication of a matrix ring depends on which one is used.  The proof of
`TauCeti.isReduced_iff_pi_divisionRing` therefore rewrites the `Fin.fintype` structure of a
one-element Artin--Wedderburn block along `Subsingleton.elim` first.

`TauCeti.IsBasic` keeps its body private; `TauCeti.isBasic_def` is the unfolding lemma through which
importing modules use the definition.

`TauCeti.IsBasic` takes only the ring, with no base field and no finite-dimensionality over it:
neither appears in the condition.  Dropping them is what puts semisimplicity of the quotient into
the definition: over a finite-dimensional algebra it is automatic, but for a general ring
reducedness alone is strictly weaker than being a product of division rings.  The formulation as
reducedness of the quotient is `TauCeti.isBasic_iff_isReduced`, which asks only for that
semisimplicity, as an instance.  A finite-dimensional algebra over a field supplies it through
`IsArtinianRing.of_finite` and the instances making an Artinian ring semiprimary and the quotient
of a semiprimary ring by its radical semisimple.

## References

See I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
Algebras I*, CUP (2006), Ch. I.6. The lifted idempotents of a basic algebra over an
algebraically closed field are the vertices of its bound-quiver presentation, ibid. Ch. II.3.
-/

public section

namespace TauCeti

universe u v w

/-! ### Reduced semisimple rings are products of division rings -/

/-- **A semisimple ring is reduced exactly when it is a finite product of division rings.**  Read
through Artin--Wedderburn, reducedness says that every block `Matₙᵢ(Dᵢ)` has `nᵢ = 1`, a larger
matrix block carrying a nonzero square-zero matrix unit; the converse is immediate, a division ring
having no nonzero nilpotent element. -/
theorem isReduced_iff_pi_divisionRing (R : Type u) [Ring R] [IsSemisimpleRing R] :
    IsReduced R ↔ ∃ (n : ℕ) (D : Fin n → Type u) (_ : ∀ i, DivisionRing (D i)),
      Nonempty (R ≃+* ∀ i, D i) := by
  refine ⟨fun _ => ?_, fun ⟨n, D, hD, ⟨e⟩⟩ => isReduced_of_injective e e.injective⟩
  obtain ⟨n, D, d, hD, hd, ⟨e⟩⟩ := IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing R
  -- Every Wedderburn block of a reduced ring has size one.
  have hsub : ∀ i, Subsingleton (Fin (d i)) := by
    simpa only [isReduced_pi_iff, Matrix.isReduced_iff_subsingleton] using
      isReduced_of_injective e.symm e.symm.injective
  refine ⟨n, D, hD, ⟨e.trans <| RingEquiv.piCongrRight fun i => ?_⟩⟩
  have : Unique (Fin (d i)) := uniqueOfSubsingleton ⟨0, (hd i).pos⟩
  -- Replace `Fin.fintype` by the `Fintype` structure `Matrix.uniqueRingEquiv` is stated for.
  rw [show Fin.fintype (d i) = Unique.fintype from Subsingleton.elim _ _]
  exact Matrix.uniqueRingEquiv

/-! ### Basic algebras -/

/-- A ring is **basic** when its quotient by the Jacobson radical is a finite product of division
rings, stated as that quotient being semisimple and reduced; the two readings agree by
`TauCeti.isBasic_iff_pi_divisionRing`.  When the quotient is semisimple anyway, as for a
finite-dimensional algebra over a field, the condition is reducedness alone -- every Wedderburn
block has size one -- which is `TauCeti.isBasic_iff_isReduced`. -/
def IsBasic (A : Type v) [Ring A] : Prop :=
  IsSemisimpleRing (A ⧸ Ring.jacobson A) ∧ IsReduced (A ⧸ Ring.jacobson A)

/-- Unfolding lemma for `TauCeti.IsBasic`: it is semisimplicity together with reducedness of the
quotient by the Jacobson radical. -/
@[simp]
theorem isBasic_def (A : Type v) [Ring A] :
    IsBasic A ↔ IsSemisimpleRing (A ⧸ Ring.jacobson A) ∧ IsReduced (A ⧸ Ring.jacobson A) := Iff.rfl

/-- **Basicness is invariant under ring equivalence.**  A ring equivalence carries the Jacobson
radical onto the Jacobson radical, hence descends to an equivalence of the quotients, along which
both semisimplicity and reducedness transport. -/
theorem _root_.RingEquiv.isBasic_iff {A : Type v} {B : Type w} [Ring A] [Ring B] (e : A ≃+* B) :
    IsBasic A ↔ IsBasic B := by
  have hmap : Ring.jacobson B = (Ring.jacobson A).map (e : A →+* B) :=
    le_antisymm (by rw [Ideal.map_comap_of_equiv]; exact Ring.le_comap_jacobson (e.symm : B →+* A))
      (Ideal.map_le_iff_le_comap.mpr (Ring.le_comap_jacobson (e : A →+* B)))
  let q : (A ⧸ Ring.jacobson A) ≃+* (B ⧸ Ring.jacobson B) :=
    Ideal.quotientEquiv _ _ e hmap
  exact and_congr q.isSemisimpleRing_iff
    ⟨fun _ => isReduced_of_injective q.symm q.symm.injective,
      fun _ => isReduced_of_injective q q.injective⟩

/-- **A ring is basic exactly when its quotient by the Jacobson radical is a finite product of
division rings.**  This is `TauCeti.isReduced_iff_pi_divisionRing`, read at that quotient; the
semisimplicity asked for by the definition is what makes the criterion applicable, and it comes
back from a product of division rings, each of which is a semisimple ring. -/
theorem isBasic_iff_pi_divisionRing (A : Type v) [Ring A] :
    IsBasic A ↔ ∃ (n : ℕ) (D : Fin n → Type v) (_ : ∀ i, DivisionRing (D i)),
      Nonempty ((A ⧸ Ring.jacobson A) ≃+* ∀ i, D i) := by
  refine ⟨fun ⟨_, h⟩ => (isReduced_iff_pi_divisionRing _).mp h, fun ⟨n, D, _, ⟨e⟩⟩ => ?_⟩
  exact ⟨e.symm.isSemisimpleRing, isReduced_of_injective e e.injective⟩

/-- **A ring with semisimple quotient by its Jacobson radical is basic exactly when that quotient
is reduced.**  The semisimplicity half of `TauCeti.IsBasic` is then automatic and only reducedness
is a condition.  This covers every Artinian, and more generally every semiprimary, ring, in
particular every finite-dimensional algebra over a field. -/
theorem isBasic_iff_isReduced (A : Type v) [Ring A] [IsSemisimpleRing (A ⧸ Ring.jacobson A)] :
    IsBasic A ↔ IsReduced (A ⧸ Ring.jacobson A) :=
  and_iff_right ‹_›

/-- **A commutative ring with semisimple quotient by its Jacobson radical is basic**, a commutative
semisimple ring being reduced.  This covers every commutative Artinian ring, in particular every
finite-dimensional commutative algebra over a field. -/
theorem isBasic_of_commRing (A : Type v) [CommRing A] [IsSemisimpleRing (A ⧸ Ring.jacobson A)] :
    IsBasic A :=
  ⟨‹_›, inferInstance⟩

/-! ### Idempotents of a basic algebra over an algebraically closed field -/

/-- **The block idempotents of a basic algebra.** A finite-dimensional basic algebra over an
algebraically closed field has a complete family of nonzero orthogonal idempotents whose classes
span its quotient by the Jacobson radical. -/
theorem IsBasic.exists_completeOrthogonalIdempotents {k : Type w} {A : Type v} [Field k]
    [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A] (hA : IsBasic A) :
    ∃ (n : ℕ) (e : Fin n → A), CompleteOrthogonalIdempotents e ∧ (∀ i, e i ≠ 0) ∧
      Submodule.span k (Set.range fun i => Ideal.Quotient.mk (Ring.jacobson A) (e i)) = ⊤ := by
  classical
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨hss, hred⟩ := (isBasic_def A).mp hA
  obtain ⟨n, d, hd, ⟨σ⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k (A ⧸ Ring.jacobson A)
  -- Every Wedderburn block of a basic algebra has size one.
  have hsub : ∀ i, Subsingleton (Fin (d i)) := by
    simpa only [isReduced_pi_iff, Matrix.isReduced_iff_subsingleton] using
      isReduced_of_injective σ.symm σ.symm.injective
  -- The block units span `A ⧸ J`; lift them along the nilpotent radical.
  let ē : Fin n → A ⧸ Ring.jacobson A := fun i => σ.symm (Pi.single i 1)
  have hē : CompleteOrthogonalIdempotents ē :=
    (CompleteOrthogonalIdempotents.single fun i => Matrix (Fin (d i)) (Fin (d i)) k).map
      σ.symm.toRingHom
  obtain ⟨e, he, hπe⟩ := hē.lift_of_isNilpotent_ker (Ideal.Quotient.mk (Ring.jacobson A))
    (fun x hx => by
      obtain ⟨m, hm⟩ := (IsSemiprimaryRing.isNilpotent : IsNilpotent (Ring.jacobson A))
      exact ⟨m, by simpa [hm] using Ideal.pow_mem_pow (Ideal.mk_ker.le hx) m⟩)
    (fun i => Ideal.Quotient.mk_surjective _)
  have hπe' (i : Fin n) : Ideal.Quotient.mk (Ring.jacobson A) (e i) = ē i := congrFun hπe i
  refine ⟨n, e, he, fun i h => ?_, eq_top_iff.mpr fun y _ => ?_⟩
  · have hēzero : ē i = 0 := by rw [← hπe' i, h, map_zero]
    have h' : (Pi.single i 1 : Π i, Matrix (Fin (d i)) (Fin (d i)) k) = 0 :=
      σ.symm.injective (hēzero.trans (map_zero _).symm)
    simpa using congrFun h' i
  · have hy : y = ∑ i, σ y i 0 0 • ē i := by
      apply σ.injective
      ext i p q
      rw [Subsingleton.elim p 0, Subsingleton.elim q 0]
      simp only [ē, AlgEquiv.apply_symm_apply, map_sum, map_smul, Finset.sum_apply,
        Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply]
      rw [Fintype.sum_eq_single i fun b hb => by simp [Pi.single_eq_of_ne (Ne.symm hb)]]
      simp
    rw [hy]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hπe' i⟩)

end TauCeti
