/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Divisors
public import TauCeti.AlgebraicGeometry.RationalPoint.Finite
public import TauCeti.AlgebraicGeometry.RationalPoint.ResidueField
import Mathlib.Algebra.Field.ULift
import Mathlib.FieldTheory.Finite.Extension
import TauCeti.AlgebraicGeometry.Scheme.ClosedPoint

/-!
# Counting rational points by residue degree

For a finite-type scheme over a finite field, a closed point of degree `d` accounts for `d`
points over an extension of degree `r` when `d ∣ r`, and none otherwise. Consequently, writing
`a_d` for the number of closed points of degree `d`, the point count over the extension is
`∑ d ∈ r.divisors, d * a_d`. Here degrees are residue-field dimensions, not residue-field
cardinalities. The formula is the closed-point count identity of Deligne, *La conjecture de
Weil. I*, §1.4(d), eq. (1.4.1).
-/

public section

open CategoryTheory
open scoped BigOperators

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))

variable {L : Type u} [Field L] [Algebra k L] [Finite L]

/-- The residue-field embeddings over a finite extension are nonempty precisely at the points
whose residue degrees divide the extension degree. -/
theorem nonempty_residueFieldAlgHom_iff_residueDegree_dvd (x : X) :
    letI : X.Over (Spec (.of k)) := ⟨a⟩
    Nonempty (X.residueField x →ₐ[k] L) ↔ a.residueDegree x ∣ Module.finrank k L := by
  let : X.Over (Spec (.of k)) := ⟨a⟩
  have hd : a.residueDegree x = Module.finrank k (X.residueField x) := by
    rw [X.residueFieldBaseAlgebra_eq_compHom k x]
    exact a.residueDegree_eq_finrank x
  rw [hd]
  exact FiniteField.nonempty_algHom_iff_finrank_dvd

/-- Over a finite extension, the points above `x` are counted by its residue degree if that
degree divides the extension degree, and by zero otherwise. -/
theorem natCard_points_over (x : X) :
    Nat.card {g : Spec (.of L) ⟶ X // g ≫ a = Spec.algebraMap k L ∧
      g (default : ↥(Spec (.of L))) = x} =
        if a.residueDegree x ∣ Module.finrank k L then a.residueDegree x else 0 := by
  let : X.Over (Spec (.of k)) := ⟨a⟩
  let e := X.pointsEquivSigmaResidueFieldAlgHom (k := k) (L := L)
  let ex : {g : Spec (.of L) ⟶ X // g ≫ a = Spec.algebraMap k L ∧
      g (default : ↥(Spec (.of L))) = x} ≃ (X.residueField x →ₐ[k] L) :=
    (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans <|
      (e.subtypeEquiv (fun g ↦ by rw [Scheme.pointsEquivSigmaResidueFieldAlgHom_apply_fst])).trans
        (Equiv.sigmaSubtype x)
  rw [Nat.card_congr ex]
  split_ifs with hx
  · have hd : a.residueDegree x = Module.finrank k (X.residueField x) := by
      rw [X.residueFieldBaseAlgebra_eq_compHom k x]
      exact a.residueDegree_eq_finrank x
    rw [hd] at hx ⊢
    exact FiniteField.natCard_algHom_of_finrank_dvd hx
  · have : IsEmpty (X.residueField x →ₐ[k] L) :=
      not_nonempty_iff.mp <| mt (a.nonempty_residueFieldAlgHom_iff_residueDegree_dvd x).mp hx
    exact Nat.card_of_isEmpty

/-- Over a finite extension of degree `r`, the image of the set of rational points in `X`
is exactly the set of points of residue degree dividing `r`. -/
theorem range_points_eq_setOf_residueDegree_dvd :
    Set.range (fun g : {g : Spec (.of L) ⟶ X // g ≫ a = Spec.algebraMap k L} ↦
      g.val (default : ↥(Spec (.of L)))) =
        {x | a.residueDegree x ∣ Module.finrank k L} := by
  let : X.Over (Spec (.of k)) := ⟨a⟩
  let e := X.pointsEquivSigmaResidueFieldAlgHom (k := k) (L := L)
  ext x
  rw [Set.mem_range, Set.mem_ofPred_eq, ← a.nonempty_residueFieldAlgHom_iff_residueDegree_dvd]
  constructor
  · rintro ⟨g, rfl⟩
    have h := X.pointsEquivSigmaResidueFieldAlgHom_apply_fst (k := k) (L := L) g
    exact ⟨h ▸ (e g).2⟩
  · rintro ⟨φ⟩
    refine ⟨e.symm ⟨x, φ⟩, ?_⟩
    rw [← X.pointsEquivSigmaResidueFieldAlgHom_apply_fst (k := k) (L := L), Equiv.apply_symm_apply]

variable [QuasiCompact a] [LocallyOfFiniteType a]

/-- There are only finitely many closed points of any given residue degree over a finite field. -/
theorem finite_closedPoints_residueDegree [Finite k] (d : ℕ) :
    Finite {x : closedPoints X // a.residueDegree x.val = d} := by
  by_cases hd : d = 0
  · have : IsEmpty {x : closedPoints X // a.residueDegree x.val = d} :=
      ⟨fun x ↦ a.residueDegree_ne_zero_of_isClosed x.val.property (x.property.trans hd)⟩
    infer_instance
  have : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
  have : NeZero d := ⟨hd⟩
  -- Lift the chosen finite-field extension to the universe of the scheme.
  let L := ULift.{u} (FiniteField.Extension k (ringChar k) d)
  have hL : Module.finrank k L = d :=
    (ULift.algEquiv (R := k)).toLinearEquiv.finrank_eq.trans
      (FiniteField.finrank_extension k (ringChar k) d)
  have := a.finite_points (L := ULift.{u} (FiniteField.Extension k (ringChar k) d))
  have hfin : ({x : X | a.residueDegree x ∣ d} : Set X).Finite := by
    rw [← hL, ← a.range_points_eq_setOf_residueDegree_dvd
      (L := ULift.{u} (FiniteField.Extension k (ringChar k) d))]
    exact Set.finite_range _
  let := hfin.fintype
  exact Finite.of_injective (fun x : {x : closedPoints X // a.residueDegree x.val = d} ↦
    (⟨x.val.val, x.property.dvd⟩ : {x : X // a.residueDegree x ∣ d}))
    fun _ _ h ↦ Subtype.ext (Subtype.ext (congrArg (fun y : {x : X // a.residueDegree x ∣ d} ↦
      y.val) h))

/-- The number of points over a finite extension of degree `r` is the sum over `d ∣ r` of
`d` times the number of closed points of degree `d`. -/
theorem numberOfRationalPoints_eq_sum_residueDegree :
    a.numberOfRationalPoints L = ∑ d ∈ (Module.finrank k L).divisors,
      d * Nat.card {x : closedPoints X // a.residueDegree x.val = d} := by
  classical
  let r := Module.finrank k L
  let P := {g : Spec (.of L) ⟶ X // g ≫ a = Spec.algebraMap k L}
  let f : P → X := fun g ↦ g.val (default : ↥(Spec (.of L)))
  let t : P → ℕ := fun g ↦ a.residueDegree (f g)
  have hr : r ≠ 0 := Module.finrank_pos.ne'
  have ht (g : P) : t g ∈ r.divisors := by
    have h := Set.mem_range_self (f := f) g
    dsimp only [f] at h
    rw [a.range_points_eq_setOf_residueDegree_dvd (L := L)] at h
    exact Nat.mem_divisors.mpr ⟨h, hr⟩
  -- For each degree, sum the fibres of the map to the underlying closed points.
  have hdegree (d : ℕ) (hd : d ∣ r) :
      Nat.card {g : P // t g = d} =
        d * Nat.card {x : closedPoints X // a.residueDegree x.val = d} := by
    let F := {x : closedPoints X // a.residueDegree x.val = d}
    have hk : Finite k := Finite.of_injective _ (algebraMap k L).injective
    let instF : Fintype F := @Fintype.ofFinite _ (a.finite_closedPoints_residueDegree d)
    let e : {g : P // t g = d} ≃ Σ x : F, {g : P // f g = x.val.val} :=
      (Equiv.sigmaSubtypeFiberEquivSubtype f (p := fun g ↦ t g = d)
        (q := fun x ↦ IsClosed ({x} : Set X) ∧ a.residueDegree x = d) (fun g ↦ by
          have hne : d ≠ 0 := fun h ↦ hr (Nat.zero_dvd.mp (h ▸ hd))
          constructor
          · intro h
            exact ⟨(a.isClosed_singleton_iff_residueDegree_ne_zero _).mpr (h.trans_ne hne), h⟩
          · exact And.right)).symm.trans <|
        Equiv.sigmaCongr (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm fun _ ↦
          Equiv.subtypeEquivRight fun _ ↦ Iff.rfl
    have : Finite P := a.finite_points (L := L)
    rw [Nat.card_congr e, Nat.card_sigma]
    have hcard (x : F) : Nat.card {g : P // f g = x.val.val} = d := by
      let ef := Equiv.subtypeSubtypeEquivSubtypeInter
        (fun g : Spec (.of L) ⟶ X ↦ g ≫ a = Spec.algebraMap k L)
        (fun g ↦ g (default : ↥(Spec (.of L))) = x.val.val)
      refine (Nat.card_congr ef).trans ?_
      rw [a.natCard_points_over, x.property, ite_eq_left hd]
    rw [Nat.card_eq_fintype_card (α := F)]
    simp [hcard, mul_comm]
  let instP : Fintype P := @Fintype.ofFinite _ (a.finite_points (L := L))
  rw [a.numberOfRationalPoints_def, Nat.card_eq_fintype_card, ← Finset.card_univ (α := P),
    Finset.card_eq_sum_card_fiberwise (f := t) (t := r.divisors) (fun g _ ↦ ht g)]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [← hdegree d (Nat.dvd_of_mem_divisors hd), Nat.card_eq_fintype_card]
  exact (Fintype.card_of_subtype _ (fun _ ↦ by simp)).symm

end AlgebraicGeometry.Scheme.Hom
