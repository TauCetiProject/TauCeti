/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Alexander.Basic
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Circle
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.One
public import TauCeti.KnotTheory.PDCode.RotateCrossing
import TauCeti.Algebra.Module.Basic

/-!
# The Alexander module under planar isotopy and the first Reidemeister move

The Alexander module of an oriented PD-code (`TauCeti.OrientedPDCode.AlexanderModule`) is
presented by one generator for each half-edge and each crossing-free component, subject to the
abelianized Fox derivatives of the Wirtinger relations. This file shows that the generating moves
of Reidemeister equivalence (`TauCeti.OrientedPDCode.IsReidemeisterMove`) that involve a single
crossing keep the module up to `ℤ[T;T⁻¹]`-linear equivalence: relabelling half-edges and
crossings, reading a crossing from another slot, and the first Reidemeister move, both on an arc
and on a crossing-free circle. The elementary ideals, the Fitting ideals of the module, are
therefore unchanged by these moves.

Relabelling and rotation only rename the generators and the relations. The first move adds four
half-edges, which the relations of the new crossing identify with the arc that the kink is cut
into: the loop of the kink joins two of them, the over-strand joins the loop to one end, and the
under-strand relation `x = t ^ ε • y + (1 - t ^ ε) • x`, whose incoming and outgoing arcs are both
the loop, forces `x = y` because `t ^ ε` is a unit. On a crossing-free circle the two arcs of the
kink and its over-strand identify the four half-edges with the single generator of the circle.

Classically the elementary ideals are shown to be link invariants through the invariance of the
link group and the invariance of elementary ideals under Tietze transformations; here each move
is treated directly on the Alexander-module presentation. The second and third Reidemeister
moves are not treated in this file.

## Main definitions

* `TauCeti.OrientedPDCode.alexanderModuleRelabelEquiv`: relabelling keeps the Alexander module.
* `TauCeti.OrientedPDCode.alexanderModuleRotateCrossingEquiv`: so does reading a crossing from
  another slot.
* `TauCeti.OrientedPDCode.alexanderModuleReidemeisterOneEquiv`: so does adding a kink to an arc.
* `TauCeti.OrientedPDCode.alexanderModuleAdjoinKinkEquiv`: an isolated kink and a crossing-free
  circle give the same Alexander module.

## Main results

* `TauCeti.OrientedPDCode.elementaryIdeal_relabel`,
  `TauCeti.OrientedPDCode.elementaryIdeal_rotateCrossing`,
  `TauCeti.OrientedPDCode.elementaryIdeal_reidemeisterOne` and
  `TauCeti.OrientedPDCode.elementaryIdeal_adjoinKink`: these moves keep every elementary ideal.
* `TauCeti.OrientedPDCode.alexanderGenerator_reidemeisterOne_inr`: the four half-edges of a kink
  give the generator of the arc it is cut into.

## References

* R. H. Crowell, R. H. Fox, *Introduction to Knot Theory*, Graduate Texts in Mathematics 57,
  Springer (1977), Chapters VI and VII.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Graduate Texts in Mathematics 175,
  Springer (1997), Chapters 1 and 6.
-/

public section

noncomputable section

open LaurentPolynomial

namespace TauCeti

namespace OrientedPDCode

variable {n m : ℕ}

/-! ### Relabelling -/

section Relabel

variable (D : OrientedPDCode n) (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m)

/-- The weight of a slot after relabelling is read at the old crossing name. -/
@[simp]
theorem alexanderWeight_relabel (i : Fin m) (slot : Fin 4) :
    (D.relabel half cross).alexanderWeight i slot = D.alexanderWeight (cross.symm i) slot := by
  simp [alexanderWeight_def]

/-- The map from the Alexander module of a relabelled code, sending each generator to the
generator of the old name. -/
private def relabelHom :
    (D.relabel half cross).AlexanderModule →ₗ[ℤ[T;T⁻¹]] D.AlexanderModule :=
  (D.relabel half cross).alexanderLift
    (Sum.elim (fun h ↦ D.alexanderGenerator (.inl (half.symm h)))
      fun j ↦ D.alexanderGenerator (.inr (Fin.cast (by simp) j)))
    (fun h ↦ by
      simp only [Sum.elim_inl, relabel_toPDCode, PDCode.relabel_edgePair,
        PerfectMatching.congr_val_apply, Equiv.symm_apply_apply, alexanderGenerator_edgePair])
    (fun i slot ↦ by simpa [PDCode.crossing_relabel] using
      D.alexanderGenerator_crossing_add_two (cross.symm i) slot)

private theorem relabelHom_alexanderGenerator (g) :
    relabelHom D half cross ((D.relabel half cross).alexanderGenerator g) =
      Sum.elim (fun h ↦ D.alexanderGenerator (.inl (half.symm h)))
        (fun j ↦ D.alexanderGenerator (.inr (Fin.cast (by simp) j))) g :=
  alexanderLift_alexanderGenerator _ _ _ _ _

/-- The map to the Alexander module of a relabelled code, sending each generator to the generator
of the new name. -/
private def relabelInvHom :
    D.AlexanderModule →ₗ[ℤ[T;T⁻¹]] (D.relabel half cross).AlexanderModule :=
  D.alexanderLift
    (Sum.elim (fun h ↦ (D.relabel half cross).alexanderGenerator (.inl (half h)))
      fun j ↦ (D.relabel half cross).alexanderGenerator (.inr (Fin.cast (by simp) j)))
    (fun h ↦ by
      have := (D.relabel half cross).alexanderGenerator_edgePair (half h)
      simp only [relabel_toPDCode, PDCode.relabel_edgePair,
        PerfectMatching.congr_val_apply_apply] at this
      simpa only [Sum.elim_inl] using this)
    (fun i slot ↦ by
      simpa [PDCode.crossing_relabel] using
        (D.relabel half cross).alexanderGenerator_crossing_add_two (cross i) slot)

private theorem relabelInvHom_alexanderGenerator (g) :
    relabelInvHom D half cross (D.alexanderGenerator g) =
      Sum.elim (fun h ↦ (D.relabel half cross).alexanderGenerator (.inl (half h)))
        (fun j ↦ (D.relabel half cross).alexanderGenerator (.inr (Fin.cast (by simp) j))) g :=
  alexanderLift_alexanderGenerator _ _ _ _ _

/-- **Relabelling keeps the Alexander module**: the generator of a half-edge of the relabelled
code corresponds to the generator of its old name. -/
def alexanderModuleRelabelEquiv :
    (D.relabel half cross).AlexanderModule ≃ₗ[ℤ[T;T⁻¹]] D.AlexanderModule :=
  LinearEquiv.ofLinearMap (relabelHom D half cross) (relabelInvHom D half cross)
    (by ext (h | j) <;> simp [relabelHom_alexanderGenerator, relabelInvHom_alexanderGenerator])
    (by ext (h | j) <;> simp [relabelHom_alexanderGenerator, relabelInvHom_alexanderGenerator])

/-- The equivalence sends each generator of the relabelled code to the generator of its old
name. -/
@[simp]
theorem alexanderModuleRelabelEquiv_apply_alexanderGenerator
    (g : Fin (4 * m) ⊕ Fin (D.relabel half cross).crossinglessComponentCount) :
    D.alexanderModuleRelabelEquiv half cross ((D.relabel half cross).alexanderGenerator g) =
      Sum.elim (fun h ↦ D.alexanderGenerator (.inl (half.symm h)))
        (fun j ↦ D.alexanderGenerator (.inr (Fin.cast (by simp) j))) g :=
  relabelHom_alexanderGenerator D half cross g

/-- The inverse equivalence sends each generator to the generator of its new name. -/
@[simp]
theorem alexanderModuleRelabelEquiv_symm_apply_alexanderGenerator
    (g : Fin (4 * n) ⊕ Fin D.crossinglessComponentCount) :
    (D.alexanderModuleRelabelEquiv half cross).symm (D.alexanderGenerator g) =
      Sum.elim (fun h ↦ (D.relabel half cross).alexanderGenerator (.inl (half h)))
        (fun j ↦ (D.relabel half cross).alexanderGenerator (.inr (Fin.cast (by simp) j))) g :=
  relabelInvHom_alexanderGenerator D half cross g

/-- **Relabelling keeps the elementary ideals.** -/
@[simp]
theorem elementaryIdeal_relabel (k : ℕ) :
    (D.relabel half cross).elementaryIdeal k = D.elementaryIdeal k := by
  rw [elementaryIdeal_def, elementaryIdeal_def]
  exact fittingIdeal_congr (D.alexanderModuleRelabelEquiv half cross) k

end Relabel

/-! ### Rotating a crossing -/

section RotateCrossing

variable (D : OrientedPDCode n) (i : Fin n)

/-- The weight of a slot of the rotated crossing is the weight of the next slot in `D`. -/
@[simp]
theorem alexanderWeight_rotateCrossing_self (slot : Fin 4) :
    (D.rotateCrossing i).alexanderWeight i slot = D.alexanderWeight i (slot + 1) := by
  have hover : (D.rotateCrossing i).isOver i slot = D.isOver i (slot + 1) := by
    fin_cases slot <;> simp [PDCode.isOver_def]
  rw [alexanderWeight_def, alexanderWeight_def, hover]
  simp

/-- The other crossings keep their weights. -/
@[simp]
theorem alexanderWeight_rotateCrossing_of_ne {j : Fin n} (hj : j ≠ i) (slot : Fin 4) :
    (D.rotateCrossing i).alexanderWeight j slot = D.alexanderWeight j slot := by
  simp [alexanderWeight_def, PDCode.isOver_def, hj]

private theorem crossing_rotateCrossing_self (slot : Fin 4) :
    (D.rotateCrossing i).crossing i slot = D.crossing i (slot + 1) := by
  simp

private theorem crossing_rotateCrossing_of_ne {j : Fin n} (hj : j ≠ i) (slot : Fin 4) :
    (D.rotateCrossing i).crossing j slot = D.crossing j slot := by
  simp [hj]

/-- The map from the Alexander module of the rotated code, fixing every generator. -/
private def rotateCrossingHom :
    (D.rotateCrossing i).AlexanderModule →ₗ[ℤ[T;T⁻¹]] D.AlexanderModule :=
  (D.rotateCrossing i).alexanderLift
    (Sum.elim (fun h ↦ D.alexanderGenerator (.inl h))
      fun j ↦ D.alexanderGenerator (.inr (Fin.cast (by simp) j)))
    (fun h ↦ by simp)
    (fun j slot ↦ by
      by_cases hj : j = i
      · subst hj
        have := D.alexanderGenerator_crossing_add_two j (slot + 1)
        rw [add_right_comm slot 1 2] at this
        simpa [crossing_rotateCrossing_self] using this
      · simpa [crossing_rotateCrossing_of_ne _ _ hj, hj] using
          D.alexanderGenerator_crossing_add_two j slot)

private theorem rotateCrossingHom_alexanderGenerator (g) :
    rotateCrossingHom D i ((D.rotateCrossing i).alexanderGenerator g) =
      Sum.elim (fun h ↦ D.alexanderGenerator (.inl h))
        (fun j ↦ D.alexanderGenerator (.inr (Fin.cast (by simp) j))) g :=
  alexanderLift_alexanderGenerator _ _ _ _ _

/-- The map to the Alexander module of the rotated code, fixing every generator. -/
private def rotateCrossingInvHom :
    D.AlexanderModule →ₗ[ℤ[T;T⁻¹]] (D.rotateCrossing i).AlexanderModule :=
  D.alexanderLift
    (Sum.elim (fun h ↦ (D.rotateCrossing i).alexanderGenerator (.inl h))
      fun j ↦ (D.rotateCrossing i).alexanderGenerator (.inr (Fin.cast (by simp) j)))
    (fun h ↦ by simpa using (D.rotateCrossing i).alexanderGenerator_edgePair h)
    (fun j slot ↦ by
      by_cases hj : j = i
      · subst hj
        obtain ⟨slot, rfl⟩ : ∃ s, s + 1 = slot := ⟨slot - 1, sub_add_cancel _ _⟩
        have := (D.rotateCrossing j).alexanderGenerator_crossing_add_two j slot
        rw [crossing_rotateCrossing_self, crossing_rotateCrossing_self,
          crossing_rotateCrossing_self, alexanderWeight_rotateCrossing_self,
          add_right_comm slot 2 1] at this
        simpa using this
      · simpa [crossing_rotateCrossing_of_ne _ _ hj, hj] using
          (D.rotateCrossing i).alexanderGenerator_crossing_add_two j slot)

private theorem rotateCrossingInvHom_alexanderGenerator (g) :
    rotateCrossingInvHom D i (D.alexanderGenerator g) =
      Sum.elim (fun h ↦ (D.rotateCrossing i).alexanderGenerator (.inl h))
        (fun j ↦ (D.rotateCrossing i).alexanderGenerator (.inr (Fin.cast (by simp) j))) g :=
  alexanderLift_alexanderGenerator _ _ _ _ _

/-- **Reading a crossing from another slot keeps the Alexander module**: the half-edges are
unchanged, and the relations at the rotated crossing are those of `D` read one slot further. -/
def alexanderModuleRotateCrossingEquiv :
    (D.rotateCrossing i).AlexanderModule ≃ₗ[ℤ[T;T⁻¹]] D.AlexanderModule :=
  LinearEquiv.ofLinearMap (rotateCrossingHom D i) (rotateCrossingInvHom D i)
    (by
      ext (h | j) <;>
        simp [rotateCrossingHom_alexanderGenerator, rotateCrossingInvHom_alexanderGenerator])
    (by
      ext (h | j) <;>
        simp [rotateCrossingHom_alexanderGenerator, rotateCrossingInvHom_alexanderGenerator])

/-- The equivalence fixes every generator. -/
@[simp]
theorem alexanderModuleRotateCrossingEquiv_apply_alexanderGenerator
    (g : Fin (4 * n) ⊕ Fin (D.rotateCrossing i).crossinglessComponentCount) :
    D.alexanderModuleRotateCrossingEquiv i ((D.rotateCrossing i).alexanderGenerator g) =
      Sum.elim (fun h ↦ D.alexanderGenerator (.inl h))
        (fun j ↦ D.alexanderGenerator (.inr (Fin.cast (by simp) j))) g :=
  rotateCrossingHom_alexanderGenerator D i g

/-- The inverse equivalence fixes every generator. -/
@[simp]
theorem alexanderModuleRotateCrossingEquiv_symm_apply_alexanderGenerator
    (g : Fin (4 * n) ⊕ Fin D.crossinglessComponentCount) :
    (D.alexanderModuleRotateCrossingEquiv i).symm (D.alexanderGenerator g) =
      Sum.elim (fun h ↦ (D.rotateCrossing i).alexanderGenerator (.inl h))
        (fun j ↦ (D.rotateCrossing i).alexanderGenerator (.inr (Fin.cast (by simp) j))) g :=
  rotateCrossingInvHom_alexanderGenerator D i g

/-- **Reading a crossing from another slot keeps the elementary ideals.** -/
@[simp]
theorem elementaryIdeal_rotateCrossing (k : ℕ) :
    (D.rotateCrossing i).elementaryIdeal k = D.elementaryIdeal k := by
  rw [elementaryIdeal_def, elementaryIdeal_def]
  exact fittingIdeal_congr (D.alexanderModuleRotateCrossingEquiv i) k

end RotateCrossing

/-! ### The first Reidemeister move -/

section ReidemeisterOne

variable (D : OrientedPDCode n) (h : Fin (4 * n)) (b : Bool)

private theorem crossing_reidemeisterOne_castSucc (i : Fin n) (slot : Fin 4) :
    (D.reidemeisterOne h b).crossing i.castSucc slot =
      PDCode.halfEdgeSuccEquiv n (.inl (D.crossing i slot)) := by
  simp

private theorem crossing_reidemeisterOne_last (slot : Fin 4) :
    (D.reidemeisterOne h b).crossing (Fin.last n) slot =
      PDCode.halfEdgeSuccEquiv n (.inr slot) := by
  simp

/-- The old crossings keep their weights. -/
@[simp]
theorem alexanderWeight_reidemeisterOne_castSucc (i : Fin n) (slot : Fin 4) :
    (D.reidemeisterOne h b).alexanderWeight i.castSucc slot = D.alexanderWeight i slot := by
  simp [alexanderWeight_def, PDCode.isOver_def]

/-- The four half-edges of the kink give the generator of the arc it is cut into: the loop of the
kink and the crossing relations identify them, whichever strand is over. -/
@[simp]
theorem alexanderGenerator_reidemeisterOne_inr (s : Fin 4) :
    (D.reidemeisterOne h b).alexanderGenerator (.inl (PDCode.halfEdgeSuccEquiv n (.inr s))) =
      (D.reidemeisterOne h b).alexanderGenerator (.inl (PDCode.halfEdgeSuccEquiv n (.inl h))) := by
  set D' := D.reidemeisterOne h b
  have arc0 : D'.alexanderGenerator (.inl (PDCode.halfEdgeSuccEquiv n (.inr 0))) =
      D'.alexanderGenerator (.inl (PDCode.halfEdgeSuccEquiv n (.inl h))) := by
    simpa [D'] using D'.alexanderGenerator_edgePair (PDCode.halfEdgeSuccEquiv n (.inl h))
  have arc23 : D'.alexanderGenerator (.inl (PDCode.halfEdgeSuccEquiv n (.inr 3))) =
      D'.alexanderGenerator (.inl (PDCode.halfEdgeSuccEquiv n (.inr 2))) := by
    simpa [D'] using D'.alexanderGenerator_edgePair (PDCode.halfEdgeSuccEquiv n (.inr 2))
  have r0 := D'.alexanderGenerator_crossing_add_two (Fin.last n) 0
  have r1 := D'.alexanderGenerator_crossing_add_two (Fin.last n) 1
  simp only [D', crossing_reidemeisterOne_last, Fin.isValue, Fin.reduceAdd, zero_add] at r0 r1
  rw [arc23] at r1
  suffices key : ∀ s, D'.alexanderGenerator (.inl (PDCode.halfEdgeSuccEquiv n (.inr s))) =
      D'.alexanderGenerator (.inl (PDCode.halfEdgeSuccEquiv n (.inr 0))) from
    (key s).trans arc0
  cases b
  · -- The over-strand is `0`–`2`, and the under-strand relation at slot `1` gives `x₂ = x₁`.
    rw [alexanderWeight_of_isOver _ (by simp [PDCode.isOver_def]), one_smul, sub_self, zero_smul,
      add_zero] at r0
    rw [alexanderWeight_of_not_isOver _ (by simp [PDCode.isOver_def])] at r1
    have h21 := (isUnit_T _).eq_of_eq_smul_add_one_sub_smul r1
    intro s
    fin_cases s
    · rfl
    · exact h21.symm.trans r0
    · exact r0
    · exact arc23.trans r0
  · -- The over-strand is `1`–`3`, and the under-strand relation at slot `0` gives `x₁ = x₀`.
    rw [alexanderWeight_of_isOver _ (by simp [PDCode.isOver_def]), one_smul, sub_self, zero_smul,
      add_zero] at r1
    rw [alexanderWeight_of_not_isOver _ (by simp [PDCode.isOver_def]), ← r1] at r0
    have h20 := (isUnit_T _).eq_of_eq_smul_add_one_sub_smul r0
    intro s
    fin_cases s
    · rfl
    · exact r1.symm.trans h20
    · exact h20
    · exact arc23.trans h20

/-- The map from the Alexander module of the code with the kink, sending the four half-edges of
the kink to the generator of the arc it is cut into. -/
private def reidemeisterOneHom :
    (D.reidemeisterOne h b).AlexanderModule →ₗ[ℤ[T;T⁻¹]] D.AlexanderModule :=
  (D.reidemeisterOne h b).alexanderLift
    (Sum.elim
      (fun x ↦ Sum.elim (fun y ↦ D.alexanderGenerator (.inl y))
        (fun _ ↦ D.alexanderGenerator (.inl h)) ((PDCode.halfEdgeSuccEquiv n).symm x))
      fun j ↦ D.alexanderGenerator (.inr (Fin.cast (by simp) j)))
    (fun x ↦ by
      obtain ⟨x | s, rfl⟩ := (PDCode.halfEdgeSuccEquiv n).surjective x
      · by_cases hx : x = h
        · subst hx
          simp
        by_cases hx' : x = D.edgePair.val h
        · subst hx'
          simp
        simp [PDCode.reidemeisterOne_edgePair_inl_of_ne _ _ _ hx hx']
      · fin_cases s <;> simp)
    (fun i slot ↦ by
      induction i using Fin.lastCases with
      | last =>
        simp only [crossing_reidemeisterOne_last, Sum.elim_inl, Equiv.symm_apply_apply,
          Sum.elim_inr]
        rw [← add_smul, add_sub_cancel, one_smul]
      | cast i =>
        simpa [crossing_reidemeisterOne_castSucc] using
          D.alexanderGenerator_crossing_add_two i slot)

private theorem reidemeisterOneHom_alexanderGenerator (g) :
    reidemeisterOneHom D h b ((D.reidemeisterOne h b).alexanderGenerator g) =
      Sum.elim
        (fun x ↦ Sum.elim (fun y ↦ D.alexanderGenerator (.inl y))
          (fun _ ↦ D.alexanderGenerator (.inl h)) ((PDCode.halfEdgeSuccEquiv n).symm x))
        (fun j ↦ D.alexanderGenerator (.inr (Fin.cast (by simp) j))) g :=
  alexanderLift_alexanderGenerator _ _ _ _ _

/-- The map to the Alexander module of the code with the kink, sending each old generator to the
generator of the same half-edge. -/
private def reidemeisterOneInvHom :
    D.AlexanderModule →ₗ[ℤ[T;T⁻¹]] (D.reidemeisterOne h b).AlexanderModule :=
  D.alexanderLift
    (Sum.elim (fun y ↦ (D.reidemeisterOne h b).alexanderGenerator
        (.inl (PDCode.halfEdgeSuccEquiv n (.inl y))))
      fun j ↦ (D.reidemeisterOne h b).alexanderGenerator (.inr (Fin.cast (by simp) j)))
    (fun y ↦ by
      have hone := (D.reidemeisterOne h b).alexanderGenerator_edgePair
        (PDCode.halfEdgeSuccEquiv n (.inr 1))
      simp only [toPDCode_reidemeisterOne, PDCode.reidemeisterOne_edgePair_inr_one,
        alexanderGenerator_reidemeisterOne_inr] at hone
      simp only [Sum.elim_inl]
      by_cases hy : y = h
      · subst hy
        exact hone
      by_cases hy' : y = D.edgePair.val h
      · subst hy'
        rw [PerfectMatching.apply_apply]
        exact hone.symm
      simpa [PDCode.reidemeisterOne_edgePair_inl_of_ne _ _ _ hy hy'] using
        (D.reidemeisterOne h b).alexanderGenerator_edgePair (PDCode.halfEdgeSuccEquiv n (.inl y)))
    (fun i slot ↦ by
      simpa [crossing_reidemeisterOne_castSucc] using
        (D.reidemeisterOne h b).alexanderGenerator_crossing_add_two i.castSucc slot)

private theorem reidemeisterOneInvHom_alexanderGenerator (g) :
    reidemeisterOneInvHom D h b (D.alexanderGenerator g) =
      Sum.elim (fun y ↦ (D.reidemeisterOne h b).alexanderGenerator
          (.inl (PDCode.halfEdgeSuccEquiv n (.inl y))))
        (fun j ↦ (D.reidemeisterOne h b).alexanderGenerator (.inr (Fin.cast (by simp) j))) g :=
  alexanderLift_alexanderGenerator _ _ _ _ _

/-- **The first Reidemeister move keeps the Alexander module**: the four half-edges of the kink
correspond to the generator of the arc it is cut into, and the old half-edges to themselves. -/
def alexanderModuleReidemeisterOneEquiv :
    (D.reidemeisterOne h b).AlexanderModule ≃ₗ[ℤ[T;T⁻¹]] D.AlexanderModule :=
  LinearEquiv.ofLinearMap (reidemeisterOneHom D h b) (reidemeisterOneInvHom D h b)
    (by
      ext (y | j) <;>
        simp [reidemeisterOneHom_alexanderGenerator, reidemeisterOneInvHom_alexanderGenerator])
    (by
      ext (x | j)
      · obtain ⟨y | s, rfl⟩ := (PDCode.halfEdgeSuccEquiv n).surjective x
        · simp [reidemeisterOneHom_alexanderGenerator, reidemeisterOneInvHom_alexanderGenerator]
        · simp [reidemeisterOneHom_alexanderGenerator, reidemeisterOneInvHom_alexanderGenerator]
      · simp [reidemeisterOneHom_alexanderGenerator, reidemeisterOneInvHom_alexanderGenerator])

/-- The equivalence sends the old half-edges to themselves and the four half-edges of the kink to
the half-edge `h` whose arc the kink is cut into. -/
@[simp]
theorem alexanderModuleReidemeisterOneEquiv_apply_alexanderGenerator
    (g : Fin (4 * (n + 1)) ⊕ Fin (D.reidemeisterOne h b).crossinglessComponentCount) :
    D.alexanderModuleReidemeisterOneEquiv h b ((D.reidemeisterOne h b).alexanderGenerator g) =
      Sum.elim
        (fun x ↦ Sum.elim (fun y ↦ D.alexanderGenerator (.inl y))
          (fun _ ↦ D.alexanderGenerator (.inl h)) ((PDCode.halfEdgeSuccEquiv n).symm x))
        (fun j ↦ D.alexanderGenerator (.inr (Fin.cast (by simp) j))) g :=
  reidemeisterOneHom_alexanderGenerator D h b g

/-- The inverse equivalence sends every generator to the generator of the same half-edge or
component. -/
@[simp]
theorem alexanderModuleReidemeisterOneEquiv_symm_apply_alexanderGenerator
    (g : Fin (4 * n) ⊕ Fin D.crossinglessComponentCount) :
    (D.alexanderModuleReidemeisterOneEquiv h b).symm (D.alexanderGenerator g) =
      Sum.elim (fun y ↦ (D.reidemeisterOne h b).alexanderGenerator
          (.inl (PDCode.halfEdgeSuccEquiv n (.inl y))))
        (fun j ↦ (D.reidemeisterOne h b).alexanderGenerator (.inr (Fin.cast (by simp) j))) g :=
  reidemeisterOneInvHom_alexanderGenerator D h b g

/-- **The first Reidemeister move keeps the elementary ideals.** -/
@[simp]
theorem elementaryIdeal_reidemeisterOne (k : ℕ) :
    (D.reidemeisterOne h b).elementaryIdeal k = D.elementaryIdeal k := by
  rw [elementaryIdeal_def, elementaryIdeal_def]
  exact fittingIdeal_congr (D.alexanderModuleReidemeisterOneEquiv h b) k

end ReidemeisterOne

/-! ### The first Reidemeister move on a crossing-free circle -/

section AdjoinKink

variable (D : OrientedPDCode n) (o b : Bool)

/-- Adjoining a crossing-free circle keeps every weight. -/
@[simp]
theorem alexanderWeight_adjoinCircle (i : Fin n) (slot : Fin 4) :
    (D.adjoinCircle o).alexanderWeight i slot = D.alexanderWeight i slot := by
  simp [alexanderWeight_def, PDCode.isOver_def]

/-- Adjoining an isolated kink keeps the weights of the old crossings. -/
@[simp]
theorem alexanderWeight_adjoinKink_castSucc (i : Fin n) (slot : Fin 4) :
    (D.adjoinKink o b).alexanderWeight i.castSucc slot = D.alexanderWeight i slot := by
  simp [alexanderWeight_def, PDCode.isOver_def]

/-- The four half-edges of an isolated kink give one generator: its two arcs and its over-strand
identify them, whichever strand is over. -/
@[simp]
theorem alexanderGenerator_adjoinKink_inr (s : Fin 4) :
    (D.adjoinKink o b).alexanderGenerator (.inl (PDCode.halfEdgeSuccEquiv n (.inr s))) =
      (D.adjoinKink o b).alexanderGenerator (.inl (PDCode.halfEdgeSuccEquiv n (.inr 0))) := by
  set D' := D.adjoinKink o b
  have arc01 : D'.alexanderGenerator (.inl (PDCode.halfEdgeSuccEquiv n (.inr 1))) =
      D'.alexanderGenerator (.inl (PDCode.halfEdgeSuccEquiv n (.inr 0))) := by
    simpa [D', Equiv.swap_apply_def] using
      D'.alexanderGenerator_edgePair (PDCode.halfEdgeSuccEquiv n (.inr 0))
  have arc23 : D'.alexanderGenerator (.inl (PDCode.halfEdgeSuccEquiv n (.inr 3))) =
      D'.alexanderGenerator (.inl (PDCode.halfEdgeSuccEquiv n (.inr 2))) := by
    simpa [D', Equiv.swap_apply_def] using
      D'.alexanderGenerator_edgePair (PDCode.halfEdgeSuccEquiv n (.inr 2))
  cases b
  · -- The over-strand `0`–`2` joins the two arcs.
    have r0 := D'.alexanderGenerator_crossing_add_two_of_isOver (i := Fin.last n) (slot := 0)
      (by simp [D', PDCode.isOver_def])
    simp only [D', PDCode.adjoinKink_crossing_last, toPDCode_adjoinKink, Fin.isValue,
      zero_add] at r0
    fin_cases s
    · rfl
    · exact arc01
    · exact r0
    · exact arc23.trans r0
  · -- The over-strand `1`–`3` joins the two arcs.
    have r1 := D'.alexanderGenerator_crossing_add_two_of_isOver (i := Fin.last n) (slot := 1)
      (by simp [D', PDCode.isOver_def])
    simp only [D', PDCode.adjoinKink_crossing_last, toPDCode_adjoinKink, Fin.isValue,
      Fin.reduceAdd] at r1
    fin_cases s
    · rfl
    · exact arc01
    · exact arc23.symm.trans (r1.trans arc01)
    · exact r1.trans arc01

private theorem crossing_adjoinCircle (i : Fin n) (slot : Fin 4) :
    (D.adjoinCircle o).crossing i slot = D.crossing i slot := by
  simp

/-- The map from the Alexander module of the code with an isolated kink to that of the code with
a crossing-free circle instead, sending the four half-edges of the kink to the generator of the
circle. -/
private def adjoinKinkHom :
    (D.adjoinKink o b).AlexanderModule →ₗ[ℤ[T;T⁻¹]] (D.adjoinCircle o).AlexanderModule :=
  (D.adjoinKink o b).alexanderLift
    (Sum.elim
      (fun x ↦ Sum.elim (fun y ↦ (D.adjoinCircle o).alexanderGenerator (.inl y))
        (fun _ ↦ (D.adjoinCircle o).alexanderGenerator
          (.inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount))))
        ((PDCode.halfEdgeSuccEquiv n).symm x))
      fun j ↦ (D.adjoinCircle o).alexanderGenerator
        (.inr (Fin.cast (by simp)
          (Fin.castSucc (Fin.cast (m := D.crossinglessComponentCount) (by simp) j)))))
    (fun x ↦ by
      obtain ⟨y | s, rfl⟩ := (PDCode.halfEdgeSuccEquiv n).surjective x
      · simpa using (D.adjoinCircle o).alexanderGenerator_edgePair y
      · simp)
    (fun i slot ↦ by
      induction i using Fin.lastCases with
      | last =>
        simp only [toPDCode_adjoinKink, PDCode.adjoinKink_crossing_last, Sum.elim_inl,
          Equiv.symm_apply_apply, Sum.elim_inr]
        rw [← add_smul, add_sub_cancel, one_smul]
      | cast i =>
        simpa [crossing_adjoinCircle] using
          (D.adjoinCircle o).alexanderGenerator_crossing_add_two i slot)

private theorem adjoinKinkHom_alexanderGenerator (g) :
    adjoinKinkHom D o b ((D.adjoinKink o b).alexanderGenerator g) =
      Sum.elim
        (fun x ↦ Sum.elim (fun y ↦ (D.adjoinCircle o).alexanderGenerator (.inl y))
          (fun _ ↦ (D.adjoinCircle o).alexanderGenerator
            (.inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount))))
          ((PDCode.halfEdgeSuccEquiv n).symm x))
        (fun j ↦ (D.adjoinCircle o).alexanderGenerator
          (.inr (Fin.cast (by simp)
            (Fin.castSucc (Fin.cast (m := D.crossinglessComponentCount) (by simp) j))))) g :=
  alexanderLift_alexanderGenerator _ _ _ _ _

/-- The map from the Alexander module of the code with a crossing-free circle to that of the code
with an isolated kink instead, sending the generator of the circle to that of the kink. -/
private def adjoinKinkInvHom :
    (D.adjoinCircle o).AlexanderModule →ₗ[ℤ[T;T⁻¹]] (D.adjoinKink o b).AlexanderModule :=
  (D.adjoinCircle o).alexanderLift
    (Sum.elim (fun y ↦ (D.adjoinKink o b).alexanderGenerator
        (.inl (PDCode.halfEdgeSuccEquiv n (.inl y))))
      fun j ↦ Fin.lastCases (motive := fun _ ↦ (D.adjoinKink o b).AlexanderModule)
        ((D.adjoinKink o b).alexanderGenerator (.inl (PDCode.halfEdgeSuccEquiv n (.inr 0))))
        (fun j ↦ (D.adjoinKink o b).alexanderGenerator (.inr (Fin.cast (by simp) j)))
        (Fin.cast (m := D.crossinglessComponentCount + 1) (by simp) j))
    (fun y ↦ by
      simpa using
        (D.adjoinKink o b).alexanderGenerator_edgePair (PDCode.halfEdgeSuccEquiv n (.inl y)))
    (fun i slot ↦ by
      simpa [crossing_adjoinCircle] using
        (D.adjoinKink o b).alexanderGenerator_crossing_add_two i.castSucc slot)

private theorem adjoinKinkInvHom_alexanderGenerator (g) :
    adjoinKinkInvHom D o b ((D.adjoinCircle o).alexanderGenerator g) =
      Sum.elim (fun y ↦ (D.adjoinKink o b).alexanderGenerator
          (.inl (PDCode.halfEdgeSuccEquiv n (.inl y))))
        (fun j ↦ Fin.lastCases (motive := fun _ ↦ (D.adjoinKink o b).AlexanderModule)
          ((D.adjoinKink o b).alexanderGenerator (.inl (PDCode.halfEdgeSuccEquiv n (.inr 0))))
          (fun j ↦ (D.adjoinKink o b).alexanderGenerator (.inr (Fin.cast (by simp) j)))
          (Fin.cast (m := D.crossinglessComponentCount + 1) (by simp) j)) g :=
  alexanderLift_alexanderGenerator _ _ _ _ _

/-- **The first Reidemeister move on a crossing-free circle keeps the Alexander module**: the
four half-edges of an isolated kink correspond to the generator of the circle it replaces. -/
def alexanderModuleAdjoinKinkEquiv :
    (D.adjoinKink o b).AlexanderModule ≃ₗ[ℤ[T;T⁻¹]] (D.adjoinCircle o).AlexanderModule :=
  LinearEquiv.ofLinearMap (adjoinKinkHom D o b) (adjoinKinkInvHom D o b)
    (by
      ext (y | j)
      · simp [adjoinKinkHom_alexanderGenerator, adjoinKinkInvHom_alexanderGenerator]
      · obtain ⟨j, rfl⟩ := (finCongr (by simp : (D.adjoinCircle o).crossinglessComponentCount =
          D.crossinglessComponentCount + 1)).symm.surjective j
        induction j using Fin.lastCases <;>
          simp [adjoinKinkHom_alexanderGenerator, adjoinKinkInvHom_alexanderGenerator])
    (by
      ext (x | j)
      · obtain ⟨y | s, rfl⟩ := (PDCode.halfEdgeSuccEquiv n).surjective x
        · simp [adjoinKinkHom_alexanderGenerator, adjoinKinkInvHom_alexanderGenerator]
        · simp [adjoinKinkHom_alexanderGenerator, adjoinKinkInvHom_alexanderGenerator]
      · simp [adjoinKinkHom_alexanderGenerator, adjoinKinkInvHom_alexanderGenerator])

/-- The equivalence sends the old half-edges and the crossing-free components of `D` to
themselves, and the four half-edges of the kink to the new circle. -/
@[simp]
theorem alexanderModuleAdjoinKinkEquiv_apply_alexanderGenerator
    (g : Fin (4 * (n + 1)) ⊕ Fin (D.adjoinKink o b).crossinglessComponentCount) :
    D.alexanderModuleAdjoinKinkEquiv o b ((D.adjoinKink o b).alexanderGenerator g) =
      Sum.elim
        (fun x ↦ Sum.elim (fun y ↦ (D.adjoinCircle o).alexanderGenerator (.inl y))
          (fun _ ↦ (D.adjoinCircle o).alexanderGenerator
            (.inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount))))
          ((PDCode.halfEdgeSuccEquiv n).symm x))
        (fun j ↦ (D.adjoinCircle o).alexanderGenerator
          (.inr (Fin.cast (by simp)
            (Fin.castSucc (Fin.cast (m := D.crossinglessComponentCount) (by simp) j))))) g :=
  adjoinKinkHom_alexanderGenerator D o b g

/-- The inverse equivalence sends the new circle to the kink, and the old half-edges and
crossing-free components to themselves. -/
@[simp]
theorem alexanderModuleAdjoinKinkEquiv_symm_apply_alexanderGenerator
    (g : Fin (4 * n) ⊕ Fin (D.adjoinCircle o).crossinglessComponentCount) :
    (D.alexanderModuleAdjoinKinkEquiv o b).symm ((D.adjoinCircle o).alexanderGenerator g) =
      Sum.elim (fun y ↦ (D.adjoinKink o b).alexanderGenerator
          (.inl (PDCode.halfEdgeSuccEquiv n (.inl y))))
        (fun j ↦ Fin.lastCases (motive := fun _ ↦ (D.adjoinKink o b).AlexanderModule)
          ((D.adjoinKink o b).alexanderGenerator (.inl (PDCode.halfEdgeSuccEquiv n (.inr 0))))
          (fun j ↦ (D.adjoinKink o b).alexanderGenerator (.inr (Fin.cast (by simp) j)))
          (Fin.cast (m := D.crossinglessComponentCount + 1) (by simp) j)) g :=
  adjoinKinkInvHom_alexanderGenerator D o b g

/-- **The first Reidemeister move on a crossing-free circle keeps the elementary ideals.** -/
@[simp]
theorem elementaryIdeal_adjoinKink (k : ℕ) :
    (D.adjoinKink o b).elementaryIdeal k = (D.adjoinCircle o).elementaryIdeal k := by
  rw [elementaryIdeal_def, elementaryIdeal_def]
  exact fittingIdeal_congr (D.alexanderModuleAdjoinKinkEquiv o b) k

end AdjoinKink

end OrientedPDCode

end TauCeti
