/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Envelope.Mat.Basic
public import TauCeti.CategoryTheory.Monoidal.Rigid.Mate

/-!
# Duals in the matrix category

Let `C` be a monoidal preadditive category, and let `M` and `N` be objects of the matrix category
`Mat_ C`, that is finite families of objects of `C`. If the index types of `M` and `N` are
identified by an equivalence `e : M.ι ≃ N.ι` and each `M.X i` is paired with `N.X (e i)` by an
exact pairing of `C`, then `M` and `N` form an exact pairing in `Mat_ C`. Its coevaluation and
evaluation are the diagonal matrices whose diagonal entries are the coevaluations and evaluations of
the summands:

```
η u (i, j) = η_ (M.X i) (N.X (e i)) ≫ M.X i ◁ 𝟙 (e i) j
ε (j, i) u = 𝟙 j (e i) ▷ M.X i ≫ ε_ (M.X i) (N.X (e i))
```

where `𝟙 j j'` is the entry of the identity matrix of `N`, so that only the entries with
`j = e i` are nonzero. The zigzag identities hold entrywise because they hold in `C`.

In particular the right dual of `M` is the family of right duals `i ↦ (M.X i)ᘁ` and its left dual
is the family of left duals `i ↦ ᘁ(M.X i)`, both over the same index type, so the matrix category
of a right rigid, left rigid or rigid monoidal preadditive category is again right rigid, left
rigid or rigid. The adjoint mate of a matrix is the transpose of the matrix of adjoint mates of its
entries. Together with the rigid structure on the idempotent completion
(`CategoryTheory.Idempotents.Karoubi.instRigidCategory`), this makes the additive and idempotent
envelope `Karoubi (Mat_ C)` of a rigid monoidal preadditive category rigid.

## Main declarations

* `CategoryTheory.Mat_.exactPairing`: the exact pairing of `M` and `N` induced by an equivalence
  `e : M.ι ≃ N.ι` and exact pairings of `M.X i` and `N.X (e i)`, with entries given by
  `Mat_.exactPairing_coevaluation_apply` and `Mat_.exactPairing_evaluation_apply`.
* `CategoryTheory.Mat_.instHasRightDual` and `CategoryTheory.Mat_.instHasLeftDual`: the right and
  left duals of `M` are the families of right and left duals of its summands, characterized by
  `Mat_.rightDual_ι`, `Mat_.rightDual_X`, `Mat_.leftDual_ι` and `Mat_.leftDual_X`.
* `CategoryTheory.Mat_.instRigidCategory`: the matrix category of a rigid monoidal preadditive
  category is rigid, and likewise for right and left rigidity.
* `CategoryTheory.Mat_.rightAdjointMate_apply` and `CategoryTheory.Mat_.leftAdjointMate_apply`:
  adjoint mates in `Mat_ C` are computed entrywise, with the indices transposed.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §2.10, for
  duals and adjoint mates in a monoidal category.
-/

public section

namespace CategoryTheory.Mat_

open MonoidalCategory ExactPairing

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C]

section ExactPairing

variable {M N : Mat_ C} (e : M.ι ≃ N.ι) (p : ∀ i, ExactPairing (M.X i) (N.X (e i)))

/-- The coevaluation of `Mat_.exactPairing e p`: the diagonal matrix of the coevaluations of the
summands. -/
private noncomputable def coev : 𝟙_ (Mat_ C) ⟶ M ⊗ N :=
  fun _ q ↦ η_ (M.X q.1) (N.X (e q.1)) ≫ M.X q.1 ◁ (𝟙 N : N ⟶ N) (e q.1) q.2

/-- The evaluation of `Mat_.exactPairing e p`: the diagonal matrix of the evaluations of the
summands. -/
private noncomputable def ev : N ⊗ M ⟶ 𝟙_ (Mat_ C) :=
  fun q _ ↦ (𝟙 N : N ⟶ N) q.1 (e q.2) ▷ M.X q.2 ≫ ε_ (M.X q.2) (N.X (e q.2))

/-- The zigzag identity on `M`, entrywise: only the summand of `(M ⊗ N) ⊗ M` indexed by
`((k, e k), i)` contributes to the entry at `((u, i), (k, u'))`, and there the zigzag identity of
`C` applies. -/
private theorem coev_whiskerRight_comp_whiskerLeft_ev :
    coev e p ▷ M ≫ (α_ M N M).hom ≫ M ◁ ev e p = (λ_ M).hom ≫ (ρ_ M).inv := by
  ext ⟨u, i⟩ ⟨k, u'⟩
  rw [comp_apply, leftUnitor_hom_comp_apply, ← Category.id_comp (ρ_ M).inv,
    comp_rightUnitor_inv_apply]
  simp only [associator_hom_comp_apply]
  refine (Fintype.sum_eq_single ((k, e k), i) ?_).trans ?_
  · rintro ⟨⟨a, b⟩, c⟩ h
    simp only [whiskerRight_apply, whiskerLeft_apply, coev, ev]
    by_cases hc : i = c
    · subst hc
      by_cases ha : a = k
      · subst ha
        have hb : e a ≠ b := fun hb ↦ h (by rw [hb])
        simp [hb]
      · simp [ha]
    · simp [hc]
  · simp only [whiskerRight_apply, whiskerLeft_apply, coev, ev]
    by_cases hik : i = k
    · subst hik
      simp
    · simp [hik, Ne.symm hik]

/-- The zigzag identity on `N`, entrywise: only the summand of `(N ⊗ M) ⊗ N` indexed by
`((e b, b), l)` contributes to the entry at `((e b, u), (u', l))`, and there the zigzag identity
of `C` applies. -/
private theorem whiskerLeft_coev_comp_ev_whiskerRight :
    N ◁ coev e p ≫ (α_ N M N).inv ≫ ev e p ▷ N = (ρ_ N).hom ≫ (λ_ N).inv := by
  ext ⟨j, u⟩ ⟨u', l⟩
  obtain ⟨b, rfl⟩ := e.surjective j
  rw [← Category.assoc, comp_apply, rightUnitor_hom_comp_apply, ← Category.id_comp (λ_ N).inv,
    comp_leftUnitor_inv_apply]
  simp only [comp_associator_inv_apply]
  refine (Fintype.sum_eq_single ((e b, b), l) ?_).trans ?_
  · rintro ⟨⟨a, b'⟩, c⟩ h
    simp only [whiskerRight_apply, whiskerLeft_apply, coev, ev]
    by_cases ha : e b = a
    · subst ha
      by_cases hc : c = l
      · subst hc
        have hb : e b ≠ e b' := fun hb ↦ h (by rw [e.injective hb])
        simp [hb]
      · simp [hc]
    · simp [ha]
  · simp only [whiskerRight_apply, whiskerLeft_apply, coev, ev]
    by_cases hl : e b = l
    · subst hl
      simp
    · simp [hl]

/-- An equivalence `e : M.ι ≃ N.ι` of index types, together with exact pairings of the summands
`M.X i` and `N.X (e i)`, induces an exact pairing of `M` and `N` in `Mat_ C`. Its coevaluation and
evaluation are the diagonal matrices of the coevaluations and evaluations of the summands
(`Mat_.exactPairing_coevaluation_apply`, `Mat_.exactPairing_evaluation_apply`). -/
@[instance_reducible]
noncomputable def exactPairing : ExactPairing M N where
  coevaluation' := coev e p
  evaluation' := ev e p
  coevaluation_evaluation' := whiskerLeft_coev_comp_ev_whiskerRight e p
  evaluation_coevaluation' := coev_whiskerRight_comp_whiskerLeft_ev e p

/-- The entries of the coevaluation of `Mat_.exactPairing`: the coevaluations of the summands on
the diagonal `j = e i`, and zero elsewhere. -/
@[simp]
theorem exactPairing_coevaluation_apply (u : (𝟙_ (Mat_ C)).ι) (q : M.ι × N.ι) :
    (@ExactPairing.coevaluation _ _ _ M N (exactPairing e p)) u q =
      η_ (M.X q.1) (N.X (e q.1)) ≫ M.X q.1 ◁ (𝟙 N : N ⟶ N) (e q.1) q.2 :=
  (rfl)

/-- The entries of the evaluation of `Mat_.exactPairing`: the evaluations of the summands on the
diagonal `j = e i`, and zero elsewhere. -/
@[simp]
theorem exactPairing_evaluation_apply (q : N.ι × M.ι) (u : (𝟙_ (Mat_ C)).ι) :
    (@ExactPairing.evaluation _ _ _ M N (exactPairing e p)) q u =
      (𝟙 N : N ⟶ N) q.1 (e q.2) ▷ M.X q.2 ≫ ε_ (M.X q.2) (N.X (e q.2)) :=
  (rfl)

end ExactPairing

-- The dual objects are exposed so that the projection lemmas below are `rfl` lemmas, usable by
-- `dsimp` to rewrite duals occurring inside the types of morphisms.
@[expose] section Duals

/-- The right dual of a family `M` is the family `i ↦ (M.X i)ᘁ` of right duals of its summands. -/
noncomputable instance instHasRightDual (M : Mat_ C) [∀ i, HasRightDual (M.X i)] :
    HasRightDual M where
  rightDual := ⟨M.ι, fun i ↦ (M.X i)ᘁ⟩
  exact := exactPairing (Equiv.refl M.ι) fun _ ↦ HasRightDual.exact

/-- The right dual of `M` is indexed by the index type of `M`. -/
@[simp]
theorem rightDual_ι (M : Mat_ C) [∀ i, HasRightDual (M.X i)] : (Mᘁ).ι = M.ι :=
  rfl

/-- The summands of the right dual of `M` are the right duals of the summands of `M`. -/
@[simp]
theorem rightDual_X (M : Mat_ C) [∀ i, HasRightDual (M.X i)] (i : M.ι) : (Mᘁ).X i = (M.X i)ᘁ :=
  rfl

/-- The entries of the coevaluation of the right dual of `M`: the coevaluations of the summands on
the diagonal, and zero elsewhere. -/
@[simp]
theorem coevaluation_rightDual_apply (M : Mat_ C) [∀ i, HasRightDual (M.X i)]
    (u : (𝟙_ (Mat_ C)).ι) (q : M.ι × M.ι) :
    (η_ M Mᘁ) u q = η_ (M.X q.1) (M.X q.1)ᘁ ≫ M.X q.1 ◁ (𝟙 Mᘁ : Mᘁ ⟶ Mᘁ) q.1 q.2 :=
  (rfl)

/-- The entries of the evaluation of the right dual of `M`: the evaluations of the summands on the
diagonal, and zero elsewhere. -/
@[simp]
theorem evaluation_rightDual_apply (M : Mat_ C) [∀ i, HasRightDual (M.X i)] (q : M.ι × M.ι)
    (u : (𝟙_ (Mat_ C)).ι) :
    (ε_ M Mᘁ) q u = (𝟙 Mᘁ : Mᘁ ⟶ Mᘁ) q.1 q.2 ▷ M.X q.2 ≫ ε_ (M.X q.2) (M.X q.2)ᘁ :=
  (rfl)

/-- The left dual of a family `M` is the family `i ↦ ᘁ(M.X i)` of left duals of its summands. -/
noncomputable instance instHasLeftDual (M : Mat_ C) [∀ i, HasLeftDual (M.X i)] :
    HasLeftDual M where
  leftDual := ⟨M.ι, fun i ↦ ᘁ(M.X i)⟩
  exact := exactPairing (N := M) (Equiv.refl M.ι) fun _ ↦ HasLeftDual.exact

/-- The left dual of `M` is indexed by the index type of `M`. -/
@[simp]
theorem leftDual_ι (M : Mat_ C) [∀ i, HasLeftDual (M.X i)] : (ᘁM : Mat_ C).ι = M.ι :=
  rfl

/-- The summands of the left dual of `M` are the left duals of the summands of `M`. -/
@[simp]
theorem leftDual_X (M : Mat_ C) [∀ i, HasLeftDual (M.X i)] (i : M.ι) :
    (ᘁM : Mat_ C).X i = (ᘁ(M.X i) : C) :=
  rfl

/-- The entries of the coevaluation of the left dual of `M`: the coevaluations of the summands on
the diagonal, and zero elsewhere. -/
@[simp]
theorem coevaluation_leftDual_apply (M : Mat_ C) [∀ i, HasLeftDual (M.X i)]
    (u : (𝟙_ (Mat_ C)).ι) (q : M.ι × M.ι) :
    (η_ (ᘁM) M) u q = η_ (ᘁ(M.X q.1) : C) (M.X q.1) ≫ (ᘁ(M.X q.1) : C) ◁ (𝟙 M : M ⟶ M) q.1 q.2 :=
  (rfl)

/-- The entries of the evaluation of the left dual of `M`: the evaluations of the summands on the
diagonal, and zero elsewhere. -/
@[simp]
theorem evaluation_leftDual_apply (M : Mat_ C) [∀ i, HasLeftDual (M.X i)] (q : M.ι × M.ι)
    (u : (𝟙_ (Mat_ C)).ι) :
    (ε_ (ᘁM) M) q u = (𝟙 M : M ⟶ M) q.1 q.2 ▷ (ᘁ(M.X q.2) : C) ≫ ε_ (ᘁ(M.X q.2) : C) (M.X q.2) :=
  (rfl)

/-- The matrix category of a right rigid monoidal preadditive category is right rigid. -/
noncomputable instance instRightRigidCategory [RightRigidCategory C] :
    RightRigidCategory (Mat_ C) where

/-- The matrix category of a left rigid monoidal preadditive category is left rigid. -/
noncomputable instance instLeftRigidCategory [LeftRigidCategory C] :
    LeftRigidCategory (Mat_ C) where

/-- The matrix category of a rigid monoidal preadditive category is rigid. -/
noncomputable instance instRigidCategory [RigidCategory C] : RigidCategory (Mat_ C) where

end Duals

/-- The right adjoint mate of a matrix is the transpose of the matrix of right adjoint mates of
its entries. -/
@[simp]
theorem rightAdjointMate_apply {M N : Mat_ C} [∀ i, HasRightDual (M.X i)]
    [∀ j, HasRightDual (N.X j)] (f : M ⟶ N) (j : N.ι) (i : M.ι) : (fᘁ) j i = (f i j)ᘁ := by
  let g : Nᘁ ⟶ Mᘁ := fun j i ↦ (f i j)ᘁ
  suffices h : fᘁ = g by rw [h]
  -- Both sides are determined by their evaluation against `M`. The evaluations of `Mat_ C` are
  -- diagonal, so each entry of either evaluated side has a single nonzero term, and these agree
  -- by the defining property of the right adjoint mates of the entries.
  refine rightHom_ext (X := M) (Y := Mᘁ) ?_
  rw [rightAdjointMate_comp_evaluation]
  ext ⟨j, i⟩ u
  rw [comp_apply, comp_apply]
  simp only [whiskerRight_apply, whiskerLeft_apply, evaluation_rightDual_apply]
  refine (Fintype.sum_eq_single (j, j) ?_).trans
    (Eq.trans ?_ (Fintype.sum_eq_single (i, i) ?_).symm)
  · rintro ⟨a, b⟩ h
    by_cases ha : j = a
    · subst ha
      simp [show j ≠ b by rintro rfl; exact h rfl]
    · simp [ha]
  · simp [g, rightAdjointMate_comp_evaluation]
  · rintro ⟨a, b⟩ h
    by_cases hb : i = b
    · subst hb
      simp [show a ≠ i by rintro rfl; exact h rfl]
    · simp [hb]

/-- The left adjoint mate of a matrix is the transpose of the matrix of left adjoint mates of its
entries. -/
@[simp]
theorem leftAdjointMate_apply {M N : Mat_ C} [∀ i, HasLeftDual (M.X i)]
    [∀ j, HasLeftDual (N.X j)] (f : M ⟶ N) (j : N.ι) (i : M.ι) : (ᘁf) j i = ᘁ(f i j) := by
  let g : (ᘁN : Mat_ C) ⟶ ᘁM := fun j i ↦ ᘁ(f i j)
  suffices h : leftAdjointMate f = g by rw [h]
  -- Both sides are determined by their evaluation against `M`. The evaluations of `Mat_ C` are
  -- diagonal, so each entry of either evaluated side has a single nonzero term, and these agree
  -- by the defining property of the left adjoint mates of the entries.
  refine leftDualHom_ext (X := (ᘁM : Mat_ C)) (Y := M) ?_
  rw [leftAdjointMate_comp_evaluation]
  ext ⟨i, j⟩ u
  rw [comp_apply, comp_apply]
  simp only [whiskerRight_apply, whiskerLeft_apply, evaluation_leftDual_apply]
  refine (Fintype.sum_eq_single (j, j) ?_).trans
    (Eq.trans ?_ (Fintype.sum_eq_single (i, i) ?_).symm)
  · rintro ⟨a, b⟩ h
    by_cases hb : j = b
    · subst hb
      simp [show a ≠ j by rintro rfl; exact h rfl]
    · simp [hb]
  · simp [g, leftAdjointMate_comp_evaluation]
  · rintro ⟨a, b⟩ h
    by_cases ha : i = a
    · subst ha
      simp [show i ≠ b by rintro rfl; exact h rfl]
    · simp [ha]

end CategoryTheory.Mat_
