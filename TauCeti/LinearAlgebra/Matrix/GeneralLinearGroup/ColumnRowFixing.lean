/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Affine
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InverseTranspose

/-!
# General linear groups fixing standard columns and rows

The subgroup `columnRowFixingSubgroup R P Q` consists of invertible matrices fixing the
standard columns indexed by `P` and the standard rows indexed by `Q`. Fixing additional
coordinates gives smaller subgroups; in particular, fixing the same set `P ∪ Q` on both sides
gives the square subgroup obtained by imposing the fewest additional row and column conditions.
These groups describe stabilizers of standard frames in the study of homological stability.

## References

* W. van der Kallen, *Homology stability for linear groups*, Invent. Math. **60** (1980),
  269–295, §3.2.
-/

public section

open Matrix

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (R : Type*) [Semiring R]

/-- The group `G^(P,Q)` of invertible matrices fixing the standard columns indexed by `P`
and the standard rows indexed by `Q`. -/
def columnRowFixingSubgroup (P Q : Set ι) : Subgroup (GL ι R) where
  carrier := {g | (g : Matrix ι ι R) * (1 : Matrix ι ι R).submatrix id (Subtype.val : P → ι) =
      (1 : Matrix ι ι R).submatrix id Subtype.val ∧
    (1 : Matrix ι ι R).submatrix (Subtype.val : Q → ι) id * (g : Matrix ι ι R) =
      (1 : Matrix ι ι R).submatrix Subtype.val id}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq, Units.val_mul] at hg hh ⊢
    exact ⟨by rw [Matrix.mul_assoc, hh.1, hg.1], by rw [← Matrix.mul_assoc, hg.2, hh.2]⟩
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    exact ⟨by simpa [← Matrix.mul_assoc] using
      congrArg (((g⁻¹ : GL ι R) : Matrix ι ι R) * ·) hg.1.symm,
      by simpa [Matrix.mul_assoc] using
        congrArg (· * ((g⁻¹ : GL ι R) : Matrix ι ι R)) hg.2.symm⟩

variable {R} {P Q P' Q' : Set ι} {g : GL ι R}

/-- On the specified columns and rows, membership requires exactly the entries of the identity
matrix. -/
theorem mem_columnRowFixingSubgroup_iff : g ∈ columnRowFixingSubgroup R P Q ↔
    (∀ j ∈ P, ∀ i, (g : Matrix ι ι R) i j = (1 : Matrix ι ι R) i j) ∧
    (∀ i ∈ Q, ∀ j, (g : Matrix ι ι R) i j = (1 : Matrix ι ι R) i j) := by
  simp only [columnRowFixingSubgroup, Subgroup.mem_mk, Submonoid.mem_mk,
    Subsemigroup.mem_mk, Set.mem_ofPred_eq]
  simp only [← @Equiv.coe_refl ι, mul_submatrix_one, one_submatrix_mul, Equiv.refl_symm]
  simp only [Equiv.coe_refl, Function.id_comp, ← Matrix.ext_iff, Matrix.submatrix_apply, id_eq]
  rw [forall_comm (α := ι) (β := P)]
  simp only [Subtype.forall]
  rfl

/-- Adding fixed columns and rows gives a smaller subgroup. -/
theorem columnRowFixingSubgroup_le (hP : P ⊆ P') (hQ : Q ⊆ Q') :
    columnRowFixingSubgroup R P' Q' ≤ columnRowFixingSubgroup R P Q := by
  intro g hg
  obtain ⟨hc, hr⟩ := mem_columnRowFixingSubgroup_iff.mp hg
  exact mem_columnRowFixingSubgroup_iff.mpr
    ⟨fun j hj ↦ hc j (hP hj), fun i hi ↦ hr i (hQ hi)⟩

/-- With neither rows nor columns prescribed, the group is all of `GL`. -/
@[simp]
theorem columnRowFixingSubgroup_empty_empty :
    columnRowFixingSubgroup R (∅ : Set ι) ∅ = ⊤ := by
  ext g
  simp [mem_columnRowFixingSubgroup_iff]

/-- Fixing more columns and rows intersects the corresponding subgroups. -/
theorem columnRowFixingSubgroup_union (P Q P' Q' : Set ι) :
    columnRowFixingSubgroup R (P ∪ P') (Q ∪ Q') =
      columnRowFixingSubgroup R P Q ⊓ columnRowFixingSubgroup R P' Q' := by
  ext g
  simp only [Subgroup.mem_inf, mem_columnRowFixingSubgroup_iff, Set.mem_union,
    or_imp, forall_and]
  tauto

/-- Fixing every column forces the matrix to be the identity. -/
@[simp]
theorem columnRowFixingSubgroup_univ_left (Q : Set ι) :
    columnRowFixingSubgroup R Set.univ Q = ⊥ := by
  refine eq_bot_iff.mpr fun g hg ↦ Subgroup.mem_bot.mpr (Units.ext (Matrix.ext fun i j ↦ ?_))
  exact (mem_columnRowFixingSubgroup_iff.mp hg).1 j (Set.mem_univ _) i

/-- Fixing every row forces the matrix to be the identity. -/
@[simp]
theorem columnRowFixingSubgroup_univ_right (P : Set ι) :
    columnRowFixingSubgroup R P Set.univ = ⊥ := by
  refine eq_bot_iff.mpr fun g hg ↦ Subgroup.mem_bot.mpr (Units.ext (Matrix.ext fun i j ↦ ?_))
  exact (mem_columnRowFixingSubgroup_iff.mp hg).2 i (Set.mem_univ _) j

/-- Fixing `P ∪ Q` on both sides gives the square subgroup of `G^(P,Q)`. -/
theorem columnRowFixingSubgroup_square_le :
    columnRowFixingSubgroup R (P ∪ Q) (P ∪ Q) ≤ columnRowFixingSubgroup R P Q :=
  columnRowFixingSubgroup_le Set.subset_union_left Set.subset_union_right

section Square

variable {A : Type*} [Ring A] {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- In block coordinates, prescribing the standard columns of the second summand gives the
lower block triangular affine group. -/
theorem columnRowFixingSubgroup_range_inr_empty :
    columnRowFixingSubgroup A (Set.range (Sum.inr : b → a ⊕ b)) ∅ = affineGroup A a b := by
  ext g
  simp only [mem_columnRowFixingSubgroup_iff, Set.notMem_empty, false_implies, implies_true,
    and_true, Set.forall_mem_range, mem_affineGroup_iff]
  constructor
  · intro h
    exact ⟨Matrix.ext fun i j ↦ by simpa [Matrix.toBlocks₁₂] using h j (Sum.inl i),
      Matrix.ext fun i j ↦ by simpa [Matrix.toBlocks₂₂, Matrix.one_apply] using h j (Sum.inr i)⟩
  · rintro ⟨h₁₂, h₂₂⟩ j (i | i)
    · simpa [Matrix.toBlocks₁₂] using Matrix.ext_iff.mpr h₁₂ i j
    · simpa [Matrix.toBlocks₂₂, Matrix.one_apply] using Matrix.ext_iff.mpr h₂₂ i j

private theorem reindexGL_eq_affineInclusion_of_mem_square (e : ι ≃ a ⊕ b) {g : GL ι A}
    (hg : g ∈ columnRowFixingSubgroup A (Set.range (e.symm ∘ Sum.inr))
      (Set.range (e.symm ∘ Sum.inr))) :
    ∃ u : GL a A, e.reindexGL A g = (affineInclusion A a b u : GL (a ⊕ b) A) := by
  obtain ⟨hc, hr⟩ := mem_columnRowFixingSubgroup_iff.mp hg
  have hcol : e.reindexGL A g ∈ affineGroup A a b := by
    rw [← columnRowFixingSubgroup_range_inr_empty, mem_columnRowFixingSubgroup_iff]
    refine ⟨?_, by simp⟩
    rintro _ ⟨j, rfl⟩ i
    simpa [Matrix.one_apply, e.symm.injective.eq_iff] using
      hc (e.symm (Sum.inr j)) (Set.mem_range_self (f := e.symm ∘ Sum.inr) j) (e.symm i)
  let M : affineGroup A a b := ⟨e.reindexGL A g, hcol⟩
  refine ⟨affineProjection A a b M, Units.ext ?_⟩
  rw [coe_affineInclusion, coe_affineProjection]
  have hzero : (e.reindexGL A g : Matrix (a ⊕ b) (a ⊕ b) A).toBlocks₂₁ = 0 := by
    ext i j
    simpa [Matrix.toBlocks₂₁, Matrix.one_apply, e.symm.injective.eq_iff] using
      hr (e.symm (Sum.inr i)) (Set.mem_range_self (f := e.symm ∘ Sum.inr) i) (e.symm (Sum.inl j))
  conv_lhs => rw [coe_eq_fromBlocks_of_mem_affineGroup hcol, hzero]

/-- For a coordinate splitting `ι ≃ a ⊕ b`, the subgroup fixing all rows and columns of the
second summand is isomorphic to `GL a A`. Taking the splitting by a set and its complement
identifies the square subgroup with the general linear group on the unfixed coordinates. -/
noncomputable def columnRowFixingSubgroupSquareEquiv (e : ι ≃ a ⊕ b) : GL a A ≃*
    columnRowFixingSubgroup A (Set.range (e.symm ∘ Sum.inr)) (Set.range (e.symm ∘ Sum.inr)) :=
  MulEquiv.ofBijective
    (((e.symm.reindexGL A).toMonoidHom.comp
      ((affineGroup A a b).subtype.comp (affineInclusion A a b))).codRestrict _ (by
        intro u
        rw [mem_columnRowFixingSubgroup_iff]
        refine ⟨?_, ?_⟩
        · rintro _ ⟨j, rfl⟩ i
          obtain ⟨i, rfl⟩ := e.symm.surjective i
          cases i <;> simp [Function.comp_def, Matrix.one_apply, e.symm.injective.eq_iff]
        · rintro _ ⟨i, rfl⟩ j
          obtain ⟨j, rfl⟩ := e.symm.surjective j
          cases j <;> simp [Function.comp_def, Matrix.one_apply, e.symm.injective.eq_iff]))
    ⟨fun _ _ h ↦ affineInclusion_injective A a b (Subtype.ext
        ((e.symm.reindexGL A).injective (congrArg Subtype.val h))),
      fun g ↦ by
        obtain ⟨u, hu⟩ := reindexGL_eq_affineInclusion_of_mem_square e g.property
        exact ⟨u, Subtype.ext (by simp [← hu])⟩⟩

/-- The square-group isomorphism inserts the identity on the fixed summand. -/
@[simp]
theorem coe_columnRowFixingSubgroupSquareEquiv (e : ι ≃ a ⊕ b) (u : GL a A) :
    (columnRowFixingSubgroupSquareEquiv e u : GL ι A) =
      e.symm.reindexGL A (fromBlocksGL (u, 1)) := by
  simp [columnRowFixingSubgroupSquareEquiv, MulEquiv.ofBijective_apply,
    affineInclusion_eq_fromBlocksGL]

/-- The inverse of the square-group isomorphism takes the block on the unfixed coordinates. -/
@[simp]
theorem coe_columnRowFixingSubgroupSquareEquiv_symm (e : ι ≃ a ⊕ b)
    (g : columnRowFixingSubgroup A (Set.range (e.symm ∘ Sum.inr)) (Set.range (e.symm ∘ Sum.inr))) :
    ((columnRowFixingSubgroupSquareEquiv e).symm g : Matrix a a A) =
      ((g : GL ι A) : Matrix ι ι A).submatrix (e.symm ∘ Sum.inl) (e.symm ∘ Sum.inl) := by
  obtain ⟨u, rfl⟩ := (columnRowFixingSubgroupSquareEquiv (A := A) e).surjective g
  rw [MulEquiv.symm_apply_apply, coe_columnRowFixingSubgroupSquareEquiv]
  ext i j
  simp [Function.comp_def]

end Square

section Stabilization

variable {A : Type*} [Ring A] {m n : ℕ} (h : m ≤ n) {P Q : Set (Fin m)}

/-- Stabilization preserves and reflects the fixed-column and fixed-row conditions, using the
initial-coordinate embedding of `Fin m` into `Fin n`. -/
@[simp]
theorem stabilizeGL_mem_columnRowFixingSubgroup_iff {g : GL (Fin m) A} :
    stabilizeGL A h g ∈ columnRowFixingSubgroup A (Fin.castLE h '' P) (Fin.castLE h '' Q) ↔
      g ∈ columnRowFixingSubgroup A P Q := by
  simp only [mem_columnRowFixingSubgroup_iff, Set.forall_mem_image]
  constructor
  · rintro ⟨hc, hr⟩
    refine ⟨fun j hj i ↦ ?_, fun i hi j ↦ ?_⟩
    · simpa [coe_stabilizeGL_apply, i.isLt, j.isLt, Matrix.one_apply, Fin.ext_iff] using
        hc hj (Fin.castLE h i)
    · simpa [coe_stabilizeGL_apply, i.isLt, j.isLt, Matrix.one_apply, Fin.ext_iff] using
        hr hi (Fin.castLE h j)
  · rintro ⟨hc, hr⟩
    refine ⟨fun j hj i ↦ ?_, fun i hi j ↦ ?_⟩
    · by_cases hi : i.val < m
      · simpa [coe_stabilizeGL_apply, hi, j.isLt, Matrix.one_apply, Fin.ext_iff] using
          hc j hj ⟨i, hi⟩
      · simp [coe_stabilizeGL_apply, hi]
    · by_cases hj : j.val < m
      · simpa [coe_stabilizeGL_apply, i.isLt, hj, Matrix.one_apply, Fin.ext_iff] using
          hr i hi ⟨j, hj⟩
      · simp [coe_stabilizeGL_apply, hj]

/-- The upper inclusion of the van der Kallen subgroups, extending a matrix by the identity on
new coordinates. -/
noncomputable def columnRowFixingStabilization : columnRowFixingSubgroup A P Q →*
    columnRowFixingSubgroup A (Fin.castLE h '' P) (Fin.castLE h '' Q) :=
  ((stabilizeGL A h).comp (columnRowFixingSubgroup A P Q).subtype).codRestrict _
    fun g ↦ (stabilizeGL_mem_columnRowFixingSubgroup_iff h).mpr g.property

/-- The restricted stabilization acts by the ambient block-diagonal inclusion. -/
@[simp]
theorem coe_columnRowFixingStabilization (g : columnRowFixingSubgroup A P Q) :
    (columnRowFixingStabilization h g : GL (Fin n) A) = stabilizeGL A h g :=
  (rfl)

/-- The upper inclusion is injective. -/
theorem columnRowFixingStabilization_injective :
    Function.Injective (columnRowFixingStabilization h (A := A) (P := P) (Q := Q)) := by
  intro g k hk
  exact Subtype.ext (stabilizeGL_injective h (congrArg Subtype.val hk))

end Stabilization

section Stabilizer

variable {A : Type*} [CommRing A] {P Q : Set ι} {κ : Type*} (e : κ → ι)

/-- The stabilizer of standard columns with indices in the image of `e` inside `G^(P,Q)` fixes
precisely the additional columns indexed by `Set.range e`. -/
theorem stabilizer_standardColumns :
    MulAction.stabilizer (columnRowFixingSubgroup A P Q) ((1 : Matrix ι ι A).submatrix id e) =
      (columnRowFixingSubgroup A (P ∪ Set.range e) Q).comap
        (columnRowFixingSubgroup A P Q).subtype := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, GeneralLinearGroup.smul_def,
    Subgroup.mem_comap, Subgroup.subtype_apply, mem_columnRowFixingSubgroup_iff]
  obtain ⟨hc, hr⟩ := mem_columnRowFixingSubgroup_iff.mp g.property
  simp only [← @Equiv.coe_refl ι, mul_submatrix_one, Equiv.refl_symm]
  simp only [Equiv.coe_refl, Function.id_comp, ← Matrix.ext_iff, submatrix_apply, id_eq]
  exact ⟨fun hg ↦ ⟨fun j hj i ↦ hj.elim (fun hj ↦ hc j hj i)
    (fun ⟨k, hk⟩ ↦ hk ▸ hg i k), hr⟩, fun hg i k ↦ hg.1 (e k) (Or.inr ⟨k, rfl⟩) i⟩

/-- On the transposed standard rows, use the contragredient action `g ↦ (g⁻¹)ᵀ`.
Their stabilizer inside `G^(P,Q)` fixes the additional standard rows indexed by `Set.range e`. -/
theorem stabilizer_standardRows :
    (MulAction.stabilizer (GL ι A) ((1 : Matrix ι ι A).submatrix id e)).comap
        (GeneralLinearGroup.inverseTranspose.toMonoidHom.comp
          (columnRowFixingSubgroup A P Q).subtype) =
      (columnRowFixingSubgroup A P (Q ∪ Set.range e)).comap
        (columnRowFixingSubgroup A P Q).subtype := by
  ext g
  rw [Subgroup.mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAction.mem_stabilizer_iff, Subgroup.mem_comap, Subgroup.subtype_apply,
    mem_columnRowFixingSubgroup_iff]
  let E := (1 : Matrix ι ι A).submatrix id e
  have hinv : GeneralLinearGroup.inverseTranspose (g : GL ι A) • E = E ↔
      GeneralLinearGroup.inverseTranspose ((g : GL ι A)⁻¹) • E = E := by
    rw [map_inv, inv_smul_eq_iff, eq_comm (a := E)]
  rw [hinv, GeneralLinearGroup.smul_def, GeneralLinearGroup.coe_inverseTranspose, inv_inv]
  simp only [E, ← @Equiv.coe_refl ι, mul_submatrix_one, Equiv.refl_symm]
  simp only [Equiv.coe_refl, Function.id_comp, ← Matrix.ext_iff, submatrix_apply, id_eq,
    Matrix.transpose_apply]
  obtain ⟨hc, hr⟩ := mem_columnRowFixingSubgroup_iff.mp g.property
  constructor
  · intro hg
    refine ⟨hc, fun i hi j ↦ hi.elim (fun h ↦ hr i h j) ?_⟩
    rintro ⟨k, rfl⟩
    simpa [Matrix.one_apply, eq_comm] using hg j k
  · intro hg j k
    simpa [Matrix.one_apply, eq_comm] using hg.2 (e k) (Or.inr (Set.mem_range_self k)) j

end Stabilizer

end TauCeti
