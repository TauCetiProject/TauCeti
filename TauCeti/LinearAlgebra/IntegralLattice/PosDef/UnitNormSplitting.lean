/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.Isometry
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Finite
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Gram
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.RepresentationNumber
public import TauCeti.LinearAlgebra.IntegralLattice.Unit

/-!
# Splitting off the vectors of norm one

Let `L` be a positive definite integral lattice. Two vectors of norm one are either equal up to
sign or orthogonal, since `B(x ∓ y, x ∓ y) = 2 ∓ 2 B(x, y)` is positive unless `x = ±y`. Choosing
one vector from each pair `±x` therefore gives an orthonormal basis of the sublattice `U` spanned
by the vectors of norm one, so `U` is a copy of the standard lattice `I_k`. Its pairing is perfect,
so it splits off orthogonally:

```text
L ≅ I_k ⊕ U^⊥,   2k = #{x ∈ L : B(x, x) = 1},
```

and the complement `U^⊥` has no vector of norm one, because such a vector would lie in `U` and be
orthogonal to itself. The complement is positive definite, has the same determinant as `L`, and is
unimodular exactly when `L` is. This is the first reduction in the classification of positive
definite unimodular lattices of small rank: every such lattice is `I_k` plus a lattice without
vectors of norm one.

The splitting is canonical. An isometry `L ≅ M` restricts to an isometry of the complements, and a
lattice of the form `I_ι ⊕ N`, with `N` positive definite without vectors of norm one, has
complement isometric to `N`. Hence `I_ι ⊕ N ≅ I_κ ⊕ N'` with `N`, `N'` positive definite without
vectors of norm one forces `#ι = #κ` and `N ≅ N'`.

## Main declarations

* `TauCeti.IntegralLattice.unitNormSubmodule`: the span of the vectors of norm one.
* `TauCeti.IntegralLattice.unitNormComplement`: its orthogonal complement, as an integral lattice.
* `TauCeti.IntegralLattice.IsPosDef.unitNormBasis`: an orthonormal basis of the unit-norm
  sublattice of a positive definite lattice.
* `TauCeti.IntegralLattice.IsPosDef.unitNormDecomposition`: the isometry
  `I_k ⊕ unitNormComplement L ≅ L`.
* `TauCeti.IntegralLattice.vectorsOfNorm_one_unitNormComplement`: the complement has no vector of
  norm one.
* `TauCeti.IntegralLattice.IsPosDef.two_mul_finrank_unitNormSubmodule`: `2k` is the number of
  vectors of norm one.
* `TauCeti.IntegralLattice.Isometry.unitNormComplement`: isometric lattices have isometric
  complements.
* `TauCeti.IntegralLattice.nonempty_isometry_of_isometry_orthogonalSum_unitLattice` and
  `TauCeti.IntegralLattice.card_eq_of_isometry_orthogonalSum_unitLattice`: cancellation of
  standard summands against lattices without vectors of norm one.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §82.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 16.
-/

public section

open Module TensorProduct

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

/-- The **unit-norm sublattice** of an integral lattice: the span of its vectors of norm one. -/
noncomputable def unitNormSubmodule : Submodule ℤ L :=
  Submodule.span ℤ (L.vectorsOfNorm 1)

/-- Every vector of norm one lies in the unit-norm sublattice. -/
theorem vectorsOfNorm_one_subset_unitNormSubmodule :
    L.vectorsOfNorm 1 ⊆ L.unitNormSubmodule :=
  Submodule.subset_span

/-- The unit-norm sublattice is the least submodule containing the vectors of norm one. -/
theorem unitNormSubmodule_le_iff {p : Submodule ℤ L} :
    L.unitNormSubmodule ≤ p ↔ L.vectorsOfNorm 1 ⊆ p :=
  Submodule.span_le

/-- The orthogonal complement of the unit-norm sublattice, as an integral lattice in its own
rational span. -/
noncomputable def unitNormComplement :
    IntegralLattice (ℚ ⊗[ℤ] L.integralForm.orthogonal L.unitNormSubmodule) :=
  ofIntegralForm (L.integralForm.restrict (L.integralForm.orthogonal L.unitNormSubmodule))
    (L.isSymm_integralForm.restrict _)

/-- The canonical identification of the orthogonal complement of the unit-norm sublattice with
the carrier of `unitNormComplement`. -/
noncomputable def unitNormComplementEquiv :
    L.integralForm.orthogonal L.unitNormSubmodule ≃ₗ[ℤ] L.unitNormComplement :=
  ofIntegralForm.carrierEquiv _ _

/-- The identification `unitNormComplementEquiv` sends `x` to the pure tensor `1 ⊗ x`. -/
@[simp]
theorem coe_unitNormComplementEquiv_apply (x : L.integralForm.orthogonal L.unitNormSubmodule) :
    (L.unitNormComplementEquiv x : ℚ ⊗[ℤ] L.integralForm.orthogonal L.unitNormSubmodule) =
      1 ⊗ₜ[ℤ] x :=
  ofIntegralForm.coe_carrierEquiv_apply _ _ x

/-- The identification `unitNormComplementEquiv` preserves the integral forms. -/
@[simp]
theorem integralForm_unitNormComplementEquiv (x y : L.integralForm.orthogonal L.unitNormSubmodule) :
    L.unitNormComplement.integralForm (L.unitNormComplementEquiv x)
      (L.unitNormComplementEquiv y) = L.integralForm x y :=
  ofIntegralForm.integralForm_carrierEquiv _ _ x y

/-- **The complement of the unit-norm sublattice has no vector of norm one.** -/
@[simp]
theorem vectorsOfNorm_one_unitNormComplement : L.unitNormComplement.vectorsOfNorm 1 = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun y hy ↦ ?_
  obtain ⟨t, rfl⟩ := L.unitNormComplementEquiv.surjective y
  rw [mem_vectorsOfNorm_one_iff, integralForm_unitNormComplementEquiv] at hy
  have hmem : (t : L) ∈ L.unitNormSubmodule :=
    L.vectorsOfNorm_one_subset_unitNormSubmodule ((L.mem_vectorsOfNorm_one_iff).2 hy)
  have h0 := LinearMap.BilinForm.mem_orthogonal_iff.1 t.2 _ hmem
  omega

variable {L}

namespace IsPosDef

variable (hL : L.IsPosDef)
include hL

/-- **Vectors of norm one in a positive definite lattice are equal up to sign or orthogonal.** -/
theorem integralForm_eq_zero_of_mem_vectorsOfNorm_one {x y : L}
    (hx : x ∈ L.vectorsOfNorm 1) (hy : y ∈ L.vectorsOfNorm 1) (hxy : y ≠ x) (hxy' : y ≠ -x) :
    L.integralForm x y = 0 := by
  rw [mem_vectorsOfNorm_one_iff] at hx hy
  have hsub := hL.posDef_integralNorm (x - y) (sub_ne_zero.2 hxy.symm)
  have hadd := hL.posDef_integralNorm (x + y) fun h ↦ hxy' (eq_neg_of_add_eq_zero_right h)
  rw [integralNorm_sub, integralNorm_apply, integralNorm_apply, hx, hy] at hsub
  rw [integralNorm_add, integralNorm_apply, integralNorm_apply, hx, hy] at hadd
  omega

end IsPosDef

/-! ### An orthonormal basis of the unit-norm sublattice -/

section Basis

variable (L) in
/-- Vectors of norm one up to sign. -/
private def signSetoid : Setoid (L.vectorsOfNorm 1) where
  r x y := (x : L) = y ∨ (x : L) = -y
  iseqv :=
    { refl := fun _ ↦ Or.inl rfl
      symm := fun h ↦ h.elim (fun h ↦ Or.inl h.symm) fun h ↦ Or.inr (by rw [h, neg_neg])
      trans := fun h₁ h₂ ↦ by
        rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> simp [h₁, h₂] }

variable (L) in
/-- The chosen representative of a pair `±x` of vectors of norm one. -/
private noncomputable def signRep (q : Quotient (signSetoid L)) : L :=
  (Quotient.out q : L.vectorsOfNorm 1)

private theorem signRep_mem (q : Quotient (signSetoid L)) : signRep L q ∈ L.vectorsOfNorm 1 :=
  (Quotient.out q).2

private theorem signRep_mk (x : L.vectorsOfNorm 1) :
    signRep L ⟦x⟧ = x ∨ signRep L ⟦x⟧ = -x :=
  Quotient.mk_out (s := signSetoid L) x

private theorem eq_of_signRep_eq_or {q r : Quotient (signSetoid L)}
    (h : signRep L q = signRep L r ∨ signRep L q = -signRep L r) : q = r := by
  rw [← Quotient.out_eq q, ← Quotient.out_eq r]
  exact Quotient.sound h

private theorem integralForm_signRep (hL : L.IsPosDef) [DecidableEq (Quotient (signSetoid L))]
    (q r : Quotient (signSetoid L)) :
    L.integralForm (signRep L q) (signRep L r) = if q = r then 1 else 0 := by
  split_ifs with h
  · subst h
    exact (L.mem_vectorsOfNorm_one_iff).1 (signRep_mem q)
  · refine hL.integralForm_eq_zero_of_mem_vectorsOfNorm_one (signRep_mem q) (signRep_mem r)
      (fun h' ↦ h (eq_of_signRep_eq_or (Or.inl h'.symm))) fun h' ↦ h ?_
    exact eq_of_signRep_eq_or (Or.inr (by rw [h', neg_neg]))

private theorem signRep_ne_neg (q : Quotient (signSetoid L)) : signRep L q ≠ -signRep L q :=
  fun h ↦ by
    have h1 := (L.mem_vectorsOfNorm_one_iff).1 (signRep_mem q)
    have h2 := congrArg (L.integralForm (signRep L q)) h
    rw [map_neg, h1] at h2
    omega

private theorem linearIndependent_signRep (hL : L.IsPosDef) :
    LinearIndependent ℤ (signRep L) := by
  classical
  rw [linearIndependent_iff']
  intro s w hs i hi
  have h := congrArg (fun y ↦ L.integralForm y (signRep L i)) hs
  simpa [integralForm_signRep hL, hi] using h

private theorem span_range_signRep :
    Submodule.span ℤ (Set.range (signRep L)) = L.unitNormSubmodule := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 fun x hx ↦ ?_)
  · rintro _ ⟨q, rfl⟩
    exact L.vectorsOfNorm_one_subset_unitNormSubmodule (signRep_mem q)
  · have hq : signRep L ⟦⟨x, hx⟩⟧ ∈ Submodule.span ℤ (Set.range (signRep L)) :=
      Submodule.subset_span ⟨_, rfl⟩
    rcases signRep_mk ⟨x, hx⟩ with h | h
    · rwa [h] at hq
    · rw [h] at hq
      simpa using Submodule.neg_mem _ hq

variable (hL : L.IsPosDef)
include hL

/-- The orthonormal basis of the unit-norm sublattice indexed by the pairs `±x` of vectors of
norm one. -/
private noncomputable def signBasis : Basis (Quotient (signSetoid L)) ℤ L.unitNormSubmodule :=
  (Basis.span (linearIndependent_signRep hL)).map (LinearEquiv.ofEq _ _ span_range_signRep)

private theorem coe_signBasis (q : Quotient (signSetoid L)) :
    (signBasis hL q : L) = signRep L q := by
  simp [signBasis, Basis.span_apply]

private theorem finrank_unitNormSubmodule_eq_natCard :
    finrank ℤ L.unitNormSubmodule = Nat.card (Quotient (signSetoid L)) :=
  finrank_eq_nat_card_basis (signBasis hL)

private noncomputable def signEquivFin :
    Quotient (signSetoid L) ≃ Fin (finrank ℤ L.unitNormSubmodule) :=
  have : Finite (L.vectorsOfNorm 1) := (hL.finite_vectorsOfNorm 1).to_subtype
  (Finite.equivFin _).trans (finCongr (finrank_unitNormSubmodule_eq_natCard hL).symm)

namespace IsPosDef

/-- **The unit-norm sublattice of a positive definite lattice has an orthonormal basis**, made of
one vector from each pair `±x` of vectors of norm one. -/
noncomputable def unitNormBasis :
    Basis (Fin (finrank ℤ L.unitNormSubmodule)) ℤ L.unitNormSubmodule :=
  (signBasis hL).reindex (signEquivFin hL)

/-- The vectors of `unitNormBasis` have norm one. -/
theorem unitNormBasis_mem_vectorsOfNorm (i : Fin (finrank ℤ L.unitNormSubmodule)) :
    (hL.unitNormBasis i : L) ∈ L.vectorsOfNorm 1 := by
  rw [unitNormBasis, Basis.reindex_apply, coe_signBasis]
  exact signRep_mem _

/-- The basis `unitNormBasis` is orthonormal. -/
theorem integralForm_unitNormBasis (i j : Fin (finrank ℤ L.unitNormSubmodule)) :
    L.integralForm (hL.unitNormBasis i) (hL.unitNormBasis j) = if i = j then 1 else 0 := by
  classical
  rw [unitNormBasis, Basis.reindex_apply, Basis.reindex_apply, coe_signBasis, coe_signBasis,
    integralForm_signRep hL]
  simp

/-- **Twice the rank of the unit-norm sublattice is the number of vectors of norm one.** -/
theorem two_mul_finrank_unitNormSubmodule :
    2 * finrank ℤ L.unitNormSubmodule = (L.vectorsOfNorm 1).ncard := by
  let f : Bool × Quotient (signSetoid L) → L.vectorsOfNorm 1 := fun p ↦
    if p.1 then ⟨signRep L p.2, signRep_mem p.2⟩
    else ⟨-signRep L p.2, (neg_mem_vectorsOfNorm_iff _).2 (signRep_mem p.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, q⟩ ⟨b, r⟩ hqr
      have hqr' := congrArg Subtype.val hqr
      cases a <;> cases b <;> simp only [f, Bool.false_eq_true, ↓reduceIte, neg_inj] at hqr'
      · rw [eq_of_signRep_eq_or (Or.inl hqr')]
      · have hq := eq_of_signRep_eq_or (Or.inr (neg_eq_iff_eq_neg.1 hqr'))
        subst hq
        exact (signRep_ne_neg q (neg_eq_iff_eq_neg.1 hqr')).elim
      · have hq := eq_of_signRep_eq_or (Or.inr hqr')
        subst hq
        exact (signRep_ne_neg q hqr').elim
      · rw [eq_of_signRep_eq_or (Or.inl hqr')]
    · rintro x
      rcases signRep_mk x with h | h
      · exact ⟨(true, ⟦x⟧), Subtype.ext (by simp [f, h])⟩
      · exact ⟨(false, ⟦x⟧), Subtype.ext (by simp [f, h])⟩
  rw [finrank_unitNormSubmodule_eq_natCard hL, ← Nat.card_coe_set_eq,
    ← Nat.card_eq_of_bijective f hf, Nat.card_prod]
  simp

/-- **The unit-norm sublattice of a positive definite lattice is unimodular**: its restricted
integral pairing is perfect. -/
theorem bijective_integralForm_restrict_unitNormSubmodule :
    Function.Bijective (L.integralForm.restrict L.unitNormSubmodule) := by
  classical
  have h : L.integralForm.restrict L.unitNormSubmodule = hL.unitNormBasis.toDual :=
    hL.unitNormBasis.ext fun i ↦ hL.unitNormBasis.ext fun j ↦ by
      rw [Basis.toDual_apply, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
        integralForm_unitNormBasis]
  rw [h]
  exact hL.unitNormBasis.toDualEquiv.bijective

end IsPosDef

end Basis

/-! ### The splitting -/

namespace IsPosDef

variable (hL : L.IsPosDef)
include hL

private theorem gramMatrix_unitLatticeBasis_eq :
    (unitLattice (Fin (finrank ℤ L.unitNormSubmodule))).gramMatrix (unitLatticeBasis _) =
      (ofIntegralForm (L.integralForm.restrict L.unitNormSubmodule)
        (L.isSymm_integralForm.restrict _)).gramMatrix
        (hL.unitNormBasis.map (ofIntegralForm.carrierEquiv _ _)) := by
  ext i j
  rw [gramMatrix_unitLatticeBasis]
  simp [gramMatrix_apply, integralForm_unitNormBasis, Matrix.one_apply]

/-- The rationalized unit-norm sublattice of a positive definite lattice is a standard lattice. -/
private noncomputable def unitLatticeIsometry :
    Isometry (unitLattice (Fin (finrank ℤ L.unitNormSubmodule)))
      (ofIntegralForm (L.integralForm.restrict L.unitNormSubmodule)
        (L.isSymm_integralForm.restrict _)) :=
  Isometry.ofGramMatrixEq (unitLatticeBasis _)
    (hL.unitNormBasis.map (ofIntegralForm.carrierEquiv _ _)) (gramMatrix_unitLatticeBasis_eq hL)

private theorem unitLatticeIsometry_single (i : Fin (finrank ℤ L.unitNormSubmodule)) :
    unitLatticeIsometry hL (Pi.single i 1) = 1 ⊗ₜ[ℤ] hL.unitNormBasis i := by
  classical
  have h : (Pi.single i 1 : Fin (finrank ℤ L.unitNormSubmodule) → ℚ) =
      (unitLatticeBasis _ i : Fin (finrank ℤ L.unitNormSubmodule) → ℚ) := by
    simp
  rw [h, unitLatticeIsometry, Isometry.ofGramMatrixEq_apply_basis, Basis.map_apply,
    ofIntegralForm.coe_carrierEquiv_apply]

/-- **A positive definite lattice is `I_k` plus a lattice without vectors of norm one.** The
standard lattice `I_k` is carried onto the unit-norm sublattice, with `k` its rank, and the second
summand is the complement `unitNormComplement L`. -/
noncomputable def unitNormDecomposition :
    Isometry ((unitLattice (Fin (finrank ℤ L.unitNormSubmodule))).orthogonalSum
      L.unitNormComplement) L :=
  -- `unitNormComplement L` is by definition the second summand of `orthogonalSplittingIsometry`.
  ((unitLatticeIsometry hL).orthogonalSum (Isometry.refl _)).trans
    (L.orthogonalSplittingIsometry _ hL.bijective_integralForm_restrict_unitNormSubmodule)

/-- The splitting sends the `i`-th coordinate vector of `I_k` to the `i`-th vector of the
orthonormal basis `unitNormBasis`. -/
@[simp]
theorem unitNormDecomposition_apply_single (i : Fin (finrank ℤ L.unitNormSubmodule)) :
    hL.unitNormDecomposition (Pi.single i 1, 0) = (hL.unitNormBasis i : V) := by
  have h := L.orthogonalSplittingIsometry_apply_one_tmul _
    hL.bijective_integralForm_restrict_unitNormSubmodule (hL.unitNormBasis i) 0
  simp only [tmul_zero, ZeroMemClass.coe_zero, add_zero] at h
  refine (Isometry.trans_apply _ _ _).trans ?_
  rw [Isometry.orthogonalSum_apply, unitLatticeIsometry_single, Isometry.refl_apply]
  -- `h` is stated for `orthogonalSplittingIsometry`, whose second summand is
  -- `unitNormComplement L` by definition.
  exact h

/-- The splitting is the inclusion on the complement of the unit-norm sublattice. -/
@[simp]
theorem unitNormDecomposition_apply_zero_tmul (r : ℚ)
    (t : L.integralForm.orthogonal L.unitNormSubmodule) :
    hL.unitNormDecomposition (0, r ⊗ₜ[ℤ] t) = r • ((t : L) : V) := by
  have h := L.orthogonalSplittingIsometry_apply_tmul _
    hL.bijective_integralForm_restrict_unitNormSubmodule 0 r 0 t
  simp only [tmul_zero, zero_smul, zero_add] at h
  refine (Isometry.trans_apply _ _ _).trans ?_
  rw [Isometry.orthogonalSum_apply, map_zero, Isometry.refl_apply]
  -- As above, `h` is stated for `orthogonalSplittingIsometry`.
  exact h

/-- The complement of the unit-norm sublattice of a positive definite lattice is positive
definite. -/
theorem isPosDef_unitNormComplement : L.unitNormComplement.IsPosDef := by
  rw [isPosDef_iff_posDef_integralNorm]
  intro y hy
  obtain ⟨t, rfl⟩ := L.unitNormComplementEquiv.surjective y
  rw [integralNorm_apply, integralForm_unitNormComplementEquiv, ← integralNorm_apply]
  refine hL.posDef_integralNorm _ fun ht ↦ hy ?_
  rw [Submodule.coe_eq_zero.1 ht, LinearEquiv.map_zero]

/-- Splitting off the unit-norm sublattice preserves the determinant. -/
@[simp]
theorem determinant_unitNormComplement : L.unitNormComplement.determinant = L.determinant := by
  rw [← hL.unitNormDecomposition.determinant_eq, determinant_orthogonalSum,
    unitLattice_determinant, one_mul]

/-- The complement of the unit-norm sublattice is unimodular exactly when the lattice is. -/
theorem isUnimodular_unitNormComplement_iff :
    L.unitNormComplement.IsUnimodular ↔ L.IsUnimodular := by
  have : L.IsNondegenerate := ⟨(L.isPosDef_iff_isPosSemidef_and_nondegenerate.1 hL).2⟩
  have : L.unitNormComplement.IsNondegenerate :=
    ⟨(L.unitNormComplement.isPosDef_iff_isPosSemidef_and_nondegenerate.1
      hL.isPosDef_unitNormComplement).2⟩
  rw [isUnimodular_iff_isUnit_determinant, isUnimodular_iff_isUnit_determinant,
    hL.determinant_unitNormComplement]

/-- The ranks of the unit-norm sublattice and of its complement add up to the rank of the
lattice. -/
theorem finrank_unitNormSubmodule_add_finrank_unitNormComplement :
    finrank ℤ L.unitNormSubmodule + finrank ℤ L.unitNormComplement = finrank ℤ L := by
  rw [← hL.unitNormDecomposition.finrank_carrier_eq, finrank_orthogonalSum,
    finrank_unitLattice, Fintype.card_fin]

end IsPosDef

/-! ### Uniqueness of the splitting -/

namespace Isometry

variable {W : Type v} [AddCommGroup W] [Module ℚ W] {M : IntegralLattice W}

/-- An isometry carries the unit-norm sublattice onto the unit-norm sublattice. -/
theorem map_unitNormSubmodule (e : Isometry L M) :
    L.unitNormSubmodule.map (e.carrierEquiv : L →ₗ[ℤ] M) = M.unitNormSubmodule :=
  e.map_span_vectorsOfNorm 1

/-- An isometry carries the orthogonal complement of the unit-norm sublattice onto the orthogonal
complement of the unit-norm sublattice. -/
theorem map_orthogonal_unitNormSubmodule (e : Isometry L M) :
    (L.integralForm.orthogonal L.unitNormSubmodule).map (e.carrierEquiv : L →ₗ[ℤ] M) =
      M.integralForm.orthogonal M.unitNormSubmodule := by
  rw [e.map_orthogonal, e.map_unitNormSubmodule]

/-- **Isometric lattices have isometric complements of their unit-norm sublattices.** -/
noncomputable def unitNormComplement (e : Isometry L M) :
    Isometry L.unitNormComplement M.unitNormComplement :=
  ofCarrierEquiv (L.unitNormComplementEquiv.symm ≪≫ₗ
      e.carrierEquiv.ofSubmodules _ _ e.map_orthogonal_unitNormSubmodule ≪≫ₗ
      M.unitNormComplementEquiv) fun x y ↦ by
    obtain ⟨x, rfl⟩ := L.unitNormComplementEquiv.surjective x
    obtain ⟨y, rfl⟩ := L.unitNormComplementEquiv.surjective y
    simp [LinearEquiv.ofSubmodules_apply]

/-- The isometry `Isometry.unitNormComplement` acts on the orthogonal complement of the unit-norm
sublattice as the carrier equivalence of the original isometry. -/
@[simp]
theorem coe_unitNormComplementEquiv_symm_unitNormComplement_apply (e : Isometry L M)
    (t : L.integralForm.orthogonal L.unitNormSubmodule) :
    (M.unitNormComplementEquiv.symm
        (e.unitNormComplement.carrierEquiv (L.unitNormComplementEquiv t)) : M) =
      e.carrierEquiv t := by
  simp [unitNormComplement, LinearEquiv.ofSubmodules_apply]

end Isometry

section OrthogonalSum

variable {ι : Type*} [Fintype ι] {W : Type v} [AddCommGroup W] [Module ℚ W]
  {N : IntegralLattice W}

/-- In `I_ι ⊕ N` with `N` positive definite without vectors of norm one, every vector of norm one
lies in the first summand. -/
private theorem eq_orthogonalSumInl_of_mem_vectorsOfNorm_one (hN : N.IsPosDef)
    (hN1 : N.vectorsOfNorm 1 = ∅) {z : (unitLattice ι).orthogonalSum N}
    (hz : z ∈ ((unitLattice ι).orthogonalSum N).vectorsOfNorm 1) :
    z = orthogonalSumInl _ N (orthogonalSumFst _ N z) := by
  rw [mem_vectorsOfNorm_one_iff, ← integralNorm_apply, integralNorm_orthogonalSum] at hz
  have h₁ := (isPosDef_unitLattice ι).isPosSemidef.integralNorm_nonneg (orthogonalSumFst _ N z)
  have h₂ : orthogonalSumSnd _ N z = 0 := by
    by_contra h
    have h₃ := hN.posDef_integralNorm _ h
    have h₄ : N.integralNorm (orthogonalSumSnd _ N z) ≠ 1 := fun h₄ ↦ by
      have : orthogonalSumSnd _ N z ∈ N.vectorsOfNorm 1 := by
        rwa [mem_vectorsOfNorm_one_iff, ← integralNorm_apply]
      simp [hN1] at this
    omega
  conv_lhs => rw [← orthogonalSumInl_fst_add_inr_snd_eq _ N z, h₂, map_zero, add_zero]

/-- In `I_ι ⊕ N` with `N` positive definite without vectors of norm one, the orthogonal
complement of the unit-norm sublattice is the second summand. -/
private theorem orthogonal_unitNormSubmodule_orthogonalSum (hN : N.IsPosDef)
    (hN1 : N.vectorsOfNorm 1 = ∅) :
    ((unitLattice ι).orthogonalSum N).integralForm.orthogonal
        ((unitLattice ι).orthogonalSum N).unitNormSubmodule =
      LinearMap.range (orthogonalSumInr (unitLattice ι) N) := by
  classical
  set S := (unitLattice ι).orthogonalSum N
  apply le_antisymm
  · intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx
    -- `x` is orthogonal to every coordinate vector of `I_ι`, so its first component vanishes.
    have hpair : LinearMap.flip (unitLattice ι).integralForm (orthogonalSumFst _ N x) = 0 := by
      refine (unitLatticeBasis ι).ext fun i ↦ ?_
      have hi : orthogonalSumInl _ N (unitLatticeBasis ι i) ∈ S.unitNormSubmodule := by
        refine S.vectorsOfNorm_one_subset_unitNormSubmodule ?_
        rw [mem_vectorsOfNorm_one_iff]
        simp [S, ← gramMatrix_apply, gramMatrix_unitLatticeBasis]
      simpa using hx _ hi
    have hfst : orthogonalSumFst _ N x = 0 := by
      by_contra h
      have := (isPosDef_unitLattice ι).posDef_integralNorm _ h
      rw [integralNorm_apply, ← LinearMap.flip_apply, hpair, LinearMap.zero_apply] at this
      exact this.false
    refine ⟨orthogonalSumSnd _ N x, ?_⟩
    conv_rhs => rw [← orthogonalSumInl_fst_add_inr_snd_eq _ N x, hfst, map_zero, zero_add]
  · rintro _ ⟨b, rfl⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    refine Submodule.span_le (p := LinearMap.ker (LinearMap.flip S.integralForm
      (orthogonalSumInr _ N b))).2 (fun z hz ↦ ?_) hu
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply,
      eq_orthogonalSumInl_of_mem_vectorsOfNorm_one hN hN1 hz]
    simp [S]

/-- **The complement of the unit-norm sublattice of `I_ι ⊕ N` is `N`**, when `N` is positive
definite without vectors of norm one. -/
noncomputable def unitNormComplementOrthogonalSumIsometry (hN : N.IsPosDef)
    (hN1 : N.vectorsOfNorm 1 = ∅) :
    Isometry N ((unitLattice ι).orthogonalSum N).unitNormComplement :=
  Isometry.ofCarrierEquiv
    (LinearEquiv.ofInjective _ (Function.LeftInverse.injective
        (g := orthogonalSumSnd (unitLattice ι) N) (orthogonalSumSnd_inr _ N)) ≪≫ₗ
      LinearEquiv.ofEq _ _ (orthogonal_unitNormSubmodule_orthogonalSum hN hN1).symm ≪≫ₗ
      ((unitLattice ι).orthogonalSum N).unitNormComplementEquiv) fun x y ↦ by
    simp [integralForm_orthogonalSum]

/-- The isometry `unitNormComplementOrthogonalSumIsometry` is the second inclusion of `I_ι ⊕ N`,
read in the orthogonal complement of the unit-norm sublattice. -/
@[simp]
theorem coe_unitNormComplementEquiv_symm_unitNormComplementOrthogonalSumIsometry_apply
    (hN : N.IsPosDef) (hN1 : N.vectorsOfNorm 1 = ∅) (x : N) :
    (((unitLattice ι).orthogonalSum N).unitNormComplementEquiv.symm
        ((unitNormComplementOrthogonalSumIsometry hN hN1).carrierEquiv x) :
        (unitLattice ι).orthogonalSum N) =
      orthogonalSumInr _ N x := by
  simp [unitNormComplementOrthogonalSumIsometry]

variable {κ : Type*} [Fintype κ] {X : Type*} [AddCommGroup X] [Module ℚ X]
  {N' : IntegralLattice X}

/-- **Cancellation of standard summands.** If `I_ι ⊕ N ≅ I_κ ⊕ N'`, where `N` and `N'` are positive
definite without vectors of norm one, then `N ≅ N'`. -/
theorem nonempty_isometry_of_isometry_orthogonalSum_unitLattice (hN : N.IsPosDef)
    (hN1 : N.vectorsOfNorm 1 = ∅) (hN' : N'.IsPosDef) (hN1' : N'.vectorsOfNorm 1 = ∅)
    (e : Isometry ((unitLattice ι).orthogonalSum N) ((unitLattice κ).orthogonalSum N')) :
    Nonempty (Isometry N N') :=
  ⟨((unitNormComplementOrthogonalSumIsometry hN hN1).trans e.unitNormComplement).trans
    (unitNormComplementOrthogonalSumIsometry hN' hN1').symm⟩

/-- **Cancellation of standard summands, rank part.** If `I_ι ⊕ N ≅ I_κ ⊕ N'`, where `N` and `N'`
are positive definite without vectors of norm one, then `#ι = #κ`. -/
theorem card_eq_of_isometry_orthogonalSum_unitLattice (hN : N.IsPosDef)
    (hN1 : N.vectorsOfNorm 1 = ∅) (hN' : N'.IsPosDef) (hN1' : N'.vectorsOfNorm 1 = ∅)
    (e : Isometry ((unitLattice ι).orthogonalSum N) ((unitLattice κ).orthogonalSum N')) :
    Fintype.card ι = Fintype.card κ := by
  obtain ⟨f⟩ := nonempty_isometry_of_isometry_orthogonalSum_unitLattice hN hN1 hN' hN1' e
  have h := e.finrank_carrier_eq
  rw [finrank_orthogonalSum, finrank_orthogonalSum, finrank_unitLattice, finrank_unitLattice,
    f.finrank_carrier_eq] at h
  omega

end OrthogonalSum

end TauCeti.IntegralLattice
