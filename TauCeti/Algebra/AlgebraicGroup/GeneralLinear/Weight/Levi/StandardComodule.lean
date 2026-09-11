/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Levi.Geometry
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive

/-!
# The standard representation of a weight Levi

Restricting the standard representation of `GL_N` to the block-diagonal subgroup attached to
an integer weight gives a faithful, completely reducible comodule over every field. Invariant
subspaces are sums of whole weight blocks, and the remaining blocks give invariant complements.
This supplies the representation-theoretic input to reductivity of weight Levis, including
those with repeated weights.

The argument uses the localized polynomial presentation of the coordinate algebra: linear
functionals extracting its surviving matrix entries recover the elementary matrix operators
from the coaction. Thus the result also holds over finite fields, where rational points alone
need not detect subcomodules.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 4 and 13.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.

The corestriction and faithfulness construction follows the standard `SL_N` comodule in
`TauCeti.Algebra.AlgebraicGroup.SpecialLinear.StandardComodule`.
-/

public section

open Module
open scoped TensorProduct

namespace TauCeti.GeneralLinear

universe u

noncomputable section

variable (R : Type u) [CommRing R] {N : ℕ} (w : Fin N → ℤ)

/-- The standard representation of a weight Levi, restricted from `GL_N`. -/
@[instance_reducible]
def weightLeviStandardComodule :
    Comodule R (weightLeviCoordinateHopfAlgebra R w) (Fin N → R) :=
  let _ := standardComodule R N
  Comodule.Corestrict (CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra R N)
    (weightLeviDefiningHopfIdeal R w)).hom.toCoalgHom

attribute [local instance] standardComodule weightLeviStandardComodule

/-- The standard weight-Levi coaction is the standard `GL_N` coaction followed by the
quotient map on the coordinate factor. -/
@[simp]
theorem weightLeviStandardComodule_coact :
    Comodule.corestrictCoact
        (R := R) (C := coordinateHopfAlgebra R N)
        (D := weightLeviCoordinateHopfAlgebra R w) (M := Fin N → R)
        (Bialgebra.Quotient.mkBialgHom (R := R)
          (weightLeviDefiningHopfIdeal R w).toIdeal).toCoalgHom =
      TensorProduct.map LinearMap.id
          (Bialgebra.Quotient.mkBialgHom (R := R)
            (weightLeviDefiningHopfIdeal R w).toIdeal).toLinearMap ∘ₗ
        standardCoact R N := by
  apply LinearMap.ext
  intro v
  rw [Comodule.corestrictCoact_apply, standardComodule_coact, LinearMap.comp_apply]

/-- The standard weight-Levi coaction on a basis vector is its quotient generic column. -/
-- This is an explicit rewrite lemma: the generic corestriction and standard-coaction simp rules
-- already reduce its left-hand side, so it is not a simp-normal-form rule.
theorem weightLeviStandardComodule_coact_single (j : Fin N) :
    Comodule.coact (R := R) (C := weightLeviCoordinateHopfAlgebra R w)
        (Pi.single j (1 : R)) =
      ∑ i, Pi.single i (1 : R) ⊗ₜ[R]
        Ideal.Quotient.mk (weightLeviDefiningHopfIdeal R w).toIdeal
          (genericMatrix R N i j) := by
  rw [Comodule.corestrict_coact_apply, standardComodule_coact,
    standardCoact_apply_basisFun]
  simp [genericMatrix_apply, BialgHom.toCoalgHom_apply]

/-- The standard representation of every weight Levi is faithful. -/
theorem isFaithful_weightLeviStandardComodule :
    Comodule.IsFaithful (k := R) (H := weightLeviCoordinateHopfAlgebra R w)
      (V := Fin N → R) :=
  Comodule.isFaithful_corestrict_of_surjective
    (CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra R N)
      (weightLeviDefiningHopfIdeal R w)).hom
    (CommHopfAlgCat.mkQuotient_surjective _ _)
    (isFaithful_standardComodule R N)

/-- A union of weight blocks spans a standard weight-Levi subcomodule. -/
def weightLeviCoordinateSubcomodule (s : Set (Fin N))
    (hs : ∀ i j, w i = w j → j ∈ s → i ∈ s) :
    Subcomodule R (weightLeviCoordinateHopfAlgebra R w) (Fin N → R) :=
  Subcomodule.ofSubmodule (Submodule.span R ((Pi.basisFun R (Fin N)) '' s)) fun v hv ↦ by
    classical
    let S := Submodule.span R ((Pi.basisFun R (Fin N)) '' s)
    let T := LinearMap.range (TensorProduct.map S.subtype
      (LinearMap.id : weightLeviCoordinateHopfAlgebra R w →ₗ[R] _))
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j, hj, rfl⟩ := hv
      rw [Pi.basisFun_apply, weightLeviStandardComodule_coact_single]
      apply T.sum_mem
      intro i _
      by_cases hij : w i = w j
      · exact ⟨⟨Pi.single i 1, Submodule.subset_span
          ⟨i, hs i j hij hj, Pi.basisFun_apply R (Fin N) i⟩⟩ ⊗ₜ[R]
            Ideal.Quotient.mk (weightLeviDefiningHopfIdeal R w).toIdeal
              (genericMatrix R N i j), by simp only [TensorProduct.map_tmul,
                Submodule.coe_subtype, LinearMap.id_apply]⟩
      · rw [genericMatrix_apply, weightLeviQuotient_mk_genericMatrix_apply_of_ne R w hij,
          TensorProduct.tmul_zero]
        exact T.zero_mem
    | zero => rw [map_zero]; exact T.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact T.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact T.smul_mem a hx

/-- The coordinate subcomodule is the span of the selected standard basis vectors. -/
@[simp]
theorem weightLeviCoordinateSubcomodule_toSubmodule (s : Set (Fin N))
    (hs : ∀ i j, w i = w j → j ∈ s → i ∈ s) :
    (weightLeviCoordinateSubcomodule R w s hs).toSubmodule =
      Submodule.span R ((Pi.basisFun R (Fin N)) '' s) :=
  (rfl)

/-- Membership in a coordinate subcomodule means vanishing outside its chosen weight blocks. -/
@[simp]
theorem mem_weightLeviCoordinateSubcomodule (s : Set (Fin N))
    (hs : ∀ i j, w i = w j → j ∈ s → i ∈ s) (v : Fin N → R) :
    v ∈ weightLeviCoordinateSubcomodule R w s hs ↔ ∀ i ∉ s, v i = 0 := by
  classical
  rw [← Subcomodule.mem_toSubmodule, weightLeviCoordinateSubcomodule_toSubmodule,
    (Pi.basisFun R (Fin N)).mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Pi.basisFun_repr]
  exact forall_congr' fun i ↦ not_imp_comm

variable (k : Type u) [Field k]

private theorem exists_weightLevi_coefficientFunctional (i j : Fin N) (hij : w i = w j) :
    ∃ f : weightLeviCoordinateHopfAlgebra k w →ₗ[k] k, ∀ a b,
      f (Ideal.Quotient.mk (weightLeviDefiningHopfIdeal k w).toIdeal
        (genericMatrix k N a b)) = if a = i ∧ b = j then 1 else 0 := by
  classical
  let P := MvPolynomial (WeightLeviIndex w) k
  let L := WeightLeviCoordinateRing k w
  let incl : P →ₗ[k] L := (IsScalarTower.toAlgHom k P L).toLinearMap
  have hinj : Function.Injective incl :=
    IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors
      (weightLeviPolynomialGenericMatrix_det_ne_zero k w))
  obtain ⟨r, hr⟩ := incl.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  let ij : WeightLeviIndex w := ⟨(i, j), hij⟩
  refine ⟨(MvPolynomial.lcoeff k (Finsupp.single ij 1)).comp
    (r.comp (weightLeviCoordinateAlgEquiv k w).toLinearMap), ?_⟩
  intro a b
  simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    genericMatrix_apply]
  rw [weightLeviCoordinateAlgEquiv_mk_genericMatrix_apply]
  by_cases hab : w a = w b
  · rw [weightLeviLocalizedGenericMatrix_apply_of_eq k w hab]
    have hrX := DFunLike.congr_fun hr (MvPolynomial.X ⟨(a, b), hab⟩)
    simp only [LinearMap.comp_apply, LinearMap.id_apply, incl, AlgHom.toLinearMap_apply] at hrX
    rw [hrX]
    simp [MvPolynomial.lcoeff_apply, MvPolynomial.coeff_X, Finsupp.single_left_inj,
      ij, Subtype.ext_iff, Prod.ext_iff]
  · rw [weightLeviLocalizedGenericMatrix_apply_of_ne k w hab, map_zero, map_zero]
    split_ifs with h
    · exact (hab (h.1 ▸ h.2 ▸ hij)).elim
    · rfl

/-- An invariant subspace contains every elementary matrix translate within a weight block. -/
theorem single_mem_weightLeviStandardSubcomodule
    (W : Subcomodule k (weightLeviCoordinateHopfAlgebra k w) (Fin N → k))
    {v : Fin N → k} (hv : v ∈ W) (i j : Fin N) (hij : w i = w j) :
    Pi.single i (v j) ∈ W := by
  classical
  obtain ⟨f, hf⟩ := exists_weightLevi_coefficientFunctional w k i j hij
  have heq : (TensorProduct.rid k (Fin N → k)).toLinearMap ∘ₗ
      LinearMap.lTensor (Fin N → k) f ∘ₗ
        Comodule.coact (R := k) (C := weightLeviCoordinateHopfAlgebra k w) =
      (LinearMap.single k (fun _ : Fin N ↦ k) i).comp (LinearMap.proj j) := by
    apply (Pi.basisFun k (Fin N)).ext
    intro b
    simp only [LinearMap.comp_apply, Pi.basisFun_apply]
    rw [weightLeviStandardComodule_coact_single]
    simp only [map_sum, LinearMap.lTensor_tmul, LinearEquiv.coe_coe,
      TensorProduct.rid_tmul, hf]
    by_cases hbj : b = j
    · subst b
      simp
    · simp [hbj, Ne.symm hbj]
  have h := W.rid_lTensor_coact_mem f hv
  have hvEq := DFunLike.congr_fun heq v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.single_apply,
    LinearMap.proj_apply] at hvEq
  rwa [hvEq] at h

/-- Every standard weight-Levi subcomodule is spanned by the coordinate vectors it contains. -/
theorem weightLeviStandardSubcomodule_eq_span
    (W : Subcomodule k (weightLeviCoordinateHopfAlgebra k w) (Fin N → k)) :
    W.toSubmodule = Submodule.span k ((Pi.basisFun k (Fin N)) ''
      {i | Pi.single i (1 : k) ∈ W}) := by
  classical
  apply le_antisymm
  · intro v hv
    rw [← Finset.univ_sum_single v]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : v i = 0
    · simp [hi]
    · have hsingle := single_mem_weightLeviStandardSubcomodule w k W hv i i rfl
      have hone : Pi.single i (1 : k) ∈ W := by
        simpa [← Pi.single_smul, hi] using W.toSubmodule.smul_mem (v i)⁻¹ hsingle
      have hmem := Submodule.subset_span (R := k)
        (s := (Pi.basisFun k (Fin N)) '' {i | Pi.single i (1 : k) ∈ W})
        ⟨i, by simpa only [Set.mem_ofPred_eq] using hone, rfl⟩
      simpa [Pi.basisFun_apply, ← Pi.single_smul] using
        Submodule.smul_mem _ (v i) hmem
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    apply Subcomodule.mem_toSubmodule.mpr
    simpa only [Pi.basisFun_apply, Set.mem_ofPred_eq] using hi

/-- **The standard representation of an arbitrary weight Levi is completely reducible.** -/
theorem isCompletelyReducible_weightLeviStandardComodule :
    Comodule.IsCompletelyReducible k (weightLeviCoordinateHopfAlgebra k w) (Fin N → k) := by
  classical
  apply Comodule.IsCompletelyReducible.of_exists_isCompl
  intro W
  let s : Set (Fin N) := {i | Pi.single i (1 : k) ∈ W}
  have hs : ∀ i j, w i = w j → j ∈ s → i ∈ s := by
    intro i j hij hj
    simpa only [s, Set.mem_ofPred_eq, Pi.single_eq_same] using
      single_mem_weightLeviStandardSubcomodule w k W hj i j hij
  have hsc : ∀ i j, w i = w j → j ∈ sᶜ → i ∈ sᶜ := by
    intro i j hij hj hi
    exact hj (hs j i hij.symm hi)
  refine ⟨weightLeviCoordinateSubcomodule k w sᶜ hsc, ?_⟩
  rw [weightLeviCoordinateSubcomodule_toSubmodule, weightLeviStandardSubcomodule_eq_span]
  exact (Pi.basisFun k (Fin N)).linearIndependent.isCompl_span_image
    (Pi.basisFun k (Fin N)).span_eq isCompl_compl

end

end TauCeti.GeneralLinear
