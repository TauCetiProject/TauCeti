/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Filtration
public import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# Completion at a place

The completion of a field at a place carries the same normalized valuation and constant field
embedding. Its valuation ring is a complete discrete valuation ring, and a uniformizer of the
original field is still a uniformizer after completion.

The inclusion identifies every finite interval of the order filtration with the corresponding
interval in the completion. In particular, completion does not change the residue field. These
identifications allow local calculations with finitely many coefficients to pass between the
field and its completion. No finiteness or perfectness of the residue field is assumed.

The underlying complete field and extension of the valuation are Mathlib's
`Valuation.Completion` and `Valued.valuedCompletion`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Section I.7.
-/

public section

open UniformSpace Topology
open scoped WithZero

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (P : Place k F)

/-- The completion of `F` for the valuation of `P`. -/
abbrev Completion := P.valuation.Completion

/-- The constants act on the completion through their embedding in `F`. -/
noncomputable instance instAlgebraCompletion : Algebra k P.Completion :=
  ((UniformSpace.Completion.coeRingHom.comp
    (WithVal.equiv P.valuation).symm.toRingHom).comp (algebraMap k F)).toAlgebra

/-- The canonical embedding of the field into its completion at `P`. -/
noncomputable def completionEmbedding : F →ₐ[k] P.Completion :=
  { UniformSpace.Completion.coeRingHom.comp (WithVal.equiv P.valuation).symm.toRingHom with
    commutes' _ := rfl }

/-- The embedding into the completion preserves the normalized valuation. -/
@[simp]
theorem valuation_completionEmbedding (x : F) :
    Valued.v (P.completionEmbedding x) = P.valuation x :=
  Valued.valuedCompletion_apply (WithVal.toVal P.valuation x)

/-- The original field is dense in its completion at `P`. -/
theorem denseRange_completionEmbedding : DenseRange P.completionEmbedding := by
  have h : (P.completionEmbedding : F → P.Completion) ∘ WithVal.ofVal =
      ((↑) : WithVal P.valuation → P.Completion) := by
    funext x
    exact congrArg ((↑) : WithVal P.valuation → P.Completion)
      (WithVal.toVal_ofVal P.valuation x)
  exact (h.symm ▸ UniformSpace.Completion.denseRange_coe).of_comp

/-- The extension of `P` to the completed field, with its original normalization. -/
noncomputable def completionPlace : Place k P.Completion where
  valuation := Valued.v
  valuation_surjective := fun γ ↦ by
    obtain ⟨x, rfl⟩ := P.valuation_surjective γ
    exact ⟨P.completionEmbedding x, P.valuation_completionEmbedding x⟩
  isTrivialOn := ⟨fun c hc ↦ by
    rw [← P.completionEmbedding.commutes c, valuation_completionEmbedding]
    exact P.isTrivialOn.eq_one c hc⟩

@[simp]
theorem completionPlace_valuation (x : P.Completion) :
    P.completionPlace.valuation x = Valued.v x := (rfl)

/-- Completion preserves the order of every function, including the junk value at zero. -/
@[simp]
theorem ord_completionEmbedding (x : F) :
    P.completionPlace.ord (P.completionEmbedding x) = P.ord x := by
  simp [ord_def]

/-- A uniformizer in the original field remains a uniformizer in the completion. -/
@[simp]
theorem isUniformizer_completionEmbedding_iff (x : F) :
    P.completionPlace.valuation.IsUniformizer (P.completionEmbedding x) ↔
      P.valuation.IsUniformizer x := by
  simp only [isUniformizer_iff_ord_eq_one, ord_completionEmbedding]

/-- The embedding preserves every step of the order filtration. -/
@[simp]
theorem completionEmbedding_mem_filtration_iff {a : ℤ} {x : F} :
    P.completionEmbedding x ∈ P.completionPlace.filtration a ↔ x ∈ P.filtration a := by
  simp only [mem_filtration_iff, completionPlace_valuation, valuation_completionEmbedding]

/-- The valuation ring of the completed field is complete for the induced uniform structure. -/
instance completeSpace_completionIntegers : CompleteSpace P.completionPlace.integers := by
  have h : (P.completionPlace.integers : Set P.Completion) =
      ((Valued.v (R := P.Completion)).valuationSubring : Set P.Completion) := by
    ext x
    simp only [SetLike.mem_coe, mem_integers_iff, completionPlace_valuation,
      Valuation.mem_valuationSubring_iff]
  exact (h.symm ▸ Valued.isClosed_valuationSubring P.Completion).completeSpace_coe

/-- A completed function can be approximated by a function in `F` to any prescribed order. -/
theorem exists_sub_completionEmbedding_mem_filtration (x : P.Completion) (b : ℤ) :
    ∃ y : F, x - P.completionEmbedding y ∈ P.completionPlace.filtration b := by
  obtain ⟨t, ht0, ht⟩ := P.exists_ne_zero_ord_eq b
  have ht' : Valued.v.restrict (P.completionEmbedding t) ≠ 0 := by
    simp [ht0]
  have hU : {z : P.Completion | Valued.v (z - x) < WithZero.exp (-b)} ∈ 𝓝 x := by
    refine Valued.mem_nhds.mpr ⟨Units.mk0 _ ht', fun z hz ↦ ?_⟩
    simp only [Set.mem_ofPred_eq, Units.val_mk0] at hz ⊢
    rw [Valuation.restrict_lt_iff_lt_embedding] at hz
    simpa [P.valuation_eq_exp_neg_ord ht0, ht] using hz
  obtain ⟨y, hy⟩ := P.denseRange_completionEmbedding.mem_nhds hU
  refine ⟨y, ?_⟩
  rw [mem_filtration_iff, completionPlace_valuation, Valuation.map_sub_swap]
  exact hy.le

/-- An element of the completed filtration has an approximation in the original filtration,
with error in any smaller step. -/
theorem exists_filtration_sub_completionEmbedding_mem {a b : ℤ} (hab : a ≤ b)
    (x : P.completionPlace.filtration a) :
    ∃ y : P.filtration a,
      (x : P.Completion) - P.completionEmbedding y ∈ P.completionPlace.filtration b := by
  obtain ⟨y, hy⟩ := P.exists_sub_completionEmbedding_mem_filtration x b
  have hya : P.completionEmbedding y ∈ P.completionPlace.filtration a := by
    have h := (P.completionPlace.filtration a).sub_mem x.2
      (P.completionPlace.filtration_antitone hab hy)
    simpa using h
  exact ⟨⟨y, P.completionEmbedding_mem_filtration_iff.mp hya⟩, hy⟩

/-- The inclusion of a step of the order filtration into its completed counterpart. -/
noncomputable def completionFiltrationMap (a : ℤ) :
    P.filtration a →ₗ[k] P.completionPlace.filtration a :=
  (P.completionEmbedding.toLinearMap.domRestrict (P.filtration a)).codRestrict
    (P.completionPlace.filtration a) (fun x ↦ P.completionEmbedding_mem_filtration_iff.mpr x.2)

@[simp]
theorem completionFiltrationMap_apply (a : ℤ) (x : P.filtration a) :
    (P.completionFiltrationMap a x : P.Completion) = P.completionEmbedding x := (rfl)

/-- Completion preserves every finite interval of the order filtration. The isomorphism is
induced by the canonical embedding, rather than by choices of representatives. -/
noncomputable def completionFiltrationQuotientEquiv {a b : ℤ} (hab : a ≤ b) :
    (P.filtration a ⧸ (P.filtration b).submoduleOf (P.filtration a)) ≃ₗ[k]
      (P.completionPlace.filtration a ⧸
        (P.completionPlace.filtration b).submoduleOf (P.completionPlace.filtration a)) := by
  let f := P.completionFiltrationMap a
  let q := (P.filtration b).submoduleOf (P.filtration a)
  let q' := (P.completionPlace.filtration b).submoduleOf (P.completionPlace.filtration a)
  have hf : q ≤ q'.comap f := fun x hx ↦
    P.completionEmbedding_mem_filtration_iff.mpr hx
  refine LinearEquiv.ofBijective (q.mapQ q' f hf) ⟨?_, ?_⟩
  · intro x y h
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective q x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective q y
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at h
    apply (Submodule.Quotient.eq q).mpr
    -- Read membership in the relative submodule as membership of the underlying function.
    have h' : P.completionEmbedding ((x : F) - (y : F)) ∈
        P.completionPlace.filtration b := by
      simpa only [q', f, Submodule.submoduleOf, Submodule.mem_comap,
        Submodule.subtype_apply, map_sub, completionFiltrationMap_apply, Submodule.coe_sub] using h
    exact P.completionEmbedding_mem_filtration_iff.mp h'
  · intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective q' x
    obtain ⟨y, hy⟩ := P.exists_filtration_sub_completionEmbedding_mem hab x
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    rw [Submodule.mapQ_apply, Submodule.Quotient.eq]
    have h := (P.completionPlace.filtration b).neg_mem hy
    simpa only [q', f, Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply, neg_sub,
      completionFiltrationMap_apply, Submodule.coe_sub] using h

/-- The filtration quotient equivalence sends the class of a function to the class of its
canonical image in the completion. -/
@[simp]
theorem completionFiltrationQuotientEquiv_apply_mk {a b : ℤ} (hab : a ≤ b)
    (x : P.filtration a) :
    P.completionFiltrationQuotientEquiv hab (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (P.completionFiltrationMap a x) := (rfl)

/-- The canonical map of valuation rings induced by completion. -/
noncomputable def completionIntegersEmbedding : P.integers →ₐ[k] P.completionPlace.integers where
  toFun x := ⟨P.completionEmbedding x, by
    simpa only [mem_integers_iff, completionPlace_valuation, valuation_completionEmbedding]
      using x.2⟩
  map_zero' := Subtype.ext (map_zero P.completionEmbedding)
  map_one' := Subtype.ext (map_one P.completionEmbedding)
  map_add' x y := Subtype.ext (map_add P.completionEmbedding (x : F) (y : F))
  map_mul' x y := Subtype.ext (map_mul P.completionEmbedding (x : F) (y : F))
  commutes' c := Subtype.ext (by simp)

@[simp]
theorem completionIntegersEmbedding_apply (x : P.integers) :
    (P.completionIntegersEmbedding x : P.Completion) = P.completionEmbedding x := (rfl)

/-- Completion reflects units of the valuation ring. -/
instance isLocalHom_completionIntegersEmbedding : IsLocalHom P.completionIntegersEmbedding where
  map_nonunit x hx := by
    rw [P.isUnit_iff_valuation_eq_one]
    simpa only [P.completionPlace.isUnit_iff_valuation_eq_one, completionPlace_valuation,
      completionIntegersEmbedding_apply, valuation_completionEmbedding] using hx

/-- Completion induces an isomorphism of residue fields over the original constants. -/
noncomputable def residueFieldEquivCompletion : P.ResidueField ≃ₐ[k]
    P.completionPlace.ResidueField := by
  let f := IsLocalRing.ResidueField.mapAlgHom P.completionIntegersEmbedding
  refine AlgEquiv.ofBijective f ⟨f.injective, ?_⟩
  intro x
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective (R := P.completionPlace.integers) x
  have hx : (x : P.Completion) ∈ P.completionPlace.filtration 0 :=
    P.completionPlace.mem_filtration_zero_iff.mpr x.2
  obtain ⟨y, hy⟩ := P.exists_filtration_sub_completionEmbedding_mem (by norm_num : (0 : ℤ) ≤ 1)
    ⟨x, hx⟩
  let y' : P.integers := ⟨y, P.mem_filtration_zero_iff.mp y.2⟩
  refine ⟨IsLocalRing.residue P.integers y', ?_⟩
  rw [IsLocalRing.ResidueField.mapAlgHom_residue]
  apply (P.completionPlace.residue_eq_iff_sub_mem_filtration_one).mpr
  have h := (P.completionPlace.filtration 1).neg_mem hy
  simpa only [neg_sub, completionIntegersEmbedding_apply] using h

/-- The residue-field isomorphism commutes with reduction of integral functions. -/
@[simp]
theorem residueFieldEquivCompletion_apply_residue (x : P.integers) :
    P.residueFieldEquivCompletion (IsLocalRing.residue P.integers x) =
      IsLocalRing.residue P.completionPlace.integers (P.completionIntegersEmbedding x) :=
  IsLocalRing.ResidueField.mapAlgHom_residue P.completionIntegersEmbedding x

/-- Completing a place preserves its degree over the constants. -/
@[simp]
theorem degree_completionPlace : P.completionPlace.degree = P.degree := by
  simp only [degree_eq_finrank]
  exact P.residueFieldEquivCompletion.toLinearEquiv.finrank_eq.symm

end TauCeti.Place
