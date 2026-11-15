/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Filtration
public import TauCeti.Topology.Algebra.Valued.WithVal
public import Mathlib.RingTheory.AdicCompletion.Noetherian

/-!
# Completion at a place

The completion of a field at a place carries the same normalized valuation and constant field
embedding. Its valuation ring is a complete discrete valuation ring, and a uniformizer of the
original field is still a uniformizer after completion. Completeness can be read through the
order filtration: a sequence whose terms agree to increasing order has a limit to which it agrees
to the same orders. In particular the completed valuation ring is complete for the adic topology
of its maximal ideal, hence a Henselian local ring.

The inclusion identifies every finite interval of the order filtration with the corresponding
interval in the completion. In particular, completion does not change the residue field. These
identifications allow local calculations with finitely many coefficients to pass between the
field and its completion. No finiteness or perfectness of the residue field is assumed.

Restricting the constant field of `P` via `TauCeti.Place.restrictScalars` induces a canonical
topological ring isomorphism `TauCeti.Place.completionRestrictScalarsRingEquiv` preserving the
completed valuation and valuation ring. In the `PlaceCompletionExtension` scope (following
`AdicCompletionExtension` in `TauCeti/NumberTheory/NumberField/LocalGlobal/Completion.lean`),
`P.Completion` and `P.completionPlace.integers` also carry their low-priority canonical `F`- and
`P.integers`-algebra structures and scalar towers.

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

/-- The canonical embedding is the uniform-space completion map on the valued field. -/
theorem completionEmbedding_apply (x : F) :
    P.completionEmbedding x =
      ((WithVal.toVal P.valuation x : WithVal P.valuation) : P.Completion) := (rfl)

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
theorem isUniformizer_completionEmbedding_iff (x : F) :
    P.completionPlace.valuation.IsUniformizer (P.completionEmbedding x) ↔
      P.valuation.IsUniformizer x := by
  simp only [isUniformizer_iff_ord_eq_one, ord_completionEmbedding]

/-- The embedding preserves every step of the order filtration. -/
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

/-- Each step of the order filtration of the completed field is closed. -/
theorem isClosed_completionPlace_filtration (a : ℤ) :
    IsClosed (P.completionPlace.filtration a : Set P.Completion) := by
  obtain ⟨s, hs0, hs⟩ := P.exists_ne_zero_ord_eq a
  convert Valued.isClosed_closedBall P.Completion
    (Valued.v.restrict (P.completionEmbedding s)) using 1
  ext x
  simp only [SetLike.mem_coe, mem_filtration_iff, completionPlace_valuation, Set.mem_ofPred_eq,
    Valuation.restrict_le_iff, valuation_completionEmbedding, P.valuation_eq_exp_neg_ord hs0, hs]

/-- Completeness of the completed field, read through the order filtration: if the terms of a
sequence agree to increasing order, `g n ≡ g m` to order `m` whenever `m ≤ n`, then some completed
function agrees with each term `g n` to order `n`. -/
theorem exists_forall_sub_mem_completionPlace_filtration {g : ℕ → P.Completion}
    (hg : ∀ ⦃m n : ℕ⦄, m ≤ n → g n - g m ∈ P.completionPlace.filtration m) :
    ∃ x : P.Completion, ∀ n : ℕ, x - g n ∈ P.completionPlace.filtration n := by
  have hcauchy : CauchySeq g := by
    refine (Valued.hasBasis_uniformity P.Completion ℤᵐ⁰).cauchySeq_iff.mpr fun γ _ ↦ ?_
    obtain ⟨n, hn⟩ := WithZero.exists_exp_neg_natCast_lt
      (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
    refine ⟨n, fun m hm l hl ↦ ?_⟩
    have hdiff : g l - g m ∈ P.completionPlace.filtration n := by
      simpa using (P.completionPlace.filtration n).sub_mem (hg hl) (hg hm)
    rw [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]
    exact (P.completionPlace.mem_filtration_iff.mp hdiff).trans_lt hn
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨x, fun n ↦ ?_⟩
  have hclosed := (P.isClosed_completionPlace_filtration n).preimage
    (continuous_id.sub (continuous_const (y := g n)))
  exact hclosed.mem_of_tendsto hx (Filter.eventually_ge_atTop n |>.mono fun m hm ↦ hg hm)

/-- The completed valuation ring is complete for the adic topology of its maximal ideal. In
particular it is a Henselian local ring (`TauCeti.IsAdicComplete.henselianLocalRing`). -/
instance isAdicComplete_completionIntegers :
    IsAdicComplete (IsLocalRing.maximalIdeal P.completionPlace.integers)
      P.completionPlace.integers where
  toIsHausdorff := inferInstance
  prec' f hf := by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top,
      mem_maximalIdeal_pow_iff_coe_mem_filtration] at hf ⊢
    obtain ⟨x, hx⟩ := P.exists_forall_sub_mem_completionPlace_filtration
      (g := fun n ↦ (f n : P.Completion)) fun m n hmn ↦ by
        simpa using (P.completionPlace.filtration m).neg_mem (hf hmn)
    have hx0 : x ∈ P.completionPlace.integers := by
      have h := (P.completionPlace.filtration 0).add_mem (hx 0)
        (P.completionPlace.mem_filtration_zero_iff.mpr (f 0).2)
      simpa [P.completionPlace.mem_filtration_zero_iff] using h
    refine ⟨⟨x, hx0⟩, fun n ↦ ?_⟩
    simpa using (P.completionPlace.filtration n).neg_mem (hx n)

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
with error in any step; for a step below the given one, `0` already approximates. -/
theorem exists_filtration_sub_completionEmbedding_mem {a : ℤ} (b : ℤ)
    (x : P.completionPlace.filtration a) :
    ∃ y : P.filtration a,
      (x : P.Completion) - P.completionEmbedding y ∈ P.completionPlace.filtration b := by
  by_cases hab : a ≤ b
  swap
  · exact ⟨0, by simpa using P.completionPlace.filtration_antitone (not_le.mp hab).le x.2⟩
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
noncomputable def completionFiltrationQuotientEquiv (a b : ℤ) :
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
    obtain ⟨y, hy⟩ := P.exists_filtration_sub_completionEmbedding_mem b x
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    rw [Submodule.mapQ_apply, Submodule.Quotient.eq]
    have h := (P.completionPlace.filtration b).neg_mem hy
    simpa only [q', f, Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply, neg_sub,
      completionFiltrationMap_apply, Submodule.coe_sub] using h

/-- The filtration quotient equivalence sends the class of a function to the class of its
canonical image in the completion. -/
@[simp]
theorem completionFiltrationQuotientEquiv_apply_mk (a b : ℤ) (x : P.filtration a) :
    P.completionFiltrationQuotientEquiv a b (Submodule.Quotient.mk x) =
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
  obtain ⟨y, hy⟩ := P.exists_filtration_sub_completionEmbedding_mem 1 ⟨x, hx⟩
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

/-- Reading the residue of a function regular at `P` back in `F_P` gives its value at `P`. -/
@[simp]
theorem residueFieldEquivCompletion_symm_residue_completionIntegersEmbedding (x : P.integers) :
    P.residueFieldEquivCompletion.symm
        (IsLocalRing.residue P.completionPlace.integers (P.completionIntegersEmbedding x)) =
      IsLocalRing.residue P.integers x := by
  rw [← residueFieldEquivCompletion_apply_residue, AlgEquiv.symm_apply_apply]

/-- Completing a place preserves its degree over the constants. -/
@[simp]
theorem degree_completionPlace : P.completionPlace.degree = P.degree := by
  simp only [degree_eq_finrank]
  exact P.residueFieldEquivCompletion.toLinearEquiv.finrank_eq.symm

section RestrictScalars

variable (k₀ : Type*) [Field k₀] [Algebra k₀ k] [Algebra k₀ F] [IsScalarTower k₀ k F]

/-- Restricting the constant field of `P` from `k` to `k₀` induces a canonical topological ring
isomorphism `(P.restrictScalars k₀).Completion ≃+* P.Completion` extending the identity on `F`. -/
noncomputable def completionRestrictScalarsRingEquiv :
    (P.restrictScalars k₀).Completion ≃+* P.Completion :=
  Valuation.Completion.congr (RingEquiv.refl F) fun _ ↦ by simp

variable {k₀}

/-- `completionRestrictScalarsRingEquiv` commutes with the canonical completion embeddings of
`F`. -/
@[simp]
theorem completionRestrictScalarsRingEquiv_completionEmbedding (x : F) :
    P.completionRestrictScalarsRingEquiv k₀ ((P.restrictScalars k₀).completionEmbedding x) =
      P.completionEmbedding x := by
  rw [completionRestrictScalarsRingEquiv, completionEmbedding_apply, completionEmbedding_apply]
  exact Valuation.Completion.congr_coe (σ := RingEquiv.refl F) _ x

/-- The inverse of `completionRestrictScalarsRingEquiv` commutes with the canonical completion
embeddings of `F`. -/
@[simp]
theorem completionRestrictScalarsRingEquiv_symm_completionEmbedding (x : F) :
    (P.completionRestrictScalarsRingEquiv k₀).symm (P.completionEmbedding x) =
      (P.restrictScalars k₀).completionEmbedding x := by
  rw [RingEquiv.symm_apply_eq, completionRestrictScalarsRingEquiv_completionEmbedding]

/-- `completionRestrictScalarsRingEquiv` is continuous. -/
theorem continuous_completionRestrictScalarsRingEquiv :
    Continuous (P.completionRestrictScalarsRingEquiv k₀) :=
  Valuation.Completion.continuous_congr _

/-- `completionRestrictScalarsRingEquiv` preserves the completed valuation. -/
@[simp]
theorem valuation_completionRestrictScalarsRingEquiv
    (z : (P.restrictScalars k₀).Completion) :
    Valued.v (P.completionRestrictScalarsRingEquiv k₀ z) = Valued.v z :=
  Valuation.Completion.valued_congr (P.restrictScalars k₀).valuation_surjective _ z

/-- The inverse of `completionRestrictScalarsRingEquiv` preserves the completed valuation. -/
@[simp]
theorem valuation_completionRestrictScalarsRingEquiv_symm (z : P.Completion) :
    Valued.v ((P.completionRestrictScalarsRingEquiv k₀).symm z) = Valued.v z := by
  simpa using (P.valuation_completionRestrictScalarsRingEquiv
    ((P.completionRestrictScalarsRingEquiv k₀).symm z)).symm

/-- `completionRestrictScalarsRingEquiv` identifies the completed valuation rings. -/
theorem completionRestrictScalarsRingEquiv_mem_integers_iff
    {z : (P.restrictScalars k₀).Completion} :
    P.completionRestrictScalarsRingEquiv k₀ z ∈ P.completionPlace.integers ↔
      z ∈ (P.restrictScalars k₀).completionPlace.integers := by
  simp only [mem_integers_iff, completionPlace_valuation,
    valuation_completionRestrictScalarsRingEquiv]

/-- The inverse of `completionRestrictScalarsRingEquiv` identifies the completed valuation
rings. -/
theorem completionRestrictScalarsRingEquiv_symm_mem_integers_iff {z : P.Completion} :
    (P.completionRestrictScalarsRingEquiv k₀).symm z ∈
        (P.restrictScalars k₀).completionPlace.integers ↔
      z ∈ P.completionPlace.integers := by
  rw [← P.completionRestrictScalarsRingEquiv_mem_integers_iff (k₀ := k₀),
    RingEquiv.apply_symm_apply]

end RestrictScalars

noncomputable section PlaceCompletionExtension

/-- The canonical `F`-algebra structure on `P.Completion`, whose scalar action agrees
definitionally with `UniformSpace.Completion.instSMul`. Installed at low priority in the
`PlaceCompletionExtension` scope so that for `F = k` it never competes with
`P.instAlgebraCompletion`. -/
@[expose, instance_reducible]
def completionFieldAlgebra : Algebra F P.Completion :=
  letI := WithVal.uniformContinuousConstSMul (S := F) P.valuation
  UniformSpace.Completion.algebra (WithVal P.valuation) F

scoped[PlaceCompletionExtension] attribute [instance 10]
  TauCeti.Place.completionFieldAlgebra

/-- The canonical `P.integers`-algebra structure on `P.Completion`, whose scalar action agrees
definitionally with `UniformSpace.Completion.instSMul`. -/
@[expose, instance_reducible]
def completionIntegersToCompletionAlgebra : Algebra P.integers P.Completion :=
  letI := WithVal.uniformContinuousConstSMul (S := P.integers) P.valuation
  UniformSpace.Completion.algebra (WithVal P.valuation) P.integers

scoped[PlaceCompletionExtension] attribute [instance 100]
  TauCeti.Place.completionIntegersToCompletionAlgebra

/-- The canonical `P.integers`-algebra structure on `P.completionPlace.integers` given by
`P.completionIntegersEmbedding`, compatible with `completionIntegersToCompletionAlgebra`. -/
@[expose, instance_reducible]
def completionIntegersAlgebra : Algebra P.integers P.completionPlace.integers :=
  P.completionIntegersEmbedding.toRingHom.toAlgebra

scoped[PlaceCompletionExtension] attribute [instance 10]
  TauCeti.Place.completionIntegersAlgebra

open scoped PlaceCompletionExtension in
@[simp]
theorem algebraMap_completionFieldAlgebra (x : F) :
    algebraMap F P.Completion x = P.completionEmbedding x :=
  (P.completionEmbedding_apply x).symm

open scoped PlaceCompletionExtension in
@[simp]
theorem algebraMap_completionIntegersToCompletionAlgebra (x : P.integers) :
    algebraMap P.integers P.Completion x = P.completionEmbedding x :=
  (P.completionEmbedding_apply (x : F)).symm

open scoped PlaceCompletionExtension in
@[simp]
theorem algebraMap_completionIntegersAlgebra (x : P.integers) :
    algebraMap P.integers P.completionPlace.integers x = P.completionIntegersEmbedding x :=
  rfl

open scoped PlaceCompletionExtension in
theorem isScalarTower_integers_completionFieldAlgebra :
    IsScalarTower P.integers F P.Completion :=
  .of_algebraMap_eq fun _ ↦ rfl

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.isScalarTower_integers_completionFieldAlgebra

open scoped PlaceCompletionExtension in
theorem isScalarTower_completionIntegersAlgebra :
    IsScalarTower P.integers P.completionPlace.integers P.Completion :=
  .of_algebraMap_eq fun r ↦
    (P.completionEmbedding_apply (r : F)).symm.trans (P.completionIntegersEmbedding_apply r).symm

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.isScalarTower_completionIntegersAlgebra

open scoped PlaceCompletionExtension in
/-- The completed valuation ring `P.completionPlace.integers` is torsion-free over `P.integers`. -/
theorem isTorsionFree_completionIntegersAlgebra :
    Module.IsTorsionFree P.integers P.completionPlace.integers := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  intro x y h
  apply Subtype.ext
  apply (algebraMap F P.Completion).injective
  simpa only [algebraMap_completionFieldAlgebra, algebraMap_completionIntegersAlgebra,
    completionIntegersEmbedding_apply] using congrArg Subtype.val h

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.isTorsionFree_completionIntegersAlgebra

end PlaceCompletionExtension

end TauCeti.Place
