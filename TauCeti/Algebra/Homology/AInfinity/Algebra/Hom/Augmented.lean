/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Augmentation
public import TauCeti.Algebra.Homology.AInfinity.Algebra.DG
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Unital
public import TauCeti.Algebra.Homology.DG.Algebra.Augmentation

/-!
# Augmented morphisms of `A∞` algebras

An `A∞` morphism `f : A ⟶ B` between augmented `A∞` algebras `(A, ε)` and `(B, ε')` is
**augmented** (`TauCeti.AInfinityHom.IsAugmented`) when its linear component commutes with the
augmentations (`ε' ∘ f₁ = ε`) and every higher component takes values in the augmentation ideal
`ker ε'`.  Equivalently, `f` commutes with the augmentations viewed as `A∞` morphisms to the
trivially graded ground ring (`TauCeti.AInfinityHom.isAugmented_iff_comp_eq`).

When `f` is both **strictly unital** and **augmented**, its action on `A = R · 1_A ⊕ ker ε` is
completely determined by its restriction to the reduced augmentation ideals
`ker ε ⟶ ker ε'`: on the unit line it maps `1_A ↦ 1_B` in arity one and vanishes in higher arities,
while on `ker ε` its components land in `ker ε'`.  Conversely, extending any `A∞` morphism
`g : ker ε ⟶ ker ε'` by `ε'.unitHom ∘ ε ∘ letter + subtype ∘ g.taylor ∘ map ε.reducedPart` produces
a strictly unital augmented `A∞` morphism `A ⟶ B`: the Stasheff morphism equation holds on pure
words from `ker ε` by functoriality of `g`, and on unit-containing words because the two-letter unit
collapses of `b_A` match the two-letter unit cuts of `coalgHom`.

This establishes the canonical equivalence (`TauCeti.AInfinityAlgebra.Augmentation.homEquivReduced`)
between strictly unital augmented `A∞` morphisms `(A, ε) ⟶ (B, ε')` and arbitrary `A∞` morphisms
`ε.reducedAlgebra ⟶ ε'.reducedAlgebra`.

## Main definitions

* `TauCeti.AInfinityAlgebra.Augmentation.toAInfinityStrictUnitalHom` and
  `TauCeti.AInfinityAlgebra.Augmentation.toAInfinityHom`: an augmentation packaged as a strictly
  unital strict `A∞` morphism (and general `A∞` morphism) to the trivially graded ground ring.
* `TauCeti.AInfinityAlgebra.Augmentation.reducedInclusion`: the inclusion `ker ε ↪ A` as a strict
  `A∞` morphism `ε.reducedAlgebra ⟶ A`.
* `TauCeti.DGAlgAugmentation.toAInfinityAugmentation`: the `A∞` augmentation induced by an
  augmentation of a differential graded algebra.
* `TauCeti.AInfinityHom.IsAugmented`: the augmentation-compatibility predicate for `A∞` morphisms.
* `TauCeti.AInfinityHom.codRestrictReduced`: corestriction of an `A∞` morphism `D ⟶ B` whose Taylor
  map lands in `ker ε'` to `D ⟶ ε'.reducedAlgebra`.
* `TauCeti.AInfinityHom.IsAugmented.restrictReduced`: restriction of an augmented `A∞` morphism
  `(A, ε) ⟶ (B, ε')` to `ε.reducedAlgebra ⟶ ε'.reducedAlgebra`.
* `TauCeti.AInfinityAlgebra.Augmentation.extendHom`: extension of an `A∞` morphism
  `ε.reducedAlgebra ⟶ ε'.reducedAlgebra` to a strictly unital augmented `A∞` morphism `A ⟶ B`.
* `TauCeti.AInfinityAlgebra.Augmentation.homEquivReduced`: the bijection between strictly unital
  augmented `A∞` morphisms `(A, ε) ⟶ (B, ε')` and `A∞` morphisms
  `ε.reducedAlgebra ⟶ ε'.reducedAlgebra`.

## References

* B. Keller, *A-infinity algebras, modules and functor categories*, Contemporary Mathematics 406
  (2006), Section 4.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1, 3.4, and 3.6.
* J.-L. Loday and B. Vallette, *Algebraic Operads*, Grundlehren der mathematischen Wissenschaften
  346, Springer (2012), Section 9.2.
-/

public section

namespace TauCeti

open ReducedTensorWords

universe uR uA uB uC uD

/-! ### Strict morphisms associated to an augmentation -/

namespace AInfinityAlgebra.Augmentation

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {AA : AInfinityAlgebra R A}

/-- An augmentation packaged as a strictly unital strict `A∞` morphism to the trivially graded
ground ring. -/
noncomputable def toAInfinityStrictUnitalHom (ε : AA.Augmentation) :
    AInfinityStrictUnitalHom ε.isStrictUnit (isDGAlgebra_trivialGrading R).strictUnit_one where
  toLinearMap := ε.toLinearMap
  map_mem' {p x} hx := by
    rw [IsNonUnitalDGAlgebra.toAInfinityAlgebra_grading, InternalGrading.ofDecomposition_piece]
    by_cases hp : p = 0
    · subst hp
      rw [mem_trivialGrading_iff]
      exact Or.inl rfl
    · rw [ε.map_of_mem_ne_zero p x hx hp]
      exact Submodule.zero_mem _
  map_m' n := by
    ext x
    rcases n with _ | _ | _ | n
    · simp
    · simp [ε.map_m_of_ne_two 1 (by decide) (by decide) x]
    · have h2 := IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_two_apply
        (isDGAlgebra_trivialGrading R).toIsNonUnitalDGAlgebra (fun i ↦ ε (x i))
      simp only [MultilinearMap.compLinearMap_apply, LinearMap.compMultilinearMap_apply]
      exact (congrArg ε (by congr 1; funext i; fin_cases i <;> rfl :
        AA.m 2 x = AA.m 2 ![x 0, x 1])).trans ((ε.map_binary (x 0) (x 1)).trans h2.symm)
    · simp [ε.map_m_of_ne_two (n + 3) (by omega) (by omega) x]
  map_unit' := ε.map_unit

@[simp]
theorem coe_toAInfinityStrictUnitalHom (ε : AA.Augmentation) :
    ⇑ε.toAInfinityStrictUnitalHom = ε := (rfl)

@[simp]
theorem toLinearMap_toAInfinityStrictUnitalHom (ε : AA.Augmentation) :
    ε.toAInfinityStrictUnitalHom.toAInfinityStrictHom.toLinearMap = ε.toLinearMap := (rfl)

/-- An augmentation viewed as an `A∞` morphism to the trivially graded ground ring. -/
noncomputable def toAInfinityHom (ε : AA.Augmentation) :
    AInfinityHom AA (isDGAlgebra_trivialGrading R).toIsNonUnitalDGAlgebra.toAInfinityAlgebra :=
  ε.toAInfinityStrictUnitalHom.toAInfinityStrictHom.toAInfinityHom

@[simp]
theorem taylor_toAInfinityHom (ε : AA.Augmentation) :
    ε.toAInfinityHom.taylor = ε.toLinearMap ∘ₗ letter R A :=
  ε.toAInfinityStrictUnitalHom.toAInfinityStrictHom.taylor_toAInfinityHom

/-- An augmentation is homogeneous of degree zero to the trivially graded ground ring. -/
theorem isHomogeneous_toLinearMap (ε : AA.Augmentation) :
    LinearMap.IsHomogeneous ε.toLinearMap AA.grading.piece (trivialGrading R R) 0 := by
  refine LinearMap.isHomogeneous_def.mpr fun p x hx ↦ ?_
  rw [add_zero]
  by_cases hp : p = 0
  · subst hp
    rw [mem_trivialGrading_iff]
    exact Or.inl rfl
  · rw [ε.map_of_mem_ne_zero p x hx hp]
    exact Submodule.zero_mem _

/-- The inclusion of the reduced augmentation ideal as a strict `A∞` morphism. -/
noncomputable def reducedInclusion (ε : AA.Augmentation) :
    AInfinityStrictHom ε.reducedAlgebra AA where
  toLinearMap := ε.augmentationIdeal.subtype
  map_mem' hx := by
    rw [reducedAlgebra_grading, reducedGrading_piece, Submodule.mem_comap] at hx
    exact hx
  map_m' n := MultilinearMap.ext fun x ↦ by
    rw [MultilinearMap.compLinearMap_apply, LinearMap.compMultilinearMap_apply, reducedAlgebra_m]
    exact ε.coe_reducedOperation n x

@[simp]
theorem toLinearMap_reducedInclusion (ε : AA.Augmentation) :
    ε.reducedInclusion.toLinearMap = ε.augmentationIdeal.subtype := (rfl)

@[simp]
theorem coe_reducedInclusion (ε : AA.Augmentation) (x : ε.augmentationIdeal) :
    ε.reducedInclusion x = (x : A) := (rfl)

@[simp]
theorem barMap_reducedInclusion (ε : AA.Augmentation) :
    ε.reducedInclusion.barMap = ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype :=
  ε.reducedInclusion.barMap_def

@[simp]
theorem toLinearMap_comp_subtype (ε : AA.Augmentation) :
    ε.toLinearMap ∘ₗ ε.augmentationIdeal.subtype = 0 := by
  refine LinearMap.ext fun x ↦ ?_
  exact (ε.mem_augmentationIdeal).mp x.property

@[simp]
theorem apply_coe_augmentationIdeal (ε : AA.Augmentation) (x : ε.augmentationIdeal) :
    ε x = 0 :=
  (ε.mem_augmentationIdeal).mp x.property

@[simp]
theorem reducedPart_comp_subtype (ε : AA.Augmentation) :
    ε.reducedPart ∘ₗ ε.augmentationIdeal.subtype = LinearMap.id :=
  LinearMap.ext fun x ↦ ε.reducedPart_coe x

@[simp]
theorem reducedPart_unit (ε : AA.Augmentation) : ε.reducedPart ε.unit = 0 := by
  apply Subtype.ext
  simp

/-- The reduced-part projection is homogeneous of degree zero. -/
theorem isHomogeneous_reducedPart (ε : AA.Augmentation) :
    LinearMap.IsHomogeneous ε.reducedPart AA.grading.piece ε.reducedAlgebra.grading.piece 0 := by
  refine LinearMap.isHomogeneous_def.mpr fun p x hx ↦ ?_
  rw [add_zero, reducedAlgebra_grading, reducedGrading_piece, Submodule.mem_comap,
    Submodule.subtype_apply, coe_reducedPart]
  by_cases hp : p = 0
  · subst hp
    exact Submodule.sub_mem _ hx (Submodule.smul_mem _ _ ε.isStrictUnit.degree_zero)
  · rw [ε.map_of_mem_ne_zero p x hx hp, zero_smul, sub_zero]
    exact hx

/-- The unit inclusion `R → A` is homogeneous of degree zero from the trivial grading. -/
theorem isHomogeneous_unitHom (ε : AA.Augmentation) :
    LinearMap.IsHomogeneous ε.unitHom (trivialGrading R R) AA.grading.piece 0 := by
  refine LinearMap.isHomogeneous_def.mpr fun p r hr ↦ ?_
  rw [add_zero, unitHom_apply]
  rcases (mem_trivialGrading_iff R R).mp hr with rfl | rfl
  · exact Submodule.smul_mem _ r ε.isStrictUnit.degree_zero
  · simp

/-- Every reduced tensor word over `A` is a sum of a word over `ker ε` and a degenerate word
containing `ε.unit`. -/
theorem top_le_range_map_subtype_sup_degenerateWords (ε : AA.Augmentation) :
    (⊤ : Submodule R (ReducedTensorWords R A)) ≤
      LinearMap.range (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype) ⊔
        degenerateWords R A ε.unit := by
  rw [← iSup_range_of R A, iSup_le_iff]
  intro n
  rw [LinearMap.range_le_iff_comap, eq_top_iff]
  intro t ht
  clear ht
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [Submodule.mem_comap, map_smul]
    refine Submodule.smul_mem _ c ?_
    suffices ∀ (S : Finset (Fin n.1)), (∀ i ∉ S, x i ∈ ε.augmentationIdeal) →
        of R A n (PiTensorProduct.tprod R x) ∈
          LinearMap.range (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype) ⊔
            degenerateWords R A ε.unit from
      this Finset.univ (fun i hi ↦ absurd (Finset.mem_univ i) hi)
    intro S
    induction S using Finset.induction_on generalizing x with
    | empty =>
      intro hx
      refine Submodule.mem_sup_left ⟨of R ε.augmentationIdeal n
        (PiTensorProduct.tprod R fun i ↦ ⟨x i, hx i (Finset.notMem_empty i)⟩), ?_⟩
      rw [map_of_tprod]
      rfl
    | insert j T hjT ih =>
      intro hx
      have hsplit : x j = (ε.reducedPart (x j) : A) + ε (x j) • ε.unit := by
        rw [coe_reducedPart, sub_add_cancel]
      have hupd : x = Function.update x j ((ε.reducedPart (x j) : A) + ε (x j) • ε.unit) := by
        rw [← hsplit, Function.update_eq_self]
      rw [hupd, (PiTensorProduct.tprod R).map_update_add, map_add]
      refine Submodule.add_mem _ (ih (Function.update x j (ε.reducedPart (x j) : A)) fun i hi ↦ ?_)
        (Submodule.mem_sup_right <|
          of_tprod_mem_degenerateWords_of_eq_smul n _ (i := j) (c := ε (x j)) (by simp))
      by_cases hij : i = j
      · subst hij
        rw [Function.update_self]
        exact (ε.reducedPart (x i)).property
      · rw [Function.update_of_ne hij]
        exact hx i fun h ↦ (Finset.mem_insert.mp h).elim hij hi
  | add t u ht hu => exact Submodule.add_mem _ ht hu

end AInfinityAlgebra.Augmentation

/-! ### Augmentations of DG algebras as `A∞` augmentations -/

namespace DGAlgAugmentation

variable {R : Type uR} {B : Type uB} [CommRing R] [Ring B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B} {hB : IsDGAlgebra ℬ dB}

/-- An augmentation of a differential graded algebra induces an augmentation of its underlying
`A∞` algebra. -/
noncomputable def toAInfinityAugmentation (εB : DGAlgAugmentation hB) :
    hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.Augmentation where
  unit := 1
  isStrictUnit := hB.strictUnit_one
  toLinearMap := (εB : B →ₗ[R] R)
  map_unit := map_one εB
  map_of_mem_ne_zero p x hx hp := by
    rw [IsNonUnitalDGAlgebra.toAInfinityAlgebra_grading,
      InternalGrading.ofDecomposition_piece] at hx
    have hmem := GradedFunLike.map_mem εB hx
    rw [trivialGrading_eq_bot R R hp, Submodule.mem_bot] at hmem
    exact hmem
  map_binary x y := by simp
  map_m_of_ne_two n hn0 hn2 x := by
    rcases n with _ | _ | _ | n
    · omega
    · simp
    · omega
    · simp

@[simp]
theorem toAInfinityAugmentation_unit (εB : DGAlgAugmentation hB) :
    εB.toAInfinityAugmentation.unit = 1 := (rfl)

@[simp]
theorem toAInfinityAugmentation_toLinearMap (εB : DGAlgAugmentation hB) :
    εB.toAInfinityAugmentation.toLinearMap = (εB : B →ₗ[R] R) := (rfl)

theorem toAInfinityAugmentation_apply (εB : DGAlgAugmentation hB) (b : B) :
    εB.toAInfinityAugmentation b = εB b := (rfl)

@[simp]
theorem toAInfinityAugmentation_augmentationIdeal (εB : DGAlgAugmentation hB) :
    εB.toAInfinityAugmentation.augmentationIdeal = εB.augmentationIdeal.toSubmodule := by
  ext b
  simp

@[simp]
theorem toAInfinityHom_toAInfinityAugmentation (εB : DGAlgAugmentation hB) :
    εB.toAInfinityAugmentation.toAInfinityHom =
      εB.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom := by
  refine AInfinityHom.ext <| LinearMap.ext fun z ↦ ?_
  simp

end DGAlgAugmentation

/-! ### Augmented `A∞` morphisms -/

namespace AInfinityHom

section AugmentedPredicate

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-- An `A∞` morphism `f : A ⟶ B` is **augmented** with respect to `ε` and `ε'` when its linear
component intertwines the augmentations and every higher component lands in `ker ε'`. -/
structure IsAugmented (f : AInfinityHom AA BB) (ε : AA.Augmentation)
    (ε' : BB.Augmentation) : Prop where
  /-- The linear part commutes with the augmentations. -/
  map_linearPart : ∀ a, ε' (f.linearPart a) = ε a
  /-- Every higher component vanishes after applying the target augmentation. -/
  map_component_eq_zero : ∀ {n : ℕ}, n ≠ 1 → ∀ x : Fin n → A, ε' (f.component n x) = 0

/-- An `A∞` morphism is augmented precisely when its suspended Taylor map commutes with the
augmentations via the letter projection. -/
theorem isAugmented_iff_taylor {f : AInfinityHom AA BB} {ε : AA.Augmentation}
    {ε' : BB.Augmentation} :
    f.IsAugmented ε ε' ↔ ε'.toLinearMap ∘ₗ f.taylor = ε.toLinearMap ∘ₗ letter R A := by
  refine ⟨fun hf ↦ ?_, fun htaylor ↦ ⟨fun a ↦ ?_, fun {n} hn x ↦ ?_⟩⟩
  · refine ReducedTensorWords.linearMap_ext R A fun ⟨n, hn⟩ x ↦ ?_
    by_cases hn1 : n = 1
    · subst hn1
      have hx1 : of R A ⟨1, hn⟩ (PiTensorProduct.tprod R x) = ofLetter R A (x 0) := by
        rw [of_tprod_eq_subword R hn, subword_one R A x hn]
        rfl
      rw [hx1, LinearMap.comp_apply, LinearMap.comp_apply, letter_ofLetter, ← linearPart_apply]
      exact hf.map_linearPart (x 0)
    · have hcomp : f.component n (fun i ↦ AA.grading.koszulTwist ((n : ℤ) - 1 - i) (x i)) =
          f.taylor (of R A ⟨n, hn⟩ (PiTensorProduct.tprod R x)) := by
        rw [component_apply f n hn]
        simp only [InternalGrading.koszulTwist_koszulTwist]
      have hne : (⟨n, hn⟩ : {k : ℕ // 0 < k}) ≠ 1 := by
        intro h
        exact hn1 (congrArg Subtype.val h)
      rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hcomp, letter_of_of_ne_one R A hne,
        map_zero]
      exact hf.map_component_eq_zero hn1 _
  · simpa only [LinearMap.comp_apply, letter_ofLetter, ← linearPart_apply] using
      LinearMap.congr_fun htaylor (ofLetter R A a)
  · rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp
    · have hne : (⟨n, hnpos⟩ : {k : ℕ // 0 < k}) ≠ 1 := by
        intro h
        exact hn (congrArg Subtype.val h)
      rw [component_apply f n hnpos]
      have hz := LinearMap.congr_fun htaylor
        (of R A ⟨n, hnpos⟩ (PiTensorProduct.tprod R fun i ↦
          AA.grading.koszulTwist ((n : ℤ) - 1 - i) (x i)))
      simpa only [LinearMap.comp_apply, letter_of_of_ne_one R A hne, map_zero] using hz

/-- An `A∞` morphism is augmented precisely when composing with `ε'` as an `A∞` morphism gives
`ε`. -/
theorem isAugmented_iff_comp_eq {f : AInfinityHom AA BB} {ε : AA.Augmentation}
    {ε' : BB.Augmentation} :
    f.IsAugmented ε ε' ↔ ε'.toAInfinityHom.comp f = ε.toAInfinityHom := by
  rw [isAugmented_iff_taylor]
  refine ⟨fun h ↦ AInfinityHom.ext ?_, fun h ↦ ?_⟩
  · rw [AInfinityAlgebra.Augmentation.toAInfinityHom,
      AInfinityStrictHom.taylor_toAInfinityHom_comp,
      AInfinityAlgebra.Augmentation.taylor_toAInfinityHom]
    exact h
  · have ht := congrArg AInfinityHom.taylor h
    rwa [AInfinityAlgebra.Augmentation.toAInfinityHom,
      AInfinityStrictHom.taylor_toAInfinityHom_comp,
      AInfinityAlgebra.Augmentation.taylor_toAInfinityHom] at ht

/-- A strict `A∞` morphism is augmented precisely when its linear part intertwines the
augmentations. -/
theorem IsStrict.isAugmented_iff {f : AInfinityHom AA BB} {ε : AA.Augmentation}
    {ε' : BB.Augmentation} (hf : f.IsStrict) :
    f.IsAugmented ε ε' ↔ ∀ a, ε' (f.linearPart a) = ε a := by
  refine ⟨IsAugmented.map_linearPart, fun hlin ↦ ⟨hlin, fun {n} hn x ↦ ?_⟩⟩
  rw [← hf.toAInfinityHom_toStrictHom,
    MultilinearMap.congr_fun (hf.toStrictHom.component_toAInfinityHom_eq_zero hn) x,
    zero_apply, map_zero]

@[simp]
theorem isAugmented_id (ε : AA.Augmentation) : (AInfinityHom.id AA).IsAugmented ε ε :=
  (isStrict_id AA).isAugmented_iff.mpr fun a ↦ by simp

theorem IsAugmented.comp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    {ε : AA.Augmentation} {ε' : BB.Augmentation} {ε'' : CC.Augmentation}
    (hg : g.IsAugmented ε' ε'') (hf : f.IsAugmented ε ε') :
    (g.comp f).IsAugmented ε ε'' := by
  rw [isAugmented_iff_comp_eq, ← comp_assoc, isAugmented_iff_comp_eq.mp hg]
  exact isAugmented_iff_comp_eq.mp hf

end AugmentedPredicate

end AInfinityHom

namespace DGAlgHom

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R]
  [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}

/-- A morphism of DG algebras is augmented as an `A∞` morphism precisely when it commutes with the
DG algebra augmentations. -/
@[simp]
theorem isAugmented_toAInfinityHom_iff {εA : DGAlgAugmentation hA} {εB : DGAlgAugmentation hB}
    (φ : DGAlgHom hA hB) :
    φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.IsAugmented
        εA.toAInfinityAugmentation εB.toAInfinityAugmentation ↔
      εB.comp φ = εA := by
  rw [(AInfinityHom.isStrict_toAInfinityHom _).isAugmented_iff, DGAlgHom.ext_iff]
  simp [AInfinityStrictHom.linearPart_toAInfinityHom]

end DGAlgHom

/-! ### Corestriction and restriction to reduced augmentation ideals -/

namespace AInfinityHom

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
  [AddCommGroup D] [Module R D]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}
  {CC : AInfinityAlgebra R C} {DD : AInfinityAlgebra R D}

/-- Corestrict an `A∞` morphism `h : D ⟶ B` whose Taylor map takes values in `ker ε'` to an `A∞`
morphism `D ⟶ ε'.reducedAlgebra`. -/
noncomputable def codRestrictReduced (h : AInfinityHom DD BB) (ε' : BB.Augmentation)
    (hh : ∀ z, h.taylor z ∈ ε'.augmentationIdeal) :
    AInfinityHom DD ε'.reducedAlgebra :=
  let t : ReducedTensorWords R D →ₗ[R] ε'.augmentationIdeal := ε'.reducedPart ∘ₗ h.taylor
  have ht : ε'.augmentationIdeal.subtype ∘ₗ t = h.taylor := by
    refine LinearMap.ext fun z ↦ ?_
    simp [t, (ε'.mem_augmentationIdeal).mp (hh z)]
  have hdeg : LinearMap.IsHomogeneous t (gradedPiece (DD.grading.shift 1))
      (ε'.reducedAlgebra.grading.shift 1).piece 0 := by
    refine LinearMap.isHomogeneous_def.mpr fun p z hz ↦ ?_
    have hmem := h.isHomogeneous_taylor.map_mem hz
    have htz : (t z : B) = h.taylor z := by
      simpa only [LinearMap.comp_apply, Submodule.subtype_apply] using LinearMap.congr_fun ht z
    rw [InternalGrading.shift_piece, AInfinityAlgebra.Augmentation.reducedAlgebra_grading,
      AInfinityAlgebra.Augmentation.reducedGrading_piece, Submodule.mem_comap,
      Submodule.subtype_apply, htz]
    simpa only [InternalGrading.shift_piece] using hmem
  have hcoalg : ε'.reducedInclusion.barMap ∘ₗ coalgHom R t = h.barMap := by
    rw [AInfinityAlgebra.Augmentation.barMap_reducedInclusion, map_comp_coalgHom, ht,
      ← h.barMap_eq_coalgHom]
  have heq : ε'.reducedAlgebra.taylor ∘ₗ coalgHom R t = t ∘ₗ DD.barDifferential := by
    refine LinearMap.ext fun z ↦ Subtype.ext ?_
    have h1 := LinearMap.congr_fun ε'.reducedInclusion.taylor_comp_barMap (coalgHom R t z)
    have h2 := LinearMap.congr_fun hcoalg z
    have h3 := LinearMap.congr_fun h.taylor_comp_barMap z
    have h4 := LinearMap.congr_fun ht (DD.barDifferential z)
    simp only [LinearMap.comp_apply, AInfinityAlgebra.Augmentation.toLinearMap_reducedInclusion,
      Submodule.subtype_apply] at h1 h2 h3 h4 ⊢
    rw [← h1, h2, h3, ← h4]
  AInfinityHom.ofTaylor t hdeg heq

@[simp]
theorem taylor_codRestrictReduced (h : AInfinityHom DD BB) (ε' : BB.Augmentation)
    (hh : ∀ z, h.taylor z ∈ ε'.augmentationIdeal) :
    (h.codRestrictReduced ε' hh).taylor = ε'.reducedPart ∘ₗ h.taylor :=
  taylor_ofTaylor _ _ _

@[simp]
theorem reducedInclusion_comp_codRestrictReduced (h : AInfinityHom DD BB) (ε' : BB.Augmentation)
    (hh : ∀ z, h.taylor z ∈ ε'.augmentationIdeal) :
    ε'.reducedInclusion.toAInfinityHom.comp (h.codRestrictReduced ε' hh) = h := by
  refine AInfinityHom.ext <| LinearMap.ext fun z ↦ ?_
  rw [AInfinityStrictHom.taylor_toAInfinityHom_comp, taylor_codRestrictReduced]
  simp [(ε'.mem_augmentationIdeal).mp (hh z)]

@[simp]
theorem codRestrictReduced_reducedInclusion_comp (ε' : BB.Augmentation)
    (g : AInfinityHom DD ε'.reducedAlgebra) (hh) :
    (ε'.reducedInclusion.toAInfinityHom.comp g).codRestrictReduced ε' hh = g := by
  refine AInfinityHom.ext <| LinearMap.ext fun z ↦ ?_
  rw [taylor_codRestrictReduced, AInfinityStrictHom.taylor_toAInfinityHom_comp]
  simp

/-- Postcomposing with `ε'.reducedInclusion` identifies `A∞` morphisms `D ⟶ ε'.reducedAlgebra`
bijectively with `A∞` morphisms `D ⟶ B` whose Taylor map takes values in `ker ε'`. -/
noncomputable def _root_.TauCeti.AInfinityAlgebra.Augmentation.homReducedCodomainEquiv
    (ε' : BB.Augmentation) (DD : AInfinityAlgebra R D) :
    AInfinityHom DD ε'.reducedAlgebra ≃
      {h : AInfinityHom DD BB // ∀ z, h.taylor z ∈ ε'.augmentationIdeal} where
  toFun g := ⟨ε'.reducedInclusion.toAInfinityHom.comp g, fun z ↦ by
    rw [AInfinityStrictHom.taylor_toAInfinityHom_comp, LinearMap.comp_apply,
      AInfinityAlgebra.Augmentation.toLinearMap_reducedInclusion]
    exact (g.taylor z).property⟩
  invFun h := h.val.codRestrictReduced ε' h.property
  left_inv g := codRestrictReduced_reducedInclusion_comp ε' g _
  right_inv h := Subtype.ext (reducedInclusion_comp_codRestrictReduced h.val ε' h.property)

namespace IsAugmented

/-- For an augmented `A∞` morphism `f : A ⟶ B`, the composite `f ∘ ε.reducedInclusion` has Taylor
values in `ker ε'`. -/
theorem taylor_comp_reducedInclusion_mem {f : AInfinityHom AA BB} {ε : AA.Augmentation}
    {ε' : BB.Augmentation} (hf : f.IsAugmented ε ε')
    (z : ReducedTensorWords R ε.augmentationIdeal) :
    (f.comp ε.reducedInclusion.toAInfinityHom).taylor z ∈ ε'.augmentationIdeal := by
  rw [ε'.mem_augmentationIdeal, taylor_comp, AInfinityStrictHom.barMap_toAInfinityHom,
    AInfinityAlgebra.Augmentation.barMap_reducedInclusion, LinearMap.comp_apply]
  have ht := LinearMap.congr_fun (isAugmented_iff_taylor.mp hf)
    (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype z)
  have hl := LinearMap.congr_fun (letter_comp_map (R := R) ε.augmentationIdeal.subtype) z
  simp only [LinearMap.comp_apply] at ht hl
  rw [ht, hl]
  exact (ε.mem_augmentationIdeal).mp (letter R ε.augmentationIdeal z).property

/-- Restrict an augmented `A∞` morphism `f : (A, ε) ⟶ (B, ε')` to an `A∞` morphism between the
reduced augmentation ideals `ε.reducedAlgebra ⟶ ε'.reducedAlgebra`. -/
noncomputable def restrictReduced {f : AInfinityHom AA BB} {ε : AA.Augmentation}
    {ε' : BB.Augmentation} (hf : f.IsAugmented ε ε') :
    AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra :=
  (f.comp ε.reducedInclusion.toAInfinityHom).codRestrictReduced ε'
    hf.taylor_comp_reducedInclusion_mem

@[simp]
theorem taylor_restrictReduced {f : AInfinityHom AA BB} {ε : AA.Augmentation}
    {ε' : BB.Augmentation} (hf : f.IsAugmented ε ε') :
    hf.restrictReduced.taylor =
      ε'.reducedPart ∘ₗ f.taylor ∘ₗ
        ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype := by
  rw [restrictReduced, taylor_codRestrictReduced, taylor_comp,
    AInfinityStrictHom.barMap_toAInfinityHom,
    AInfinityAlgebra.Augmentation.barMap_reducedInclusion]

@[simp]
theorem reducedInclusion_comp_restrictReduced {f : AInfinityHom AA BB} {ε : AA.Augmentation}
    {ε' : BB.Augmentation} (hf : f.IsAugmented ε ε') :
    ε'.reducedInclusion.toAInfinityHom.comp hf.restrictReduced =
      f.comp ε.reducedInclusion.toAInfinityHom :=
  reducedInclusion_comp_codRestrictReduced _ _ _

@[simp]
theorem restrictReduced_id (ε : AA.Augmentation) :
    (isAugmented_id ε).restrictReduced = AInfinityHom.id ε.reducedAlgebra := by
  refine AInfinityHom.ext <| LinearMap.ext fun z ↦ Subtype.ext ?_
  simp

theorem restrictReduced_comp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    {ε : AA.Augmentation} {ε' : BB.Augmentation} {ε'' : CC.Augmentation}
    (hg : g.IsAugmented ε' ε'') (hf : f.IsAugmented ε ε') :
    (hg.comp hf).restrictReduced = hg.restrictReduced.comp hf.restrictReduced := by
  refine AInfinityHom.ext <| LinearMap.ext fun z ↦ Subtype.ext ?_
  have heq : ε''.reducedInclusion.toAInfinityHom.comp (hg.comp hf).restrictReduced =
      ε''.reducedInclusion.toAInfinityHom.comp (hg.restrictReduced.comp hf.restrictReduced) := by
    calc ε''.reducedInclusion.toAInfinityHom.comp (hg.comp hf).restrictReduced
        = (g.comp f).comp ε.reducedInclusion.toAInfinityHom :=
          (hg.comp hf).reducedInclusion_comp_restrictReduced
      _ = g.comp (f.comp ε.reducedInclusion.toAInfinityHom) := comp_assoc _ _ _
      _ = g.comp (ε'.reducedInclusion.toAInfinityHom.comp hf.restrictReduced) := by
          rw [← hf.reducedInclusion_comp_restrictReduced]
      _ = (g.comp ε'.reducedInclusion.toAInfinityHom).comp hf.restrictReduced :=
          (comp_assoc _ _ _).symm
      _ = (ε''.reducedInclusion.toAInfinityHom.comp hg.restrictReduced).comp
            hf.restrictReduced := by
          rw [← hg.reducedInclusion_comp_restrictReduced]
      _ = ε''.reducedInclusion.toAInfinityHom.comp
            (hg.restrictReduced.comp hf.restrictReduced) := comp_assoc _ _ _
  have hz := congrArg (fun k ↦ k.taylor z) heq
  rw [AInfinityStrictHom.taylor_toAInfinityHom_comp,
    AInfinityStrictHom.taylor_toAInfinityHom_comp] at hz
  simpa using hz

end IsAugmented

end AInfinityHom

/-! ### Extending reduced `A∞` morphisms to strictly unital augmented morphisms -/

section ExtendHom

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

/-- Prepending a strict unit `e` before a word `w` and applying `taylor` recovers `letter w`. -/
private theorem taylor_prepend_unit {e : B} (hB : BB.StrictUnit e) (w : ReducedTensorWords R B) :
    BB.taylor (prepend R B e w) = letter R B w := by
  have h : BB.taylor ∘ₗ prepend R B e = letter R B := by
    refine ReducedTensorWords.linearMap_ext R B fun ⟨k, hk⟩ y ↦ ?_
    rcases k with _ | _ | k
    · omega
    · have hy : of R B ⟨1, hk⟩ (PiTensorProduct.tprod R y) = ofLetter R B (y 0) := by
        rw [of_tprod_eq_subword R hk, subword_one R B y hk]
        rfl
      rw [LinearMap.comp_apply, hy, prepend_ofLetter, hB.taylor_of_two_unit_left, letter_ofLetter]
    · have hne2 : (⟨k + 3, by omega⟩ : {n : ℕ // 0 < n}).1 ≠ 2 := by dsimp only; omega
      have hne1 : (⟨k + 2, hk⟩ : {n : ℕ // 0 < n}) ≠ 1 := by
        intro h0
        have h' : k + 2 = 1 := congrArg Subtype.val h0
        omega
      rw [LinearMap.comp_apply, prepend_of_tprod,
        hB.taylor_of_tprod_eq_zero ⟨k + 3, by omega⟩ hne2 _ ⟨0, rfl⟩,
        letter_of_of_ne_one R B hne1]
  exact LinearMap.congr_fun h w

/-- Prepending `b` and then a strict unit `e` produces a word of length at least three containing
`e`, on which `taylor` vanishes. -/
private theorem taylor_prepend_prepend_unit {e : B} (hB : BB.StrictUnit e) (b : B)
    (v : ReducedTensorWords R B) :
    BB.taylor (prepend R B b (prepend R B e v)) = 0 := by
  have h : BB.taylor ∘ₗ prepend R B b ∘ₗ prepend R B e = 0 := by
    refine ReducedTensorWords.linearMap_ext R B fun ⟨k, hk⟩ y ↦ ?_
    have hne2 : (⟨k + 2, by omega⟩ : {n : ℕ // 0 < n}).1 ≠ 2 := by dsimp only; omega
    rw [LinearMap.comp_apply, LinearMap.comp_apply, prepend_of_tprod, prepend_of_tprod,
      LinearMap.zero_apply]
    exact hB.taylor_of_tprod_eq_zero ⟨k + 2, by omega⟩ hne2 _ ⟨1, rfl⟩
  exact LinearMap.congr_fun h v

/-- Prepending two letters `b, u` to any degenerate word produces words of length at least three
containing `e`, on which `taylor` vanishes. -/
private theorem taylor_prepend_prepend_of_mem_degenerateWords {e : B} (hB : BB.StrictUnit e)
    (b u : B) {z : ReducedTensorWords R B} (hz : z ∈ degenerateWords R B e) :
    BB.taylor (prepend R B b (prepend R B u z)) = 0 := by
  suffices hle : degenerateWords R B e ≤
      LinearMap.ker (BB.taylor ∘ₗ prepend R B b ∘ₗ prepend R B u) from
    LinearMap.mem_ker.mp (hle hz)
  rw [degenerateWords_le_iff]
  rintro ⟨k, hk⟩ y ⟨i, hi⟩
  have hne2 : (⟨k + 2, by omega⟩ : {n : ℕ // 0 < n}).1 ≠ 2 := by dsimp only; omega
  rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.comp_apply, prepend_of_tprod,
    prepend_of_tprod]
  exact hB.taylor_of_tprod_eq_zero ⟨k + 2, by omega⟩ hne2 _ ⟨i.succ.succ, by simpa using hi⟩

namespace AInfinityAlgebra.Augmentation

/-- The candidate suspended Taylor map extending `g : ε.reducedAlgebra ⟶ ε'.reducedAlgebra` to
`A ⟶ B`. -/
private noncomputable def extendTaylor (ε : AA.Augmentation) (ε' : BB.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) : ReducedTensorWords R A →ₗ[R] B :=
  ε'.unitHom ∘ₗ ε.toLinearMap ∘ₗ letter R A +
    ε'.augmentationIdeal.subtype ∘ₗ g.taylor ∘ₗ ReducedTensorWords.map (R := R) ε.reducedPart

private theorem extendTaylor_ofLetter_unit (ε : AA.Augmentation) (ε' : BB.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    extendTaylor ε ε' g (ofLetter R A ε.unit) = ε'.unit := by
  simp [extendTaylor]

private theorem extendTaylor_of_tprod_eq_zero (ε : AA.Augmentation) (ε' : BB.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra)
    (k : {k : ℕ // 0 < k}) (hk : k.1 ≠ 1) (y : Fin k.1 → A) (hy : ∃ i, y i = ε.unit) :
    extendTaylor ε ε' g (of R A k (PiTensorProduct.tprod R y)) = 0 := by
  obtain ⟨i, hi⟩ := hy
  have hne : k ≠ 1 := fun h ↦ hk (congrArg Subtype.val h)
  have hmap : ReducedTensorWords.map (R := R) ε.reducedPart
      (of R A k (PiTensorProduct.tprod R y)) = 0 := by
    rw [map_of_tprod]
    have hupd : (fun j ↦ ε.reducedPart (y j)) =
        Function.update (fun j ↦ ε.reducedPart (y j)) i 0 := by
      ext j
      by_cases hij : j = i
      · subst hij
        simp [hi]
      · simp [hij]
    rw [hupd, (PiTensorProduct.tprod R).map_update_zero, map_zero]
  simp [extendTaylor, letter_of_of_ne_one R A hne, hmap]

private theorem isHomogeneous_extendTaylor (ε : AA.Augmentation) (ε' : BB.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    LinearMap.IsHomogeneous (extendTaylor ε ε' g)
      (gradedPiece (AA.grading.shift 1)) (BB.grading.shift 1).piece 0 := by
  refine LinearMap.isHomogeneous_def.mpr fun p z hz ↦ ?_
  rw [extendTaylor, LinearMap.add_apply]
  refine Submodule.add_mem _ ?_ ?_
  · have hl : letter R A z ∈ AA.grading.piece (p + 1) := by
      have h1 := (isHomogeneous_letter (AA.grading.shift 1)).map_mem hz
      simpa only [InternalGrading.shift_piece, add_zero] using h1
    by_cases hp : p + 1 = 0
    · have h0 : p + 0 + 1 = 0 := by omega
      rw [InternalGrading.shift_piece, h0, LinearMap.comp_apply, LinearMap.comp_apply,
        unitHom_apply]
      exact Submodule.smul_mem _ _ ε'.isStrictUnit.degree_zero
    · simp [LinearMap.comp_apply, ε.map_of_mem_ne_zero (p + 1) _ hl hp]
  · have hred_shift : LinearMap.IsHomogeneous ε.reducedPart
        (AA.grading.shift 1).piece (ε.reducedAlgebra.grading.shift 1).piece 0 := by
      refine LinearMap.isHomogeneous_def.mpr fun q a ha ↦ ?_
      simpa only [InternalGrading.shift_piece, add_zero] using
        ε.isHomogeneous_reducedPart.map_mem (by simpa only [InternalGrading.shift_piece] using ha)
    have hmap := (isHomogeneous_map _ _ hred_shift).map_mem hz
    rw [add_zero] at hmap
    have hg := g.isHomogeneous_taylor.map_mem hmap
    rw [InternalGrading.shift_piece, reducedAlgebra_grading, reducedGrading_piece,
      Submodule.mem_comap] at hg
    simpa only [InternalGrading.shift_piece, LinearMap.comp_apply] using hg

/-- Evaluating `BB.taylor ∘ coalgHom (extendTaylor g)` on a word of length `n + 1` with `ε.unit` at
index `j`: only a leading or trailing singleton cut around `ε.unit` survives. -/
private theorem taylor_coalgHom_extendTaylor_of_tprod (ε : AA.Augmentation) (ε' : BB.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra)
    {n : ℕ} (x : Fin (n + 1) → A) (j : Fin (n + 1)) (hj : x j = ε.unit) :
    BB.taylor (coalgHom R (extendTaylor ε ε' g)
        (of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R x))) =
      (if j.1 = 0 ∧ 0 < n then extendTaylor ε ε' g (subword R x 1 n) else 0) +
        (if j.1 = n ∧ 0 < n then
          BB.grading.koszulTwist 1 (extendTaylor ε ε' g (subword R x 0 n)) else 0) := by
  set F := extendTaylor ε ε' g
  have hjn := j.isLt
  have hvanish : ∀ {a b : ℕ}, 1 < b → a ≤ j.1 → j.1 < a + b → F (subword R x a b) = 0 := by
    intro a b hb haj hjb
    by_cases hab : a + b ≤ n + 1
    · have hb1 : (⟨b, by omega⟩ : {k : ℕ // 0 < k}).1 ≠ 1 := by dsimp only; omega
      rw [subword_eq_of_tprod R x (by omega) hab]
      exact extendTaylor_of_tprod_eq_zero ε ε' g ⟨b, by omega⟩ hb1 _
        ⟨⟨j.1 - a, by dsimp only; omega⟩, by
          rw [← hj]; exact congrArg x (Fin.ext (by simp; omega))⟩
    · rw [subword_eq_zero_of_lt_add R x (by omega), map_zero]
  have hsingle : ∀ {a : ℕ}, a = j.1 → F (subword R x a 1) = ε'.unit := by
    intro a ha
    rw [subword_one R A x (by omega)]
    have hxa : x ⟨a, by omega⟩ = ε.unit := by
      rw [← hj]
      exact congrArg x (Fin.ext ha)
    rw [hxa]
    exact extendTaylor_ofLetter_unit ε ε' g
  rw [of_tprod_eq_subword R n.succ_pos, coalgHom_subword, map_add, map_sum]
  simp only [zero_add, Nat.succ_eq_add_one]
  have hfirst : BB.taylor (ofLetter R B (F (subword R x 0 (n + 1)))) = 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hsingle (by omega)]
      simpa [AInfinityAlgebra.taylor_ofLetter] using ε'.isStrictUnit.unary_eq_zero
    · rw [hvanish (by omega) (by omega) (by omega), map_zero, map_zero]
  rw [hfirst, zero_add]
  have hterm : ∀ d ∈ Finset.range (n + 1),
      BB.taylor (prepend R B (F (subword R x 0 d)) (coalgHom R F (subword R x d (n + 1 - d)))) =
        (if d = 1 ∧ (j.1 = 0 ∧ 0 < n) then F (subword R x 1 n) else 0) +
          (if d = n ∧ (j.1 = n ∧ 0 < n) then
            BB.grading.koszulTwist 1 (F (subword R x 0 n)) else 0) := by
    intro d hd
    rw [Finset.mem_range] at hd
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · simp (disch := omega) [subword_length_zero]
    by_cases hjd : j.1 < d
    · by_cases hd1 : d = 1
      · subst d
        have hj0 : j.1 = 0 := by omega
        have hn0 : 0 < n := by omega
        have hsub : n + 1 - 1 = n := by omega
        rw [hsub, hsingle hj0.symm, taylor_prepend_unit ε'.isStrictUnit, ← LinearMap.comp_apply,
          letter_comp_coalgHom, ite_eq_left ⟨rfl, hj0, hn0⟩, ite_eq_right (by omega), add_zero]
      · have h0d : j.1 < 0 + d := by omega
        rw [hvanish (by omega) (Nat.zero_le _) h0d, map_zero, LinearMap.zero_apply, map_zero,
          ite_eq_right (by omega), ite_eq_right (by omega), add_zero]
    · -- `j` lies in the second block `subword R x d (n + 1 - d)`.
      rw [coalgHom_subword, map_add, map_add, map_sum, map_sum]
      have htail : ∑ d' ∈ Finset.range (n + 1 - d),
          BB.taylor (prepend R B (F (subword R x 0 d))
            (prepend R B (F (subword R x d d'))
              (coalgHom R F (subword R x (d + d') (n + 1 - d - d'))))) = 0 := by
        refine Finset.sum_eq_zero fun d' hd' ↦ ?_
        rw [Finset.mem_range] at hd'
        rcases Nat.eq_zero_or_pos d' with rfl | hd'0
        · simp [subword_length_zero]
        by_cases hjd' : j.1 < d + d'
        · by_cases hd'1 : d' = 1
          · subst d'
            rw [hsingle (by omega)]
            exact taylor_prepend_prepend_unit ε'.isStrictUnit _ _
          · rw [hvanish (by omega) (by omega) hjd', map_zero, LinearMap.zero_apply, map_zero,
              map_zero]
        · refine taylor_prepend_prepend_of_mem_degenerateWords ε'.isStrictUnit _ _ ?_
          exact coalgHom_subword_mem_degenerateWords F (extendTaylor_ofLetter_unit ε ε' g)
            (extendTaylor_of_tprod_eq_zero ε ε' g) x (by omega)
            ⟨j, by omega, by omega, hj⟩
      rw [htail, add_zero]
      by_cases hdn : d = n
      · subst d
        have hjn' : j.1 = n := by omega
        have hsub : n + 1 - n = 1 := by omega
        rw [hsub, hsingle hjn'.symm, prepend_ofLetter, ε'.isStrictUnit.taylor_of_two_unit_right,
          ite_eq_right (by omega), ite_eq_left ⟨rfl, hjn', hd0⟩, zero_add]
      · have h1 : 1 < n + 1 - d := by omega
        have h2 : d ≤ j.1 := by omega
        have h3 : j.1 < d + (n + 1 - d) := by omega
        rw [hvanish h1 h2 h3, map_zero, map_zero, map_zero,
          ite_eq_right (by omega), ite_eq_right (by omega), add_zero]
  rw [Finset.sum_congr rfl fun d hd ↦ hterm d hd]
  simp only [Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq', Finset.mem_range]
  congr 1 <;> split_ifs <;> first | rfl | omega

/-- Evaluating `(extendTaylor g) ∘ AA.barDifferential` on a homogeneous word of length `n + 1` with
`ε.unit` at index `j`: only the two-letter collapses `[ε.unit, a]` and `[a, ε.unit]` survive. -/
private theorem extendTaylor_barDifferential_of_tprod (ε : AA.Augmentation) (ε' : BB.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra)
    {n : ℕ} (x : Fin (n + 1) → A) (𝒟 : Fin (n + 1) → ℤ)
    (hx : ∀ i, x i ∈ (AA.grading.shift 1).piece (𝒟 i))
    (j : Fin (n + 1)) (hj : x j = ε.unit) :
    extendTaylor ε ε' g
        (AA.barDifferential (of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R x))) =
      (if j.1 = 0 ∧ 0 < n then extendTaylor ε ε' g (subword R x 1 n) else 0) +
        (if j.1 = n ∧ 0 < n then
          BB.grading.koszulTwist 1 (extendTaylor ε ε' g (subword R x 0 n)) else 0) := by
  set F := extendTaylor ε ε' g
  have hjn := j.isLt
  rw [AA.barDifferential_def, gradedCoderiv_of_tprod_of_homogeneous _ _ 1 _ x 𝒟 hx]
  simp only [map_sum, map_smul, one_mul]
  have hterm : ∀ p ∈ Finset.range (n + 1), ∀ d ∈ Finset.range (n + 1 + 1),
      (((∑ i ∈ Finset.range p, if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0).negOnePow : ℤ) : R) •
          F (splice R x 0 (n + 1) p d (AA.taylor (subword R x p d))) =
        (if p = j.1 ∧ d = 2 ∧ j.1 + 1 ≤ n then
          negOnePowCast R (∑ i ∈ Finset.range j.1, if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0) •
            F (splice R x 0 (n + 1) j.1 2
              (if h : j.1 + 1 < n + 1 then x ⟨j.1 + 1, h⟩ else 0)) else 0) +
        (if p = j.1 - 1 ∧ d = 2 ∧ 1 ≤ j.1 then
          negOnePowCast R
              (∑ i ∈ Finset.range (j.1 - 1), if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0) •
            negOnePowCast R (𝒟 ⟨j.1 - 1, by omega⟩ + 1) •
            F (splice R x 0 (n + 1) (j.1 - 1) 2 (x ⟨j.1 - 1, by omega⟩)) else 0) := by
    intro p hp d hd
    rw [Finset.mem_range] at hp hd
    by_cases hfit : 0 < d ∧ p + d ≤ n + 1
    swap
    · simp (disch := omega) only [splice_eq_zero_of_not_fits R _ _ hfit, map_zero, smul_zero,
        ite_eq_right, add_zero]
    by_cases hblock : p ≤ j.1 ∧ j.1 < p + d
    swap
    · obtain ⟨y, ⟨k, hk⟩, hy⟩ := exists_splice_eq_of_tprod R x hfit.2
        (AA.taylor (subword R x p d)) hblock
      have hlen : (⟨n + 1 + 1 - d, by omega⟩ : {m : ℕ // 0 < m}).1 ≠ 1 := by dsimp only; omega
      have hF0 : F (of R A ⟨n + 1 + 1 - d, by omega⟩ (PiTensorProduct.tprod R y)) = 0 :=
        extendTaylor_of_tprod_eq_zero ε ε' g ⟨n + 1 + 1 - d, by omega⟩ hlen y ⟨k, hk.trans hj⟩
      simp (disch := omega) only [hy, hF0, smul_zero, ite_eq_right, add_zero]
    by_cases hd2 : d = 2
    swap
    · have hzero : AA.taylor (subword R x p d) = 0 := by
        rw [subword_eq_of_tprod R x hfit.1 hfit.2]
        exact ε.isStrictUnit.taylor_of_tprod_eq_zero ⟨d, hfit.1⟩ hd2 _
          ⟨⟨j.1 - p, by dsimp only; omega⟩, by
            rw [← hj]; exact congrArg x (Fin.ext (by simp; omega))⟩
      simp (disch := omega) only [hzero, splice_zero, map_zero, smul_zero, ite_eq_right, add_zero]
    subst hd2
    rcases Nat.lt_or_ge p j.1 with hpj | hpj
    · obtain rfl : p = j.1 - 1 := by omega
      simp (disch := omega) only [true_and, ite_eq_right, ite_eq_left, zero_add]
      rw [subword_two_eq R x hfit.2]
      have hj' : (⟨j.1 - 1 + 1, by omega⟩ : Fin (n + 1)) = j := Fin.ext (by simp; omega)
      rw [hj', hj, ε.isStrictUnit.taylor_of_two_unit_right,
        AA.grading.koszulTwist_one_apply_of_mem
          (by simpa [InternalGrading.shift_piece] using hx ⟨j.1 - 1, by omega⟩),
        splice_smul, map_smul]
      simp only [negOnePowCast_eq_intCast]
    · obtain rfl : p = j.1 := by omega
      simp (disch := omega) only [true_and, ite_eq_right, ite_eq_left, add_zero]
      rw [subword_two_eq R x hfit.2, Fin.eta, hj, ε.isStrictUnit.taylor_of_two_unit_left,
        negOnePowCast_eq_intCast, dite_eq_left (by omega)]
  rw [Finset.sum_congr rfl fun p hp ↦ Finset.sum_congr rfl fun d hd ↦ hterm p hp d hd]
  simp only [Finset.sum_add_distrib, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_range]
  set S : ℕ → ℤ := fun p ↦ ∑ i ∈ Finset.range p, if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0 with hS
  have hSsucc (p : ℕ) (hp : p < n + 1) : S (p + 1) = S p + 𝒟 ⟨p, hp⟩ := by
    simp only [hS, Finset.sum_range_succ, dite_eq_left hp]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rcases Nat.eq_zero_or_pos j.1 with hj0 | hj0
  · have hW : splice R x 0 (n + 1) j.1 2 (if h : j.1 + 1 < n + 1 then x ⟨j.1 + 1, h⟩ else 0) =
        subword R x 1 n := by
      rw [dite_eq_left (by omega)]
      exact splice_two_succ_eq_subword R hn hj0 x
    simp (disch := omega) only [ite_eq_right, ite_eq_left, add_zero]
    rw [hW, hj0, Finset.sum_range_zero, negOnePowCast_zero, one_smul]
  rcases Nat.lt_or_ge j.1 n with hjlt | hjge
  · have hW : splice R x 0 (n + 1) j.1 2 (if h : j.1 + 1 < n + 1 then x ⟨j.1 + 1, h⟩ else 0) =
        splice R x 0 (n + 1) (j.1 - 1) 2 (x ⟨j.1 - 1, by omega⟩) := by
      rw [dite_eq_left (by omega)]
      exact splice_two_succ_eq_splice_two_pred R hj0 hjlt x
    simp (disch := omega) only [ite_eq_right, ite_eq_left, add_zero]
    rw [hW, smul_smul, ← negOnePowCast_add, ← add_smul]
    have hsign : negOnePowCast R (S j.1) +
        negOnePowCast R (S (j.1 - 1) + (𝒟 ⟨j.1 - 1, by omega⟩ + 1)) = 0 := by
      have := hSsucc (j.1 - 1) (by omega)
      rw [Nat.sub_add_cancel hj0] at this
      rw [this, ← add_assoc, negOnePowCast_add (R := R) _ 1, negOnePowCast_one, mul_neg_one,
        add_neg_cancel]
    simp only [hS] at hsign
    rw [hsign, zero_smul]
  · have hW : splice R x 0 (n + 1) (j.1 - 1) 2 (x ⟨j.1 - 1, by omega⟩) = subword R x 0 n :=
      splice_two_pred_eq_subword R (by omega) x
    have hsub := subword_mem_gradedPiece x (fun i ↦ if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0)
      (fun i ↦ by simpa only [Fin.is_lt, dite_true, Fin.eta] using hx i) 0 n
    have hdeg : F (subword R x 0 n) ∈ BB.grading.piece (S n + 1) := by
      simpa [hS, InternalGrading.shift_piece] using
        (isHomogeneous_extendTaylor ε ε' g).map_mem hsub
    simp (disch := omega) only [ite_eq_right, ite_eq_left, zero_add]
    rw [hW, smul_smul, ← negOnePowCast_add, BB.grading.koszulTwist_one_apply_of_mem hdeg,
      ← negOnePowCast_eq_intCast]
    have hSn : S n = S (j.1 - 1) + 𝒟 ⟨j.1 - 1, by omega⟩ := by
      rw [← hSsucc]
      congr 1
      omega
    congr 2
    simp only [hS] at hSn ⊢
    rw [hSn]
    ring

private theorem taylor_comp_coalgHom_extendTaylor (ε : AA.Augmentation) (ε' : BB.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    BB.taylor ∘ₗ coalgHom R (extendTaylor ε ε' g) =
      extendTaylor ε ε' g ∘ₗ AA.barDifferential := by
  set F := extendTaylor ε ε' g
  suffices hker : (⊤ : Submodule R (ReducedTensorWords R A)) ≤
      LinearMap.ker (BB.taylor ∘ₗ coalgHom R F - F ∘ₗ AA.barDifferential) by
    refine LinearMap.ext fun z ↦ sub_eq_zero.mp ?_
    exact LinearMap.mem_ker.mp (hker Submodule.mem_top)
  refine le_trans ε.top_le_range_map_subtype_sup_degenerateWords (sup_le ?_ ?_)
  · rw [LinearMap.range_le_iff_comap, eq_top_iff]
    intro u _
    rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    have hFsub : F ∘ₗ ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype =
        ε'.augmentationIdeal.subtype ∘ₗ g.taylor := by
      have hmap : ReducedTensorWords.map (R := R) ε.reducedPart ∘ₗ
          ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype = LinearMap.id := by
        rw [← map_comp, ε.reducedPart_comp_subtype, map_id]
      refine LinearMap.ext fun v ↦ ?_
      have hv := LinearMap.congr_fun hmap v
      have hl := LinearMap.congr_fun (letter_comp_map (R := R) ε.augmentationIdeal.subtype) v
      simp only [F, extendTaylor, LinearMap.add_apply, LinearMap.comp_apply,
        Submodule.subtype_apply] at hv hl ⊢
      rw [hl, ε.apply_coe_augmentationIdeal, map_zero, zero_add, hv, LinearMap.id_apply]
    have hcoalg : coalgHom R F ∘ₗ ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype =
        ε'.reducedInclusion.barMap ∘ₗ g.barMap := by
      rw [((isCoalgHom_coalgHom F).comp (isCoalgHom_map _)).eq_coalgHom, ← LinearMap.comp_assoc,
        letter_comp_coalgHom, hFsub, ← map_comp_coalgHom, barMap_reducedInclusion,
        g.barMap_eq_coalgHom]
    have h1 := LinearMap.congr_fun hcoalg u
    have h2 := LinearMap.congr_fun ε'.reducedInclusion.taylor_comp_barMap (g.barMap u)
    have h3 := LinearMap.congr_fun g.taylor_comp_barMap u
    have h4 := ε.reducedInclusion.toAInfinityHom.barDifferential_barMap u
    have h5 := LinearMap.congr_fun hFsub (ε.reducedAlgebra.barDifferential u)
    simp only [LinearMap.comp_apply, toLinearMap_reducedInclusion,
      AInfinityStrictHom.barMap_toAInfinityHom, barMap_reducedInclusion] at h1 h2 h3 h4 h5 ⊢
    rw [h1, h2, h3, h4, h5]
  · rw [degenerateWords_le_iff_of_mem_piece _ ε.isStrictUnit.mem_shift_one_piece]
    rintro ⟨_ | n, hN⟩ x 𝒟 j hx hj _
    · omega
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.comp_apply,
        LinearMap.comp_apply, taylor_coalgHom_extendTaylor_of_tprod ε ε' g x j hj,
        extendTaylor_barDifferential_of_tprod ε ε' g x 𝒟 hx j hj]

/-- Extend an `A∞` morphism `g : ε.reducedAlgebra ⟶ ε'.reducedAlgebra` between reduced augmentation
ideals to a strictly unital augmented `A∞` morphism `A ⟶ B`. -/
noncomputable def extendHom (ε : AA.Augmentation) (ε' : BB.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    AInfinityHom AA BB :=
  AInfinityHom.ofTaylor (extendTaylor ε ε' g) (isHomogeneous_extendTaylor ε ε' g)
    (taylor_comp_coalgHom_extendTaylor ε ε' g)

@[simp]
theorem taylor_extendHom (ε : AA.Augmentation) (ε' : BB.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    (ε.extendHom ε' g).taylor =
      ε'.unitHom ∘ₗ ε.toLinearMap ∘ₗ letter R A +
        ε'.augmentationIdeal.subtype ∘ₗ g.taylor ∘ₗ
          ReducedTensorWords.map (R := R) ε.reducedPart :=
  AInfinityHom.taylor_ofTaylor _ _ _

@[simp]
theorem linearPart_extendHom (ε : AA.Augmentation) (ε' : BB.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    (ε.extendHom ε' g).linearPart =
      ε'.unitHom ∘ₗ ε.toLinearMap +
        ε'.augmentationIdeal.subtype ∘ₗ g.linearPart ∘ₗ ε.reducedPart := by
  ext a
  rw [AInfinityHom.linearPart_apply, taylor_extendHom]
  simp [AInfinityHom.linearPart_apply]

theorem linearPart_extendHom_apply (ε : AA.Augmentation) (ε' : BB.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) (a : A) :
    (ε.extendHom ε' g).linearPart a =
      ε a • ε'.unit + (g.linearPart (ε.reducedPart a) : B) := by
  rw [linearPart_extendHom]
  simp

/-- The extended `A∞` morphism `extendHom ε ε' g` is strictly unital. -/
theorem isStrictlyUnital_extendHom (ε : AA.Augmentation) (ε' : BB.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    (ε.extendHom ε' g).IsStrictlyUnital ε.isStrictUnit ε'.isStrictUnit where
  map_unit := by simp
  component_eq_zero {n} hn x hx := by
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp
    · obtain ⟨i, hi⟩ := hx
      rw [AInfinityHom.component_apply _ n hnpos, extendHom, AInfinityHom.taylor_ofTaylor]
      exact extendTaylor_of_tprod_eq_zero ε ε' g ⟨n, hnpos⟩ hn _
        ⟨i, by rw [hi, AA.grading.koszulTwist_apply_of_mem_zero ε.isStrictUnit.degree_zero]⟩

/-- The extended `A∞` morphism `extendHom ε ε' g` is augmented. -/
theorem isAugmented_extendHom (ε : AA.Augmentation) (ε' : BB.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    (ε.extendHom ε' g).IsAugmented ε ε' := by
  rw [AInfinityHom.isAugmented_iff_taylor]
  refine LinearMap.ext fun z ↦ ?_
  simp [taylor_extendHom]

@[simp]
theorem restrictReduced_extendHom (ε : AA.Augmentation) (ε' : BB.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    (ε.isAugmented_extendHom ε' g).restrictReduced = g := by
  refine AInfinityHom.ext <| LinearMap.ext fun z ↦ ?_
  have hz : ReducedTensorWords.map (R := R) ε.reducedPart
      (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype z) = z := by
    rw [← LinearMap.comp_apply, ← map_comp, ε.reducedPart_comp_subtype, map_id, LinearMap.id_apply]
  have hl : ε (letter R A (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype z)) = 0 := by
    have h := LinearMap.congr_fun (letter_comp_map (R := R) ε.augmentationIdeal.subtype) z
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply] at h
    rw [h, ε.apply_coe_augmentationIdeal]
  rw [AInfinityHom.IsAugmented.taylor_restrictReduced, taylor_extendHom]
  simp only [LinearMap.comp_apply, LinearMap.add_apply, hl, map_zero, zero_add,
    Submodule.subtype_apply, ε'.reducedPart_coe, hz]

@[simp]
theorem extendHom_comp_reducedInclusion (ε : AA.Augmentation) (ε' : BB.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    (ε.extendHom ε' g).comp ε.reducedInclusion.toAInfinityHom =
      ε'.reducedInclusion.toAInfinityHom.comp g := by
  rw [← (ε.isAugmented_extendHom ε' g).reducedInclusion_comp_restrictReduced,
    restrictReduced_extendHom]

/-- Every strictly unital augmented `A∞` morphism is the canonical extension of its restriction to
the reduced augmentation ideals. -/
@[simp]
theorem extendHom_restrictReduced (ε : AA.Augmentation) (ε' : BB.Augmentation)
    {f : AInfinityHom AA BB} (hfu : f.IsStrictlyUnital ε.isStrictUnit ε'.isStrictUnit)
    (hfa : f.IsAugmented ε ε') :
    ε.extendHom ε' hfa.restrictReduced = f := by
  suffices hker : (⊤ : Submodule R (ReducedTensorWords R A)) ≤
      LinearMap.ker ((ε.extendHom ε' hfa.restrictReduced).taylor - f.taylor) by
    refine AInfinityHom.ext <| LinearMap.ext fun z ↦ sub_eq_zero.mp ?_
    exact LinearMap.mem_ker.mp (hker Submodule.mem_top)
  refine le_trans ε.top_le_range_map_subtype_sup_degenerateWords (sup_le ?_ ?_)
  · rw [LinearMap.range_le_iff_comap, eq_top_iff]
    intro u _
    rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    have h1 := congrArg (fun k ↦ k.taylor u)
      ((ε.extendHom_comp_reducedInclusion ε' hfa.restrictReduced).trans
        hfa.reducedInclusion_comp_restrictReduced)
    simpa only [AInfinityHom.taylor_comp, LinearMap.comp_apply,
      AInfinityStrictHom.barMap_toAInfinityHom, barMap_reducedInclusion] using h1
  · rw [degenerateWords_le_iff]
    rintro ⟨k, hk⟩ x hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    have hext_u := ε.isStrictlyUnital_extendHom ε' hfa.restrictReduced
    by_cases hk1 : k = 1
    · subst hk1
      obtain ⟨i, hi⟩ := hx
      have h0 : i = 0 := Subsingleton.elim i 0
      subst h0
      have hword : of R A ⟨1, hk⟩ (PiTensorProduct.tprod R x) = ofLetter R A ε.unit := by
        rw [of_tprod_eq_subword R hk, subword_one R A x hk]
        exact congrArg (ofLetter R A) hi
      rw [hword, ← AInfinityHom.linearPart_apply, ← AInfinityHom.linearPart_apply,
        hext_u.map_unit, hfu.map_unit]
    · rw [hext_u.taylor_of_tprod_eq_zero ⟨k, hk⟩ hk1 x hx,
        hfu.taylor_of_tprod_eq_zero ⟨k, hk⟩ hk1 x hx]

/-- **Equivalence between strictly unital augmented `A∞` morphisms and reduced `A∞` morphisms**:
restricting to `ker ε ⟶ ker ε'` and extending along `A ≃ R · 1_A ⊕ ker ε` are mutually inverse
bijections. -/
noncomputable def homEquivReduced (ε : AA.Augmentation) (ε' : BB.Augmentation) :
    {f : AInfinityHom AA BB //
      f.IsStrictlyUnital ε.isStrictUnit ε'.isStrictUnit ∧ f.IsAugmented ε ε'} ≃
      AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra where
  toFun f := f.property.2.restrictReduced
  invFun g := ⟨ε.extendHom ε' g, ε.isStrictlyUnital_extendHom ε' g, ε.isAugmented_extendHom ε' g⟩
  left_inv f := Subtype.ext (ε.extendHom_restrictReduced ε' f.property.1 f.property.2)
  right_inv g := ε.restrictReduced_extendHom ε' g

@[simp]
theorem homEquivReduced_apply (ε : AA.Augmentation) (ε' : BB.Augmentation)
    (f : {f : AInfinityHom AA BB //
      f.IsStrictlyUnital ε.isStrictUnit ε'.isStrictUnit ∧ f.IsAugmented ε ε'}) :
    ε.homEquivReduced ε' f = f.property.2.restrictReduced := (rfl)

@[simp]
theorem homEquivReduced_symm_apply (ε : AA.Augmentation) (ε' : BB.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    ((ε.homEquivReduced ε').symm g).val = ε.extendHom ε' g := (rfl)

@[simp]
theorem extendHom_id (ε : AA.Augmentation) :
    ε.extendHom ε (AInfinityHom.id ε.reducedAlgebra) = AInfinityHom.id AA := by
  rw [← AInfinityHom.IsAugmented.restrictReduced_id ε]
  exact ε.extendHom_restrictReduced ε (AInfinityHom.isStrictlyUnital_id ε.isStrictUnit)
    (AInfinityHom.isAugmented_id ε)

@[simp]
theorem extendHom_comp {C : Type uC} [AddCommGroup C] [Module R C] {CC : AInfinityAlgebra R C}
    (ε : AA.Augmentation) (ε' : BB.Augmentation) (ε'' : CC.Augmentation)
    (g' : AInfinityHom ε'.reducedAlgebra ε''.reducedAlgebra)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    ε.extendHom ε'' (g'.comp g) = (ε'.extendHom ε'' g').comp (ε.extendHom ε' g) := by
  have hu := (ε'.isStrictlyUnital_extendHom ε'' g').comp (ε.isStrictlyUnital_extendHom ε' g)
  have ha := (ε'.isAugmented_extendHom ε'' g').comp (ε.isAugmented_extendHom ε' g)
  have hres : ha.restrictReduced = g'.comp g := by
    rw [AInfinityHom.IsAugmented.restrictReduced_comp
        (ε'.isAugmented_extendHom ε'' g') (ε.isAugmented_extendHom ε' g),
      ε'.restrictReduced_extendHom ε'' g', ε.restrictReduced_extendHom ε' g]
  rw [← hres, ε.extendHom_restrictReduced ε'' hu ha]

end AInfinityAlgebra.Augmentation

end ExtendHom

end TauCeti
