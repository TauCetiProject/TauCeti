/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Augmentation
public import TauCeti.Algebra.Homology.AInfinity.Algebra.DG
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Unital
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Unit.Degenerate
public import TauCeti.Algebra.Homology.DG.Algebra.Augmentation

/-!
# Augmented morphisms of `A∞` algebras and reduction to the augmentation ideal

Let `(A, ε)` and `(B, ε')` be augmented uncurved `A∞` algebras over `R`.  An `A∞` morphism
`f : A ⟶ B` is **augmented** (`AInfinityHom.IsAugmented`) when it is strictly unital for the
chosen strict units, its linear component intertwines the augmentations (`ε' ∘ f₁ = ε`), and all
higher components `f_n` (`n ≠ 1`) take values in the target augmentation ideal `ker ε'`.

Equivalently, on suspended Taylor components, `f` is strictly unital and satisfies
`ε' ∘ f.taylor = ε ∘ letter` (`isAugmented_iff_taylor`).  From this characterization closure under
identities and composition is immediate, and for a morphism of unital DG algebras regarded as a
strict `A∞` morphism, being augmented is equivalent to `ε_B ∘ φ = ε_A`
(`DGAlgHom.isAugmented_toAInfinityHom_iff`).

Crucially, because the strict unit splits `A ≃ R ⊕ ker ε` and `B ≃ R ⊕ ker ε'`, strictly unital
augmented `A∞` morphisms `A ⟶ B` are in canonical bijection with arbitrary nonunital `A∞`
morphisms `ker ε ⟶ ker ε'` between the reduced augmentation ideals
(`AInfinityAlgebra.Augmentation.augmentedHomEquiv`):

* restricting `f` along the strict inclusion `ε.inclusion : ker ε ⟶ A` lands in `ker ε'` and defines
  `hf.reducedHom : ker ε ⟶ ker ε'`;
* conversely, any `A∞` morphism `g : ker ε ⟶ ker ε'` extends uniquely to `A ⟶ B`
  (`ε.extendReducedHom ε' g`) via the Taylor map sending a word `z` to `ε(z₁) • 1_B + g(π(z))`,
  where `π(z)` applies `ε.reducedPart` to every letter of `z`.  On words of `ker ε` the Stasheff
  morphism equations reduce to those of `g`, while on unit-containing words both sides collapse to
  the initial/final boundary terms `g(z₂ ⋯ zₙ)` and `(-1)^{|g(z₁ ⋯ z_{n-1})|} g(z₁ ⋯ z_{n-1})`.

## Main definitions

* `TauCeti.AInfinityAlgebra.Augmentation.inclusion`: the strict `A∞` inclusion `ker ε ⟶ A`.
* `TauCeti.AInfinityHom.IsAugmented`: strictly unital augmentation-preserving `A∞` morphisms.
* `TauCeti.DGAlgAugmentation.toAInfinityAugmentation`: a DG algebra augmentation as an `A∞`
  augmentation.
* `TauCeti.AInfinityHom.IsAugmented.reducedHom`: the induced `A∞` morphism `ker ε ⟶ ker ε'`.
* `TauCeti.AInfinityAlgebra.Augmentation.extendReducedHom`: extension of a reduced `A∞` morphism
  `ker ε ⟶ ker ε'` to a strictly unital augmented morphism `A ⟶ B`.
* `TauCeti.AInfinityAlgebra.Augmentation.augmentedHomEquiv`: the equivalence between strictly unital
  augmented `A∞` morphisms `A ⟶ B` and nonunital `A∞` morphisms `ker ε ⟶ ker ε'`.
* `TauCeti.AInfinityAlgebra.Augmentation.liftReducedHomEquiv`: the universal property of `ker ε'`
  for `A∞` morphisms whose Taylor map vanishes under `ε'`.

## Main results

* `TauCeti.AInfinityHom.isAugmented_iff_taylor`: Taylor characterization of augmented morphisms.
* `TauCeti.AInfinityHom.isAugmented_id` and `TauCeti.AInfinityHom.IsAugmented.comp`: identity and
  composition laws.
* `TauCeti.DGAlgHom.isAugmented_toAInfinityHom_iff`: compatibility with DG algebra augmentations.
* `TauCeti.AInfinityHom.IsAugmented.reducedHom_id` and `reducedHom_comp`: functoriality of
  reduction to the augmentation ideal.
* `TauCeti.AInfinityHom.IsAugmented.ext_comp_inclusion`: augmented morphisms are determined by their
  restrictions to the source augmentation ideal.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
* B. Keller, *A-infinity algebras, modules and functor categories*, Section 4.
-/

public section

namespace TauCeti

open ReducedTensorWords

universe uR uA uB uC

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

/-! ### Strict inclusion and projection of the augmentation ideal -/

namespace AInfinityAlgebra.Augmentation

variable {𝒜 : AInfinityAlgebra R A}

/-- The canonical strict `A∞` inclusion of the reduced augmentation ideal `ker ε` into `A`. -/
noncomputable def inclusion (ε : 𝒜.Augmentation) : AInfinityStrictHom ε.reducedAlgebra 𝒜 where
  toLinearMap := ε.augmentationIdeal.subtype
  map_mem' hx := by
    rw [ε.reducedAlgebra_grading, ε.reducedGrading_piece, Submodule.mem_comap] at hx
    exact hx
  map_m' n := by
    ext x
    rw [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      Submodule.subtype_apply, ε.reducedAlgebra_m, ε.coe_reducedOperation]
    rfl

@[simp]
theorem inclusion_toLinearMap (ε : 𝒜.Augmentation) :
    ε.inclusion.toLinearMap = ε.augmentationIdeal.subtype := (rfl)

@[simp]
theorem inclusion_apply (ε : 𝒜.Augmentation) (x : ε.augmentationIdeal) :
    ε.inclusion x = x := (rfl)

/-- The reduced-part projection annihilates the strict unit. -/
@[simp]
theorem reducedPart_unit (ε : 𝒜.Augmentation) : ε.reducedPart ε.unit = 0 := by
  apply Subtype.ext
  rw [coe_reducedPart, map_unit, one_smul, sub_self, Submodule.coe_zero]

/-- The reduced-part projection is homogeneous of degree zero. -/
theorem isHomogeneous_reducedPart (ε : 𝒜.Augmentation) :
    LinearMap.IsHomogeneous ε.reducedPart 𝒜.grading.piece ε.reducedAlgebra.grading.piece 0 := by
  refine LinearMap.isHomogeneous_def.mpr fun p a ha ↦ ?_
  rw [add_zero, ε.reducedAlgebra_grading, ε.reducedGrading_piece, Submodule.mem_comap,
    Submodule.subtype_apply, ε.coe_reducedPart]
  by_cases hp : p = 0
  · subst hp
    exact Submodule.sub_mem _ ha (Submodule.smul_mem _ _ ε.isStrictUnit.degree_zero)
  · rw [ε.map_of_mem_ne_zero p a ha hp, zero_smul, sub_zero]
    exact ha

/-- The reduced-part projection is homogeneous of degree zero for the suspended gradings. -/
theorem isHomogeneous_reducedPart_shift_one (ε : 𝒜.Augmentation) :
    LinearMap.IsHomogeneous ε.reducedPart (𝒜.grading.shift 1).piece
      (ε.reducedAlgebra.grading.shift 1).piece 0 := by
  refine LinearMap.isHomogeneous_def.mpr fun p a ha ↦ ?_
  rw [InternalGrading.shift_piece] at ha
  simpa only [InternalGrading.shift_piece, add_zero] using ε.isHomogeneous_reducedPart.map_mem ha

theorem reducedPart_comp_inclusion_toLinearMap (ε : 𝒜.Augmentation) :
    ε.reducedPart ∘ₗ ε.inclusion.toLinearMap = LinearMap.id :=
  LinearMap.ext ε.reducedPart_coe

@[simp]
theorem map_reducedPart_comp_inclusion_barMap (ε : 𝒜.Augmentation) :
    ReducedTensorWords.map (R := R) ε.reducedPart ∘ₗ ε.inclusion.barMap = LinearMap.id := by
  rw [AInfinityStrictHom.barMap_def, ← ReducedTensorWords.map_comp,
    ε.reducedPart_comp_inclusion_toLinearMap, ReducedTensorWords.map_id]

theorem comp_inclusion_toLinearMap (ε : 𝒜.Augmentation) :
    ε.toLinearMap ∘ₗ ε.inclusion.toLinearMap = 0 := by
  ext x
  exact (ε.mem_augmentationIdeal).mp x.property

/-- An `A∞` augmentation is invariant under every Koszul sign twist, since it vanishes outside
degree zero and the Koszul twist fixes degree zero. -/
@[simp]
theorem map_koszulTwist (ε : 𝒜.Augmentation) (q : ℤ) (x : A) :
    ε (𝒜.grading.koszulTwist q x) = ε x := by
  induction x using DirectSum.Decomposition.inductionOn 𝒜.grading.piece with
  | zero => simp
  | @homogeneous p x =>
    rw [𝒜.grading.koszulTwist_apply_of_mem x.2 q, map_smul]
    by_cases hp : p = 0
    · subst hp
      simp
    · rw [ε.map_of_mem_ne_zero p _ x.2 hp, smul_zero]
  | add x y hx hy => simp [map_add, hx, hy]

theorem koszulTwist_mem_augmentationIdeal_iff (ε : 𝒜.Augmentation) (q : ℤ) (x : A) :
    𝒜.grading.koszulTwist q x ∈ ε.augmentationIdeal ↔ x ∈ ε.augmentationIdeal := by
  rw [mem_augmentationIdeal, mem_augmentationIdeal, ε.map_koszulTwist]

end AInfinityAlgebra.Augmentation

/-! ### Augmented `A∞` morphisms -/

namespace AInfinityHom

variable {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B} {𝒞 : AInfinityAlgebra R C}

/-- A morphism of augmented `A∞` algebras is **augmented** when it is strictly unital, its linear
part intertwines the augmentations, and all higher components take values in the target
augmentation ideal. -/
structure IsAugmented (f : AInfinityHom 𝒜 ℬ) (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation) : Prop where
  /-- The morphism is strictly unital for the chosen strict units. -/
  isStrictlyUnital : f.IsStrictlyUnital ε.isStrictUnit ε'.isStrictUnit
  /-- The linear component intertwines the augmentations. -/
  map_augmentation : ε'.toLinearMap ∘ₗ f.linearPart = ε.toLinearMap
  /-- Every component above arity one lands in the target augmentation ideal. -/
  augmentation_component_eq_zero : ∀ {n : ℕ}, n ≠ 1 → ∀ x : Fin n → A, ε' (f.component n x) = 0

/-- On suspended Taylor components, `f` is augmented exactly when it is strictly unital and
`ε' ∘ f.taylor = ε ∘ letter`. -/
theorem isAugmented_iff_taylor {f : AInfinityHom 𝒜 ℬ} {ε : 𝒜.Augmentation}
    {ε' : ℬ.Augmentation} :
    f.IsAugmented ε ε' ↔
      f.IsStrictlyUnital ε.isStrictUnit ε'.isStrictUnit ∧
        ε'.toLinearMap ∘ₗ f.taylor = ε.toLinearMap ∘ₗ letter R A := by
  constructor
  · intro hf
    refine ⟨hf.isStrictlyUnital, linearMap_ext R A fun n x ↦ ?_⟩
    simp only [LinearMap.comp_apply]
    by_cases hn1 : n.1 = 1
    · obtain ⟨k, hk⟩ := n
      dsimp only at hn1
      subst k
      rw [of_tprod_eq_subword R hk, subword_one R A x hk, letter_ofLetter, ← f.linearPart_apply]
      exact LinearMap.congr_fun hf.map_augmentation (x 0)
    · have htwist : f.component n.1
          (fun i ↦ 𝒜.grading.koszulTwist ((n.1 : ℤ) - 1 - i) (x i)) =
          f.taylor (of R A n (PiTensorProduct.tprod R x)) := by
        rw [component_apply f n.1 n.2]
        simp only [InternalGrading.koszulTwist_koszulTwist]
      rw [← htwist, of_tprod_eq_subword R n.2, letter_subword_of_ne_one R A x 0 hn1, map_zero]
      exact hf.augmentation_component_eq_zero hn1 _
  · rintro ⟨hsu, htaylor⟩
    refine ⟨hsu, ?_, ?_⟩
    · ext a
      have ha := LinearMap.congr_fun htaylor (ofLetter R A a)
      simpa only [LinearMap.comp_apply, letter_ofLetter, linearPart_apply] using ha
    · intro n hn x
      rcases Nat.eq_zero_or_pos n with rfl | hnpos
      · simp
      · rw [component_apply f n hnpos]
        have hx := LinearMap.congr_fun htaylor
          (of R A ⟨n, hnpos⟩
            (PiTensorProduct.tprod R fun i ↦ 𝒜.grading.koszulTwist ((n : ℤ) - 1 - i) (x i)))
        simp only [LinearMap.comp_apply] at hx
        rw [of_tprod_eq_subword R hnpos, letter_subword_of_ne_one R A _ 0 hn, map_zero] at hx
        rw [of_tprod_eq_subword R hnpos]
        exact hx

/-- The identity `A∞` morphism is augmented. -/
@[simp]
theorem isAugmented_id (ε : 𝒜.Augmentation) : (AInfinityHom.id 𝒜).IsAugmented ε ε :=
  isAugmented_iff_taylor.2 ⟨isStrictlyUnital_id ε.isStrictUnit, by rw [taylor_id]⟩

/-- Augmented `A∞` morphisms are closed under composition. -/
theorem IsAugmented.comp {g : AInfinityHom ℬ 𝒞} {f : AInfinityHom 𝒜 ℬ}
    {ε : 𝒜.Augmentation} {ε' : ℬ.Augmentation} {ε'' : 𝒞.Augmentation}
    (hg : g.IsAugmented ε' ε'') (hf : f.IsAugmented ε ε') :
    (g.comp f).IsAugmented ε ε'' := by
  rw [isAugmented_iff_taylor] at hg hf ⊢
  refine ⟨hg.1.comp hf.1, ?_⟩
  rw [taylor_comp, ← LinearMap.comp_assoc, hg.2, LinearMap.comp_assoc, ← f.taylor_def, hf.2]

/-- A strict `A∞` morphism is augmented if and only if its linear part preserves the unit and
intertwines the augmentations. -/
theorem IsStrict.isAugmented_iff {f : AInfinityHom 𝒜 ℬ} {ε : 𝒜.Augmentation}
    {ε' : ℬ.Augmentation} (hf : f.IsStrict) :
    f.IsAugmented ε ε' ↔
      f.linearPart ε.unit = ε'.unit ∧ ε'.toLinearMap ∘ₗ f.linearPart = ε.toLinearMap := by
  rw [isAugmented_iff_taylor, hf.isStrictlyUnital_iff]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext a
    have ha := LinearMap.congr_fun h (ofLetter R A a)
    simpa only [LinearMap.comp_apply, letter_ofLetter, linearPart_apply] using ha
  · rw [(isStrict_iff f).1 hf, ← LinearMap.comp_assoc, h]

end AInfinityHom

/-! ### Compatibility with augmented DG algebras -/

section DG

variable {D : Type uA} {E : Type uB} [Ring D] [Ring E] [Algebra R D] [Algebra R E]
  {𝒟 : ℤ → Submodule R D} {ℰ : ℤ → Submodule R E} [GradedAlgebra 𝒟] [GradedAlgebra ℰ]
  {dD : D →ₗ[R] D} {dE : E →ₗ[R] E} {hD : IsDGAlgebra 𝒟 dD} {hE : IsDGAlgebra ℰ dE}

namespace DGAlgAugmentation

/-- An augmentation of a differential graded algebra induces an augmentation of its underlying
`A∞` algebra. -/
noncomputable def toAInfinityAugmentation (e : DGAlgAugmentation hD) :
    hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.Augmentation where
  unit := 1
  isStrictUnit := hD.strictUnit_one
  toLinearMap := e.toGradedAlgHom.toAlgHom.toLinearMap
  map_unit := map_one e
  map_of_mem_ne_zero p x hx hp := by
    rw [IsNonUnitalDGAlgebra.toAInfinityAlgebra_grading,
      InternalGrading.ofDecomposition_piece] at hx
    rcases (mem_trivialGrading_iff R R).mp (e.map_mem hx) with h0 | hzero
    · exact absurd h0 hp
    · exact hzero
  map_binary x y := by
    rw [IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_two_apply]
    exact map_mul e x y
  map_m_of_ne_two n hn0 hn2 x := by
    rcases n with _ | _ | _ | n
    · omega
    · rw [IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_one_apply]
      exact e.map_d (x 0)
    · exact absurd rfl hn2
    · simp

@[simp]
theorem toAInfinityAugmentation_unit (e : DGAlgAugmentation hD) :
    e.toAInfinityAugmentation.unit = 1 := (rfl)

@[simp]
theorem toAInfinityAugmentation_toLinearMap (e : DGAlgAugmentation hD) :
    e.toAInfinityAugmentation.toLinearMap = e.toGradedAlgHom.toAlgHom.toLinearMap := (rfl)

theorem toAInfinityAugmentation_apply (e : DGAlgAugmentation hD) (x : D) :
    e.toAInfinityAugmentation x = e x := (rfl)

@[simp]
theorem toAInfinityAugmentation_augmentationIdeal (e : DGAlgAugmentation hD) :
    e.toAInfinityAugmentation.augmentationIdeal = e.augmentationIdeal.toSubmodule := by
  ext x
  simp [AInfinityAlgebra.Augmentation.mem_augmentationIdeal]

/-- A DG algebra augmentation is invariant under every Koszul sign twist. -/
@[simp]
theorem map_koszulTwist (e : DGAlgAugmentation hD) (q : ℤ) (x : D) :
    e ((InternalGrading.ofDecomposition 𝒟).koszulTwist q x) = e x := by
  simpa [hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra_grading] using
    e.toAInfinityAugmentation.map_koszulTwist q x

theorem koszulTwist_mem_augmentationIdeal_iff (e : DGAlgAugmentation hD) (q : ℤ) (x : D) :
    (InternalGrading.ofDecomposition 𝒟).koszulTwist q x ∈ e.augmentationIdeal ↔
      x ∈ e.augmentationIdeal := by
  rw [mem_augmentationIdeal, mem_augmentationIdeal, e.map_koszulTwist]

end DGAlgAugmentation

namespace DGAlgHom

/-- A unital DG algebra morphism, viewed as a strict `A∞` morphism, is augmented if and only if it
commutes with the DG algebra augmentations. -/
@[simp]
theorem isAugmented_toAInfinityHom_iff (φ : DGAlgHom hD hE)
    (eD : DGAlgAugmentation hD) (eE : DGAlgAugmentation hE) :
    φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.IsAugmented
        eD.toAInfinityAugmentation eE.toAInfinityAugmentation ↔
      eE.comp φ = eD := by
  rw [(AInfinityHom.isStrict_toAInfinityHom _).isAugmented_iff]
  simp only [AInfinityStrictHom.linearPart_toAInfinityHom,
    DGAlgAugmentation.toAInfinityAugmentation_unit]
  have h1 : φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toLinearMap 1 = (1 : E) := by simp
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨h1, ?_⟩⟩
  · ext x
    simpa using LinearMap.congr_fun h.2 x
  · ext x
    simpa using congrArg (fun ψ ↦ ψ x) h

end DGAlgHom

end DG

/-! ### Equivalence with nonunital `A∞` morphisms on augmentation ideals -/

namespace AInfinityHom.IsAugmented

variable {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B} {𝒞 : AInfinityAlgebra R C}
  {f : AInfinityHom 𝒜 ℬ} {ε : 𝒜.Augmentation} {ε' : ℬ.Augmentation}

/-- Restricting the Taylor map of an augmented morphism to words in `ker ε` lands in `ker ε'`, so
including `ε'.reducedPart` recovers the original Taylor values. -/
theorem inclusion_comp_reducedPart_taylor (hf : f.IsAugmented ε ε') :
    ε'.inclusion.toLinearMap ∘ₗ ε'.reducedPart ∘ₗ f.taylor ∘ₗ ε.inclusion.barMap =
      f.taylor ∘ₗ ε.inclusion.barMap := by
  have hzero : ε'.toLinearMap ∘ₗ f.taylor ∘ₗ ε.inclusion.barMap = 0 := by
    rw [← LinearMap.comp_assoc, (isAugmented_iff_taylor.1 hf).2, LinearMap.comp_assoc,
      AInfinityStrictHom.barMap_def, letter_comp_map, ← LinearMap.comp_assoc,
      AInfinityAlgebra.Augmentation.inclusion_toLinearMap, ← ε.inclusion_toLinearMap,
      ε.comp_inclusion_toLinearMap, LinearMap.zero_comp]
  refine LinearMap.ext fun w ↦ ?_
  have hw : ε' (f.taylor (ε.inclusion.barMap w)) = 0 := LinearMap.congr_fun hzero w
  simp only [LinearMap.comp_apply, AInfinityAlgebra.Augmentation.inclusion_toLinearMap,
    Submodule.subtype_apply, AInfinityAlgebra.Augmentation.coe_reducedPart, hw, zero_smul, sub_zero]

private theorem reducedTaylor_isHomogeneous (f : AInfinityHom 𝒜 ℬ)
    (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation) :
    LinearMap.IsHomogeneous (ε'.reducedPart ∘ₗ f.taylor ∘ₗ ε.inclusion.barMap)
      (gradedPiece (ε.reducedAlgebra.grading.shift 1))
      (ε'.reducedAlgebra.grading.shift 1).piece 0 := by
  have h1 : LinearMap.IsHomogeneous (f.taylor ∘ₗ ε.inclusion.barMap)
      (gradedPiece (ε.reducedAlgebra.grading.shift 1)) (ℬ.grading.shift 1).piece 0 := by
    simpa only [add_zero] using f.isHomogeneous_taylor.comp ε.inclusion.isHomogeneous_barMap
  simpa only [add_zero] using ε'.isHomogeneous_reducedPart_shift_one.comp h1

private theorem reducedTaylor_component_eq (hf : f.IsAugmented ε ε') :
    ε'.reducedAlgebra.taylor ∘ₗ coalgHom R (ε'.reducedPart ∘ₗ f.taylor ∘ₗ ε.inclusion.barMap) =
      (ε'.reducedPart ∘ₗ f.taylor ∘ₗ ε.inclusion.barMap) ∘ₗ ε.reducedAlgebra.barDifferential := by
  have hinj : Function.Injective ε'.inclusion.toLinearMap := Subtype.val_injective
  refine LinearMap.ext fun w ↦ hinj ?_
  have hcoalg : ε'.inclusion.barMap ∘ₗ
      coalgHom R (ε'.reducedPart ∘ₗ f.taylor ∘ₗ ε.inclusion.barMap) =
      f.barMap ∘ₗ ε.inclusion.barMap := by
    rw [AInfinityStrictHom.barMap_def, map_comp_coalgHom, hf.inclusion_comp_reducedPart_taylor]
    have hcomp : coalgHom R f.taylor ∘ₗ ε.inclusion.barMap =
        coalgHom R (f.taylor ∘ₗ ε.inclusion.barMap) := by
      rw [AInfinityStrictHom.barMap_def,
        ((isCoalgHom_coalgHom f.taylor).comp (isCoalgHom_map _)).eq_coalgHom,
        ← LinearMap.comp_assoc, letter_comp_coalgHom]
    rw [← hcomp, ← f.barMap_eq_coalgHom]
  have hLHS : ε'.inclusion.toLinearMap
      ((ε'.reducedAlgebra.taylor ∘ₗ
        coalgHom R (ε'.reducedPart ∘ₗ f.taylor ∘ₗ ε.inclusion.barMap)) w) =
      (f.taylor ∘ₗ 𝒜.barDifferential ∘ₗ ε.inclusion.barMap) w := by
    have h1 := LinearMap.congr_fun ε'.inclusion.taylor_comp_barMap
      (coalgHom R (ε'.reducedPart ∘ₗ f.taylor ∘ₗ ε.inclusion.barMap) w)
    have h2 := LinearMap.congr_fun hcoalg w
    have h3 := LinearMap.congr_fun f.taylor_comp_barMap (ε.inclusion.barMap w)
    simp only [LinearMap.comp_apply] at h1 h2 h3 ⊢
    rw [← h1, h2, h3]
  have hRHS : ε'.inclusion.toLinearMap
      (((ε'.reducedPart ∘ₗ f.taylor ∘ₗ ε.inclusion.barMap) ∘ₗ
        ε.reducedAlgebra.barDifferential) w) =
      (f.taylor ∘ₗ 𝒜.barDifferential ∘ₗ ε.inclusion.barMap) w := by
    have hpt := LinearMap.congr_fun hf.inclusion_comp_reducedPart_taylor
      (ε.reducedAlgebra.barDifferential w)
    have hbd := LinearMap.congr_fun ε.inclusion.barDifferential_comp_barMap w
    simp only [LinearMap.comp_apply] at hpt hbd ⊢
    rw [hpt, ← hbd]
  exact hLHS.trans hRHS.symm

/-- The nonunital `A∞` morphism `ker ε ⟶ ker ε'` induced on reduced augmentation ideals by a
strictly unital augmented `A∞` morphism `f : A ⟶ B`. -/
noncomputable def reducedHom (hf : f.IsAugmented ε ε') :
    AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra :=
  AInfinityHom.ofTaylor (ε'.reducedPart ∘ₗ f.taylor ∘ₗ ε.inclusion.barMap)
    (reducedTaylor_isHomogeneous f ε ε') hf.reducedTaylor_component_eq

@[simp]
theorem taylor_reducedHom (hf : f.IsAugmented ε ε') :
    hf.reducedHom.taylor = ε'.reducedPart ∘ₗ f.taylor ∘ₗ ε.inclusion.barMap :=
  taylor_ofTaylor _ _ _

/-- The reduced morphism intertwines the strict inclusions of the augmentation ideals. -/
theorem inclusion_comp_reducedHom (hf : f.IsAugmented ε ε') :
    ε'.inclusion.toAInfinityHom.comp hf.reducedHom = f.comp ε.inclusion.toAInfinityHom := by
  apply AInfinityHom.ext
  rw [AInfinityStrictHom.taylor_toAInfinityHom_comp, taylor_reducedHom,
    hf.inclusion_comp_reducedPart_taylor, taylor_comp, AInfinityStrictHom.barMap_toAInfinityHom]

/-- Restricting the identity morphism to the augmentation ideal gives the identity morphism. -/
@[simp]
theorem reducedHom_id (ε : 𝒜.Augmentation) :
    (isAugmented_id ε).reducedHom = AInfinityHom.id ε.reducedAlgebra := by
  apply AInfinityHom.ext
  rw [taylor_reducedHom, taylor_id, taylor_id, AInfinityStrictHom.barMap_def, letter_comp_map,
    ← LinearMap.comp_assoc, ε.reducedPart_comp_inclusion_toLinearMap, LinearMap.id_comp]

/-- Reduction to the augmentation ideal preserves composition of augmented `A∞` morphisms. -/
theorem reducedHom_comp {g : AInfinityHom ℬ 𝒞} {ε'' : 𝒞.Augmentation}
    (hg : g.IsAugmented ε' ε'') (hf : f.IsAugmented ε ε') :
    (hg.comp hf).reducedHom = hg.reducedHom.comp hf.reducedHom := by
  refine AInfinityHom.ext (LinearMap.ext fun w ↦ ?_)
  have hbar : ε'.inclusion.barMap ∘ₗ hf.reducedHom.barMap = f.barMap ∘ₗ ε.inclusion.barMap := by
    have h := congrArg AInfinityHom.barMap hf.inclusion_comp_reducedHom
    simpa only [barMap_comp, AInfinityStrictHom.barMap_toAInfinityHom] using h
  have hbw := LinearMap.congr_fun hbar w
  simp only [taylor_reducedHom, taylor_comp, LinearMap.comp_apply] at hbw ⊢
  rw [hbw]

end AInfinityHom.IsAugmented

namespace AInfinityAlgebra.Augmentation

variable {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B} {𝒞 : AInfinityAlgebra R C}

/-- The suspended Taylor map extending a reduced `A∞` morphism `g : ker ε ⟶ ker ε'` to `A ⟶ B`. -/
private noncomputable def extendTaylor (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) : ReducedTensorWords R A →ₗ[R] B :=
  ε'.unitHom ∘ₗ ε.toLinearMap ∘ₗ letter R A +
    ε'.inclusion.toLinearMap ∘ₗ g.taylor ∘ₗ ReducedTensorWords.map (R := R) ε.reducedPart

private theorem extendTaylor_comp_inclusion_barMap (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    ε.extendTaylor ε' g ∘ₗ ε.inclusion.barMap = ε'.inclusion.toLinearMap ∘ₗ g.taylor := by
  refine LinearMap.ext fun z ↦ ?_
  have hl := LinearMap.congr_fun (letter_comp_map (R := R) ε.inclusion.toLinearMap) z
  have hm := LinearMap.congr_fun (ε.map_reducedPart_comp_inclusion_barMap) z
  simp only [AInfinityStrictHom.barMap_def, LinearMap.comp_apply] at hl hm
  simp only [extendTaylor, LinearMap.add_apply, LinearMap.comp_apply,
    AInfinityStrictHom.barMap_def]
  rw [hl, hm]
  simp [(ε.mem_augmentationIdeal).mp (letter _ _ z).property]

private theorem extendTaylor_of_mem_degenerateWords (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) {z : ReducedTensorWords R A}
    (hz : z ∈ degenerateWords R A ε.unit) :
    ε.extendTaylor ε' g z = ε (letter R A z) • ε'.unit := by
  have hker := LinearMap.mem_ker.mp
    (degenerateWords_le_ker_map ε.reducedPart ε.reducedPart_unit hz)
  simp only [extendTaylor, LinearMap.add_apply, LinearMap.comp_apply, unitHom_apply, hker,
    map_zero, add_zero]

private theorem extendTaylor_ofLetter_unit (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    ε.extendTaylor ε' g (ofLetter R A ε.unit) = ε'.unit := by
  rw [extendTaylor_of_mem_degenerateWords ε ε' g (ofLetter_mem_degenerateWords ε.unit),
    letter_ofLetter, ε.map_unit, one_smul]

private theorem extendTaylor_of_tprod_eq_zero (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra)
    (m : {m : ℕ // 0 < m}) (hm : m.1 ≠ 1) (y : Fin m.1 → A) (hy : ∃ i, y i = ε.unit) :
    ε.extendTaylor ε' g (of R A m (PiTensorProduct.tprod R y)) = 0 := by
  rw [extendTaylor_of_mem_degenerateWords ε ε' g (of_tprod_mem_degenerateWords m y hy),
    of_tprod_eq_subword R m.2, letter_subword_of_ne_one R A y 0 hm, map_zero, zero_smul]

private theorem extendTaylor_subword_eq_zero (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) {k : ℕ} (x : Fin k → A)
    {a b : ℕ} (hb : 1 < b) (hx : ∃ i : Fin k, a ≤ i.1 ∧ i.1 < a + b ∧ x i = ε.unit) :
    ε.extendTaylor ε' g (subword R x a b) = 0 := by
  rw [extendTaylor_of_mem_degenerateWords ε ε' g (subword_mem_degenerateWords x hx),
    letter_subword_of_ne_one R A x a (by omega), map_zero, zero_smul]

private theorem extendTaylor_isHomogeneous (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    LinearMap.IsHomogeneous (ε.extendTaylor ε' g) (gradedPiece (𝒜.grading.shift 1))
      (ℬ.grading.shift 1).piece 0 := by
  have h1 : LinearMap.IsHomogeneous (ε'.unitHom ∘ₗ ε.toLinearMap ∘ₗ letter R A)
      (gradedPiece (𝒜.grading.shift 1)) (ℬ.grading.shift 1).piece 0 := by
    refine LinearMap.isHomogeneous_def.mpr fun p z hz ↦ ?_
    have hl := (isHomogeneous_letter (𝒜.grading.shift 1)).map_mem hz
    rw [add_zero, InternalGrading.shift_piece] at hl ⊢
    by_cases hp : p + 1 = 0
    · rw [hp]
      simp only [LinearMap.comp_apply, unitHom_apply]
      exact Submodule.smul_mem _ _ ε'.isStrictUnit.degree_zero
    · simp only [LinearMap.comp_apply, unitHom_apply,
        ε.map_of_mem_ne_zero (p + 1) _ hl hp, zero_smul, Submodule.zero_mem]
  have h2a : LinearMap.IsHomogeneous
      (g.taylor ∘ₗ ReducedTensorWords.map (R := R) ε.reducedPart)
      (gradedPiece (𝒜.grading.shift 1)) (ε'.reducedAlgebra.grading.shift 1).piece 0 := by
    simpa only [add_zero] using g.isHomogeneous_taylor.comp
      (isHomogeneous_map _ _ ε.isHomogeneous_reducedPart_shift_one)
  have h2 : LinearMap.IsHomogeneous
      (ε'.inclusion.toLinearMap ∘ₗ g.taylor ∘ₗ ReducedTensorWords.map (R := R) ε.reducedPart)
      (gradedPiece (𝒜.grading.shift 1)) (ℬ.grading.shift 1).piece 0 := by
    simpa only [add_zero] using (ε'.inclusion.isHomogeneous_shift 1).comp h2a
  exact h1.add h2

/-- Cuts into three or more blocks in `coalgHom (extendTaylor g)` on a word containing `ε.unit`
always vanish under `ℬ.taylor`. -/
private theorem sum_taylor_prepend_prepend_extendTaylor_eq_zero
    (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) {n : ℕ} (x : Fin (n + 1) → A)
    (j : Fin (n + 1)) (hj : x j = ε.unit) {d : ℕ} (hdpos : 0 < d) (hd : d < n + 1) :
    ∑ c ∈ Finset.range (n + 1 - d),
      ℬ.taylor (prepend R B (ε.extendTaylor ε' g (subword R x 0 d))
        (prepend R B (ε.extendTaylor ε' g (subword R x d c))
          (coalgHom R (ε.extendTaylor ε' g) (subword R x (d + c) (n + 1 - d - c))))) = 0 := by
  have := j.isLt
  refine Finset.sum_eq_zero fun c hc ↦ ?_
  rw [Finset.mem_range] at hc
  rcases Nat.eq_zero_or_pos c with rfl | hcpos
  · simp [subword_length_zero]
  by_cases hjd : j.1 < d
  · by_cases hd1 : d = 1
    · have hx0 : x ⟨0, by omega⟩ = ε.unit := by
        rw [← hj]; exact congrArg x (Fin.ext (by dsimp only; omega))
      rw [hd1, subword_one R A x (by omega), hx0]
      exact ε'.isStrictUnit.taylor_prepend_prepend_eq_zero _ _ _
        (Or.inl (ε.extendTaylor_ofLetter_unit ε' g))
    · rw [ε.extendTaylor_subword_eq_zero ε' g x (by omega) ⟨j, by omega, by omega, hj⟩]
      simp
  · by_cases hjdc : j.1 < d + c
    · by_cases hc1 : c = 1
      · have hxd : x ⟨d, by omega⟩ = ε.unit := by
          rw [← hj]; exact congrArg x (Fin.ext (by dsimp only; omega))
        rw [hc1, subword_one R A x (by omega), hxd]
        exact ε'.isStrictUnit.taylor_prepend_prepend_eq_zero _ _ _
          (Or.inr (Or.inl (ε.extendTaylor_ofLetter_unit ε' g)))
      · rw [ε.extendTaylor_subword_eq_zero ε' g x (by omega) ⟨j, by omega, hjdc, hj⟩]
        simp
    · exact ε'.isStrictUnit.taylor_prepend_prepend_eq_zero _ _ _ (Or.inr (Or.inr
        (coalgHom_subword_mem_degenerateWords _ (ε.extendTaylor_ofLetter_unit ε' g)
          (ε.extendTaylor_of_tprod_eq_zero ε' g) x (by omega)
          ⟨j, by omega, by omega, hj⟩)))

/-- A single cut `d` in `coalgHom (extendTaylor g)` on a pure word with strict unit at `j`
contributes only when `d = 1` (`j = 0`) or `d = n` (`j = n`). -/
private theorem taylor_prepend_coalgHom_extendTaylor (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) {n : ℕ} (x : Fin (n + 1) → A)
    (j : Fin (n + 1)) (hj : x j = ε.unit) (d : ℕ) (hd : d ∈ Finset.range (n + 1)) :
    ℬ.taylor (prepend R B (ε.extendTaylor ε' g (subword R x 0 d))
        (coalgHom R (ε.extendTaylor ε' g) (subword R x d (n + 1 - d)))) =
      (if d = 1 ∧ (j.1 = 0 ∧ 0 < n) then ε.extendTaylor ε' g (subword R x 1 n) else 0) +
        (if d = n ∧ (j.1 = n ∧ 0 < n) then
          ℬ.grading.koszulTwist 1 (ε.extendTaylor ε' g (subword R x 0 n)) else 0) := by
  have := j.isLt
  rw [Finset.mem_range] at hd
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · simp (disch := omega) [subword_length_zero]
  rw [coalgHom_subword _ x d (n + 1 - d), map_add, map_add, map_sum, map_sum,
    ε.sum_taylor_prepend_prepend_extendTaylor_eq_zero ε' g x j hj hdpos hd, add_zero]
  by_cases hjd : j.1 < d
  · by_cases hd1 : d = 1
    · subst hd1
      have hx0 : x ⟨0, by omega⟩ = ε.unit := by
        rw [← hj]; exact congrArg x (Fin.ext (by dsimp only; omega))
      simp (disch := omega) only [true_and, ite_eq_left, ite_eq_right, add_zero,
        Nat.add_sub_cancel]
      rw [prepend_ofLetter, subword_one R A x (by omega), hx0,
        ε.extendTaylor_ofLetter_unit ε' g, ε'.isStrictUnit.taylor_of_two_unit_left]
    · rw [ε.extendTaylor_subword_eq_zero ε' g x (a := 0) (by omega) ⟨j, by omega, by omega, hj⟩]
      simp (disch := omega)
  · by_cases hdn : d = n
    · subst hdn
      have hxd : x ⟨d, by omega⟩ = ε.unit := by
        rw [← hj]; exact congrArg x (Fin.ext (by dsimp only; omega))
      simp (disch := omega) only [true_and, ite_eq_right, ite_eq_left, zero_add,
        Nat.add_sub_cancel_left]
      rw [prepend_ofLetter, subword_one R A x (by omega), hxd,
        ε.extendTaylor_ofLetter_unit ε' g, ε'.isStrictUnit.taylor_of_two_unit_right]
    · rw [ε.extendTaylor_subword_eq_zero ε' g x (a := d) (by omega) ⟨j, by omega, by omega, hj⟩,
        map_zero, map_zero, map_zero]
      simp (disch := omega) only [ite_eq_right, add_zero]

/-- Evaluation of `ℬ.taylor (coalgHom (extendTaylor g) (of (tprod x)))` on a pure word containing
the strict unit at `j`: only the two-block cuts isolating `ε.unit` at `j = 0` or `j = n` survive. -/
private theorem taylor_coalgHom_extendTaylor_of_tprod (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) {n : ℕ} (x : Fin (n + 1) → A)
    (j : Fin (n + 1)) (hj : x j = ε.unit) :
    ℬ.taylor (coalgHom R (ε.extendTaylor ε' g)
        (of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R x))) =
      (if j.1 = 0 ∧ 0 < n then ε.extendTaylor ε' g (subword R x 1 n) else 0) +
        (if j.1 = n ∧ 0 < n then
          ℬ.grading.koszulTwist 1 (ε.extendTaylor ε' g (subword R x 0 n)) else 0) := by
  have hjn := j.isLt
  rw [of_tprod_eq_subword R n.succ_pos, coalgHom_subword, map_add, map_sum]
  have hsingle : ℬ.taylor (ofLetter R B (ε.extendTaylor ε' g (subword R x 0 (n + 1)))) = 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hj0 : (0 : Fin 1) = j := Subsingleton.elim _ _
      rw [subword_one R A x Nat.one_pos, Fin.zero_eta, hj0, hj,
        ε.extendTaylor_ofLetter_unit ε' g, ofLetter_eq_of_tprod]
      exact ε'.isStrictUnit.taylor_of_tprod_eq_zero ⟨1, Nat.one_pos⟩ (by decide) _ ⟨0, rfl⟩
    · rw [ε.extendTaylor_subword_eq_zero ε' g x (by omega) ⟨j, by omega, by omega, hj⟩,
        map_zero, map_zero]
  rw [hsingle, zero_add]
  simp only [zero_add]
  rw [Finset.sum_congr rfl (ε.taylor_prepend_coalgHom_extendTaylor ε' g x j hj)]
  simp only [Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq', Finset.mem_range]
  congr 1 <;> split_ifs <;> first | rfl | omega

/-- The Stasheff morphism equation for `extendTaylor g` holds on `degenerateWords R A ε.unit`. -/
private theorem degenerateWords_le_ker_extendTaylor_component
    (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    degenerateWords R A ε.unit ≤
      LinearMap.ker (ℬ.taylor ∘ₗ coalgHom R (ε.extendTaylor ε' g) -
        ε.extendTaylor ε' g ∘ₗ 𝒜.barDifferential) := by
  let t := ε.extendTaylor ε' g
  rw [degenerateWords_le_iff_of_mem_piece _ ε.isStrictUnit.mem_shift_one_piece]
  rintro ⟨_ | n, hN⟩ x 𝒟 j hx hj _
  · omega
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  simp only [LinearMap.comp_apply]
  rw [ε.taylor_coalgHom_extendTaylor_of_tprod ε' g x j hj,
    ε.isStrictUnit.apply_barDifferential_of_tprod_of_higher_eq_zero
      (ε.extendTaylor_of_tprod_eq_zero ε' g) x 𝒟 hx j hj]
  have htwist : t ((ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1
      (subword R x 0 n)) = -ℬ.grading.koszulTwist 1 (t (subword R x 0 n)) := by
    have hhom : LinearMap.IsHomogeneous t
        (ReducedTensorWords.grading (𝒜.grading.shift 1)).piece (ℬ.grading.shift 1).piece 0 := by
      rw [ReducedTensorWords.grading_piece]
      exact ε.extendTaylor_isHomogeneous ε' g
    have hkt := hhom.koszulTwist_apply 1 (subword R x 0 n)
    simp only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul] at hkt
    rw [← hkt, InternalGrading.koszulTwist_one_shift_one, LinearMap.neg_apply]
  dsimp only [t] at htwist
  rw [htwist, sub_eq_add_neg]
  congr 1
  split_ifs <;> simp

private theorem extendTaylor_component_eq (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    ℬ.taylor ∘ₗ coalgHom R (ε.extendTaylor ε' g) =
      ε.extendTaylor ε' g ∘ₗ 𝒜.barDifferential := by
  let t := ε.extendTaylor ε' g
  -- First, the component equation holds on words coming from `ker ε`.
  have hred : (ℬ.taylor ∘ₗ coalgHom R t) ∘ₗ ε.inclusion.barMap =
      (t ∘ₗ 𝒜.barDifferential) ∘ₗ ε.inclusion.barMap := by
    have hcoalg : coalgHom R t ∘ₗ ε.inclusion.barMap = ε'.inclusion.barMap ∘ₗ g.barMap := by
      rw [AInfinityStrictHom.barMap_def,
        ((isCoalgHom_coalgHom t).comp (isCoalgHom_map _)).eq_coalgHom,
        ← LinearMap.comp_assoc, letter_comp_coalgHom, ← AInfinityStrictHom.barMap_def,
        ε.extendTaylor_comp_inclusion_barMap ε' g, AInfinityStrictHom.barMap_def,
        ← map_comp_coalgHom, ← g.barMap_eq_coalgHom]
    dsimp only [t] at hcoalg ⊢
    rw [LinearMap.comp_assoc, hcoalg, ← LinearMap.comp_assoc, ε'.inclusion.taylor_comp_barMap,
      LinearMap.comp_assoc, g.taylor_comp_barMap, LinearMap.comp_assoc,
      ε.inclusion.barDifferential_comp_barMap, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc,
      ε.extendTaylor_comp_inclusion_barMap ε' g]
  -- Every word decomposes into a word of `ker ε` plus a degenerate word.
  refine LinearMap.ext fun z ↦ ?_
  let P : A →ₗ[R] A := ε.inclusion.toLinearMap ∘ₗ ε.reducedPart
  have hP : ∀ a, ∃ c : R, a - P a = c • ε.unit := fun a ↦
    ⟨ε a, by simp [P, coe_reducedPart]⟩
  have hsub := sub_eq_zero.mp (LinearMap.mem_ker.mp
    (ε.degenerateWords_le_ker_extendTaylor_component ε' g (sub_map_mem_degenerateWords P hP z)))
  have hmap : ReducedTensorWords.map (R := R) P z =
      ε.inclusion.barMap (ReducedTensorWords.map (R := R) ε.reducedPart z) := by
    dsimp only [P]
    rw [AInfinityStrictHom.barMap_def, ReducedTensorWords.map_comp, LinearMap.comp_apply]
  have hredz : (ℬ.taylor ∘ₗ coalgHom R t) (ReducedTensorWords.map (R := R) P z) =
      (t ∘ₗ 𝒜.barDifferential) (ReducedTensorWords.map (R := R) P z) := by
    have h := LinearMap.congr_fun hred (ReducedTensorWords.map (R := R) ε.reducedPart z)
    simpa only [LinearMap.comp_apply, ← hmap] using h
  have hz : z = ReducedTensorWords.map (R := R) P z + (z - ReducedTensorWords.map (R := R) P z) :=
    (add_sub_cancel _ _).symm
  dsimp only [t] at hredz
  rw [hz, map_add, map_add, hredz, hsub]

/-- Extend any nonunital `A∞` morphism `g : ker ε ⟶ ker ε'` between reduced augmentation ideals to
a strictly unital augmented `A∞` morphism `A ⟶ B`. -/
noncomputable def extendReducedHom (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) : AInfinityHom 𝒜 ℬ :=
  AInfinityHom.ofTaylor (ε.extendTaylor ε' g) (ε.extendTaylor_isHomogeneous ε' g)
    (ε.extendTaylor_component_eq ε' g)

/-- The extended morphism is strictly unital and augmented. -/
theorem isAugmented_extendReducedHom (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    (ε.extendReducedHom ε' g).IsAugmented ε ε' := by
  rw [AInfinityHom.isAugmented_iff_taylor]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [AInfinityHom.linearPart_apply, extendReducedHom, AInfinityHom.taylor_ofTaylor]
    exact ε.extendTaylor_ofLetter_unit ε' g
  · intro n hn x hx
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp
    · rw [AInfinityHom.component_apply _ n hnpos, extendReducedHom, AInfinityHom.taylor_ofTaylor]
      obtain ⟨i, hi⟩ := hx
      exact ε.extendTaylor_of_tprod_eq_zero ε' g ⟨n, hnpos⟩ hn _
        ⟨i, by rw [hi, 𝒜.grading.koszulTwist_apply_of_mem_zero ε.isStrictUnit.degree_zero]⟩
  · rw [extendReducedHom, AInfinityHom.taylor_ofTaylor]
    ext z
    simp [extendTaylor, (ε'.mem_augmentationIdeal).mp (g.taylor _).property]

theorem extendReducedHom_linearPart_unit (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    (ε.extendReducedHom ε' g).linearPart ε.unit = ε'.unit :=
  (ε.isAugmented_extendReducedHom ε' g).isStrictlyUnital.map_unit

/-- Restricting `extendReducedHom g` along `ε.inclusion` factors through `ε'.inclusion`. -/
@[simp]
theorem extendReducedHom_comp_inclusion (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    (ε.extendReducedHom ε' g).comp ε.inclusion.toAInfinityHom =
      ε'.inclusion.toAInfinityHom.comp g := by
  apply AInfinityHom.ext
  rw [AInfinityHom.taylor_comp, extendReducedHom, AInfinityHom.taylor_ofTaylor,
    AInfinityStrictHom.barMap_toAInfinityHom, ε.extendTaylor_comp_inclusion_barMap ε' g,
    AInfinityStrictHom.taylor_toAInfinityHom_comp]

@[simp]
theorem reducedHom_extendReducedHom (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    (ε.isAugmented_extendReducedHom ε' g).reducedHom = g := by
  apply AInfinityHom.ext
  rw [AInfinityHom.IsAugmented.taylor_reducedHom, extendReducedHom, AInfinityHom.taylor_ofTaylor,
    ε.extendTaylor_comp_inclusion_barMap ε' g, ← LinearMap.comp_assoc,
    ε'.reducedPart_comp_inclusion_toLinearMap, LinearMap.id_comp]

@[simp]
theorem extendReducedHom_reducedHom {f : AInfinityHom 𝒜 ℬ} (hf : f.IsAugmented ε ε') :
    ε.extendReducedHom ε' hf.reducedHom = f := by
  refine AInfinityHom.ext (LinearMap.ext fun z ↦ ?_)
  rw [extendReducedHom, AInfinityHom.taylor_ofTaylor]
  let P : A →ₗ[R] A := ε.inclusion.toLinearMap ∘ₗ ε.reducedPart
  have hP : ∀ a, ∃ c : R, a - P a = c • ε.unit := fun a ↦
    ⟨ε a, by simp [P, coe_reducedPart]⟩
  let w := z - ReducedTensorWords.map (R := R) P z
  have hw : w ∈ degenerateWords R A ε.unit := sub_map_mem_degenerateWords P hP z
  have hlw : letter R A w = ε (letter R A z) • ε.unit := by
    have hlp := LinearMap.congr_fun (letter_comp_map (R := R) P) z
    simp only [LinearMap.comp_apply] at hlp
    rw [map_sub, hlp]
    simp only [P, LinearMap.comp_apply, inclusion_toLinearMap, Submodule.subtype_apply,
      coe_reducedPart, sub_sub_cancel]
  have hfw : f.taylor w = ε (letter R A z) • ε'.unit := by
    rw [hf.isStrictlyUnital.taylor_eq_linearPart_letter hw, hlw, map_smul,
      hf.isStrictlyUnital.map_unit]
  have htw : ε.extendTaylor ε' hf.reducedHom w = ε (letter R A z) • ε'.unit := by
    rw [ε.extendTaylor_of_mem_degenerateWords ε' hf.reducedHom hw, hlw, map_smul, ε.map_unit,
      smul_eq_mul, mul_one]
  have hmap : ReducedTensorWords.map (R := R) P z =
      ε.inclusion.barMap (ReducedTensorWords.map (R := R) ε.reducedPart z) := by
    dsimp only [P]
    rw [AInfinityStrictHom.barMap_def, ReducedTensorWords.map_comp, LinearMap.comp_apply]
  have hred : ε.extendTaylor ε' hf.reducedHom (ReducedTensorWords.map (R := R) P z) =
      f.taylor (ReducedTensorWords.map (R := R) P z) := by
    have h1 := LinearMap.congr_fun (ε.extendTaylor_comp_inclusion_barMap ε' hf.reducedHom)
      (ReducedTensorWords.map (R := R) ε.reducedPart z)
    have h2 := LinearMap.congr_fun hf.inclusion_comp_reducedPart_taylor
      (ReducedTensorWords.map (R := R) ε.reducedPart z)
    rw [hmap]
    simp only [LinearMap.comp_apply, AInfinityHom.IsAugmented.taylor_reducedHom] at h1 h2
    exact h1.trans h2
  have hz : z = ReducedTensorWords.map (R := R) P z + w := (add_sub_cancel _ _).symm
  rw [hz, map_add, map_add, hred, htw, hfw]

/-- **Reduction of augmented `A∞` morphisms to the augmentation ideal**: strictly unital augmented
`A∞` morphisms `(A, ε) ⟶ (B, ε')` correspond bijectively to nonunital `A∞` morphisms
`ker ε ⟶ ker ε'`. -/
noncomputable def augmentedHomEquiv (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation) :
    {f : AInfinityHom 𝒜 ℬ // f.IsAugmented ε ε'} ≃
      AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra where
  toFun f := f.property.reducedHom
  invFun g := ⟨ε.extendReducedHom ε' g, ε.isAugmented_extendReducedHom ε' g⟩
  left_inv f := Subtype.ext (extendReducedHom_reducedHom f.property)
  right_inv g := reducedHom_extendReducedHom ε ε' g

@[simp]
theorem augmentedHomEquiv_apply (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (f : {f : AInfinityHom 𝒜 ℬ // f.IsAugmented ε ε'}) :
    ε.augmentedHomEquiv ε' f = f.property.reducedHom := (rfl)

@[simp]
theorem augmentedHomEquiv_symm_apply_val (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    ((ε.augmentedHomEquiv ε').symm g).val = ε.extendReducedHom ε' g := (rfl)

/-- Extending reduced morphisms commutes with composition. -/
theorem extendReducedHom_comp (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation) (ε'' : 𝒞.Augmentation)
    (h : AInfinityHom ε'.reducedAlgebra ε''.reducedAlgebra)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    ε.extendReducedHom ε'' (h.comp g) =
      (ε'.extendReducedHom ε'' h).comp (ε.extendReducedHom ε' g) := by
  have hh := ε'.isAugmented_extendReducedHom ε'' h
  have hg := ε.isAugmented_extendReducedHom ε' g
  rw [← extendReducedHom_reducedHom (hh.comp hg), hh.reducedHom_comp hg,
    reducedHom_extendReducedHom, reducedHom_extendReducedHom]

private theorem inclusion_comp_reducedPart_of_mem (ε' : ℬ.Augmentation) {g : AInfinityHom 𝒜 ℬ}
    (hg : ∀ w, g.taylor w ∈ ε'.augmentationIdeal) :
    ε'.inclusion.toLinearMap ∘ₗ (ε'.reducedPart ∘ₗ g.taylor) = g.taylor := by
  refine LinearMap.ext fun w ↦ ?_
  have hw := (ε'.mem_augmentationIdeal).mp (hg w)
  simp [coe_reducedPart, hw]

private theorem liftReducedHom_component_eq (ε' : ℬ.Augmentation) {g : AInfinityHom 𝒜 ℬ}
    (hg : ∀ w, g.taylor w ∈ ε'.augmentationIdeal) :
    ε'.reducedAlgebra.taylor ∘ₗ coalgHom R (ε'.reducedPart ∘ₗ g.taylor) =
      (ε'.reducedPart ∘ₗ g.taylor) ∘ₗ 𝒜.barDifferential := by
  have hinc := inclusion_comp_reducedPart_of_mem ε' hg
  have hcoalg : ε'.inclusion.barMap ∘ₗ coalgHom R (ε'.reducedPart ∘ₗ g.taylor) = g.barMap := by
    rw [AInfinityStrictHom.barMap_def, map_comp_coalgHom, hinc, g.barMap_eq_coalgHom]
  refine LinearMap.ext fun w ↦ Subtype.val_injective ?_
  have h1 := LinearMap.congr_fun ε'.inclusion.taylor_comp_barMap
    (coalgHom R (ε'.reducedPart ∘ₗ g.taylor) w)
  have h2 := LinearMap.congr_fun hcoalg w
  have h3 := LinearMap.congr_fun g.taylor_comp_barMap w
  have h4 := LinearMap.congr_fun hinc (𝒜.barDifferential w)
  simp only [LinearMap.comp_apply, inclusion_toLinearMap, Submodule.subtype_apply]
    at h1 h2 h3 h4 ⊢
  exact (h1.symm.trans ((congrArg ℬ.taylor h2).trans h3)).trans h4.symm

/-- **Universal property of the augmentation ideal**: `A∞` morphisms `A ⟶ ker ε'` correspond
bijectively to `A∞` morphisms `g : A ⟶ B` whose Taylor map takes values in `ker ε'`. -/
noncomputable def liftReducedHomEquiv (𝒜 : AInfinityAlgebra R A) (ε' : ℬ.Augmentation) :
    AInfinityHom 𝒜 ε'.reducedAlgebra ≃
      {g : AInfinityHom 𝒜 ℬ // ∀ w, g.taylor w ∈ ε'.augmentationIdeal} where
  toFun k := ⟨ε'.inclusion.toAInfinityHom.comp k, fun w ↦ by simp⟩
  invFun g := AInfinityHom.ofTaylor (ε'.reducedPart ∘ₗ g.val.taylor)
    (by simpa only [add_zero] using
      ε'.isHomogeneous_reducedPart_shift_one.comp g.val.isHomogeneous_taylor)
    (liftReducedHom_component_eq ε' g.property)
  left_inv k := by
    apply AInfinityHom.ext
    dsimp only
    rw [AInfinityHom.taylor_ofTaylor, AInfinityStrictHom.taylor_toAInfinityHom_comp,
      ← LinearMap.comp_assoc, ε'.reducedPart_comp_inclusion_toLinearMap, LinearMap.id_comp]
  right_inv g := by
    apply Subtype.ext
    apply AInfinityHom.ext
    dsimp only
    rw [AInfinityStrictHom.taylor_toAInfinityHom_comp, AInfinityHom.taylor_ofTaylor,
      inclusion_comp_reducedPart_of_mem ε' g.property]

@[simp]
theorem liftReducedHomEquiv_apply_val (𝒜 : AInfinityAlgebra R A) (ε' : ℬ.Augmentation)
    (k : AInfinityHom 𝒜 ε'.reducedAlgebra) :
    (liftReducedHomEquiv 𝒜 ε' k).val = ε'.inclusion.toAInfinityHom.comp k := (rfl)

@[simp]
theorem taylor_liftReducedHomEquiv_symm (𝒜 : AInfinityAlgebra R A) (ε' : ℬ.Augmentation)
    (g : {g : AInfinityHom 𝒜 ℬ // ∀ w, g.taylor w ∈ ε'.augmentationIdeal}) :
    ((liftReducedHomEquiv 𝒜 ε').symm g).taylor = ε'.reducedPart ∘ₗ g.val.taylor :=
  AInfinityHom.taylor_ofTaylor _ _ _

end AInfinityAlgebra.Augmentation

namespace AInfinityHom.IsAugmented

variable {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B}
  {ε : 𝒜.Augmentation} {ε' : ℬ.Augmentation}

/-- Two strictly unital augmented `A∞` morphisms are equal as soon as they agree after
precomposing with the strict inclusion of the source augmentation ideal. -/
theorem ext_comp_inclusion {f₁ f₂ : AInfinityHom 𝒜 ℬ}
    (hf₁ : f₁.IsAugmented ε ε') (hf₂ : f₂.IsAugmented ε ε')
    (h : f₁.comp ε.inclusion.toAInfinityHom = f₂.comp ε.inclusion.toAInfinityHom) :
    f₁ = f₂ := by
  have hred : hf₁.reducedHom = hf₂.reducedHom := by
    apply AInfinityHom.ext
    have ht := congrArg AInfinityHom.taylor h
    simp only [AInfinityHom.taylor_comp, AInfinityStrictHom.barMap_toAInfinityHom] at ht
    rw [taylor_reducedHom, taylor_reducedHom, ht]
  rw [← AInfinityAlgebra.Augmentation.extendReducedHom_reducedHom hf₁,
    ← AInfinityAlgebra.Augmentation.extendReducedHom_reducedHom hf₂, hred]

end AInfinityHom.IsAugmented

end TauCeti
