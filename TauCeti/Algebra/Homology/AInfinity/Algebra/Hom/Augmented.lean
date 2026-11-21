/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Augmentation
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Unital
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Unit.Degenerate

/-!
# Augmented morphisms of `A∞` algebras and reduction to the augmentation ideal

An `A∞` morphism `f : A ⟶ B` between augmented uncurved `A∞` algebras `(A, ε)` and `(B, ε')` is
**augmented** (`AInfinityHom.IsAugmented`) if it is strictly unital and `ε' ∘ f.taylor = ε ∘ letter`
(`isAugmented_iff_taylor`). For differential graded algebras,
`DGAlgHom.isAugmented_toAInfinityHom_iff` characterizes when a `DGAlgHom` induces an augmented `A∞`
morphism with respect to `DGAlgAugmentation.toAInfinityAugmentation`.

More generally, for any target `A∞` algebra `B` with a strict unit `e_B`, restricting to `ker ε`
and extending across the strict-unit splitting
(`AInfinityAlgebra.Augmentation.extendStrictlyUnitalHom`) yields
`AInfinityAlgebra.Augmentation.strictlyUnitalHomEquiv`, identifying strictly unital `A∞`
morphisms `(A, ε) ⟶ (B, e_B)` with nonunital `A∞` morphisms `ker ε ⟶ B`. When `(B, ε')` is
augmented, morphisms into `B` whose Taylor map lands in `ker ε'` factor uniquely through `ker ε'`
(`AInfinityAlgebra.Augmentation.liftReducedHomEquiv`). Restricting `strictlyUnitalHomEquiv` along
`liftReducedHomEquiv` produces `AInfinityAlgebra.Augmentation.extendReducedHom` and
`AInfinityAlgebra.Augmentation.augmentedHomEquiv`, identifying strictly unital augmented morphisms
`(A, ε) ⟶ (B, ε')` with nonunital `A∞` morphisms `ker ε ⟶ ker ε'`. Passing to `ker ε` eliminates
unit-containing bar words so the nonunital bar--cobar adjunction on `ker ε` classifies strictly
unital (and strictly unital augmented) morphisms out of `(A, ε)`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
* B. Keller, *A-infinity algebras, modules and functor categories*, Section 4.
-/

public section

namespace TauCeti

open ReducedTensorWords

universe uR uA uB uC

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

namespace AInfinityAlgebra.Augmentation

variable {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B}

/-- The canonical strict `A∞` inclusion of the reduced augmentation ideal `ker ε` into `A`. -/
noncomputable def inclusion (ε : 𝒜.Augmentation) : AInfinityStrictHom ε.reducedAlgebra 𝒜 where
  toLinearMap := ε.augmentationIdeal.subtype
  map_mem' hx := by
    simpa only [ε.reducedAlgebra_grading, ε.reducedGrading_piece, Submodule.mem_comap] using hx
  map_m' _ := MultilinearMap.ext fun _ ↦ by simp [ε.coe_reducedOperation]

@[simp] theorem inclusion_toLinearMap (ε : 𝒜.Augmentation) :
    ε.inclusion.toLinearMap = ε.augmentationIdeal.subtype := (rfl)

@[simp] theorem inclusion_apply (ε : 𝒜.Augmentation) (x : ε.augmentationIdeal) :
    ε.inclusion x = x := (rfl)

@[simp] theorem map_reducedPart_comp_inclusion_barMap (ε : 𝒜.Augmentation) :
    ReducedTensorWords.map (R := R) ε.reducedPart ∘ₗ ε.inclusion.barMap = LinearMap.id := by
  rw [AInfinityStrictHom.barMap_def, ← ReducedTensorWords.map_comp, ε.inclusion_toLinearMap,
    ε.reducedPart_comp_subtype, ReducedTensorWords.map_id]

/-- Every bar word over `A` differs from its `ker ε` projection by a `ε.unit`-degenerate word. -/
theorem sub_inclusion_barMap_map_reducedPart_mem_degenerateWords (ε : 𝒜.Augmentation)
    (z : ReducedTensorWords R A) :
    z - ε.inclusion.barMap (ReducedTensorWords.map (R := R) ε.reducedPart z) ∈
      degenerateWords R A ε.unit := by
  rw [AInfinityStrictHom.barMap_def, ← LinearMap.comp_apply, ← ReducedTensorWords.map_comp]
  exact sub_map_mem_degenerateWords _ (fun a ↦ ⟨ε a, by simp [coe_reducedPart]⟩) z

/-- On single letters, subtracting the reduced projection of `z` gives `ε (letter z) • ε.unit`. -/
theorem letter_sub_inclusion_barMap_map_reducedPart (ε : 𝒜.Augmentation)
    (z : ReducedTensorWords R A) :
    letter R A (z - ε.inclusion.barMap (ReducedTensorWords.map (R := R) ε.reducedPart z)) =
      ε (letter R A z) • ε.unit := by
  have hl := LinearMap.congr_fun
    (letter_comp_map (R := R) (ε.inclusion.toLinearMap ∘ₗ ε.reducedPart)) z
  rw [ReducedTensorWords.map_comp] at hl
  simpa only [map_sub, AInfinityStrictHom.barMap_def, LinearMap.comp_apply,
    ε.inclusion_toLinearMap, Submodule.subtype_apply, ε.coe_reducedPart, sub_sub_cancel] using
    congrArg (letter R A z - ·) hl

private theorem inclusion_comp_reducedPart_of_mem (ε' : ℬ.Augmentation) {g : AInfinityHom 𝒜 ℬ}
    (hg : ∀ w, g.taylor w ∈ ε'.augmentationIdeal) :
    ε'.inclusion.toLinearMap ∘ₗ (ε'.reducedPart ∘ₗ g.taylor) = g.taylor :=
  LinearMap.ext fun w ↦ by simp [coe_reducedPart, (ε'.mem_augmentationIdeal).mp (hg w)]

private theorem liftReducedHom_component_eq (ε' : ℬ.Augmentation) {g : AInfinityHom 𝒜 ℬ}
    (hg : ∀ w, g.taylor w ∈ ε'.augmentationIdeal) :
    ε'.reducedAlgebra.taylor ∘ₗ coalgHom R (ε'.reducedPart ∘ₗ g.taylor) =
      (ε'.reducedPart ∘ₗ g.taylor) ∘ₗ 𝒜.barDifferential := by
  have hinc := inclusion_comp_reducedPart_of_mem ε' hg
  have hcoalg : ε'.inclusion.barMap ∘ₗ coalgHom R (ε'.reducedPart ∘ₗ g.taylor) = g.barMap := by
    rw [AInfinityStrictHom.barMap_def, map_comp_coalgHom, hinc, g.barMap_eq_coalgHom]
  apply (LinearMap.cancel_left (Submodule.injective_subtype _)).mp
  rw [← ε'.inclusion_toLinearMap, ← LinearMap.comp_assoc, ← ε'.inclusion.taylor_comp_barMap,
    LinearMap.comp_assoc, hcoalg, g.taylor_comp_barMap, ← LinearMap.comp_assoc, hinc]

/-- **Universal property of the augmentation ideal**: `A∞` morphisms `A ⟶ ker ε'` correspond
bijectively to `A∞` morphisms `g : A ⟶ B` whose Taylor map takes values in `ker ε'`. -/
noncomputable def liftReducedHomEquiv (𝒜 : AInfinityAlgebra R A) (ε' : ℬ.Augmentation) :
    AInfinityHom 𝒜 ε'.reducedAlgebra ≃
      {g : AInfinityHom 𝒜 ℬ // ∀ w, g.taylor w ∈ ε'.augmentationIdeal} where
  toFun k := ⟨ε'.inclusion.toAInfinityHom.comp k, fun _ ↦ by simp⟩
  invFun g := AInfinityHom.ofTaylor (ε'.reducedPart ∘ₗ g.val.taylor) (by
      simpa only [add_zero] using (LinearMap.isHomogeneous_shift_piece_iff.2
        ε'.isHomogeneous_reducedPart).comp g.val.isHomogeneous_taylor)
    (liftReducedHom_component_eq ε' g.property)
  left_inv k := AInfinityHom.ext <| by
    rw [AInfinityHom.taylor_ofTaylor, AInfinityStrictHom.taylor_toAInfinityHom_comp,
      ← LinearMap.comp_assoc, ε'.inclusion_toLinearMap, ε'.reducedPart_comp_subtype,
      LinearMap.id_comp]
  right_inv g := Subtype.ext <| AInfinityHom.ext <| by
    rw [AInfinityStrictHom.taylor_toAInfinityHom_comp, AInfinityHom.taylor_ofTaylor,
      inclusion_comp_reducedPart_of_mem ε' g.property]

@[simp] theorem liftReducedHomEquiv_apply_val (𝒜 : AInfinityAlgebra R A) (ε' : ℬ.Augmentation)
    (k : AInfinityHom 𝒜 ε'.reducedAlgebra) :
    (liftReducedHomEquiv 𝒜 ε' k).val = ε'.inclusion.toAInfinityHom.comp k := (rfl)

@[simp] theorem taylor_liftReducedHomEquiv_symm (𝒜 : AInfinityAlgebra R A) (ε' : ℬ.Augmentation)
    (g) : ((liftReducedHomEquiv 𝒜 ε').symm g).taylor = ε'.reducedPart ∘ₗ g.val.taylor :=
  AInfinityHom.taylor_ofTaylor _ _ _

/-- `(liftReducedHomEquiv 𝒜 ε').symm g` has linear part `ε'.reducedPart ∘ₗ g.val.linearPart`. -/
@[simp] theorem linearPart_liftReducedHomEquiv_symm (𝒜 : AInfinityAlgebra R A)
    (ε' : ℬ.Augmentation) (g) :
    ((liftReducedHomEquiv 𝒜 ε').symm g).linearPart = ε'.reducedPart ∘ₗ g.val.linearPart :=
  LinearMap.ext fun _ ↦ by simp

end AInfinityAlgebra.Augmentation

namespace AInfinityHom

variable {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B} {𝒞 : AInfinityAlgebra R C}

/-- A morphism of augmented `A∞` algebras is **augmented** when it is strictly unital, its linear
part intertwines the augmentations, and all higher components land in `ker ε'`. -/
structure IsAugmented (f : AInfinityHom 𝒜 ℬ) (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation) : Prop where
  /-- The morphism is strictly unital for the chosen strict units. -/
  isStrictlyUnital : f.IsStrictlyUnital ε.isStrictUnit ε'.isStrictUnit
  /-- The linear component intertwines the augmentations. -/
  augmentation_comp_linearPart : ε'.toLinearMap ∘ₗ f.linearPart = ε.toLinearMap
  /-- Every component above arity one lands in the target augmentation ideal. -/
  augmentation_component_eq_zero : ∀ {n : ℕ}, n ≠ 1 → ∀ x : Fin n → A, ε' (f.component n x) = 0

/-- An `A∞` morphism is augmented if and only if it is strictly unital and its Taylor map
intertwines augmentations via `letter`. -/
theorem isAugmented_iff_taylor {f : AInfinityHom 𝒜 ℬ} {ε : 𝒜.Augmentation} {ε' : ℬ.Augmentation} :
    f.IsAugmented ε ε' ↔ f.IsStrictlyUnital ε.isStrictUnit ε'.isStrictUnit ∧
      ε'.toLinearMap ∘ₗ f.taylor = ε.toLinearMap ∘ₗ letter R A := by
  refine ⟨fun hf ↦ ⟨hf.isStrictlyUnital, linearMap_ext R A fun n x ↦ ?_⟩,
    fun ⟨hsu, htaylor⟩ ↦ ⟨hsu, LinearMap.ext fun a ↦ by
      simpa using LinearMap.congr_fun htaylor (ofLetter R A a), fun {n} hn x ↦ ?_⟩⟩
  · simp only [LinearMap.comp_apply]
    by_cases hn1 : n.val = 1
    · obtain ⟨k, hk⟩ := n; subst hn1
      rw [of_tprod_eq_subword R hk, subword_one R A x hk, letter_ofLetter, ← f.linearPart_apply]
      exact LinearMap.congr_fun hf.augmentation_comp_linearPart (x 0)
    · have hcomp : f.component n.val (fun i ↦ 𝒜.grading.koszulTwist ((n.val : ℤ) - 1 - i) (x i)) =
          f.taylor (of R A n (PiTensorProduct.tprod R x)) := by
        simp [component_apply f n.val n.property, InternalGrading.koszulTwist_koszulTwist]
      rw [← hcomp, of_tprod_eq_subword R n.property, letter_subword_of_ne_one R A x 0 hn1, map_zero]
      exact hf.augmentation_component_eq_zero hn1 _
  · rcases Nat.eq_zero_or_pos n with rfl | hnpos; · simp
    simpa [component_apply f n hnpos, of_tprod_eq_subword R hnpos,
      letter_subword_of_ne_one R A _ 0 hn] using LinearMap.congr_fun htaylor (of R A ⟨n, hnpos⟩
        (PiTensorProduct.tprod R fun i ↦ 𝒜.grading.koszulTwist ((n : ℤ) - 1 - i) (x i)))

/-- The identity morphism of an augmented `A∞` algebra is augmented. -/
@[simp] theorem isAugmented_id (ε : 𝒜.Augmentation) : (AInfinityHom.id 𝒜).IsAugmented ε ε :=
  isAugmented_iff_taylor.2 ⟨isStrictlyUnital_id ε.isStrictUnit, by rw [taylor_id]⟩

/-- Composition preserves augmented `A∞` morphisms. -/
theorem IsAugmented.comp {g : AInfinityHom ℬ 𝒞} {f : AInfinityHom 𝒜 ℬ}
    {ε : 𝒜.Augmentation} {ε' : ℬ.Augmentation} {ε'' : 𝒞.Augmentation}
    (hg : g.IsAugmented ε' ε'') (hf : f.IsAugmented ε ε') : (g.comp f).IsAugmented ε ε'' := by
  rw [isAugmented_iff_taylor] at hg hf ⊢
  exact ⟨hg.1.comp hf.1, by
    rw [taylor_comp, ← LinearMap.comp_assoc, hg.2, LinearMap.comp_assoc, ← f.taylor_def, hf.2]⟩

/-- A strict `A∞` morphism is augmented if and only if its linear part preserves the unit and
intertwines the augmentations. -/
theorem IsStrict.isAugmented_iff {f : AInfinityHom 𝒜 ℬ} {ε : 𝒜.Augmentation} {ε' : ℬ.Augmentation}
    (hf : f.IsStrict) :
    f.IsAugmented ε ε' ↔
      f.linearPart ε.unit = ε'.unit ∧ ε'.toLinearMap ∘ₗ f.linearPart = ε.toLinearMap := by
  rw [isAugmented_iff_taylor, hf.isStrictlyUnital_iff]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ LinearMap.ext fun a ↦
    by simpa using LinearMap.congr_fun h (ofLetter R A a),
    fun h ↦ by rw [(isStrict_iff f).1 hf, ← LinearMap.comp_assoc, h]⟩

end AInfinityHom

section DG

variable {D : Type uA} {E : Type uB} [Ring D] [Ring E] [Algebra R D] [Algebra R E]
  {𝒟 : ℤ → Submodule R D} {ℰ : ℤ → Submodule R E} [GradedAlgebra 𝒟] [GradedAlgebra ℰ]
  {dD : D →ₗ[R] D} {dE : E →ₗ[R] E} {hD : IsDGAlgebra 𝒟 dD} {hE : IsDGAlgebra ℰ dE}

/-- A DG algebra morphism induces an augmented `A∞` morphism iff it intertwines augmentations. -/
@[simp] theorem DGAlgHom.isAugmented_toAInfinityHom_iff (φ : DGAlgHom hD hE)
    (eD : DGAlgAugmentation hD) (eE : DGAlgAugmentation hE) :
    φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.IsAugmented
      eD.toAInfinityAugmentation eE.toAInfinityAugmentation ↔ eE.comp φ = eD := by
  rw [(AInfinityHom.isStrict_toAInfinityHom _).isAugmented_iff]
  simp only [AInfinityStrictHom.linearPart_toAInfinityHom,
    DGAlgAugmentation.toAInfinityAugmentation_unit]
  exact ⟨fun h ↦ DGAlgHom.ext fun x ↦ by simpa using LinearMap.congr_fun h.2 x,
    fun h ↦ ⟨by simp, LinearMap.ext fun x ↦ by simpa using congrArg (· x) h⟩⟩

end DG

namespace AInfinityHom.IsStrictlyUnital

variable {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B}
  {f f₁ f₂ : AInfinityHom 𝒜 ℬ} {ε : 𝒜.Augmentation} {eB : B} {hB : ℬ.StrictUnit eB}

/-- A strictly unital `A∞` morphism out of an augmented `A∞` algebra splits on any bar word into
its scalar unit term plus its value on the reduced bar word. -/
theorem taylor_apply (hf : f.IsStrictlyUnital ε.isStrictUnit hB) (z : ReducedTensorWords R A) :
    f.taylor z = ε (letter R A z) • eB +
      f.taylor (ε.inclusion.barMap (ReducedTensorWords.map (R := R) ε.reducedPart z)) := by
  conv_lhs =>
    rw [← sub_add_cancel z (ε.inclusion.barMap (ReducedTensorWords.map (R := R) ε.reducedPart z)),
      map_add]
  rw [hf.taylor_eq_linearPart_letter
      (ε.sub_inclusion_barMap_map_reducedPart_mem_degenerateWords z),
    ε.letter_sub_inclusion_barMap_map_reducedPart z, map_smul, hf.map_unit]

/-- Two strictly unital `A∞` morphisms out of an augmented `A∞` algebra are equal as soon as their
restrictions to `ker ε` agree. -/
theorem ext_comp_inclusion (hf₁ : f₁.IsStrictlyUnital ε.isStrictUnit hB)
    (hf₂ : f₂.IsStrictlyUnital ε.isStrictUnit hB)
    (h : f₁.comp ε.inclusion.toAInfinityHom = f₂.comp ε.inclusion.toAInfinityHom) : f₁ = f₂ := by
  refine AInfinityHom.ext (LinearMap.ext fun z ↦ ?_)
  have ht := LinearMap.congr_fun (congrArg AInfinityHom.taylor h)
    (ReducedTensorWords.map (R := R) ε.reducedPart z)
  simp only [AInfinityHom.taylor_comp, AInfinityStrictHom.barMap_toAInfinityHom,
    LinearMap.comp_apply] at ht
  rw [hf₁.taylor_apply z, hf₂.taylor_apply z, ht]

end AInfinityHom.IsStrictlyUnital

namespace AInfinityHom.IsAugmented

variable {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B} {𝒞 : AInfinityAlgebra R C}
  {f : AInfinityHom 𝒜 ℬ} {ε : 𝒜.Augmentation} {ε' : ℬ.Augmentation}

/-- The linear part of an augmented `A∞` morphism intertwines the augmentations pointwise. -/
theorem augmentation_comp_linearPart_apply (hf : f.IsAugmented ε ε') (a : A) :
    ε' (f.linearPart a) = ε a :=
  LinearMap.congr_fun hf.augmentation_comp_linearPart a

/-- The Taylor map of an augmented `A∞` morphism intertwines the augmentations via `letter`. -/
theorem augmentation_comp_taylor (hf : f.IsAugmented ε ε') :
    ε'.toLinearMap ∘ₗ f.taylor = ε.toLinearMap ∘ₗ letter R A := (isAugmented_iff_taylor.1 hf).2

/-- Pointwise augmentation compatibility of the Taylor map of an augmented `A∞` morphism. -/
theorem augmentation_comp_taylor_apply (hf : f.IsAugmented ε ε') (z : ReducedTensorWords R A) :
    ε' (f.taylor z) = ε (letter R A z) := LinearMap.congr_fun hf.augmentation_comp_taylor z

/-- The linear part of an augmented `A∞` morphism maps `ker ε` into `ker ε'`. -/
theorem linearPart_mem_augmentationIdeal (hf : f.IsAugmented ε ε') {a : A}
    (ha : a ∈ ε.augmentationIdeal) : f.linearPart a ∈ ε'.augmentationIdeal := by
  rw [AInfinityAlgebra.Augmentation.mem_augmentationIdeal, hf.augmentation_comp_linearPart_apply]
  exact (ε.mem_augmentationIdeal).mp ha

/-- Restricting an augmented `A∞` morphism to `ker ε` produces Taylor components in `ker ε'`. -/
theorem taylor_comp_inclusion_mem (hf : f.IsAugmented ε ε')
    (w : ReducedTensorWords R ε.augmentationIdeal) :
    (f.comp ε.inclusion.toAInfinityHom).taylor w ∈ ε'.augmentationIdeal := by
  have hzero : ε'.toLinearMap ∘ₗ f.taylor ∘ₗ ε.inclusion.barMap = 0 := by
    rw [← LinearMap.comp_assoc, hf.augmentation_comp_taylor, LinearMap.comp_assoc,
      AInfinityStrictHom.barMap_def, letter_comp_map, ← LinearMap.comp_assoc,
      ε.inclusion_toLinearMap, ε.toLinearMap_comp_subtype, LinearMap.zero_comp]
  simpa [AInfinityAlgebra.Augmentation.mem_augmentationIdeal, AInfinityHom.taylor_comp] using
    LinearMap.congr_fun hzero w

/-- An augmented `A∞` morphism splits on any bar word into its scalar unit term plus its value on
the reduced bar word. -/
theorem taylor_apply (hf : f.IsAugmented ε ε') (z : ReducedTensorWords R A) :
    f.taylor z = ε (letter R A z) • ε'.unit +
      f.taylor (ε.inclusion.barMap (ReducedTensorWords.map (R := R) ε.reducedPart z)) :=
  hf.isStrictlyUnital.taylor_apply z

/-- Two augmented `A∞` morphisms are equal as soon as their restrictions to `ker ε` agree. -/
theorem ext_comp_inclusion {f₁ f₂ : AInfinityHom 𝒜 ℬ}
    (hf₁ : f₁.IsAugmented ε ε') (hf₂ : f₂.IsAugmented ε ε')
    (h : f₁.comp ε.inclusion.toAInfinityHom = f₂.comp ε.inclusion.toAInfinityHom) : f₁ = f₂ :=
  hf₁.isStrictlyUnital.ext_comp_inclusion hf₂.isStrictlyUnital h

/-- The nonunital `A∞` morphism `ker ε ⟶ ker ε'` induced on reduced augmentation ideals by `f`. -/
noncomputable def reducedHom (hf : f.IsAugmented ε ε') :
    AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra :=
  (AInfinityAlgebra.Augmentation.liftReducedHomEquiv ε.reducedAlgebra ε').symm
    ⟨f.comp ε.inclusion.toAInfinityHom, hf.taylor_comp_inclusion_mem⟩

@[simp] theorem taylor_reducedHom (hf : f.IsAugmented ε ε') :
    hf.reducedHom.taylor = ε'.reducedPart ∘ₗ f.taylor ∘ₗ ε.inclusion.barMap := by
  simp [reducedHom, AInfinityHom.taylor_comp]

/-- The linear part of `hf.reducedHom` is `ε'.reducedPart ∘ₗ f.linearPart` on `ker ε`. -/
@[simp] theorem linearPart_reducedHom (hf : f.IsAugmented ε ε') :
    hf.reducedHom.linearPart = ε'.reducedPart ∘ₗ f.linearPart ∘ₗ ε.augmentationIdeal.subtype :=
  LinearMap.ext fun _ ↦ by simp [AInfinityStrictHom.barMap_def]

/-- The induced morphism `hf.reducedHom` intertwines the augmentation-ideal inclusions with `f`. -/
@[simp] theorem inclusion_comp_reducedHom (hf : f.IsAugmented ε ε') :
    ε'.inclusion.toAInfinityHom.comp hf.reducedHom = f.comp ε.inclusion.toAInfinityHom :=
  congrArg Subtype.val ((AInfinityAlgebra.Augmentation.liftReducedHomEquiv _ _).apply_symm_apply _)

@[simp] theorem reducedHom_id (ε : 𝒜.Augmentation) :
    (isAugmented_id ε).reducedHom = AInfinityHom.id ε.reducedAlgebra := AInfinityHom.ext <| by
  rw [taylor_reducedHom, taylor_id, taylor_id, AInfinityStrictHom.barMap_def, letter_comp_map,
    ← LinearMap.comp_assoc, ε.inclusion_toLinearMap, ε.reducedPart_comp_subtype, LinearMap.id_comp]

/-- Passing to `reducedHom` preserves composition of augmented `A∞` morphisms. -/
theorem reducedHom_comp {g : AInfinityHom ℬ 𝒞} {ε'' : 𝒞.Augmentation}
    (hg : g.IsAugmented ε' ε'') (hf : f.IsAugmented ε ε') :
    (hg.comp hf).reducedHom = hg.reducedHom.comp hf.reducedHom := by
  refine AInfinityHom.ext (LinearMap.ext fun w ↦ ?_)
  have hbw := LinearMap.congr_fun (by
    simpa only [barMap_comp, AInfinityStrictHom.barMap_toAInfinityHom] using
      congrArg AInfinityHom.barMap hf.inclusion_comp_reducedHom) w
  simp only [taylor_reducedHom, taylor_comp, LinearMap.comp_apply] at hbw ⊢; rw [hbw]

end AInfinityHom.IsAugmented

/-- A strictly unital `A∞` morphism out of an augmented `A∞` algebra is augmented if and only if
its restriction to `ker ε` has Taylor components in `ker ε'`. -/
theorem AInfinityHom.IsStrictlyUnital.isAugmented_iff_taylor_comp_inclusion_mem
    {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B} {f : AInfinityHom 𝒜 ℬ}
    {ε : 𝒜.Augmentation} {ε' : ℬ.Augmentation}
    (hf : f.IsStrictlyUnital ε.isStrictUnit ε'.isStrictUnit) :
    f.IsAugmented ε ε' ↔
      ∀ w : ReducedTensorWords R ε.augmentationIdeal,
        (f.comp ε.inclusion.toAInfinityHom).taylor w ∈ ε'.augmentationIdeal := by
  refine ⟨fun h ↦ h.taylor_comp_inclusion_mem,
    fun hw ↦ AInfinityHom.isAugmented_iff_taylor.2 ⟨hf, LinearMap.ext fun z ↦ ?_⟩⟩
  have hmem := (ε'.mem_augmentationIdeal).mp (hw (ReducedTensorWords.map (R := R) ε.reducedPart z))
  simp only [AInfinityHom.taylor_comp, AInfinityStrictHom.barMap_toAInfinityHom,
    LinearMap.comp_apply] at hmem
  simp [hf.taylor_apply z, hmem]

namespace AInfinityAlgebra.Augmentation

variable {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B} {𝒞 : AInfinityAlgebra R C}

/-! ### Extension of nonunital morphisms to strictly unital morphisms -/

private noncomputable def extendStrictlyUnitalTaylor (ε : 𝒜.Augmentation) (eB : B)
    (g : AInfinityHom ε.reducedAlgebra ℬ) : ReducedTensorWords R A →ₗ[R] B :=
  LinearMap.toSpanSingleton R B eB ∘ₗ ε.toLinearMap ∘ₗ letter R A +
    g.taylor ∘ₗ ReducedTensorWords.map (R := R) ε.reducedPart

private theorem extendStrictlyUnitalTaylor_comp_inclusion_barMap (ε : 𝒜.Augmentation) (eB : B)
    (g : AInfinityHom ε.reducedAlgebra ℬ) :
    ε.extendStrictlyUnitalTaylor eB g ∘ₗ ε.inclusion.barMap = g.taylor := by
  rw [extendStrictlyUnitalTaylor, LinearMap.add_comp, LinearMap.comp_assoc, LinearMap.comp_assoc,
    AInfinityStrictHom.barMap_def, letter_comp_map, ε.inclusion_toLinearMap,
    ← LinearMap.comp_assoc (letter R _), ε.toLinearMap_comp_subtype, LinearMap.zero_comp,
    LinearMap.comp_zero, zero_add, LinearMap.comp_assoc, ← map_comp, ε.reducedPart_comp_subtype,
    map_id, LinearMap.comp_id]

private theorem extendStrictlyUnitalTaylor_of_mem_degenerateWords (ε : 𝒜.Augmentation) (eB : B)
    (g : AInfinityHom ε.reducedAlgebra ℬ) {z : ReducedTensorWords R A}
    (hz : z ∈ degenerateWords R A ε.unit) :
    ε.extendStrictlyUnitalTaylor eB g z = ε (letter R A z) • eB := by
  simp [extendStrictlyUnitalTaylor, LinearMap.mem_ker.mp
    (degenerateWords_le_ker_map ε.reducedPart ε.reducedPart_unit hz)]

private theorem extendStrictlyUnitalTaylor_of_tprod_eq_zero (ε : 𝒜.Augmentation) (eB : B)
    (g : AInfinityHom ε.reducedAlgebra ℬ) (m : {m : ℕ // 0 < m}) (hm : m.val ≠ 1)
    (y : Fin m.val → A) (hy : ∃ i, y i = ε.unit) :
    ε.extendStrictlyUnitalTaylor eB g (of R A m (PiTensorProduct.tprod R y)) = 0 := by
  rw [extendStrictlyUnitalTaylor_of_mem_degenerateWords ε eB g
      (of_tprod_mem_degenerateWords m y hy),
    of_tprod_eq_subword R m.property, letter_subword_of_ne_one R A y 0 hm, map_zero, zero_smul]

private theorem extendStrictlyUnitalTaylor_isHomogeneous (ε : 𝒜.Augmentation) {eB : B}
    (hB : ℬ.StrictUnit eB) (g : AInfinityHom ε.reducedAlgebra ℬ) :
    LinearMap.IsHomogeneous (ε.extendStrictlyUnitalTaylor eB g) (gradedPiece (𝒜.grading.shift 1))
      (ℬ.grading.shift 1).piece 0 := by
  refine (LinearMap.isHomogeneous_def.mpr fun p _ hz ↦ ?_).add ?_
  · have hl := (isHomogeneous_letter (𝒜.grading.shift 1)).map_mem hz
    rw [add_zero, InternalGrading.shift_piece] at hl ⊢
    by_cases hp : p + 1 = 0
    · rw [hp, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
      exact Submodule.smul_mem _ _ hB.degree_zero
    · simp [ε.map_of_mem_ne_zero (p + 1) _ hl hp]
  · simpa only [add_zero] using g.isHomogeneous_taylor.comp (isHomogeneous_map _ _
      (LinearMap.isHomogeneous_shift_piece_iff.2 ε.isHomogeneous_reducedPart))

private theorem extendStrictlyUnitalTaylor_component_eq (ε : 𝒜.Augmentation) {eB : B}
    (hB : ℬ.StrictUnit eB) (g : AInfinityHom ε.reducedAlgebra ℬ) :
    ℬ.taylor ∘ₗ coalgHom R (ε.extendStrictlyUnitalTaylor eB g) =
      ε.extendStrictlyUnitalTaylor eB g ∘ₗ 𝒜.barDifferential := by
  let t := ε.extendStrictlyUnitalTaylor eB g
  have hcoalg : coalgHom R t ∘ₗ ε.inclusion.barMap = g.barMap := by
    rw [AInfinityStrictHom.barMap_def,
      ((isCoalgHom_coalgHom t).comp (isCoalgHom_map _)).eq_coalgHom,
      ← LinearMap.comp_assoc, letter_comp_coalgHom, ← AInfinityStrictHom.barMap_def,
      ε.extendStrictlyUnitalTaylor_comp_inclusion_barMap eB g, g.barMap_eq_coalgHom]
  have hred : (ℬ.taylor ∘ₗ coalgHom R t) ∘ₗ ε.inclusion.barMap =
      (t ∘ₗ 𝒜.barDifferential) ∘ₗ ε.inclusion.barMap := by
    rw [LinearMap.comp_assoc, hcoalg, g.taylor_comp_barMap,
      ← ε.extendStrictlyUnitalTaylor_comp_inclusion_barMap eB g, LinearMap.comp_assoc,
      ← ε.inclusion.barDifferential_comp_barMap, ← LinearMap.comp_assoc]
  have hker := ε.isStrictUnit.degenerateWords_le_ker_taylor_coalgHom_sub_barDifferential hB t
    (ε.extendStrictlyUnitalTaylor_isHomogeneous hB g)
    (by
      rw [extendStrictlyUnitalTaylor_of_mem_degenerateWords _ _ _ (ofLetter_mem_degenerateWords _),
        letter_ofLetter, ε.map_unit, one_smul])
    (ε.extendStrictlyUnitalTaylor_of_tprod_eq_zero eB g)
  refine LinearMap.ext fun z ↦ ?_
  have hsub := sub_eq_zero.mp <| LinearMap.mem_ker.mp <|
    hker (ε.sub_inclusion_barMap_map_reducedPart_mem_degenerateWords z)
  have hredr := LinearMap.congr_fun hred (ReducedTensorWords.map (R := R) ε.reducedPart z)
  dsimp only [t, LinearMap.comp_apply] at hsub hredr ⊢
  simpa only [← map_add, sub_add_cancel] using congrArg₂ (· + ·) hsub hredr

/-- Extend any nonunital `A∞` morphism `g : ker ε ⟶ B` into a strictly unital `A∞` algebra
`(B, e_B)` to a strictly unital `A∞` morphism `A ⟶ B`. -/
noncomputable def extendStrictlyUnitalHom (ε : 𝒜.Augmentation) {eB : B} (hB : ℬ.StrictUnit eB)
    (g : AInfinityHom ε.reducedAlgebra ℬ) : AInfinityHom 𝒜 ℬ :=
  AInfinityHom.ofTaylor (ε.extendStrictlyUnitalTaylor eB g)
    (ε.extendStrictlyUnitalTaylor_isHomogeneous hB g)
    (ε.extendStrictlyUnitalTaylor_component_eq hB g)

/-- The Taylor map of `extendStrictlyUnitalHom` combines the scalar unit projection on single
letters with `g.taylor` along `ε.reducedPart`. -/
@[simp] theorem taylor_extendStrictlyUnitalHom (ε : 𝒜.Augmentation) {eB : B}
    (hB : ℬ.StrictUnit eB) (g : AInfinityHom ε.reducedAlgebra ℬ) :
    (ε.extendStrictlyUnitalHom hB g).taylor =
      LinearMap.toSpanSingleton R B eB ∘ₗ ε.toLinearMap ∘ₗ letter R A +
        g.taylor ∘ₗ ReducedTensorWords.map (R := R) ε.reducedPart :=
  AInfinityHom.taylor_ofTaylor _ _ _

/-- The linear part of `extendStrictlyUnitalHom` combines the unit map with `g.linearPart` on
`ker ε`. -/
@[simp] theorem linearPart_extendStrictlyUnitalHom (ε : 𝒜.Augmentation) {eB : B}
    (hB : ℬ.StrictUnit eB) (g : AInfinityHom ε.reducedAlgebra ℬ) :
    (ε.extendStrictlyUnitalHom hB g).linearPart =
      LinearMap.toSpanSingleton R B eB ∘ₗ ε.toLinearMap + g.linearPart ∘ₗ ε.reducedPart :=
  LinearMap.ext fun _ ↦ by simp

/-- Extending a morphism `g : ker ε ⟶ B` yields a strictly unital `A∞` morphism. -/
@[simp] theorem isStrictlyUnital_extendStrictlyUnitalHom (ε : 𝒜.Augmentation) {eB : B}
    (hB : ℬ.StrictUnit eB) (g : AInfinityHom ε.reducedAlgebra ℬ) :
    (ε.extendStrictlyUnitalHom hB g).IsStrictlyUnital ε.isStrictUnit hB := by
  refine ⟨by simp, fun {n} hn x ⟨i, hi⟩ ↦ ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hnpos; · simp
  rw [AInfinityHom.component_apply _ n hnpos, extendStrictlyUnitalHom, AInfinityHom.taylor_ofTaylor]
  exact ε.extendStrictlyUnitalTaylor_of_tprod_eq_zero eB g ⟨n, hnpos⟩ hn _
    ⟨i, by rw [hi, 𝒜.grading.koszulTwist_apply_of_mem_zero ε.isStrictUnit.degree_zero]⟩

/-- Restricting `ε.extendStrictlyUnitalHom hB g` to `ker ε` recovers `g`. -/
@[simp] theorem extendStrictlyUnitalHom_comp_inclusion (ε : 𝒜.Augmentation) {eB : B}
    (hB : ℬ.StrictUnit eB) (g : AInfinityHom ε.reducedAlgebra ℬ) :
    (ε.extendStrictlyUnitalHom hB g).comp ε.inclusion.toAInfinityHom = g :=
  AInfinityHom.ext <| by
    rw [AInfinityHom.taylor_comp, AInfinityStrictHom.barMap_toAInfinityHom,
      extendStrictlyUnitalHom, AInfinityHom.taylor_ofTaylor,
      ε.extendStrictlyUnitalTaylor_comp_inclusion_barMap eB g]

/-- Extending the restriction of a strictly unital morphism `f : A ⟶ B` recovers `f`. -/
theorem extendStrictlyUnitalHom_of_isStrictlyUnital (ε : 𝒜.Augmentation) {eB : B}
    {hB : ℬ.StrictUnit eB} {f : AInfinityHom 𝒜 ℬ} (hf : f.IsStrictlyUnital ε.isStrictUnit hB) :
    ε.extendStrictlyUnitalHom hB (f.comp ε.inclusion.toAInfinityHom) = f :=
  (ε.isStrictlyUnital_extendStrictlyUnitalHom hB _).ext_comp_inclusion hf
    (ε.extendStrictlyUnitalHom_comp_inclusion hB _)

/-- **Reduction of strictly unital `A∞` morphisms to the augmentation ideal**: strictly unital
`A∞` morphisms `(A, ε) ⟶ (B, e_B)` into any strictly unital `A∞` algebra correspond bijectively to
nonunital `A∞` morphisms `ker ε ⟶ B`. -/
noncomputable def strictlyUnitalHomEquiv (ε : 𝒜.Augmentation) {eB : B} (hB : ℬ.StrictUnit eB) :
    {f : AInfinityHom 𝒜 ℬ // f.IsStrictlyUnital ε.isStrictUnit hB} ≃
      AInfinityHom ε.reducedAlgebra ℬ where
  toFun f := f.val.comp ε.inclusion.toAInfinityHom
  invFun g := ⟨ε.extendStrictlyUnitalHom hB g, ε.isStrictlyUnital_extendStrictlyUnitalHom hB g⟩
  left_inv f := Subtype.ext (ε.extendStrictlyUnitalHom_of_isStrictlyUnital f.property)
  right_inv g := ε.extendStrictlyUnitalHom_comp_inclusion hB g

@[simp] theorem strictlyUnitalHomEquiv_apply (ε : 𝒜.Augmentation) {eB : B} (hB : ℬ.StrictUnit eB)
    (f : {f : AInfinityHom 𝒜 ℬ // f.IsStrictlyUnital ε.isStrictUnit hB}) :
    ε.strictlyUnitalHomEquiv hB f = f.val.comp ε.inclusion.toAInfinityHom := (rfl)

@[simp] theorem strictlyUnitalHomEquiv_symm_apply_val (ε : 𝒜.Augmentation) {eB : B}
    (hB : ℬ.StrictUnit eB) (g : AInfinityHom ε.reducedAlgebra ℬ) :
    ((ε.strictlyUnitalHomEquiv hB).symm g).val = ε.extendStrictlyUnitalHom hB g := (rfl)

/-! ### Specialization to augmented morphisms -/

/-- Extend any nonunital `A∞` morphism `g : ker ε ⟶ ker ε'` between reduced augmentation ideals to
a strictly unital augmented `A∞` morphism `A ⟶ B`. -/
noncomputable def extendReducedHom (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) : AInfinityHom 𝒜 ℬ :=
  ε.extendStrictlyUnitalHom ε'.isStrictUnit (ε'.inclusion.toAInfinityHom.comp g)

/-- The Taylor map of `extendReducedHom` combines the scalar unit projection on single letters with
the reduced Taylor map along `ε.reducedPart`. -/
@[simp] theorem taylor_extendReducedHom (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    (ε.extendReducedHom ε' g).taylor = ε'.unitHom ∘ₗ ε.toLinearMap ∘ₗ letter R A +
      ε'.augmentationIdeal.subtype ∘ₗ g.taylor ∘ₗ
        ReducedTensorWords.map (R := R) ε.reducedPart := by
  rw [extendReducedHom, taylor_extendStrictlyUnitalHom,
    AInfinityStrictHom.taylor_toAInfinityHom_comp]
  exact LinearMap.ext fun _ ↦ by simp

/-- The linear part of `extendReducedHom` combines the unit map with `g.linearPart` on `ker ε`. -/
@[simp] theorem linearPart_extendReducedHom (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    (ε.extendReducedHom ε' g).linearPart =
      ε'.unitHom ∘ₗ ε.toLinearMap + ε'.augmentationIdeal.subtype ∘ₗ g.linearPart ∘ₗ ε.reducedPart :=
  LinearMap.ext fun _ ↦ by simp

/-- Extending a morphism `g : ker ε ⟶ ker ε'` yields a strictly unital augmented `A∞` morphism. -/
@[simp] theorem isAugmented_extendReducedHom (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    (ε.extendReducedHom ε' g).IsAugmented ε ε' :=
  (ε.isStrictlyUnital_extendStrictlyUnitalHom ε'.isStrictUnit
    _).isAugmented_iff_taylor_comp_inclusion_mem.2 fun _ ↦ by simp

@[simp] theorem extendReducedHom_comp_inclusion (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    (ε.extendReducedHom ε' g).comp ε.inclusion.toAInfinityHom =
      ε'.inclusion.toAInfinityHom.comp g :=
  ε.extendStrictlyUnitalHom_comp_inclusion ε'.isStrictUnit _

@[simp] theorem reducedHom_extendReducedHom (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    (ε.isAugmented_extendReducedHom ε' g).reducedHom = g :=
  (liftReducedHomEquiv ε.reducedAlgebra ε').injective <| Subtype.ext <| by simp

@[simp] theorem extendReducedHom_reducedHom {ε : 𝒜.Augmentation} {ε' : ℬ.Augmentation}
    {f : AInfinityHom 𝒜 ℬ} (hf : f.IsAugmented ε ε') : ε.extendReducedHom ε' hf.reducedHom = f := by
  rw [extendReducedHom, hf.inclusion_comp_reducedHom]
  exact ε.extendStrictlyUnitalHom_of_isStrictlyUnital hf.isStrictlyUnital

/-- Extending the identity morphism of `ker ε` recovers the identity morphism of `A`. -/
@[simp] theorem extendReducedHom_id (ε : 𝒜.Augmentation) :
    ε.extendReducedHom ε (AInfinityHom.id ε.reducedAlgebra) = AInfinityHom.id 𝒜 := by
  rw [← AInfinityHom.IsAugmented.reducedHom_id ε, extendReducedHom_reducedHom]

/-- **Reduction of augmented `A∞` morphisms to the augmentation ideal**: strictly unital augmented
`A∞` morphisms `(A, ε) ⟶ (B, ε')` correspond bijectively to nonunital `A∞` morphisms
`ker ε ⟶ ker ε'`. -/
noncomputable def augmentedHomEquiv (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation) :
    {f : AInfinityHom 𝒜 ℬ // f.IsAugmented ε ε'} ≃
      AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra :=
  ((Equiv.subtypeEquivRight fun _ ↦
      ⟨fun hf ↦ ⟨hf.isStrictlyUnital, hf.taylor_comp_inclusion_mem⟩,
        fun ⟨hsu, hmem⟩ ↦ hsu.isAugmented_iff_taylor_comp_inclusion_mem.2 hmem⟩).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm).trans
    (((ε.strictlyUnitalHomEquiv ε'.isStrictUnit).subtypeEquiv fun _ ↦ Iff.rfl).trans
      (liftReducedHomEquiv ε.reducedAlgebra ε').symm)

@[simp] theorem augmentedHomEquiv_apply (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (f : {f : AInfinityHom 𝒜 ℬ // f.IsAugmented ε ε'}) :
    ε.augmentedHomEquiv ε' f = f.property.reducedHom := (rfl)

@[simp] theorem augmentedHomEquiv_symm_apply_val (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    ((ε.augmentedHomEquiv ε').symm g).val = ε.extendReducedHom ε' g := (rfl)

/-- `extendReducedHom` preserves composition of morphisms between reduced augmentation ideals. -/
theorem extendReducedHom_comp (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation) (ε'' : 𝒞.Augmentation)
    (h : AInfinityHom ε'.reducedAlgebra ε''.reducedAlgebra)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    ε.extendReducedHom ε'' (h.comp g) =
      (ε'.extendReducedHom ε'' h).comp (ε.extendReducedHom ε' g) :=
  (ε.isAugmented_extendReducedHom ε'' _).ext_comp_inclusion
    ((ε'.isAugmented_extendReducedHom ε'' h).comp (ε.isAugmented_extendReducedHom ε' g))
    (by
      rw [extendReducedHom_comp_inclusion, AInfinityHom.comp_assoc, extendReducedHom_comp_inclusion,
        ← AInfinityHom.comp_assoc (ε'.extendReducedHom ε'' h), extendReducedHom_comp_inclusion,
        AInfinityHom.comp_assoc])

end AInfinityAlgebra.Augmentation
end TauCeti
