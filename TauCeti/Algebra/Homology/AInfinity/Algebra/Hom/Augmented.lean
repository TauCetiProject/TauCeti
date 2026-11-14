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

An `A∞` morphism `f : A ⟶ B` between augmented uncurved `A∞` algebras `(A, ε)` and `(B, ε')` is
**augmented** (`AInfinityHom.IsAugmented`) if it is strictly unital and `ε' ∘ f.taylor = ε ∘ letter`
(`isAugmented_iff_taylor`). Augmented morphisms correspond bijectively to nonunital `A∞` morphisms
`ker ε ⟶ ker ε'` (`AInfinityAlgebra.Augmentation.augmentedHomEquiv`) via `reducedHom` and
`extendReducedHom`.

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

@[simp]
theorem inclusion_toLinearMap (ε : 𝒜.Augmentation) :
    ε.inclusion.toLinearMap = ε.augmentationIdeal.subtype := (rfl)

@[simp]
theorem inclusion_apply (ε : 𝒜.Augmentation) (x : ε.augmentationIdeal) :
    ε.inclusion x = x := (rfl)

@[simp]
theorem reducedPart_unit (ε : 𝒜.Augmentation) : ε.reducedPart ε.unit = 0 :=
  Subtype.ext <| by rw [coe_reducedPart, map_unit, one_smul, sub_self, Submodule.coe_zero]

theorem isHomogeneous_reducedPart (ε : 𝒜.Augmentation) :
    LinearMap.IsHomogeneous ε.reducedPart 𝒜.grading.piece ε.reducedAlgebra.grading.piece 0 :=
  LinearMap.isHomogeneous_def.mpr fun p a ha ↦ by
    rw [add_zero, ε.reducedAlgebra_grading, ε.reducedGrading_piece, Submodule.mem_comap,
      Submodule.subtype_apply, ε.coe_reducedPart]
    by_cases hp : p = 0
    · subst hp; exact Submodule.sub_mem _ ha (Submodule.smul_mem _ _ ε.isStrictUnit.degree_zero)
    · simpa only [ε.map_of_mem_ne_zero p a ha hp, zero_smul, sub_zero] using ha

theorem isHomogeneous_reducedPart_shift_one (ε : 𝒜.Augmentation) :
    LinearMap.IsHomogeneous ε.reducedPart (𝒜.grading.shift 1).piece
      (ε.reducedAlgebra.grading.shift 1).piece 0 :=
  LinearMap.isHomogeneous_def.mpr fun _ _ ha ↦ by
    simpa only [InternalGrading.shift_piece, add_zero] using
      ε.isHomogeneous_reducedPart.map_mem (by simpa only [InternalGrading.shift_piece] using ha)

theorem reducedPart_comp_inclusion_toLinearMap (ε : 𝒜.Augmentation) :
    ε.reducedPart ∘ₗ ε.inclusion.toLinearMap = LinearMap.id :=
  LinearMap.ext ε.reducedPart_coe

@[simp]
theorem map_reducedPart_comp_inclusion_barMap (ε : 𝒜.Augmentation) :
    ReducedTensorWords.map (R := R) ε.reducedPart ∘ₗ ε.inclusion.barMap = LinearMap.id := by
  rw [AInfinityStrictHom.barMap_def, ← ReducedTensorWords.map_comp,
    ε.reducedPart_comp_inclusion_toLinearMap, ReducedTensorWords.map_id]

theorem comp_inclusion_toLinearMap (ε : 𝒜.Augmentation) :
    ε.toLinearMap ∘ₗ ε.inclusion.toLinearMap = 0 :=
  LinearMap.ext fun x ↦ (ε.mem_augmentationIdeal).mp x.property

theorem sub_inclusion_barMap_map_reducedPart_mem_degenerateWords (ε : 𝒜.Augmentation)
    (z : ReducedTensorWords R A) :
    z - ε.inclusion.barMap (ReducedTensorWords.map (R := R) ε.reducedPart z) ∈
      degenerateWords R A ε.unit := by
  rw [AInfinityStrictHom.barMap_def, ← LinearMap.comp_apply, ← ReducedTensorWords.map_comp]
  exact sub_map_mem_degenerateWords _ (fun a ↦ ⟨ε a, by simp [coe_reducedPart]⟩) z

theorem letter_sub_inclusion_barMap_map_reducedPart (ε : 𝒜.Augmentation)
    (z : ReducedTensorWords R A) :
    letter R A (z - ε.inclusion.barMap (ReducedTensorWords.map (R := R) ε.reducedPart z)) =
      ε (letter R A z) • ε.unit := by
  have hl := LinearMap.congr_fun
    (letter_comp_map (R := R) (ε.inclusion.toLinearMap ∘ₗ ε.reducedPart)) z
  rw [ReducedTensorWords.map_comp] at hl
  simp only [map_sub, AInfinityStrictHom.barMap_def, LinearMap.comp_apply] at hl ⊢
  rw [hl, ε.inclusion_toLinearMap, Submodule.subtype_apply, ε.coe_reducedPart, sub_sub_cancel]

@[simp]
theorem map_koszulTwist (ε : 𝒜.Augmentation) (q : ℤ) (x : A) :
    ε (𝒜.grading.koszulTwist q x) = ε x := by
  induction x using DirectSum.Decomposition.inductionOn 𝒜.grading.piece with
  | zero => simp
  | @homogeneous p x =>
    rw [𝒜.grading.koszulTwist_apply_of_mem x.2 q, map_smul]
    by_cases hp : p = 0
    · subst hp; simp
    · rw [ε.map_of_mem_ne_zero p _ x.2 hp, smul_zero]
  | add _ _ hx hy => simp [map_add, hx, hy]

theorem koszulTwist_mem_augmentationIdeal_iff (ε : 𝒜.Augmentation) (q : ℤ) (x : A) :
    𝒜.grading.koszulTwist q x ∈ ε.augmentationIdeal ↔ x ∈ ε.augmentationIdeal := by
  rw [mem_augmentationIdeal, mem_augmentationIdeal, ε.map_koszulTwist]

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
  have heq : ε'.inclusion.toLinearMap ∘ₗ
      (ε'.reducedAlgebra.taylor ∘ₗ coalgHom R (ε'.reducedPart ∘ₗ g.taylor)) =
      ε'.inclusion.toLinearMap ∘ₗ ((ε'.reducedPart ∘ₗ g.taylor) ∘ₗ 𝒜.barDifferential) := by
    rw [← LinearMap.comp_assoc, ← ε'.inclusion.taylor_comp_barMap, LinearMap.comp_assoc, hcoalg,
      g.taylor_comp_barMap, ← LinearMap.comp_assoc, hinc]
  exact LinearMap.ext fun w ↦ Subtype.val_injective (LinearMap.congr_fun heq w)

/-- **Universal property of the augmentation ideal**: `A∞` morphisms `A ⟶ ker ε'` correspond
bijectively to `A∞` morphisms `g : A ⟶ B` whose Taylor map takes values in `ker ε'`. -/
noncomputable def liftReducedHomEquiv (𝒜 : AInfinityAlgebra R A) (ε' : ℬ.Augmentation) :
    AInfinityHom 𝒜 ε'.reducedAlgebra ≃
      {g : AInfinityHom 𝒜 ℬ // ∀ w, g.taylor w ∈ ε'.augmentationIdeal} where
  toFun k := ⟨ε'.inclusion.toAInfinityHom.comp k, fun _ ↦ by simp⟩
  invFun g := AInfinityHom.ofTaylor (ε'.reducedPart ∘ₗ g.val.taylor)
    (by simpa only [add_zero] using
      ε'.isHomogeneous_reducedPart_shift_one.comp g.val.isHomogeneous_taylor)
    (liftReducedHom_component_eq ε' g.property)
  left_inv k := AInfinityHom.ext <| by
    rw [AInfinityHom.taylor_ofTaylor, AInfinityStrictHom.taylor_toAInfinityHom_comp,
      ← LinearMap.comp_assoc, ε'.reducedPart_comp_inclusion_toLinearMap, LinearMap.id_comp]
  right_inv g := Subtype.ext <| AInfinityHom.ext <| by
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

namespace AInfinityHom

variable {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B} {𝒞 : AInfinityAlgebra R C}

/-- A morphism of augmented `A∞` algebras is **augmented** when it is strictly unital, its linear
part intertwines the augmentations, and all higher components land in `ker ε'`. -/
structure IsAugmented (f : AInfinityHom 𝒜 ℬ) (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation) : Prop where
  /-- The morphism is strictly unital for the chosen strict units. -/
  isStrictlyUnital : f.IsStrictlyUnital ε.isStrictUnit ε'.isStrictUnit
  /-- The linear component intertwines the augmentations. -/
  map_augmentation : ε'.toLinearMap ∘ₗ f.linearPart = ε.toLinearMap
  /-- Every component above arity one lands in the target augmentation ideal. -/
  augmentation_component_eq_zero : ∀ {n : ℕ}, n ≠ 1 → ∀ x : Fin n → A, ε' (f.component n x) = 0

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
      subst hn1
      rw [of_tprod_eq_subword R hk, subword_one R A x hk, letter_ofLetter, ← f.linearPart_apply]
      exact LinearMap.congr_fun hf.map_augmentation (x 0)
    · have htwist : f.component n.1 (fun i ↦ 𝒜.grading.koszulTwist ((n.1 : ℤ) - 1 - i) (x i)) =
          f.taylor (of R A n (PiTensorProduct.tprod R x)) := by
        simp [component_apply f n.1 n.2, InternalGrading.koszulTwist_koszulTwist]
      rw [← htwist, of_tprod_eq_subword R n.2, letter_subword_of_ne_one R A x 0 hn1, map_zero]
      exact hf.augmentation_component_eq_zero hn1 _
  · rintro ⟨hsu, htaylor⟩
    refine ⟨hsu, LinearMap.ext fun a ↦ by
      simpa using LinearMap.congr_fun htaylor (ofLetter R A a), fun {n} hn x ↦ ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp
    · have hx := LinearMap.congr_fun htaylor (of R A ⟨n, hnpos⟩
        (PiTensorProduct.tprod R fun i ↦ 𝒜.grading.koszulTwist ((n : ℤ) - 1 - i) (x i)))
      simpa [component_apply f n hnpos, of_tprod_eq_subword R hnpos,
        letter_subword_of_ne_one R A _ 0 hn] using hx

@[simp]
theorem isAugmented_id (ε : 𝒜.Augmentation) : (AInfinityHom.id 𝒜).IsAugmented ε ε :=
  isAugmented_iff_taylor.2 ⟨isStrictlyUnital_id ε.isStrictUnit, by rw [taylor_id]⟩

theorem IsAugmented.comp {g : AInfinityHom ℬ 𝒞} {f : AInfinityHom 𝒜 ℬ}
    {ε : 𝒜.Augmentation} {ε' : ℬ.Augmentation} {ε'' : 𝒞.Augmentation}
    (hg : g.IsAugmented ε' ε'') (hf : f.IsAugmented ε ε') : (g.comp f).IsAugmented ε ε'' := by
  rw [isAugmented_iff_taylor] at hg hf ⊢
  exact ⟨hg.1.comp hf.1, by
    rw [taylor_comp, ← LinearMap.comp_assoc, hg.2, LinearMap.comp_assoc, ← f.taylor_def, hf.2]⟩

theorem IsStrict.isAugmented_iff {f : AInfinityHom 𝒜 ℬ} {ε : 𝒜.Augmentation}
    {ε' : ℬ.Augmentation} (hf : f.IsStrict) :
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

namespace DGAlgAugmentation

/-- An augmentation of a DG algebra induces an augmentation of its underlying `A∞` algebra. -/
noncomputable def toAInfinityAugmentation (e : DGAlgAugmentation hD) :
    hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.Augmentation where
  unit := 1
  isStrictUnit := hD.strictUnit_one
  toLinearMap := e.toGradedAlgHom.toAlgHom.toLinearMap
  map_unit := map_one e
  map_of_mem_ne_zero p x hx hp := by
    rw [IsNonUnitalDGAlgebra.toAInfinityAlgebra_grading,
      InternalGrading.ofDecomposition_piece] at hx
    exact (mem_trivialGrading_iff R R).mp (e.map_mem hx) |>.resolve_left hp
  map_binary x y := by rw [IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_two_apply]; exact map_mul e x y
  map_m_of_ne_two n hn0 hn2 x := by
    rcases n with _ | _ | _ | n
    · omega
    · rw [IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_one_apply]; exact e.map_d (x 0)
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
  ext x; simp [AInfinityAlgebra.Augmentation.mem_augmentationIdeal]

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

@[simp]
theorem isAugmented_toAInfinityHom_iff (φ : DGAlgHom hD hE)
    (eD : DGAlgAugmentation hD) (eE : DGAlgAugmentation hE) :
    φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.IsAugmented
        eD.toAInfinityAugmentation eE.toAInfinityAugmentation ↔ eE.comp φ = eD := by
  rw [(AInfinityHom.isStrict_toAInfinityHom _).isAugmented_iff]
  simp only [AInfinityStrictHom.linearPart_toAInfinityHom,
    DGAlgAugmentation.toAInfinityAugmentation_unit]
  refine ⟨fun h ↦ DGAlgHom.ext fun x ↦ by simpa using LinearMap.congr_fun h.2 x,
    fun h ↦ ⟨by simp, LinearMap.ext fun x ↦ by simpa using congrArg (· x) h⟩⟩

end DGAlgHom

end DG

namespace AInfinityHom.IsAugmented

variable {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B} {𝒞 : AInfinityAlgebra R C}
  {f : AInfinityHom 𝒜 ℬ} {ε : 𝒜.Augmentation} {ε' : ℬ.Augmentation}

private theorem taylor_comp_inclusion_mem (hf : f.IsAugmented ε ε')
    (w : ReducedTensorWords R ε.augmentationIdeal) :
    (f.comp ε.inclusion.toAInfinityHom).taylor w ∈ ε'.augmentationIdeal := by
  have hzero : ε'.toLinearMap ∘ₗ f.taylor ∘ₗ ε.inclusion.barMap = 0 := by
    rw [← LinearMap.comp_assoc, (isAugmented_iff_taylor.1 hf).2, LinearMap.comp_assoc,
      AInfinityStrictHom.barMap_def, letter_comp_map, ← LinearMap.comp_assoc,
      ε.comp_inclusion_toLinearMap, LinearMap.zero_comp]
  simpa [AInfinityAlgebra.Augmentation.mem_augmentationIdeal, AInfinityHom.taylor_comp] using
    LinearMap.congr_fun hzero w

/-- The nonunital `A∞` morphism `ker ε ⟶ ker ε'` induced on reduced augmentation ideals by a
strictly unital augmented `A∞` morphism `f : A ⟶ B`. -/
noncomputable def reducedHom (hf : f.IsAugmented ε ε') :
    AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra :=
  (AInfinityAlgebra.Augmentation.liftReducedHomEquiv ε.reducedAlgebra ε').symm
    ⟨f.comp ε.inclusion.toAInfinityHom, hf.taylor_comp_inclusion_mem⟩

@[simp]
theorem taylor_reducedHom (hf : f.IsAugmented ε ε') :
    hf.reducedHom.taylor = ε'.reducedPart ∘ₗ f.taylor ∘ₗ ε.inclusion.barMap := by
  simp [reducedHom, AInfinityHom.taylor_comp]

theorem inclusion_comp_reducedHom (hf : f.IsAugmented ε ε') :
    ε'.inclusion.toAInfinityHom.comp hf.reducedHom = f.comp ε.inclusion.toAInfinityHom :=
  congrArg Subtype.val
    ((AInfinityAlgebra.Augmentation.liftReducedHomEquiv _ _).apply_symm_apply _)

theorem inclusion_comp_reducedPart_taylor (hf : f.IsAugmented ε ε') :
    ε'.inclusion.toLinearMap ∘ₗ ε'.reducedPart ∘ₗ f.taylor ∘ₗ ε.inclusion.barMap =
      f.taylor ∘ₗ ε.inclusion.barMap := by
  have h := congrArg AInfinityHom.taylor hf.inclusion_comp_reducedHom
  rwa [AInfinityStrictHom.taylor_toAInfinityHom_comp, taylor_reducedHom,
    AInfinityHom.taylor_comp, AInfinityStrictHom.barMap_toAInfinityHom] at h

@[simp]
theorem reducedHom_id (ε : 𝒜.Augmentation) :
    (isAugmented_id ε).reducedHom = AInfinityHom.id ε.reducedAlgebra := by
  apply AInfinityHom.ext
  rw [taylor_reducedHom, taylor_id, taylor_id, AInfinityStrictHom.barMap_def, letter_comp_map,
    ← LinearMap.comp_assoc, ε.reducedPart_comp_inclusion_toLinearMap, LinearMap.id_comp]

theorem reducedHom_comp {g : AInfinityHom ℬ 𝒞} {ε'' : 𝒞.Augmentation}
    (hg : g.IsAugmented ε' ε'') (hf : f.IsAugmented ε ε') :
    (hg.comp hf).reducedHom = hg.reducedHom.comp hf.reducedHom := by
  refine AInfinityHom.ext (LinearMap.ext fun w ↦ ?_)
  have hbw := LinearMap.congr_fun (by
    simpa only [barMap_comp, AInfinityStrictHom.barMap_toAInfinityHom] using
      congrArg AInfinityHom.barMap hf.inclusion_comp_reducedHom) w
  simp only [taylor_reducedHom, taylor_comp, LinearMap.comp_apply] at hbw ⊢
  rw [hbw]

end AInfinityHom.IsAugmented

namespace AInfinityAlgebra.Augmentation

variable {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B} {𝒞 : AInfinityAlgebra R C}

private noncomputable def extendTaylor (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) : ReducedTensorWords R A →ₗ[R] B :=
  ε'.unitHom ∘ₗ ε.toLinearMap ∘ₗ letter R A +
    ε'.inclusion.toLinearMap ∘ₗ g.taylor ∘ₗ ReducedTensorWords.map (R := R) ε.reducedPart

private theorem extendTaylor_comp_inclusion_barMap (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    ε.extendTaylor ε' g ∘ₗ ε.inclusion.barMap = ε'.inclusion.toLinearMap ∘ₗ g.taylor := by
  refine LinearMap.ext fun z ↦ ?_
  have hl := LinearMap.congr_fun (letter_comp_map (R := R) ε.inclusion.toLinearMap) z
  have hm := LinearMap.congr_fun ε.map_reducedPart_comp_inclusion_barMap z
  simp only [AInfinityStrictHom.barMap_def, LinearMap.comp_apply] at hl hm
  simp only [extendTaylor, LinearMap.add_apply, LinearMap.comp_apply,
    AInfinityStrictHom.barMap_def]
  rw [hl, hm]
  simp [(ε.mem_augmentationIdeal).mp (letter _ _ z).property]

private theorem extendTaylor_of_mem_degenerateWords (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) {z : ReducedTensorWords R A}
    (hz : z ∈ degenerateWords R A ε.unit) :
    ε.extendTaylor ε' g z = ε (letter R A z) • ε'.unit := by
  simp [extendTaylor, LinearMap.mem_ker.mp
    (degenerateWords_le_ker_map ε.reducedPart ε.reducedPart_unit hz)]

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

private theorem extendTaylor_subword_of_mem_block (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) {k : ℕ} (x : Fin k → A)
    {j : Fin k} (hj : x j = ε.unit) {a b : ℕ} (hab : a + b ≤ k) (ha : a ≤ j.1)
    (hb : j.1 < a + b) :
    ε.extendTaylor ε' g (subword R x a b) = if b = 1 then ε'.unit else 0 := by
  by_cases hb1 : b = 1
  · subst hb1
    rw [ite_eq_left rfl, subword_one R A x (by omega),
      show x ⟨a, by omega⟩ = ε.unit from by rw [← hj]; exact congrArg x (Fin.ext (by simp; omega)),
      ε.extendTaylor_ofLetter_unit ε' g]
  · rw [ite_eq_right hb1, ε.extendTaylor_of_mem_degenerateWords ε' g
      (subword_mem_degenerateWords x ⟨j, ha, hb, hj⟩),
      letter_subword_of_ne_one R A x a hb1, map_zero, zero_smul]

private theorem extendTaylor_isHomogeneous (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    LinearMap.IsHomogeneous (ε.extendTaylor ε' g) (gradedPiece (𝒜.grading.shift 1))
      (ℬ.grading.shift 1).piece 0 := by
  refine (LinearMap.isHomogeneous_def.mpr fun p _ hz ↦ ?_).add ?_
  · have hl := (isHomogeneous_letter (𝒜.grading.shift 1)).map_mem hz
    rw [add_zero, InternalGrading.shift_piece] at hl ⊢
    by_cases hp : p + 1 = 0
    · rw [hp]; simp only [LinearMap.comp_apply, unitHom_apply]
      exact Submodule.smul_mem _ _ ε'.isStrictUnit.degree_zero
    · simp [ε.map_of_mem_ne_zero (p + 1) _ hl hp]
  · have h1 : LinearMap.IsHomogeneous
        (g.taylor ∘ₗ ReducedTensorWords.map (R := R) ε.reducedPart)
        (gradedPiece (𝒜.grading.shift 1)) (ε'.reducedAlgebra.grading.shift 1).piece 0 := by
      simpa only [add_zero] using g.isHomogeneous_taylor.comp
        (isHomogeneous_map _ _ ε.isHomogeneous_reducedPart_shift_one)
    simpa only [add_zero] using (ε'.inclusion.isHomogeneous_shift 1).comp h1

private theorem sum_taylor_prepend_prepend_extendTaylor_eq_zero
    (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) {n : ℕ} (x : Fin (n + 1) → A)
    (j : Fin (n + 1)) (hj : x j = ε.unit) {d : ℕ} (hd : d < n + 1) :
    ∑ c ∈ Finset.range (n + 1 - d),
      ℬ.taylor (prepend R B (ε.extendTaylor ε' g (subword R x 0 d))
        (prepend R B (ε.extendTaylor ε' g (subword R x d c))
          (coalgHom R (ε.extendTaylor ε' g) (subword R x (d + c) (n + 1 - d - c))))) = 0 := by
  have := j.isLt
  refine Finset.sum_eq_zero fun c hc ↦ ?_
  rw [Finset.mem_range] at hc
  rcases Nat.eq_zero_or_pos c with rfl | _
  · simp [subword_length_zero]
  by_cases hjd : j.1 < d
  · rw [ε.extendTaylor_subword_of_mem_block ε' g x hj (a := 0) (by omega) (by omega) (by omega)]
    split_ifs
    · exact ε'.isStrictUnit.taylor_prepend_prepend_eq_zero _ _ _ (Or.inl rfl)
    · simp
  · by_cases hjdc : j.1 < d + c
    · rw [ε.extendTaylor_subword_of_mem_block ε' g x hj (a := d) (by omega) (by omega) (by omega)]
      split_ifs
      · exact ε'.isStrictUnit.taylor_prepend_prepend_eq_zero _ _ _ (Or.inr (Or.inl rfl))
      · simp
    · exact ε'.isStrictUnit.taylor_prepend_prepend_eq_zero _ _ _ (Or.inr (Or.inr
        (coalgHom_subword_mem_degenerateWords _ (ε.extendTaylor_ofLetter_unit ε' g)
          (ε.extendTaylor_of_tprod_eq_zero ε' g) x (by omega) ⟨j, by omega, by omega, hj⟩)))

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
  rcases Nat.eq_zero_or_pos d with rfl | _
  · simp (disch := omega) [subword_length_zero]
  rw [coalgHom_subword _ x d (n + 1 - d), map_add, map_add, map_sum, map_sum,
    ε.sum_taylor_prepend_prepend_extendTaylor_eq_zero ε' g x j hj hd, add_zero]
  by_cases hjd : j.1 < d
  · rw [ε.extendTaylor_subword_of_mem_block ε' g x hj (a := 0) (by omega) (by omega) (by omega)]
    by_cases hd1 : d = 1
    · subst hd1
      rw [ite_eq_left rfl, Nat.add_sub_cancel, prepend_ofLetter,
        ε'.isStrictUnit.taylor_of_two_unit_left]
      simp (disch := omega) only [true_and, ite_eq_left, ite_eq_right, add_zero]
    · rw [ite_eq_right hd1, map_zero, LinearMap.zero_apply, map_zero]
      simp (disch := omega) only [ite_eq_right, add_zero]
  · rw [ε.extendTaylor_subword_of_mem_block ε' g x hj (a := d) (by omega) (by omega) (by omega)]
    by_cases hdn : d = n
    · subst hdn
      rw [Nat.add_sub_cancel_left, ite_eq_left rfl, prepend_ofLetter,
        ε'.isStrictUnit.taylor_of_two_unit_right]
      simp (disch := omega) only [true_and, ite_eq_right, ite_eq_left, zero_add]
    · rw [ite_eq_right (by omega : n + 1 - d ≠ 1), map_zero, map_zero, map_zero]
      simp (disch := omega) only [ite_eq_right, add_zero]

private theorem taylor_coalgHom_extendTaylor_of_tprod (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) {n : ℕ} (x : Fin (n + 1) → A)
    (j : Fin (n + 1)) (hj : x j = ε.unit) :
    ℬ.taylor (coalgHom R (ε.extendTaylor ε' g)
        (of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R x))) =
      (if j.1 = 0 ∧ 0 < n then ε.extendTaylor ε' g (subword R x 1 n) else 0) +
        (if j.1 = n ∧ 0 < n then
          ℬ.grading.koszulTwist 1 (ε.extendTaylor ε' g (subword R x 0 n)) else 0) := by
  have hjn := j.isLt
  rw [of_tprod_eq_subword R (Nat.zero_lt_succ n), coalgHom_subword, map_add, map_sum,
    ε.extendTaylor_subword_of_mem_block ε' g x hj (a := 0) (by omega) (by omega) (by omega)]
  have hsingle : ℬ.taylor (ofLetter R B (if n + 1 = 1 then ε'.unit else 0)) = 0 := by
    split_ifs
    · rw [ofLetter_eq_of_tprod]
      exact ε'.isStrictUnit.taylor_of_tprod_eq_zero ⟨1, Nat.one_pos⟩ (by decide) _ ⟨0, rfl⟩
    · simp
  rw [hsingle, zero_add]
  simp only [zero_add]
  rw [Finset.sum_congr rfl (ε.taylor_prepend_coalgHom_extendTaylor ε' g x j hj)]
  simp only [Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq', Finset.mem_range]
  congr 1 <;> split_ifs <;> first | rfl | omega

private theorem degenerateWords_le_ker_extendTaylor_component
    (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    degenerateWords R A ε.unit ≤
      LinearMap.ker (ℬ.taylor ∘ₗ coalgHom R (ε.extendTaylor ε' g) -
        ε.extendTaylor ε' g ∘ₗ 𝒜.barDifferential) := by
  rw [degenerateWords_le_iff_of_mem_piece _ ε.isStrictUnit.mem_shift_one_piece]
  rintro ⟨_ | n, hN⟩ x 𝒟 j hx hj _
  · omega
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  simp only [LinearMap.comp_apply]
  rw [ε.taylor_coalgHom_extendTaylor_of_tprod ε' g x j hj,
    ε.isStrictUnit.apply_barDifferential_of_tprod_of_higher_eq_zero
      (ε.extendTaylor_of_tprod_eq_zero ε' g) x 𝒟 hx j hj]
  have hhom : LinearMap.IsHomogeneous (ε.extendTaylor ε' g)
      (ReducedTensorWords.grading (𝒜.grading.shift 1)).piece (ℬ.grading.shift 1).piece 0 := by
    simpa only [ReducedTensorWords.grading_piece] using ε.extendTaylor_isHomogeneous ε' g
  have hkt : ε.extendTaylor ε' g
      ((ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 (subword R x 0 n)) =
      -ℬ.grading.koszulTwist 1 (ε.extendTaylor ε' g (subword R x 0 n)) := by
    simpa [InternalGrading.koszulTwist_one_shift_one] using
      (hhom.koszulTwist_apply 1 (subword R x 0 n)).symm
  rw [hkt, sub_eq_add_neg]
  congr 1
  split_ifs <;> simp

private theorem extendTaylor_component_eq (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    ℬ.taylor ∘ₗ coalgHom R (ε.extendTaylor ε' g) =
      ε.extendTaylor ε' g ∘ₗ 𝒜.barDifferential := by
  let t := ε.extendTaylor ε' g
  have hcoalg : coalgHom R t ∘ₗ ε.inclusion.barMap = ε'.inclusion.barMap ∘ₗ g.barMap := by
    rw [AInfinityStrictHom.barMap_def,
      ((isCoalgHom_coalgHom t).comp (isCoalgHom_map _)).eq_coalgHom,
      ← LinearMap.comp_assoc, letter_comp_coalgHom, ← AInfinityStrictHom.barMap_def,
      ε.extendTaylor_comp_inclusion_barMap ε' g, AInfinityStrictHom.barMap_def,
      ← map_comp_coalgHom, ← g.barMap_eq_coalgHom]
  have hred : (ℬ.taylor ∘ₗ coalgHom R t) ∘ₗ ε.inclusion.barMap =
      (t ∘ₗ 𝒜.barDifferential) ∘ₗ ε.inclusion.barMap := by
    dsimp only [t] at hcoalg ⊢
    rw [LinearMap.comp_assoc, hcoalg, ← LinearMap.comp_assoc, ε'.inclusion.taylor_comp_barMap,
      LinearMap.comp_assoc, g.taylor_comp_barMap, LinearMap.comp_assoc,
      ε.inclusion.barDifferential_comp_barMap, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc,
      ε.extendTaylor_comp_inclusion_barMap ε' g]
  refine LinearMap.ext fun z ↦ ?_
  let r := ReducedTensorWords.map (R := R) ε.reducedPart z
  have hsub := sub_eq_zero.mp <| LinearMap.mem_ker.mp <|
    ε.degenerateWords_le_ker_extendTaylor_component ε' g
      (ε.sub_inclusion_barMap_map_reducedPart_mem_degenerateWords z)
  have hredr := LinearMap.congr_fun hred r
  dsimp only [t, r, LinearMap.comp_apply] at hsub hredr ⊢
  simpa only [← map_add, sub_add_cancel] using congrArg₂ (· + ·) hsub hredr

/-- Extend any nonunital `A∞` morphism `g : ker ε ⟶ ker ε'` between reduced augmentation ideals to
a strictly unital augmented `A∞` morphism `A ⟶ B`. -/
noncomputable def extendReducedHom (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) : AInfinityHom 𝒜 ℬ :=
  AInfinityHom.ofTaylor (ε.extendTaylor ε' g) (ε.extendTaylor_isHomogeneous ε' g)
    (ε.extendTaylor_component_eq ε' g)

theorem isAugmented_extendReducedHom (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    (ε.extendReducedHom ε' g).IsAugmented ε ε' := by
  rw [AInfinityHom.isAugmented_iff_taylor]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [AInfinityHom.linearPart_apply, extendReducedHom, AInfinityHom.taylor_ofTaylor]
    exact ε.extendTaylor_ofLetter_unit ε' g
  · intro n hn x ⟨i, hi⟩
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp
    · rw [AInfinityHom.component_apply _ n hnpos, extendReducedHom, AInfinityHom.taylor_ofTaylor]
      exact ε.extendTaylor_of_tprod_eq_zero ε' g ⟨n, hnpos⟩ hn _
        ⟨i, by rw [hi, 𝒜.grading.koszulTwist_apply_of_mem_zero ε.isStrictUnit.degree_zero]⟩
  · rw [extendReducedHom, AInfinityHom.taylor_ofTaylor]
    exact LinearMap.ext fun _ ↦ by
      simp [extendTaylor, (ε'.mem_augmentationIdeal).mp (g.taylor _).property]

theorem extendReducedHom_linearPart_unit (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    (ε.extendReducedHom ε' g).linearPart ε.unit = ε'.unit :=
  (ε.isAugmented_extendReducedHom ε' g).isStrictlyUnital.map_unit

@[simp]
theorem extendReducedHom_comp_inclusion (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    (ε.extendReducedHom ε' g).comp ε.inclusion.toAInfinityHom =
      ε'.inclusion.toAInfinityHom.comp g :=
  AInfinityHom.ext <| by rw [AInfinityHom.taylor_comp, extendReducedHom,
    AInfinityHom.taylor_ofTaylor, AInfinityStrictHom.barMap_toAInfinityHom,
    ε.extendTaylor_comp_inclusion_barMap ε' g, AInfinityStrictHom.taylor_toAInfinityHom_comp]

@[simp]
theorem reducedHom_extendReducedHom (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    (ε.isAugmented_extendReducedHom ε' g).reducedHom = g :=
  AInfinityHom.ext <| by rw [AInfinityHom.IsAugmented.taylor_reducedHom, extendReducedHom,
    AInfinityHom.taylor_ofTaylor, ε.extendTaylor_comp_inclusion_barMap ε' g,
    ← LinearMap.comp_assoc, ε'.reducedPart_comp_inclusion_toLinearMap, LinearMap.id_comp]

@[simp]
theorem extendReducedHom_reducedHom {ε : 𝒜.Augmentation} {ε' : ℬ.Augmentation}
    {f : AInfinityHom 𝒜 ℬ} (hf : f.IsAugmented ε ε') :
    ε.extendReducedHom ε' hf.reducedHom = f := by
  refine AInfinityHom.ext (LinearMap.ext fun z ↦ ?_)
  rw [extendReducedHom, AInfinityHom.taylor_ofTaylor]
  let r := ReducedTensorWords.map (R := R) ε.reducedPart z
  have hw := ε.sub_inclusion_barMap_map_reducedPart_mem_degenerateWords z
  have htw : ε.extendTaylor ε' hf.reducedHom (z - ε.inclusion.barMap r) =
      f.taylor (z - ε.inclusion.barMap r) := by
    rw [ε.extendTaylor_of_mem_degenerateWords ε' hf.reducedHom hw,
      hf.isStrictlyUnital.taylor_eq_linearPart_letter hw,
      ε.letter_sub_inclusion_barMap_map_reducedPart z, map_smul, map_smul, ε.map_unit,
      hf.isStrictlyUnital.map_unit, smul_eq_mul, mul_one]
  have h1 := LinearMap.congr_fun (ε.extendTaylor_comp_inclusion_barMap ε' hf.reducedHom) r
  have h2 := LinearMap.congr_fun hf.inclusion_comp_reducedPart_taylor r
  simp only [LinearMap.comp_apply, AInfinityHom.IsAugmented.taylor_reducedHom] at h1 h2
  simpa only [← map_add, sub_add_cancel] using congrArg₂ (· + ·) htw (h1.trans h2)

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

theorem extendReducedHom_comp (ε : 𝒜.Augmentation) (ε' : ℬ.Augmentation) (ε'' : 𝒞.Augmentation)
    (h : AInfinityHom ε'.reducedAlgebra ε''.reducedAlgebra)
    (g : AInfinityHom ε.reducedAlgebra ε'.reducedAlgebra) :
    ε.extendReducedHom ε'' (h.comp g) =
      (ε'.extendReducedHom ε'' h).comp (ε.extendReducedHom ε' g) := by
  rw [← extendReducedHom_reducedHom ((ε'.isAugmented_extendReducedHom ε'' h).comp
    (ε.isAugmented_extendReducedHom ε' g)), (ε'.isAugmented_extendReducedHom ε'' h).reducedHom_comp
    (ε.isAugmented_extendReducedHom ε' g), reducedHom_extendReducedHom, reducedHom_extendReducedHom]

theorem _root_.TauCeti.AInfinityHom.IsAugmented.ext_comp_inclusion
    {ε : 𝒜.Augmentation} {ε' : ℬ.Augmentation} {f₁ f₂ : AInfinityHom 𝒜 ℬ}
    (hf₁ : f₁.IsAugmented ε ε') (hf₂ : f₂.IsAugmented ε ε')
    (h : f₁.comp ε.inclusion.toAInfinityHom = f₂.comp ε.inclusion.toAInfinityHom) : f₁ = f₂ := by
  rw [← extendReducedHom_reducedHom hf₁, ← extendReducedHom_reducedHom hf₂,
    show hf₁.reducedHom = hf₂.reducedHom from congrArg (liftReducedHomEquiv _ _).symm
      (Subtype.ext h)]

end AInfinityAlgebra.Augmentation

end TauCeti
