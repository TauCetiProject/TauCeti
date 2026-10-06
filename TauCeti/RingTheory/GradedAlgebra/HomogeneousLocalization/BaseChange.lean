/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import TauCeti.RingTheory.Localization.TensorProduct
public import Mathlib.RingTheory.Flat.Basic

/-!
# Base change of homogeneous affine charts

Homogeneous localization away from a homogeneous element commutes with flat extension
of the coefficient ring. These are the coordinate rings of the standard affine charts
of a projective spectrum, so the comparison is the affine input to projective base change.
In particular, extension from a field satisfies the flatness hypothesis automatically.

The comparison uses Mathlib's ordinary-localization base-change equivalence
`IsLocalization.Away.tensorProductEquivTMulRight` and its grading on a scalar extension.

## References

* [The Stacks Project, Lemma 27.11.6](https://stacks.math.columbia.edu/tag/01N2),
  base change for projective spectra, proved on standard affine opens.
-/

public section

open scoped TensorProduct

namespace HomogeneousLocalization

variable {ι R A : Type*} [AddCommMonoid ι] [DecidableEq ι]
  [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

section BaseChange

variable (S : Type*) [CommRing S] [Algebra R S] (f : A)

/-- The canonical graded coefficient map induces a map on homogeneous charts. -/
noncomputable def Away.baseChangeMap :
    Away 𝒜 f →+* Away (fun i ↦ (𝒜 i).baseChange S) (1 ⊗ₜ[R] f) :=
  Away.map (𝒜 := 𝒜) (ℬ := fun i ↦ (𝒜 i).baseChange S) {
    toFun a := (1 : S) ⊗ₜ[R] a
    map_one' := rfl
    map_mul' a b := by simp [Algebra.TensorProduct.tmul_mul_tmul]
    map_zero' := by simp
    map_add' a b := TensorProduct.tmul_add _ _ _
    map_mem := fun hx ↦ Submodule.tmul_mem_baseChange_of_mem 1 hx } f

/-- Extension of a homogeneous fraction extends its numerator and denominator. -/
@[simp]
theorem Away.baseChangeMap_mk {d : ι} (hf : f ∈ 𝒜 d) (n : ℕ) (a : A)
    (ha : a ∈ 𝒜 (n • d)) :
    Away.baseChangeMap 𝒜 S f (Away.mk 𝒜 hf n a ha) =
      Away.mk (fun i ↦ (𝒜 i).baseChange S)
        (Submodule.tmul_mem_baseChange_of_mem 1 hf) n (1 ⊗ₜ[R] a)
        (Submodule.tmul_mem_baseChange_of_mem 1 ha) := by
  dsimp only [Away.baseChangeMap]
  exact Away.map_mk _ f hf n a ha

/-- Coefficient extension on a chart respects the structure maps of the base rings. -/
@[simp]
theorem Away.baseChangeMap_algebraMap (r : R) :
    Away.baseChangeMap 𝒜 S f (algebraMap R (Away 𝒜 f) r) =
      algebraMap S _ (algebraMap R S r) := by
  apply val_injective
  simp only [Away.baseChangeMap, Away.map]
  rw [val_map, val_algebraMap, val_algebraMap]
  rw [IsScalarTower.algebraMap_apply R A (Localization.Away f)]
  -- The stored graded map and its ring-hom coercion have the same coefficient map.
  erw [IsLocalization.map_eq]
  -- Reduce only the explicitly constructed graded inclusion, before coefficient functoriality.
  change algebraMap (S ⊗[R] A) (Localization.Away (1 ⊗ₜ[R] f))
      (1 ⊗ₜ[R] algebraMap R A r) =
    algebraMap S (Localization.Away (1 ⊗ₜ[R] f)) (algebraMap R S r)
  have hr : (1 : S) ⊗ₜ[R] algebraMap R A r = algebraMap R (S ⊗[R] A) r :=
    (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).commutes r
  rw [hr, ← IsScalarTower.algebraMap_apply R (S ⊗[R] A),
    ← IsScalarTower.algebraMap_apply R S]

/-- Forgetting the grading identifies coefficient extension with ordinary localization. -/
theorem Away.val_baseChangeMap (z : Away 𝒜 f) :
    (Away.baseChangeMap 𝒜 S f z).val =
      Localization.awayMap
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom f z.val := by
  simp only [Away.baseChangeMap, Away.map, val_map]
  rfl

/-- The canonical comparison from the scalar extension of a homogeneous affine chart to
the corresponding chart of the scalar-extended graded algebra. -/
noncomputable def Away.baseChangeHom :
    S ⊗[R] Away 𝒜 f →ₐ[S]
      Away (fun i ↦ (𝒜 i).baseChange S) (1 ⊗ₜ[R] f) := by
  letI := Algebra.compHom
    (Away (fun i ↦ (𝒜 i).baseChange S) (1 ⊗ₜ[R] f)) (algebraMap R S)
  letI : IsScalarTower R S
      (Away (fun i ↦ (𝒜 i).baseChange S) (1 ⊗ₜ[R] f)) := IsScalarTower.of_compHom ..
  exact AlgHom.liftEquiv R S _ _
    { Away.baseChangeMap 𝒜 S f with commutes' := Away.baseChangeMap_algebraMap 𝒜 S f }

/-- On pure tensors, the comparison multiplies by the extended coefficient. -/
@[simp]
theorem Away.baseChangeHom_tmul (s : S) (z : Away 𝒜 f) :
    Away.baseChangeHom 𝒜 S f (s ⊗ₜ[R] z) = s • Away.baseChangeMap 𝒜 S f z := (rfl)

/-- The scalar-extended fraction `s ⊗ (a/fⁿ)` has numerator `s ⊗ a`. -/
theorem Away.baseChangeHom_tmul_mk {d : ι} (hf : f ∈ 𝒜 d) (n : ℕ) (s : S) (a : A)
    (ha : a ∈ 𝒜 (n • d)) :
    Away.baseChangeHom 𝒜 S f (s ⊗ₜ[R] Away.mk 𝒜 hf n a ha) =
      Away.mk (fun i ↦ (𝒜 i).baseChange S)
        (Submodule.tmul_mem_baseChange_of_mem 1 hf) n (s ⊗ₜ[R] a)
        (Submodule.tmul_mem_baseChange_of_mem s ha) := by
  rw [Away.baseChangeHom_tmul, Away.baseChangeMap_mk]
  apply val_injective
  simp only [val_smul, Away.val_mk]
  rw [Localization.smul_mk, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Every homogeneous fraction after scalar extension comes from the scalar extension of
the original chart. No flatness is required for surjectivity. -/
theorem Away.baseChangeHom_surjective {d : ι} (hf : f ∈ 𝒜 d) :
    Function.Surjective (Away.baseChangeHom 𝒜 S f) := by
  intro z
  have hf' := Submodule.tmul_mem_baseChange_of_mem (A := S) 1 hf
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (fun i ↦ (𝒜 i).baseChange S) hf' z
  obtain ⟨x, hx⟩ := (𝒜 (n • d)).toBaseChange_surjective S ⟨a, ha⟩
  let F := (Away.mkLinearMap hf n).baseChange S
  refine ⟨F x, ?_⟩
  have h : ∀ y, Away.baseChangeHom 𝒜 S f (F y) =
      Away.mkLinearMap (𝒜 := fun i ↦ (𝒜 i).baseChange S) hf' n ((𝒜 (n • d)).toBaseChange S y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul s b =>
      simp only [F, LinearMap.baseChange_tmul, Away.mkLinearMap_apply,
        Away.baseChangeHom_tmul_mk, Submodule.coe_toBaseChange_tmul]
  rw [h, hx, Away.mkLinearMap_apply]

/-- The homogeneous comparison agrees with ordinary-localization base change after the
canonical embeddings into ordinary localizations. -/
theorem Away.val_baseChangeHom (z : S ⊗[R] Away 𝒜 f) :
    (Away.baseChangeHom 𝒜 S f z).val =
      IsLocalization.Away.tensorProductEquivTMulRight R S f (Localization.Away f)
        ((IsScalarTower.toAlgHom R (Away 𝒜 f) (Localization.Away f)).toLinearMap.baseChange
          S z) := by
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ h₁ h₂ => simp only [map_add, val_add, h₁, h₂]
  | tmul s z =>
    rw [Away.baseChangeHom_tmul, val_smul, Away.val_baseChangeMap,
      LinearMap.baseChange_tmul, AlgHom.toLinearMap_apply, IsScalarTower.toAlgHom_apply,
      algebraMap_apply]
    rw [← IsLocalization.Away.tensorProductEquivTMulRight_one_tmul S f
      (Localization.Away f) z.val,
      ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Flat coefficient extension makes the homogeneous chart comparison injective. -/
theorem Away.baseChangeHom_injective [Module.Flat R S] :
    Function.Injective (Away.baseChangeHom 𝒜 S f) := by
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := S)
    (IsScalarTower.toAlgHom R (Away 𝒜 f) (Localization.Away f)).toLinearMap (val_injective _)
  intro x y hxy
  apply h
  apply (IsLocalization.Away.tensorProductEquivTMulRight R S f
    (Localization.Away f)).injective
  have hv := congrArg val hxy
  rw [Away.val_baseChangeHom, Away.val_baseChangeHom] at hv
  exact hv

/-- Homogeneous localization away from a homogeneous element commutes with flat extension
of the coefficient ring. -/
noncomputable def Away.baseChangeEquiv [Module.Flat R S] {d : ι} (hf : f ∈ 𝒜 d) :
    S ⊗[R] Away 𝒜 f ≃ₐ[S]
      Away (fun i ↦ (𝒜 i).baseChange S) (1 ⊗ₜ[R] f) :=
  AlgEquiv.ofBijective (Away.baseChangeHom 𝒜 S f)
    ⟨Away.baseChangeHom_injective 𝒜 S f, Away.baseChangeHom_surjective 𝒜 S f hf⟩

/-- The chart isomorphism has the canonical comparison as its underlying map. -/
@[simp]
theorem Away.baseChangeEquiv_apply [Module.Flat R S] {d : ι} (hf : f ∈ 𝒜 d)
    (z : S ⊗[R] Away 𝒜 f) :
    Away.baseChangeEquiv 𝒜 S f hf z = Away.baseChangeHom 𝒜 S f z := (rfl)

/-- The inverse chart isomorphism recovers scalar-extended homogeneous fractions. -/
@[simp]
theorem Away.baseChangeEquiv_symm_mk [Module.Flat R S] {d : ι} (hf : f ∈ 𝒜 d)
    (n : ℕ) (s : S) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    (Away.baseChangeEquiv 𝒜 S f hf).symm
      (Away.mk (fun i ↦ (𝒜 i).baseChange S)
        (Submodule.tmul_mem_baseChange_of_mem 1 hf) n (s ⊗ₜ[R] a)
        (Submodule.tmul_mem_baseChange_of_mem s ha)) =
      s ⊗ₜ[R] Away.mk 𝒜 hf n a ha := by
  apply (Away.baseChangeEquiv 𝒜 S f hf).injective
  simp only [AlgEquiv.apply_symm_apply, Away.baseChangeEquiv_apply,
    Away.baseChangeHom_tmul_mk]

end BaseChange

end HomogeneousLocalization
