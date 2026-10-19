/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Maps
public import TauCeti.RingTheory.Localization.TensorProduct

/-!
# Base change of homogeneous affine charts

Homogeneous localization away from a homogeneous element commutes with arbitrary extension
of the coefficient ring. These are the coordinate rings of the standard affine charts
of a projective spectrum, so the comparison is the affine input to projective base change.

The proof puts a finite sum of homogeneous fractions over a common denominator. Injectivity
then follows from the direct-sum decomposition of a graded algebra after scalar extension.

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

/-- The chart coefficient map is the homogeneous-localization map of graded coefficient
inclusion. -/
theorem Away.baseChangeMap_eq_map :
    Away.baseChangeMap 𝒜 S f = Away.map (TauCeti.GradedAlgebra.baseChangeMap S 𝒜) f := by
  rw [Away.baseChangeMap]
  congr 1

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

/-- The chart comparison sends a scalar-extended fixed-denominator numerator to the same
fixed-denominator numerator after scalar extension. -/
private theorem Away.baseChangeHom_mkLinearMap_baseChange {f : A} {d : ι} (hf : f ∈ 𝒜 d)
    (n : ℕ) (a : S ⊗[R] 𝒜 (n • d)) :
    Away.baseChangeHom 𝒜 S f ((Away.mkLinearMap hf n).baseChange S a) =
      Away.mkLinearMap (Submodule.tmul_mem_baseChange_of_mem 1 hf) n
        ((𝒜 (n • d)).toBaseChange S a) := by
  induction a using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s a =>
      simp only [LinearMap.baseChange_tmul, Away.mkLinearMap_apply,
        Away.baseChangeHom_tmul_mk, Submodule.coe_toBaseChange_tmul]

/-- Every homogeneous fraction after scalar extension comes from the scalar extension of
the original chart. No flatness is required for surjectivity. -/
theorem Away.baseChangeHom_surjective {d : ι} (hf : f ∈ 𝒜 d) :
    Function.Surjective (Away.baseChangeHom 𝒜 S f) := by
  intro z
  have hf' := Submodule.tmul_mem_baseChange_of_mem (A := S) 1 hf
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (fun i ↦ (𝒜 i).baseChange S) hf' z
  obtain ⟨x, hx⟩ := (𝒜 (n • d)).toBaseChange_surjective S ⟨a, ha⟩
  refine ⟨(Away.mkLinearMap hf n).baseChange S x, ?_⟩
  rw [Away.baseChangeHom_mkLinearMap_baseChange, hx, Away.mkLinearMap_apply]

/-- Raising a numerator commutes with scalar extension and does not change the resulting
homogeneous fraction. -/
private theorem Away.mkLinearMap_baseChange_promoteNumerator {f : A} {d : ι}
    (hf : f ∈ 𝒜 d) (n N : ℕ) (hnN : n ≤ N) (a : S ⊗[R] 𝒜 (n • d)) :
    (Away.mkLinearMap hf N).baseChange S
        ((Away.promoteNumerator hf n N hnN).baseChange S a) =
      (Away.mkLinearMap hf n).baseChange S a := by
  induction a using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s a =>
      simp only [LinearMap.baseChange_tmul, Away.mkLinearMap_promoteNumerator]

/-- Every element of a scalar-extended homogeneous chart can be written with one homogeneous
denominator. -/
private theorem Away.exists_eq_mkLinearMap_baseChange {f : A} {d : ι} (hf : f ∈ 𝒜 d)
    (z : S ⊗[R] Away 𝒜 f) :
    ∃ (n : ℕ) (a : S ⊗[R] 𝒜 (n • d)),
      (Away.mkLinearMap hf n).baseChange S a = z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨m, b, hb⟩ := hy
      let N := n + m
      let a' := (Away.promoteNumerator hf n N (Nat.le_add_right n m)).baseChange S a
      let b' := (Away.promoteNumerator hf m N (Nat.le_add_left m n)).baseChange S b
      refine ⟨N, a' + b', ?_⟩
      simp only [map_add, a', b', Away.mkLinearMap_baseChange_promoteNumerator]
      rw [ha, hb]
  | tmul s x =>
      obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf x
      refine ⟨n, s ⊗ₜ[R] (⟨a, ha⟩ : 𝒜 (n • d)), ?_⟩
      rw [LinearMap.baseChange_tmul, Away.mkLinearMap_apply]

/-- Multiplication by an added denominator commutes with the inclusion of a base-changed
homogeneous component into the scalar-extended algebra. -/
private theorem Away.coe_toBaseChange_promoteNumerator {f : A} {d : ι} (hf : f ∈ 𝒜 d)
    (n N : ℕ) (hnN : n ≤ N) (a : S ⊗[R] 𝒜 (n • d)) :
    ((𝒜 (N • d)).toBaseChange S
        ((Away.promoteNumerator hf n N hnN).baseChange S a) : S ⊗[R] A) =
      (1 ⊗ₜ[R] f) ^ (N - n) * ((𝒜 (n • d)).toBaseChange S a : S ⊗[R] A) := by
  induction a using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Submodule.coe_add, mul_add, hx, hy]
  | tmul s a =>
      simp only [LinearMap.baseChange_tmul, Away.coe_promoteNumerator,
        Submodule.coe_toBaseChange_tmul]
      simp only [Algebra.TensorProduct.tmul_pow, one_pow,
        Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
      -- The scalar-extension constructors retain a displayed coercion from the component.
      change s ⊗ₜ[R] ((a : A) * f ^ (N - n)) =
        (s * 1) ⊗ₜ[R] ((a : A) * f ^ (N - n))
      rw [mul_one]

/-- The homogeneous chart comparison is injective for every coefficient extension. -/
theorem Away.baseChangeHom_injective {d : ι} (hf : f ∈ 𝒜 d) :
    Function.Injective (Away.baseChangeHom 𝒜 S f) := by
  intro x y hxy
  apply sub_eq_zero.mp
  obtain ⟨n, a, ha⟩ := Away.exists_eq_mkLinearMap_baseChange 𝒜 S hf (x - y)
  have hmap : Away.baseChangeHom 𝒜 S f
      ((Away.mkLinearMap hf n).baseChange S a) = 0 := by
    rw [ha, map_sub, hxy, sub_self]
  rw [Away.baseChangeHom_mkLinearMap_baseChange] at hmap
  have hval := congrArg HomogeneousLocalization.val hmap
  simp only [Away.mkLinearMap_apply, Away.val_mk, val_zero] at hval
  rw [Localization.mk_eq_mk'] at hval
  obtain ⟨c, hc⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hval
  obtain ⟨k, hk⟩ := c.property
  rw [← hk] at hc
  let N := n + k
  let a' := (Away.promoteNumerator hf n N (Nat.le_add_right n k)).baseChange S a
  have ha' : a' = 0 := by
    apply DirectSum.toBaseChange_injective 𝒜 (N • d)
    apply Subtype.ext
    have hcoe : ((𝒜 (N • d)).toBaseChange S a' : S ⊗[R] A) = 0 := by
      dsimp only [a']
      rw [Away.coe_toBaseChange_promoteNumerator, Nat.add_sub_cancel_left]
      exact hc
    simpa only [map_zero, Submodule.coe_zero] using hcoe
  calc
    x - y = (Away.mkLinearMap hf n).baseChange S a := ha.symm
    _ = (Away.mkLinearMap hf N).baseChange S a' :=
      (Away.mkLinearMap_baseChange_promoteNumerator 𝒜 S hf n N
        (Nat.le_add_right n k) a).symm
    _ = 0 := by rw [ha', map_zero]

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

/-- Homogeneous localization away from a homogeneous element commutes with arbitrary extension
of the coefficient ring. -/
noncomputable def Away.baseChangeEquiv {d : ι} (hf : f ∈ 𝒜 d) :
    S ⊗[R] Away 𝒜 f ≃ₐ[S]
      Away (fun i ↦ (𝒜 i).baseChange S) (1 ⊗ₜ[R] f) :=
  AlgEquiv.ofBijective (Away.baseChangeHom 𝒜 S f)
    ⟨Away.baseChangeHom_injective 𝒜 S f hf, Away.baseChangeHom_surjective 𝒜 S f hf⟩

/-- The chart isomorphism has the canonical comparison as its underlying map. -/
@[simp]
theorem Away.baseChangeEquiv_apply {d : ι} (hf : f ∈ 𝒜 d)
    (z : S ⊗[R] Away 𝒜 f) :
    Away.baseChangeEquiv 𝒜 S f hf z = Away.baseChangeHom 𝒜 S f z := (rfl)

/-- The inverse chart isomorphism recovers scalar-extended homogeneous fractions. -/
@[simp]
theorem Away.baseChangeEquiv_symm_mk {d : ι} (hf : f ∈ 𝒜 d)
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
