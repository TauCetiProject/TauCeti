/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Abelian
public import TauCeti.Algebra.Coalgebra.Comodule.Cofree.Adjunction
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The augmented cofree resolution of a comodule

For a right comodule `M` over a coalgebra `C`, the augmented cofree resolution has terms
`M → M ⊗ C → (M ⊗ C) ⊗ C → ⋯`. The augmentation is the coaction. Its differential
alternately applies the coaction to `M` and the comultiplication to each coalgebra factor.
Every differential is a comodule morphism for the cofree coaction on the last factor.

The underlying module sequence is split exact: the contracting homotopy applies the counit
to the last factor, with the alternating sign. Thus no flatness or injectivity assumption on
the coefficient module is necessary. If `C` is flat, this gives an exact augmented complex
in the abelian category of comodules. Its terms are cofree, and need not be injective.
This resolution is used to compute derived invariants for coordinate Hopf algebras.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, Part I, §§4.14–4.16.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.ComoduleCat

universe u v w

variable (R : Type u) (C : Type v) [CommRing R]
  [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable (M : ComoduleCat.{u, v, max v w} R C)

attribute [local instance] Comodule.cofree

/-- The augmented cofree terms: term zero is `M`, and each subsequent term is cofree on
the underlying module of the previous term. -/
-- The recursive carrier must reduce to a tensor product in the types of the differential
-- and counit maps, just as for the Hochschild cochain modules.
@[expose, reducible]
noncomputable def cofreeResolutionTerm : ℕ → ComoduleCat.{u, v, max v w} R C
  | 0 => M
  | n + 1 => cofree R C (cofreeResolutionTerm n)

/-- The augmented differential, with the coaction first and alternating comultiplications.
The degree-zero map is the augmentation. -/
noncomputable def cofreeResolutionD : (n : ℕ) →
    (cofreeResolutionTerm R C M n ⟶ cofreeResolutionTerm R C M (n + 1))
  | 0 => Comodule.Hom.cofreeUnit M
  | n + 1 => Comodule.Hom.cofreeMap (cofreeResolutionD n).toLinearMap +
      ((-1 : R) ^ (n + 1)) • Comodule.Hom.cofreeUnit (cofreeResolutionTerm R C M (n + 1))

/-- The augmentation is the original coaction. -/
@[simp]
theorem cofreeResolutionD_zero_toLinearMap :
    (cofreeResolutionD R C M 0).toLinearMap = Comodule.coact (R := R) (C := C) (M := M) :=
  (rfl)

/-- The differential is obtained by tensoring the preceding differential and adding the
last comultiplication with its sign. -/
theorem cofreeResolutionD_succ_toLinearMap (n : ℕ) :
    (cofreeResolutionD R C M (n + 1)).toLinearMap =
      (cofreeResolutionD R C M n).toLinearMap.rTensor C +
        ((-1 : R) ^ (n + 1)) •
          Comodule.coact (R := R) (C := C) (M := cofreeResolutionTerm R C M (n + 1)) :=
  (rfl)

/-- The recursive differential evaluated on an element. -/
theorem cofreeResolutionD_succ_apply (n : ℕ) (x : cofreeResolutionTerm R C M (n + 1)) :
    cofreeResolutionD R C M (n + 1) x =
      (cofreeResolutionD R C M n).toLinearMap.rTensor C x +
        ((-1 : R) ^ (n + 1)) •
          Comodule.coact (R := R) (C := C) (M := cofreeResolutionTerm R C M (n + 1)) x :=
  LinearMap.congr_fun (cofreeResolutionD_succ_toLinearMap R C M n) x

/-- Consecutive augmented differentials compose to zero. -/
@[simp]
theorem cofreeResolutionD_comp (n : ℕ) :
    cofreeResolutionD R C M n ≫ cofreeResolutionD R C M (n + 1) = 0 := by
  apply Comodule.Hom.toLinearMap_injective
  rw [toLinearMap_comp, toLinearMap_zero]
  induction n with
  | zero =>
    rw [cofreeResolutionD_succ_toLinearMap, LinearMap.add_comp, LinearMap.smul_comp]
    have h := (cofreeResolutionD R C M 0).map_coact
    rw [← LinearMap.rTensor_def] at h
    simp only [cofreeResolutionD_zero_toLinearMap] at h ⊢
    rw [h]
    have hs := add_smul (1 : R) (-1 : R)
      (Comodule.coact (R := R) (C := C) (M := cofreeResolutionTerm R C M 1) ∘ₗ
        Comodule.coact (R := R) (C := C) (M := M))
    convert hs.symm using 1 <;> simp
  | succ n ih =>
    have ht := congrArg (LinearMap.rTensor C) ih
    rw [LinearMap.rTensor_comp, LinearMap.rTensor_zero] at ht
    have hc := (cofreeResolutionD R C M (n + 1)).map_coact
    rw [← LinearMap.rTensor_def] at hc
    rw [cofreeResolutionD_succ_toLinearMap R C M (n + 1), LinearMap.add_comp,
      LinearMap.smul_comp, cofreeResolutionD_succ_toLinearMap R C M n,
      LinearMap.comp_add, LinearMap.comp_smul, ← cofreeResolutionD_succ_toLinearMap R C M n,
      ht, zero_add, hc]
    simp only [pow_succ, mul_neg_one, neg_neg]
    rw [← add_smul, neg_add_cancel, zero_smul]

/-- The counit homotopy identity before inserting the alternating sign. -/
private theorem counit_comp_cofreeResolutionD_succ (n : ℕ) :
    Comodule.cofreeCounit R C (cofreeResolutionTerm R C M (n + 1)) ∘ₗ
        (cofreeResolutionD R C M (n + 1)).toLinearMap =
      (cofreeResolutionD R C M n).toLinearMap ∘ₗ
        Comodule.cofreeCounit R C (cofreeResolutionTerm R C M n) +
        ((-1 : R) ^ (n + 1)) • LinearMap.id := by
  rw [cofreeResolutionD_succ_toLinearMap, LinearMap.comp_add, LinearMap.comp_smul]
  congr 1
  · exact Comodule.cofreeCounit_comp_rTensor _
  · congr 1
    apply LinearMap.ext
    intro x
    exact Comodule.rid_lTensor_counit_coact (R := R) (C := C) x

/-- The signed counit contraction of the underlying augmented module sequence. -/
noncomputable def cofreeResolutionContraction (n : ℕ) :
    cofreeResolutionTerm R C M (n + 1) →ₗ[R] cofreeResolutionTerm R C M n :=
  ((-1 : R) ^ n) • Comodule.cofreeCounit R C (cofreeResolutionTerm R C M n)

/-- The signed contraction applies the counit to the final factor. -/
@[simp]
theorem cofreeResolutionContraction_tmul (n : ℕ) (x : cofreeResolutionTerm R C M n) (c : C) :
    cofreeResolutionContraction R C M n (x ⊗ₜ[R] c) =
      ((-1 : R) ^ n) • (Coalgebra.counit (R := R) c • x) := by
  rw [cofreeResolutionContraction, LinearMap.smul_apply, Comodule.cofreeCounit_tmul]

/-- The contracting homotopy splits the augmentation on underlying modules. -/
@[simp]
theorem cofreeResolutionContraction_comp_zero :
    cofreeResolutionContraction R C M 0 ∘ₗ Comodule.coact (R := R) (C := C) (M := M) =
      LinearMap.id := by
  rw [cofreeResolutionContraction, pow_zero, one_smul]
  apply LinearMap.ext
  intro x
  exact Comodule.rid_lTensor_counit_coact x

/-- The signed counit is a contracting homotopy in all positive augmented degrees. -/
theorem cofreeResolutionContraction_comp_d (n : ℕ) :
    cofreeResolutionContraction R C M (n + 1) ∘ₗ
        (cofreeResolutionD R C M (n + 1)).toLinearMap +
      (cofreeResolutionD R C M n).toLinearMap ∘ₗ cofreeResolutionContraction R C M n =
        LinearMap.id := by
  let : AddCommGroup (cofreeResolutionTerm R C M (n + 1)) :=
    Module.addCommMonoidToAddCommGroup R
  rw [cofreeResolutionContraction, cofreeResolutionContraction, LinearMap.smul_comp,
    LinearMap.comp_smul, counit_comp_cofreeResolutionD_succ, smul_add, smul_smul]
  have hs : (-1 : R) ^ (n + 1) * (-1 : R) ^ (n + 1) = 1 := by
    rw [← mul_pow]
    simp
  rw [hs, one_smul, pow_succ, mul_neg_one]
  simp only [neg_smul]
  abel

/-- Every cocycle in a positive augmented degree has the specified counit primitive. -/
theorem cofreeResolutionD_contraction_of_cocycle (n : ℕ)
    (x : cofreeResolutionTerm R C M (n + 1))
    (hx : (cofreeResolutionD R C M (n + 1)).toLinearMap x = 0) :
    (cofreeResolutionD R C M n).toLinearMap (cofreeResolutionContraction R C M n x) = x := by
  have h := LinearMap.congr_fun (cofreeResolutionContraction_comp_d R C M n) x
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, hx, map_zero, zero_add,
    LinearMap.id_apply] using h

/-- Exactness of the underlying augmented sequence, without flatness hypotheses. -/
theorem cofreeResolutionD_exact (n : ℕ) :
    Function.Exact (cofreeResolutionD R C M n).toLinearMap
      (cofreeResolutionD R C M (n + 1)).toLinearMap := by
  intro x
  constructor
  · intro hx
    exact ⟨cofreeResolutionContraction R C M n x,
      cofreeResolutionD_contraction_of_cocycle R C M n x hx⟩
  · rintro ⟨y, rfl⟩
    have h := congrArg Comodule.Hom.toLinearMap (cofreeResolutionD_comp R C M n)
    rw [toLinearMap_comp, toLinearMap_zero] at h
    exact LinearMap.congr_fun h y

/-- The cofree resolution, starting with `M ⊗ C` in cochain degree zero. -/
-- Expose the complex so its terms in morphism signatures are the cofree terms.
@[expose, implicit_reducible]
noncomputable def cofreeResolution : CochainComplex (ComoduleCat.{u, v, max v w} R C) ℕ :=
  CochainComplex.of (fun n ↦ cofreeResolutionTerm R C M (n + 1))
    (fun n ↦ cofreeResolutionD R C M (n + 1)) (fun n ↦ cofreeResolutionD_comp R C M (n + 1))

/-- The resolution terms are the positive augmented terms. -/
@[simp]
theorem cofreeResolution_X (n : ℕ) :
    (cofreeResolution R C M).X n = cofreeResolutionTerm R C M (n + 1) := (rfl)

/-- The differential of the packaged resolution is the augmented differential. -/
@[simp]
theorem cofreeResolution_d (n : ℕ) :
    (cofreeResolution R C M).d n (n + 1) = cofreeResolutionD R C M (n + 1) := by
  simp [cofreeResolution]

/-- The augmentation from `M` into its cofree resolution is its coaction. -/
noncomputable def cofreeResolutionι : M ⟶ (cofreeResolution R C M).X 0 :=
  cofreeResolutionD R C M 0

/-- The augmentation followed by the first differential vanishes. -/
@[reassoc (attr := simp)]
theorem cofreeResolutionι_d :
    cofreeResolutionι R C M ≫ cofreeResolutionD R C M 1 = 0 := by
  exact cofreeResolutionD_comp R C M 0

/-- The augmentation acts by the original coaction. -/
@[simp]
theorem cofreeResolutionι_toLinearMap :
    (cofreeResolutionι R C M).toLinearMap = Comodule.coact (R := R) (C := C) (M := M) :=
  (rfl)

/-- The augmentation is a monomorphism, since the counit splits its underlying module map. -/
instance : Mono (cofreeResolutionι R C M) := by
  apply ConcreteCategory.mono_of_injective
  convert (Comodule.coact_injective (R := R) (C := C) (M := M)) using 1 <;> rfl


variable {M} {N P : ComoduleCat.{u, v, max v w} R C}

/-- A coefficient morphism acts on the first tensor factor of every augmented term. -/
noncomputable def cofreeResolutionTermMap (f : M ⟶ N) : (n : ℕ) →
    (cofreeResolutionTerm R C M n ⟶ cofreeResolutionTerm R C N n)
  | 0 => f
  | n + 1 => (cofreeFunctor R C).map
      ((forget₂ (ComoduleCat R C) (ModuleCat R)).map (cofreeResolutionTermMap f n))

/-- In augmented degree zero, the coefficient map is the original morphism. -/
@[simp]
theorem cofreeResolutionTermMap_zero (f : M ⟶ N) : cofreeResolutionTermMap R C f 0 = f :=
  (rfl)

/-- On a successor term, the coefficient map tensors the preceding map with the identity. -/
theorem cofreeResolutionTermMap_succ_toLinearMap (f : M ⟶ N) (n : ℕ) :
    (cofreeResolutionTermMap R C f (n + 1)).toLinearMap =
      (cofreeResolutionTermMap R C f n).toLinearMap.rTensor C :=
  (rfl)

/-- Identity coefficient maps act as identities in every augmented degree. -/
@[simp]
theorem cofreeResolutionTermMap_id (n : ℕ) :
    cofreeResolutionTermMap R C (𝟙 M) n = 𝟙 _ := by
  apply Comodule.Hom.toLinearMap_injective
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cofreeResolutionTermMap_succ_toLinearMap, ih, toLinearMap_id, LinearMap.rTensor_id]
    exact (toLinearMap_id R C (cofreeResolutionTerm R C M (n + 1))).symm

/-- Coefficient composition is preserved in every augmented degree. -/
@[simp]
theorem cofreeResolutionTermMap_comp (f : M ⟶ N) (g : N ⟶ P) (n : ℕ) :
    cofreeResolutionTermMap R C (f ≫ g) n =
      cofreeResolutionTermMap R C f n ≫ cofreeResolutionTermMap R C g n := by
  apply Comodule.Hom.toLinearMap_injective
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cofreeResolutionTermMap_succ_toLinearMap, ih, toLinearMap_comp,
      LinearMap.rTensor_comp, toLinearMap_comp, cofreeResolutionTermMap_succ_toLinearMap,
      cofreeResolutionTermMap_succ_toLinearMap]

/-- The augmented differential is natural in the coefficient comodule. -/
theorem cofreeResolutionTermMap_comp_d (f : M ⟶ N) (n : ℕ) :
    cofreeResolutionTermMap R C f n ≫ cofreeResolutionD R C N n =
      cofreeResolutionD R C M n ≫ cofreeResolutionTermMap R C f (n + 1) := by
  apply Comodule.Hom.toLinearMap_injective
  simp only [toLinearMap_comp]
  induction n with
  | zero =>
    simpa only [cofreeResolutionD_zero_toLinearMap, cofreeResolutionTermMap_zero,
      cofreeResolutionTermMap_succ_toLinearMap, LinearMap.rTensor_def] using f.map_coact.symm
  | succ n ih =>
    have ht := congrArg (LinearMap.rTensor C) ih
    rw [LinearMap.rTensor_comp, LinearMap.rTensor_comp] at ht
    have hc := (cofreeResolutionTermMap R C f (n + 1)).map_coact
    rw [← LinearMap.rTensor_def] at hc
    rw [cofreeResolutionD_succ_toLinearMap, cofreeResolutionD_succ_toLinearMap,
      LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul]
    simp only [cofreeResolutionTermMap_succ_toLinearMap] at ht hc ⊢
    rw [ht, hc]

/-- The chain map on cofree resolutions induced by a coefficient morphism. -/
noncomputable def cofreeResolutionMap (f : M ⟶ N) :
    cofreeResolution R C M ⟶ cofreeResolution R C N :=
  CochainComplex.ofHom (fun n ↦ cofreeResolutionTermMap R C f (n + 1))
    (fun n ↦ by simpa only [cofreeResolution_d] using
      cofreeResolutionTermMap_comp_d R C f (n + 1))

/-- Components of the induced chain map are the tensor coefficient maps. -/
@[simp]
theorem cofreeResolutionMap_f (f : M ⟶ N) (n : ℕ) :
    (cofreeResolutionMap R C f).f n = cofreeResolutionTermMap R C f (n + 1) :=
  (rfl)

/-- The chain map induced by an identity is the identity. -/
@[simp]
theorem cofreeResolutionMap_id : cofreeResolutionMap R C (𝟙 M) = 𝟙 _ := by
  ext n : 1
  simp [cofreeResolution]

/-- The chain map induced by a composite is the composite of the induced chain maps. -/
@[simp]
theorem cofreeResolutionMap_comp (f : M ⟶ N) (g : N ⟶ P) :
    cofreeResolutionMap R C (f ≫ g) = cofreeResolutionMap R C f ≫ cofreeResolutionMap R C g := by
  ext n : 1
  simp

/-- The augmentation is natural in the coefficient comodule. -/
@[reassoc]
theorem cofreeResolutionι_naturality (f : M ⟶ N) :
    f ≫ cofreeResolutionι R C N =
      cofreeResolutionι R C M ≫ (cofreeResolutionMap R C f).f 0 := by
  apply Comodule.Hom.toLinearMap_injective
  rw [toLinearMap_comp, toLinearMap_comp, cofreeResolutionι_toLinearMap,
    cofreeResolutionι_toLinearMap, cofreeResolutionMap_f,
    cofreeResolutionTermMap_succ_toLinearMap, cofreeResolutionTermMap_zero]
  simpa only [LinearMap.rTensor_def] using f.map_coact.symm

variable (M)

variable [Module.Flat R C]

/-- Exactness of each augmented short complex in the comodule category. -/
theorem exact_cofreeResolutionD (n : ℕ) :
    (ShortComplex.mk (cofreeResolutionD R C M n) (cofreeResolutionD R C M (n + 1))
      (cofreeResolutionD_comp R C M n)).Exact := by
  apply (ShortComplex.exact_map_iff_of_faithful _
    (forget₂ (ComoduleCat R C) (ModuleCat R))).mp
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  simp only [ShortComplex.map_g, forget₂_moduleCat_map] at hx
  refine ⟨cofreeResolutionContraction R C M n x, ?_⟩
  exact cofreeResolutionD_contraction_of_cocycle R C M n x hx

/-- The cofree resolution is exact in every positive degree in the comodule category. -/
theorem exactAt_cofreeResolution (n : ℕ) : (cofreeResolution R C M).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  simpa only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    cofreeResolution_d] using exact_cofreeResolutionD R C M (n + 1)

/-- Exactness at degree zero, including the augmentation. -/
theorem exact_cofreeResolutionι :
    (ShortComplex.mk (cofreeResolutionι R C M) ((cofreeResolution R C M).d 0 1)
      (cofreeResolutionι_d R C M)).Exact := by
  exact exact_cofreeResolutionD R C M 0

end TauCeti.ComoduleCat
