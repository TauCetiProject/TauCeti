/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.Geometry.Symplectic.Finrank
public import TauCeti.LinearAlgebra.BilinearForm.Symmetric

/-!
# Dimensions of the tame and compatible tangent spaces

Let `J` be a linear complex structure on a real vector space `V` of complex dimension `n`, and
`ω` a symplectic form on `V`. Varying `J` through tame structures moves it in the directions of
the tangent space `TauCeti.AlmostComplexStructure.tangentSpace J`, the endomorphisms `Y` with
`Y J + J Y = 0`; varying it through `ω`-compatible structures moves it in the smaller compatible
tangent space `TauCeti.SymplecticForm.compatibleTangentSpace ω J`, where `Y` is moreover
skew-adjoint for `ω`. This file computes their dimensions:

* the tame tangent space has real dimension `2 n²`
  (`TauCeti.AlmostComplexStructure.finrank_tangentSpace`);
* for a `J`-invariant `ω`, the compatible tangent space has real dimension `n (n + 1)`
  (`TauCeti.SymplecticForm.Invariant.finrank_compatibleTangentSpace`), the dimension of the
  complex symmetric `n × n` matrices, which is the dimension of Siegel's upper half space;
* so the two agree exactly when `n ≤ 1`
  (`TauCeti.SymplecticForm.Invariant.compatibleTangentSpace_eq_tangentSpace_iff`). In real
  dimension at most two every tame structure is compatible
  (`TauCeti.SymplecticForm.Tames.compatible_of_finrank_le_two`), while from complex dimension two
  on the compatible variations form a proper subspace of the tame ones, so that a transversality
  argument varying the structure has to be carried out separately for tame and for compatible
  structures.

The tame count is the case `V = W` of a general one
(`TauCeti.AlmostComplexStructure.finrank_complexAntilinearMaps` and
`TauCeti.AlmostComplexStructure.finrank_complexLinearMaps`): the complex-linear and the
complex-antilinear real maps between complex vector spaces of complex dimensions `n` and `m` both
form spaces of real dimension `2 n m`. They are complementary
(`TauCeti.isCompl_complexLinearMaps_complexAntilinearMaps`), and precomposition with a
conjugation of the source (`TauCeti.AlmostComplexStructure.exists_conjugation`), a real-linear
involution anticommuting with `J`, exchanges them.

For the compatible count, `Y ↦ ω(Y ·, ·)` identifies endomorphisms with bilinear forms. It takes
the `ω`-skew-adjoint endomorphisms to the symmetric forms, of dimension `2n (2n + 1) / 2`, and,
when `ω` is `J`-invariant, the variations of `J` to the forms `B` with `B (J v) w = B v (J w)` and
the complex-linear endomorphisms to those with `B (J v) w = -B v (J w)`. The symmetric forms split
along these two conditions, and on the second condition `B ↦ B(·, J ·)` exchanges symmetric and
antisymmetric forms, so the symmetric forms of the second kind have dimension `n²`, half of `2n²`.
This leaves `2n² + n - n² = n (n + 1)` for the compatible variations.

## Main results

* `TauCeti.AlmostComplexStructure.exists_conjugation`: a complex structure on a
  finite-dimensional real space admits a real-linear involution anticommuting with it.
* `TauCeti.AlmostComplexStructure.finrank_complexLinearMaps`,
  `TauCeti.AlmostComplexStructure.finrank_complexAntilinearMaps`: both have real dimension
  `2 n m`.
* `TauCeti.AlmostComplexStructure.finrank_tangentSpace`: the tame tangent space has real
  dimension `2 n²`.
* `TauCeti.SymplecticForm.Invariant.finrank_compatibleTangentSpace`: the compatible tangent space
  has real dimension `n (n + 1)`.
* `TauCeti.SymplecticForm.Invariant.compatibleTangentSpace_eq_tangentSpace_iff`: the two tangent
  spaces agree exactly in complex dimension at most one.
* `TauCeti.SymplecticForm.Tames.compatible_of_finrank_le_two`: in real dimension at most two,
  tameness implies compatibility.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Sections 2.5 and 2.6 (the spaces of tame and compatible complex structures and
  Siegel's upper half space).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 3.2.
-/

public section

namespace TauCeti

open Module

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Two complementary pieces of a submodule: if `A` and `B` are disjoint and every element of `P`
is the sum of an element of `P ⊓ A` and one of `P ⊓ B`, the dimensions of these pieces add up to
that of `P`. -/
private theorem finrank_inf_add_finrank_inf {X : Type*} [AddCommGroup X] [Module ℝ X]
    [FiniteDimensional ℝ X] {P A B : Submodule ℝ X} (hAB : Disjoint A B)
    (h : ∀ x ∈ P, ∃ a ∈ P ⊓ A, ∃ b ∈ P ⊓ B, a + b = x) :
    finrank ℝ (P ⊓ A : Submodule ℝ X) + finrank ℝ (P ⊓ B : Submodule ℝ X) = finrank ℝ P := by
  have hsup : P ⊓ A ⊔ P ⊓ B = P := le_antisymm (sup_le inf_le_left inf_le_left) fun x hx ↦ by
    obtain ⟨a, ha, b, hb, rfl⟩ := h x hx
    exact Submodule.add_mem_sup ha hb
  have hinf : P ⊓ A ⊓ (P ⊓ B) = ⊥ :=
    eq_bot_iff.2 fun x hx ↦ hAB.le_bot ⟨hx.1.2, hx.2.2⟩
  have := Submodule.finrank_sup_add_finrank_inf_eq (P ⊓ A) (P ⊓ B)
  rw [hsup, hinf, finrank_bot, add_zero] at this
  exact this.symm

namespace AlmostComplexStructure

/-- **Conjugations exist.** A complex structure `J` on a finite-dimensional real vector space
admits a *conjugation*: a real-linear involution `K` that anticommutes with `J`, such as
coordinatewise complex conjugation under an identification of `(V, J)` with `ℂⁿ`. -/
theorem exists_conjugation [FiniteDimensional ℝ V] (J : AlmostComplexStructure V) :
    ∃ K : V ≃ₗ[ℝ] V, (∀ v, K (K v) = v) ∧ ∀ v, K (J v) = -J (K v) := by
  obtain ⟨φ, hφ⟩ := J.exists_linearEquiv_I_smul (G := Fin J.complexFinrank → ℂ) (by
    rw [Module.finrank_fin_fun, J.finrank_real_eq_two_mul_complexFinrank])
  let c : (Fin J.complexFinrank → ℂ) →ₗ[ℝ] (Fin J.complexFinrank → ℂ) :=
    { toFun := fun z i ↦ star (z i)
      map_add' := fun z w ↦ funext fun i ↦ star_add (z i) (w i)
      map_smul' := fun r z ↦ funext fun i ↦ by
        simp only [Pi.smul_apply, star_smul, star_trivial, RingHom.id_apply] }
  have hc : Function.Involutive c := fun z ↦ by
    ext i
    simp only [c, LinearMap.coe_mk, AddHom.coe_mk, Complex.star_def, Complex.conj_conj]
  have hcI (z : Fin J.complexFinrank → ℂ) : c (Complex.I • z) = -(Complex.I • c z) := by
    ext i
    simp only [c, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
      Complex.star_def, map_mul, Complex.conj_I]
    ring
  refine ⟨φ.symm.trans ((LinearEquiv.ofInvolutive c hc).trans φ), fun v ↦ ?_, fun v ↦ ?_⟩
  · simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.coe_ofInvolutive, hc (φ.symm v), LinearEquiv.apply_symm_apply]
  obtain ⟨z, rfl⟩ := φ.surjective v
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, ← hφ,
    LinearEquiv.coe_ofInvolutive, hcI, map_neg]

/-- The variations of `J` are its complex-antilinear endomorphisms. -/
theorem tangentSpace_eq_complexAntilinearMaps (J : AlmostComplexStructure V) :
    J.tangentSpace = complexAntilinearMaps J.toLinearMap J.toLinearMap := by
  ext Y
  rw [mem_tangentSpace_iff_apply, mem_complexAntilinearMaps]
  exact ⟨isComplexAntilinear_of_apply, IsComplexAntilinear.apply⟩

variable [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
  (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)

omit [FiniteDimensional ℝ W] in
/-- Precomposition with a conjugation of the source exchanges the complex-linear and the
complex-antilinear maps, so the two spaces have the same dimension. -/
private theorem finrank_complexLinearMaps_eq_finrank_complexAntilinearMaps :
    finrank ℝ (complexLinearMaps J.toLinearMap J'.toLinearMap) =
      finrank ℝ (complexAntilinearMaps J.toLinearMap J'.toLinearMap) := by
  obtain ⟨K, hKK, hKJ⟩ := J.exists_conjugation
  -- `Ψ F = F ∘ K⁻¹`; since `K⁻¹ = K`, it is precomposition with `K`.
  let Ψ : (V →ₗ[ℝ] W) ≃ₗ[ℝ] (V →ₗ[ℝ] W) := K.arrowCongr (LinearEquiv.refl ℝ W)
  have hK (v : V) : K.symm v = K v := by
    rw [LinearEquiv.symm_apply_eq, hKK]
  have hΨ (F : V →ₗ[ℝ] W) (v : V) : Ψ F v = F (K v) := by
    simp [Ψ, LinearEquiv.arrowCongr_apply, hK]
  have h : complexLinearMaps J.toLinearMap J'.toLinearMap =
      (complexAntilinearMaps J.toLinearMap J'.toLinearMap).comap (Ψ : _ →ₗ[ℝ] _) := by
    ext F
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe, mem_complexLinearMaps,
      mem_complexAntilinearMaps]
    constructor
    · intro hF
      refine isComplexAntilinear_of_apply fun v ↦ ?_
      rw [hΨ, hΨ]
      exact (congrArg F (hKJ v)).trans (by rw [map_neg, hF.apply])
    · intro hF
      refine isComplexLinear_of_apply fun v ↦ ?_
      have := hF.apply (K v)
      rw [hΨ, hΨ, hKJ, hKK, map_neg, neg_inj] at this
      exact this
  rw [h, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]

/-- The complex-linear and the complex-antilinear maps together have the dimension of all real
linear maps. -/
private theorem finrank_complexLinearMaps_add_finrank_complexAntilinearMaps :
    finrank ℝ (complexLinearMaps J.toLinearMap J'.toLinearMap) +
        finrank ℝ (complexAntilinearMaps J.toLinearMap J'.toLinearMap) =
      finrank ℝ V * finrank ℝ W := by
  rw [Submodule.finrank_add_eq_of_isCompl
    (isCompl_complexLinearMaps_complexAntilinearMaps J.square_neg J'.square_neg),
    Module.finrank_linearMap]

/-- The complex-linear maps between complex vector spaces of complex dimensions `n` and `m` form a
real vector space of dimension `2 n m`. -/
theorem finrank_complexLinearMaps :
    finrank ℝ (complexLinearMaps J.toLinearMap J'.toLinearMap) =
      2 * J.complexFinrank * J'.complexFinrank := by
  have h₁ := finrank_complexLinearMaps_add_finrank_complexAntilinearMaps J J'
  rw [finrank_complexLinearMaps_eq_finrank_complexAntilinearMaps,
    J.finrank_real_eq_two_mul_complexFinrank, J'.finrank_real_eq_two_mul_complexFinrank] at h₁
  rw [finrank_complexLinearMaps_eq_finrank_complexAntilinearMaps]
  linarith

/-- The complex-antilinear real maps between complex vector spaces of complex dimensions `n` and
`m` form a real vector space of dimension `2 n m`. -/
theorem finrank_complexAntilinearMaps :
    finrank ℝ (complexAntilinearMaps J.toLinearMap J'.toLinearMap) =
      2 * J.complexFinrank * J'.complexFinrank := by
  rw [← finrank_complexLinearMaps_eq_finrank_complexAntilinearMaps, finrank_complexLinearMaps]

/-- **The tame tangent space has real dimension `2 n²`**: the endomorphisms anticommuting with a
complex structure on a space of complex dimension `n`. -/
theorem finrank_tangentSpace :
    finrank ℝ J.tangentSpace = 2 * J.complexFinrank ^ 2 := by
  rw [tangentSpace_eq_complexAntilinearMaps, finrank_complexAntilinearMaps]
  ring

end AlmostComplexStructure

namespace SymplecticForm

open LinearMap (BilinForm)

variable {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-! ### Bilinear forms with a symmetry under `J` -/

variable (J) in
/-- The bilinear forms `B` with `B (J v) w = B v (J w)`. For a `J`-invariant `ω`, these are the
forms `ω(Y ·, ·)` of the variations `Y` of `J`. -/
private def jCommForms : Submodule ℝ (BilinForm ℝ V) where
  carrier := {B | ∀ v w, B (J v) w = B v (J w)}
  zero_mem' _ _ := by simp
  add_mem' hB hC v w := by simp [hB v w, hC v w]
  smul_mem' c B hB v w := by simp [hB v w]

variable (J) in
/-- The bilinear forms `B` with `B (J v) w = -B v (J w)`. For a `J`-invariant `ω`, these are the
forms `ω(Y ·, ·)` of the complex-linear endomorphisms `Y`. -/
private def jAntiForms : Submodule ℝ (BilinForm ℝ V) where
  carrier := {B | ∀ v w, B (J v) w = -B v (J w)}
  zero_mem' _ _ := by simp
  add_mem' hB hC v w := by
    simp only [LinearMap.add_apply, hB v w, hC v w]
    abel
  smul_mem' c B hB v w := by simp [hB v w]

variable (V) in
/-- The antisymmetric bilinear forms. -/
private def antisymmForms : Submodule ℝ (BilinForm ℝ V) where
  carrier := {B | ∀ v w, B v w = -B w v}
  zero_mem' _ _ := by simp
  add_mem' hB hC v w := by
    simp only [LinearMap.add_apply, hB v w, hC v w]
    abel
  smul_mem' c B hB v w := by simp [hB v w]

private theorem mem_jCommForms {B : BilinForm ℝ V} :
    B ∈ jCommForms J ↔ ∀ v w, B (J v) w = B v (J w) := Iff.rfl

private theorem mem_jAntiForms {B : BilinForm ℝ V} :
    B ∈ jAntiForms J ↔ ∀ v w, B (J v) w = -B v (J w) := Iff.rfl

private theorem mem_antisymmForms {B : BilinForm ℝ V} :
    B ∈ antisymmForms V ↔ ∀ v w, B v w = -B w v := Iff.rfl

/-- A bilinear form satisfying both symmetries under `J` vanishes. -/
private theorem disjoint_jCommForms_jAntiForms : Disjoint (jCommForms J) (jAntiForms J) := by
  refine Submodule.disjoint_def.2 fun B hB hB' ↦ LinearMap.ext₂ fun v w ↦ ?_
  have h := (hB v (-J w)).symm.trans (hB' v (-J w))
  rw [map_neg, AlmostComplexStructure.apply_apply, neg_neg] at h
  rw [LinearMap.zero_apply, LinearMap.zero_apply]
  linarith

/-- A symmetric bilinear form splits into a symmetric form in `jCommForms J` and one in
`jAntiForms J`, the halves of `B ∓ B (J ·, J ·)`. -/
private theorem finrank_symm_inf_jCommForms_add [FiniteDimensional ℝ V] :
    finrank ℝ (BilinForm.symmSubmodule ℝ V ⊓ jCommForms J : Submodule ℝ (BilinForm ℝ V)) +
        finrank ℝ (BilinForm.symmSubmodule ℝ V ⊓ jAntiForms J : Submodule ℝ (BilinForm ℝ V)) =
      finrank ℝ (BilinForm.symmSubmodule ℝ V) := by
  have hs : ∀ B ∈ BilinForm.symmSubmodule ℝ V,
      ∃ a ∈ BilinForm.symmSubmodule ℝ V ⊓ jCommForms J,
        ∃ b ∈ BilinForm.symmSubmodule ℝ V ⊓ jAntiForms J, a + b = B := by
    intro B hB
    have hBs := BilinForm.isSymm_def.1 (BilinForm.mem_symmSubmodule.1 hB)
    let C := B.compl₁₂ J.toLinearMap J.toLinearMap
    have hC (v w : V) : C v w = B (J v) (J w) := rfl
    refine ⟨(1 / 2 : ℝ) • (B - C), ⟨BilinForm.mem_symmSubmodule.2 (BilinForm.isSymm_def.2
        fun v w ↦ ?_), mem_jCommForms.2 fun v w ↦ ?_⟩, (1 / 2 : ℝ) • (B + C),
      ⟨BilinForm.mem_symmSubmodule.2 (BilinForm.isSymm_def.2 fun v w ↦ ?_),
        mem_jAntiForms.2 fun v w ↦ ?_⟩, LinearMap.ext₂ fun v w ↦ ?_⟩
    · simp only [LinearMap.smul_apply, LinearMap.sub_apply, hC, smul_eq_mul, hBs v w,
        hBs (J v) (J w)]
    · simp only [LinearMap.smul_apply, LinearMap.sub_apply, hC,
        AlmostComplexStructure.apply_apply, map_neg, LinearMap.neg_apply, smul_eq_mul]
      ring
    · simp only [LinearMap.smul_apply, LinearMap.add_apply, hC, smul_eq_mul, hBs v w,
        hBs (J v) (J w)]
    · simp only [LinearMap.smul_apply, LinearMap.add_apply, hC,
        AlmostComplexStructure.apply_apply, map_neg, LinearMap.neg_apply, smul_eq_mul]
      ring
    · simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]
      ring
  exact finrank_inf_add_finrank_inf (X := BilinForm ℝ V) disjoint_jCommForms_jAntiForms hs

/-- Inside `jAntiForms J`, the bilinear forms split into symmetric and antisymmetric ones. -/
private theorem finrank_jAntiForms_inf_symm_add [FiniteDimensional ℝ V] :
    finrank ℝ (jAntiForms J ⊓ BilinForm.symmSubmodule ℝ V : Submodule ℝ (BilinForm ℝ V)) +
        finrank ℝ (jAntiForms J ⊓ antisymmForms V : Submodule ℝ (BilinForm ℝ V)) =
      finrank ℝ (jAntiForms J) := by
  have hd : Disjoint (BilinForm.symmSubmodule ℝ V) (antisymmForms V) := by
    refine Submodule.disjoint_def.2 fun B hB hB' ↦ LinearMap.ext₂ fun v w ↦ ?_
    have h₁ := BilinForm.isSymm_def.1 (BilinForm.mem_symmSubmodule.1 hB) v w
    have h₂ := mem_antisymmForms.1 hB' v w
    rw [LinearMap.zero_apply, LinearMap.zero_apply]
    linarith
  have hs : ∀ B ∈ jAntiForms J, ∃ a ∈ jAntiForms J ⊓ BilinForm.symmSubmodule ℝ V,
      ∃ b ∈ jAntiForms J ⊓ antisymmForms V, a + b = B := by
    intro B hB
    have hB' := mem_jAntiForms.1 hB
    refine ⟨(1 / 2 : ℝ) • (B + B.flip), ⟨mem_jAntiForms.2 fun v w ↦ ?_,
        BilinForm.mem_symmSubmodule.2 (BilinForm.isSymm_def.2 fun v w ↦ ?_)⟩,
      (1 / 2 : ℝ) • (B - B.flip), ⟨mem_jAntiForms.2 fun v w ↦ ?_,
        mem_antisymmForms.2 fun v w ↦ ?_⟩, LinearMap.ext₂ fun v w ↦ ?_⟩
    · simp only [LinearMap.smul_apply, LinearMap.add_apply, BilinForm.flip_apply, smul_eq_mul]
      linarith [hB' v w, hB' w v]
    · simp only [LinearMap.smul_apply, LinearMap.add_apply, BilinForm.flip_apply, smul_eq_mul]
      ring
    · simp only [LinearMap.smul_apply, LinearMap.sub_apply, BilinForm.flip_apply, smul_eq_mul]
      linarith [hB' v w, hB' w v]
    · simp only [LinearMap.smul_apply, LinearMap.sub_apply, BilinForm.flip_apply, smul_eq_mul]
      ring
    · simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]
      ring
  exact finrank_inf_add_finrank_inf (X := BilinForm ℝ V) hd hs

/-- On `jAntiForms J`, the map `B ↦ B (·, J ·)` exchanges symmetric and antisymmetric forms, so
the two have the same dimension. -/
private theorem finrank_jAntiForms_inf_symm_eq :
    finrank ℝ (jAntiForms J ⊓ BilinForm.symmSubmodule ℝ V : Submodule ℝ (BilinForm ℝ V)) =
      finrank ℝ (jAntiForms J ⊓ antisymmForms V : Submodule ℝ (BilinForm ℝ V)) := by
  let Ψ : BilinForm ℝ V ≃ₗ[ℝ] BilinForm ℝ V :=
    (LinearEquiv.refl ℝ V).arrowCongr (J.linearEquiv.symm.arrowCongr (LinearEquiv.refl ℝ ℝ))
  have hΨ (B : BilinForm ℝ V) (v w : V) : Ψ B v w = B v (J w) := by
    simp [Ψ]
  have h : (jAntiForms J ⊓ BilinForm.symmSubmodule ℝ V : Submodule ℝ (BilinForm ℝ V)) =
      (jAntiForms J ⊓ antisymmForms V).comap (Ψ : BilinForm ℝ V →ₗ[ℝ] BilinForm ℝ V) := by
    ext B
    rw [Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_inf, mem_jAntiForms, mem_jAntiForms,
      mem_antisymmForms, BilinForm.mem_symmSubmodule, BilinForm.isSymm_def, LinearEquiv.coe_coe]
    simp only [hΨ, AlmostComplexStructure.apply_apply, map_neg, neg_neg]
    constructor
    · rintro ⟨hA, hS⟩
      refine ⟨fun v w ↦ ?_, fun v w ↦ ?_⟩
      · simpa using hA v (J w)
      · rw [hS v (J w), hA w v]
    · rintro ⟨hA, hS⟩
      refine ⟨fun v w ↦ ?_, fun v w ↦ ?_⟩
      · simpa using (hA (J v) w).symm
      · have h₁ := hS v (J w)
        rw [AlmostComplexStructure.apply_apply, map_neg] at h₁
        rw [← neg_inj, h₁, hA w v]
  rw [h, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]

/-! ### From endomorphisms to bilinear forms -/

variable [FiniteDimensional ℝ V]

variable (ω) in
/-- Endomorphisms as bilinear forms: `Y ↦ ω(Y ·, ·)`, a linear isomorphism since `ω` is
nondegenerate. -/
private noncomputable def leftBilinEquiv : Module.End ℝ V ≃ₗ[ℝ] BilinForm ℝ V :=
  LinearEquiv.congrRight (ω.toBilinForm.toDual ω.nondegenerate)

private theorem leftBilinEquiv_apply (Y : Module.End ℝ V) (v w : V) :
    ω.leftBilinEquiv Y v w = ω (Y v) w :=
  BilinForm.toDual_def ω.nondegenerate

/-- A vector is determined by its pairings under `ω`. -/
private theorem eq_of_forall_apply_eq (ω : SymplecticForm V) {x y : V}
    (h : ∀ w, ω x w = ω y w) : x = y :=
  (ω.toBilinForm.toDual ω.nondegenerate).injective <| LinearMap.ext fun w ↦ by
    simpa [BilinForm.toDual_def] using h w

/-- For a `J`-invariant `ω`, the variations `Y` of `J` are the endomorphisms with
`ω (Y (J v)) w = ω (Y v) (J w)`. -/
private theorem Invariant.mem_tangentSpace_iff (h : ω.Invariant J) {Y : Module.End ℝ V} :
    Y ∈ J.tangentSpace ↔ ∀ v w, ω (Y (J v)) w = ω (Y v) (J w) := by
  rw [AlmostComplexStructure.mem_tangentSpace_iff_apply]
  refine ⟨fun hY v w ↦ ?_, fun hY v ↦ ω.eq_of_forall_apply_eq fun w ↦ ?_⟩
  · have h₁ := h.apply_apply_eq_neg (Y v) w
    beta_reduce at h₁ ⊢
    rw [hY, map_neg, LinearMap.neg_apply, h₁, neg_neg]
  · have h₁ := h.apply_apply_eq_neg (Y v) w
    have h₂ := hY v w
    beta_reduce at h₁ h₂ ⊢
    rw [map_neg, LinearMap.neg_apply, h₁, neg_neg, h₂]

/-- For a `J`-invariant `ω`, the complex-linear endomorphisms are the forms in
`jAntiForms J`. -/
private theorem Invariant.complexLinearMaps_eq_comap (h : ω.Invariant J) :
    complexLinearMaps J.toLinearMap J.toLinearMap =
      (jAntiForms J).comap (ω.leftBilinEquiv : Module.End ℝ V →ₗ[ℝ] BilinForm ℝ V) := by
  ext Y
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe, mem_complexLinearMaps, mem_jAntiForms,
    leftBilinEquiv_apply]
  refine ⟨fun hY v w ↦ ?_, fun hY ↦ isComplexLinear_of_apply fun v ↦
    ω.eq_of_forall_apply_eq fun w ↦ ?_⟩
  · have h₁ := h.apply_apply_eq_neg (Y v) w
    beta_reduce at h₁
    rw [hY.apply, h₁]
  · have h₁ := h.apply_apply_eq_neg (Y v) w
    beta_reduce at h₁ ⊢
    rw [hY, h₁]

/-- For a `J`-invariant `ω`, the compatible variations of `J` are the endomorphisms `Y` for which
`ω(Y ·, ·)` is symmetric and lies in `jCommForms J`. -/
private theorem Invariant.compatibleTangentSpace_eq_comap (h : ω.Invariant J) :
    ω.compatibleTangentSpace J =
      (BilinForm.symmSubmodule ℝ V ⊓ jCommForms J).comap
        (ω.leftBilinEquiv : Module.End ℝ V →ₗ[ℝ] BilinForm ℝ V) := by
  ext Y
  rw [Submodule.mem_comap, Submodule.mem_inf, BilinForm.mem_symmSubmodule, BilinForm.isSymm_def,
    mem_jCommForms, mem_compatibleTangentSpace, ← AlmostComplexStructure.mem_tangentSpace_iff_apply,
    h.mem_tangentSpace_iff, and_comm]
  simp only [LinearEquiv.coe_coe, leftBilinEquiv_apply]
  refine and_congr (forall₂_congr fun v w ↦ ?_) Iff.rfl
  have h₁ := ω.neg_eq (Y w) v
  beta_reduce at h₁
  rw [← h₁, add_neg_eq_zero]

/-! ### The dimension of the compatible tangent space -/

/-- **The compatible tangent space has real dimension `n (n + 1)`.** For a symplectic form `ω`
invariant under a complex structure `J` on a space of complex dimension `n`, the variations of
`J` that are skew-adjoint for `ω` form a real vector space of dimension `n (n + 1)`, the dimension
of the complex symmetric `n × n` matrices. -/
theorem Invariant.finrank_compatibleTangentSpace (h : ω.Invariant J) :
    finrank ℝ (ω.compatibleTangentSpace J) = J.complexFinrank * (J.complexFinrank + 1) := by
  set n := J.complexFinrank
  have hCT : finrank ℝ (ω.compatibleTangentSpace J) =
      finrank ℝ (BilinForm.symmSubmodule ℝ V ⊓ jCommForms J : Submodule ℝ (BilinForm ℝ V)) := by
    rw [h.compatibleTangentSpace_eq_comap, Submodule.comap_equiv_eq_map_symm,
      LinearEquiv.finrank_map_eq]
  have hanti : finrank ℝ (jAntiForms J) = 2 * n * n := by
    have := J.finrank_complexLinearMaps J
    rwa [h.complexLinearMaps_eq_comap, Submodule.comap_equiv_eq_map_symm,
      LinearEquiv.finrank_map_eq] at this
  have hsymm : finrank ℝ (BilinForm.symmSubmodule ℝ V) = n * (2 * n + 1) := by
    rw [BilinForm.finrank_symmSubmodule, J.finrank_real_eq_two_mul_complexFinrank, mul_assoc]
    exact Nat.mul_div_cancel_left _ two_pos
  have h₁ := finrank_symm_inf_jCommForms_add (J := J)
  have h₂ := finrank_jAntiForms_inf_symm_add (J := J)
  have h₃ := finrank_jAntiForms_inf_symm_eq (J := J)
  rw [inf_comm (jAntiForms J)] at h₂ h₃
  rw [hCT]
  nlinarith

/-- **Tame and compatible variations agree exactly in complex dimension at most one.** For a
symplectic form `ω` invariant under `J`, the compatible tangent space equals the tangent space of
`J` if and only if `J.complexFinrank ≤ 1`: from complex dimension two on, `n (n + 1) < 2 n²`. -/
theorem Invariant.compatibleTangentSpace_eq_tangentSpace_iff (h : ω.Invariant J) :
    ω.compatibleTangentSpace J = J.tangentSpace ↔ J.complexFinrank ≤ 1 := by
  have hT := J.finrank_tangentSpace
  have hC := h.finrank_compatibleTangentSpace
  refine ⟨fun hE ↦ ?_, fun hn ↦ Submodule.eq_of_le_of_finrank_eq
    compatibleTangentSpace_le_tangentSpace ?_⟩
  · rw [hE, hT] at hC
    nlinarith
  · rw [hT, hC]
    interval_cases J.complexFinrank <;> rfl

/-- **In real dimension at most two, tame structures are compatible**: every complex structure
preserves an alternating form there, so `ω`-tameness of `J` already gives `ω`-compatibility. -/
theorem Tames.compatible_of_finrank_le_two (h : ω.Tames J) (hV : finrank ℝ V ≤ 2) :
    ω.Compatible J :=
  Compatible.of_tames ((ω.invariant_iff J).2 (J.bilin_apply_apply_eq_of_finrank_le_two hV ω.isAlt))
    h

end SymplecticForm

end TauCeti
