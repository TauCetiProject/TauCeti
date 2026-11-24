/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.HochschildCohomology.Bimodule
import TauCeti.Data.Fin.Tuple.Basic

/-!
# Normalized Hochschild cochains with coefficients in a bimodule

Let `A` be a unital algebra over a commutative ring `R` and `M` an `A`-bimodule. A Hochschild
cochain `ψ : Aⁿ → M` is **normalized** when it vanishes as soon as one of its arguments is `1`;
by multilinearity it then vanishes as soon as one of its arguments is a scalar
(`TauCeti.apply_eq_zero_of_mem_hochschildBimoduleNormalizedCochains_of_eq_algebraMap`), so the
normalized cochains are the cochains on `(A / R·1)^{⊗n}`.

The Hochschild coboundary of a normalized cochain is normalized
(`TauCeti.hochschildBimoduleCoboundary_mem_hochschildBimoduleNormalizedCochains`). On a tuple
`(a₀, …, aₙ)` with `aⱼ = 1`, every coface `∂ᵢψ` other than `∂ⱼψ` and `∂ⱼ₊₁ψ` evaluates `ψ` on a
tuple that still contains the entry `1`, and `∂ⱼψ` and `∂ⱼ₊₁ψ` both evaluate `ψ` on the tuple with
`aⱼ` removed; they enter `δψ` with opposite signs. So the normalized cochains form a subcomplex
`TauCeti.hochschildBimoduleNormalizedCochainComplex` of the Hochschild cochain complex, with
inclusion `TauCeti.hochschildBimoduleNormalizedCochainComplexι`.

In degrees at most two, the lemmas below show at the level of cocycles and coboundaries that the
inclusion is bijective on `HH⁰`, `HH¹` and `HH²`; the induced map on the homology objects of the
two complexes is not stated here. Every cochain of degree zero is normalized, and so is every
cocycle of degree one: a derivation `D` has `D 1 = D (1 * 1) = 2 D 1`. Every `2`-cocycle `ψ` is
cohomologous to a normalized one: the cocycle identity gives `ψ(1, b) = ψ(1, 1) b` and
`ψ(a, 1) = a ψ(1, 1)`, so `ψ` minus the coboundary of `a ↦ a ψ(1, 1)` is normalized. A `1`-cochain
whose coboundary is normalized is normalized, since `(δφ)(1, 1) = φ 1`. Whether the inclusion is a
quasi-isomorphism in every degree is not addressed here.

## Main definitions

* `TauCeti.hochschildBimoduleNormalizedCochains`: the normalized `n`-cochains.
* `TauCeti.hochschildBimoduleNormalizedCoboundary`: the Hochschild coboundary restricted to
  normalized cochains.
* `TauCeti.hochschildBimoduleNormalizedCochainComplex`: the normalized Hochschild cochain complex.
* `TauCeti.hochschildBimoduleNormalizedCochainComplexXIso`: its degree-`n` term is the module of
  normalized `n`-cochains.
* `TauCeti.hochschildBimoduleNormalizedCochainComplexι`: its inclusion into the Hochschild cochain
  complex, a monomorphism.

## Main results

* `TauCeti.hochschildBimoduleCoboundary_mem_hochschildBimoduleNormalizedCochains`: the coboundary
  of a normalized cochain is normalized.
* `TauCeti.hochschildBimoduleNormalizedCochains_zero`: every `0`-cochain is normalized.
* `TauCeti.hochschildBimoduleCocycles_one_le_hochschildBimoduleNormalizedCochains`: every
  `1`-cocycle is normalized.
* `TauCeti.apply_one_left_eq_op_smul_of_mem_hochschildBimoduleCocycles_two`,
  `TauCeti.apply_one_right_eq_smul_of_mem_hochschildBimoduleCocycles_two`: a `2`-cocycle satisfies
  `ψ(1, b) = ψ(1, 1) b` and `ψ(a, 1) = a ψ(1, 1)`.
* `TauCeti.exists_sub_hochschildBimoduleCoboundary_mem_hochschildBimoduleNormalizedCochains_two`:
  every `2`-cocycle is cohomologous to a normalized one.
* `TauCeti.mem_hochschildBimoduleNormalizedCochains_one_of_hochschildBimoduleCoboundary_mem`: a
  `1`-cochain with normalized coboundary is normalized.
* `hochschildBimoduleCohomology.exists_mem_hochschildBimoduleNormalizedCochains_mk_two_eq`: every
  class in `HH²(A, M)` is the class of a normalized cocycle.
* `hochschildBimoduleCohomology.mk_two_eq_mk_iff_of_mem_hochschildBimoduleNormalizedCochains`: two
  normalized cocycles have the same class in `HH²(A, M)` exactly when they differ by the coboundary
  of a normalized cochain.

## References

* J.-L. Loday, *Cyclic Homology*, §1.5.
-/

public section

noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti

section Cochains

variable (R A M : Type*) [CommSemiring R] [Semiring A] [Module R A] [AddCommMonoid M]
  [Module R M]

/-- The **normalized** Hochschild `n`-cochains with coefficients in the bimodule `M`: the
cochains `ψ : Aⁿ → M` that vanish whenever one of their arguments is `1`. -/
def hochschildBimoduleNormalizedCochains (n : ℕ) : Submodule R ((Fin n → A) →ₘₗ[R] M) where
  carrier := {ψ | ∀ (a : Fin n → A) (i : Fin n), a i = 1 → ψ a = 0}
  add_mem' hψ hφ a i hi := by simp [hψ a i hi, hφ a i hi]
  zero_mem' _ _ _ := rfl
  smul_mem' c ψ hψ a i hi := by simp [hψ a i hi]

variable {R A M}

@[simp]
theorem mem_hochschildBimoduleNormalizedCochains {n : ℕ} {ψ : (Fin n → A) →ₘₗ[R] M} :
    ψ ∈ hochschildBimoduleNormalizedCochains R A M n ↔
      ∀ (a : Fin n → A) (i : Fin n), a i = 1 → ψ a = 0 :=
  Iff.rfl

variable (R A M) in
/-- **Every `0`-cochain is normalized**: a `0`-cochain has no arguments. -/
@[simp]
theorem hochschildBimoduleNormalizedCochains_zero :
    hochschildBimoduleNormalizedCochains R A M 0 = ⊤ :=
  eq_top_iff.2 fun _ _ _ i ↦ i.elim0

end Cochains

/-! ### The coboundary of a normalized cochain -/

section Coboundary

variable {R A M : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [AddCommGroup M]
  [Module R M] [Module A M] [Module Aᵐᵒᵖ M] [IsScalarTower R A M] [IsScalarTower R Aᵐᵒᵖ M]

omit [Module A M] [Module Aᵐᵒᵖ M] [IsScalarTower R A M] [IsScalarTower R Aᵐᵒᵖ M] in
/-- **A normalized cochain vanishes when one of its arguments is a scalar.** -/
theorem apply_eq_zero_of_mem_hochschildBimoduleNormalizedCochains_of_eq_algebraMap {n : ℕ}
    {ψ : (Fin n → A) →ₘₗ[R] M} (hψ : ψ ∈ hochschildBimoduleNormalizedCochains R A M n)
    (a : Fin n → A) (i : Fin n) (r : R) (hi : a i = algebraMap R A r) : ψ a = 0 := by
  have ha : a = Function.update a i (r • 1) := by
    rw [eq_comm, Function.update_eq_self_iff, hi, Algebra.algebraMap_eq_smul_one]
  rw [ha, MultilinearMap.map_update_smul, hψ _ i (Function.update_self i 1 a), smul_zero]

/-- On a tuple with `aⱼ = 1`, a coface of a normalized cochain other than `∂ⱼ` and `∂ⱼ₊₁`
vanishes: it evaluates the cochain on a tuple that still contains `1`. -/
private theorem hochschildBimoduleCoface_apply_eq_zero {n : ℕ} {ψ : (Fin n → A) →ₘₗ[R] M}
    (hψ : ψ ∈ hochschildBimoduleNormalizedCochains R A M n) {a : Fin (n + 1) → A}
    {j : Fin (n + 1)} (hj : a j = 1) (i : Fin (n + 2)) (hi₁ : i ≠ j.castSucc)
    (hi₂ : i ≠ j.succ) : hochschildBimoduleCoface R A M i ψ a = 0 := by
  induction i using Fin.cases with
  | zero =>
    obtain ⟨k, rfl⟩ :=
      Fin.exists_succ_eq.2 (show j ≠ 0 from fun h ↦ hi₁ (by rw [h, Fin.castSucc_zero]))
    rw [hochschildBimoduleCoface_zero_apply, hψ (Fin.tail a) k hj, smul_zero]
  | succ i =>
    induction i using Fin.lastCases with
    | last =>
      obtain ⟨k, rfl⟩ := Fin.exists_castSucc_eq.2
        (show j ≠ Fin.last n from fun h ↦ hi₂ (by rw [h, Fin.succ_last]))
      rw [Fin.succ_last, hochschildBimoduleCoface_last_apply, hψ (Fin.init a) k hj, smul_zero]
    | cast k =>
      rw [hochschildBimoduleCoface_castSucc_succ_apply]
      have h₁ : (j : ℕ) ≠ k + 1 := fun h ↦ hi₁ (Fin.ext (by simp [h]))
      have h₂ : (j : ℕ) ≠ k := fun h ↦ hi₂ (Fin.ext (by simp [h]))
      rcases lt_or_gt_of_ne h₂ with h | h
      · refine hψ _ ⟨j, by omega⟩ ?_
        rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using h)]
        exact hj
      · refine hψ _ ⟨j - 1, by omega⟩ ?_
        rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp; omega)]
        convert hj using 2
        ext
        simp only [Fin.val_succ]
        omega

/-- **The coboundary of a normalized cochain is normalized.** -/
theorem hochschildBimoduleCoboundary_mem_hochschildBimoduleNormalizedCochains {n : ℕ}
    {ψ : (Fin n → A) →ₘₗ[R] M} (hψ : ψ ∈ hochschildBimoduleNormalizedCochains R A M n) :
    hochschildBimoduleCoboundary R A M n ψ ∈
      hochschildBimoduleNormalizedCochains R A M (n + 1) := by
  intro a j hj
  rw [hochschildBimoduleCoboundary_apply,
    Fintype.sum_eq_add j.castSucc j.succ (Fin.castSucc_lt_succ (i := j)).ne fun i hi ↦ by
      rw [hochschildBimoduleCoface_apply_eq_zero hψ hj i hi.1 hi.2, smul_zero],
    hochschildBimoduleCoface_castSucc_apply_eq_succ_apply_of_apply_eq_one ψ hj, Fin.val_castSucc,
    Fin.val_succ, pow_succ, mul_neg_one, neg_smul, add_neg_cancel]

end Coboundary

/-! ### The normalized cochain complex -/

section Complex

variable (R A M : Type*) [CommRing R] [Semiring A] [Algebra R A] [AddCommGroup M]
  [Module R M] [Module A M] [Module Aᵐᵒᵖ M] [IsScalarTower R A M] [IsScalarTower R Aᵐᵒᵖ M]

/-- The Hochschild coboundary restricted to normalized cochains. -/
def hochschildBimoduleNormalizedCoboundary (n : ℕ) :
    hochschildBimoduleNormalizedCochains R A M n →ₗ[R]
      hochschildBimoduleNormalizedCochains R A M (n + 1) :=
  (hochschildBimoduleCoboundary R A M n).restrict fun _ ↦
    hochschildBimoduleCoboundary_mem_hochschildBimoduleNormalizedCochains

variable {R A M} in
@[simp]
theorem coe_hochschildBimoduleNormalizedCoboundary (n : ℕ)
    (ψ : hochschildBimoduleNormalizedCochains R A M n) :
    (hochschildBimoduleNormalizedCoboundary R A M n ψ : (Fin (n + 1) → A) →ₘₗ[R] M) =
      hochschildBimoduleCoboundary R A M n ψ :=
  (rfl)

variable [SMulCommClass A Aᵐᵒᵖ M]

/-- The **normalized Hochschild cochain complex** with coefficients in the bimodule `M`: in degree
`n` the normalized `n`-cochains, with the Hochschild coboundary as differential. -/
def hochschildBimoduleNormalizedCochainComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (hochschildBimoduleNormalizedCochains R A M n))
    (fun n ↦ ModuleCat.ofHom (hochschildBimoduleNormalizedCoboundary R A M n))
    fun _ ↦ ModuleCat.hom_ext <| LinearMap.ext fun _ ↦ Subtype.ext <| by
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        coe_hochschildBimoduleNormalizedCoboundary,
        hochschildBimoduleCoboundary_hochschildBimoduleCoboundary, ModuleCat.hom_zero,
        LinearMap.zero_apply, ZeroMemClass.coe_zero]

/-- The degree-`n` term of the normalized Hochschild cochain complex is the module of normalized
`n`-cochains. -/
def hochschildBimoduleNormalizedCochainComplexXIso (n : ℕ) :
    (hochschildBimoduleNormalizedCochainComplex R A M).X n ≅
      ModuleCat.of R (hochschildBimoduleNormalizedCochains R A M n) :=
  Iso.refl _

/-- Under the identifications `hochschildBimoduleNormalizedCochainComplexXIso`, the differential of
the normalized Hochschild cochain complex is the restricted Hochschild coboundary. -/
@[reassoc, elementwise]
theorem hochschildBimoduleNormalizedCochainComplex_d (n : ℕ) :
    (hochschildBimoduleNormalizedCochainComplex R A M).d n (n + 1) ≫
        (hochschildBimoduleNormalizedCochainComplexXIso R A M (n + 1)).hom =
      (hochschildBimoduleNormalizedCochainComplexXIso R A M n).hom ≫
        ModuleCat.ofHom (hochschildBimoduleNormalizedCoboundary R A M n) := by
  simp [hochschildBimoduleNormalizedCochainComplex, hochschildBimoduleNormalizedCochainComplexXIso]

/-- The inclusion of the normalized Hochschild cochain complex into the Hochschild cochain
complex. -/
def hochschildBimoduleNormalizedCochainComplexι :
    hochschildBimoduleNormalizedCochainComplex R A M ⟶ hochschildBimoduleCochainComplex R A M where
  f n := (hochschildBimoduleNormalizedCochainComplexXIso R A M n).hom ≫
    ModuleCat.ofHom (hochschildBimoduleNormalizedCochains R A M n).subtype ≫
      (hochschildBimoduleCochainComplexXIso R A M n).inv
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [← cancel_mono (hochschildBimoduleCochainComplexXIso R A M (i + 1)).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      hochschildBimoduleCochainComplex_d, Iso.inv_hom_id_assoc,
      hochschildBimoduleNormalizedCochainComplex_d_assoc]
    refine whisker_eq _ (ModuleCat.hom_ext <| LinearMap.ext fun ψ ↦ ?_)
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      Submodule.subtype_apply, coe_hochschildBimoduleNormalizedCoboundary]

/-- Under the identifications `hochschildBimoduleNormalizedCochainComplexXIso` and
`hochschildBimoduleCochainComplexXIso`, the inclusion of normalized cochains is the inclusion of
the submodule of normalized cochains. -/
@[reassoc, elementwise]
theorem hochschildBimoduleNormalizedCochainComplexι_f (n : ℕ) :
    (hochschildBimoduleNormalizedCochainComplexι R A M).f n ≫
        (hochschildBimoduleCochainComplexXIso R A M n).hom =
      (hochschildBimoduleNormalizedCochainComplexXIso R A M n).hom ≫
        ModuleCat.ofHom (hochschildBimoduleNormalizedCochains R A M n).subtype := by
  simp [hochschildBimoduleNormalizedCochainComplexι]

instance mono_hochschildBimoduleNormalizedCochainComplexι :
    Mono (hochschildBimoduleNormalizedCochainComplexι R A M) := by
  refine HomologicalComplex.mono_of_mono_f _ fun n ↦ ?_
  have : Mono (ModuleCat.ofHom (hochschildBimoduleNormalizedCochains R A M n).subtype) :=
    (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
  dsimp only [hochschildBimoduleNormalizedCochainComplexι]
  infer_instance

end Complex

/-! ### Low degrees -/

section LowDegree

variable {R A M : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [AddCommGroup M]
  [Module R M] [Module A M] [Module Aᵐᵒᵖ M] [IsScalarTower R A M] [IsScalarTower R Aᵐᵒᵖ M]

omit [Module A M] [Module Aᵐᵒᵖ M] [IsScalarTower R A M] [IsScalarTower R Aᵐᵒᵖ M] in
/-- A `1`-cochain is normalized exactly when it vanishes at `1`. -/
theorem mem_hochschildBimoduleNormalizedCochains_one_iff (ψ : (Fin 1 → A) →ₘₗ[R] M) :
    ψ ∈ hochschildBimoduleNormalizedCochains R A M 1 ↔ ψ (fun _ ↦ 1) = 0 := by
  refine ⟨fun hψ ↦ hψ _ 0 rfl, fun hψ a i hi ↦ ?_⟩
  rwa [show a = fun _ ↦ 1 from funext fun k ↦ by rw [Subsingleton.elim k i, hi]]

variable (R A M) in
/-- **Every `1`-cocycle is normalized**: a derivation `D` satisfies `D 1 = D 1 + D 1`. -/
theorem hochschildBimoduleCocycles_one_le_hochschildBimoduleNormalizedCochains :
    hochschildBimoduleCocycles R A M 1 ≤ hochschildBimoduleNormalizedCochains R A M 1 := by
  intro ψ hψ
  rw [mem_hochschildBimoduleCocycles_one_iff] at hψ
  have h := hψ 1 1
  simp only [mul_one, one_smul, op_one, left_eq_add] at h
  exact (mem_hochschildBimoduleNormalizedCochains_one_iff ψ).2 h

/-- **A `1`-cochain with normalized coboundary is normalized**: `(δφ)(1, 1) = φ 1`. -/
theorem mem_hochschildBimoduleNormalizedCochains_one_of_hochschildBimoduleCoboundary_mem
    {φ : (Fin 1 → A) →ₘₗ[R] M}
    (h : hochschildBimoduleCoboundary R A M 1 φ ∈ hochschildBimoduleNormalizedCochains R A M 2) :
    φ ∈ hochschildBimoduleNormalizedCochains R A M 1 := by
  obtain ⟨f, rfl⟩ := (MultilinearMap.ofSubsingleton (RingHom.id R) A M (0 : Fin 1)).surjective φ
  have h₁ := h (fun _ ↦ 1) 0 rfl
  rw [hochschildBimoduleCoboundary_ofSubsingleton] at h₁
  simp only [mul_one, one_smul, op_one, sub_self, zero_add] at h₁
  rw [mem_hochschildBimoduleNormalizedCochains_one_iff]
  simpa using h₁

/-- **The left unit identity of a `2`-cocycle**: the cocycle identity at `(1, 1, b)` gives
`ψ(1, b) = ψ(1, 1) b`. -/
theorem apply_one_left_eq_op_smul_of_mem_hochschildBimoduleCocycles_two
    {ψ : (Fin 2 → A) →ₘₗ[R] M} (hψ : ψ ∈ hochschildBimoduleCocycles R A M 2) (b : A) :
    ψ ![1, b] = op b • ψ ![1, 1] := by
  have h := (mem_hochschildBimoduleCocycles_two_iff ψ).1 hψ 1 1 b
  rwa [one_smul, mul_one, one_mul, sub_add_cancel, sub_eq_zero] at h

/-- **The right unit identity of a `2`-cocycle**: the cocycle identity at `(a, 1, 1)` gives
`ψ(a, 1) = a ψ(1, 1)`. -/
theorem apply_one_right_eq_smul_of_mem_hochschildBimoduleCocycles_two
    {ψ : (Fin 2 → A) →ₘₗ[R] M} (hψ : ψ ∈ hochschildBimoduleCocycles R A M 2) (a : A) :
    ψ ![a, 1] = a • ψ ![1, 1] := by
  have h := (mem_hochschildBimoduleCocycles_two_iff ψ).1 hψ a 1 1
  rw [op_one, one_smul, mul_one, mul_one, sub_add_cancel, sub_eq_zero] at h
  exact h.symm

/-- **Every `2`-cocycle is cohomologous to a normalized one**: for a `2`-cocycle `ψ`, the cocycle
`ψ - δφ` is normalized, where `φ a = a ψ(1, 1)`. -/
theorem exists_sub_hochschildBimoduleCoboundary_mem_hochschildBimoduleNormalizedCochains_two
    {ψ : (Fin 2 → A) →ₘₗ[R] M} (hψ : ψ ∈ hochschildBimoduleCocycles R A M 2) :
    ∃ φ : (Fin 1 → A) →ₘₗ[R] M,
      ψ - hochschildBimoduleCoboundary R A M 1 φ ∈
        hochschildBimoduleNormalizedCochains R A M 2 := by
  refine ⟨MultilinearMap.ofSubsingleton (RingHom.id R) A M 0
    (LinearMap.id.smulRight (ψ ![1, 1])), fun a i hi ↦ ?_⟩
  rw [show a = ![a 0, a 1] from (FinVec.etaExpand_eq a).symm, sub_apply,
    hochschildBimoduleCoboundary_ofSubsingleton]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue] at hi
    rw [hi, apply_one_left_eq_op_smul_of_mem_hochschildBimoduleCocycles_two hψ]
    simp
  · simp only [Fin.mk_one, Fin.isValue] at hi
    rw [hi, apply_one_right_eq_smul_of_mem_hochschildBimoduleCocycles_two hψ]
    simp

end LowDegree

/-! ### Cohomology in degree two -/

namespace hochschildBimoduleCohomology

variable {R A M : Type*} [CommRing R] [Semiring A] [Algebra R A] [AddCommGroup M]
  [Module R M] [Module A M] [Module Aᵐᵒᵖ M] [IsScalarTower R A M] [IsScalarTower R Aᵐᵒᵖ M]
  [SMulCommClass A Aᵐᵒᵖ M]

/-- **Every class in `HH²(A, M)` is the class of a normalized cocycle.** -/
theorem exists_mem_hochschildBimoduleNormalizedCochains_mk_two_eq
    (x : hochschildBimoduleCohomology R A M 2) :
    ∃ ψ : hochschildBimoduleCocycles R A M 2,
      (ψ : (Fin 2 → A) →ₘₗ[R] M) ∈ hochschildBimoduleNormalizedCochains R A M 2 ∧
        mk R A M 2 ψ = x := by
  obtain ⟨ψ, rfl⟩ := mk_surjective R A M 2 x
  obtain ⟨φ, hφ⟩ :=
    exists_sub_hochschildBimoduleCoboundary_mem_hochschildBimoduleNormalizedCochains_two ψ.property
  have hmem : (ψ : (Fin 2 → A) →ₘₗ[R] M) - hochschildBimoduleCoboundary R A M 1 φ ∈
      hochschildBimoduleCocycles R A M 2 :=
    sub_mem ψ.property (hochschildBimoduleCoboundaries_le_hochschildBimoduleCocycles R A M 2
      (mem_hochschildBimoduleCoboundaries_succ_iff.2 ⟨φ, rfl⟩))
  refine ⟨⟨_, hmem⟩, hφ, (mk_eq_mk_iff R A M 2 _ _).2 ?_⟩
  rw [show (ψ : (Fin 2 → A) →ₘₗ[R] M) - hochschildBimoduleCoboundary R A M 1 φ - ψ =
    -hochschildBimoduleCoboundary R A M 1 φ by abel]
  exact neg_mem (mem_hochschildBimoduleCoboundaries_succ_iff.2 ⟨φ, rfl⟩)

/-- **Two normalized `2`-cocycles have the same class in `HH²(A, M)` exactly when they differ by
the coboundary of a normalized `1`-cochain.** -/
theorem mk_two_eq_mk_iff_of_mem_hochschildBimoduleNormalizedCochains
    (ψ φ : hochschildBimoduleCocycles R A M 2)
    (hψ : (ψ : (Fin 2 → A) →ₘₗ[R] M) ∈ hochschildBimoduleNormalizedCochains R A M 2)
    (hφ : (φ : (Fin 2 → A) →ₘₗ[R] M) ∈ hochschildBimoduleNormalizedCochains R A M 2) :
    mk R A M 2 ψ = mk R A M 2 φ ↔
      ∃ θ ∈ hochschildBimoduleNormalizedCochains R A M 1,
        hochschildBimoduleCoboundary R A M 1 θ = ψ - φ := by
  rw [mk_eq_mk_iff, mem_hochschildBimoduleCoboundaries_succ_iff]
  refine ⟨fun ⟨θ, hθ⟩ ↦ ⟨θ, ?_, hθ⟩, fun ⟨θ, _, hθ⟩ ↦ ⟨θ, hθ⟩⟩
  refine mem_hochschildBimoduleNormalizedCochains_one_of_hochschildBimoduleCoboundary_mem ?_
  rw [hθ]
  exact sub_mem hψ hφ

end hochschildBimoduleCohomology

end TauCeti
