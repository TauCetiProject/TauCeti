/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.HochschildCohomology.Bimodule

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

In degrees at most two the inclusion induces a bijection on cohomology. Every cochain of degree
zero is normalized, and so is every cocycle of degree one: a derivation `D` has
`D 1 = D (1 * 1) = 2 D 1`. Every `2`-cocycle `ψ` is cohomologous to a normalized one: the cocycle
identity gives `ψ(1, b) = ψ(1, 1) b` and `ψ(a, 1) = a ψ(1, 1)`, so `ψ` minus the coboundary of
`a ↦ a ψ(1, 1)` is normalized. A `1`-cochain whose coboundary is normalized is normalized, since
`(δφ)(1, 1) = φ 1`. Whether the inclusion is a quasi-isomorphism in every degree is not addressed
here.

## Main definitions

* `TauCeti.hochschildBimoduleNormalizedCochains`: the normalized `n`-cochains.
* `TauCeti.hochschildBimoduleNormalizedCoboundary`: the Hochschild coboundary restricted to
  normalized cochains.
* `TauCeti.hochschildBimoduleNormalizedCochainComplex`: the normalized Hochschild cochain complex.
* `TauCeti.hochschildBimoduleNormalizedCochainComplexι`: its inclusion into the Hochschild cochain
  complex, a monomorphism.

## Main results

* `TauCeti.hochschildBimoduleCoboundary_mem_hochschildBimoduleNormalizedCochains`: the coboundary
  of a normalized cochain is normalized.
* `TauCeti.hochschildBimoduleNormalizedCochains_zero`: every `0`-cochain is normalized.
* `TauCeti.hochschildBimoduleCocycles_one_le_hochschildBimoduleNormalizedCochains`: every
  `1`-cocycle is normalized.
* `TauCeti.exists_sub_hochschildBimoduleCoboundary_mem_hochschildBimoduleNormalizedCochains_two`:
  every `2`-cocycle is cohomologous to a normalized one.
* `TauCeti.mem_hochschildBimoduleNormalizedCochains_one_of_hochschildBimoduleCoboundary_mem`: a
  `1`-cochain with normalized coboundary is normalized.
* `TauCeti.hochschildBimoduleCohomology.exists_mk_eq_of_mem_normalized_two` and
  `TauCeti.hochschildBimoduleCohomology.mk_eq_mk_iff_of_mem_normalized_two`: every class in
  `HH²(A, M)` is the class of a normalized cocycle, and two normalized cocycles have the same class
  exactly when they differ by the coboundary of a normalized cochain.

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

omit [AddCommGroup M] [Module R M] [Module A M] [Module Aᵐᵒᵖ M] [IsScalarTower R A M]
  [IsScalarTower R Aᵐᵒᵖ M] in
/-- Contracting `aₚ aₚ₊₁` in a tuple with `aₚ₊₁ = 1` removes the entry `aₚ₊₁`. -/
private theorem contractNth_castSucc_eq_removeNth_succ {n : ℕ} (a : Fin (n + 1) → A) (p : Fin n)
    (h : a p.succ = 1) : Fin.contractNth p.castSucc (· * ·) a = Fin.removeNth p.succ a := by
  ext m
  rw [Fin.removeNth]
  rcases lt_trichotomy (m : ℕ) p with hm | hm | hm
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using hm),
      Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simp; omega)]
  · have hmp : m.succ = p.succ := Fin.ext (by simp [hm])
    rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simpa using hm), hmp, h, mul_one,
      Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simp; omega)]
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using hm),
      Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)]

omit [AddCommGroup M] [Module R M] [Module A M] [Module Aᵐᵒᵖ M] [IsScalarTower R A M]
  [IsScalarTower R Aᵐᵒᵖ M] in
/-- Contracting `aₚ aₚ₊₁` in a tuple with `aₚ = 1` removes the entry `aₚ`. -/
private theorem contractNth_castSucc_eq_removeNth_castSucc {n : ℕ} (a : Fin (n + 1) → A)
    (p : Fin n) (h : a p.castSucc = 1) :
    Fin.contractNth p.castSucc (· * ·) a = Fin.removeNth p.castSucc a := by
  ext m
  rw [Fin.removeNth]
  rcases lt_trichotomy (m : ℕ) p with hm | hm | hm
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using hm),
      Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simp; omega)]
  · have hmp : m.castSucc = p.castSucc := Fin.ext (by simp [hm])
    rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simpa using hm), hmp, h, one_mul,
      Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)]
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using hm),
      Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)]

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

/-- On a tuple with `aⱼ = 1`, the cofaces `∂ⱼ` and `∂ⱼ₊₁` agree: both evaluate the cochain on the
tuple with `aⱼ` removed. -/
private theorem hochschildBimoduleCoface_castSucc_apply_eq {n : ℕ} (ψ : (Fin n → A) →ₘₗ[R] M)
    {a : Fin (n + 1) → A} {j : Fin (n + 1)} (hj : a j = 1) :
    hochschildBimoduleCoface R A M j.castSucc ψ a = hochschildBimoduleCoface R A M j.succ ψ a := by
  induction j using Fin.cases with
  | zero =>
    rw [Fin.castSucc_zero, hochschildBimoduleCoface_zero_apply, hj, one_smul]
    cases n with
    | zero =>
      rw [show Fin.succ (0 : Fin 1) = Fin.last 1 from rfl, hochschildBimoduleCoface_last_apply,
        show Fin.last 0 = (0 : Fin 1) from rfl, hj, op_one, one_smul]
      exact congrArg ψ (funext fun i ↦ i.elim0)
    | succ n =>
      rw [show Fin.succ (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc.succ from rfl,
        hochschildBimoduleCoface_castSucc_succ_apply,
        contractNth_castSucc_eq_removeNth_castSucc a 0 hj, Fin.castSucc_zero, Fin.removeNth_zero]
  | succ k =>
    rw [← Fin.succ_castSucc, hochschildBimoduleCoface_castSucc_succ_apply,
      contractNth_castSucc_eq_removeNth_succ a k hj]
    cases n with
    | zero => exact k.elim0
    | succ n =>
      induction k using Fin.lastCases with
      | last =>
        rw [Fin.succ_last] at hj ⊢
        rw [Fin.succ_last, hochschildBimoduleCoface_last_apply, hj, op_one, one_smul,
          Fin.removeNth_last]
      | cast l =>
        rw [Fin.succ_castSucc] at hj ⊢
        rw [hochschildBimoduleCoface_castSucc_succ_apply,
          contractNth_castSucc_eq_removeNth_castSucc a l.succ hj]

/-- **The coboundary of a normalized cochain is normalized.** -/
theorem hochschildBimoduleCoboundary_mem_hochschildBimoduleNormalizedCochains {n : ℕ}
    {ψ : (Fin n → A) →ₘₗ[R] M} (hψ : ψ ∈ hochschildBimoduleNormalizedCochains R A M n) :
    hochschildBimoduleCoboundary R A M n ψ ∈
      hochschildBimoduleNormalizedCochains R A M (n + 1) := by
  intro a j hj
  rw [hochschildBimoduleCoboundary_apply,
    Fintype.sum_eq_add j.castSucc j.succ (Fin.castSucc_lt_succ (i := j)).ne fun i hi ↦ by
      rw [hochschildBimoduleCoface_apply_eq_zero hψ hj i hi.1 hi.2, smul_zero],
    hochschildBimoduleCoface_castSucc_apply_eq ψ hj, Fin.val_castSucc, Fin.val_succ, pow_succ,
    mul_neg_one, neg_smul, add_neg_cancel]

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
abbrev hochschildBimoduleNormalizedCochainComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (hochschildBimoduleNormalizedCochains R A M n))
    (fun n ↦ ModuleCat.ofHom (hochschildBimoduleNormalizedCoboundary R A M n))
    fun _ ↦ ModuleCat.hom_ext <| LinearMap.ext fun _ ↦ Subtype.ext <| by
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        coe_hochschildBimoduleNormalizedCoboundary,
        hochschildBimoduleCoboundary_hochschildBimoduleCoboundary, ModuleCat.hom_zero,
        LinearMap.zero_apply, ZeroMemClass.coe_zero]

/-- The differential of the normalized Hochschild cochain complex is the restricted Hochschild
coboundary. -/
theorem hochschildBimoduleNormalizedCochainComplex_d (n : ℕ) :
    (hochschildBimoduleNormalizedCochainComplex R A M).d n (n + 1) =
      ModuleCat.ofHom (hochschildBimoduleNormalizedCoboundary R A M n) :=
  CochainComplex.of_d (fun n ↦ ModuleCat.of R (hochschildBimoduleNormalizedCochains R A M n))
    (fun n ↦ ModuleCat.ofHom (hochschildBimoduleNormalizedCoboundary R A M n)) n

/-- The inclusion of the normalized Hochschild cochain complex into the Hochschild cochain
complex. -/
def hochschildBimoduleNormalizedCochainComplexι :
    hochschildBimoduleNormalizedCochainComplex R A M ⟶ hochschildBimoduleCochainComplex R A M where
  f n := ModuleCat.ofHom (hochschildBimoduleNormalizedCochains R A M n).subtype ≫
    (hochschildBimoduleCochainComplexXIso R A M n).inv
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [hochschildBimoduleNormalizedCochainComplex_d, ← cancel_mono
      (hochschildBimoduleCochainComplexXIso R A M (i + 1)).hom, Category.assoc, Category.assoc,
      hochschildBimoduleCochainComplex_d, Iso.inv_hom_id_assoc]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl

/-- The inclusion of normalized cochains is the identity on underlying cochains. -/
@[simp]
theorem hochschildBimoduleCochainComplexXIso_hom_hochschildBimoduleNormalizedCochainComplexι_f
    (n : ℕ) (ψ : hochschildBimoduleNormalizedCochains R A M n) :
    (hochschildBimoduleCochainComplexXIso R A M n).hom
        ((hochschildBimoduleNormalizedCochainComplexι R A M).f n ψ) = ψ := by
  simp [hochschildBimoduleNormalizedCochainComplexι]

instance mono_hochschildBimoduleNormalizedCochainComplexι :
    Mono (hochschildBimoduleNormalizedCochainComplexι R A M) := by
  refine HomologicalComplex.mono_of_mono_f _ fun n ↦ ?_
  have : Mono (ModuleCat.ofHom (hochschildBimoduleNormalizedCochains R A M n).subtype) :=
    (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
  exact mono_comp _ _

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

/-- The Hochschild coboundary of a `2`-cochain, in explicit form:
`(δψ)(a, b, c) = a ψ(b, c) - ψ(ab, c) + ψ(a, bc) - ψ(a, b) c`. -/
private theorem hochschildBimoduleCoboundary_two_apply (ψ : (Fin 2 → A) →ₘₗ[R] M) (a b c : A) :
    hochschildBimoduleCoboundary R A M 2 ψ ![a, b, c] =
      a • ψ ![b, c] - ψ ![a * b, c] + ψ ![a, b * c] - op c • ψ ![a, b] := by
  rw [hochschildBimoduleCoboundary_apply_eq_add_sum_add, Fin.sum_univ_two]
  have h₀ : Fin.contractNth (0 : Fin 2).castSucc (· * ·) ![a, b, c] = ![a * b, c] := by
    ext i
    fin_cases i <;> rfl
  have h₁ : Fin.contractNth (1 : Fin 2).castSucc (· * ·) ![a, b, c] = ![a, b * c] := by
    ext i
    fin_cases i <;> rfl
  have ht : Fin.tail ![a, b, c] = ![b, c] := rfl
  have hi : Fin.init ![a, b, c] = ![a, b] := by
    ext i
    fin_cases i <;> rfl
  rw [h₀, h₁, ht, hi]
  simp only [Matrix.cons_val_zero, Fin.val_zero, zero_add, pow_one, neg_smul, one_smul,
    Fin.val_one, Fin.last, Matrix.cons_val, Fin.reduceFinMk]
  norm_num
  abel

omit [Semiring A] in
/-- The tuple `a : Fin 2 → A` as `![a 0, a 1]`. -/
private theorem eq_vecCons_two (a : Fin 2 → A) : a = ![a 0, a 1] := by
  ext i
  fin_cases i <;> rfl

/-- **Every `2`-cocycle is cohomologous to a normalized one**: for a `2`-cocycle `ψ`, the cocycle
`ψ - δφ` is normalized, where `φ a = a ψ(1, 1)`. -/
theorem exists_sub_hochschildBimoduleCoboundary_mem_hochschildBimoduleNormalizedCochains_two
    {ψ : (Fin 2 → A) →ₘₗ[R] M} (hψ : ψ ∈ hochschildBimoduleCocycles R A M 2) :
    ∃ φ : (Fin 1 → A) →ₘₗ[R] M,
      ψ - hochschildBimoduleCoboundary R A M 1 φ ∈
        hochschildBimoduleNormalizedCochains R A M 2 := by
  rw [mem_hochschildBimoduleCocycles_iff] at hψ
  set m := ψ ![1, 1]
  refine ⟨MultilinearMap.ofSubsingleton (RingHom.id R) A M 0 (LinearMap.id.smulRight m), ?_⟩
  -- the cocycle identity at `(1, 1, b)` and `(a, 1, 1)`
  have hl (b : A) : ψ ![1, b] = op b • m := by
    have h := congrArg (fun f ↦ f ![1, 1, b]) hψ
    simp only [hochschildBimoduleCoboundary_two_apply, one_smul, mul_one, one_mul,
      zero_apply] at h
    rwa [sub_add_cancel, sub_eq_zero] at h
  have hr (a : A) : ψ ![a, 1] = a • m := by
    have h := congrArg (fun f ↦ f ![a, 1, 1]) hψ
    simp only [hochschildBimoduleCoboundary_two_apply, op_one, one_smul, mul_one,
      zero_apply] at h
    rw [sub_add_cancel, sub_eq_zero] at h
    exact h.symm
  intro a i hi
  rw [eq_vecCons_two a, sub_apply, hochschildBimoduleCoboundary_ofSubsingleton]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue] at hi
    simp [hi, hl]
  · simp only [Fin.mk_one, Fin.isValue] at hi
    simp [hi, hr]

end LowDegree

/-! ### Cohomology in degree two -/

namespace hochschildBimoduleCohomology

variable {R A M : Type*} [CommRing R] [Semiring A] [Algebra R A] [AddCommGroup M]
  [Module R M] [Module A M] [Module Aᵐᵒᵖ M] [IsScalarTower R A M] [IsScalarTower R Aᵐᵒᵖ M]
  [SMulCommClass A Aᵐᵒᵖ M]

/-- **Every class in `HH²(A, M)` is the class of a normalized cocycle.** -/
theorem exists_mk_eq_of_mem_normalized_two (x : hochschildBimoduleCohomology R A M 2) :
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
theorem mk_eq_mk_iff_of_mem_normalized_two (ψ φ : hochschildBimoduleCocycles R A M 2)
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
