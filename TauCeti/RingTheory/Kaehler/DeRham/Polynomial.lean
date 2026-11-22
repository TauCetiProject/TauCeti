/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import TauCeti.RingTheory.Kaehler.DeRham.Basic
public import TauCeti.RingTheory.Kaehler.DeRham.LieDerivative
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import TauCeti.RingTheory.Kaehler.MvPolynomial

/-!
# Algebraic de Rham coordinate formulas and support over multivariate polynomial algebras

Over a multivariate polynomial ring `MvPolynomial σ R` (for an arbitrary, possibly infinite
variable set `σ`), the universal Kähler differential `D R (MvPolynomial σ R) p` expands in terms
of formal partial derivatives (`KaehlerDifferential.mvPolynomial_D_apply_eq_sum_vars`). This file
transfers those coordinate formulas to the algebraic exterior derivative
`TauCeti.KaehlerDeRham.extDeriv` on `ExteriorAlgebra (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R]`.

In addition, for any commutative ring `B`, `TauCeti.KaehlerDeRham.supportedForms B s` defines the
`B`-subalgebra of forms supported on a set `s : Set σ` of variables. Both `extDeriv` and the grade
involution preserve each `supportedForms B s`, while `Derivation.deRhamLieDeriv` maps forms
supported on `s` to forms supported on `t ⊇ s` whenever the underlying derivation maps polynomials
supported on `s` into those supported on `t`.

## Main definitions

* `TauCeti.KaehlerDeRham.supportedForms`: the subalgebra of polynomial forms supported on a set of
  variables.

## Main results

* `TauCeti.KaehlerDeRham.extDeriv_algebraMap_mvPolynomial_eq_sum_vars`:
  `d p = ∑ i ∈ p.vars, MvPolynomial.pderiv i p • ι (D (X i))` for arbitrary `σ`.
* `TauCeti.KaehlerDeRham.extDeriv_algebraMap_mvPolynomial`:
  `d p = ∑ i : σ, MvPolynomial.pderiv i p • ι (D (X i))` when `[Fintype σ]`.
* `TauCeti.KaehlerDeRham.extDeriv_smul_eq_sum_vars_of_extDeriv_eq_zero`:
  for any closed form `x` (`extDeriv R (MvPolynomial σ R) x = 0`),
  `d (p • x) = ∑ j ∈ p.vars, MvPolynomial.pderiv j p • (ι (D (X j)) * x)`.
* `TauCeti.KaehlerDeRham.algebraMap_mem_supportedForms_iff`,
  `TauCeti.KaehlerDeRham.ι_D_X_mem_supportedForms_iff`: membership characterizations for zero-forms
  and coordinate one-forms in `supportedForms`.
* `TauCeti.KaehlerDeRham.extDeriv_mem_supportedForms`,
  `TauCeti.KaehlerDeRham.deRhamLieDeriv_mem_supportedForms`, and
  `TauCeti.KaehlerDeRham.exists_finset_mem_supportedForms`: variable-support preservation and
  finiteness.
-/

public section

namespace TauCeti.KaehlerDeRham

section CoordinateFormulas

variable {R σ : Type*} [CommRing R]

/-- Over a multivariate polynomial ring `MvPolynomial σ R` (with `σ` possibly infinite), the
algebraic exterior derivative of a polynomial `p` is the finite sum over `p.vars` of its formal
partial derivatives wedged with the coordinate differentials `D (X i)`. -/
theorem extDeriv_algebraMap_mvPolynomial_eq_sum_vars (p : MvPolynomial σ R) :
    extDeriv R (MvPolynomial σ R)
        (algebraMap (MvPolynomial σ R) (ExteriorAlgebra (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R])
          p) =
      ∑ i ∈ p.vars,
        MvPolynomial.pderiv i p •
          ExteriorAlgebra.ι (MvPolynomial σ R)
            (KaehlerDifferential.D R (MvPolynomial σ R) (MvPolynomial.X i)) := by
  rw [extDeriv_algebraMap, KaehlerDifferential.mvPolynomial_D_apply_eq_sum_vars, map_sum]
  simp only [LinearMap.map_smul]

/-- Over a multivariate polynomial ring on a finite variable set `σ`, the exterior derivative of `p`
is `∑ i : σ, MvPolynomial.pderiv i p • ι (D (X i))`. -/
theorem extDeriv_algebraMap_mvPolynomial [Fintype σ] (p : MvPolynomial σ R) :
    extDeriv R (MvPolynomial σ R)
        (algebraMap (MvPolynomial σ R) (ExteriorAlgebra (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R])
          p) =
      ∑ i : σ,
        MvPolynomial.pderiv i p •
          ExteriorAlgebra.ι (MvPolynomial σ R)
            (KaehlerDifferential.D R (MvPolynomial σ R) (MvPolynomial.X i)) := by
  rw [extDeriv_algebraMap, KaehlerDifferential.mvPolynomial_D_apply, map_sum]
  simp only [LinearMap.map_smul]

/-- Coordinate formula for `extDeriv` on `p • x` for any closed form `x`
(`extDeriv R (MvPolynomial σ R) x = 0`) over `MvPolynomial σ R`, valid without finiteness
hypotheses on `σ`. -/
theorem extDeriv_smul_eq_sum_vars_of_extDeriv_eq_zero (p : MvPolynomial σ R)
    {x : ExteriorAlgebra (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R]}
    (hx : extDeriv R (MvPolynomial σ R) x = 0) :
    extDeriv R (MvPolynomial σ R) (p • x) =
      ∑ j ∈ p.vars,
        MvPolynomial.pderiv j p •
          (ExteriorAlgebra.ι (MvPolynomial σ R)
              (KaehlerDifferential.D R (MvPolynomial σ R) (MvPolynomial.X j)) * x) := by
  rw [extDeriv_smul, hx, smul_zero, add_zero, ← extDeriv_algebraMap,
    extDeriv_algebraMap_mvPolynomial_eq_sum_vars, Finset.sum_mul]
  simp only [smul_mul_assoc]

end CoordinateFormulas

section SupportedForms

open _root_.ExteriorAlgebra _root_.KaehlerDifferential MvPolynomial

noncomputable section

variable (B : Type*) [CommRing B] {σ : Type*}

/-- The `B`-subalgebra of polynomial differential forms supported on a set `s` of variables,
generated by polynomials in `MvPolynomial.supported B s` and coordinate one-forms `dXᵢ` with
`i ∈ s`. -/
def supportedForms (s : Set σ) :
    Subalgebra B (ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) :=
  Algebra.adjoin B
    ((algebraMap (MvPolynomial σ B) _ '' (MvPolynomial.supported B s : Set (MvPolynomial σ B))) ∪
      ((fun i ↦ ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) (X i))) '' s))

variable {B}

/-- `supportedForms B s` is the `B`-subalgebra generated by zero-forms supported on `s` and
coordinate one-forms `dXᵢ` for `i ∈ s`. -/
theorem supportedForms_eq_adjoin (s : Set σ) :
    supportedForms B s = Algebra.adjoin B
      ((algebraMap (MvPolynomial σ B) _ ''
          (MvPolynomial.supported B s : Set (MvPolynomial σ B))) ∪
        ((fun i ↦
          ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) (X i))) '' s)) := by
  rfl

/-- Enlarging the set of allowed variables enlarges the subalgebra of supported forms. -/
theorem supportedForms_mono : Monotone (supportedForms B (σ := σ)) := by
  intro s t hst
  refine Algebra.adjoin_mono (Set.union_subset_union ?_ (Set.image_mono hst))
  exact Set.image_mono (MvPolynomial.supported_mono hst)

/-- A zero-form whose polynomial is supported on `s` belongs to `supportedForms B s`. -/
theorem algebraMap_mem_supportedForms {s : Set σ} {p : MvPolynomial σ B}
    (hp : p ∈ MvPolynomial.supported B s) :
    algebraMap (MvPolynomial σ B)
        (ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) p ∈
      supportedForms B s :=
  Algebra.subset_adjoin (Or.inl ⟨p, hp, rfl⟩)

/-- A coordinate one-form `dXᵢ` with `i ∈ s` belongs to `supportedForms B s`. -/
theorem ι_D_X_mem_supportedForms {s : Set σ} {i : σ} (hi : i ∈ s) :
    ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) (X i)) ∈
      supportedForms B s :=
  Algebra.subset_adjoin (Or.inr ⟨i, hi, rfl⟩)

/-- A polynomial zero-form belongs to `supportedForms B s` if and only if the polynomial is
supported on `s`. -/
theorem algebraMap_mem_supportedForms_iff {s : Set σ} {p : MvPolynomial σ B} :
    algebraMap (MvPolynomial σ B)
        (ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) p ∈
      supportedForms B s ↔ p ∈ MvPolynomial.supported B s := by
  refine ⟨fun hp ↦ ?_, algebraMap_mem_supportedForms⟩
  let π : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B]) →ₐ[MvPolynomial σ B]
      MvPolynomial σ B :=
    _root_.ExteriorAlgebra.lift (MvPolynomial σ B) ⟨0, fun _ ↦ by simp⟩
  have hmem : ∀ α ∈ supportedForms B s, π α ∈ MvPolynomial.supported B s := by
    intro α hα
    induction hα using Algebra.adjoin_induction with
    | mem _ hx =>
      rcases hx with ⟨q, hq, rfl⟩ | ⟨i, _, rfl⟩
      · simpa [π] using hq
      · simp [π]
    | algebraMap b =>
      rw [IsScalarTower.algebraMap_apply B (MvPolynomial σ B) _ b, AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ b
    | add _ _ _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
    | mul _ _ _ _ hx hy =>
      rw [map_mul]
      exact mul_mem hx hy
  simpa [π] using hmem _ hp

/-- Over a nontrivial coefficient ring `B`, a coordinate one-form `dXᵢ` belongs to
`supportedForms B s` if and only if `i ∈ s`. -/
@[simp]
theorem ι_D_X_mem_supportedForms_iff [Nontrivial B] {s : Set σ} {i : σ} :
    ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) (X i)) ∈
      supportedForms B s ↔ i ∈ s := by
  classical
  refine ⟨fun hi ↦ ?_, ι_D_X_mem_supportedForms⟩
  by_contra his
  let f : Ω[MvPolynomial σ B⁄B] →ₗ[MvPolynomial σ B]
      TrivSqZeroExt (MvPolynomial σ B) (MvPolynomial σ B) :=
    (TrivSqZeroExt.inrHom (MvPolynomial σ B) (MvPolynomial σ B)).comp
      ((KaehlerDifferential.mvPolynomialBasis B σ).coord i)
  let ψ : ExteriorAlgebra (MvPolynomial σ B) Ω[MvPolynomial σ B⁄B] →ₐ[MvPolynomial σ B]
      TrivSqZeroExt (MvPolynomial σ B) (MvPolynomial σ B) :=
    _root_.ExteriorAlgebra.lift (MvPolynomial σ B) ⟨f, fun ω ↦ by
      change f ω * f ω = 0
      simp [f]⟩
  have hmem : ∀ α ∈ supportedForms B s, (ψ α).snd = 0 := by
    intro α hα
    induction hα using Algebra.adjoin_induction with
    | mem _ hx =>
      rcases hx with ⟨p, _, rfl⟩ | ⟨j, hj, rfl⟩
      · rw [AlgHom.commutes, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]
      · have hji : j ≠ i := fun h ↦ his (h ▸ hj)
        simp [ψ, f, hji]
    | algebraMap b =>
      rw [IsScalarTower.algebraMap_apply B (MvPolynomial σ B) _ b, AlgHom.commutes,
        TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]
    | add _ _ _ _ hx hy =>
      rw [map_add, TrivSqZeroExt.snd_add, hx, hy, add_zero]
    | mul _ _ _ _ hx hy =>
      rw [map_mul, TrivSqZeroExt.snd_mul, hx, hy, smul_zero, smul_zero, add_zero]
  have h1 : (ψ (ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) (X i)))).snd =
      0 :=
    hmem _ hi
  have h2 : (ψ (ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) (X i)))).snd =
      1 := by
    simp [ψ, f]
  exact one_ne_zero (h2.symm.trans h1)

/-- A polynomial multiple of a form in `supportedForms B s` stays in `supportedForms B s` when
the polynomial is supported on `s`. -/
theorem smul_mem_supportedForms {s : Set σ} {p : MvPolynomial σ B}
    (hp : p ∈ MvPolynomial.supported B s)
    {α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])}
    (hα : α ∈ supportedForms B s) : p • α ∈ supportedForms B s := by
  rw [Algebra.smul_def]
  exact mul_mem (algebraMap_mem_supportedForms hp) hα

/-- The differential of a polynomial supported on `s` belongs to `supportedForms B s`. -/
theorem ι_D_mem_supportedForms {s : Set σ} {p : MvPolynomial σ B}
    (hp : p ∈ MvPolynomial.supported B s) :
    ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) p) ∈
      supportedForms B s := by
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact ι_D_X_mem_supportedForms hi
  | algebraMap b => simp
  | add x y _ _ hx hy =>
    rw [map_add, map_add]
    exact add_mem hx hy
  | mul x y hx hy ihx ihy =>
    rw [Derivation.leibniz, map_add, _root_.map_smul, _root_.map_smul]
    exact add_mem (smul_mem_supportedForms hx ihy) (smul_mem_supportedForms hy ihx)

/-- The grade involution preserves `supportedForms B s`. -/
theorem involute_mem_supportedForms {s : Set σ}
    {α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])}
    (hα : α ∈ supportedForms B s) :
    CliffordAlgebra.involute (Q := (0 : QuadraticForm (MvPolynomial σ B) _)) α ∈
      supportedForms B s := by
  let inv : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B]) →ₐ[B]
      ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B]) :=
    (CliffordAlgebra.involute (Q := (0 : QuadraticForm (MvPolynomial σ B) _))).restrictScalars B
  have hle : (supportedForms B s).map inv ≤ supportedForms B s := by
    rw [supportedForms, AlgHom.map_adjoin, Algebra.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with ⟨p, hp, rfl⟩ | ⟨i, hi, rfl⟩
    · simp only [inv, AlgHom.coe_restrictScalars', AlgHom.commutes]
      exact algebraMap_mem_supportedForms hp
    · simp only [inv, AlgHom.coe_restrictScalars', CliffordAlgebra.involute_ι]
      exact neg_mem (ι_D_X_mem_supportedForms hi)
  exact hle ⟨α, hα, rfl⟩

/-- The algebraic exterior derivative preserves every supported-form subalgebra. -/
theorem extDeriv_mem_supportedForms {s : Set σ}
    {α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])}
    (hα : α ∈ supportedForms B s) :
    extDeriv B (MvPolynomial σ B) α ∈ supportedForms B s := by
  induction hα using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨p, hp, rfl⟩ | ⟨i, _, rfl⟩
    · rw [extDeriv_algebraMap]
      exact ι_D_mem_supportedForms hp
    · rw [extDeriv_ι_D]
      exact zero_mem _
  | algebraMap b =>
    rw [extDeriv_algebraMap_base]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mul x y hx hy ihx ihy =>
    rw [extDeriv_mul]
    exact add_mem (mul_mem ihx hy) (mul_mem (involute_mem_supportedForms hx) ihy)

/-- If an `R`-derivation `D` preserving `B`-constants maps polynomials supported on `s` into
polynomials supported on `t ⊇ s`, then `D.deRhamLieDeriv hB` maps `supportedForms B s` into
`supportedForms B t`. -/
theorem deRhamLieDeriv_mem_supportedForms {R : Type*} [CommRing R] [Algebra R B]
    {D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B)}
    (hB : ∀ b : B, KaehlerDifferential.D B (MvPolynomial σ B) (D (algebraMap B _ b)) = 0)
    {s t : Set σ} (hst : s ⊆ t)
    (hD : ∀ p ∈ MvPolynomial.supported B s, D p ∈ MvPolynomial.supported B t)
    {α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])}
    (hα : α ∈ supportedForms B s) : D.deRhamLieDeriv hB α ∈ supportedForms B t := by
  induction hα using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨p, hp, rfl⟩ | ⟨i, hi, rfl⟩
    · rw [Derivation.deRhamLieDeriv_algebraMap]
      exact algebraMap_mem_supportedForms (hD p hp)
    · rw [Derivation.deRhamLieDeriv_ι, Derivation.kaehlerLieDeriv_D]
      exact ι_D_mem_supportedForms (hD (X i) (Algebra.subset_adjoin ⟨i, hi, rfl⟩))
  | algebraMap b =>
    have hb : algebraMap B (ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) b =
        algebraMap (MvPolynomial σ B) _ (C b) :=
      IsScalarTower.algebraMap_apply B (MvPolynomial σ B) _ b
    rw [hb, Derivation.deRhamLieDeriv_algebraMap]
    exact algebraMap_mem_supportedForms (hD (C b) (Subalgebra.algebraMap_mem _ b))
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mul x y hx hy ihx ihy =>
    rw [Derivation.deRhamLieDeriv_mul]
    exact add_mem (mul_mem ihx (supportedForms_mono hst hy))
      (mul_mem (supportedForms_mono hst hx) ihy)

/-- Every polynomial differential form uses only finitely many variables. -/
theorem exists_finset_mem_supportedForms
    (α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) :
    ∃ s : Finset σ, α ∈ supportedForms B (s : Set σ) := by
  classical
  induction α using CliffordAlgebra.induction with
  | algebraMap p =>
    exact ⟨p.vars, algebraMap_mem_supportedForms p.mem_supported_vars⟩
  | ι ω =>
    obtain ⟨v, rfl⟩ := (KaehlerDifferential.mvPolynomialEquiv B σ).symm.surjective ω
    induction v using Finsupp.induction_linear with
    | zero => exact ⟨∅, by simp⟩
    | add v₁ v₂ h₁ h₂ =>
      obtain ⟨s₁, hs₁⟩ := h₁
      obtain ⟨s₂, hs₂⟩ := h₂
      refine ⟨s₁ ∪ s₂, ?_⟩
      rw [map_add, map_add]
      exact add_mem
        (supportedForms_mono (Finset.coe_subset.mpr Finset.subset_union_left) hs₁)
        (supportedForms_mono (Finset.coe_subset.mpr Finset.subset_union_right) hs₂)
    | single i p =>
      have hsingle : (KaehlerDifferential.mvPolynomialEquiv B σ).symm (Finsupp.single i p) =
          p • KaehlerDifferential.D B (MvPolynomial σ B) (X i) :=
        KaehlerDifferential.mvPolynomialBasis_repr_symm_single B σ i p
      refine ⟨insert i p.vars, ?_⟩
      rw [hsingle, _root_.map_smul]
      exact smul_mem_supportedForms
        (MvPolynomial.supported_mono (Finset.coe_subset.mpr (Finset.subset_insert i p.vars))
          p.mem_supported_vars)
        (ι_D_X_mem_supportedForms (by simp))
  | mul α β hα hβ =>
    obtain ⟨s₁, hs₁⟩ := hα
    obtain ⟨s₂, hs₂⟩ := hβ
    exact ⟨s₁ ∪ s₂, mul_mem
      (supportedForms_mono (Finset.coe_subset.mpr Finset.subset_union_left) hs₁)
      (supportedForms_mono (Finset.coe_subset.mpr Finset.subset_union_right) hs₂)⟩
  | add α β hα hβ =>
    obtain ⟨s₁, hs₁⟩ := hα
    obtain ⟨s₂, hs₂⟩ := hβ
    exact ⟨s₁ ∪ s₂, add_mem
      (supportedForms_mono (Finset.coe_subset.mpr Finset.subset_union_left) hs₁)
      (supportedForms_mono (Finset.coe_subset.mpr Finset.subset_union_right) hs₂)⟩

end

end SupportedForms

end TauCeti.KaehlerDeRham
