/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Data.Finset.Pi
public import TauCeti.LinearAlgebra.Matrix.Trace.Partial

/-!
# Local algebras of a quantum spin system

A quantum spin system has a set `L` of sites, each carrying a copy of the matrix algebra
`M_d`. We label the basis states of a single site by a finite type `S` (for instance `Fin d`), so
a *configuration* of a finite region `Λ ⊆ L` is a function `Λ → S`. The *local algebra* of `Λ` is
`A_Λ = ⊗_{x ∈ Λ} M_d`; in the basis of configurations it is the matrix algebra
`Matrix (Λ → S) (Λ → S) R`. The inclusions need coefficients `R` forming a commutative semiring
with a star operation, while the partial trace needs only addition; the physical case is `R = ℂ`.

For `Λ ⊆ Λ'` a configuration of `Λ'` splits into its restriction to `Λ` and its values on the
sites of `Λ'` outside `Λ`, `QuantumSpin.configurationEquiv`. Under this splitting
`A_Λ' ≅ A_Λ ⊗ A_{Λ' \ Λ}`, and the *inclusion* `QuantumSpin.inclusion : A_Λ →⋆ₐ A_Λ'` is
`x ↦ x ⊗ 1`. Its matrix entries are `x (σ|_Λ) (τ|_Λ)` when `σ` and `τ` agree off `Λ`, and `0`
otherwise, `QuantumSpin.inclusion_apply`. The inclusions are unital ⋆-algebra homomorphisms,
injective when there is at least one basis state, and compatible:
`ι_{Λ' Λ''} ∘ ι_{Λ Λ'} = ι_{Λ Λ''}`. Observables localized in disjoint regions commute,
`QuantumSpin.commute_inclusion_inclusion`.

The *partial trace* `QuantumSpin.partialTrace : A_Λ' → A_Λ` traces out the sites of `Λ' \ Λ`.
It preserves the trace, commutes with adjoints and preserves positive semidefiniteness, sends
`ι x` to a multiple of `x`, and is a bimodule map over `A_Λ`. Partial traces compose: tracing out
`Λ'' \ Λ'` and then `Λ' \ Λ` traces out `Λ'' \ Λ`. Over a semifield, the normalized
partial trace `QuantumSpin.expectation` divides by the number of configurations of `Λ' \ Λ`. It
composes in the same way, commutes with adjoints, preserves positive semidefiniteness, and is a
bimodule map, `E (ι a * X * ι b) = a * E X * b`. It rescales the trace so as to preserve the
normalized traces, and in characteristic zero it is unital and a left inverse of the inclusion,
`E 1 = 1` and `E (ι x) = x`. Composition with `E` is the operation that extends a state of `A_Λ`
to `A_Λ'` by the normalized trace on the sites of `Λ' \ Λ`, as needed for finite-volume states of
spin systems.

## References

Bratteli–Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second edition,
Section 6.2.1, for the local algebras of quantum spin systems and their inclusions.
-/

public section

open Matrix
open scoped Kronecker

namespace TauCeti.QuantumSpin

variable {L S R : Type*} [DecidableEq L] {Λ Λ' Λ'' : Finset L}

section Configuration

/-- For regions `Λ ⊆ Λ'`, a configuration of `Λ'` is equivalently a configuration of `Λ` together
with a configuration of the sites of `Λ'` outside `Λ`. -/
def configurationEquiv (h : Λ ⊆ Λ') :
    (Λ' → S) ≃ (Λ → S) × ({i : Λ' // (i : L) ∉ Λ} → S) :=
  (Equiv.piEquivPiSubtypeProd (fun i : Λ' => (i : L) ∈ Λ) fun _ => S).trans <|
    (Equiv.arrowCongr (Equiv.subtypeSubtypeEquivSubtype fun hi => h hi) (.refl S)).prodCongr
      (.refl _)

@[simp]
theorem configurationEquiv_apply_fst (h : Λ ⊆ Λ') (σ : Λ' → S) :
    (configurationEquiv h σ).1 = Finset.restrict₂ (π := fun _ => S) h σ :=
  (rfl)

@[simp]
theorem configurationEquiv_apply_snd (h : Λ ⊆ Λ') (σ : Λ' → S) (i : {i : Λ' // (i : L) ∉ Λ}) :
    (configurationEquiv h σ).2 i = σ i :=
  (rfl)

theorem configurationEquiv_symm_apply_of_mem (h : Λ ⊆ Λ') (p : (Λ → S) × _) {i : Λ'}
    (hi : (i : L) ∈ Λ) : (configurationEquiv h).symm p i = p.1 ⟨i, hi⟩ := by
  have hsub : Equiv.subtypeSubtypeEquivSubtype (fun hj => h hj) ⟨i, hi⟩ = ⟨i, hi⟩ :=
    Subtype.ext (Equiv.subtypeSubtypeEquivSubtype_apply_coe _ _)
  simp [configurationEquiv, hi, hsub]

theorem configurationEquiv_symm_apply_of_notMem (h : Λ ⊆ Λ') (p : (Λ → S) × _) {i : Λ'}
    (hi : (i : L) ∉ Λ) : (configurationEquiv h).symm p i = p.2 ⟨i, hi⟩ := by
  simp [configurationEquiv, hi]

/-- No site of `Λ` lies outside `Λ`. -/
private instance : IsEmpty {i : Λ // (i : L) ∉ Λ} := ⟨fun i => i.2 i.1.2⟩

/-- For regions `Λ ⊆ Λ' ⊆ Λ''`, a configuration of the sites of `Λ''` outside `Λ` is a
configuration of the sites of `Λ'` outside `Λ` together with one of the sites of `Λ''` outside
`Λ'`. -/
private def complementEquiv (h₁ : Λ ⊆ Λ') (h₂ : Λ' ⊆ Λ'') :
    ({i : Λ' // (i : L) ∉ Λ} → S) × ({i : Λ'' // (i : L) ∉ Λ'} → S) ≃
      ({i : Λ'' // (i : L) ∉ Λ} → S) where
  toFun ζ i := if hi : (i : L) ∈ Λ' then ζ.1 ⟨⟨i, hi⟩, i.2⟩ else ζ.2 ⟨i, hi⟩
  invFun ζ := (fun i => ζ ⟨⟨i, h₂ i.1.2⟩, i.2⟩, fun i => ζ ⟨i, fun hi => i.2 (h₁ hi)⟩)
  left_inv ζ := by
    ext i
    · simp [i.1.2]
    · simp [i.2]
  right_inv ζ := by
    ext i
    by_cases hi : (i : L) ∈ Λ' <;> simp [hi]

private theorem configurationEquiv_symm_symm (h₁ : Λ ⊆ Λ') (h₂ : Λ' ⊆ Λ'') (σ₀ : Λ → S)
    (ζ : ({i : Λ' // (i : L) ∉ Λ} → S) × ({i : Λ'' // (i : L) ∉ Λ'} → S)) :
    (configurationEquiv h₂).symm ((configurationEquiv h₁).symm (σ₀, ζ.1), ζ.2) =
      (configurationEquiv (h₁.trans h₂)).symm (σ₀, complementEquiv h₁ h₂ ζ) := by
  ext i
  by_cases hi : (i : L) ∈ Λ
  · simp [configurationEquiv_symm_apply_of_mem, hi, h₁ hi]
  by_cases hi' : (i : L) ∈ Λ'
  · simp [configurationEquiv_symm_apply_of_mem, configurationEquiv_symm_apply_of_notMem,
      complementEquiv, hi, hi']
  · simp [configurationEquiv_symm_apply_of_notMem, complementEquiv, hi, hi']

end Configuration

variable [Fintype S]

section Inclusion

variable [DecidableEq S] [CommSemiring R] [StarRing R]

/-- The **inclusion of local algebras** `A_Λ → A_Λ'` for regions `Λ ⊆ Λ'`: under the splitting
`configurationEquiv` of configurations of `Λ'`, it is `x ↦ x ⊗ 1`, acting as `x` on the sites of
`Λ` and as the identity on the sites of `Λ'` outside `Λ`. -/
def inclusion (h : Λ ⊆ Λ') : Matrix (Λ → S) (Λ → S) R →⋆ₐ[R] Matrix (Λ' → S) (Λ' → S) R where
  toFun x := (x ⊗ₖ (1 : Matrix ({i : Λ' // (i : L) ∉ Λ} → S) _ R)).submatrix
    (configurationEquiv h) (configurationEquiv h)
  map_one' := by simp
  map_mul' x y := by rw [submatrix_mul_equiv, ← mul_kronecker_mul, one_mul]
  map_zero' := by simp
  map_add' x y := by
    ext
    simp [add_mul]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, smul_kronecker, one_kronecker_one, submatrix_smul,
      Pi.smul_apply, submatrix_one_equiv]
  map_star' x := by simp [star_eq_conjTranspose, conjTranspose_kronecker]

/-- The inclusion is `x ↦ x ⊗ 1` in the splitting of configurations of `Λ'`. -/
theorem submatrix_inclusion (h : Λ ⊆ Λ') (x : Matrix (Λ → S) (Λ → S) R) :
    (inclusion h x).submatrix (configurationEquiv h).symm (configurationEquiv h).symm =
      x ⊗ₖ (1 : Matrix ({i : Λ' // (i : L) ∉ Λ} → S) _ R) := by
  ext
  simp [inclusion]

/-- The matrix entries of the inclusion: `ι x σ τ` is `x (σ|_Λ) (τ|_Λ)` when the configurations
`σ` and `τ` of `Λ'` agree off `Λ`, and `0` otherwise. -/
theorem inclusion_apply (h : Λ ⊆ Λ') (x : Matrix (Λ → S) (Λ → S) R) (σ τ : Λ' → S) :
    inclusion h x σ τ =
      if ∀ i : Λ', (i : L) ∉ Λ → σ i = τ i then
        x (Finset.restrict₂ (π := fun _ => S) h σ) (Finset.restrict₂ (π := fun _ => S) h τ)
      else 0 := by
  have hagree : (configurationEquiv h σ).2 = (configurationEquiv h τ).2 ↔
      ∀ i : Λ', (i : L) ∉ Λ → σ i = τ i := by
    simp [funext_iff]
  simp [inclusion, one_apply, hagree]

@[simp]
theorem inclusion_self : inclusion (subset_refl Λ) = StarAlgHom.id R (Matrix (Λ → S) _ R) := by
  ext x σ τ
  simp [inclusion_apply, Finset.restrict₂_def]

@[simp]
theorem inclusion_inclusion (h₁ : Λ ⊆ Λ') (h₂ : Λ' ⊆ Λ'') (x : Matrix (Λ → S) (Λ → S) R) :
    inclusion h₂ (inclusion h₁ x) = inclusion (h₁.trans h₂) x := by
  ext σ τ
  have hagree : ((∀ i : Λ'', (i : L) ∉ Λ' → σ i = τ i) ∧
      ∀ i : Λ', (i : L) ∉ Λ → Finset.restrict₂ (π := fun _ => S) h₂ σ i =
        Finset.restrict₂ (π := fun _ => S) h₂ τ i) ↔
      ∀ i : Λ'', (i : L) ∉ Λ → σ i = τ i := by
    refine ⟨fun ⟨h', h''⟩ i hi => ?_, fun H => ⟨fun i hi => H i fun hΛ => hi (h₁ hΛ),
      fun i hi => H _ hi⟩⟩
    by_cases hi' : (i : L) ∈ Λ'
    · exact h'' ⟨i, hi'⟩ hi
    · exact h' i hi'
  simp only [inclusion_apply]
  rw [← ite_and]
  exact if_congr hagree rfl rfl

theorem inclusion_comp_inclusion (h₁ : Λ ⊆ Λ') (h₂ : Λ' ⊆ Λ'') :
    (inclusion h₂).comp (inclusion h₁) = (inclusion (h₁.trans h₂) : Matrix (Λ → S) _ R →⋆ₐ[R] _) :=
  StarAlgHom.ext (inclusion_inclusion h₁ h₂)

/-- When there is at least one basis state, the inclusion of local algebras is injective. -/
theorem inclusion_injective [Nonempty S] (h : Λ ⊆ Λ') :
    Function.Injective (inclusion h : Matrix (Λ → S) _ R → Matrix (Λ' → S) _ R) := by
  intro x y hxy
  have := congrArg (·.submatrix (configurationEquiv h).symm (configurationEquiv h).symm) hxy
  simp only [submatrix_inclusion] at this
  ext σ₀ τ₀
  let ζ : {i : Λ' // (i : L) ∉ Λ} → S := fun _ => Classical.arbitrary S
  simpa using congrFun (congrFun this (σ₀, ζ)) (τ₀, ζ)

/-- The product of observables localized in disjoint regions `Λ₁, Λ₂ ⊆ Λ`: its `(σ, τ)` entry is
`x (σ|_Λ₁) (τ|_Λ₁) * y (σ|_Λ₂) (τ|_Λ₂)` when `σ` and `τ` agree off `Λ₁ ∪ Λ₂`, and `0` otherwise. -/
private theorem inclusion_mul_inclusion_apply {Λ₁ Λ₂ : Finset L} (h₁ : Λ₁ ⊆ Λ) (h₂ : Λ₂ ⊆ Λ)
    (hd : Disjoint Λ₁ Λ₂) (x : Matrix (Λ₁ → S) (Λ₁ → S) R) (y : Matrix (Λ₂ → S) (Λ₂ → S) R)
    (σ τ : Λ → S) :
    (inclusion h₁ x * inclusion h₂ y) σ τ =
      if ∀ i : Λ, (i : L) ∉ Λ₁ → (i : L) ∉ Λ₂ → σ i = τ i then
        x (Finset.restrict₂ (π := fun _ => S) h₁ σ) (Finset.restrict₂ (π := fun _ => S) h₁ τ) *
          y (Finset.restrict₂ (π := fun _ => S) h₂ σ) (Finset.restrict₂ (π := fun _ => S) h₂ τ)
      else 0 := by
  -- The only intermediate configuration contributing to the matrix product follows `τ` on `Λ₁`
  -- and `σ` elsewhere.
  let ρ : Λ → S := fun i => if (i : L) ∈ Λ₁ then τ i else σ i
  have hρ₁ : Finset.restrict₂ (π := fun _ => S) h₁ ρ =
      Finset.restrict₂ (π := fun _ => S) h₁ τ := by
    ext i
    simp [ρ, i.2]
  have hρ₂ : Finset.restrict₂ (π := fun _ => S) h₂ ρ =
      Finset.restrict₂ (π := fun _ => S) h₂ σ := by
    ext i
    simp [ρ, Finset.disjoint_right.1 hd i.2]
  have hσρ : ∀ i : Λ, (i : L) ∉ Λ₁ → σ i = ρ i := fun i hi => by simp [ρ, hi]
  have hρτ : (∀ i : Λ, (i : L) ∉ Λ₂ → ρ i = τ i) ↔
      ∀ i : Λ, (i : L) ∉ Λ₁ → (i : L) ∉ Λ₂ → σ i = τ i := by
    refine ⟨fun H i hi₁ hi₂ => by simpa [ρ, hi₁] using H i hi₂, fun H i hi₂ => ?_⟩
    by_cases hi₁ : (i : L) ∈ Λ₁
    · simp [ρ, hi₁]
    · simpa [ρ, hi₁] using H i hi₁ hi₂
  rw [mul_apply, Finset.sum_eq_single ρ]
  · simp only [inclusion_apply, hρ₁, hρ₂, eq_true hσρ, ↓reduceIte, mul_ite, mul_zero]
    exact if_congr hρτ rfl rfl
  · intro ρ' _ hne
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    simp only [inclusion_apply]
    by_cases hi₁ : (i : L) ∈ Λ₁
    · have : ¬∀ j : Λ, (j : L) ∉ Λ₂ → ρ' j = τ j := fun h' =>
        hi (by simpa [ρ, hi₁] using h' i (Finset.disjoint_left.1 hd hi₁))
      simp only [this, ↓reduceIte, mul_zero]
    · have : ¬∀ j : Λ, (j : L) ∉ Λ₁ → σ j = ρ' j := fun h' =>
        hi (by simpa [ρ, hi₁] using (h' i hi₁).symm)
      simp only [this, ↓reduceIte, zero_mul]
  · simp

/-- Observables localized in disjoint regions commute. -/
theorem commute_inclusion_inclusion {Λ₁ Λ₂ : Finset L} (h₁ : Λ₁ ⊆ Λ) (h₂ : Λ₂ ⊆ Λ)
    (hd : Disjoint Λ₁ Λ₂) (x : Matrix (Λ₁ → S) (Λ₁ → S) R) (y : Matrix (Λ₂ → S) (Λ₂ → S) R) :
    Commute (inclusion h₁ x) (inclusion h₂ y) := by
  ext σ τ
  rw [inclusion_mul_inclusion_apply h₁ h₂ hd, inclusion_mul_inclusion_apply h₂ h₁ hd.symm,
    mul_comm (x _ _)]
  exact if_congr ⟨fun H i hi₂ hi₁ => H i hi₁ hi₂, fun H i hi₁ hi₂ => H i hi₂ hi₁⟩ rfl rfl

end Inclusion

section PartialTrace

variable [AddCommMonoid R]

/-- The **partial trace** `A_Λ' → A_Λ` over the sites of `Λ'` outside `Λ`, for regions `Λ ⊆ Λ'`:
`Matrix.partialTraceRight` in the splitting `configurationEquiv` of configurations of `Λ'`. -/
def partialTrace (h : Λ ⊆ Λ') (X : Matrix (Λ' → S) (Λ' → S) R) : Matrix (Λ → S) (Λ → S) R :=
  partialTraceRight (X.submatrix (configurationEquiv h).symm (configurationEquiv h).symm)

/-- The entries of the partial trace sum over the configurations of the sites of `Λ'` outside
`Λ`. -/
theorem partialTrace_apply (h : Λ ⊆ Λ') (X : Matrix (Λ' → S) (Λ' → S) R) (σ₀ τ₀ : Λ → S) :
    partialTrace h X σ₀ τ₀ =
      ∑ ζ, X ((configurationEquiv h).symm (σ₀, ζ)) ((configurationEquiv h).symm (τ₀, ζ)) := by
  simp [partialTrace]

@[simp]
theorem partialTrace_zero (h : Λ ⊆ Λ') :
    partialTrace h (0 : Matrix (Λ' → S) (Λ' → S) R) = 0 := by
  simp [partialTrace]

@[simp]
theorem partialTrace_add (h : Λ ⊆ Λ') (X Y : Matrix (Λ' → S) (Λ' → S) R) :
    partialTrace h (X + Y) = partialTrace h X + partialTrace h Y := by
  simp only [partialTrace, submatrix_add, Pi.add_apply, partialTraceRight_add]

@[simp]
theorem partialTrace_smul {α : Type*} [DistribSMul α R] (h : Λ ⊆ Λ') (c : α)
    (X : Matrix (Λ' → S) (Λ' → S) R) :
    partialTrace h (c • X) = c • partialTrace h X := by
  simp only [partialTrace, submatrix_smul, Pi.smul_apply, partialTraceRight_smul]

/-- The partial trace preserves the trace. -/
@[simp]
theorem trace_partialTrace (h : Λ ⊆ Λ') (X : Matrix (Λ' → S) (Λ' → S) R) :
    trace (partialTrace h X) = trace X := by
  rw [partialTrace, trace_partialTraceRight]
  exact Equiv.sum_comp (configurationEquiv h).symm fun ρ => X ρ ρ

/-- The partial trace commutes with conjugate transposition. -/
@[simp]
theorem partialTrace_conjTranspose [StarAddMonoid R] (h : Λ ⊆ Λ')
    (X : Matrix (Λ' → S) (Λ' → S) R) :
    partialTrace h Xᴴ = (partialTrace h X)ᴴ := by
  rw [partialTrace, partialTrace, ← conjTranspose_submatrix, partialTraceRight_conjTranspose]

/-- The partial trace of a positive semidefinite matrix is positive semidefinite. -/
theorem _root_.Matrix.PosSemidef.quantumSpinPartialTrace {R : Type*} [Ring R] [PartialOrder R]
    [StarRing R] [AddLeftMono R] (h : Λ ⊆ Λ') {X : Matrix (Λ' → S) (Λ' → S) R} (hX : X.PosSemidef) :
    (partialTrace h X).PosSemidef :=
  (hX.submatrix _).partialTraceRight

/-- Tracing out no sites is the identity. -/
@[simp]
theorem partialTrace_self (X : Matrix (Λ → S) (Λ → S) R) : partialTrace (subset_refl Λ) X = X := by
  have hσ (σ : Λ → S) ζ : (configurationEquiv (subset_refl Λ)).symm (σ, ζ) = σ :=
    funext fun i => configurationEquiv_symm_apply_of_mem _ _ i.2
  ext σ τ
  simp [partialTrace_apply, hσ]

/-- Partial traces compose: tracing out the sites of `Λ''` outside `Λ'` and then those of `Λ'`
outside `Λ` traces out the sites of `Λ''` outside `Λ`. -/
@[simp]
theorem partialTrace_partialTrace (h₁ : Λ ⊆ Λ') (h₂ : Λ' ⊆ Λ'') (X : Matrix (Λ'' → S) (Λ'' → S) R) :
    partialTrace h₁ (partialTrace h₂ X) = partialTrace (h₁.trans h₂) X := by
  ext σ₀ τ₀
  simp only [partialTrace_apply]
  rw [← Fintype.sum_prod_type', ← (complementEquiv h₁ h₂).sum_comp]
  simp only [configurationEquiv_symm_symm]

end PartialTrace

/-- Tracing out the sites of `Λ'` outside `Λ` from the identity gives the number of
configurations of those sites. -/
@[simp]
theorem partialTrace_one [NonAssocSemiring R] [DecidableEq S] (h : Λ ⊆ Λ') :
    partialTrace h (1 : Matrix (Λ' → S) (Λ' → S) R) =
      (Fintype.card ({i : Λ' // (i : L) ∉ Λ} → S) : R) • 1 := by
  rw [partialTrace, submatrix_one_equiv, partialTraceRight_one]

section PartialTraceInclusion

variable [CommSemiring R] [DecidableEq S] [StarRing R]

/-- Tracing out the sites of `Λ'` outside `Λ` from `ι x = x ⊗ 1` multiplies `x` by the number of
configurations of those sites. -/
@[simp]
theorem partialTrace_inclusion (h : Λ ⊆ Λ') (x : Matrix (Λ → S) (Λ → S) R) :
    partialTrace h (inclusion h x) =
      (Fintype.card ({i : Λ' // (i : L) ∉ Λ} → S) : R) • x := by
  simp [partialTrace, submatrix_inclusion]

/-- Tracing out the sites of `Λ''` outside `Λ'` from an observable localized in a smaller region
`Λ ⊆ Λ'` multiplies it by the number of configurations of those sites. -/
@[simp]
theorem partialTrace_inclusion_of_subset (h₁ : Λ ⊆ Λ') (h₂ : Λ' ⊆ Λ'') (h : Λ ⊆ Λ'')
    (x : Matrix (Λ → S) (Λ → S) R) :
    partialTrace h₂ (inclusion h x) =
      (Fintype.card ({i : Λ'' // (i : L) ∉ Λ'} → S) : R) • inclusion h₁ x := by
  rw [← inclusion_inclusion h₁ h₂, partialTrace_inclusion]

/-- The partial trace is left linear over the local algebra of the smaller region:
`Tr (ι a * X) = a * Tr X`. -/
theorem partialTrace_inclusion_mul (h : Λ ⊆ Λ') (a : Matrix (Λ → S) (Λ → S) R)
    (X : Matrix (Λ' → S) (Λ' → S) R) :
    partialTrace h (inclusion h a * X) = a * partialTrace h X := by
  simp only [partialTrace, ← submatrix_mul_equiv _ _ _ (configurationEquiv h).symm,
    submatrix_inclusion, partialTraceRight_kronecker_one_mul]

/-- The partial trace is right linear over the local algebra of the smaller region:
`Tr (X * ι b) = Tr X * b`. -/
theorem partialTrace_mul_inclusion (h : Λ ⊆ Λ') (b : Matrix (Λ → S) (Λ → S) R)
    (X : Matrix (Λ' → S) (Λ' → S) R) :
    partialTrace h (X * inclusion h b) = partialTrace h X * b := by
  simp only [partialTrace, ← submatrix_mul_equiv _ _ _ (configurationEquiv h).symm,
    submatrix_inclusion, partialTraceRight_mul_kronecker_one]

/-- The partial trace is a bimodule map over the local algebra of the smaller region:
`Tr (ι a * X * ι b) = a * Tr X * b`. -/
theorem partialTrace_inclusion_mul_mul_inclusion (h : Λ ⊆ Λ') (a b : Matrix (Λ → S) (Λ → S) R)
    (X : Matrix (Λ' → S) (Λ' → S) R) :
    partialTrace h (inclusion h a * X * inclusion h b) = a * partialTrace h X * b := by
  rw [partialTrace_mul_inclusion, partialTrace_inclusion_mul]

end PartialTraceInclusion

section Expectation

variable [Semifield R]

/-- The **normalized partial trace** `A_Λ' → A_Λ` for regions `Λ ⊆ Λ'`: the partial trace over the
sites of `Λ'` outside `Λ`, divided by the number of configurations of those sites. -/
def expectation (h : Λ ⊆ Λ') : Matrix (Λ' → S) (Λ' → S) R →ₗ[R] Matrix (Λ → S) (Λ → S) R where
  toFun X := (Fintype.card ({i : Λ' // (i : L) ∉ Λ} → S) : R)⁻¹ • partialTrace h X
  map_add' X Y := by simp
  map_smul' c X := by simp [smul_comm c]

theorem expectation_apply (h : Λ ⊆ Λ') (X : Matrix (Λ' → S) (Λ' → S) R) :
    expectation h X = (Fintype.card ({i : Λ' // (i : L) ∉ Λ} → S) : R)⁻¹ • partialTrace h X :=
  (rfl)

/-- The normalized partial trace rescales the trace by the number of configurations of the sites
of `Λ'` outside `Λ`, so it preserves the normalized traces `Tr / card (Λ → S)` and
`Tr / card (Λ' → S)`. -/
theorem trace_expectation (h : Λ ⊆ Λ') (X : Matrix (Λ' → S) (Λ' → S) R) :
    trace (expectation h X) = (Fintype.card ({i : Λ' // (i : L) ∉ Λ} → S) : R)⁻¹ * trace X := by
  rw [expectation_apply, trace_smul, trace_partialTrace, smul_eq_mul]

/-- The normalized partial trace over no sites is the identity. -/
@[simp]
theorem expectation_self (X : Matrix (Λ → S) (Λ → S) R) : expectation (subset_refl Λ) X = X := by
  simp [expectation_apply]

/-- Normalized partial traces compose. -/
@[simp]
theorem expectation_expectation (h₁ : Λ ⊆ Λ') (h₂ : Λ' ⊆ Λ'')
    (X : Matrix (Λ'' → S) (Λ'' → S) R) :
    expectation h₁ (expectation h₂ X) = expectation (h₁.trans h₂) X := by
  have hcard : (Fintype.card ({i : Λ'' // (i : L) ∉ Λ} → S) : R) =
      Fintype.card ({i : Λ' // (i : L) ∉ Λ} → S) *
        Fintype.card ({i : Λ'' // (i : L) ∉ Λ'} → S) := by
    rw [← Fintype.card_congr (complementEquiv h₁ h₂), Fintype.card_prod, Nat.cast_mul]
  simp only [expectation_apply]
  rw [partialTrace_smul, partialTrace_partialTrace, smul_smul, hcard, mul_inv]

/-- Normalized partial traces compose, as linear maps. -/
theorem expectation_comp_expectation (h₁ : Λ ⊆ Λ') (h₂ : Λ' ⊆ Λ'') :
    (expectation h₁).comp (expectation h₂) =
      (expectation (h₁.trans h₂) : Matrix (Λ'' → S) _ R →ₗ[R] _) :=
  LinearMap.ext (expectation_expectation h₁ h₂)

/-- The normalized partial trace commutes with conjugate transposition. -/
@[simp]
theorem expectation_conjTranspose [StarRing R] (h : Λ ⊆ Λ') (X : Matrix (Λ' → S) (Λ' → S) R) :
    expectation h Xᴴ = (expectation h X)ᴴ := by
  simp [expectation_apply]

/-- The normalized partial trace of a positive semidefinite matrix is positive semidefinite. -/
theorem _root_.Matrix.PosSemidef.quantumSpinExpectation {R : Type*} [Field R] [PartialOrder R]
    [StarRing R] [StarOrderedRing R] [IsOrderedRing R] (h : Λ ⊆ Λ') {X : Matrix (Λ' → S) (Λ' → S) R}
    (hX : X.PosSemidef) : (expectation h X).PosSemidef := by
  set c : R := (Fintype.card ({i : Λ' // (i : L) ∉ Λ} → S) : R)
  -- `c⁻¹` is nonnegative as the conjugate `star c⁻¹ * c * c⁻¹` of the nonnegative `c`.
  have hc : 0 ≤ c⁻¹ := by
    obtain hc | hc := eq_or_ne c 0
    · simp [hc]
    · have hcc : c⁻¹ = star c⁻¹ * c * c⁻¹ := by
        rw [star_inv₀, star_natCast, inv_mul_cancel₀ hc, one_mul]
      exact hcc ▸ star_left_conjugate_nonneg (Nat.cast_nonneg _) _
  exact (hX.quantumSpinPartialTrace h).smul hc

/-- The normalized partial trace is unital: `E 1 = 1`. -/
@[simp]
theorem expectation_one [CharZero R] [Nonempty S] [DecidableEq S] (h : Λ ⊆ Λ') :
    expectation h (1 : Matrix (Λ' → S) (Λ' → S) R) = 1 := by
  rw [expectation_apply, partialTrace_one, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_smul]

variable [DecidableEq S] [StarRing R]

/-- The normalized partial trace is a left inverse of the inclusion: `E (ι x) = x`. -/
@[simp]
theorem expectation_inclusion [CharZero R] [Nonempty S] (h : Λ ⊆ Λ')
    (x : Matrix (Λ → S) (Λ → S) R) :
    expectation h (inclusion h x) = x := by
  rw [expectation_apply, partialTrace_inclusion, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_smul]

/-- The normalized partial trace onto an intermediate region `Λ ⊆ Λ' ⊆ Λ''` fixes observables
localized in `Λ`: `E_{Λ''→Λ'} (ι_{Λ→Λ''} x) = ι_{Λ→Λ'} x`. -/
@[simp]
theorem expectation_inclusion_of_subset [CharZero R] [Nonempty S] (h₁ : Λ ⊆ Λ') (h₂ : Λ' ⊆ Λ'')
    (h : Λ ⊆ Λ'') (x : Matrix (Λ → S) (Λ → S) R) :
    expectation h₂ (inclusion h x) = inclusion h₁ x := by
  rw [← inclusion_inclusion h₁ h₂, expectation_inclusion]

/-- The normalized partial trace is left linear over the local algebra of the smaller region:
`E (ι a * X) = a * E X`. -/
theorem expectation_inclusion_mul (h : Λ ⊆ Λ') (a : Matrix (Λ → S) (Λ → S) R)
    (X : Matrix (Λ' → S) (Λ' → S) R) :
    expectation h (inclusion h a * X) = a * expectation h X := by
  rw [expectation_apply, expectation_apply, partialTrace_inclusion_mul, mul_smul_comm]

/-- The normalized partial trace is right linear over the local algebra of the smaller region:
`E (X * ι b) = E X * b`. -/
theorem expectation_mul_inclusion (h : Λ ⊆ Λ') (b : Matrix (Λ → S) (Λ → S) R)
    (X : Matrix (Λ' → S) (Λ' → S) R) :
    expectation h (X * inclusion h b) = expectation h X * b := by
  rw [expectation_apply, expectation_apply, partialTrace_mul_inclusion, smul_mul_assoc]

/-- The normalized partial trace is a bimodule map over the local algebra of the smaller region:
`E (ι a * X * ι b) = a * E X * b`. -/
theorem expectation_inclusion_mul_mul_inclusion (h : Λ ⊆ Λ') (a b : Matrix (Λ → S) (Λ → S) R)
    (X : Matrix (Λ' → S) (Λ' → S) R) :
    expectation h (inclusion h a * X * inclusion h b) = a * expectation h X * b := by
  rw [expectation_mul_inclusion, expectation_inclusion_mul]

end Expectation

end TauCeti.QuantumSpin
