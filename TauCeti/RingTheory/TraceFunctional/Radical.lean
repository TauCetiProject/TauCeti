/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Radicals of tracial linear functionals

For a tracial linear functional `τ : A →ₗ[R] R`, its trace radical consists of the elements
`x` with `τ (x * y) = 0` for every `y`. It is a two-sided ideal, not merely the kernel of `τ`.
The induced functional on the quotient is tracial and its multiplication pairing is
nondegenerate. No positivity, finite dimensionality or field hypothesis is required.

The radical is the largest two-sided ideal on which `τ` vanishes. Under a surjective
trace-preserving algebra map it pulls back exactly; without surjectivity only one inclusion
is asserted. These facts allow algebraic trace quotients to be compared before any completion.

## References

* M. Geck and G. Pfeiffer, *Characters of Finite Coxeter Groups and Iwahori-Hecke Algebras*,
  OUP (2000), Section 7.1, for trace forms on symmetric algebras.
-/

public section

namespace LinearMap

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A]
  [Ring B] [Algebra R B]
variable (τ : A →ₗ[R] R) (hτ : ∀ x y, τ (x * y) = τ (y * x))

/-- Precomposing a tracial linear functional with an algebra map preserves traciality. -/
theorem comp_algHom_mul_comm (hτ : ∀ x y, τ (x * y) = τ (y * x))
    (f : B →ₐ[R] A) (x y : B) :
    (τ ∘ₗ f.toLinearMap) (x * y) = (τ ∘ₗ f.toLinearMap) (y * x) := by
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, hτ]

/-- The two-sided radical of the multiplication pairing of a tracial linear functional. -/
def traceRadical : Ideal A where
  carrier := {x | ∀ y, τ (x * y) = 0}
  zero_mem' := by simp
  add_mem' hx hz y := by simp [add_mul, hx y, hz y]
  smul_mem' a x hx y := by
    rw [smul_eq_mul, mul_assoc, hτ, mul_assoc]
    exact hx _

/-- Membership in the trace radical is vanishing against every right factor. -/
@[simp]
theorem mem_traceRadical {x : A} :
    x ∈ τ.traceRadical hτ ↔ ∀ y, τ (x * y) = 0 := Iff.rfl

instance : (τ.traceRadical hτ).IsTwoSided where
  mul_mem_of_left b hx y := by simpa only [mul_assoc] using hx (b * y)

/-- The underlying coefficient submodule is the kernel of `x ↦ (y ↦ τ (x * y))`. -/
theorem traceRadical_restrictScalars_eq_ker :
    (τ.traceRadical hτ).restrictScalars R = ker ((LinearMap.mul R A).compr₂ τ) := by
  ext x
  simp [mem_traceRadical, LinearMap.ext_iff]

/-- Vanishing against left factors gives the same radical. -/
theorem mem_traceRadical_iff_left {x : A} :
    x ∈ τ.traceRadical hτ ↔ ∀ y, τ (y * x) = 0 := by
  simp only [mem_traceRadical, hτ x]

/-- It suffices to test the trace pairing on any coefficient basis. -/
theorem mem_traceRadical_iff_basis {ι : Type*} (b : Module.Basis ι R A) {x : A} :
    x ∈ τ.traceRadical hτ ↔ ∀ i, τ (x * b i) = 0 := by
  rw [mem_traceRadical]
  refine ⟨fun hx i ↦ hx _, fun hx y ↦ ?_⟩
  let f := τ ∘ₗ LinearMap.mulLeft R x
  have hf : f = 0 := b.ext fun i ↦ by simpa [f] using hx i
  exact LinearMap.congr_fun hf y

/-- The trace itself vanishes on its radical. -/
theorem traceRadical_le_ker : (τ.traceRadical hτ).restrictScalars R ≤ ker τ := by
  intro x hx
  simpa using hx 1

/-- A trace nonzero at the identity has a proper radical. -/
theorem traceRadical_ne_top (h : τ 1 ≠ 0) : τ.traceRadical hτ ≠ ⊤ := by
  intro heq
  have hmem : (1 : A) ∈ τ.traceRadical hτ := by rw [heq]; trivial
  exact h (by simpa using hmem 1)

/-- The trace radical is the largest two-sided ideal annihilated by the trace. -/
theorem le_traceRadical_iff (I : Ideal A) [I.IsTwoSided] :
    I ≤ τ.traceRadical hτ ↔ I.restrictScalars R ≤ ker τ := by
  refine ⟨fun h ↦ le_trans (Submodule.restrictScalars_mono R h) (τ.traceRadical_le_ker hτ), ?_⟩
  intro h x hx y
  exact h (I.mul_mem_right y hx)

/-- The linear functional induced on the quotient by the trace radical. -/
def quotientTrace : A ⧸ τ.traceRadical hτ →ₗ[R] R :=
  ((τ.traceRadical hτ).restrictScalars R).liftQ τ (τ.traceRadical_le_ker hτ) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R (τ.traceRadical hτ)).symm.toLinearMap

/-- The quotient functional agrees with the original trace on representatives. -/
@[simp]
theorem quotientTrace_mk (x : A) :
    τ.quotientTrace hτ (Ideal.Quotient.mk (τ.traceRadical hτ) x) = τ x := by
  simp only [quotientTrace, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← Ideal.Quotient.mk_eq_mk,
    Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.liftQ_apply]

/-- The quotient preserves the value at the identity, in particular normalization. -/
@[simp]
theorem quotientTrace_one : τ.quotientTrace hτ 1 = τ 1 := by
  simpa only [map_one] using τ.quotientTrace_mk hτ 1

/-- The induced functional is tracial. -/
theorem quotientTrace_mul_comm (x y : A ⧸ τ.traceRadical hτ) :
    τ.quotientTrace hτ (x * y) = τ.quotientTrace hτ (y * x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (τ.traceRadical hτ) x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (τ.traceRadical hτ) y
  simp only [← map_mul, Ideal.Quotient.mkₐ_eq_mk, quotientTrace_mk, hτ]

/-- The quotient multiplication pairing has zero left radical. By traciality its right radical
is zero as well. This is algebraic nondegeneracy, not positivity or faithfulness of a state. -/
theorem quotientTrace_nondegenerate (x : A ⧸ τ.traceRadical hτ)
    (hx : ∀ y, τ.quotientTrace hτ (x * y) = 0) : x = 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (τ.traceRadical hτ) x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  intro y
  simpa only [← map_mul, Ideal.Quotient.mkₐ_eq_mk, quotientTrace_mk] using
    hx (Ideal.Quotient.mkₐ R (τ.traceRadical hτ) y)

/-- A functional on the trace quotient is determined by its values on representatives. -/
theorem eq_quotientTrace (σ : A ⧸ τ.traceRadical hτ →ₗ[R] R)
    (hσ : σ ∘ₗ (Ideal.Quotient.mkₐ R (τ.traceRadical hτ)).toLinearMap = τ) :
    σ = τ.quotientTrace hτ := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (τ.traceRadical hτ) x
  exact (LinearMap.congr_fun hσ x).trans (τ.quotientTrace_mk hτ x).symm

variable {τ} {σ : B →ₗ[R] R} (hσ : ∀ x y, σ (x * y) = σ (y * x))

/-- Pullback of the target radical is contained in the source radical for a trace-preserving
map. The reverse inclusion need not hold for a nonsurjective map. -/
theorem comap_traceRadical_le (f : A →ₐ[R] B) (hf : σ ∘ₗ f.toLinearMap = τ) :
    Ideal.comap f (σ.traceRadical hσ) ≤ τ.traceRadical hτ := by
  intro x hx y
  have heq (a) : σ (f a) = τ a := LinearMap.congr_fun hf a
  rw [← heq, map_mul]
  exact hx _

/-- A surjective trace-preserving algebra map pulls back the trace radical exactly. -/
theorem comap_traceRadical_of_surjective (f : A →ₐ[R] B)
    (hf : σ ∘ₗ f.toLinearMap = τ) (hsurj : Function.Surjective f) :
    Ideal.comap f (σ.traceRadical hσ) = τ.traceRadical hτ := by
  refine le_antisymm (comap_traceRadical_le hτ hσ f hf) ?_
  intro x hx y
  obtain ⟨y, rfl⟩ := hsurj y
  have heq : σ (f (x * y)) = τ (x * y) := LinearMap.congr_fun hf _
  simpa only [map_mul] using heq.trans (hx y)

end LinearMap

namespace AlgHom

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- For an algebra character, the trace radical is exactly its kernel. -/
theorem traceRadical_eq_ker (χ : A →ₐ[R] R) :
    χ.toLinearMap.traceRadical (fun x y ↦ by simp [mul_comm]) = RingHom.ker χ := by
  ext x
  constructor
  · intro hx
    simpa using hx 1
  · intro hx y
    simp only [RingHom.mem_ker] at hx
    simp [hx]

end AlgHom
