/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.RingTheory.Trace.Basic
public import TauCeti.Algebra.Algebra.Frobenius.DivisionRing
public import TauCeti.LinearAlgebra.BilinearForm.Prod

/-!
# Transfer of bilinear forms along a linear functional

Let `K` be an `F`-algebra and `M` a `K`-module which is also an `F`-module compatibly. For a
`K`-bilinear form `B` on `M` and an `F`-linear functional `f : K →ₗ[F] F`, Mathlib's
`LinearMap.compBilinForm f B` is the `F`-bilinear form `f ∘ B` on `M`. It is the bilinear
counterpart of the Scharlau transfer `QuadraticMap.scharlauTransfer` of quadratic forms. For the
trace `f = Algebra.trace F K` of a finite extension of fields it restricts a symplectic space over
`K` to a symplectic space over `F`.

When `K` is a field and `f` is nonzero, transfer loses no information. Every nonzero `x : K` has a
multiple `a * x` outside the kernel of `f`, since a nonzero functional on a division ring is a
Frobenius functional (`LinearMap.isFrobeniusFunctional_iff_ne_zero`). So transfer is injective on
bilinear forms, and it preserves and reflects left and right separation and nondegeneracy. A
`K`-linear endomorphism scales the transferred form by `c : F` exactly when it scales `B` by
`algebraMap F K c`. None of this needs finiteness or separability. Transfer along any functional
preserves alternation, but need not reflect it in characteristic two: for `K = F₂(s)` over
`F = F₂(s²)` every square lies in `F`, so a functional vanishing on `F` transfers the
non-alternating form `x * y` on `K` to an alternating one.

For the trace of a finite extension of fields `K / F`, the transfer of a nondegenerate form on a
nonzero space is nondegenerate exactly when `K / F` is separable: the trace of an inseparable
extension vanishes, and so does every form transferred along it.

For a finite separable extension `K / F`, applied to the orthogonal sum `LinearMap.BilinForm.pi`
of a family `ψ i` of nondegenerate alternating forms, for instance of `r` copies of one form `ψ`
on `V`, this gives the nondegenerate alternating `F`-bilinear form
`Ψ ((vᵢ), (wᵢ)) = Tr_{K/F} (∑ᵢ ψ (vᵢ, wᵢ))` on `V^r`. This is the symplectic form through which
a symplectic representation over `K` is restricted to `F`. A family `(gᵢ)` of `K`-linear
endomorphisms is an `F`-similitude of `Ψ` with multiplier `c : F` exactly when every `gᵢ` is a
similitude of `ψ i` with the common multiplier `algebraMap F K c`; so independent multipliers in
`K` do not give similitudes of `Ψ`.

## Main declarations

* `LinearMap.compBilinForm_injective`: transfer along a nonzero functional is injective.
* `LinearMap.BilinForm.IsAlt.compBilinForm`: transfer preserves alternation.
* `LinearMap.separatingLeft_compBilinForm_iff`, `LinearMap.separatingRight_compBilinForm_iff`,
  `LinearMap.nondegenerate_compBilinForm_iff`: transfer along a nonzero functional preserves and
  reflects separation and nondegeneracy.
* `LinearMap.compl₁₂_compBilinForm_eq_smul_iff`: for a nonzero functional, the `K`-linear
  similitudes of the transferred form are the similitudes of the original form with a multiplier
  from `F`.
* `LinearMap.nondegenerate_trace_compBilinForm_iff`: the trace transfer of a nondegenerate form
  on a nonzero space is nondegenerate exactly for separable extensions.
* `LinearMap.compl₁₂_compBilinForm_pi_piMap_eq_smul_iff`: for a nonzero functional, the
  similitudes of the transferred orthogonal sum given by families of `K`-linear maps are the
  families of similitudes with one common multiplier from `F`.

## References

* M. Kisin and R. Zhou, *Independence of ℓ for Frobenius conjugacy classes attached to abelian
  varieties*, Proposition 3.1.12.
* W. Scharlau, *Quadratic and Hermitian Forms* (1985), Chapter 2, §5.
-/

public section

open LinearMap (BilinForm)

namespace LinearMap

section Semiring

variable {F K M : Type*} [CommSemiring F] [CommSemiring K] [Algebra F K] [AddCommMonoid M]
  [Module K M] [Module F M] [IsScalarTower F K M]

/-- The transfer of an alternating form is alternating. -/
theorem BilinForm.IsAlt.compBilinForm {B : BilinForm K M} (hB : B.IsAlt) (f : K →ₗ[F] F) :
    (f.compBilinForm B).IsAlt := fun x ↦ by
  simp [hB.self_eq_zero x]

/-- Transfer along the zero functional is zero. -/
@[simp]
theorem zero_compBilinForm (B : BilinForm K M) : (0 : K →ₗ[F] F).compBilinForm B = 0 := by
  ext x y
  simp

/-- Transfer along the identity of the scalars is the identity. -/
@[simp]
theorem id_compBilinForm (B : BilinForm K M) : (LinearMap.id : K →ₗ[K] K).compBilinForm B = B := by
  ext x y
  simp

/-- Flipping commutes with transfer. -/
@[simp]
theorem flip_compBilinForm (f : K →ₗ[F] F) (B : BilinForm K M) :
    LinearMap.flip (f.compBilinForm B) = f.compBilinForm (LinearMap.flip B) := by
  ext x y
  simp

/-- Transfer commutes with multiplication by a scalar from `F`. -/
@[simp]
theorem compBilinForm_smul (f : K →ₗ[F] F) (c : F) (B : BilinForm K M) :
    f.compBilinForm (c • B) = c • f.compBilinForm B := by
  ext x y
  simp [-smul_eq_mul]

/-- Precomposing a transferred form with `K`-linear maps transfers the precomposed form. -/
@[simp]
theorem compl₁₂_compBilinForm {N : Type*} [AddCommMonoid N] [Module K N] [Module F N]
    [IsScalarTower F K N] (f : K →ₗ[F] F) (B : BilinForm K M) (g h : N →ₗ[K] M) :
    (f.compBilinForm B).compl₁₂ (g.restrictScalars F) (h.restrictScalars F) =
      f.compBilinForm (B.compl₁₂ g h) := by
  ext x y
  simp

end Semiring

section Field

variable {F K M : Type*} [CommSemiring F] [Field K] [Algebra F K] [AddCommMonoid M] [Module K M]
  [Module F M] [IsScalarTower F K M] {f : K →ₗ[F] F}

/-- Transfer along a nonzero functional is injective on bilinear forms. -/
theorem compBilinForm_injective (hf : f ≠ 0) :
    Function.Injective (f.compBilinForm : BilinForm K M → BilinForm F M) := by
  intro B C h
  ext x y
  exact ((isFrobeniusFunctional_iff_ne_zero f).2 hf).eq_of_forall_apply_mul_eq fun a ↦ by
    simpa using congr($h x (a • y))

@[simp]
theorem compBilinForm_inj (hf : f ≠ 0) {B C : BilinForm K M} :
    f.compBilinForm B = f.compBilinForm C ↔ B = C :=
  (compBilinForm_injective hf).eq_iff

/-- The transfer along a nonzero functional is left-separating exactly when the form is. -/
theorem separatingLeft_compBilinForm_iff (hf : f ≠ 0) {B : BilinForm K M} :
    (f.compBilinForm B).SeparatingLeft ↔ B.SeparatingLeft := by
  refine ⟨fun h x hx ↦ h x fun y ↦ by simp [hx y], fun h x hx ↦ h x fun y ↦ ?_⟩
  refine ((isFrobeniusFunctional_iff_ne_zero f).2 hf).eq_zero_of_forall_right fun a ↦ ?_
  simpa using hx (a • y)

/-- The transfer along a nonzero functional is right-separating exactly when the form is. -/
theorem separatingRight_compBilinForm_iff (hf : f ≠ 0) {B : BilinForm K M} :
    (f.compBilinForm B).SeparatingRight ↔ B.SeparatingRight := by
  rw [← flip_separatingLeft, flip_compBilinForm, separatingLeft_compBilinForm_iff hf,
    flip_separatingLeft]

/-- The transfer along a nonzero functional is nondegenerate exactly when the form is. -/
theorem nondegenerate_compBilinForm_iff (hf : f ≠ 0) {B : BilinForm K M} :
    (f.compBilinForm B).Nondegenerate ↔ B.Nondegenerate :=
  and_congr (separatingLeft_compBilinForm_iff hf) (separatingRight_compBilinForm_iff hf)

/-- **Similitudes of a transferred form.** A `K`-linear endomorphism `g` scales the transfer of
`B` along a nonzero functional by `c : F` exactly when it scales `B` by `algebraMap F K c`. -/
theorem compl₁₂_compBilinForm_eq_smul_iff (hf : f ≠ 0) {B : BilinForm K M} {g : M →ₗ[K] M}
    {c : F} :
    (f.compBilinForm B).compl₁₂ (g.restrictScalars F) (g.restrictScalars F) =
        c • f.compBilinForm B ↔
      B.compl₁₂ g g = algebraMap F K c • B := by
  rw [compl₁₂_compBilinForm, algebraMap_smul, ← compBilinForm_smul, compBilinForm_inj hf]

variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
  [∀ i, Module F (V i)] [∀ i, IsScalarTower F K (V i)]

/-- **Similitudes of a transferred orthogonal sum.** A family `(gᵢ)` of `K`-linear endomorphisms
scales the transfer of the orthogonal sum of the `ψ i` along a nonzero functional by `c : F`
exactly when every `gᵢ` scales `ψ i` by the common multiplier `algebraMap F K c`. -/
theorem compl₁₂_compBilinForm_pi_piMap_eq_smul_iff (hf : f ≠ 0) {ψ : ∀ i, BilinForm K (V i)}
    {g : ∀ i, V i →ₗ[K] V i} {c : F} :
    (f.compBilinForm (BilinForm.pi ψ)).compl₁₂ ((LinearMap.piMap g).restrictScalars F)
        ((LinearMap.piMap g).restrictScalars F) = c • f.compBilinForm (BilinForm.pi ψ) ↔
      ∀ i, (ψ i).compl₁₂ (g i) (g i) = algebraMap F K c • ψ i := by
  rw [compl₁₂_compBilinForm_eq_smul_iff hf, BilinForm.compl₁₂_pi_piMap,
    ← BilinForm.pi_smul, BilinForm.pi_inj, funext_iff]
  simp only [Pi.smul_apply]

end Field

section Trace

variable {F K M : Type*} [Field F] [Field K] [Algebra F K] [AddCommMonoid M] [Module K M]
  [Module F M] [IsScalarTower F K M]

/-- **Trace transfer and separability.** For a finite extension of fields `K / F` and a
nondegenerate `K`-bilinear form `B` on a nonzero space, the `F`-bilinear form `Tr_{K/F} ∘ B` is
nondegenerate exactly when `K / F` is separable. For an inseparable extension the trace, and so
the transferred form, vanishes. -/
theorem nondegenerate_trace_compBilinForm_iff [FiniteDimensional F K] [Nontrivial M]
    {B : BilinForm K M} (hB : B.Nondegenerate) :
    ((Algebra.trace F K).compBilinForm B).Nondegenerate ↔ Algebra.IsSeparable F K := by
  refine ⟨fun h ↦ ?_, fun _ ↦ (nondegenerate_compBilinForm_iff (Algebra.trace_ne_zero F K)).2 hB⟩
  by_contra hsep
  rw [Algebra.trace_eq_zero_of_not_isSeparable hsep, zero_compBilinForm] at h
  exact BilinForm.not_nondegenerate_zero F M h

end Trace

end LinearMap
