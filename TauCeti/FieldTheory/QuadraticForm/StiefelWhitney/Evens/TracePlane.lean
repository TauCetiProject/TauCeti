/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Trace.Basic
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension

/-!
# The transferred plane inside the separable closure

Let `L/K` be a separable quadratic extension, let `σ : L → Kˢ` be a `K`-embedding, and choose
`s ∈ G_K` outside the subgroup fixing `σ(L)`. For `a ∈ L` and a square root `r² = σ(a)`, the map

```text
φ(y) = (σ(y) r, s(σ(y) r))
```

realizes the transferred quadratic plane `y ↦ Tr_{L/K}(a y²)` inside `(Kˢ)²`: its standard dot
product satisfies

```text
φ(y) · φ(y') = Tr_{L/K}(a y y').
```

The two coordinates correspond to the two embeddings of the quadratic extension into `Kˢ`, namely
`σ` and `s ∘ σ`. This realization is the plane on which the induced Kummer representation acts in
the computation of the Evens norm of a Kummer class.

## Main definitions

* `TauCeti.kummerPoint`: the point `φ(y) = (σ(y) r, s(σ(y) r))` of `(Kˢ)²`.

## Main results

* `TauCeti.kummerPoint_dotProduct`: the standard dot product on the image of `φ` is the twisted
  trace pairing `(y, y') ↦ Tr_{L/K}(a y y')`.

## References

* J.-P. Serre, *L'invariant de Witt de la forme Tr(x²)*, Comment. Math. Helv. **59** (1984),
  651–676, second proof of Théorème 1′.
* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations galoisiennes
  réelles*, Invent. Math. **78** (1984), 223–256, Lemme II.2.1.
-/

public section

noncomputable section

namespace TauCeti

universe u v

variable {K : Type u} [Field K]

/-- **The point of the transferred plane associated to `y ∈ L`:**
`φ(y) = (σ(y) r, s(σ(y) r)) ∈ (Kˢ)²`. When `r² = σ(a)` and `s` represents the nontrivial
coset of `G_L` in `G_K`, the image of `φ` carries the transferred form `Tr_*⟨a⟩`. -/
def kummerPoint {L : Type v} [Field L] [Algebra K L]
    (σ : L →ₐ[K] SeparableClosure K) (r : SeparableClosure K) (s : AbsoluteGaloisGroup K)
    (y : L) : Fin 2 → SeparableClosure K :=
  ![σ y * r, s (σ y * r)]

section kummerPoint

variable {L : Type v} [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K) (r : SeparableClosure K) (s : AbsoluteGaloisGroup K)

/-- `kummerPoint σ r s y` is the vector `![σ y * r, s (σ y * r)]`. -/
theorem kummerPoint_def (y : L) : kummerPoint σ r s y = ![σ y * r, s (σ y * r)] := by
  unfold kummerPoint
  rfl

/-- The first coordinate of `kummerPoint σ r s y` is `σ(y) r`. -/
@[simp]
theorem kummerPoint_apply_zero (y : L) : kummerPoint σ r s y 0 = σ y * r := by
  simp [kummerPoint_def]

/-- The second coordinate of `kummerPoint σ r s y` is `s(σ(y) r)`. -/
@[simp]
theorem kummerPoint_apply_one (y : L) : kummerPoint σ r s y 1 = s (σ y * r) := by
  simp [kummerPoint_def]

/-- `kummerPoint σ r s` is additive in `y`. -/
theorem kummerPoint_add (y y' : L) :
    kummerPoint σ r s (y + y') = kummerPoint σ r s y + kummerPoint σ r s y' := by
  ext i
  fin_cases i <;> simp [add_mul]

/-- `kummerPoint σ r s` is `K`-homogeneous in `y`. -/
theorem kummerPoint_smul (c : K) (y : L) :
    kummerPoint σ r s (c • y) = c • kummerPoint σ r s y := by
  ext i
  fin_cases i <;> simp

end kummerPoint

/-- **The transferred-plane identity:** if `L/K` is separable quadratic, `r² = σ(a)`, and
`s ∈ G_K` does not fix `σ(L)`, then
`φ(y) · φ(y') = Tr_{L/K}(a y y')` after embedding into `Kˢ`.

Thus the standard quadratic form on `(Kˢ)²`, restricted along `y ↦ φ(y)`, is the scalar extension
of the trace transfer of the line `⟨a⟩`. -/
theorem kummerPoint_dotProduct {L : Type v} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (σ : L →ₐ[K] SeparableClosure K) (hdeg : Module.finrank K L = 2) (a : L)
    (r : SeparableClosure K) (hr : r ^ 2 = σ a) (s : AbsoluteGaloisGroup K)
    (hs : s ∉ galoisSubgroup K L σ) (y y' : L) :
    kummerPoint σ r s y ⬝ᵥ kummerPoint σ r s y' =
      algebraMap K (SeparableClosure K) (Algebra.trace K L (a * y * y')) := by
  classical
  let τ : L →ₐ[K] SeparableClosure K := s.toAlgHom.comp σ
  have hτσ : τ ≠ σ := by
    intro h
    apply hs
    rw [mem_galoisSubgroup_iff]
    intro z
    simpa only [τ, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply] using DFunLike.congr_fun h z
  let ι : SeparableClosure K →ₐ[K] AlgebraicClosure K :=
    IsScalarTower.toAlgHom K (SeparableClosure K) (AlgebraicClosure K)
  let σ' : L →ₐ[K] AlgebraicClosure K := ι.comp σ
  let τ' : L →ₐ[K] AlgebraicClosure K := ι.comp τ
  have hστ : σ' ≠ τ' := by
    intro h
    apply hτσ
    apply DFunLike.ext _ _
    intro z
    apply ι.injective
    exact (DFunLike.congr_fun h z).symm
  have hcard : Fintype.card (L →ₐ[K] AlgebraicClosure K) = 2 := by
    simpa only [hdeg] using AlgHom.card K L (AlgebraicClosure K)
  have huniv : (Finset.univ : Finset (L →ₐ[K] AlgebraicClosure K)) = {σ', τ'} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hστ, hcard]
  have htrace (z : L) :
      algebraMap K (SeparableClosure K) (Algebra.trace K L z) = σ z + τ z := by
    apply ι.injective
    calc
      ι (algebraMap K (SeparableClosure K) (Algebra.trace K L z)) =
          algebraMap K (AlgebraicClosure K) (Algebra.trace K L z) := by simp [ι]
      _ = ∑ ψ : L →ₐ[K] AlgebraicClosure K, ψ z :=
        trace_eq_sum_embeddings (AlgebraicClosure K)
      _ = σ' z + τ' z := by rw [huniv, Finset.sum_pair hστ]
      _ = ι (σ z + τ z) := by simp [σ', τ']
  rw [htrace]
  simp only [kummerPoint, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, map_mul, τ]
  have hr' : r * r = σ a := by simpa only [pow_two] using hr
  have hsr' : s r * s r = s (σ a) := by rw [← map_mul, hr']
  ring_nf at hr' hsr' ⊢
  rw [hr', hsr']
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply]
  ring

end TauCeti
