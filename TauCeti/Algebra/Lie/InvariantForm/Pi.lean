/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.InvariantForm.Basic
public import TauCeti.Algebra.Lie.Pi
public import TauCeti.Algebra.Lie.BaseChange.Perfect

/-!
# Invariant forms on finite products of perfect Lie algebras

An invariant bilinear form pairs distinct perfect factors to zero. Consequently an invariant
symmetric form on a finite product of perfect Lie algebras is uniquely the sum of the pullbacks
of its restrictions to the factors. `TauCeti.LieModule.invariantFormsPiEquiv` packages this as a
linear equivalence, with forward and inverse evaluation formulas and a dimension formula.
This describes the independent level parameters for semisimple current algebras.

The orthogonality argument uses only perfectness, not nondegeneracy of the form, characteristic
zero, or simplicity of the factors.

## References

* V. G. Kac, *Infinite-Dimensional Lie Algebras*, Chapter 7, for invariant forms and levels
  on semisimple current algebras.
-/

public section

open LieAlgebra

namespace LinearMap.BilinForm.lieInvariant

variable {ι R : Type*} {L : ι → Type*} [CommRing R] [DecidableEq ι]
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra R (L i)]
  {Φ : LinearMap.BilinForm R (∀ i, L i)}

/-- An invariant form pairs a perfect factor to zero with every distinct factor. Symmetry of
the form and perfectness of the second factor are not required. -/
theorem apply_pi_single_eq_zero (hΦ : Φ.lieInvariant (∀ i, L i)) {i j : ι}
    (hi : derivedSeries R (L i) 1 = ⊤) (hij : i ≠ j) (x : L i) (y : L j) :
    Φ (Pi.single i x) (Pi.single j y) = 0 := by
  let f : L i →ₗ[R] R := (Φ.compl₁₂ (LinearMap.single R L i)
    (LinearMap.single R L j)).flip y
  have hf : Submodule.span R {⁅a, b⁆ | (a : L i) (b : L i)} ≤ f.ker := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, b, rfl⟩
    have h := hΦ (Pi.single i a) (Pi.single i b) (Pi.single j y)
    rw [LieAlgebra.Pi.lie_single_single_of_ne hij, map_zero, neg_zero] at h
    have hs := (LieHom.single R L i).map_lie a b
    simp only [LieHom.single_apply] at hs
    simpa [f, hs] using h
  exact hf (TauCeti.LieAlgebra.mem_span_lie_of_derivedSeries_one_eq_top hi x)

end LinearMap.BilinForm.lieInvariant

namespace TauCeti.LieModule

variable {ι R : Type*} {L : ι → Type*} [CommRing R]
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra R (L i)]

/-- Restrict an invariant symmetric form on a product to a single factor. -/
def invariantFormsPiRestrict [DecidableEq ι] (i : ι) :
    invariantForms R (∀ i, L i) (∀ i, L i) →ₗ[R] invariantForms R (L i) (L i) where
  toFun Φ := by
    let s := LieHom.single R L i
    refine ⟨(Φ : LinearMap.BilinForm R _).compl₁₂ s.toLinearMap s.toLinearMap,
      mem_invariantForms_iff.mpr ⟨?_, ?_⟩⟩
    · intro x y z
      simpa only [LinearMap.compl₁₂_apply, LieHom.coe_toLinearMap, LieHom.map_lie] using
        (mem_invariantForms_iff.mp Φ.2).1 (s x) (s y) (s z)
    · exact ⟨fun x y ↦ (mem_invariantForms_iff.mp Φ.2).2.eq _ _⟩
  map_add' Φ Ψ := by ext x y; rfl
  map_smul' r Φ := by ext x y; rfl

@[simp]
theorem invariantFormsPiRestrict_apply [DecidableEq ι] (i : ι)
    (Φ : invariantForms R (∀ i, L i) (∀ i, L i)) (x y : L i) :
    (invariantFormsPiRestrict i Φ : LinearMap.BilinForm R (L i)) x y =
      (Φ : LinearMap.BilinForm R _) (Pi.single i x) (Pi.single i y) := by
  simp [invariantFormsPiRestrict]

variable [Fintype ι]

/-- Sum the pullbacks of invariant symmetric forms along the coordinate projections. -/
def invariantFormsPiSum :
    (∀ i, invariantForms R (L i) (L i)) →ₗ[R]
      invariantForms R (∀ i, L i) (∀ i, L i) where
  toFun Φ := ⟨∑ i, (Φ i : LinearMap.BilinForm R (L i)).compl₁₂
      (LinearMap.proj i) (LinearMap.proj i),
    mem_invariantForms_iff.mpr ⟨(fun x y z ↦ by
      simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.proj_apply,
        LieAlgebra.Pi.bracket_apply]
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ (mem_invariantForms_iff.mp (Φ i).2).1 _ _ _),
    ⟨fun x y ↦ by
      simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.proj_apply]
      exact Finset.sum_congr rfl fun i _ ↦ (mem_invariantForms_iff.mp (Φ i).2).2.eq _ _⟩⟩⟩
  map_add' Φ Ψ := by ext x y; simp [Finset.sum_add_distrib]
  map_smul' r Φ := by ext x y; simp [Finset.mul_sum]

@[simp]
theorem invariantFormsPiSum_apply (Φ : ∀ i, invariantForms R (L i) (L i))
    (x y : ∀ i, L i) :
    (invariantFormsPiSum Φ : LinearMap.BilinForm R _) x y =
      ∑ i, (Φ i : LinearMap.BilinForm R (L i)) (x i) (y i) := by
  simp [invariantFormsPiSum]

variable [DecidableEq ι]

/-- Restriction to a factor recovers the corresponding summand. -/
@[simp]
theorem invariantFormsPiRestrict_sum (Φ : ∀ i, invariantForms R (L i) (L i)) (i : ι) :
    invariantFormsPiRestrict i (invariantFormsPiSum Φ) = Φ i := by
  ext x y
  simp only [invariantFormsPiRestrict_apply, invariantFormsPiSum_apply]
  rw [Fintype.sum_eq_single i (fun j hji ↦ by simp [Pi.single_eq_of_ne hji])]
  simp

/-- An invariant form on a finite product of perfect Lie algebras is the sum of its diagonal
blocks. In particular it has no mixed terms. -/
theorem invariantForms_apply_eq_sum
    (hL : ∀ i, derivedSeries R (L i) 1 = ⊤)
    (Φ : invariantForms R (∀ i, L i) (∀ i, L i)) (x y : ∀ i, L i) :
    (Φ : LinearMap.BilinForm R _) x y =
      ∑ i, (Φ : LinearMap.BilinForm R _) (Pi.single i (x i)) (Pi.single i (y i)) := by
  conv_lhs => rw [← Finset.univ_sum_single x, ← Finset.univ_sum_single y]
  simp only [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact Fintype.sum_eq_single i fun j hji ↦
    (mem_invariantForms_iff.mp Φ.2).1.apply_pi_single_eq_zero (hL j) hji _ _

/-- Summing the restrictions reconstructs a form on a finite product of perfect Lie algebras. -/
-- State perfectness in bracket form because it is the simp normal form of `derivedSeries` at one.
@[simp]
theorem invariantFormsPiSum_restrict
    (hL : ∀ i, ⁅(⊤ : LieIdeal R (L i)), (⊤ : LieIdeal R (L i))⁆ = ⊤)
    (Φ : invariantForms R (∀ i, L i) (∀ i, L i)) :
    invariantFormsPiSum (fun i ↦ invariantFormsPiRestrict i Φ) = Φ := by
  apply Subtype.ext
  apply LinearMap.ext₂
  intro x y
  simpa only [invariantFormsPiSum_apply, invariantFormsPiRestrict_apply] using
    (invariantForms_apply_eq_sum (fun i ↦ by
      simpa only [derivedSeries_def, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero]
        using hL i) Φ x y).symm

/-- Invariant symmetric forms on a finite product of perfect Lie algebras are exactly families
of invariant symmetric forms on its factors. The inverse sums coordinate pullbacks. -/
def invariantFormsPiEquiv (hL : ∀ i, derivedSeries R (L i) 1 = ⊤) :
    invariantForms R (∀ i, L i) (∀ i, L i) ≃ₗ[R]
      (∀ i, invariantForms R (L i) (L i)) :=
  LinearEquiv.ofLinearMap
    (LinearMap.pi invariantFormsPiRestrict) invariantFormsPiSum
    (by
      apply LinearMap.ext
      intro Φ
      funext i
      exact invariantFormsPiRestrict_sum Φ i)
    (by
      apply LinearMap.ext
      intro Φ
      exact invariantFormsPiSum_restrict (fun i ↦ by
        simpa only [derivedSeries_def, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero]
          using hL i) Φ)

@[simp]
theorem invariantFormsPiEquiv_apply (hL : ∀ i, derivedSeries R (L i) 1 = ⊤)
    (Φ : invariantForms R (∀ i, L i) (∀ i, L i)) (i : ι) :
    invariantFormsPiEquiv hL Φ i = invariantFormsPiRestrict i Φ := (rfl)

@[simp]
theorem invariantFormsPiEquiv_symm_apply (hL : ∀ i, derivedSeries R (L i) 1 = ⊤)
    (Φ : ∀ i, invariantForms R (L i) (L i)) :
    (invariantFormsPiEquiv hL).symm Φ = invariantFormsPiSum Φ := (rfl)

omit [DecidableEq ι] in
/-- The dimension of invariant symmetric forms on a finite product of perfect Lie algebras
is the sum of the dimensions for its factors. -/
theorem finrank_invariantForms_pi {K : Type*} [Field K] [∀ i, LieAlgebra K (L i)]
    [∀ i : ι, Module.Finite K (invariantForms K (L i) (L i))]
    (hL : ∀ i, derivedSeries K (L i) 1 = ⊤) :
    Module.finrank K (invariantForms K (∀ i, L i) (∀ i, L i)) =
      ∑ i, Module.finrank K (invariantForms K (L i) (L i)) := by
  classical
  -- Specify the scalar ring in the subgroup instance for this opaque submodule.
  let (i : ι) : AddCommGroup (invariantForms K (L i) (L i)) :=
    @Submodule.addCommGroup K (LinearMap.BilinForm K (L i)) _ _ _ _
  rw [(invariantFormsPiEquiv hL).finrank_eq, Module.finrank_pi_fintype]

end TauCeti.LieModule
