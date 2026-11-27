/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Flat.EffectiveDescent

/-!
# Degree-one exactness of the Amitsur complex

For an `R`-algebra `S` and an `R`-module `M`, let `C₀ = S ⊗[R] M` and
`Cᵢ₊₁ = S ⊗[R] Cᵢ`. This file defines the first two differentials
`TauCeti.Amitsur.d₀ : C₀ →ₗ[R] C₁` and `TauCeti.Amitsur.d₁ : C₁ →ₗ[R] C₂`.
The sign of `d₀` agrees with `Module.FaithfullyFlat.exact_mk_one_lTensor_sub_mk_one`:
the insertion on the right has positive sign. The three insertions in `d₁` have signs
`+ - +`, starting on the left.

For a faithfully flat algebra, `TauCeti.Amitsur.exact_d₀_d₁` says that every additive
descent cocycle is a coboundary. This is the module-theoretic input for trivializing
vector-group torsors over affine schemes. The ambiguity of a primitive is exactly an
element `1 ⊗ m`, by `TauCeti.Amitsur.d₀_eq_d₀_iff` and degree-zero exactness.

The contracting homotopy after tensoring with `S` multiplies the first two factors,
as in the proof of degree-zero exactness in `TauCeti.RingTheory.Flat.EffectiveDescent`.

## References

* The Stacks Project, Lemma 35.3.6, Tag 023M (exactness of the extended Amitsur complex).
-/

public section

open TensorProduct

namespace TauCeti.Amitsur

variable {R : Type*} [CommRing R] (S M : Type*) [Ring S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- The degree-zero Amitsur differential, with the right insertion positive. -/
noncomputable def d₀ : S ⊗[R] M →ₗ[R] S ⊗[R] (S ⊗[R] M) :=
  (TensorProduct.mk R S M 1).lTensor S - TensorProduct.mk R S (S ⊗[R] M) 1

/-- The degree-one Amitsur differential: unit insertions with signs `+ - +`
from the left. -/
noncomputable def d₁ : S ⊗[R] (S ⊗[R] M) →ₗ[R] S ⊗[R] (S ⊗[R] (S ⊗[R] M)) :=
  TensorProduct.mk R S (S ⊗[R] (S ⊗[R] M)) 1 + (d₀ S M).lTensor S

@[simp]
theorem d₀_tmul (s : S) (m : M) :
    d₀ S M (s ⊗ₜ[R] m) = s ⊗ₜ[R] (1 ⊗ₜ[R] m) - 1 ⊗ₜ[R] (s ⊗ₜ[R] m) := by
  simp [d₀]

@[simp]
theorem d₁_tmul (s t : S) (m : M) :
    d₁ S M (s ⊗ₜ[R] (t ⊗ₜ[R] m)) =
      1 ⊗ₜ[R] (s ⊗ₜ[R] (t ⊗ₜ[R] m)) - s ⊗ₜ[R] (1 ⊗ₜ[R] (t ⊗ₜ[R] m)) +
        s ⊗ₜ[R] (t ⊗ₜ[R] (1 ⊗ₜ[R] m)) := by
  simp [d₁, tmul_sub]
  abel

/-- The first two Amitsur differentials compose to zero over any algebra. -/
@[simp]
theorem d₁_comp_d₀ : d₁ (R := R) S M ∘ₗ d₀ S M = 0 := by
  ext s m
  simp

/-- Over a faithfully flat algebra, every degree-one Amitsur cocycle is a coboundary. -/
theorem exact_d₀_d₁ [Module.FaithfullyFlat R S] :
    Function.Exact (d₀ (R := R) S M) (d₁ S M) := by
  -- Multiplication of the first two factors contracts the complex after base change.
  let h' := TensorProduct.lift
    (Algebra.lsmul R R (A := S) (S ⊗[R] (S ⊗[R] M))).toLinearMap
  let h'' := TensorProduct.lift
    (Algebra.lsmul R R (A := S) (S ⊗[R] (S ⊗[R] (S ⊗[R] M)))).toLinearMap
  have key : h'' ∘ₗ (d₁ S M).lTensor S =
      LinearMap.id + (d₀ S M).lTensor S ∘ₗ h' := by
    ext s t u m
    simp [h', h'', d₁, d₀, smul_tmul']
  refine Module.FaithfullyFlat.lTensor_reflects_exact R S _ _ fun y ↦ ⟨fun hy ↦ ?_, ?_⟩
  · refine ⟨-h' y, ?_⟩
    have hk := congr($key y)
    simp only [LinearMap.comp_apply, hy, map_zero, LinearMap.add_apply,
      LinearMap.id_apply] at hk
    simpa only [map_neg] using (eq_neg_of_add_eq_zero_left hk.symm).symm
  · rintro ⟨x, rfl⟩
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, d₁_comp_d₀,
      LinearMap.lTensor_zero, LinearMap.zero_apply]

/-- Two primitives have the same coboundary precisely when their difference comes from `M`. -/
theorem d₀_eq_d₀_iff [Module.FaithfullyFlat R S] (x y : S ⊗[R] M) :
    d₀ S M x = d₀ S M y ↔ ∃ m : M, x - y = 1 ⊗ₜ[R] m := by
  rw [← sub_eq_zero, ← map_sub]
  exact (Module.FaithfullyFlat.exact_mk_one_lTensor_sub_mk_one S M (x - y)).trans
    (exists_congr fun _ ↦ eq_comm)

end TauCeti.Amitsur
