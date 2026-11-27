/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.GSpin.CliffordGroup
public import TauCeti.LinearAlgebra.QuadraticForm.Matrix
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Base change of general spin groups

Let `q` be a quadratic form on `R^n` and `A` a commutative `R`-algebra, and let
`q_A = QuadraticForm.baseChangeForm q A` be the form on `A^n` with the same coefficients; nothing
assumes `2` invertible. The inclusion `R^n → A^n` sends `q` to `q_A`
(`QuadraticForm.baseChangeForm_algebraMap_comp`), so it induces a morphism of `R`-algebras
`CliffordAlgebra.baseChangeHom q A : C(q) → C(q_A)` with `ι(x) ↦ ι(x_A)`. It preserves the even
part and commutes with `reverse`.

Every vector of `A^n` is an `A`-linear combination of the images of the coordinate vectors, so
`ι(A^n)` is the `A`-span of the images of `ι(R^n)`. Hence if `g ∈ C(q)^×` is even and
`g ι(R^n) g⁻¹ = ι(R^n)`, its image in `C(q_A)^×` is even with `g ι(A^n) g⁻¹ ⊆ ι(A^n)`, and
likewise for `g⁻¹`: base change maps `GSpin(q)` to `GSpin(q_A)`
(`CliffordAlgebra.specialCliffordGroupBaseChange`), compatibly with the norm
`ν(g) = reverse(g) g`, and so maps `Spin(q)` to `Spin(q_A)`. These are the transition maps of the
functors `A ↦ GSpin(q_A)` and `A ↦ Spin(q_A)` on points.

## Main results

* `QuadraticForm.baseChangeForm_algebraMap_comp`: `q_A(x_A) = q(x)`.
* `CliffordAlgebra.baseChangeHom`: the algebra morphism `C(q) → C(q_A)`.
* `CliffordAlgebra.baseChangeHom_mem_even`, `CliffordAlgebra.baseChangeHom_reverse`: it preserves
  the even part and commutes with `reverse`.
* `CliffordAlgebra.specialCliffordGroupBaseChange`: the homomorphism `GSpin(q) → GSpin(q_A)`.
* `CliffordAlgebra.specialCliffordGroupNorm_specialCliffordGroupBaseChange`: compatibility with
  the norm `ν`.
* `CliffordAlgebra.units_map_baseChangeHom_mem_normOneSpinGroup`: `Spin(q)` maps to `Spin(q_A)`.
-/

public section

namespace QuadraticForm

variable {R n : Type*} [CommRing R] [Fintype n] [LinearOrder n] (A : Type*) [CommRing A]
  [Algebra R A]

/-- **The form `q_A` restricts to `q`**: on a vector with coordinates in `R`, `q_A` takes the value
of `q`. -/
theorem baseChangeForm_algebraMap_comp (q : QuadraticForm R (n → R)) (x : n → R) :
    baseChangeForm q A (algebraMap R A ∘ x) = algebraMap R A (q x) := by
  conv_rhs => rw [← baseChangeForm_self q]
  rw [baseChangeForm_apply, baseChangeForm_apply, RingHom.map_dotProduct, Algebra.algebraMap_self,
    RingHom.coe_id, Matrix.map_id]
  congr 1
  ext i
  rw [Function.comp_apply, RingHom.map_mulVec]

end QuadraticForm

namespace CliffordAlgebra

open QuadraticForm (baseChangeForm baseChangeForm_algebraMap_comp)

variable {R n : Type*} [CommRing R] [Fintype n] [LinearOrder n] (q : QuadraticForm R (n → R))
  (A : Type*) [CommRing A] [Algebra R A]

/-- The morphism of `R`-algebras `C(q) → C(q_A)` induced by the inclusion `R^n → A^n`. -/
noncomputable def baseChangeHom : CliffordAlgebra q →ₐ[R] CliffordAlgebra (baseChangeForm q A) :=
  lift q ⟨(CliffordAlgebra.ι (baseChangeForm q A)).restrictScalars R ∘ₗ
      (Algebra.linearMap R A).compLeft n,
    fun x ↦ by
      change CliffordAlgebra.ι _ (algebraMap R A ∘ x) *
        CliffordAlgebra.ι _ (algebraMap R A ∘ x) = _
      rw [ι_sq_scalar, baseChangeForm_algebraMap_comp, ← IsScalarTower.algebraMap_apply]⟩

variable {q A}

/-- `baseChangeHom` sends `ι(x)` to `ι(x_A)`. -/
@[simp]
theorem baseChangeHom_ι (x : n → R) :
    baseChangeHom q A (CliffordAlgebra.ι q x) =
      CliffordAlgebra.ι (baseChangeForm q A) (algebraMap R A ∘ x) := by
  rw [baseChangeHom, lift_ι_apply]
  rfl

/-- Every vector of `ι(A^n)` is an `A`-linear combination of images of vectors of `ι(R^n)`: of the
coordinate vectors. -/
theorem ι_eq_sum_smul_baseChangeHom (m : n → A) :
    CliffordAlgebra.ι (baseChangeForm q A) m =
      ∑ i, m i • baseChangeHom q A (CliffordAlgebra.ι q (Pi.single i 1)) := by
  conv_lhs => rw [pi_eq_sum_univ m]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, baseChangeHom_ι]
  congr 2
  ext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj, Ne.symm hj]

/-- `baseChangeHom` preserves the even part. -/
theorem baseChangeHom_mem_even {x : CliffordAlgebra q} (hx : x ∈ even q) :
    baseChangeHom q A x ∈ even (baseChangeForm q A) := by
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at hx ⊢
  induction x, hx using even_induction with
  | algebraMap r =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R A]
    exact SetLike.algebraMap_mem_graded _ _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | ι_mul_ι_mul m₁ m₂ x _ hx =>
    rw [map_mul, map_mul, baseChangeHom_ι, baseChangeHom_ι]
    simpa only [add_zero] using SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero _ _ _) hx

/-- `baseChangeHom` commutes with `reverse`. -/
theorem baseChangeHom_reverse (x : CliffordAlgebra q) :
    baseChangeHom q A (reverse x) = reverse (baseChangeHom q A x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [reverse.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply R A, reverse.commutes]
  | ι x => rw [reverse_ι, baseChangeHom_ι, reverse_ι]
  | mul x y hx hy => rw [reverse.map_mul, map_mul, map_mul, hx, hy, reverse.map_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Base change maps `GSpin(q)` into `GSpin(q_A)`.** -/
theorem units_map_baseChangeHom_mem_specialCliffordGroup {g : (CliffordAlgebra q)ˣ}
    (hg : g ∈ specialCliffordGroup q) :
    Units.map (baseChangeHom q A : CliffordAlgebra q →* CliffordAlgebra (baseChangeForm q A)) g ∈
      specialCliffordGroup (baseChangeForm q A) := by
  rw [mem_specialCliffordGroup_iff_conj] at hg ⊢
  obtain ⟨heven, hconj, hconj'⟩ := hg
  -- conjugation by the image of `g` or `g⁻¹` is `A`-linear and preserves the images of
  -- `ι(R^n)`
  have key (u v : CliffordAlgebra q)
      (h : ∀ m, u * CliffordAlgebra.ι q m * v ∈ LinearMap.range (CliffordAlgebra.ι q))
      (m : n → A) : baseChangeHom q A u * CliffordAlgebra.ι (baseChangeForm q A) m *
        baseChangeHom q A v ∈ LinearMap.range (CliffordAlgebra.ι (baseChangeForm q A)) := by
    rw [ι_eq_sum_smul_baseChangeHom, Finset.mul_sum, Finset.sum_mul]
    refine sum_mem fun i _ ↦ ?_
    rw [mul_smul_comm, smul_mul_assoc, ← map_mul, ← map_mul]
    obtain ⟨w, hw⟩ := h (Pi.single i 1)
    rw [← hw, baseChangeHom_ι]
    exact Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _)
  refine ⟨baseChangeHom_mem_even heven, fun m ↦ ?_, fun m ↦ ?_⟩
  · exact key _ _ hconj m
  · exact key _ _ hconj' m

/-- **The base change homomorphism `GSpin(q) → GSpin(q_A)`**, the transition map of the functor
`A ↦ GSpin(q_A)` on points. -/
noncomputable def specialCliffordGroupBaseChange (q : QuadraticForm R (n → R)) (A : Type*)
    [CommRing A] [Algebra R A] :
    specialCliffordGroup q →* specialCliffordGroup (baseChangeForm q A) :=
  ((Units.map (baseChangeHom q A : CliffordAlgebra q →* CliffordAlgebra (baseChangeForm q A))).comp
    (specialCliffordGroup q).subtype).codRestrict _ fun g ↦
      units_map_baseChangeHom_mem_specialCliffordGroup g.property

/-- The base change homomorphism applies `baseChangeHom` to the underlying element. -/
@[simp]
theorem coe_specialCliffordGroupBaseChange (g : specialCliffordGroup q) :
    (((specialCliffordGroupBaseChange q A g : (CliffordAlgebra (baseChangeForm q A))ˣ)) :
        CliffordAlgebra (baseChangeForm q A)) =
      baseChangeHom q A ((g : (CliffordAlgebra q)ˣ) : CliffordAlgebra q) := by
  simp [specialCliffordGroupBaseChange]

/-- **Base change is compatible with the norm** `ν(g) = reverse(g) g`. -/
theorem specialCliffordGroupNorm_specialCliffordGroupBaseChange (g : specialCliffordGroup q) :
    ((specialCliffordGroupNorm (baseChangeForm q A) (specialCliffordGroupBaseChange q A g) :
        (CliffordAlgebra (baseChangeForm q A))ˣ) : CliffordAlgebra (baseChangeForm q A)) =
      baseChangeHom q A ((specialCliffordGroupNorm q g : (CliffordAlgebra q)ˣ) :
        CliffordAlgebra q) := by
  rw [coe_specialCliffordGroupNorm, coe_specialCliffordGroupNorm,
    coe_specialCliffordGroupBaseChange, map_mul, baseChangeHom_reverse]

/-- **Base change maps `Spin(q)` into `Spin(q_A)`.** -/
theorem units_map_baseChangeHom_mem_normOneSpinGroup {g : (CliffordAlgebra q)ˣ}
    (hg : g ∈ normOneSpinGroup q) :
    Units.map (baseChangeHom q A : CliffordAlgebra q →* CliffordAlgebra (baseChangeForm q A)) g ∈
      normOneSpinGroup (baseChangeForm q A) := by
  rw [mem_normOneSpinGroup_iff] at hg ⊢
  refine ⟨units_map_baseChangeHom_mem_specialCliffordGroup hg.1, ?_⟩
  rw [Units.coe_map, MonoidHom.coe_ofClass, ← baseChangeHom_reverse, ← map_mul, hg.2, map_one]

end CliffordAlgebra
