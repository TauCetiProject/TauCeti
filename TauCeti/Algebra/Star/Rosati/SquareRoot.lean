/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import TauCeti.Algebra.Star.Rosati.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import TauCeti.Algebra.Star.Positive
import TauCeti.Algebra.Star.SelfAdjoint.LinearMap
import TauCeti.Analysis.InnerProductSpace.Positive.SquareRoot
import TauCeti.Analysis.InnerProductSpace.Symmetric.FunctionalCalculus

/-!
# Internal positive square roots for Rosati-positive elements

In a finite-dimensional real star algebra `E` with cyclic `t : E →ₗ[ℝ] ℝ` strictly positive on
`x * star x`, every `IsRosatiPositive` element `s` is a unit and admits a unique
`IsRosatiPositive` square root `r` with `r, r⁻¹ ∈ ℝ[s]` (`TauCeti.exists_rosatiPositive_sq_eq`),
via `LinearMap.IsPositive.sqrt` and `LinearMap.IsSymmetric.exists_aeval_eq_cfc`.

## References

* J. Voight, *Quaternion Algebras*, GTM 288, Springer (2021), §8.4.
* M. Lipnowski and J. Tsimerman, *How large is A_g(F_q)?*, arXiv:1511.02212v1, §4.3.2.
-/

public section

namespace TauCeti

open scoped Polynomial

private theorem hasEigenvalue_lmul_pos {E : Type*} [Ring E] [Algebra ℝ E] [StarRing E]
    (t : E →ₗ[ℝ] ℝ) (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) {s : E}
    (hs : IsRosatiPositive t s) {μ : ℝ} (hμ : (Algebra.lmul ℝ E s).HasEigenvalue μ) : 0 < μ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have h1 := hs.trace_mul_mul_star_pos hv.2
  rw [show s * v = μ • v by simpa using Module.End.mem_eigenspace_iff.mp hv.1,
    smul_mul_assoc, map_smul, smul_eq_mul] at h1
  exact pos_of_mul_pos_left h1 (hpos v hv.2).le

private theorem exists_rosatiPositive_sq_eq_of_star_invariant {E : Type*} [Ring E] [Algebra ℝ E]
    [StarRing E] [Module.Finite ℝ E] (t : E →ₗ[ℝ] ℝ)
    (hcyc : ∀ x y : E, t (x * y) = t (y * x)) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) (s : E) (hs : IsRosatiPositive t s) :
    IsUnit s ∧ ∃ r : Eˣ, IsRosatiPositive t r ∧ (r : E) * r = s ∧
      (r : E) ∈ Algebra.adjoin ℝ ({s} : Set E) ∧
      ((r⁻¹ : Eˣ) : E) ∈ Algebra.adjoin ℝ ({s} : Set E) ∧
      (∀ x : E, Commute x s → Commute x r ∧ Commute x ((r⁻¹ : Eˣ) : E)) ∧
      ∀ r' : E, IsRosatiPositive t r' → r' * r' = s → r' = r := by
  let core := rosatiInnerProductCore t hstar hpos
  let _ := core.toNormedAddCommGroup; let _ := InnerProductSpace.ofCore core.toCore
  have hT := isPositive_lmul_of_isRosatiPositive t hcyc hstar hpos hs
  have hsqrt : hT.sqrt = hT.isSymmetric.cfc Real.sqrt :=
    (hT.isSymmetric.eq_cfc_iff Real.sqrt).mpr fun _ _ hx ↦ hT.sqrt_apply_of_apply_eq_smul hx
  obtain ⟨p, hp⟩ := hT.isSymmetric.exists_aeval_eq_cfc Real.sqrt
  obtain ⟨q, hq⟩ := hT.isSymmetric.exists_aeval_eq_cfc (fun μ ↦ (Real.sqrt μ)⁻¹)
  simp only [Algebra.algebraMap_self, Polynomial.map_id] at hp hq
  set r : E := Polynomial.aeval s p; set rInv : E := Polynomial.aeval s q
  have hlmul_r : Algebra.lmul ℝ E r = hT.sqrt := by
    rw [hsqrt, ← hp]; exact (Polynomial.aeval_algHom_apply (Algebra.lmul ℝ E) s p).symm
  have hrInv : Algebra.lmul ℝ E rInv = hT.isSymmetric.cfc (fun μ ↦ (Real.sqrt μ)⁻¹) :=
    hq ▸ (Polynomial.aeval_algHom_apply (Algebra.lmul ℝ E) s q).symm
  have hmul {f g : ℝ → ℝ} {a b : E} (ha : Algebra.lmul ℝ E a = hT.isSymmetric.cfc f)
      (hb : Algebra.lmul ℝ E b = hT.isSymmetric.cfc g)
      (hfg : ∀ μ, (Algebra.lmul ℝ E s).HasEigenvalue μ → f μ * g μ = 1) : a * b = 1 :=
    Algebra.lmul_injective (R := ℝ) (by
      rw [map_mul, map_one, ha, hb, ← hT.isSymmetric.cfc_mul, ← hT.isSymmetric.cfc_one]
      exact hT.isSymmetric.cfc_congr hfg)
  let u : Eˣ := ⟨r, rInv,
    hmul (hlmul_r.trans hsqrt) hrInv
      fun _ hμ ↦ mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (hasEigenvalue_lmul_pos t hpos hs hμ)),
    hmul hrInv (hlmul_r.trans hsqrt)
      fun _ hμ ↦ inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (hasEigenvalue_lmul_pos t hpos hs hμ))⟩
  have hadj (f : ℝ[X]) : Polynomial.aeval s f ∈ Algebra.adjoin ℝ ({s} : Set E) :=
    Polynomial.aeval_mem_adjoin_singleton ℝ s
  have hcom {x a : E} (ha : a ∈ Algebra.adjoin ℝ ({s} : Set E)) (hx : Commute x s) :
      Commute x a := Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha (by simpa using hx)
  refine ⟨hs.isUnit, u, isRosatiPositive_of_isPositive_lmul t hcyc hstar hpos
      (hlmul_r ▸ hT.sqrt_isPositive) (fun _ _ h ↦ by simpa using congrArg ((↑u⁻¹ : E) * ·) h),
    Algebra.lmul_injective (R := ℝ) (by rw [map_mul, hlmul_r, Module.End.mul_eq_comp, hT.sqrt_sq]),
    hadj p, hadj q, fun _ hx ↦ ⟨hcom (hadj p) hx, hcom (hadj q) hx⟩,
    fun r' hr' hr'sq ↦ Algebra.lmul_injective (R := ℝ) <| by
      rw [hlmul_r]; exact hT.sqrt_unique (isPositive_lmul_of_isRosatiPositive t hcyc hstar hpos hr')
        (by rw [← Module.End.mul_eq_comp, ← map_mul, hr'sq])⟩

/-- **Internal positive square roots.** In a finite-dimensional real star algebra with a cyclic
linear functional `t : E →ₗ[ℝ] ℝ` strictly positive on `x * star x`, every element `s` with
`IsRosatiPositive t s` is a unit and admits a unique root `r` with `IsRosatiPositive t r` and
`r * r = s`. Both `r` and `r⁻¹` lie in `ℝ[s]` and commute with every element commuting with `s`.

Constructed by passing to the star-symmetrized functional, taking the positive operator square
root `LinearMap.IsPositive.sqrt` (unique by `LinearMap.IsPositive.sqrt_unique`), and expressing
`sqrt` and its inverse as polynomials via `LinearMap.IsSymmetric.exists_aeval_eq_cfc`. -/
theorem exists_rosatiPositive_sq_eq {E : Type*} [Ring E] [Algebra ℝ E] [StarRing E]
    [Module.Finite ℝ E] (t : E →ₗ[ℝ] ℝ) (hcyclic : ∀ x y : E, t (x * y) = t (y * x))
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) (s : E) (hs : IsRosatiPositive t s) :
    IsUnit s ∧ ∃ r : Eˣ, IsRosatiPositive t r ∧ (r : E) * r = s ∧
      (r : E) ∈ Algebra.adjoin ℝ ({s} : Set E) ∧
      ((r⁻¹ : Eˣ) : E) ∈ Algebra.adjoin ℝ ({s} : Set E) ∧
      (∀ x : E, Commute x s → Commute x r ∧ Commute x ((r⁻¹ : Eˣ) : E)) ∧
      ∀ r' : E, IsRosatiPositive t r' → r' * r' = s → r' = r := by
  have : StarModule ℝ E := starModule_of_trace_mul_star_pos t hpos
  let t' : E →ₗ[ℝ] ℝ := (t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)
  have hiff (a : E) : IsRosatiPositive t' a ↔ IsRosatiPositive t a :=
    isRosatiPositive_iff_of_symmetrize
      (fun x ↦ by simpa [t', div_eq_inv_mul] using LinearMap.comp_selfAdjointPart_apply t x) hcyclic
  obtain ⟨hsU, r, hrpos, hrsq, hrmem, hrImem, hcomm, huniq⟩ :=
    exists_rosatiPositive_sq_eq_of_star_invariant t' (LinearMap.comp_selfAdjointPart_cyclic hcyclic)
      (LinearMap.comp_selfAdjointPart_star t)
      (fun _ hx ↦ LinearMap.comp_selfAdjointPart_mul_star_pos hpos hx) s ((hiff s).mpr hs)
  exact ⟨hsU, r, (hiff r).mp hrpos, hrsq, hrmem, hrImem, hcomm,
    fun r' hr' hr'sq ↦ huniq r' ((hiff r').mpr hr') hr'sq⟩

end TauCeti
