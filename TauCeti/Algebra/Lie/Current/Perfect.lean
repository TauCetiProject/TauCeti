/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.ResidueCocycle
public import TauCeti.Algebra.Lie.Extension
public import Mathlib.Algebra.Lie.Solvable

/-!
# Perfectness of residue central extensions

Over a field, the residue central extension of the formal current algebra of a perfect Lie
algebra is perfect exactly when the invariant symmetric form is nonzero. This is the
perfectness condition needed for the universal central extension of a loop algebra.

We use Mathlib's `LieAlgebra.ofTwoCocycle` directly. The form `Φ` has Mathlib's residue
convention `Res(f dg) Φ(x, y)`; the affine convention with level form `κ` uses `Φ = -κ`.
No degree derivation is adjoined. Perfectness is expressed by `derivedSeries R L 1 = ⊤`.

The derived-algebra membership lemmas can also be used over commutative rings to study the
current summand and central form values separately, including the split extension at zero level.

## References

* V. Kac, *Infinite-Dimensional Lie Algebras*, Chapter 7 (central extensions of loop algebras).
-/

public section

noncomputable section

open scoped TensorProduct LaurentSeries
open LieAlgebra

attribute [local instance 1100] HahnSeries.instAlgebra

namespace TauCeti.CurrentAlgebra

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)

local notation "C" => currentAlgebra R L
local notation "Z" => TrivialLieModule R C R
local notation "c" => twoCocycleOfBilinear R L Φ hΦ hΦs
local notation "E" => ofTwoCocycle c

/-- Values of the form occur as central elements in the derived algebra. -/
theorem ofProd_form_mem_derivedSeries (x y : L) :
    ofProd c (0, (TrivialLieModule.equiv R C R).symm (Φ x y)) ∈ derivedSeries R E 1 := by
  have h (u v : C) : ⁅ofProd c (u, 0), ofProd c (v, 0)⁆ ∈ derivedSeries R E 1 :=
    LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _)
  have hd := (derivedSeries R E 1).sub_mem
    (h (HahnSeries.single (-1) 1 ⊗ₜ x) (HahnSeries.single 1 1 ⊗ₜ y))
    (h (HahnSeries.single 0 1 ⊗ₜ x) (HahnSeries.single 0 1 ⊗ₜ y))
  have he : ofProd c (0, (TrivialLieModule.equiv R C R).symm (Φ x y)) =
      ⁅ofProd c (HahnSeries.single (-1) 1 ⊗ₜ x, 0),
        ofProd c (HahnSeries.single 1 1 ⊗ₜ y, 0)⁆ -
      ⁅ofProd c (HahnSeries.single 0 1 ⊗ₜ x, 0),
        ofProd c (HahnSeries.single 0 1 ⊗ₜ y, 0)⁆ := by
    apply (ofProdLinearEquiv c).symm.injective
    simp only [map_sub, coe_ofProdLinearEquiv_symm]
    simp [bracket_ofTwoCocycle, residuePairing_tmul]
  rwa [← he] at hd

/-- When `L` is perfect, the entire current summand lies in the derived algebra of its
residue central extension, including at zero level. -/
theorem ofProd_current_mem_derivedSeries (hperfect : derivedSeries R L 1 = ⊤) (u : C) :
    ofProd c (u, 0) ∈ derivedSeries R E 1 := by
  let s : C →ₗ[R] E := (ofProdLinearEquiv c).toLinearMap ∘ₗ LinearMap.inl R C Z
  have hs (u : C) : s u = ofProd c (u, 0) := by simp [s]
  rw [← hs]
  suffices ∀ u : C, s u ∈ derivedSeries R E 1 from this u
  intro u
  induction u using TensorProduct.inductionOn with
  | tmul f x =>
    have hx : x ∈ Submodule.span R {⁅a, b⁆ | (a : L) (b : L)} := by
      rw [← coe_derivedSeries_one_eq, hperfect]
      simp
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, b, rfl⟩ := hz
      have hb : ⁅s (f ⊗ₜ a), s (HahnSeries.single 0 1 ⊗ₜ b)⁆ ∈ derivedSeries R E 1 :=
        LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _)
      have hr : LaurentSeries.residuePairing R f 1 = 0 := by
        simpa using LaurentSeries.residuePairing_single_zero_right R f 1
      simpa [hs, bracket_ofTwoCocycle, residuePairing_tmul, hr] using hb
    | zero => simp
    | add x y _ _ hx hy =>
      rw [TensorProduct.tmul_add, map_add]
      exact (derivedSeries R E 1).add_mem hx hy
    | smul r x _ hx =>
      rw [TensorProduct.tmul_smul, map_smul]
      exact (derivedSeries R E 1).smul_mem r hx
  | add u v hu hv =>
    rw [map_add]
    exact (derivedSeries R E 1).add_mem hu hv

/-- At zero level every element of the derived algebra has zero central coordinate. -/
theorem central_eq_zero_of_mem_derivedSeries (hzero : Φ = 0) {v : E}
    (hv : v ∈ derivedSeries R E 1) : ((ofProd c).symm v).2 = 0 := by
  have hv' : v ∈ Submodule.span R {⁅a, b⁆ | (a : E) (b : E)} := by
    rwa [← coe_derivedSeries_one_eq]
  let q : E →ₗ[R] Z := LinearMap.snd R C Z ∘ₗ (ofProdLinearEquiv c).symm.toLinearMap
  have hq (v : E) : q v = ((ofProd c).symm v).2 := by simp [q]
  rw [← hq]
  clear hv
  induction hv' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, b, rfl⟩ := hz
    simp [hq, bracket_ofTwoCocycle, hzero, trivial_lie_zero]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul r x _ hx => simp [hx]

section Field

variable {K : Type*} [Field K] [LieAlgebra K L]
  (Ψ : LinearMap.BilinForm K L) (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm)

local notation "CK" => currentAlgebra K L
local notation "cK" => twoCocycleOfBilinear K L Ψ hΨ hΨs
local notation "EK" => ofTwoCocycle cK

/-- The residue central extension of a perfect Lie algebra over a field is perfect if and
only if its form is nonzero. No finite-dimensionality or characteristic assumption is needed. -/
theorem derivedSeries_ofTwoCocycle_eq_top_iff (hperfect : derivedSeries K L 1 = ⊤) :
    derivedSeries K EK 1 = ⊤ ↔ Ψ ≠ 0 := by
  constructor
  · intro h hzero
    have hv : ofProd cK (0, (TrivialLieModule.equiv K CK K).symm 1) ∈
        derivedSeries K EK 1 := by
      rw [h]
      exact LieSubmodule.mem_top _
    have hz := central_eq_zero_of_mem_derivedSeries K L Ψ hΨ hΨs hzero hv
    exact (one_ne_zero : (1 : K) ≠ 0) (by
      simpa using congrArg (TrivialLieModule.equiv K CK K) hz)
  · intro hne
    obtain ⟨x, y, hxy⟩ : ∃ x y, Ψ x y ≠ 0 := by
      by_contra! h
      exact hne (LinearMap.ext₂ h)
    have hcentral (z : TrivialLieModule K CK K) :
        ofProd cK (0, z) ∈ derivedSeries K EK 1 := by
      have hz := (derivedSeries K EK 1).smul_mem
        ((TrivialLieModule.equiv K _ K) z / Ψ x y)
        (ofProd_form_mem_derivedSeries K L Ψ hΨ hΨs x y)
      have he : ofProd cK (0, z) =
          ((TrivialLieModule.equiv K _ K) z / Ψ x y) •
            ofProd cK
              (0, (TrivialLieModule.equiv K _ K).symm (Ψ x y)) := by
        apply (ofProdLinearEquiv cK).symm.injective
        simp only [coe_ofProdLinearEquiv_symm, of_symm_smul, Equiv.symm_apply_apply,
          Prod.smul_mk, smul_zero, Prod.mk.injEq, true_and]
        apply (TrivialLieModule.equiv K CK K).injective
        simp [div_mul_cancel₀ _ hxy]
      rwa [← he] at hz
    rw [eq_top_iff]
    intro v _
    obtain ⟨⟨u, z⟩, rfl⟩ := (ofProd cK).surjective v
    have hu := ofProd_current_mem_derivedSeries K L Ψ hΨ hΨs hperfect u
    have hsum :=
      (derivedSeries K EK 1).add_mem hu (hcentral z)
    rw [← of_add, Prod.mk_add_mk, add_zero, zero_add] at hsum
    exact hsum

end Field

end TauCeti.CurrentAlgebra
