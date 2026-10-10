/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Decomposition
public import TauCeti.RepresentationTheory.Irreducible

/-!
# Integral central characters of rational irreducible representations

Scalar matrices act on a rational irreducible representation of `GL n ℂ` by a unique
integer power of the scalar. Every occurring torus weight has the same coordinate sum,
and this sum is the exponent of that central character. Thus the torus weights retain
the central information that is lost on restricting to `SL n`.

The scalar-action formula for an occurring weight holds over any field, without a
finite-dimensionality or rationality assumption. An infinite field is needed to recover
the exponent uniquely from its values on units. Rationality supplies an occurring integer
weight in the complex case. Rank zero is included: its central exponent is zero.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open Matrix

namespace Representation.IsIrreducible

open TauCeti

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] {n : ℕ}
  {ρ : Representation K (GL (Fin n) K) W}

/-- A scalar matrix acts on an irreducible representation by the scalar raised to the
coordinate sum of any occurring torus weight. -/
theorem apply_scalar_eq_zpow_smul_of_weightSpace_ne_bot (hρ : ρ.IsIrreducible)
    {l : Fin n → ℤ} (hl : weightSpace ρ l ≠ ⊥) (z : Kˣ) (v : W) :
    ρ (GeneralLinearGroup.scalar (Fin n) z) v = ((z ^ (∑ i, l i) : Kˣ) : K) • v := by
  have := hρ
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp hl
  let a : K := ((z ^ (∑ i, l i) : Kˣ) : K)
  let f : Module.End K W := ρ (GeneralLinearGroup.scalar (Fin n) z) - a • LinearMap.id
  have hf : ∀ g x, f (ρ g x) = ρ g (f x) := by
    intro g x
    have hc := congrArg (fun g' ↦ ρ g' x) (GeneralLinearGroup.scalar_commute z g)
    simpa [f, map_mul, Module.End.mul_apply] using hc
  let F := f.intertwiningMap_of_isIntertwiningMap ρ ρ hf
  have hwf : F w = 0 := by
    have he := apply_of_mem_weightSpace hw (fun _ ↦ z)
    rw [weightChar_apply, torusCharacter_def, Finset.prod_zpow_eq_zpow_sum,
      diagGL_const] at he
    simpa [F, f, a] using sub_eq_zero.mpr he
  have hF : F = 0 := (injective_or_eq_zero F).resolve_left fun hinj ↦
    hw0 (hinj (hwf.trans (map_zero F).symm))
  have hv := DFunLike.congr_fun hF v
  simpa [F, f, a, sub_eq_zero] using hv

end Representation.IsIrreducible

namespace TauCeti

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] {n : ℕ}
  {ρ : Representation K (GL (Fin n) K) W}

/-- An occurring weight determines the exponent of a scalar action over an infinite field.
Irreducibility is not needed when the scalar action is already known. -/
theorem sum_eq_of_forall_apply_scalar_eq_zpow_smul [Infinite K]
    {l : Fin n → ℤ} (hl : weightSpace ρ l ≠ ⊥) {d : ℤ}
    (hd : ∀ (z : Kˣ) (v : W),
      ρ (GeneralLinearGroup.scalar (Fin n) z) v = ((z ^ d : Kˣ) : K) • v) :
    ∑ i, l i = d := by
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp hl
  have he : ∀ z : Kˣ, z ^ (∑ i, l i) = z ^ d := by
    intro z
    apply Units.ext
    apply smul_left_injective K hw0
    have h := apply_of_mem_weightSpace hw (fun _ ↦ z)
    rw [weightChar_apply, torusCharacter_def, Finset.prod_zpow_eq_zpow_sum,
      diagGL_const] at h
    exact h.symm.trans (hd z w)
  have hchar : weightChar K (fun _ : Fin 1 ↦ ∑ i, l i) =
      weightChar K (fun _ : Fin 1 ↦ d) := by
    apply MonoidHom.ext
    intro t
    simpa [weightChar_apply, torusCharacter_def] using he (t 0)
  exact congrFun (weightChar_injective hchar) 0

/-- Over an infinite field, every occurring weight of an irreducible representation has
the same coordinate sum. This sum records its central character. -/
theorem sum_eq_sum_of_weightSpace_ne_bot [Infinite K] [ρ.IsIrreducible]
    {l m : Fin n → ℤ} (hl : weightSpace ρ l ≠ ⊥) (hm : weightSpace ρ m ≠ ⊥) :
    ∑ i, l i = ∑ i, m i :=
  sum_eq_of_forall_apply_scalar_eq_zpow_smul hl
    ((inferInstance : ρ.IsIrreducible).apply_scalar_eq_zpow_smul_of_weightSpace_ne_bot hm)

/-- Scalar matrices act on a rational irreducible representation of `GL n ℂ` by a unique
integer power. Its exponent is the coordinate sum of every occurring torus weight. -/
theorem IsRationalRep.existsUnique_forall_apply_scalar_eq_zpow_smul
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) ℂ) W} [ρ.IsIrreducible] (h : IsRationalRep ρ) :
    ∃! d : ℤ, ∀ (z : ℂˣ) (v : W),
      ρ (GeneralLinearGroup.scalar (Fin n) z) v = ((z ^ d : ℂˣ) : ℂ) • v := by
  have := (inferInstance : ρ.IsIrreducible).nontrivial
  have hweight : ∃ l : Fin n → ℤ, weightSpace ρ l ≠ ⊥ := by
    by_contra! hbot
    have htop := h.iSup_weightSpace_eq_top
    simp only [hbot, iSup_bot] at htop
    exact bot_ne_top htop
  obtain ⟨l, hl⟩ := hweight
  refine ⟨∑ i, l i,
    (inferInstance : ρ.IsIrreducible).apply_scalar_eq_zpow_smul_of_weightSpace_ne_bot hl,
    fun d hd ↦ ?_⟩
  exact (sum_eq_of_forall_apply_scalar_eq_zpow_smul hl hd).symm

end TauCeti
