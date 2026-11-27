/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.LinearAlgebra.QuadraticForm.FreeBaseChange
import TauCeti.LinearAlgebra.TensorProduct.Range

/-!
# The geometric radical of a quadratic form

The singular vectors of a quadric are the zeros of the quadratic form in the kernel of
its polar pairing. Over an imperfect field their span can grow after scalar extension.
For example, in characteristic two, `x² + t y²` has trivial radical when `t` is a
nonsquare, but acquires a radical line when a square root of `t` is adjoined.

Quadratic nondegeneracy includes a bound of one on the rank of the polar kernel.
Under that bound the radical commutes with extension to any reduced algebra over the field. Thus
nondegeneracy can be tested after any field extension, and over a perfect extension
it is enough to test that the quadratic radical vanishes.

## References

* SGA 7 II, Exposé XII, §1.1, for the geometric criterion for ordinary quadratic forms.
-/

public section

open TensorProduct

namespace QuadraticForm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Over a perfect field the quadratic radical detects nondegeneracy, even in
characteristic two and in odd dimension. -/
theorem nondegenerate_iff_radical_eq_bot_of_perfectField [PerfectField K]
    (Q : QuadraticForm K V) : Q.Nondegenerate ↔ Q.radical = ⊥ := by
  by_cases h₂ : (2 : K) ≠ 0
  · let := invertibleOfNonzero h₂
    exact QuadraticMap.nondegenerate_iff_radical_eq_bot
  let : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (not_ne_iff.mp h₂)
  refine ⟨fun h ↦ h.radical_eq_bot, fun h ↦ ⟨h, ?_⟩⟩
  have hzero {v : V} (hv : v ∈ Q.polarBilin.ker) (hq : Q v = 0) : v = 0 :=
    (Submodule.eq_bot_iff _).mp h v ⟨hq, hv⟩
  by_cases hker : Q.polarBilin.ker = ⊥
  · rw [hker, rank_bot]
    exact zero_le_one
  obtain ⟨v, hv, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hqv : Q v ≠ 0 := fun h ↦ hv₀ (hzero hv h)
  refine (rank_submodule_le_one_iff _).mpr ⟨v, hv, fun w hw ↦ ?_⟩
  obtain ⟨c, hc⟩ := surjective_frobenius K 2 (-Q w / Q v)
  have hc' : c * c * Q v = -Q w :=
    (eq_div_iff hqv).mp (by simpa [frobenius_def, pow_two] using hc)
  have hp : QuadraticMap.polar Q w (c • v) = 0 :=
    DFunLike.congr_fun (LinearMap.mem_ker.mp hw) _
  have hwc := hzero (Q.polarBilin.ker.add_mem hw (Q.polarBilin.ker.smul_mem c hv))
  have heq : w + c • v = 0 := hwc (by
    simp [QuadraticMap.map_add, QuadraticMap.map_smul, hp, hc'])
  exact Submodule.mem_span_singleton.mpr ⟨-c, by simpa using (eq_neg_of_add_eq_zero_left heq).symm⟩

section Algebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
variable (A : Type*) [CommRing A] [Algebra R A] [FaithfulSMul R A]

/-- Along an injective scalar extension, a ground-ring vector belongs to the radical
exactly when its image does. -/
@[simp]
theorem one_tmul_mem_radical_freeBaseChange_iff (Q : QuadraticForm R M) (v : M) :
    (1 : A) ⊗ₜ[R] v ∈ (Q.freeBaseChange A).radical ↔ v ∈ Q.radical := by
  have hinj := FaithfulSMul.algebraMap_injective R A
  have hval : Q.freeBaseChange A (1 ⊗ₜ v) = 0 ↔ Q v = 0 := by
    rw [freeBaseChange_one_tmul, map_eq_zero_iff _ hinj]
  refine and_congr hval ⟨fun h ↦ LinearMap.ext fun w ↦ ?_, fun h ↦ LinearMap.ext fun x ↦ ?_⟩
  · have he := DFunLike.congr_fun h (1 ⊗ₜ[R] w)
    simpa [Algebra.smul_def, map_eq_zero_iff _ hinj] using he
  · induction x with
    | tmul a w =>
      have hw := DFunLike.congr_fun h w
      simpa using congrArg (fun t : R ↦ t • a) hw
    | add x y hx hy => simp_all

end Algebra

variable (A : Type*) [CommRing A] [Algebra K A] [IsReduced A]

/-- If the polar kernel has rank at most one, the quadratic radical commutes with
extension to a reduced algebra over the ground field. -/
theorem radical_freeBaseChange_of_rank_ker_le_one (Q : QuadraticForm K V)
    (h : Module.rank K Q.polarBilin.ker ≤ 1) :
    (Q.freeBaseChange A).radical = Q.radical.baseChange A := by
  nontriviality A
  refine le_antisymm (fun x hx ↦ ?_) (Submodule.baseChange_le_iff_le_comap.mpr fun v hv ↦
    (Q.one_tmul_mem_radical_freeBaseChange_iff A v).mpr hv)
  obtain ⟨v, hv, hspan⟩ := (rank_submodule_le_one_iff _).mp h
  have hker := (Q.freeBaseChange A).radical_le_ker_polarBilin hx
  rw [polarBilin_freeBaseChange, LinearMap.BilinForm.ker_baseChange] at hker
  have hmem := Submodule.baseChange_mono (A := A) hspan hker
  rw [Submodule.baseChange_span, Set.image_singleton, TensorProduct.mk_apply] at hmem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hmem
  by_cases hc : c = 0
  · simp [hc]
  have hq : Q v = 0 := by
    by_contra hq
    have hu := (isUnit_iff_ne_zero.mpr hq).map (algebraMap K A)
    have hz := hx.1
    rw [QuadraticMap.map_smul, freeBaseChange_one_tmul, smul_eq_mul, hu.mul_left_eq_zero] at hz
    exact hc (eq_zero_of_pow_eq_zero (n := 2) (by simpa [pow_two] using hz))
  have hv' : v ∈ Q.radical := ⟨hq, hv⟩
  exact (Q.radical.baseChange A).smul_mem c (Submodule.tmul_mem_baseChange_of_mem _ hv')

/-- Quadratic nondegeneracy is preserved and reflected by extension to any nonzero
reduced algebra over the field. -/
@[simp]
theorem nondegenerate_freeBaseChange_iff [Nontrivial A] (Q : QuadraticForm K V) :
    (Q.freeBaseChange A).Nondegenerate ↔ Q.Nondegenerate := by
  have hrank : Module.rank A (Q.freeBaseChange A).polarBilin.ker ≤ 1 ↔
      Module.rank K Q.polarBilin.ker ≤ 1 := by
    rw [polarBilin_freeBaseChange, LinearMap.BilinForm.ker_baseChange,
      Submodule.rank_baseChange_of_isComplemented _ (exists_isCompl _),
      Cardinal.lift_le_one_iff]
  constructor
  · intro h
    refine ⟨(Submodule.eq_bot_iff _).mpr fun v hv ↦ ?_, hrank.mp h.rank_rad_polar_le⟩
    have hz := (Submodule.eq_bot_iff _).mp h.radical_eq_bot _ <|
      (Q.one_tmul_mem_radical_freeBaseChange_iff A v).mpr hv
    simpa using hz
  · intro h
    refine ⟨?_, hrank.mpr h.rank_rad_polar_le⟩
    rw [radical_freeBaseChange_of_rank_ker_le_one _ _ h.rank_rad_polar_le,
      h.radical_eq_bot, Submodule.baseChange_bot]

variable (L : Type*) [Field L] [Algebra K L]

/-- A quadratic form is nondegenerate exactly when its radical vanishes over a
perfect extension, in particular over an algebraic closure. -/
theorem nondegenerate_iff_radical_freeBaseChange_eq_bot [PerfectField L] (Q : QuadraticForm K V) :
    Q.Nondegenerate ↔ (Q.freeBaseChange L).radical = ⊥ :=
  (Q.nondegenerate_freeBaseChange_iff L).symm.trans
    (nondegenerate_iff_radical_eq_bot_of_perfectField _)

end QuadraticForm
