/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Regular.LinearMap
public import TauCeti.Algebra.Module.Injective.Bidual
import Mathlib.Algebra.GroupWithZero.Action.Regular
import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Ideals together with their annihilators

In a reduced Noetherian ring, an ideal `J` and its annihilator together contain a nonzerodivisor.
An element killing `J.annihilator ⊔ J` lies in `J.annihilator` and kills itself, so it is
nilpotent, hence zero; Mathlib's `IsSMulRegular.subsingleton_linearMap_iff` turns this into a
regular element of `J.annihilator ⊔ J`.

This is the input that splits an idempotent off the total ring of fractions of a reduced
Noetherian ring with two minimal primes, as in `IsLocalRing.isDomain_of_isIntegrallyClosed`.

A nilpotent ideal of a nontrivial ring, at the other extreme, kills a nonzero element: its last
nonzero power does.

Over a self-injective commutative ring, every finitely generated ideal equals its double
annihilator. This follows by applying reflexivity of finitely presented modules to the quotient
by the ideal. It makes annihilation reverse and reflect inclusion in a noetherian self-injective
ring, allowing the ascending and descending chain conditions to be compared.

## Main results

* `Ideal.exists_mem_annihilator_sup_isSMulRegular`: in a reduced Noetherian ring, every ideal
  together with its annihilator contains a nonzerodivisor.
* `Ideal.exists_ne_zero_forall_mul_eq_zero_of_isNilpotent`: a nilpotent ideal of a nontrivial
  ring kills a nonzero element.
* `Ideal.annihilator_annihilator_of_fg`: a finitely generated ideal of a self-injective
  commutative ring equals its double annihilator.
-/

public section

/-- In a reduced Noetherian ring, every ideal `J` together with its annihilator contains a
nonzerodivisor: some element of `J.annihilator ⊔ J` is regular on `R`. -/
theorem Ideal.exists_mem_annihilator_sup_isSMulRegular {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsReduced R] (J : Ideal R) :
    ∃ b ∈ J.annihilator ⊔ J, IsSMulRegular R b := by
  -- an element killing `J.annihilator ⊔ J` lies in and kills `J.annihilator`, so its square is zero
  have hann (m : R) (hm : ∀ k ∈ J.annihilator ⊔ J, k * m = 0) : m = 0 := by
    have hmI : m ∈ J.annihilator := Submodule.mem_annihilator.2 fun j hj ↦ by
      rw [smul_eq_mul, mul_comm]
      exact hm j (Ideal.mem_sup_right hj)
    exact IsReduced.eq_zero m ⟨2, by rw [pow_two]; exact hm m (Ideal.mem_sup_left hmI)⟩
  -- so every linear map `R ⧸ (J.annihilator ⊔ J) → R` vanishes
  rw [← Ideal.annihilator_quotient (I := J.annihilator ⊔ J)]
  refine IsSMulRegular.subsingleton_linearMap_iff.1 (subsingleton_of_forall_eq 0 fun f ↦ ?_)
  have hmk (r : R) : Ideal.Quotient.mk (J.annihilator ⊔ J) r = r • Ideal.Quotient.mk _ 1 := by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one]
  have h0 : f (Ideal.Quotient.mk _ 1) = 0 := hann _ fun k hk ↦ by
    rw [← smul_eq_mul, ← map_smul, ← hmk, Ideal.Quotient.eq_zero_iff_mem.2 hk, map_zero]
  refine LinearMap.ext fun q ↦ ?_
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [hmk, map_smul, h0, smul_zero, LinearMap.zero_apply]

/-- A nilpotent ideal `I` of a nontrivial commutative ring kills a nonzero element: every nonzero
element of the last nonzero power of `I` will do. -/
theorem Ideal.exists_ne_zero_forall_mul_eq_zero_of_isNilpotent {R : Type*} [CommSemiring R]
    [Nontrivial R] {I : Ideal R} (hI : IsNilpotent I) : ∃ s ≠ 0, ∀ x ∈ I, x * s = 0 := by
  obtain ⟨s, hsmem, hs⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (pow_pred_nilpotencyClass hI)
  refine ⟨s, hs, fun x hx ↦ ?_⟩
  have hmem := Ideal.mul_mem_mul hx hsmem
  rwa [← pow_succ', Nat.sub_add_cancel (pos_nilpotencyClass_iff.mpr hI), pow_nilpotencyClass hI,
    Ideal.zero_eq_bot, Ideal.mem_bot] at hmem

/-- A finitely generated ideal in a self-injective commutative ring is its double
annihilator. -/
@[simp]
theorem Ideal.annihilator_annihilator_of_fg {R : Type*} [CommRing R] [Module.Injective R R]
    (I : Ideal R) (hI : I.FG) : I.annihilator.annihilator = I := by
  have : Module.FinitePresentation R (R ⧸ I) :=
    Module.finitePresentation_of_surjective I.mkQ I.mkQ_surjective
      (by simpa [Ideal.FG, Submodule.FG] using hI)
  apply le_antisymm
  · intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (Module.bijective_dual_eval R (R ⧸ I)).injective
    ext f
    have hfx (r : R) : f (Ideal.Quotient.mk I r) = r * f (Ideal.Quotient.mk I 1) := by
      simpa using (f.comp I.mkQ).map_smul r 1
    have hf : f (Ideal.Quotient.mk I 1) ∈ I.annihilator :=
      Submodule.mem_annihilator.mpr fun r hr ↦ by
        simp only [smul_eq_mul, mul_comm, ← hfx]
        simp [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
    have hx' := Submodule.mem_annihilator.mp hx _ hf
    simpa only [smul_eq_mul, ← hfx, map_zero, Module.Dual.eval_apply,
      LinearMap.zero_apply] using hx'
  · intro x hx
    exact Submodule.mem_annihilator.mpr fun r hr ↦ by
      simpa [mul_comm] using Submodule.mem_annihilator.mp hr x hx
