/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.Data.ZMod.Defs
import TauCeti.Algebra.Module.PseudoCoherent.FiniteProjectiveDimension

/-!
# Tests for pseudocoherent modules

The quotient of a ring by a non-zero-divisor is pseudocoherent, with the resolution
`0 → R → R → R ⧸ fR → 0` given by multiplication by `f`. Finitely generated projective modules are
pseudocoherent, and over a noetherian ring pseudocoherence is finite generation. Dividing a
pseudocoherent module by a non-zero-divisor on it keeps it pseudocoherent.

For finite projective dimension: finitely generated projective modules are `0`-fpd, the quotient by
a non-zero-divisor is `1`-fpd, and over `ℤ ⧸ 4` the module `ℤ ⧸ 2` is pseudocoherent but `m`-fpd for
no `m`, because each of its syzygies is again `ℤ ⧸ 2`, which is not projective.
-/

namespace TauCeti.Huber

open LinearMap

/-- *test_quotient_nonZeroDivisor*: for a non-zero-divisor `f`, the kernel `fR` of `R → R ⧸ fR` is
isomorphic to `R`, so `R ⧸ fR` is pseudocoherent. -/
example {R : Type*} [CommRing R] {f : R} (hf : f ∈ nonZeroDivisors R) :
    IsPseudoCoherentOver R (R ⧸ Ideal.span {f}) ⊤ := by
  have hinj : Function.Injective (toSpanSingleton R R f) := fun a b hab ↦
    (mul_cancel_right_mem_nonZeroDivisors hf).mp (by simpa using hab)
  have hrange : range (toSpanSingleton R R f) = ker (Ideal.span {f}).mkQ := by
    rw [Submodule.ker_mkQ]
    exact (span_singleton_eq_range R R f).symm
  rw [← top_add (1 : ℕ∞)]
  exact (IsPseudoCoherentOver.succ_iff_ker (Submodule.mkQ_surjective _)).mpr
    ((IsPseudoCoherentOver.of_projective (M := R)).of_equiv
      ((LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hrange)))

/-- *test_finiteProjective*: a finitely generated projective module is pseudocoherent. -/
example {R P : Type*} [Ring R] [AddCommGroup P] [Module R P] [Module.Finite R P]
    [Module.Projective R P] : IsPseudoCoherentOver R P ⊤ :=
  .of_projective

/-- *test_noetherian*: over a noetherian ring, a module is pseudocoherent exactly when it is
finitely generated. -/
example {R M : Type*} [Ring R] [IsNoetherianRing R] [AddCommGroup M] [Module R M] :
    IsPseudoCoherentOver R M ⊤ ↔ Module.Finite R M :=
  ⟨IsPseudoCoherentOver.finite, fun _ ↦ .of_isNoetherianRing⟩

/-- *test_ker_mul_nonZeroDivisor*: if `M` is pseudocoherent and `f` is a non-zero-divisor on `M`,
then the cokernel `M ⧸ fM` of multiplication by `f` is pseudocoherent. -/
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {f : R} (hf : IsSMulRegular M f)
    (hM : IsPseudoCoherentOver R M ⊤) : IsPseudoCoherentOver R (M ⧸ range (lsmul R M f)) ⊤ :=
  IsPseudoCoherentOver.cokernel (ker_eq_bot.mp ((isSMulRegular_iff_ker_lsmul_eq_bot M f).mp hf))
    (exact_map_mkQ_range _) (Submodule.mkQ_surjective _)
    (fun _ ↦ ENat.top_sub_one ▸ hM) hM

end TauCeti.Huber

namespace TauCeti.Module

open LinearMap

universe u

/-- *test_finiteProjective*: a finitely generated projective module is `0`-fpd, and so is the zero
module. -/
example {R P : Type*} [Ring R] [AddCommGroup P] [Module R P] [Module.Finite R P]
    [Module.Projective R P] : IsFPD R P 0 ∧ IsFPD R PUnit.{1} 0 :=
  ⟨.of_projective, .of_projective⟩

/-- *test_quotient_nonZeroDivisor*: for a non-zero-divisor `f`, the resolution
`0 → R → R → R ⧸ fR → 0` makes `R ⧸ fR` a `1`-fpd module. -/
example {R : Type*} [CommRing R] {f : R} (hf : f ∈ nonZeroDivisors R) :
    IsFPD R (R ⧸ Ideal.span {f}) 1 := by
  have hinj : Function.Injective (toSpanSingleton R R f) := fun a b hab ↦
    (mul_cancel_right_mem_nonZeroDivisors hf).mp (by simpa using hab)
  have hrange : range (toSpanSingleton R R f) = ker (Ideal.span {f}).mkQ := by
    rw [Submodule.ker_mkQ]
    exact (span_singleton_eq_range R R f).symm
  exact (IsFPD.succ_iff_ker (Submodule.mkQ_surjective _)).mpr
    ((IsFPD.of_projective (M := R)).of_equiv
      ((LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hrange)))

/-- *test_projectiveDimension*: a module is `m`-fpd exactly when it is pseudocoherent and
`Ext^i(M, -)` vanishes for `i > m`. -/
example {R M : Type u} [Ring R] [AddCommGroup M] [Module R M] (m : ℕ) :
    IsFPD R M m ↔ Huber.IsPseudoCoherentOver R M ⊤ ∧
      CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R M) m :=
  isFPD_iff_hasProjectiveDimensionLE

/-- *test_not_fpd* (*isPseudoCoherentOver_zmod_four*): over `R = ℤ ⧸ 4` the module `R ⧸ 2R` is
pseudocoherent but `m`-fpd for no `m`. The kernel `2R` of `R → R ⧸ 2R` is again isomorphic to
`R ⧸ 2R`, which is not projective, since `R → R ⧸ 2R` has no section. -/
example : Huber.IsPseudoCoherentOver (ZMod 4) (ZMod 4 ⧸ Ideal.span {(2 : ZMod 4)}) ⊤ ∧
    ∀ m, ¬ IsFPD (ZMod 4) (ZMod 4 ⧸ Ideal.span {(2 : ZMod 4)}) m := by
  set I := Ideal.span {(2 : ZMod 4)}
  let φ := toSpanSingleton (ZMod 4) (ZMod 4) 2
  have hmem (x : ZMod 4) : x ∈ I ↔ 2 * x = 0 :=
    Ideal.mem_span_singleton.trans
      ((by decide : ∀ y : ZMod 4, (∃ c : ZMod 4, y = 2 * c) ↔ 2 * y = 0) x)
  -- `R ⧸ 2R` is not projective: a section `s` of `R → R ⧸ 2R` would send `1` into `2R`.
  have hproj : ¬ Module.Projective (ZMod 4) (ZMod 4 ⧸ I) := by
    intro _
    obtain ⟨s, hs⟩ := Module.projective_lifting_property I.mkQ LinearMap.id I.mkQ_surjective
    let one : ZMod 4 ⧸ I := Submodule.Quotient.mk 1
    have hs1 : I.mkQ (s one) = one := LinearMap.congr_fun hs one
    have h2 : (2 : ZMod 4) • one = 0 := by
      rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one, Submodule.Quotient.mk_eq_zero]
      exact Ideal.mem_span_singleton_self 2
    have hI : s one ∈ I := (hmem _).mpr (by rw [← smul_eq_mul, ← map_smul, h2, map_zero])
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero I).mpr hI, eq_comm,
      Submodule.Quotient.mk_eq_zero, hmem] at hs1
    exact absurd hs1 (by decide)
  -- `2R`, the kernel of `R → R ⧸ 2R`, is isomorphic to `R ⧸ 2R` through multiplication by `2`.
  have hker : I = ker φ := by
    ext x
    rw [hmem, mem_ker, toSpanSingleton_apply, smul_eq_mul, mul_comm]
  let e : (ZMod 4 ⧸ I) ≃ₗ[ZMod 4] ker I.mkQ :=
    (Submodule.quotEquivOfEq I (ker φ) hker).trans (φ.quotKerEquivRange.trans
      (LinearEquiv.ofEq (range φ) (ker I.mkQ)
        (by rw [Submodule.ker_mkQ, ← span_singleton_eq_range])))
  refine ⟨.of_isNoetherianRing, fun m ↦ ?_⟩
  induction m with
  | zero => exact fun h ↦ hproj (IsFPD.zero_iff.mp h).2
  | succ m ih => exact fun h ↦ ih (((IsFPD.succ_iff_ker I.mkQ_surjective).mp h).of_equiv e.symm)

end TauCeti.Module
