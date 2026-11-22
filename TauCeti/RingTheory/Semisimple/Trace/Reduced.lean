/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CentralSimple.BaseChange
public import TauCeti.LinearAlgebra.Trace.RestrictScalars
public import TauCeti.RingTheory.Semisimple.CenterDimension

import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix
import TauCeti.Algebra.Subalgebra.Center
import TauCeti.LinearAlgebra.Matrix.Trace.LinearMap
import TauCeti.LinearAlgebra.Trace.Basic
import TauCeti.RingTheory.SimpleModule.Isotypic

/-!
# The reduced trace of a semisimple algebra

Let `B` be a finite-dimensional semisimple algebra over a field `F`. Its **reduced trace**
`Trd_{B/F} : B → F` is the sum over the simple factors `B_i` of `B`, with centres `Z_i`, of the
field trace `Tr_{Z_i/F}` composed with the reduced trace of the central simple `Z_i`-algebra `B_i`.
On a central simple algebra `A` of degree `d` over `F`, which becomes the matrix algebra `M_d(L)`
over a splitting field `L`, the reduced trace of `a` is the matrix trace of the image of `1 ⊗ a`.

This file defines `TauCeti.Algebra.reducedTrace F B` without choosing a Wedderburn presentation.
The simple factors of `B` are its isotypic components `c` as a left module over itself, which are
two-sided ideals, and left multiplication by `b` preserves each of them. The trace of left
multiplication by `b` on `c`, `TauCeti.Algebra.idealTrace F c b`, is `d_c` times the reduced trace
of the `c`-component of `b`, where `d_c` is the degree of `c` over its centre: `d_c ^ 2` is the
dimension of `c` over its centre `Z(B) ∩ c`. That number is `TauCeti.Algebra.idealDeg F c`, and

`Trd_{B/F}(b) = ∑_c d_c⁻¹ · tr_F(x ↦ b x on c)`.

In characteristic `0`, the case of the definition, each `d_c` is invertible in `F`.

## Main definitions

* `TauCeti.Algebra.idealTrace F c`: the trace over `F` of left multiplication on a left ideal `c`.
* `TauCeti.Algebra.idealDeg F c`: the natural square root of `dim_F c / dim_F (c ∩ Z(B))`. For an
  isotypic component `c` of a finite-dimensional semisimple algebra it is the degree of `c` over
  its centre `Z(B) ∩ c`.
* `TauCeti.Algebra.reducedTrace F B`: the reduced trace `Trd_{B/F}`.

## Main results

* `TauCeti.Algebra.reducedTrace_mul_comm`: `Trd(a b) = Trd(b a)`.
* `TauCeti.Algebra.reducedTrace_eq_trace_reducedTrace`: on a simple algebra `B` central over a
  field `Z` finite over `F`, `Trd_{B/F} = Tr_{Z/F} ∘ Trd_{B/Z}`.
* `TauCeti.Algebra.reducedTrace_eq_inv_deg_mul_trace`: on a central simple algebra `A`,
  `Trd_{A/F}(a) = (deg A)⁻¹ · tr_F(L_a)`, and when `deg A` is nonzero in `F`,
  `TauCeti.Algebra.trace_lmul_eq_deg_mul_reducedTrace_of_ne_zero`:
  `tr_F(L_a) = deg A · Trd_{A/F}(a)` (`TauCeti.Algebra.trace_lmul_eq_deg_mul_reducedTrace` in
  characteristic `0`).
* `TauCeti.Algebra.trace_lmul_eq_idealDeg_mul_reducedTrace_of_ne_zero`: on a semisimple algebra,
  for `b` in a simple factor `c` with `d_c` nonzero in `F`, `tr_F(L_b) = d_c · Trd_{B/F}(b)`
  (`TauCeti.Algebra.trace_lmul_eq_idealDeg_mul_reducedTrace` in characteristic `0`, where
  `d_c > 0` by `TauCeti.Algebra.idealDeg_pos`).
* `Matrix.reducedTrace_eq_trace_of_ne_zero`: the reduced trace of `M_n(F)` is the matrix trace
  when `n` is nonzero in `F`, and `Matrix.reducedTrace_eq_trace` in characteristic `0`.
* `TauCeti.Algebra.reducedTrace_field`: the reduced trace of a finite field extension `E / F` is
  the field trace `Algebra.trace F E`.
* `TauCeti.Algebra.reducedTrace_baseChange_tmul`: for a central simple `A`, the reduced trace of
  `L ⊗[F] A` over `L` extends that of `A`, and
  `AlgEquiv.algebraMap_reducedTrace_eq_trace_of_ne_zero` computes `Trd_{A/F}(a)` as the matrix
  trace of `1 ⊗ a` in any splitting `L ⊗[F] A ≃ M_n(L)` with `n` nonzero in `F`
  (`AlgEquiv.algebraMap_reducedTrace_eq_trace` in characteristic `0`).

## Implementation notes

Mathlib's `Algebra.trace` is defined only for commutative algebras, so the regular trace of a
noncommutative algebra is written `LinearMap.trace F B (Algebra.lmul F B b)` throughout, as in
`Algebra.regularTraceForm`.

The definition makes sense for any `F`-algebra; it is the reduced trace when `B` is
finite-dimensional and semisimple and `F` has characteristic `0`. In characteristic `p` a degree
`d_c` divisible by `p` is `0` in `F`, and the formula above loses the factor `c`.

## References

* J.-P. Serre, *Local Fields*, Chapter XII.
* I. Reiner, *Maximal Orders*, §9.
* J. S. Milne, *Introduction to Shimura varieties*, §8.
-/

public section

open scoped TensorProduct

open Module

namespace TauCeti

namespace Algebra

section IdealTrace

variable (R : Type*) [CommRing R] {B : Type*} [Ring B] [Algebra R B]

/-- The trace over `R` of left multiplication by `b` on a left ideal `c` of `B`. For an isotypic
component `c` of a semisimple algebra it is the regular trace of the `c`-component of `b`. -/
noncomputable def idealTrace (c : Submodule B B) : B →ₗ[R] R :=
  LinearMap.trace R c ∘ₗ (Algebra.lsmul R R c).toLinearMap

variable {R}

/-- `TauCeti.Algebra.idealTrace R c b` is the trace of left multiplication by `b` on `c`. -/
theorem _root_.Submodule.idealTrace_apply (c : Submodule B B) (b : B) :
    TauCeti.Algebra.idealTrace R c b = LinearMap.trace R (c.restrictScalars R)
      ((Algebra.lmul R B b).restrict fun _ hx ↦ c.smul_mem b hx) :=
  (rfl)

/-- On the whole algebra, `TauCeti.Algebra.idealTrace` is the regular trace. -/
@[simp]
theorem idealTrace_top (b : B) :
    idealTrace R (⊤ : Submodule B B) b = LinearMap.trace R B (Algebra.lmul R B b) := by
  let e : ((⊤ : Submodule B B).restrictScalars R) ≃ₗ[R] B :=
    (LinearEquiv.ofEq _ _ (Submodule.restrictScalars_top R B B)).trans Submodule.topEquiv
  rw [Submodule.idealTrace_apply, ← LinearMap.trace_conj' _ e]
  congr 1

/-- Cyclicity of `TauCeti.Algebra.idealTrace`: it takes the same value on `a * b` and `b * a`. -/
theorem _root_.Submodule.idealTrace_mul_comm (c : Submodule B B) (a b : B) :
    TauCeti.Algebra.idealTrace R c (a * b) = TauCeti.Algebra.idealTrace R c (b * a) := by
  simp only [TauCeti.Algebra.idealTrace, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, map_mul]
  exact LinearMap.trace_mul_comm R _ _

/-- The trace of left multiplication by an element `b` of an isotypic component `c` vanishes on
every other isotypic component. -/
theorem idealTrace_eq_zero_of_mem_isotypicComponents {c c' : Submodule B B}
    (hc : c ∈ isotypicComponents B B) (hc' : c' ∈ isotypicComponents B B) (hne : c' ≠ c)
    {b : B} (hb : b ∈ c) : idealTrace R c' b = 0 := by
  have h0 : ((Algebra.lmul R B b).restrict fun _ hx ↦ c'.smul_mem b hx :
      c'.restrictScalars R →ₗ[R] c'.restrictScalars R) = 0 := by
    ext x
    simpa using mul_eq_zero_of_mem_isotypicComponents hc hc' hne hb x.property
  rw [c'.idealTrace_apply, h0, map_zero]

end IdealTrace

section Field

variable (F : Type*) [Field F] {B : Type*} [Ring B] [Algebra F B]

/-- The natural square root of `dim_F c / dim_F (c ∩ Z(B))` for a left ideal `c` of `B`. For an
isotypic component `c` of a finite-dimensional semisimple algebra, `c` is a simple algebra with
centre `Z(B) ∩ c` and this is its **degree** over that centre, in the sense of
`TauCeti.Algebra.deg` (`TauCeti.Algebra.idealDeg_top`). For other left ideals it is only this
number. -/
noncomputable def idealDeg (c : Submodule B B) : ℕ :=
  Nat.sqrt (finrank F (c.restrictScalars F) /
    finrank F ↥(c.restrictScalars F ⊓ Subalgebra.toSubmodule (Subalgebra.center F B)))

/-- The defining formula of `TauCeti.Algebra.idealDeg`. -/
theorem idealDeg_def (c : Submodule B B) :
    idealDeg F c = Nat.sqrt (finrank F (c.restrictScalars F) /
      finrank F ↥(c.restrictScalars F ⊓ Subalgebra.toSubmodule (Subalgebra.center F B))) :=
  (rfl)

variable (B) in
/-- The **reduced trace** `Trd_{B/F}` of an `F`-algebra `B`: the sum over the isotypic components
`c` of `B` as a left module over itself of `(idealDeg F c)⁻¹` times the trace of left
multiplication on `c`. For a finite-dimensional semisimple algebra in characteristic `0` it is the
sum over the simple factors of the field trace of the centre composed with the reduced trace
(`TauCeti.Algebra.reducedTrace_eq_trace_reducedTrace`). -/
noncomputable def reducedTrace : B →ₗ[F] F :=
  ∑ᶠ c ∈ isotypicComponents B B, ((idealDeg F c : F)⁻¹) • idealTrace F c

/-- The defining formula of `TauCeti.Algebra.reducedTrace`. -/
theorem reducedTrace_def :
    reducedTrace F B = ∑ᶠ c ∈ isotypicComponents B B, ((idealDeg F c : F)⁻¹) • idealTrace F c :=
  (rfl)

variable {F}

/-- **Cyclicity of the reduced trace.** -/
theorem reducedTrace_mul_comm (a b : B) : reducedTrace F B (a * b) = reducedTrace F B (b * a) :=
  finsum_mem_induction (fun T : B →ₗ[F] F ↦ T (a * b) = T (b * a)) rfl
    (fun _ _ h₁ h₂ ↦ by simp [h₁, h₂])
    (fun c _ ↦ by simp [Submodule.idealTrace_mul_comm])

section Semisimple

variable [IsSemisimpleRing B]

/-- On a semisimple algebra, which has finitely many isotypic components, the reduced trace of
`b` is the finite sum over the isotypic components `c` of `(idealDeg F c)⁻¹` times the trace of
left multiplication by `b` on `c`. -/
theorem reducedTrace_apply (b : B) :
    reducedTrace F B b =
      ∑ᶠ c ∈ isotypicComponents B B, (idealDeg F c : F)⁻¹ * idealTrace F c b := by
  have hs := (isotypicComponents B B).toFinite
  rw [reducedTrace_def, finsum_mem_eq_finite_toFinset_sum _ hs,
    finsum_mem_eq_finite_toFinset_sum _ hs]
  simp

variable [FiniteDimensional F B]

/-- The regular trace of a finite-dimensional semisimple algebra is the sum of the traces on its
isotypic components. -/
theorem trace_lmul_eq_sum_idealTrace (b : B) :
    LinearMap.trace F B (Algebra.lmul F B b) =
      ∑ᶠ c ∈ isotypicComponents B B, idealTrace F c b := by
  classical
  let _ : Fintype (isotypicComponents B B) := Fintype.ofFinite _
  have hint : DirectSum.IsInternal fun c : isotypicComponents B B ↦ c.val.restrictScalars F :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (iSupIndep_isotypicComponents_restrictScalars F) <| by
        rw [← Submodule.restrictScalars_iSup, ← sSup_eq_iSup', sSup_isotypicComponents,
          Submodule.restrictScalars_top]
  rw [← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype,
    LinearMap.trace_eq_sum_trace_restrict hint (f := Algebra.lmul F B b)
      fun c _ hx ↦ c.val.smul_mem b hx]
  rfl

/-- The trace on an isotypic component `c` of left multiplication by `b ∈ c` is the regular trace
of `b`. -/
theorem idealTrace_eq_trace_lmul {c : Submodule B B} (hc : c ∈ isotypicComponents B B)
    {b : B} (hb : b ∈ c) : idealTrace F c b = LinearMap.trace F B (Algebra.lmul F B b) := by
  rw [trace_lmul_eq_sum_idealTrace, finsum_mem_def, finsum_eq_single _ c, Set.indicator_of_mem hc]
  intro c' hne
  by_cases hc' : c' ∈ isotypicComponents B B
  · rw [Set.indicator_of_mem hc', idealTrace_eq_zero_of_mem_isotypicComponents hc hc' hne hb]
  · rw [Set.indicator_of_notMem hc']

/-- On an isotypic component `c`, the reduced trace of `b ∈ c` is `(idealDeg F c)⁻¹` times its
trace on `c`. -/
theorem reducedTrace_eq_of_mem {c : Submodule B B} (hc : c ∈ isotypicComponents B B) {b : B}
    (hb : b ∈ c) :
    reducedTrace F B b = (idealDeg F c : F)⁻¹ * LinearMap.trace F B (Algebra.lmul F B b) := by
  rw [reducedTrace_apply, finsum_mem_def, finsum_eq_single _ c, Set.indicator_of_mem hc,
    idealTrace_eq_trace_lmul hc hb]
  intro c' hne
  by_cases hc' : c' ∈ isotypicComponents B B
  · rw [Set.indicator_of_mem hc', idealTrace_eq_zero_of_mem_isotypicComponents hc hc' hne hb,
      mul_zero]
  · rw [Set.indicator_of_notMem hc']

/-- The degree of an isotypic component of a finite-dimensional semisimple algebra is positive. -/
theorem idealDeg_pos {c : Submodule B B} (hc : c ∈ isotypicComponents B B) : 0 < idealDeg F c := by
  obtain ⟨e, hec, he0, hcen⟩ := exists_ne_zero_mem_center_of_mem_isotypicComponents F B hc
  have hpos : 0 < finrank F ↥(c.restrictScalars F ⊓
      Subalgebra.toSubmodule (Subalgebra.center F B)) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨e, hec, hcen⟩, ne_of_apply_ne Subtype.val he0⟩
  rw [idealDeg_def, Nat.sqrt_pos, Nat.div_pos_iff]
  exact ⟨hpos, Submodule.finrank_mono inf_le_left⟩

/-- For `b` in an isotypic component `c` of a finite-dimensional semisimple algebra whose degree
`idealDeg F c` is nonzero in `F`, the trace of left multiplication by `b` is `idealDeg F c` times
the reduced trace of `b`. -/
theorem trace_lmul_eq_idealDeg_mul_reducedTrace_of_ne_zero {c : Submodule B B}
    (hc : c ∈ isotypicComponents B B) (hdeg : (idealDeg F c : F) ≠ 0) {b : B} (hb : b ∈ c) :
    LinearMap.trace F B (Algebra.lmul F B b) = idealDeg F c * reducedTrace F B b := by
  rw [reducedTrace_eq_of_mem hc hb, ← mul_assoc, mul_inv_cancel₀ hdeg, one_mul]

/-- **The regular trace is a positive multiple of the reduced trace on each simple factor.** For
`b` in an isotypic component `c` of a finite-dimensional semisimple algebra in characteristic `0`,
the trace of left multiplication by `b` is `idealDeg F c` times the reduced trace of `b`. -/
theorem trace_lmul_eq_idealDeg_mul_reducedTrace [CharZero F] {c : Submodule B B}
    (hc : c ∈ isotypicComponents B B) {b : B} (hb : b ∈ c) :
    LinearMap.trace F B (Algebra.lmul F B b) = idealDeg F c * reducedTrace F B b :=
  trace_lmul_eq_idealDeg_mul_reducedTrace_of_ne_zero hc (by exact_mod_cast (idealDeg_pos hc).ne')
    hb

end Semisimple

/-! ### Simple and central simple algebras -/

/-- On a simple Artinian algebra the reduced trace is `(idealDeg F ⊤)⁻¹` times the regular
trace. -/
theorem reducedTrace_of_isSimpleRing [IsSimpleRing B] [IsArtinianRing B] (b : B) :
    reducedTrace F B b =
      (idealDeg F (⊤ : Submodule B B) : F)⁻¹ * LinearMap.trace F B (Algebra.lmul F B b) := by
  rw [reducedTrace_def, (IsSimpleRing.isIsotypic B B).isotypicComponents_eq_singleton_top,
    finsum_mem_singleton, LinearMap.smul_apply, idealTrace_top, smul_eq_mul]

/-- On a simple algebra `B` central over a field `Z` finite over `F`, `idealDeg F ⊤` is the degree
of `B` over `Z`. -/
theorem idealDeg_top (Z : Type*) [Field Z] [Algebra F Z] [Algebra Z B] [IsScalarTower F Z B]
    [Algebra.IsCentral Z B] [IsSimpleRing B] [FiniteDimensional F Z] :
    idealDeg F (⊤ : Submodule B B) = deg Z B := by
  rw [idealDeg_def, Submodule.restrictScalars_top, top_inf_eq, finrank_top,
    Subalgebra.finrank_toSubmodule, finrank_center_eq_of_isCentral F Z,
    ← Module.finrank_mul_finrank F Z B, Nat.mul_div_cancel_left _ Module.finrank_pos,
    ← deg_sq Z B, Nat.sqrt_eq']

/-- **The reduced trace of a central simple algebra.** On a simple algebra `B` central over a
field `Z` finite over `F`, `Trd_{B/F}(b) = (deg_Z B)⁻¹ · tr_F(L_b)`. -/
theorem reducedTrace_eq_inv_deg_mul_trace_of_isScalarTower (Z : Type*) [Field Z] [Algebra F Z]
    [Algebra Z B] [IsScalarTower F Z B] [Algebra.IsCentral Z B] [IsSimpleRing B]
    [FiniteDimensional F Z] [FiniteDimensional Z B] (b : B) :
    reducedTrace F B b = (deg Z B : F)⁻¹ * LinearMap.trace F B (Algebra.lmul F B b) := by
  have := Module.Finite.trans Z (R := F) B
  have := IsArtinianRing.of_finite F B
  rw [reducedTrace_of_isSimpleRing, idealDeg_top Z]

/-- On a central simple algebra `A`, `Trd_{A/F}(a) = (deg A)⁻¹ · tr_F(L_a)`. -/
theorem reducedTrace_eq_inv_deg_mul_trace [Algebra.IsCentral F B] [IsSimpleRing B]
    [FiniteDimensional F B] (b : B) :
    reducedTrace F B b = (deg F B : F)⁻¹ * LinearMap.trace F B (Algebra.lmul F B b) :=
  reducedTrace_eq_inv_deg_mul_trace_of_isScalarTower F b

/-- **Transitivity of the reduced trace.** On a simple algebra `B` central over a field `Z` finite
over `F`, `Trd_{B/F} = Tr_{Z/F} ∘ Trd_{B/Z}`. -/
theorem reducedTrace_eq_trace_reducedTrace (Z : Type*) [Field Z] [Algebra F Z] [Algebra Z B]
    [IsScalarTower F Z B] [Algebra.IsCentral Z B] [IsSimpleRing B] [FiniteDimensional F Z]
    [FiniteDimensional Z B] (b : B) :
    reducedTrace F B b = Algebra.trace F Z (reducedTrace Z B b) := by
  have hl : (Algebra.lmul Z B b).restrictScalars F = Algebra.lmul F B b := by
    ext; simp
  rw [reducedTrace_eq_inv_deg_mul_trace_of_isScalarTower Z, reducedTrace_eq_inv_deg_mul_trace,
    ← hl, LinearMap.trace_restrictScalars, ← map_natCast (algebraMap F Z), ← map_inv₀,
    ← Algebra.smul_def, map_smul, smul_eq_mul]

/-- The reduced trace of a field extension `E / F` is the field trace. -/
@[simp]
theorem reducedTrace_field (E : Type*) [Field E] [Algebra F E] (x : E) :
    reducedTrace F E x = Algebra.trace F E x := by
  by_cases hE : FiniteDimensional F E
  · rw [reducedTrace_eq_trace_reducedTrace E, reducedTrace_eq_inv_deg_mul_trace, deg_self,
      Nat.cast_one, inv_one, one_mul, ← Algebra.trace_apply, Algebra.trace_self,
      LinearMap.id_apply]
  · rw [reducedTrace_of_isSimpleRing, Algebra.trace_apply,
      TauCeti.LinearMap.trace_eq_zero_of_not_finite hE, LinearMap.zero_apply, mul_zero]

variable [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B]

/-- On a central simple algebra whose degree is nonzero in `F`, the regular trace is the degree
times the reduced trace. -/
theorem trace_lmul_eq_deg_mul_reducedTrace_of_ne_zero (hdeg : (deg F B : F) ≠ 0) (b : B) :
    LinearMap.trace F B (Algebra.lmul F B b) = deg F B * reducedTrace F B b := by
  rw [reducedTrace_eq_inv_deg_mul_trace, ← mul_assoc, mul_inv_cancel₀ hdeg, one_mul]

/-- On a central simple algebra in characteristic `0`, the regular trace is the degree times the
reduced trace. -/
theorem trace_lmul_eq_deg_mul_reducedTrace [CharZero F] (b : B) :
    LinearMap.trace F B (Algebra.lmul F B b) = deg F B * reducedTrace F B b :=
  trace_lmul_eq_deg_mul_reducedTrace_of_ne_zero (by exact_mod_cast deg_ne_zero F B) b

/-- The reduced trace of `1` in a central simple algebra is its degree. -/
@[simp]
theorem reducedTrace_one : reducedTrace F B 1 = deg F B := by
  rw [reducedTrace_eq_inv_deg_mul_trace, map_one, LinearMap.trace_one, ← deg_sq F B, Nat.cast_pow,
    sq, ← mul_assoc]
  by_cases h : (deg F B : F) = 0
  · rw [h, mul_zero]
  · rw [inv_mul_cancel₀ h, one_mul]

/-- The reduced trace of a scalar `r` in a central simple algebra is `deg A · r`. -/
@[simp]
theorem reducedTrace_algebraMap (r : F) :
    reducedTrace F B (algebraMap F B r) = deg F B * r := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, reducedTrace_one, smul_eq_mul, mul_comm]

/-- An algebra isomorphism of central simple algebras preserves the reduced trace. -/
theorem _root_.AlgEquiv.reducedTrace_apply {B' : Type*} [Ring B'] [Algebra F B'] (e : B ≃ₐ[F] B')
    (b : B) :
    reducedTrace F B' (e b) = reducedTrace F B b := by
  have : IsSimpleRing B' := IsSimpleRing.of_ringEquiv e.toRingEquiv inferInstance
  -- `Algebra.IsCentral.of_algEquiv` needs `B` and `B'` in the same universe.
  have : Algebra.IsCentral F B' := ⟨fun x hx ↦ by
    obtain ⟨r, hr⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out (K := F) (D := B)
      (Subalgebra.mem_center_iff.mpr fun y ↦ by
        simpa using congrArg e.symm (Subalgebra.mem_center_iff.mp hx (e y))))
    exact Algebra.mem_bot.mpr ⟨r, by rw [← e.apply_symm_apply x, ← hr, AlgEquiv.commutes]⟩⟩
  have : FiniteDimensional F B' := Module.Finite.equiv e.toLinearEquiv
  have hl : Algebra.lmul F B' (e b) = e.toLinearEquiv.conj (Algebra.lmul F B b) := by
    ext; simp [LinearEquiv.conj_apply]
  rw [reducedTrace_eq_inv_deg_mul_trace, reducedTrace_eq_inv_deg_mul_trace, hl,
    LinearMap.trace_conj', deg_eq_of_algEquiv e]

variable (L : Type*) [Field L] [Algebra F L]

/-- **The reduced trace commutes with base change.** For a central simple algebra `A` over `F`
and a field extension `L / F`, the reduced trace of `1 ⊗ a` in `L ⊗[F] A` is that of `a`. -/
theorem reducedTrace_baseChange_tmul (b : B) :
    reducedTrace L (L ⊗[F] B) (1 ⊗ₜ b) = algebraMap F L (reducedTrace F B b) := by
  rw [reducedTrace_eq_inv_deg_mul_trace, reducedTrace_eq_inv_deg_mul_trace, deg_baseChange,
    ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, map_mul, map_inv₀, map_natCast]

end Field

/-! ### Matrix algebras and splitting fields -/

section Matrix

variable {F : Type*} [Field F]

/-- **The reduced trace of a matrix algebra is the matrix trace**, for `n × n` matrices with `n`
nonzero in `F`. -/
theorem _root_.Matrix.reducedTrace_eq_trace_of_ne_zero {n : Type*} [Fintype n] [DecidableEq n]
    (hn : (Fintype.card n : F) ≠ 0) (M : Matrix n n F) :
    reducedTrace F (Matrix n n F) M = M.trace := by
  have : Nonempty n := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero fun h ↦ hn (by simp [h]))
  have hdeg : deg F (Matrix n n F) = Fintype.card n :=
    deg_eq_of_finrank_eq_sq (by rw [Module.finrank_matrix, Module.finrank_self, mul_one, sq])
  have hl : Algebra.lmul F (Matrix n n F) M = LinearMap.mulLeft F M := rfl
  rw [reducedTrace_eq_inv_deg_mul_trace, hdeg, hl, Matrix.trace_mulLeft, ← mul_assoc,
    inv_mul_cancel₀ hn, one_mul]

/-- **The reduced trace of a matrix algebra is the matrix trace**, in characteristic `0`. -/
@[simp]
theorem _root_.Matrix.reducedTrace_eq_trace [CharZero F] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n F) : reducedTrace F (Matrix n n F) M = M.trace := by
  obtain hn | hn := isEmpty_or_nonempty n
  · rw [Subsingleton.elim M 0, map_zero, Matrix.trace_zero]
  exact M.reducedTrace_eq_trace_of_ne_zero (by simp)

/-- **The reduced trace via a splitting field.** If `L ⊗[F] A ≃ M_n(L)` over `L` for a central
simple algebra `A`, with `n` nonzero in `F`, then `Trd_{A/F}(a)` is the matrix trace of the image
of `1 ⊗ a`. -/
theorem _root_.AlgEquiv.algebraMap_reducedTrace_eq_trace_of_ne_zero {A : Type*} [Ring A]
    [Algebra F A] [Algebra.IsCentral F A] [IsSimpleRing A] [FiniteDimensional F A] {L : Type*}
    [Field L] [Algebra F L] {n : Type*} [Fintype n] [DecidableEq n]
    (e : L ⊗[F] A ≃ₐ[L] Matrix n n L) (hn : (Fintype.card n : F) ≠ 0) (a : A) :
    algebraMap F L (reducedTrace F A a) = (e (1 ⊗ₜ a)).trace := by
  have hn' : (Fintype.card n : L) ≠ 0 := by
    rwa [← map_natCast (algebraMap F L), map_ne_zero]
  rw [← reducedTrace_baseChange_tmul, ← e.reducedTrace_apply,
    Matrix.reducedTrace_eq_trace_of_ne_zero hn']

/-- **The reduced trace via a splitting field**, in characteristic `0`. If `L ⊗[F] A ≃ M_n(L)`
over `L` for a central simple algebra `A`, then `Trd_{A/F}(a)` is the matrix trace of the image of
`1 ⊗ a`. -/
theorem _root_.AlgEquiv.algebraMap_reducedTrace_eq_trace [CharZero F] {A : Type*} [Ring A]
    [Algebra F A] [Algebra.IsCentral F A] [IsSimpleRing A] [FiniteDimensional F A] {L : Type*}
    [Field L] [Algebra F L] {n : Type*} [Fintype n] [DecidableEq n]
    (e : L ⊗[F] A ≃ₐ[L] Matrix n n L) (a : A) :
    algebraMap F L (reducedTrace F A a) = (e (1 ⊗ₜ a)).trace := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap F L).injective
  rw [← reducedTrace_baseChange_tmul, ← e.reducedTrace_apply, Matrix.reducedTrace_eq_trace]

end Matrix

end Algebra

end TauCeti
