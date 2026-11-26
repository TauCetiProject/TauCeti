/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Imported publicly: the reduced trace `TauCeti.Algebra.reducedTrace` of a central simple
-- algebra, with its degree `TauCeti.Algebra.deg`, occurs in the comparison theorems.
public import TauCeti.Algebra.CentralSimple.ReducedTrace
public import TauCeti.LinearAlgebra.Trace.RestrictScalars
public import TauCeti.RingTheory.Semisimple.CenterDimension

import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import TauCeti.Algebra.Subalgebra.Center
import TauCeti.LinearAlgebra.Trace.Basic
import TauCeti.RingTheory.SimpleModule.Isotypic

/-!
# The reduced trace of a semisimple algebra

Let `B` be a finite-dimensional semisimple algebra over a field `F`. Its **reduced trace**
`Trd_{B/F} : B → F` is the sum over the simple factors `B_i` of `B`, with centres `Z_i`, of the
field trace `Tr_{Z_i/F}` composed with the reduced trace `TauCeti.Algebra.reducedTrace Z_i B_i` of
the central simple `Z_i`-algebra `B_i`.

This file defines it as `TauCeti.Algebra.semisimpleReducedTrace F B` without choosing a Wedderburn
presentation. The simple factors of `B` are its isotypic components `c` as a left module over
itself, which are two-sided ideals, and left multiplication by `b` preserves each of them. Write
`TauCeti.Algebra.idealTrace F c b` for the trace of left multiplication by `b` on `c`, and
`d_c = TauCeti.Algebra.idealDeg F c` for the natural square root of the dimension of `c` over
`Z(B) ∩ c`; mathematically `Z(B) ∩ c` is the centre of the simple factor `c`, `d_c` is its degree
and the trace on `c` is `d_c` times the field trace of its reduced trace. The definition is

`Trd_{B/F}(b) = ∑_c d_c⁻¹ · tr_F(x ↦ b x on c)`.

In characteristic `0`, the case of the definition, each `d_c` is invertible in `F`.

## Main definitions

* `TauCeti.Algebra.idealTrace F c`: the trace over `F` of left multiplication on a left ideal `c`.
* `TauCeti.Algebra.idealDeg F c`: the natural square root of `dim_F c / dim_F (c ∩ Z(B))`, meant
  as the degree of an isotypic component `c` over its centre; `TauCeti.Algebra.idealDeg_top`
  proves this for `c = ⊤` when `B` is simple and central over a field `Z`.
* `TauCeti.Algebra.semisimpleReducedTrace F B`: the reduced trace `Trd_{B/F}`.

## Main results

* `TauCeti.Algebra.semisimpleReducedTrace_mul_comm`: `Trd(a b) = Trd(b a)`.
* `TauCeti.Algebra.semisimpleReducedTrace_eq_trace_reducedTrace`: on a simple algebra `B` central
  over a field `Z` finite over `F`, in characteristic `0`, `Trd_{B/F} = Tr_{Z/F} ∘ Trd_{B/Z}`,
  where `Trd_{B/Z}` is `TauCeti.Algebra.reducedTrace Z B`
  (`TauCeti.Algebra.semisimpleReducedTrace_eq_trace_reducedTrace_of_ne_zero` when `deg_Z B` is
  nonzero in `F`). In particular on a central simple algebra it is
  `TauCeti.Algebra.reducedTrace F B` (`TauCeti.Algebra.semisimpleReducedTrace_eq_reducedTrace`).
* `TauCeti.Algebra.semisimpleReducedTrace_eq_inv_deg_mul_trace`: on a central simple algebra `A`,
  `Trd_{A/F}(a) = (deg A)⁻¹ · tr_F(L_a)`.
* `TauCeti.Algebra.trace_mulLeft_eq_idealDeg_mul_semisimpleReducedTrace_of_ne_zero`: on a
  semisimple algebra, for `b` in a simple factor `c` with `d_c` nonzero in `F`,
  `tr_F(L_b) = d_c · Trd_{B/F}(b)`
  (`TauCeti.Algebra.trace_mulLeft_eq_idealDeg_mul_semisimpleReducedTrace` in characteristic `0`,
  where `d_c > 0` by `TauCeti.Algebra.idealDeg_pos`).
* `TauCeti.Algebra.semisimpleReducedTrace_eq_trace`: the reduced trace of a field extension
  `E / F` is the field trace `Algebra.trace F E`.

## Implementation notes

Mathlib's `Algebra.trace` is defined only for commutative algebras, so the regular trace of a
noncommutative algebra is written `LinearMap.trace F B (LinearMap.mulLeft F b)` throughout, as in
`TauCeti.Algebra.trace_mulLeft_eq_deg_mul_reducedTrace`.

The definition makes sense for any `F`-algebra; it is the reduced trace when `B` is
finite-dimensional and semisimple and `F` has characteristic `0`. In characteristic `p` a degree
`d_c` divisible by `p` is `0` in `F`, and the formula above loses the factor `c`. The reduced trace
`TauCeti.Algebra.reducedTrace` of a central simple algebra is defined in every characteristic.

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

/-- `TauCeti.Algebra.idealTrace R c b` is the trace of left multiplication by `b` on `c`. -/
theorem idealTrace_apply (c : Submodule B B) (b : B) :
    idealTrace R c b = LinearMap.trace R (c.restrictScalars R)
      ((LinearMap.mulLeft R b).restrict
        fun _ hx ↦ (c.restrictScalars_mem R _).2 (c.smul_mem b hx)) := by
  -- `idealTrace` uses the `R`-module structure of `c` from the scalar tower `R → B → B`, the right
  -- side that of the `R`-submodule `c.restrictScalars R`. Mathlib's
  -- `Submodule.restrictScalarsEquiv` identifies the two `R`-modules; it is the identity on
  -- elements, which closes the last goal.
  rw [idealTrace, LinearMap.comp_apply,
    ← LinearMap.trace_conj' _ ((c.restrictScalarsEquiv R B).restrictScalars R)]
  refine congrArg _ (LinearMap.ext fun x ↦ Subtype.ext ?_)
  simp
  rfl

/-- Cyclicity of `TauCeti.Algebra.idealTrace`: it takes the same value on `a * b` and `b * a`. -/
theorem idealTrace_mul_comm (c : Submodule B B) (a b : B) :
    idealTrace R c (a * b) = idealTrace R c (b * a) := by
  simp only [idealTrace, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    map_mul]
  exact LinearMap.trace_mul_comm R _ _

variable {R}

/-- On the whole algebra, `TauCeti.Algebra.idealTrace` is the regular trace. -/
@[simp]
theorem idealTrace_top (b : B) :
    idealTrace R (⊤ : Submodule B B) b = LinearMap.trace R B (LinearMap.mulLeft R b) := by
  let e : ((⊤ : Submodule B B).restrictScalars R) ≃ₗ[R] B :=
    (LinearEquiv.ofEq _ _ (Submodule.restrictScalars_top R B B)).trans Submodule.topEquiv
  rw [idealTrace_apply, ← LinearMap.trace_conj' _ e]
  refine congrArg _ <| LinearMap.ext fun x ↦ ?_
  -- Plain `simp [e]` merges `e.conj` into `Submodule.topEquiv.conj` on the domain
  -- `restrictScalars R ⊤` (not syntactically `⊤`) and gets stuck there, so the conjugation by
  -- the composite equivalence is unfolded by hand first.
  simp only [e, LinearEquiv.conj_apply_apply, LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply,
    Submodule.topEquiv_apply, LinearEquiv.coe_ofEq_apply, LinearMap.coe_restrict_apply,
    LinearMap.mulLeft_apply, LinearEquiv.ofEq_symm]
  simp

/-- The trace of left multiplication by an element `b` of an isotypic component `c` vanishes on
every other isotypic component. -/
theorem idealTrace_eq_zero_of_mem_isotypicComponents {c c' : Submodule B B}
    (hc : c ∈ isotypicComponents B B) (hc' : c' ∈ isotypicComponents B B) (hne : c' ≠ c)
    {b : B} (hb : b ∈ c) : idealTrace R c' b = 0 := by
  have h0 : ((LinearMap.mulLeft R b).restrict
      fun _ hx ↦ (c'.restrictScalars_mem R _).2 (c'.smul_mem b hx) :
      c'.restrictScalars R →ₗ[R] c'.restrictScalars R) = 0 := by
    ext x
    simpa using mul_eq_zero_of_mem_isotypicComponents hc hc' hne hb x.property
  rw [idealTrace_apply R c', h0, map_zero]

/-- A sum over the isotypic components `c'` of a function of `c'` and `idealTrace R c' b`, which
vanishes when the trace does, reduces for `b` in an isotypic component `c` to its term at `c`. -/
private theorem finsum_mem_isotypicComponents_idealTrace_eq {M : Type*} [AddCommMonoid M]
    (f : Submodule B B → R → M) (hf : ∀ c', f c' 0 = 0) {c : Submodule B B}
    (hc : c ∈ isotypicComponents B B) {b : B} (hb : b ∈ c) :
    ∑ᶠ c' ∈ isotypicComponents B B, f c' (idealTrace R c' b) = f c (idealTrace R c b) := by
  rw [finsum_mem_def, finsum_eq_single _ c, Set.indicator_of_mem hc]
  intro c' hne
  by_cases hc' : c' ∈ isotypicComponents B B
  · rw [Set.indicator_of_mem hc', idealTrace_eq_zero_of_mem_isotypicComponents hc hc' hne hb, hf]
  · rw [Set.indicator_of_notMem hc']

end IdealTrace

section Field

variable (F : Type*) [Field F] {B : Type*} [Ring B] [Algebra F B]

/-- The natural square root of `dim_F c / dim_F (c ∩ Z(B))` for a left ideal `c` of `B`. For an
isotypic component `c` of a finite-dimensional semisimple algebra, `c` is a simple algebra with
centre `Z(B) ∩ c`, and this number is meant as its **degree** over that centre. This file proves
the identification only for `c = ⊤` with `B` simple and central over a field `Z`:
`TauCeti.Algebra.idealDeg_top` gives `idealDeg F ⊤ = TauCeti.Algebra.deg Z B`. For other left
ideals it is only this number. -/
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
multiplication on `c`. It is meant as the reduced trace of a finite-dimensional semisimple algebra
in characteristic `0`: the sum over the simple factors of the field trace of the centre composed
with the reduced trace of the factor. This file proves that formula for a simple algebra `B`
central over a field `Z` finite over `F`, where it reads
`Tr_{Z/F} ∘ TauCeti.Algebra.reducedTrace Z B`
(`TauCeti.Algebra.semisimpleReducedTrace_eq_trace_reducedTrace`). -/
noncomputable def semisimpleReducedTrace : B →ₗ[F] F :=
  ∑ᶠ c ∈ isotypicComponents B B, ((idealDeg F c : F)⁻¹) • idealTrace F c

/-- The defining formula of `TauCeti.Algebra.semisimpleReducedTrace`. -/
theorem semisimpleReducedTrace_def :
    semisimpleReducedTrace F B =
      ∑ᶠ c ∈ isotypicComponents B B, ((idealDeg F c : F)⁻¹) • idealTrace F c :=
  (rfl)

variable {F}

/-- **Cyclicity of the reduced trace.** -/
theorem semisimpleReducedTrace_mul_comm (a b : B) :
    semisimpleReducedTrace F B (a * b) = semisimpleReducedTrace F B (b * a) :=
  finsum_mem_induction (fun T : B →ₗ[F] F ↦ T (a * b) = T (b * a)) rfl
    (fun _ _ h₁ h₂ ↦ by simp [h₁, h₂])
    (fun c _ ↦ by simp [idealTrace_mul_comm])

section Semisimple

variable [IsSemisimpleRing B]

/-- On a semisimple algebra, which has finitely many isotypic components, the reduced trace of
`b` is the finite sum over the isotypic components `c` of `(idealDeg F c)⁻¹` times the trace of
left multiplication by `b` on `c`. -/
theorem semisimpleReducedTrace_apply (b : B) :
    semisimpleReducedTrace F B b =
      ∑ᶠ c ∈ isotypicComponents B B, (idealDeg F c : F)⁻¹ * idealTrace F c b := by
  have hs := (isotypicComponents B B).toFinite
  rw [semisimpleReducedTrace_def, finsum_mem_eq_finite_toFinset_sum _ hs,
    finsum_mem_eq_finite_toFinset_sum _ hs]
  simp

variable [FiniteDimensional F B]

/-- The regular trace of a finite-dimensional semisimple algebra is the sum of the traces on its
isotypic components. -/
theorem trace_mulLeft_eq_finsum_idealTrace (b : B) :
    LinearMap.trace F B (LinearMap.mulLeft F b) =
      ∑ᶠ c ∈ isotypicComponents B B, idealTrace F c b := by
  classical
  let _ : Fintype (isotypicComponents B B) := Fintype.ofFinite _
  have hint : DirectSum.IsInternal fun c : isotypicComponents B B ↦ c.val.restrictScalars F :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (iSupIndep_isotypicComponents_restrictScalars F) <| by
        rw [← Submodule.restrictScalars_iSup, ← sSup_eq_iSup', sSup_isotypicComponents,
          Submodule.restrictScalars_top]
  rw [← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype,
    LinearMap.trace_eq_sum_trace_restrict hint (f := LinearMap.mulLeft F b)
      fun c _ hx ↦ (c.val.restrictScalars_mem F _).2 (c.val.smul_mem b hx)]
  simp only [idealTrace_apply]

/-- The trace on an isotypic component `c` of left multiplication by `b ∈ c` is the regular trace
of `b`. -/
theorem idealTrace_eq_trace_mulLeft {c : Submodule B B} (hc : c ∈ isotypicComponents B B)
    {b : B} (hb : b ∈ c) : idealTrace F c b = LinearMap.trace F B (LinearMap.mulLeft F b) := by
  rw [trace_mulLeft_eq_finsum_idealTrace,
    finsum_mem_isotypicComponents_idealTrace_eq (fun _ t ↦ t) (fun _ ↦ rfl) hc hb]

/-- On an isotypic component `c`, the reduced trace of `b ∈ c` is `(idealDeg F c)⁻¹` times its
trace on `c`. -/
theorem semisimpleReducedTrace_eq_inv_idealDeg_mul_trace_of_mem {c : Submodule B B}
    (hc : c ∈ isotypicComponents B B) {b : B} (hb : b ∈ c) :
    semisimpleReducedTrace F B b =
      (idealDeg F c : F)⁻¹ * LinearMap.trace F B (LinearMap.mulLeft F b) := by
  rw [semisimpleReducedTrace_apply, finsum_mem_isotypicComponents_idealTrace_eq
    (fun c' t ↦ (idealDeg F c' : F)⁻¹ * t) (fun _ ↦ mul_zero _) hc hb,
    idealTrace_eq_trace_mulLeft hc hb]

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
theorem trace_mulLeft_eq_idealDeg_mul_semisimpleReducedTrace_of_ne_zero {c : Submodule B B}
    (hc : c ∈ isotypicComponents B B) (hdeg : (idealDeg F c : F) ≠ 0) {b : B} (hb : b ∈ c) :
    LinearMap.trace F B (LinearMap.mulLeft F b) = idealDeg F c * semisimpleReducedTrace F B b := by
  rw [semisimpleReducedTrace_eq_inv_idealDeg_mul_trace_of_mem hc hb, ← mul_assoc,
    mul_inv_cancel₀ hdeg, one_mul]

/-- **The regular trace is a positive multiple of the reduced trace on each simple factor.** For
`b` in an isotypic component `c` of a finite-dimensional semisimple algebra in characteristic `0`,
the trace of left multiplication by `b` is `idealDeg F c` times the reduced trace of `b`. -/
theorem trace_mulLeft_eq_idealDeg_mul_semisimpleReducedTrace [CharZero F] {c : Submodule B B}
    (hc : c ∈ isotypicComponents B B) {b : B} (hb : b ∈ c) :
    LinearMap.trace F B (LinearMap.mulLeft F b) = idealDeg F c * semisimpleReducedTrace F B b :=
  trace_mulLeft_eq_idealDeg_mul_semisimpleReducedTrace_of_ne_zero hc
    (by exact_mod_cast (idealDeg_pos hc).ne') hb

end Semisimple

/-! ### Simple and central simple algebras -/

/-- On a simple Artinian algebra the reduced trace is `(idealDeg F ⊤)⁻¹` times the regular
trace. -/
theorem semisimpleReducedTrace_eq_inv_idealDeg_top_mul_trace [IsSimpleRing B] [IsArtinianRing B]
    (b : B) :
    semisimpleReducedTrace F B b =
      (idealDeg F (⊤ : Submodule B B) : F)⁻¹ * LinearMap.trace F B (LinearMap.mulLeft F b) := by
  rw [semisimpleReducedTrace_def,
    (IsSimpleRing.isIsotypic B B).isotypicComponents_eq_singleton_top, finsum_mem_singleton,
    LinearMap.smul_apply, idealTrace_top, smul_eq_mul]

/-- On a simple algebra `B` central over a field `Z` finite over `F`, `idealDeg F ⊤` is the degree
of `B` over `Z`. -/
theorem idealDeg_top (Z : Type*) [Field Z] [Algebra F Z] [Algebra Z B] [IsScalarTower F Z B]
    [Algebra.IsCentral Z B] [IsSimpleRing B] [FiniteDimensional F Z] :
    idealDeg F (⊤ : Submodule B B) = deg Z B := by
  have hB : finrank F B = finrank F Z * deg Z B ^ 2 := by
    rw [deg_sq, Module.finrank_mul_finrank]
  have hZ : finrank F Z ≠ 0 := Module.finrank_pos.ne'
  rw [idealDeg_def, Submodule.restrictScalars_top, top_inf_eq, finrank_top,
    Subalgebra.finrank_toSubmodule, finrank_center_eq_of_isCentral F Z, hB,
    Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hZ), Nat.sqrt_eq']

/-- **The reduced trace of a central simple algebra.** On a simple algebra `B` central over a
field `Z` finite over `F`, `Trd_{B/F}(b) = (deg_Z B)⁻¹ · tr_F(L_b)`. -/
theorem semisimpleReducedTrace_eq_inv_deg_mul_trace_of_isScalarTower (Z : Type*) [Field Z]
    [Algebra F Z] [Algebra Z B] [IsScalarTower F Z B] [Algebra.IsCentral Z B] [IsSimpleRing B]
    [FiniteDimensional F Z] [FiniteDimensional Z B] (b : B) :
    semisimpleReducedTrace F B b =
      (deg Z B : F)⁻¹ * LinearMap.trace F B (LinearMap.mulLeft F b) := by
  have := Module.Finite.trans Z (R := F) B
  have := IsArtinianRing.of_finite F B
  rw [semisimpleReducedTrace_eq_inv_idealDeg_top_mul_trace, idealDeg_top Z]

/-- On a central simple algebra `A`, `Trd_{A/F}(a) = (deg A)⁻¹ · tr_F(L_a)`. -/
theorem semisimpleReducedTrace_eq_inv_deg_mul_trace [Algebra.IsCentral F B] [IsSimpleRing B]
    [FiniteDimensional F B] (b : B) :
    semisimpleReducedTrace F B b =
      (deg F B : F)⁻¹ * LinearMap.trace F B (LinearMap.mulLeft F b) :=
  semisimpleReducedTrace_eq_inv_deg_mul_trace_of_isScalarTower F b

/-- The reduced trace of a field extension `E / F` is the field trace. -/
@[simp]
theorem semisimpleReducedTrace_eq_trace (E : Type*) [Field E] [Algebra F E] (x : E) :
    semisimpleReducedTrace F E x = Algebra.trace F E x := by
  by_cases hE : FiniteDimensional F E
  · rw [semisimpleReducedTrace_eq_inv_deg_mul_trace_of_isScalarTower E, deg_self, Nat.cast_one,
      inv_one, one_mul, Algebra.trace_apply]
    -- `Algebra.trace_apply` is stated with `Algebra.lmul`; both maps are `y ↦ x * y`.
    exact congrArg _ <| LinearMap.ext fun y ↦ by simp
  · rw [semisimpleReducedTrace_eq_inv_idealDeg_top_mul_trace, Algebra.trace_apply,
      TauCeti.LinearMap.trace_eq_zero_of_not_finite hE, LinearMap.zero_apply, LinearMap.zero_apply,
      mul_zero]

/-- **Comparison with the reduced trace of a central simple algebra.** On a simple algebra `B`
central over a field `Z` finite over `F`, whose degree over `Z` is nonzero in `F`,
`Trd_{B/F} = Tr_{Z/F} ∘ Trd_{B/Z}`, where `Trd_{B/Z}` is the reduced trace
`TauCeti.Algebra.reducedTrace Z B` of the central simple `Z`-algebra `B`. -/
theorem semisimpleReducedTrace_eq_trace_reducedTrace_of_ne_zero (Z : Type*) [Field Z]
    [Algebra F Z] [Algebra Z B] [IsScalarTower F Z B] [Algebra.IsCentral Z B] [IsSimpleRing B]
    [FiniteDimensional F Z] [FiniteDimensional Z B] (hdeg : (deg Z B : F) ≠ 0) (b : B) :
    semisimpleReducedTrace F B b = Algebra.trace F Z (reducedTrace Z B b) := by
  have hl : (LinearMap.mulLeft Z b).restrictScalars F = LinearMap.mulLeft F b := by
    ext; simp
  rw [semisimpleReducedTrace_eq_inv_deg_mul_trace_of_isScalarTower Z, ← hl,
    LinearMap.trace_restrictScalars, trace_mulLeft_eq_deg_mul_reducedTrace]
  rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
  field_simp

/-- **Comparison with the reduced trace of a central simple algebra**, in characteristic `0`. On
a simple algebra `B` central over a field `Z` finite over `F`, `Trd_{B/F} = Tr_{Z/F} ∘ Trd_{B/Z}`,
where `Trd_{B/Z}` is the reduced trace `TauCeti.Algebra.reducedTrace Z B`. -/
theorem semisimpleReducedTrace_eq_trace_reducedTrace [CharZero F] (Z : Type*) [Field Z]
    [Algebra F Z] [Algebra Z B] [IsScalarTower F Z B] [Algebra.IsCentral Z B] [IsSimpleRing B]
    [FiniteDimensional F Z] [FiniteDimensional Z B] (b : B) :
    semisimpleReducedTrace F B b = Algebra.trace F Z (reducedTrace Z B b) :=
  semisimpleReducedTrace_eq_trace_reducedTrace_of_ne_zero Z
    (Nat.cast_ne_zero.mpr (deg_ne_zero Z B)) b

variable [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B]

/-- On a central simple algebra whose degree is nonzero in `F`, `semisimpleReducedTrace F B` is
the reduced trace `TauCeti.Algebra.reducedTrace F B`. -/
theorem semisimpleReducedTrace_eq_reducedTrace_of_ne_zero (hdeg : (deg F B : F) ≠ 0) (b : B) :
    semisimpleReducedTrace F B b = reducedTrace F B b := by
  rw [semisimpleReducedTrace_eq_trace_reducedTrace_of_ne_zero F hdeg, Algebra.trace_self_apply]

/-- On a central simple algebra in characteristic `0`, `semisimpleReducedTrace F B` is the reduced
trace `TauCeti.Algebra.reducedTrace F B`. -/
theorem semisimpleReducedTrace_eq_reducedTrace [CharZero F] (b : B) :
    semisimpleReducedTrace F B b = reducedTrace F B b := by
  rw [semisimpleReducedTrace_eq_trace_reducedTrace F, Algebra.trace_self_apply]

end Field

end Algebra

end TauCeti
