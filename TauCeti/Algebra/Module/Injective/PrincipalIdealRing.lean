/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Injective modules over principal ideal rings

If multiplication by each nonzero scalar is surjective on a module over a principal ideal ring,
the module satisfies Baer's criterion and is injective.

A division algebra faithfully containing the scalar ring has this divisibility property, as does
its quotient by any submodule. In particular, `ℚ_p / ℤ_p` is injective over `ℤ_p`. Thus a
`ℚ_p / ℤ_p`-valued character of a torsion submodule extends to the whole module, without a splitting
or finite-generation assumption. This is the extension property used in torsion duality.

Every quotient `R ⧸ (a)` of a principal ideal domain `R` by a nonzero element `a` is also
self-injective: pulling an ideal of `R ⧸ (a)` back to `R` expresses it as `(d) ⧸ (a)` for a divisor
`d` of `a`, and annihilation by `a / d` forces the image of the generator under any linear map into
`R ⧸ (a)` to be divisible by `d`.

## Main results

* `Module.Baer.of_surjective_smul`: scalar divisibility implies Baer's criterion.
* `Submodule.injective_quotient_of_divisionRing`: quotients of a faithful division algebra are
  injective over a principal ideal ring.
* `Module.Baer.quotient_span_singleton` and `Ideal.Quotient.injective_span_singleton`: for `a ≠ 0`
  in a principal ideal domain `R`, the quotient ring `R ⧸ Ideal.span {a}` satisfies Baer's criterion
  and is self-injective.
-/

public section

/- Adapted from Jujian Zhang's Module.Baer.of_divisible in
Mathlib/Algebra/Category/Grp/Injective.lean, with scalar surjectivity in place of integer
division. -/
/-- A module over a principal ideal ring satisfies Baer's criterion if multiplication by each
nonzero scalar is surjective. -/
theorem Module.Baer.of_surjective_smul {R M : Type*} [Ring R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M]
    (h : ∀ r : R, r ≠ 0 → Function.Surjective (fun x : M ↦ r • x)) : Module.Baer R M := by
  intro I g
  obtain ⟨r, rfl⟩ := IsPrincipalIdealRing.principal I
  obtain rfl | hr := eq_or_ne r 0
  · refine ⟨0, fun x hx ↦ ?_⟩
    rw [Submodule.span_zero_singleton] at hx
    subst hx
    exact (map_zero g).symm
  have hrI : r ∈ Submodule.span R {r} := Submodule.mem_span_singleton_self r
  obtain ⟨m, hm⟩ := h r hr (g ⟨r, hrI⟩)
  refine ⟨LinearMap.toSpanSingleton R M m, fun x hx ↦ ?_⟩
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hx
  have hx' : (⟨s • r, hx⟩ : Submodule.span R {r}) = s • ⟨r, hrI⟩ := Subtype.ext rfl
  simp only [hx', map_smul, LinearMap.toSpanSingleton_apply, hm]

/-- Every quotient of a division algebra faithfully containing a principal ideal ring is
injective as a module over that ring. In particular, this applies to the quotient of a fraction
field by any submodule, such as `ℚ_p / ℤ_p` over `ℤ_p`. -/
instance Submodule.injective_quotient_of_divisionRing {R K : Type*} [CommRing R]
    [IsPrincipalIdealRing R] [DivisionRing K] [Algebra R K] [FaithfulSMul R K]
    (S : Submodule R K) : Module.Injective R (K ⧸ S) := by
  apply (Module.Baer.of_surjective_smul ?_).injective
  intro r hr q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective S q
  have hR : algebraMap R K r ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective R K).ne hr
  refine ⟨S.mkQ ((algebraMap R K r)⁻¹ * x), ?_⟩
  dsimp only
  rw [← map_smul]
  simp [Algebra.smul_def, hR]

/-- **Quotients of a principal ideal domain by a nonzero principal ideal satisfy Baer's criterion
over themselves.** Generalizes `Module.Baer.zmod_self` from `ℤ ⧸ nℤ` to any principal ideal domain,
covering Artinian valuation quotients `O ⧸ (ϖ ^ n)`. -/
theorem Module.Baer.quotient_span_singleton {R : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] {a : R} (ha : a ≠ 0) :
    Module.Baer (R ⧸ Ideal.span {a}) (R ⧸ Ideal.span {a}) := by
  let π := Ideal.Quotient.mk (Ideal.span ({a} : Set R))
  intro I g
  obtain ⟨d, hd_eq⟩ : ∃ d : R, I.comap π = Ideal.span {d} :=
    ⟨_, (Ideal.span_singleton_generator (I.comap π)).symm⟩
  have hI : I = Ideal.span {π d} := by
    rw [← Ideal.map_comap_of_surjective π Ideal.Quotient.mk_surjective I, hd_eq, Ideal.map_span,
      Set.image_singleton]
  subst hI
  have ha_mem : a ∈ Ideal.span {d} := by
    rw [← hd_eq, Ideal.mem_comap,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a)]
    exact zero_mem _
  obtain ⟨c, hac⟩ := Ideal.mem_span_singleton.mp ha_mem
  have hc : c ≠ 0 := right_ne_zero_of_mul (hac ▸ ha)
  have hd : π d ∈ Ideal.span {π d} := Ideal.mem_span_singleton_self (π d)
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (g ⟨π d, hd⟩)
  -- Since `c * d = a` vanishes in the quotient, `π c` annihilates `g ⟨π d, hd⟩ = π z`.
  have hcz : π (c * z) = 0 := by
    have hcd : π c • (⟨π d, hd⟩ : Ideal.span {π d}) = 0 := by
      ext
      simp only [SetLike.val_smul, smul_eq_mul, ZeroMemClass.coe_zero, ← map_mul, mul_comm c d,
        ← hac]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a)
    rw [map_mul, ← smul_eq_mul, hz, ← map_smul, hcd, map_zero]
  obtain ⟨k, hkz⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hcz)
  have hdz : d ∣ z := ⟨k, mul_left_cancel₀ hc <| by
    calc c * z = a * k := hkz
      _ = (d * c) * k := by rw [hac]
      _ = c * (d * k) := by ring⟩
  obtain ⟨y, rfl⟩ := hdz
  refine ⟨LinearMap.toSpanSingleton _ _ (π y), fun x hx ↦ ?_⟩
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  have hs : (⟨s * π d, hx⟩ : Ideal.span {π d}) = s • ⟨π d, hd⟩ := Subtype.ext (by simp)
  rw [hs, map_smul, LinearMap.toSpanSingleton_apply, ← hz, map_mul, smul_eq_mul, smul_eq_mul,
    mul_assoc]

/-- **A quotient of a principal ideal domain by a nonzero principal ideal is self-injective.** -/
theorem Ideal.Quotient.injective_span_singleton {R : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] {a : R} (ha : a ≠ 0) :
    Module.Injective (R ⧸ Ideal.span {a}) (R ⧸ Ideal.span {a}) :=
  (Module.Baer.quotient_span_singleton ha).injective
