/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Span

/-!
# Injective modules over principal ideal rings

If multiplication by each nonzero scalar is surjective on a module over a principal ideal ring,
the module satisfies Baer's criterion and is injective.

A division algebra faithfully containing the scalar ring has this divisibility property, as does
its quotient by any submodule. In particular, `ℚ_p / ℤ_p` is injective over `ℤ_p`. Thus a
`ℚ_p / ℤ_p`-valued character of a torsion submodule extends to the whole module, without a splitting
or finite-generation assumption. This is the extension property used in torsion duality.

## Main results

* `Module.Baer.of_surjective_smul`: scalar divisibility implies Baer's criterion.
* `Submodule.injective_quotient_of_divisionRing`: quotients of a faithful division algebra are
  injective over a principal ideal ring.
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
