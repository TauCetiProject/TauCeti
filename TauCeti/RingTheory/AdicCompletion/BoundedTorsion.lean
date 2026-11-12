/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Regular.IsSMulRegular
public import TauCeti.RingTheory.AdicCompletion.Exactness

/-!
# Principal-adic completion and bounded torsion obstructions

Completion for a principal ideal preserves an inclusion if the parameter-power torsion of
its cokernel is killed by a fixed power. Consequently, if the parameter acts injectively on
`range g` and its power torsion in `coker g` is bounded, completion preserves the kernel of a map
`g : M →ₗ[R] N`. No Noetherianity or finite generation is assumed.

For a complex `M → N → P`, regularity of the parameter on the second map's range identifies
parameter-power torsion in the cokernel of the first map with torsion in first cohomology.
Thus an annihilating power for first cohomology supplies the boundedness hypothesis. This
supplies the algebraic kernel step in comparing completed sections with compatible sections on
infinitesimal neighbourhoods via a Čech complex. The sheaf comparison and the separate
completeness of the section module are not asserted here.

## Main results

* `AdicCompletion.map_span_singleton_exact_of_annihilates_homology`: middle exactness after
  completion, with an annihilating power for the next cohomology group.
* `LinearMap.kerAdicCompletionEquiv`: the canonical comparison of the two kernels, with
  formulas for the comparison and its inverse under the kernel inclusion.

## References

* [Stacks Project, Lemma 52.12.7](https://stacks.math.columbia.edu/tag/0EII),
  the bounded-torsion argument in formal-section comparison.

The completion and its residue maps are Mathlib's construction of Judith Ludwig and
Christian Merten. The proofs use the existing principal-adic exactness theorem for a regular
last term.
-/

public section

open scoped Pointwise

namespace AdicCompletion

variable {R : Type*} [CommRing R] {r : R} {k : ℕ}
  {L M N P : Type*} [AddCommGroup L] [Module R L]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- An inclusion remains injective after principal-adic completion if the parameter-power
torsion of its cokernel is killed by a fixed power. No finiteness assumptions are needed. -/
theorem map_span_singleton_injective_of_bounded_torsion {f : M →ₗ[R] N}
    (hf : Function.Injective f)
    (hbound : ∀ x : N ⧸ f.range, (∃ n : ℕ, r ^ n • x = 0) → r ^ k • x = 0) :
    Function.Injective (map (Ideal.span {r}) f) := by
  have hfil (n : ℕ) (x : M)
      (hx : f x ∈ ((Ideal.span {r}) ^ (n + k) • ⊤ : Submodule R N)) :
      x ∈ ((Ideal.span {r}) ^ n • ⊤ : Submodule R M) := by
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hx ⊢
    obtain ⟨y, -, hy⟩ := hx
    have hq : r ^ k • (Submodule.Quotient.mk y : N ⧸ f.range) = 0 := by
      apply hbound _ ⟨n + k, ?_⟩
      rw [← Submodule.Quotient.mk_smul, hy, Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range_self f x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hq
    obtain ⟨z, hz⟩ := hq
    refine ⟨z, Submodule.mem_top, hf ?_⟩
    rw [map_smul, hz, smul_smul, ← pow_add, hy]
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  apply AdicCompletion.ext
  intro n
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x.val (n + k))
  have hfy : f y ∈ ((Ideal.span {r}) ^ (n + k) • ⊤ : Submodule R N) := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    have he := congrArg (fun z ↦ z.val (n + k)) hx
    simpa only [map_val_apply, ← hy, LinearMap.reduceModIdeal_apply, val_zero_apply] using he
  have he := x.property (Nat.le_add_right n k)
  -- Transition maps are quotient factor maps; evaluate them on the chosen representative.
  simp only [← hy, transitionMap, Submodule.factorPow, Submodule.factor,
    Submodule.mapQ_apply, LinearMap.id_apply] at he
  rw [← he, (Submodule.Quotient.mk_eq_zero _).mpr (hfil n y hfy), val_zero_apply]

/-- Completion preserves middle exactness when the parameter is regular on the last map's
range and the parameter-power torsion of its cokernel is bounded. The last map need not be
surjective, and the ambient target may have parameter-torsion outside the range. -/
theorem map_span_singleton_exact_of_bounded_torsion {f : L →ₗ[R] M} {g : M →ₗ[R] N}
    (hfg : Function.Exact f g) (hr : IsSMulRegular g.range r)
    (hbound : ∀ x : N ⧸ g.range, (∃ n : ℕ, r ^ n • x = 0) → r ^ k • x = 0) :
    Function.Exact (map (Ideal.span {r}) f) (map (Ideal.span {r}) g) := by
  have hi := map_span_singleton_injective_of_bounded_torsion
    (f := g.range.subtype) g.range.injective_subtype (k := k) (r := r) (by
      rw [Submodule.range_subtype]
      exact hbound)
  have he : Function.Exact f g.rangeRestrict :=
    (g.range.injective_subtype.comp_exact_iff_exact).mp
      (by simpa only [LinearMap.subtype_comp_rangeRestrict] using hfg)
  have hc := map_span_singleton_exact_of_isSMulRegular he g.surjective_rangeRestrict hr
  apply hi.comp_exact_iff_exact.mpr at hc
  simpa only [map_comp, LinearMap.subtype_comp_rangeRestrict] using hc

/-- In an exact sequence `L → M → N` extending to a complex `M → N → P`, completion
preserves exactness at `M` if the parameter is regular on `range g` and `range h` and a fixed
power kills `ker h / range g`. In a Čech complex the latter is the first-cohomology obstruction. -/
theorem map_span_singleton_exact_of_annihilates_homology
    {f : L →ₗ[R] M} {g : M →ₗ[R] N} {h : N →ₗ[R] P}
    (hfg : Function.Exact f g) (hgh : h ∘ₗ g = 0)
    (hr : IsSMulRegular g.range r) (hrP : IsSMulRegular h.range r)
    (hkill : ∀ y ∈ LinearMap.ker h, r ^ k • y ∈ g.range) :
    Function.Exact (map (Ideal.span {r}) f) (map (Ideal.span {r}) g) := by
  apply map_span_singleton_exact_of_bounded_torsion hfg hr (k := k)
  intro x hx
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨n, hn⟩ := hx
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hn ⊢
  apply hkill y
  apply (isSMulRegular_submodule_iff_right_eq_zero_of_smul h.range (r ^ n)).mp
    (hrP.pow n) (h y) (LinearMap.mem_range_self h y)
  obtain ⟨z, hz⟩ := hn
  rw [← map_smul, ← hz]
  exact LinearMap.congr_fun hgh z

end AdicCompletion

namespace LinearMap

variable {R : Type*} [CommRing R] {r : R} {k : ℕ}
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (g : M →ₗ[R] N) (hr : IsSMulRegular g.range r)
  (hbound : ∀ x : N ⧸ g.range, (∃ n : ℕ, r ^ n • x = 0) → r ^ k • x = 0)

/-- Completion of the kernel is the kernel of the completed map when the parameter is
regular on the range and its power torsion in the cokernel is bounded. The comparison is
induced by the original kernel inclusion, not by a choice of presentations. -/
noncomputable def kerAdicCompletionEquiv :
    AdicCompletion (Ideal.span {r}) g.ker ≃ₗ[AdicCompletion (Ideal.span {r}) R]
      (AdicCompletion.map (Ideal.span {r}) g).ker := by
  have he : Function.Exact g.ker.subtype g.rangeRestrict :=
    (g.range.injective_subtype.comp_exact_iff_exact).mp
      (by simpa only [subtype_comp_rangeRestrict] using g.exact_subtype_ker_map)
  have hi := AdicCompletion.map_span_singleton_injective_of_isSMulRegular
    g.ker.injective_subtype he hr
  have hc := AdicCompletion.map_span_singleton_exact_of_bounded_torsion
    g.exact_subtype_ker_map hr hbound
  exact LinearEquiv.ofBijective
    ((AdicCompletion.map (Ideal.span {r}) g.ker.subtype).codRestrict _
      fun x ↦ (hc _).mpr ⟨x, rfl⟩)
    ⟨fun x y h ↦ hi (congrArg Subtype.val h), fun y ↦ by
      obtain ⟨x, hx⟩ := (hc y).mp y.property
      exact ⟨x, Subtype.ext hx⟩⟩

/-- The kernel comparison followed by inclusion is the completion of the kernel inclusion. -/
@[simp]
theorem coe_kerAdicCompletionEquiv_apply (x : AdicCompletion (Ideal.span {r}) g.ker) :
    (g.kerAdicCompletionEquiv hr hbound x : AdicCompletion (Ideal.span {r}) M) =
      AdicCompletion.map (Ideal.span {r}) g.ker.subtype x :=
  (rfl)

/-- The inverse kernel comparison lifts a completed element of the kernel through the
completed kernel inclusion. -/
@[simp]
theorem map_subtype_kerAdicCompletionEquiv_symm
    (x : (AdicCompletion.map (Ideal.span {r}) g).ker) :
    AdicCompletion.map (Ideal.span {r}) g.ker.subtype
        ((g.kerAdicCompletionEquiv hr hbound).symm x) = x := by
  rw [← coe_kerAdicCompletionEquiv_apply g hr hbound, LinearEquiv.apply_symm_apply]

end LinearMap
