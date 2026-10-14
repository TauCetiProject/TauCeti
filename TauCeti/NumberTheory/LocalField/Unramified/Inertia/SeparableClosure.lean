/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Basic
import Mathlib.FieldTheory.Galois.Infinite

/-!
# The inertia subgroup of the Galois group of the separable closure

Let `K` be a nonarchimedean local field. Its inertia subgroup `TauCeti.inertiaSubgroup K` is a
subgroup of `Gal(K^{alg}/K)`, the automorphisms of the algebraic closure fixing the maximal
unramified extension `K^{ur}` inside it. Galois cohomology is stated at the Galois group
`TauCeti.AbsoluteGaloisGroup K = Gal(Kˢ/K)` of the separable closure instead, and the two groups
are compared by restriction, `TauCeti.absoluteGaloisGroupRestrictEquiv K`.

This file identifies the image of inertia under that comparison: it is the subgroup of
`Gal(Kˢ/K)` fixing the maximal unramified extension of `K` inside `Kˢ`. Both subgroups are cut
out by the roots of the polynomials `X^{q^f} − X`, and these roots are separable over `K`, so
they lie in `Kˢ`. By infinite Galois theory, a finite subextension `E` of `Kˢ/K` is therefore
unramified exactly when inertia fixes it. This is the form in which unramifiedness of a field
cut out by a Galois module over `Kˢ`, such as the field of `m`-torsion points of an elliptic
curve, is read off the action of inertia on that module.

## Main results

* `TauCeti.map_inertiaSubgroup_absoluteGaloisGroupRestrictEquiv`: the image of `I_K` in
  `Gal(Kˢ/K)` is the fixing subgroup of the maximal unramified extension of `K` inside `Kˢ`.
* `TauCeti.map_inertiaSubgroup_le_fixingSubgroup_iff`: a finite subextension of `Kˢ/K` is
  unramified exactly when the image of `I_K` fixes it.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §5.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §9.
-/

public section

noncomputable section

open ValuativeRel IntermediateField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

variable (K) in
/-- **Inertia in the Galois group of the separable closure.** The image of the inertia subgroup
`I_K ≤ Gal(K^{alg}/K)` under restriction to the separable closure is the subgroup of
`Gal(Kˢ/K)` fixing the maximal unramified extension of `K` inside `Kˢ`. -/
@[simp]
theorem map_inertiaSubgroup_absoluteGaloisGroupRestrictEquiv :
    (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom =
      (maximalUnramifiedExtension K (SeparableClosure K)).fixingSubgroup := by
  ext τ
  obtain ⟨σ, rfl⟩ := (absoluteGaloisGroupRestrictEquiv K).surjective τ
  have hmem : absoluteGaloisGroupRestrictEquiv K σ ∈
      (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom ↔
        σ ∈ inertiaSubgroup K :=
    Subgroup.mem_map_iff_mem (absoluteGaloisGroupRestrictEquiv K).injective
  -- Both memberships say that the automorphism fixes the roots of the polynomials `X^{q^f} − X`.
  have hfix : absoluteGaloisGroupRestrictEquiv K σ ∈
      (maximalUnramifiedExtension K (SeparableClosure K)).fixingSubgroup ↔
        ∀ y : SeparableClosure K, ∀ f ≠ 0, y ^ Nat.card 𝓀[K] ^ f = y →
          absoluteGaloisGroupRestrictEquiv K σ y = y := by
    rw [IntermediateField.mem_fixingSubgroup_iff, maximalUnramifiedExtension_eq_adjoin]
    simp only [← AlgEquiv.smul_def, forall_mem_adjoin_smul_eq_self_iff, Set.mem_ofPred_eq]
    exact ⟨fun h y f hf hy ↦ h y ⟨f, hf, hy⟩, fun h y ⟨f, hf, hy⟩ ↦ h y f hf hy⟩
  rw [hmem, mem_inertiaSubgroup_iff_pow_natCard_pow_eq_self, hfix]
  refine ⟨fun h y f hf hy ↦ Subtype.ext ?_, fun h x f hf hx ↦ ?_⟩
  · -- Both automorphisms take the same value on `y`, computed in the algebraic closure.
    refine (coe_absoluteGaloisGroupRestrictEquiv_apply K σ y).trans (h y f hf ?_)
    simpa using congrArg (fun z : SeparableClosure K ↦ (z : AlgebraicClosure K)) hy
  · -- A root `x` of `X^{q^f} − X` lies in `K^{ur}`, which is separable, so `x ∈ Kˢ`.
    have hxM : x ∈ maximalUnramifiedExtension K (AlgebraicClosure K) := by
      rw [maximalUnramifiedExtension_eq_adjoin]
      exact subset_adjoin _ _ ⟨f, hf, hx⟩
    set y : SeparableClosure K := ⟨x, le_separableClosure K _ _ hxM⟩
    have hy := congrArg (fun z : SeparableClosure K ↦ (z : AlgebraicClosure K))
      (h y f hf (Subtype.ext (by simpa [y] using hx)))
    exact (coe_absoluteGaloisGroupRestrictEquiv_apply K σ y).symm.trans hy

/-- **Unramified subextensions of the separable closure are those fixed by inertia.** A
subextension `E` of `Kˢ/K`, with a structure of nonarchimedean local field compatible with `K`, is
unramified over `K` exactly when the image of the inertia subgroup in `Gal(Kˢ/K)` fixes it. -/
theorem map_inertiaSubgroup_le_fixingSubgroup_iff (E : IntermediateField K (SeparableClosure K))
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension K E] :
    (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom ≤
        E.fixingSubgroup ↔ IsUnramified K E := by
  rw [map_inertiaSubgroup_absoluteGaloisGroupRestrictEquiv, ← E.le_maximalUnramifiedExtension_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ fixingSubgroup_antitone h⟩
  -- Infinite Galois theory: an intermediate field of `Kˢ/K` is the fixed field of its fixing group.
  rw [← InfiniteGalois.fixedField_fixingSubgroup E,
    ← InfiniteGalois.fixedField_fixingSubgroup (maximalUnramifiedExtension K (SeparableClosure K))]
  exact fixedField_antitone h

end TauCeti
