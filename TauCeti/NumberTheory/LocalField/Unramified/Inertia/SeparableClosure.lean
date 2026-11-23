/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Map
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Basic
public import TauCeti.NumberTheory.LocalField.Unramified.ZHat
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

We package this subgroup as `TauCeti.separableClosureInertiaSubgroup K`. Transporting
`Gal(K^{alg}/K) ⧸ I_K ≃ₜ* Gal(K^{ur}/K) ≃ₜ* zHat` along
`TauCeti.absoluteGaloisGroupRestrictEquiv K` identifies `Gal(Kˢ/K) ⧸ I_K` with `zHat`
(`TauCeti.quotientSeparableClosureInertiaSubgroupEquivZHat`), sending
`TauCeti.unramifiedQuotientFrobenius K` to `zHat.gen`.

For an extension `L/K` of nonarchimedean local fields, a `K`-embedding `τ : Kˢ → Lˢ` of separable
closures induces `TauCeti.absoluteGaloisGroupMap τ : Gal(Lˢ/L) → Gal(Kˢ/K)`, and this map sends
inertia into inertia: `τ` carries `K^{ur}` into `L^{ur}`, so an automorphism of `Lˢ` fixing `L^{ur}`
induces one of `Kˢ` fixing `K^{ur}`. This is what makes a Galois cohomology class of `K` vanishing
on inertia restrict to a class of `L` vanishing on inertia.

## Main definitions

* `TauCeti.separableClosureInertiaSubgroup`: the inertia subgroup of `AbsoluteGaloisGroup K`.
* `TauCeti.quotientSeparableClosureInertiaSubgroupEquivZHat`: the topological group isomorphism
  `Gal(Kˢ/K) ⧸ I_K ≃ₜ* zHat` sending arithmetic Frobenius to `zHat.gen`.
* `TauCeti.unramifiedQuotientFrobenius`: the arithmetic Frobenius element of `Gal(Kˢ/K) ⧸ I_K`.

## Main results

* `TauCeti.separableClosureInertiaSubgroup_eq_fixingSubgroup`: `separableClosureInertiaSubgroup K`
  is the fixing subgroup of the maximal unramified extension of `K` inside `Kˢ`.
* `TauCeti.isClosed_separableClosureInertiaSubgroup`,
  `TauCeti.separableClosureInertiaSubgroup_normal`: closedness and normality of inertia in
  `AbsoluteGaloisGroup K`.
* `TauCeti.separableClosureInertiaSubgroup_le_fixingSubgroup_iff`: a finite subextension of
  `Kˢ/K` is unramified exactly when `separableClosureInertiaSubgroup K` fixes it.
* `TauCeti.quotientSeparableClosureInertiaSubgroupEquivZHat_mk`,
  `TauCeti.unramifiedQuotientFrobenius_eq_mk_of_isArithFrobeniusLift`,
  `TauCeti.topologicalClosure_zpowers_unramifiedQuotientFrobenius`: restriction formula, Frobenius
  lifts, and topological generation of the unramified quotient.
* `AlgHom.map_absoluteGaloisGroupMap_separableClosureInertiaSubgroup_le`: for an extension `L/K` of
  local fields, the map `Gal(Lˢ/L) → Gal(Kˢ/K)` along an embedding of separable closures sends the
  inertia subgroup of `L` into that of `K`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §5.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §9.
-/

public section

noncomputable section

open ValuativeRel IntermediateField

namespace TauCeti

universe u

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

variable (K) in
/-- **The inertia subgroup of `AbsoluteGaloisGroup K`**: the image of `inertiaSubgroup K` under
restriction `absoluteGaloisGroupRestrictEquiv K : Gal(K^{alg}/K) ≃ₜ* Gal(Kˢ/K)`. -/
def separableClosureInertiaSubgroup : Subgroup (AbsoluteGaloisGroup K) :=
  (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom

variable (K) in
/-- `separableClosureInertiaSubgroup K` is the image of `inertiaSubgroup K` under
`absoluteGaloisGroupRestrictEquiv K`. -/
theorem separableClosureInertiaSubgroup_def :
    separableClosureInertiaSubgroup K =
      (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom :=
  (rfl)

/-- An automorphism of `K^{alg}` restricts into `separableClosureInertiaSubgroup K` if and only if
it lies in `inertiaSubgroup K`. -/
theorem absoluteGaloisGroupRestrictEquiv_mem_separableClosureInertiaSubgroup_iff
    {σ : Field.absoluteGaloisGroup K} :
    absoluteGaloisGroupRestrictEquiv K σ ∈ separableClosureInertiaSubgroup K ↔
      σ ∈ inertiaSubgroup K := by
  rw [separableClosureInertiaSubgroup_def]
  exact Subgroup.mem_map_iff_mem (absoluteGaloisGroupRestrictEquiv K).injective

variable (K) in
/-- **Inertia in the Galois group of the separable closure.** `separableClosureInertiaSubgroup K`
is the subgroup of `Gal(Kˢ/K)` fixing the maximal unramified extension of `K` inside `Kˢ`. -/
theorem separableClosureInertiaSubgroup_eq_fixingSubgroup :
    separableClosureInertiaSubgroup K =
      (maximalUnramifiedExtension K (SeparableClosure K)).fixingSubgroup := by
  ext τ
  obtain ⟨σ, rfl⟩ := (absoluteGaloisGroupRestrictEquiv K).surjective τ
  -- Both memberships say that the automorphism fixes the roots of the polynomials `X^{q^f} − X`.
  have hfix : absoluteGaloisGroupRestrictEquiv K σ ∈
      (maximalUnramifiedExtension K (SeparableClosure K)).fixingSubgroup ↔
        ∀ y : SeparableClosure K, ∀ f ≠ 0, y ^ Nat.card 𝓀[K] ^ f = y →
          absoluteGaloisGroupRestrictEquiv K σ y = y := by
    rw [IntermediateField.mem_fixingSubgroup_iff, maximalUnramifiedExtension_eq_adjoin]
    simp only [← AlgEquiv.smul_def, forall_mem_adjoin_smul_eq_self_iff, Set.mem_ofPred_eq]
    exact ⟨fun h y f hf hy ↦ h y ⟨f, hf, hy⟩, fun h y ⟨f, hf, hy⟩ ↦ h y f hf hy⟩
  rw [absoluteGaloisGroupRestrictEquiv_mem_separableClosureInertiaSubgroup_iff,
    mem_inertiaSubgroup_iff_pow_natCard_pow_eq_self, hfix]
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

/-- An automorphism of `Kˢ/K` lies in `separableClosureInertiaSubgroup K` if and only if it fixes
every element of the maximal unramified extension of `K` inside `Kˢ`. -/
@[simp]
theorem mem_separableClosureInertiaSubgroup_iff {τ : AbsoluteGaloisGroup K} :
    τ ∈ separableClosureInertiaSubgroup K ↔
      ∀ x ∈ maximalUnramifiedExtension K (SeparableClosure K), τ x = x := by
  rw [separableClosureInertiaSubgroup_eq_fixingSubgroup, IntermediateField.mem_fixingSubgroup_iff]

variable (K) in
/-- **Inertia in `AbsoluteGaloisGroup K` is closed** in the Krull topology. -/
theorem isClosed_separableClosureInertiaSubgroup :
    IsClosed (separableClosureInertiaSubgroup K : Set (AbsoluteGaloisGroup K)) := by
  rw [separableClosureInertiaSubgroup_def, Subgroup.coe_map]
  exact (absoluteGaloisGroupRestrictEquiv K).toHomeomorph.isClosed_image.mpr
    (isClosed_inertiaSubgroup K)

variable (K) in
/-- **Inertia in `AbsoluteGaloisGroup K` is normal**, as the image of `inertiaSubgroup K` under the
surjective isomorphism `absoluteGaloisGroupRestrictEquiv K`. -/
instance separableClosureInertiaSubgroup_normal : (separableClosureInertiaSubgroup K).Normal := by
  rw [separableClosureInertiaSubgroup_def]
  exact Subgroup.Normal.map (inertiaSubgroup_normal K) _
    (absoluteGaloisGroupRestrictEquiv K).surjective

/-- **Unramified subextensions of the separable closure are those fixed by inertia.** A
subextension `E` of `Kˢ/K`, with a structure of nonarchimedean local field compatible with `K`, is
unramified over `K` exactly when `separableClosureInertiaSubgroup K` fixes it. -/
theorem separableClosureInertiaSubgroup_le_fixingSubgroup_iff
    (E : IntermediateField K (SeparableClosure K))
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension K E] :
    separableClosureInertiaSubgroup K ≤ E.fixingSubgroup ↔ IsUnramified K E := by
  rw [separableClosureInertiaSubgroup_eq_fixingSubgroup, ← E.le_maximalUnramifiedExtension_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ fixingSubgroup_antitone h⟩
  -- Infinite Galois theory: an intermediate field of `Kˢ/K` is the fixed field of its fixing group.
  rw [← InfiniteGalois.fixedField_fixingSubgroup E,
    ← InfiniteGalois.fixedField_fixingSubgroup (maximalUnramifiedExtension K (SeparableClosure K))]
  exact fixedField_antitone h

section QuotientZHat

variable (K)

/-- **The unramified quotient of `AbsoluteGaloisGroup K` is `zHat`.** Transporting from
`Field.absoluteGaloisGroup K ⧸ inertiaSubgroup K` through `TauCeti.quotientInertiaSubgroupEquiv`
and `TauCeti.maximalUnramifiedGaloisGroupEquivZHat` sends arithmetic Frobenius lifts to
`zHat.gen`. -/
def quotientSeparableClosureInertiaSubgroupEquivZHat :
    (AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K) ≃ₜ* zHat.{u} :=
  ((absoluteGaloisGroupRestrictEquiv K).quotientCongr (inertiaSubgroup K)
      (separableClosureInertiaSubgroup K) (separableClosureInertiaSubgroup_def K).symm).symm.trans
    ((quotientInertiaSubgroupEquiv K).trans
      (maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)))

/-- `quotientSeparableClosureInertiaSubgroupEquivZHat K` evaluates on the coset of `τ` via
`(absoluteGaloisGroupRestrictEquiv K).symm`, restriction to the maximal unramified extension, and
`maximalUnramifiedGaloisGroupEquivZHat`. -/
@[simp]
theorem quotientSeparableClosureInertiaSubgroupEquivZHat_mk (τ : AbsoluteGaloisGroup K) :
    quotientSeparableClosureInertiaSubgroupEquivZHat K
        (τ : AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K) =
      maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)
        (restrictMaximalUnramifiedHom K ((absoluteGaloisGroupRestrictEquiv K).symm τ)) := by
  rw [quotientSeparableClosureInertiaSubgroupEquivZHat, ContinuousMulEquiv.trans_apply,
    ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.quotientCongr_symm_mk,
    ← unramifiedDegree_apply, quotientInertiaSubgroupEquiv_unramifiedDegree]

variable {K} in
/-- **An arithmetic Frobenius lift maps to `zHat.gen` in the unramified quotient.** -/
theorem quotientSeparableClosureInertiaSubgroupEquivZHat_mk_of_isArithFrobeniusLift
    {σ : Field.absoluteGaloisGroup K} (hσ : IsArithFrobeniusLift K σ) :
    quotientSeparableClosureInertiaSubgroupEquivZHat K
        (absoluteGaloisGroupRestrictEquiv K σ :
          AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K) =
      zHat.gen := by
  rw [quotientSeparableClosureInertiaSubgroupEquivZHat_mk, ContinuousMulEquiv.symm_apply_apply,
    isArithFrobeniusLift_def.mp hσ, maximalUnramifiedGaloisGroupEquivZHat_apply_frobenius]

/-- **The arithmetic Frobenius element of the unramified quotient** of `AbsoluteGaloisGroup K`,
corresponding to `zHat.gen` under `quotientSeparableClosureInertiaSubgroupEquivZHat K`. -/
def unramifiedQuotientFrobenius : AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K :=
  (quotientSeparableClosureInertiaSubgroupEquivZHat K).symm zHat.gen

/-- `unramifiedQuotientFrobenius K` is the preimage of `zHat.gen` under
`quotientSeparableClosureInertiaSubgroupEquivZHat K`. -/
theorem unramifiedQuotientFrobenius_def :
    unramifiedQuotientFrobenius K =
      (quotientSeparableClosureInertiaSubgroupEquivZHat K).symm zHat.gen :=
  (rfl)

/-- The inverse of `quotientSeparableClosureInertiaSubgroupEquivZHat K` sends `zHat.gen` to
`unramifiedQuotientFrobenius K`. -/
@[simp]
theorem quotientSeparableClosureInertiaSubgroupEquivZHat_symm_gen :
    (quotientSeparableClosureInertiaSubgroupEquivZHat K).symm zHat.gen =
      unramifiedQuotientFrobenius K :=
  (rfl)

/-- `quotientSeparableClosureInertiaSubgroupEquivZHat K` sends `unramifiedQuotientFrobenius K` to
`zHat.gen`. -/
@[simp]
theorem quotientSeparableClosureInertiaSubgroupEquivZHat_unramifiedQuotientFrobenius :
    quotientSeparableClosureInertiaSubgroupEquivZHat K (unramifiedQuotientFrobenius K) =
      zHat.gen :=
  (quotientSeparableClosureInertiaSubgroupEquivZHat K).apply_symm_apply zHat.gen

variable {K} in
/-- `unramifiedQuotientFrobenius K` is the coset of the restriction to `Kˢ` of any arithmetic
Frobenius lift. -/
theorem unramifiedQuotientFrobenius_eq_mk_of_isArithFrobeniusLift {σ : Field.absoluteGaloisGroup K}
    (hσ : IsArithFrobeniusLift K σ) :
    unramifiedQuotientFrobenius K =
      (absoluteGaloisGroupRestrictEquiv K σ :
        AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K) := by
  apply (quotientSeparableClosureInertiaSubgroupEquivZHat K).injective
  rw [quotientSeparableClosureInertiaSubgroupEquivZHat_unramifiedQuotientFrobenius,
    quotientSeparableClosureInertiaSubgroupEquivZHat_mk_of_isArithFrobeniusLift hσ]

/-- **Arithmetic Frobenius topologically generates the unramified quotient** of
`AbsoluteGaloisGroup K`. -/
theorem topologicalClosure_zpowers_unramifiedQuotientFrobenius :
    (Subgroup.zpowers (unramifiedQuotientFrobenius K)).topologicalClosure = ⊤ := by
  let e := quotientSeparableClosureInertiaSubgroupEquivZHat K
  have hmap : (Subgroup.zpowers zHat.gen).map e.symm.toMonoidHom =
      Subgroup.zpowers (unramifiedQuotientFrobenius K) := by
    rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers (quotientSeparableClosureInertiaSubgroupEquivZHat_symm_gen K)
  have hcoe : (e.symm.toMonoidHom : zHat.{u} → _) = e.symm.toHomeomorph := rfl
  rw [← hmap, ← SetLike.coe_set_eq, Subgroup.topologicalClosure_coe, Subgroup.coe_map,
    Subgroup.coe_top, hcoe, ← e.symm.toHomeomorph.image_closure, ← Subgroup.topologicalClosure_coe,
    zHat.topologicalClosure_zpowers_gen, Subgroup.coe_top, Set.image_univ,
    e.symm.toHomeomorph.surjective.range_eq]

end QuotientZHat

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- **Inertia along an extension of local fields.** For an extension `L/K` of nonarchimedean local
fields and a `K`-embedding `τ : Kˢ → Lˢ` of separable closures, the induced map
`Gal(Lˢ/L) → Gal(Kˢ/K)` sends the inertia subgroup of `L` into that of `K`. -/
theorem _root_.AlgHom.map_absoluteGaloisGroupMap_separableClosureInertiaSubgroup_le
    (τ : SeparableClosure K →ₐ[K] SeparableClosure L) :
    (separableClosureInertiaSubgroup L).map
        (absoluteGaloisGroupMap τ : AbsoluteGaloisGroup L →* AbsoluteGaloisGroup K) ≤
      separableClosureInertiaSubgroup K := by
  rw [separableClosureInertiaSubgroup_eq_fixingSubgroup,
    separableClosureInertiaSubgroup_eq_fixingSubgroup]
  rintro _ ⟨g, hg, rfl⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hg
  rw [IntermediateField.mem_fixingSubgroup_iff]
  -- `τ` carries `K^{ur}` into `L^{ur}`, which `g` fixes.
  exact fun x hx ↦ τ.injective ((absoluteGaloisGroupMap_commutes τ g x).trans
    (hg _ (τ.map_maximalUnramifiedExtension_le ⟨x, hx, rfl⟩)))

end TauCeti
