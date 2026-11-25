/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.OfMulAction

/-!
# Change of coefficients for invariants of permutation representations

Let a group `I` act on a set `X`. Over a commutative ring `k`, the invariants of the permutation
representation `k[X]` are free on the finite orbits, the basis vector at a finite orbit being the
sum of its points (`TauCeti.invariantFiniteOrbitSumBasis`): an invariant vector has coefficients
constant along orbits, so it vanishes on the infinite ones. This extends
`TauCeti.invariantOrbitSumBasis`, which asks `X` itself to be finite.

As a consequence, for every commutative `k`-algebra `B`, flat or not, the comparison map
`B ⊗_k k[X]^I → (B ⊗_k k[X])^I` (`Representation.invariantsBaseChangeMap`) is bijective
(`Representation.invariantsBaseChangeMap_ofMulAction_bijective`): after identifying
`B ⊗_k k[X]` with `B[X]` (`TauCeti.baseChangeOfMulActionEquiv`), it sends the base change of the
orbit-sum basis over `k` to the orbit-sum basis over `B`. For a compact open subgroup acting on the
cosets of an open subgroup this is the permutation-module Check of the change of coefficients for
smooth representations.

## Main results

* `TauCeti.coeff_eq_zero_of_mem_invariants_of_infinite`: an invariant vector of `k[X]` vanishes
  on the infinite orbits.
* `TauCeti.invariantFiniteOrbitSumBasis`: the orbit-sum basis of the invariants of `k[X]`, indexed
  by the finite orbits.
* `TauCeti.coeff_invariantFiniteOrbitSumBasis_repr_symm`: the invariant vector with orbit
  coordinates `c` has coefficient `c ⟦x⟧` at a point `x` with finite orbit.
* `TauCeti.coeff_invariantFiniteOrbitSumBasis`: the basis vector at a finite orbit is the
  indicator function of the orbit.
* `TauCeti.baseChangeOfMulActionEquiv_one_tmul_coeff`: the identification `B ⊗_k k[X] ≅ B[X]`
  maps `1 ⊗ v` to `v` with its coefficients mapped to `B`.
* `Representation.invariantsBaseChangeMap_ofMulAction_bijective`: for any commutative
  `k`-algebra `B`, `B ⊗_k k[X]^I → (B ⊗_k k[X])^I` is bijective.
-/

public section

open MonoidAlgebra MulAction Representation TensorProduct

namespace TauCeti

section FiniteOrbits

variable (k : Type*) {I X : Type*} [CommRing k] [Group I] [MulAction I X]

/-- An invariant vector of `k[X]` vanishes on every infinite orbit: its coefficients are constant
along orbits and finitely supported. -/
theorem coeff_eq_zero_of_mem_invariants_of_infinite {v : k[X]}
    (hv : v ∈ (ofMulAction k I X).invariants) {x : X} (hx : (orbit I x).Infinite) :
    v.coeff x = 0 := by
  by_contra h
  refine hx (v.coeff.support.finite_toSet.subset ?_)
  rintro _ ⟨g, rfl⟩
  exact Finsupp.mem_support_iff.2 ((coeff_smul_of_forall_ofMulAction_eq hv g x).symm ▸ h)

open Classical in
/-- The coefficient at the orbit `ω` of a finitely supported function on the finite orbits:
zero if `ω` is infinite. -/
private noncomputable def finiteOrbitCoeff
    (c : {ω : orbitRel.Quotient I X // ω.orbit.Finite} →₀ k) (ω : orbitRel.Quotient I X) : k :=
  if h : ω.orbit.Finite then c ⟨ω, h⟩ else 0

private theorem finiteOrbitCoeff_of_finite
    (c : {ω : orbitRel.Quotient I X // ω.orbit.Finite} →₀ k) {ω : orbitRel.Quotient I X}
    (h : ω.orbit.Finite) : finiteOrbitCoeff k c ω = c ⟨ω, h⟩ := by
  simp [finiteOrbitCoeff, h]

private theorem finiteOrbitCoeff_of_infinite
    (c : {ω : orbitRel.Quotient I X // ω.orbit.Finite} →₀ k) {ω : orbitRel.Quotient I X}
    (h : ¬ω.orbit.Finite) : finiteOrbitCoeff k c ω = 0 := by
  simp [finiteOrbitCoeff, h]

variable (I X) in
/-- The coefficients of an invariant vector of `k[X]`, as a finitely supported function on the
finite orbits; the inverse sends such a function to the vector with that coefficient at each point
of the corresponding orbit, and zero on the infinite orbits. -/
private noncomputable def invariantsFiniteOrbitEquiv :
    (ofMulAction k I X).invariants ≃ₗ[k] ({ω : orbitRel.Quotient I X // ω.orbit.Finite} →₀ k) where
  toFun v := Finsupp.ofSupportFinite
    (fun ω ↦ Quotient.liftOn' ω.val (v : k[X]).coeff fun _ _ ⟨g, hg⟩ ↦ by
      rw [← hg]
      exact coeff_smul_of_forall_ofMulAction_eq v.property g _)
    ((((v : k[X]).coeff.support.finite_toSet.image (Quotient.mk (orbitRel I X))).preimage
      Subtype.val_injective.injOn).subset fun ⟨ω, _⟩ hω ↦ by
        induction ω using Quotient.inductionOn' with
        | h x => exact ⟨x, Finsupp.mem_support_iff.2 hω, rfl⟩)
  map_add' v w := Finsupp.ext fun ⟨ω, _⟩ ↦ by
    induction ω using Quotient.inductionOn' with
    | h x => simp [Finsupp.ofSupportFinite_coe, Quotient.liftOn'_mk'']
  map_smul' r v := Finsupp.ext fun ⟨ω, _⟩ ↦ by
    induction ω using Quotient.inductionOn' with
    | h x => simp [Finsupp.ofSupportFinite_coe, Quotient.liftOn'_mk'']
  invFun c := ⟨ofCoeff (Finsupp.ofSupportFinite (fun x ↦ finiteOrbitCoeff k c ⟦x⟧)
      (((c.support.finite_toSet.image Subtype.val).preimage' fun ω ⟨ω', _, hω'⟩ ↦ by
        subst hω'
        exact ω'.property.subset fun _ hx ↦ orbitRel.Quotient.mem_orbit.2 hx).subset fun x hx ↦ by
        by_cases h : (orbit I x).Finite
        · rw [Function.mem_support, finiteOrbitCoeff_of_finite k c (ω := ⟦x⟧) h] at hx
          exact ⟨⟨⟦x⟧, h⟩, Finsupp.mem_support_iff.2 hx, rfl⟩
        · exact absurd (finiteOrbitCoeff_of_infinite k c (ω := ⟦x⟧) h) hx)),
    (mem_invariants_ofMulAction_iff).2 fun g x ↦ by
      simp only [Finsupp.ofSupportFinite_coe]
      exact congrArg _ (Quotient.sound (mem_orbit x g))⟩
  left_inv v := Subtype.ext <| by
    ext x
    simp only [Finsupp.ofSupportFinite_coe]
    by_cases h : (orbit I x).Finite
    · exact finiteOrbitCoeff_of_finite k _ (ω := ⟦x⟧) h
    · exact (finiteOrbitCoeff_of_infinite k _ (ω := ⟦x⟧) h).trans
        (coeff_eq_zero_of_mem_invariants_of_infinite k v.property h).symm
  right_inv c := Finsupp.ext fun ⟨ω, hω⟩ ↦ by
    induction ω using Quotient.inductionOn' with
    | h x => exact finiteOrbitCoeff_of_finite k c hω

variable (I X) in
/-- **The orbit-sum basis.** For a group `I` acting on a set `X`, the invariants of the permutation
representation `k[X]` are free on the finite orbits: the basis vector at a finite orbit `ω` is the
orbit sum `∑ x ∈ ω, x` (`TauCeti.coeff_invariantFiniteOrbitSumBasis`). -/
noncomputable def invariantFiniteOrbitSumBasis :
    Module.Basis {ω : orbitRel.Quotient I X // ω.orbit.Finite} k (ofMulAction k I X).invariants :=
  .ofRepr (invariantsFiniteOrbitEquiv k I X)

variable {k}

/-- The coordinate of an invariant vector at the finite orbit of `x` is its coefficient at `x`. -/
@[simp]
theorem invariantFiniteOrbitSumBasis_repr_mk (v : (ofMulAction k I X).invariants) {x : X}
    (hx : (orbit I x).Finite) :
    (invariantFiniteOrbitSumBasis k I X).repr v ⟨⟦x⟧, hx⟩ = (v : k[X]).coeff x := by
  simp [invariantFiniteOrbitSumBasis, invariantsFiniteOrbitEquiv, Finsupp.ofSupportFinite_coe,
    Quotient.liftOn'_mk'']

/-- The invariant vector with coordinates `c` in the orbit-sum basis has coefficient `c ⟦x⟧` at
a point `x` with finite orbit. -/
theorem coeff_invariantFiniteOrbitSumBasis_repr_symm
    (c : {ω : orbitRel.Quotient I X // ω.orbit.Finite} →₀ k) {x : X} (hx : (orbit I x).Finite) :
    (((invariantFiniteOrbitSumBasis k I X).repr.symm c : _) : k[X]).coeff x = c ⟨⟦x⟧, hx⟩ := by
  rw [← invariantFiniteOrbitSumBasis_repr_mk _ hx, LinearEquiv.apply_symm_apply]

/-- The basis vector at a finite orbit `ω` is the indicator function of `ω`. -/
@[simp]
theorem coeff_invariantFiniteOrbitSumBasis (ω : {ω : orbitRel.Quotient I X // ω.orbit.Finite})
    (x : X) :
    (invariantFiniteOrbitSumBasis k I X ω : k[X]).coeff x = ω.val.orbit.indicator 1 x := by
  classical
  by_cases hx : (orbit I x).Finite
  · rw [← Module.Basis.repr_symm_single_one, coeff_invariantFiniteOrbitSumBasis_repr_symm _ hx]
    obtain ⟨ω, hω⟩ := ω
    simp [Set.indicator_apply, Finsupp.single_apply, orbitRel.Quotient.mem_orbit, eq_comm,
      Subtype.ext_iff]
  · rw [coeff_eq_zero_of_mem_invariants_of_infinite k (Subtype.property _) hx,
      Set.indicator_of_notMem]
    intro hxω
    rw [orbitRel.Quotient.mem_orbit] at hxω
    exact hx (by simpa [← hxω] using ω.property)

end FiniteOrbits

/-- The identification `B ⊗_k k[X] ≅ B[X]` maps `1 ⊗ v` to `v` with its coefficients mapped to
`B`. -/
theorem baseChangeOfMulActionEquiv_one_tmul_coeff {k B G X : Type*} [CommSemiring k]
    [Semiring B] [Algebra k B] [Monoid G] [MulAction G X] (v : k[X]) (x : X) :
    (baseChangeOfMulActionEquiv k B G X (1 ⊗ₜ v)).coeff x = algebraMap k B (v.coeff x) := by
  classical
  induction v using MonoidAlgebra.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [tmul_add, map_add, coeff_add, Finsupp.add_apply, hv, hw]
  | single y r =>
    rw [baseChangeOfMulActionEquiv_tmul_single, coeff_single, coeff_single,
      Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp [Algebra.smul_def]

end TauCeti

namespace Representation

open TauCeti

variable {k B I X : Type*} [CommRing k] [CommRing B] [Algebra k B] [Group I] [MulAction I X]

/-- **Change of coefficients commutes with the invariants of a permutation representation.**
For a group `I` acting on a set `X` and any commutative `k`-algebra `B`, flat or not, the
comparison map `B ⊗_k k[X]^I → (B ⊗_k k[X])^I` is bijective: both sides are free on the finite
orbits, and the map matches the orbit sums. -/
theorem invariantsBaseChangeMap_ofMulAction_bijective :
    Function.Bijective (invariantsBaseChangeMap (A := B) (ofMulAction k I X)) := by
  let e := baseChangeOfMulActionEquiv k B I X
  let β := (invariantFiniteOrbitSumBasis k I X).baseChange B
  let γ := invariantFiniteOrbitSumBasis B I X
  -- After `e`, the comparison map is the identification of the two orbit-sum bases.
  have hF : (e.toLinearMap ∘ₗ (baseChange B (ofMulAction k I X)).invariants.subtype) ∘ₗ
      invariantsBaseChangeMap (ofMulAction k I X) =
        (ofMulAction B I X).invariants.subtype ∘ₗ
          (β.equiv γ (_root_.Equiv.refl _)).toLinearMap := by
    refine β.ext fun ω ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      Module.Basis.equiv_apply, _root_.Equiv.refl_apply]
    ext x
    simp only [β, γ, Module.Basis.baseChange_apply, Submodule.coe_subtype,
      coe_invariantsBaseChangeMap_tmul, Representation.IntertwiningMap.toLinearMap_apply,
      Representation.Equiv.coe_toIntertwiningMap]
    rw [baseChangeOfMulActionEquiv_one_tmul_coeff,
      coeff_invariantFiniteOrbitSumBasis, coeff_invariantFiniteOrbitSumBasis]
    by_cases hx : x ∈ ω.val.orbit <;> simp [hx]
  have hFx (y) : e (invariantsBaseChangeMap (ofMulAction k I X) y : B ⊗[k] k[X]) =
      β.equiv γ (_root_.Equiv.refl _) y := LinearMap.congr_fun hF y
  refine ⟨fun y z h ↦ (β.equiv γ (_root_.Equiv.refl _)).injective (Subtype.ext ?_), fun y ↦ ?_⟩
  · rw [← hFx, ← hFx, h]
  · -- `e y` is invariant, since `e` is equivariant.
    have hy : e y ∈ (ofMulAction B I X).invariants := (mem_invariants _ _).2 fun g ↦ by
      have h := IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g y
      rw [Representation.Equiv.coe_toIntertwiningMap] at h
      rw [← h, (mem_invariants _ _).1 y.property g]
    refine ⟨(β.equiv γ (_root_.Equiv.refl _)).symm ⟨_, hy⟩, Subtype.ext ?_⟩
    have h := hFx ((β.equiv γ (_root_.Equiv.refl _)).symm ⟨_, hy⟩)
    rw [LinearEquiv.apply_symm_apply] at h
    simpa [Representation.Equiv.symm_apply_apply] using congrArg e.symm h

end Representation
