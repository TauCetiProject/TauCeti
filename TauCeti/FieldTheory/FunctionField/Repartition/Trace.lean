/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Trace.Basic
public import TauCeti.FieldTheory.FunctionField.Different.Complementary
public import TauCeti.FieldTheory.FunctionField.Different.Divisor
public import TauCeti.FieldTheory.FunctionField.Divisor.Conorm
public import TauCeti.FieldTheory.FunctionField.Repartition.Basic

/-!
# The trace of repartitions along an extension of function fields

Let `F' / k'` be a finite extension of the algebraic function field `F / k`.  Stichtenoth builds
the cotrace of Weil differentials (Section III.4) from the repartitions of `F'` that are
**constant on the fibres** of the restriction map, that is, whose entries at two places
`P', Q'` of `F'` agree whenever `P'` and `Q'` lie over the same place of `F`.  Such a repartition
is a family indexed by the places of `F` itself, and its trace is taken entrywise:

`(Tr α)_P = Tr_{F'/F} (α_P)`.

This file sets up that construction.  The **relative repartitions** are the families
`β : Place k F → F'` whose entries are integral over `𝒪_P` at almost every place `P`; they are
exactly the families whose pullback `P' ↦ β (P'.restrict k F)` is a repartition of `F' / k'`
(`TauCeti.comp_restrict_mem_repartitionSpace_iff`), so they are Stichtenoth's fibre-constant
repartitions, with the entries read at the places of `F`.  The entrywise trace carries them to
repartitions of `F / k`, and the main theorem is the estimate that makes the divisor of the
cotrace computable:

`β ∘ restrict ∈ A_{F'}(Con D + Diff(F'/F)) → Tr β ∈ A_F(D)`,

obtained place by place from the valuation criterion for the complementary module,
`TauCeti.Place.valuation_trace_le_exp`.  The trace is compatible with the diagonal embeddings and
with multiplication by functions of `F`.

## Main definitions

* `TauCeti.relativeRepartitionSpace`: the relative repartitions of `F' / F`.
* `TauCeti.repartitionTrace`: the entrywise trace `Tr_{F'/F}`, a `k`-linear map from the relative
  repartitions to `A_F`.

## Main results

* `TauCeti.comp_restrict_mem_repartitionSpace` and
  `TauCeti.comp_restrict_mem_repartitionSpace_iff`: the pullback of a relative repartition is a
  repartition of `F' / k'`, and every fibre-constant repartition arises this way.
* `TauCeti.repartitionTrace_mem_adeleFiltration`: **the trace estimate**
  `Tr (A_{F'/F} ∩ A_{F'}(Con D + Diff(F'/F))) ⊆ A_F(D)`.
* `TauCeti.repartitionTrace_const` and `TauCeti.repartitionTrace_smul`: the trace of a diagonal
  repartition is diagonal, and the trace is `F`-linear.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.4, Definition 3.4.5 and the proof of Theorem 3.4.6.
-/

public section

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

attribute [local instance 10] Place.algebraIntegersExtension Place.isScalarTowerIntegersExtension

/-! ### Relative repartitions -/

section Relative

omit [Algebra k k'] [Algebra k' F'] [IsScalarTower k k' F']

variable (k F F') in
/-- The **relative repartitions** of `F' / F`: the families `β : Place k F → F'` whose entry at
`P` is integral over the valuation ring `𝒪_P` for all but finitely many places `P` of `F / k`.

Pulled back along the restriction of places, these are the repartitions of `F'` that are
constant on the fibres over the places of `F`, the space written `A_{F'/F}` by Stichtenoth
(Section III.4); see `TauCeti.comp_restrict_mem_repartitionSpace_iff`. -/
noncomputable def relativeRepartitionSpace : Submodule k (Place k F → F') where
  carrier := {β | ∀ᶠ (P : Place k F) in Filter.cofinite, IsIntegral P.integers (β P)}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    exact (ha.and hb).mono fun _ h ↦ by simpa using h.1.add h.2
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    exact Filter.Eventually.of_forall fun _ ↦ by simpa using isIntegral_zero
  smul_mem' c a ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    refine ha.mono fun P h ↦ ?_
    rw [Pi.smul_apply, Algebra.smul_def, IsScalarTower.algebraMap_apply k F F']
    exact (isIntegral_algebraMap (x := (⟨_, P.algebraMap_mem_integers c⟩ : P.integers))).mul h

/-- Membership in the relative repartitions, unfolded. -/
@[simp]
theorem mem_relativeRepartitionSpace_iff {β : Place k F → F'} :
    β ∈ relativeRepartitionSpace k F F' ↔
      ∀ᶠ (P : Place k F) in Filter.cofinite, IsIntegral P.integers (β P) :=
  (Iff.rfl)

/-- The relative repartitions are stable under multiplication by a function of `F`, which has
only finitely many poles. -/
theorem smul_mem_relativeRepartitionSpace (hF : IsFunctionField k F) (f : F)
    {β : Place k F → F'} (hβ : β ∈ relativeRepartitionSpace k F F') :
    f • β ∈ relativeRepartitionSpace k F F' := by
  have hf := (mem_repartitionSpace_iff_integers.mp (const_mem_repartitionSpace hF f))
  refine (hf.and hβ).mono fun P h ↦ ?_
  rw [Pi.smul_apply, Algebra.smul_def]
  exact (isIntegral_algebraMap (x := (⟨f, h.1⟩ : P.integers))).mul h.2

/-- The constant families are relative repartitions: a function of `F'`, which is integral over
`F`, is integral over `𝒪_P` at almost every place `P`. -/
theorem const_mem_relativeRepartitionSpace [Algebra.IsIntegral F F'] (hF : IsFunctionField k F)
    (x : F') : Function.const (Place k F) x ∈ relativeRepartitionSpace k F F' :=
  Filter.eventually_cofinite.mpr
    (Place.finite_setOf_not_isIntegral hF x (Algebra.IsIntegral.isIntegral x))

end Relative

/-! ### Pulling relative repartitions back to `F'` -/

section Pullback

variable [FiniteDimensional F F']

/-- **The pullback of a relative repartition is a repartition of `F' / k'`**: at a place `P'`
over a place `P` at which `β P` is integral over `𝒪_P`, the entry `β P` is regular at `P'`, and
only finitely many places lie over the finitely many exceptional `P`. -/
theorem comp_restrict_mem_repartitionSpace {β : Place k F → F'}
    (hβ : β ∈ relativeRepartitionSpace k F F') :
    (fun P' : Place k' F' ↦ β (P'.restrict k F)) ∈ repartitionSpace k' F' := by
  rw [mem_repartitionSpace_iff_finite]
  have hbad : {P : Place k F | ¬ IsIntegral P.integers (β P)}.Finite :=
    Filter.eventually_cofinite.mp hβ
  refine (hbad.biUnion fun P _ ↦ Place.finite_setOf_restrict_eq (k' := k') (F' := F') k F P).subset
    fun P' hP' ↦ Set.mem_iUnion₂.mpr ⟨P'.restrict k F, fun hint ↦ hP' ?_, rfl⟩
  refine P'.mem_integers_iff.mp (P'.mem_integers_of_isIntegral (fun a ↦ ?_) hint)
  exact (Place.mem_integers_restrict_iff k F P' (a : F)).mp a.2

/-- **The relative repartitions are the fibre-constant repartitions of `F'`**: a family indexed by
the places of `F` is a relative repartition exactly when its pullback to the places of `F'` is a
repartition.  The converse direction needs every place of `F` to have a place above it and
`𝒪'_P` to be the intersection of the valuation rings above `P`, hence the hypotheses on `F'` and
on the constant fields. -/
theorem comp_restrict_mem_repartitionSpace_iff [Algebra.IsIntegral k k']
    (hF' : IsFunctionField k' F') {β : Place k F → F'} :
    (fun P' : Place k' F' ↦ β (P'.restrict k F)) ∈ repartitionSpace k' F' ↔
      β ∈ relativeRepartitionSpace k F F' := by
  refine ⟨fun h ↦ ?_, comp_restrict_mem_repartitionSpace⟩
  rw [mem_repartitionSpace_iff_finite] at h
  rw [mem_relativeRepartitionSpace_iff, Filter.eventually_cofinite]
  refine (h.image fun P' ↦ P'.restrict k F).subset fun P hP ↦ ?_
  by_contra hnot
  refine hP ((Place.isIntegral_iff_forall_restrict_eq_mem_integers hF' P).mpr fun P' hP' ↦ ?_)
  subst hP'
  exact P'.mem_integers_iff.mpr (not_not.mp fun h' ↦ hnot ⟨P', h', rfl⟩)

end Pullback

/-! ### The trace -/

section Trace

variable [FiniteDimensional F F']

omit [Algebra k k'] [Algebra k' F'] [IsScalarTower k k' F']

/-- The entrywise trace of a relative repartition is a repartition of `F / k`: the trace of an
element integral over the integrally closed ring `𝒪_P` lies in `𝒪_P`. -/
theorem trace_comp_mem_repartitionSpace {β : Place k F → F'}
    (hβ : β ∈ relativeRepartitionSpace k F F') :
    (fun P ↦ Algebra.trace F F' (β P)) ∈ repartitionSpace k F :=
  mem_repartitionSpace_iff_integers.mpr <| (mem_relativeRepartitionSpace_iff.mp hβ).mono fun P h ↦
    P.mem_integers_of_isIntegral (R := P.integers) (fun a ↦ a.2) (Algebra.isIntegral_trace h)

variable (k F F') in
/-- **The trace of relative repartitions** `Tr_{F'/F}`, taken entrywise (Stichtenoth,
Section III.4): the `k`-linear map carrying a relative repartition `β` of `F' / F` to the
repartition `P ↦ Tr_{F'/F} (β P)` of `F / k`. -/
noncomputable def repartitionTrace :
    ↥(relativeRepartitionSpace k F F') →ₗ[k] ↥(repartitionSpace k F) where
  toFun β := ⟨fun P ↦ Algebra.trace F F' ((β : Place k F → F') P),
    trace_comp_mem_repartitionSpace β.2⟩
  map_add' β γ := Subtype.ext <| funext fun _ ↦ by simp
  map_smul' c β := Subtype.ext <| funext fun _ ↦ by
    simp only [SetLike.val_smul, Pi.smul_apply, RingHom.id_apply, algebra_compatible_smul F c,
      LinearMap.map_smul]

/-- The entries of the trace of a relative repartition are the traces of its entries. -/
@[simp]
theorem repartitionTrace_apply (β : ↥(relativeRepartitionSpace k F F')) (P : Place k F) :
    ((repartitionTrace k F F' β : ↥(repartitionSpace k F)) : Place k F → F) P =
      Algebra.trace F F' ((β : Place k F → F') P) :=
  (rfl)

/-- **The trace of a diagonal repartition is diagonal**: the trace of the constant family at `x`
is the constant family at `Tr_{F'/F} x`. -/
theorem repartitionTrace_const (β : ↥(relativeRepartitionSpace k F F')) {x : F'}
    (hβ : (β : Place k F → F') = Function.const (Place k F) x) :
    ((repartitionTrace k F F' β : ↥(repartitionSpace k F)) : Place k F → F) =
      Function.const (Place k F) (Algebra.trace F F' x) :=
  funext fun P ↦ by rw [repartitionTrace_apply, hβ, Function.const_apply, Function.const_apply]

/-- **The trace of repartitions is `F`-linear**: the trace of `f • β` is `f` times the trace of
`β`. -/
theorem repartitionTrace_smul (hF : IsFunctionField k F) (f : F)
    (β : ↥(relativeRepartitionSpace k F F')) :
    repartitionTrace k F F' ⟨f • (β : Place k F → F'), smul_mem_relativeRepartitionSpace hF f β.2⟩
      = repartitionMul hF f (repartitionTrace k F F' β) :=
  Subtype.ext <| funext fun P ↦ by
    simp only [repartitionTrace_apply, coe_repartitionMul_apply, Pi.smul_apply,
      LinearMap.map_smul]

/-- **The trace estimate** (Stichtenoth, proof of Theorem 3.4.6): if the pullback of a relative
repartition `β` to `F'` lies in `A_{F'}(Con D + Diff(F'/F))`, then its trace lies in `A_F(D)`.
At each place `P` of `F` this is `TauCeti.Place.valuation_trace_le_exp`: the coefficient of
`Con D + Diff(F'/F)` at a place `P'` over `P` is `e(P' ∣ P) · D(P) + d(P' ∣ P)`. -/
theorem repartitionTrace_mem_adeleFiltration [Algebra k k'] [Algebra k' F']
    [IsScalarTower k k' F'] [Algebra.IsIntegral k k'] [Algebra.IsSeparable F F']
    (hF : IsFunctionField k F) (hF' : IsFunctionField k' F') {D : Divisor k F}
    (β : ↥(relativeRepartitionSpace k F F'))
    (hβ : (fun P' : Place k' F' ↦ (β : Place k F → F') (P'.restrict k F)) ∈
      adeleFiltration (Divisor.conorm k' F' D + Divisor.different k' F' hF)) :
    ((repartitionTrace k F F' β : ↥(repartitionSpace k F)) : Place k F → F) ∈
      adeleFiltration D := by
  rw [mem_adeleFiltration_iff] at hβ ⊢
  intro P
  rw [repartitionTrace_apply]
  refine Place.valuation_trace_le_exp k F hF' P (D.coeff P) fun P' hP' ↦ ?_
  have h := hβ P'
  rwa [AlgebraicGeometry.WeilDivisor.coeff_add, Divisor.coeff_conorm, Divisor.coeff_different,
    hP'] at h

end Trace

end TauCeti

end
