/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.CanonicalDivisor
public import TauCeti.FieldTheory.FunctionField.Repartition.Trace
public import TauCeti.RingTheory.Trace.Dual

/-!
# The cotrace of Weil differentials

Let `F' / k'` be a finite separable extension of the algebraic function field `F / k`, with
`k' / k` finite separable.  For every Weil differential `ω` of `F / k` there is exactly one Weil
differential `ω'` of `F' / k'` with

`Tr_{k'/k} (ω' α) = ω (Tr_{F'/F} α)`

for every repartition `α` of `F'` that is constant on the fibres over the places of `F`.  This
`ω'` is the **cotrace** `Cotr_{F'/F} ω` (Stichtenoth, Definition 3.4.5 and Theorem 3.4.6).  It is
bounded by `Con D + Diff(F'/F)` whenever `ω` is bounded by `D`, so that
`Con (ω) + Diff(F'/F) ≤ (Cotr ω)`; this is the inequality half of the divisor identity
`(Cotr ω) = Con (ω) + Diff(F'/F)` from which the Hurwitz genus formula follows.

The construction follows Stichtenoth.  Every repartition of `F'` is a fibre-constant repartition
modulo `A_{F'}(B')`, for any divisor `B'` of `F'`, by weak approximation on each of the finitely
many fibres where the repartition is not already bounded by `B'`
(`TauCeti.exists_sub_relativeRepartitionPullback_mem_adeleFiltration`).  With
`B' = Con D + Diff(F'/F)`, the trace estimate `TauCeti.repartitionTrace_mem_adeleFiltration`
shows that `α ↦ ω (Tr α)` is well defined on `A_{F'} ⧸ A_{F'}(B')`, which gives a `k`-linear form
on `A_{F'}`; the trace form of `k' / k` turns it into a `k'`-linear one
(`Module.Dual.traceCompEquiv`).

## Main definitions

* `TauCeti.weilDifferentialCotrace`: the cotrace `Ω_F → Ω_{F'}`, as a `k`-linear map.

## Main results

* `TauCeti.exists_mem_weilDifferentialFiltration_trace_apply_eq`: existence of the cotrace, with
  its bound.
* `TauCeti.trace_weilDifferentialCotrace_apply`: the defining identity of the cotrace.
* `TauCeti.eq_weilDifferentialCotrace`: the cotrace is the only Weil differential of `F'`
  satisfying it.
* `TauCeti.weilDifferentialCotrace_mem_weilDifferentialFiltration`: if `ω ∈ Ω_F(D)`, then
  `Cotr ω ∈ Ω_{F'}(Con D + Diff(F'/F))`.
* `TauCeti.weilDifferentialCotrace_eq_zero_iff` and `TauCeti.weilDifferentialCotrace_injective`:
  the cotrace is injective.
* `TauCeti.conorm_add_different_le_weilDifferentialDivisor`:
  `Con (ω) + Diff(F'/F) ≤ (Cotr ω)` for a nonzero Weil differential `ω`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.4, Definition 3.4.5 and Theorem 3.4.6.
-/

public section

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F']

/-! ### The cotrace -/

section Cotrace

variable [Algebra.IsSeparable F F'] [FiniteDimensional k k'] [Algebra.IsSeparable k k']

omit [Algebra k k'] [IsScalarTower k k' F'] [Algebra.IsSeparable F F'] [FiniteDimensional k k']
  [Algebra.IsSeparable k k'] in
/-- The linear form `β ↦ ω (Tr β)` on the relative repartitions. -/
private noncomputable def traceDual (hF : IsFunctionField k F)
    (ω : Module.Dual k ↥(repartitionSpace k F)) :
    Module.Dual k ↥(relativeRepartitionSpace k F F') := by
  letI := relativeRepartitionSpaceModule (F' := F') hF
  letI := repartitionSpaceModule hF
  letI : IsScalarTower k F ↥(relativeRepartitionSpace k F F') :=
    IsScalarTower.of_algebraMap_smul fun c β ↦ by
      ext P
      rw [congrFun (coe_relativeRepartitionSpaceModule_smul hF (algebraMap k F c) β) P]
      simp only [Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def]
      rw [← IsScalarTower.algebraMap_apply k F F']
  letI : IsScalarTower k F ↥(repartitionSpace k F) :=
    IsScalarTower.of_algebraMap_smul fun c a ↦ by
      ext P
      simp [Algebra.smul_def]
  exact ω.comp ((repartitionTrace k F F' hF).restrictScalars k)

/-- **Existence of the cotrace** (Stichtenoth, Theorem 3.4.6): for a Weil differential `ω` of
`F / k` bounded by `D`, some Weil differential `ω'` of `F' / k'` bounded by
`Con D + Diff(F'/F)` satisfies `Tr_{k'/k} (ω' α) = ω (Tr_{F'/F} α)` on the fibre-constant
repartitions `α` of `F'`. -/
theorem exists_mem_weilDifferentialFiltration_trace_apply_eq (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') {D : Divisor k F} {ω : Module.Dual k ↥(repartitionSpace k F)}
    (hω : ω ∈ weilDifferentialFiltration D) :
    ∃ ω' ∈ weilDifferentialFiltration (Divisor.conorm k' F' D + Divisor.different k' F' hF),
      ∀ β : ↥(relativeRepartitionSpace k F F'),
        Algebra.trace k k' (ω' (relativeRepartitionPullback k k' F F' β)) =
          ω (repartitionTrace k F F' hF β) := by
  set B' := Divisor.conorm k' F' D + Divisor.different k' F' hF
  set V := ↥(repartitionSpace k' F')
  set p := relativeRepartitionPullback k k' F F'
  set N : Submodule k V :=
    ((adeleFiltration B').comap (repartitionSpace k' F').subtype).restrictScalars k with hN
  -- the form `β ↦ ω (Tr β)` kills the relative repartitions whose pullback is bounded by `B'`
  have hvanish : ∀ β, p β ∈ N → traceDual hF ω β = 0 := fun β hβ ↦ by
    simpa only [traceDual, LinearMap.comp_apply, LinearMap.restrictScalars_apply] using
      weilDifferentialFiltration_apply_eq_zero_of_mem_adeleFiltration hω _
        (repartitionTrace_mem_adeleFiltration hF hF' β hβ)
  -- so it descends to `A_{F'} ⧸ A_{F'}(B')`, which every relative repartition reaches
  set q : ↥(relativeRepartitionSpace k F F') →ₗ[k] V ⧸ N := N.mkQ ∘ₗ p
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨a, rfl⟩ := N.mkQ_surjective x
    obtain ⟨β, hβ⟩ :=
      exists_sub_relativeRepartitionPullback_mem_adeleFiltration (k := k) (F := F) a B'
    refine ⟨β, (Submodule.Quotient.eq N).mpr ?_⟩
    rw [hN, Submodule.restrictScalars_mem, Submodule.mem_comap, ← neg_mem_iff, map_sub, neg_sub]
    exact hβ
  have hker : LinearMap.ker q ≤ LinearMap.ker (traceDual hF ω) := fun β hβ ↦
    hvanish β ((Submodule.Quotient.mk_eq_zero N).mp hβ)
  let μ : Module.Dual k V := (LinearMap.ker q).liftQ (traceDual hF ω) hker ∘ₗ
    (q.quotKerEquivOfSurjective hq).symm.toLinearMap ∘ₗ N.mkQ
  have hμp (β) : μ (p β) = traceDual hF ω β := by
    have hqβ : q β = N.mkQ (p β) := LinearMap.comp_apply _ _ _
    simp only [μ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, ← hqβ,
      LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  have hμN (a : V) (ha : a ∈ N) : μ a = 0 := by
    simp [μ, (Submodule.Quotient.mk_eq_zero N).mpr ha]
  -- the `k'`-linear form with trace `μ` is the required Weil differential
  refine ⟨(Module.Dual.traceCompEquiv k k' V).symm μ,
    mem_weilDifferentialFiltration_of_apply_eq_zero (fun a ha ↦ ?_) (fun a ha ↦ ?_),
    fun β ↦ by
      rw [Module.Dual.trace_traceCompEquiv_symm_apply, hμp]
      simp only [traceDual, LinearMap.comp_apply, LinearMap.restrictScalars_apply]⟩
  · refine (Module.Dual.apply_eq_zero_iff_forall_trace_eq_zero (K := k) _ a).mpr fun b ↦ ?_
    rw [Module.Dual.trace_traceCompEquiv_symm_apply]
    exact hμN _ ((adeleFiltration B').smul_mem b ha)
  · refine (Module.Dual.apply_eq_zero_iff_forall_trace_eq_zero (K := k) _ a).mpr fun b ↦ ?_
    rw [Module.Dual.trace_traceCompEquiv_symm_apply]
    obtain ⟨β, hβ⟩ := smul_mem_range_relativeRepartitionPullback (k := k) (F := F) hF' b
      (const_mem_range_relativeRepartitionPullback (F := F) hF' ha)
    obtain ⟨x, hx⟩ := mem_diagonalRepartitions_iff.mp ha
    rw [← hβ, hμp]
    simp only [traceDual, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    refine weilDifferentialFiltration_apply_eq_zero_of_mem_diagonalRepartitions hω _
      (mem_diagonalRepartitions_iff.mpr ⟨Algebra.trace F F' (b • x), funext fun P ↦ ?_⟩)
    obtain ⟨P', rfl⟩ := Place.restrict_surjective (k := k) (F := F) hF' P
    have hentry := congrArg (fun a : V ↦ (a : Place k' F' → F') P') hβ
    simp only [relativeRepartitionPullback_apply] at hentry
    simp [hentry, ← hx]

omit [Algebra.IsSeparable F F'] in
/-- **Uniqueness of the cotrace** (Stichtenoth, Theorem 3.4.6): two Weil differentials of `F'`
whose values on the fibre-constant repartitions have the same traces to `k` are equal. -/
theorem eq_of_trace_apply_relativeRepartitionPullback_eq (hF' : IsFunctionField k' F')
    {ω₁ ω₂ : Module.Dual k' ↥(repartitionSpace k' F')} (h₁ : ω₁ ∈ weilDifferentialSpace k' F')
    (h₂ : ω₂ ∈ weilDifferentialSpace k' F')
    (h : ∀ β : ↥(relativeRepartitionSpace k F F'),
      Algebra.trace k k' (ω₁ (relativeRepartitionPullback k k' F F' β)) =
        Algebra.trace k k' (ω₂ (relativeRepartitionPullback k k' F F' β))) :
    ω₁ = ω₂ := by
  rw [← sub_eq_zero]
  obtain ⟨C, hC⟩ := mem_weilDifferentialSpace_iff.mp (sub_mem h₁ h₂)
  -- the difference kills the fibre-constant repartitions
  have hrange (β : ↥(relativeRepartitionSpace k F F')) :
      (ω₁ - ω₂) (relativeRepartitionPullback k k' F F' β) = 0 := by
    refine (Module.Dual.apply_eq_zero_iff_forall_trace_eq_zero (K := k) _ _).mpr fun b ↦ ?_
    obtain ⟨γ, hγ⟩ := smul_mem_range_relativeRepartitionPullback hF' b ⟨β, rfl⟩
    rw [← hγ, LinearMap.sub_apply, map_sub, h, sub_self]
  -- and every repartition is fibre-constant modulo `A_{F'}(C)`, where it vanishes too
  ext a
  obtain ⟨β, hβ⟩ :=
    exists_sub_relativeRepartitionPullback_mem_adeleFiltration (k := k) (F := F) a C
  have hsplit : a = (a - relativeRepartitionPullback k k' F F' β) +
      relativeRepartitionPullback k k' F F' β := (sub_add_cancel _ _).symm
  rw [hsplit, map_add, hrange,
    weilDifferentialFiltration_apply_eq_zero_of_mem_adeleFiltration hC _ hβ, add_zero,
    LinearMap.zero_apply]

/-- The underlying linear form of the cotrace, chosen by
`TauCeti.exists_mem_weilDifferentialFiltration_trace_apply_eq`. -/
private noncomputable def cotraceAux (hF : IsFunctionField k F) (hF' : IsFunctionField k' F')
    (ω : ↥(weilDifferentialSpace k F)) : Module.Dual k' ↥(repartitionSpace k' F') :=
  (exists_mem_weilDifferentialFiltration_trace_apply_eq (k' := k') (F' := F') hF hF'
    (mem_weilDifferentialSpace_iff.mp ω.2).choose_spec).choose

private theorem cotraceAux_mem (hF : IsFunctionField k F) (hF' : IsFunctionField k' F')
    (ω : ↥(weilDifferentialSpace k F)) : cotraceAux hF hF' ω ∈ weilDifferentialSpace k' F' :=
  weilDifferentialFiltration_le_weilDifferentialSpace _
    (exists_mem_weilDifferentialFiltration_trace_apply_eq (k' := k') (F' := F') hF hF'
      (mem_weilDifferentialSpace_iff.mp ω.2).choose_spec).choose_spec.1

private theorem trace_cotraceAux_apply (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') (ω : ↥(weilDifferentialSpace k F))
    (β : ↥(relativeRepartitionSpace k F F')) :
    Algebra.trace k k' (cotraceAux hF hF' ω (relativeRepartitionPullback k k' F F' β)) =
      (ω : Module.Dual k ↥(repartitionSpace k F)) (repartitionTrace k F F' hF β) :=
  (exists_mem_weilDifferentialFiltration_trace_apply_eq (k' := k') (F' := F') hF hF'
    (mem_weilDifferentialSpace_iff.mp ω.2).choose_spec).choose_spec.2 β

variable (k' F') in
/-- **The cotrace of a Weil differential** `Cotr_{F'/F} ω` (Stichtenoth, Definition 3.4.5): the
unique Weil differential of `F' / k'` with `Tr_{k'/k} (Cotr ω α) = ω (Tr_{F'/F} α)` for every
fibre-constant repartition `α` of `F'`.  It is characterized by
`TauCeti.trace_weilDifferentialCotrace_apply` and `TauCeti.eq_weilDifferentialCotrace`. -/
noncomputable def weilDifferentialCotrace (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') :
    ↥(weilDifferentialSpace k F) →ₗ[k] ↥(weilDifferentialSpace k' F') where
  toFun ω := ⟨cotraceAux hF hF' ω, cotraceAux_mem hF hF' ω⟩
  map_add' ω₁ ω₂ := Subtype.ext <|
    eq_of_trace_apply_relativeRepartitionPullback_eq (k := k) (F := F) hF'
      (cotraceAux_mem hF hF' _) (add_mem (cotraceAux_mem hF hF' ω₁) (cotraceAux_mem hF hF' ω₂))
      fun β ↦ by
        simp only [trace_cotraceAux_apply, Submodule.coe_add, LinearMap.add_apply, map_add]
  map_smul' c ω := Subtype.ext <|
    eq_of_trace_apply_relativeRepartitionPullback_eq (k := k) (F := F) hF'
      (cotraceAux_mem hF hF' _) (Submodule.smul_of_tower_mem _ c (cotraceAux_mem hF hF' ω))
      fun β ↦ by
        simp only [trace_cotraceAux_apply, Submodule.coe_smul_of_tower, LinearMap.smul_apply,
          map_smul, RingHom.id_apply]

/-- **The defining identity of the cotrace**: `Tr_{k'/k} (Cotr ω α) = ω (Tr_{F'/F} α)` for every
fibre-constant repartition `α` of `F'`. -/
@[simp]
theorem trace_weilDifferentialCotrace_apply (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') (ω : ↥(weilDifferentialSpace k F))
    (β : ↥(relativeRepartitionSpace k F F')) :
    Algebra.trace k k' ((weilDifferentialCotrace k' F' hF hF' ω : Module.Dual k' _)
      (relativeRepartitionPullback k k' F F' β)) =
      (ω : Module.Dual k ↥(repartitionSpace k F)) (repartitionTrace k F F' hF β) :=
  trace_cotraceAux_apply hF hF' ω β

/-- **The cotrace is the only Weil differential with its defining identity** (Stichtenoth,
Theorem 3.4.6). -/
theorem eq_weilDifferentialCotrace (hF : IsFunctionField k F) (hF' : IsFunctionField k' F')
    (ω : ↥(weilDifferentialSpace k F)) {ω' : Module.Dual k' ↥(repartitionSpace k' F')}
    (hω' : ω' ∈ weilDifferentialSpace k' F')
    (h : ∀ β : ↥(relativeRepartitionSpace k F F'),
      Algebra.trace k k' (ω' (relativeRepartitionPullback k k' F F' β)) =
        (ω : Module.Dual k ↥(repartitionSpace k F)) (repartitionTrace k F F' hF β)) :
    ω' = weilDifferentialCotrace k' F' hF hF' ω :=
  eq_of_trace_apply_relativeRepartitionPullback_eq hF' hω' (Submodule.coe_mem _) fun β ↦ by
    rw [h, trace_weilDifferentialCotrace_apply]

/-- **The cotrace raises the bound by the different** (Stichtenoth, Theorem 3.4.6): if `ω` is
bounded by `D`, then `Cotr ω` is bounded by `Con D + Diff(F'/F)`. -/
theorem weilDifferentialCotrace_mem_weilDifferentialFiltration (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') (ω : ↥(weilDifferentialSpace k F)) {D : Divisor k F}
    (hD : (ω : Module.Dual k ↥(repartitionSpace k F)) ∈ weilDifferentialFiltration D) :
    (weilDifferentialCotrace k' F' hF hF' ω : Module.Dual k' ↥(repartitionSpace k' F')) ∈
      weilDifferentialFiltration (Divisor.conorm k' F' D + Divisor.different k' F' hF) := by
  obtain ⟨ω', hω', h⟩ := exists_mem_weilDifferentialFiltration_trace_apply_eq (k' := k')
    (F' := F') hF hF' hD
  rwa [← eq_weilDifferentialCotrace hF hF' ω
    (weilDifferentialFiltration_le_weilDifferentialSpace _ hω') h]

/-- **The cotrace is injective**: `Cotr ω = 0` only for `ω = 0`, because the trace of the
fibre-constant repartitions is onto `A_F`. -/
@[simp]
theorem weilDifferentialCotrace_eq_zero_iff (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') {ω : ↥(weilDifferentialSpace k F)} :
    weilDifferentialCotrace k' F' hF hF' ω = 0 ↔ ω = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]⟩
  obtain ⟨x, hx⟩ := Algebra.trace_surjective F F' 1
  refine Subtype.ext (LinearMap.ext fun a ↦ ?_)
  -- `a` is the trace of the relative repartition `P ↦ a P • x`
  have hβ : (fun P ↦ (a : Place k F → F) P • x) ∈ relativeRepartitionSpace k F F' := by
    have hx' := mem_relativeRepartitionSpace_iff.mp
      (const_mem_relativeRepartitionSpace (k := k) hF x)
    refine mem_relativeRepartitionSpace_iff.mpr <|
      ((mem_repartitionSpace_iff_integers.mp a.2).and hx').mono fun P hP ↦ ?_
    rw [Algebra.smul_def]
    exact (isIntegral_algebraMap (x := (⟨_, hP.1⟩ : P.integers))).mul hP.2
  have htr : repartitionTrace k F F' hF ⟨_, hβ⟩ = a := Subtype.ext <| funext fun P ↦ by
    rw [repartitionTrace_apply, LinearMap.map_smul, hx, smul_eq_mul, mul_one]
  have := trace_weilDifferentialCotrace_apply hF hF' ω ⟨_, hβ⟩
  rw [h, htr] at this
  simpa using this.symm

/-- The cotrace is injective. -/
theorem weilDifferentialCotrace_injective (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') : Function.Injective (weilDifferentialCotrace k' F' hF hF') :=
  (injective_iff_map_eq_zero _).mpr fun _ ↦ (weilDifferentialCotrace_eq_zero_iff hF hF').mp

/-- **The divisor of the cotrace is at least `Con (ω) + Diff(F'/F)`** (Stichtenoth,
Theorem 3.4.6), for a nonzero Weil differential `ω` of `F / k`. -/
theorem conorm_add_different_le_weilDifferentialDivisor (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') (hex : IsIntegrallyClosedIn k F)
    (hex' : IsIntegrallyClosedIn k' F') (ω : ↥(weilDifferentialSpace k F)) (hω : ω ≠ 0) :
    Divisor.conorm k' F' (weilDifferentialDivisor hF hex ω.2 (by simpa using hω)) +
        Divisor.different k' F' hF ≤
      weilDifferentialDivisor hF' hex' (weilDifferentialCotrace k' F' hF hF' ω).2
        (by simpa [ZeroMemClass.coe_eq_zero] using hω) :=
  (mem_weilDifferentialFiltration_iff_le_weilDifferentialDivisor hF' hex' _ _ _).mp <|
    weilDifferentialCotrace_mem_weilDifferentialFiltration hF hF' ω
      (isGreatest_weilDifferentialDivisor hF hex ω.2 _).1

end Cotrace

end TauCeti
