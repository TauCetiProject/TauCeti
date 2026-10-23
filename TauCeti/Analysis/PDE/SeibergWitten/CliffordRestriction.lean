/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Trace.Free
public import TauCeti.LinearAlgebra.CliffordAlgebra.Chirality

/-!
# The Clifford map from self-dual two-forms to trace-free endomorphisms of `W⁺`

Let `V` be an oriented real inner product space of dimension four, `Q v = -‖v‖²`, and let `W` be a
finite-dimensional complex inner product space carrying a real algebra map
`ρ : CliffordAlgebra Q → End_ℂ W` whose generators act skew-adjointly, `c(v)* = -c(v)`: a
Hermitian Clifford module, such as the spinors of a `Spinᶜ` structure. The chirality element `Γ`
(`CliffordAlgebra.chirality`) splits off the positive half-spinors `W⁺ = {ψ | Γ ψ = ψ}`
(`TauCeti.SeibergWitten.positiveHalfSpinors`), and two-forms preserve `W⁺` because they commute
with `Γ`.

The **Clifford map** sends an imaginary two-form `iα`, `α ∈ ⋀² V`, to the endomorphism
`C(iα) = i c₂(α)` of `W⁺`, where `c₂ = CliffordAlgebra.bivectorExterior Q`. Here it is indexed by
the real form `α` (`TauCeti.SeibergWitten.cliffordRestriction`). Each `C(iα)` is self-adjoint and
trace free, anti-self-dual forms act by zero, and the `C(iα)` satisfy the Clifford relation
`C(iα) C(iβ) + C(iβ) C(iα) = 2 (⟪α, β⟫ + ⟪⋆α, β⟫)`. Taking traces gives the Hilbert–Schmidt
normalization `tr (C(iα)* C(iβ)) = 4 ⟪α, β⟫` for self-dual `α` when `W⁺` has complex dimension
two. As both spaces have real dimension three, `C` is then a real isomorphism from the self-dual
two-forms `Λ⁺` onto the trace-free self-adjoint endomorphisms of `W⁺`
(`TauCeti.SeibergWitten.cliffordRestrictionEquiv`). This is the identification through which the
curvature equation `F_A⁺ = q(ψ) + η` of the Seiberg–Witten equations compares a self-dual
two-form with the quadratic endomorphism `TauCeti.SeibergWitten.quadraticEnd ψ` of a positive
spinor.

## Main definitions

* `TauCeti.SeibergWitten.positiveHalfSpinors o ρ`: the positive half-spinors `W⁺`, the `+1`
  eigenspace of `Γ`.
* `TauCeti.SeibergWitten.cliffordRestriction o ρ hQ`: the real-linear map `α ↦ C(iα) = i c₂(α)`
  from two-forms to endomorphisms of `W⁺`.
* `TauCeti.SeibergWitten.cliffordRestrictionEquiv`: in complex dimension two, the restriction of
  `C` to self-dual two-forms, as an isomorphism onto `TauCeti.traceFreeSelfAdjoint W⁺`.

## Main results

* `TauCeti.SeibergWitten.adjoint_map_bivectorExterior`: two-forms act skew-adjointly,
  `c₂(α)* = -c₂(α)`, and `TauCeti.SeibergWitten.trace_map_bivectorExterior`: trace freely on
  every finite-dimensional Clifford module.
* `TauCeti.SeibergWitten.isSelfAdjoint_cliffordRestriction`,
  `TauCeti.SeibergWitten.trace_cliffordRestriction`,
  `TauCeti.SeibergWitten.cliffordRestriction_mem_traceFreeSelfAdjoint`: `C(iα)` is self-adjoint and
  trace free.
* `TauCeti.SeibergWitten.cliffordRestriction_eq_zero_of_hodgeStar_eq_neg`: anti-self-dual forms
  act by zero on `W⁺`.
* `TauCeti.SeibergWitten.cliffordRestriction_mul_add_swap`: the Clifford relation of `C`.
* `TauCeti.SeibergWitten.trace_cliffordRestriction_mul`:
  `tr (C(iα) C(iβ)) = (⟪α, β⟫ + ⟪⋆α, β⟫) dim W⁺`, and
  `TauCeti.SeibergWitten.trace_adjoint_cliffordRestriction_mul_of_hodgeStar_eq_self`: the
  Hilbert–Schmidt normalization `tr (C(iα)* C(iβ)) = 4 ⟪α, β⟫`.
* `TauCeti.SeibergWitten.cliffordRestriction_eq_zero_iff_of_hodgeStar_eq_self`: `C` is faithful on
  self-dual forms when `W⁺ ≠ 0`.

## References

* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1–§4.1.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5 and Chapter IV, §1.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open CliffordAlgebra Module
open scoped RealInnerProductSpace InnerProductSpace

/-! ### Two-forms on a Hermitian Clifford module -/

section Bivector

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)

/-- Two-forms act trace-freely on every Clifford module: `tr c₂(α) = 0`. -/
theorem trace_map_bivectorExterior (x : ⋀[ℝ]^2 M) :
    LinearMap.trace ℂ W (ρ (bivectorExterior Q x)) = 0 := by
  refine bivectorExterior_range_le_of_bivector_mem Q
    (LinearMap.ker ((LinearMap.trace ℂ W).restrictScalars ℝ ∘ₗ ρ.toLinearMap)) (fun a b ↦ ?_)
    ⟨x, rfl⟩
  simp [bivector_def, LinearMap.trace_mul_comm ℂ (ρ (ι Q a))]

variable [FiniteDimensional ℂ W] {ρ}

/-- If the generators act skew-adjointly, `c(v)* = -c(v)`, then so do two-forms:
`c₂(α)* = -c₂(α)`. -/
theorem adjoint_map_bivectorExterior (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (x : ⋀[ℝ]^2 M) :
    LinearMap.adjoint (ρ (bivectorExterior Q x)) = -ρ (bivectorExterior Q x) := by
  -- The elements acting skew-adjointly form a real subspace containing every bivector.
  let P : Submodule ℝ (CliffordAlgebra Q) :=
    { carrier := {a | LinearMap.adjoint (ρ a) = -ρ a}
      add_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
        rw [ha, hb, neg_add]
      zero_mem' := by simp
      smul_mem' := fun r a ha ↦ by
        simp only [Set.mem_ofPred_eq, map_smul] at ha ⊢
        rw [← Complex.coe_smul, map_smulₛₗ, ha, Complex.conj_ofReal, smul_neg, Complex.coe_smul] }
  refine bivectorExterior_range_le_of_bivector_mem Q P (fun a b ↦ ?_) ⟨x, rfl⟩
  simp only [P, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
  rw [bivector_def, map_smul, map_sub, map_mul, map_mul, ← Complex.coe_smul, map_smulₛₗ, map_sub,
    Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.adjoint_comp,
    LinearMap.adjoint_comp, hρ, hρ]
  simp only [LinearMap.neg_comp, LinearMap.comp_neg, neg_neg, Complex.conj_ofReal]
  module

end Bivector

/-! ### The positive half-spinors and the Clifford map -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4))
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3

/-- The positive half-spinors `W⁺ = {ψ | Γ ψ = ψ}` of a Clifford module `W`. -/
def positiveHalfSpinors : Submodule ℂ W :=
  Module.End.eigenspace (ρ (chirality Q o)) 1

variable {o ρ} in
/-- A vector is a positive half-spinor exactly when `Γ ψ = ψ`. -/
@[simp]
theorem mem_positiveHalfSpinors {ψ : W} :
    ψ ∈ positiveHalfSpinors o ρ ↔ ρ (chirality Q o) ψ = ψ := by
  simp [positiveHalfSpinors]

/-- Clifford elements commuting with `Γ`, such as two-forms, preserve `W⁺`. -/
theorem mapsTo_positiveHalfSpinors {a : CliffordAlgebra Q} (ha : Commute (chirality Q o) a) :
    ∀ ψ ∈ positiveHalfSpinors o ρ, ρ a ψ ∈ positiveHalfSpinors o ρ := fun _ hψ ↦
  Module.End.mapsTo_genEigenspace_of_comm (ha.map ρ) 1 1 hψ

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)

/-- The Clifford action of a two-form, restricted to the positive half-spinors. -/
private def restrictBivector (x : ⋀[ℝ]^2 V) : Module.End ℂ (positiveHalfSpinors o ρ) :=
  (ρ (bivectorExterior Q x)).restrict
    (mapsTo_positiveHalfSpinors o ρ (commute_chirality_bivectorExterior o hQ x))

private theorem coe_restrictBivector_apply (x : ⋀[ℝ]^2 V) (ψ : positiveHalfSpinors o ρ) :
    (restrictBivector o ρ hQ x ψ : W) = ρ (bivectorExterior Q x) ψ := rfl

/-- Two-forms act on `W⁺` with the anticommutator `-2 ⟪α, β⟫ - 2 ⟪⋆α, β⟫`. -/
private theorem restrictBivector_mul_add_swap (hkl : 2 + 2 = finrank ℝ V) (x y : ⋀[ℝ]^2 V) :
    restrictBivector o ρ hQ x * restrictBivector o ρ hQ y +
        restrictBivector o ρ hQ y * restrictBivector o ρ hQ x =
      ((-2 * ⟪x, y⟫ - 2 * ⟪o.hodgeStar hkl x, y⟫ : ℝ) : ℂ) • 1 := by
  ext ψ
  have hψ := mem_positiveHalfSpinors.1 ψ.2
  have h := congrArg (fun a ↦ ρ a (ψ : W))
    (bivectorExterior_mul_bivectorExterior_add_swap o hQ hkl x y)
  simp only [map_add, map_mul, map_sub, map_smul, AlgHom.commutes, LinearMap.add_apply,
    Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, hψ,
    Module.algebraMap_end_apply] at h
  simp only [LinearMap.add_apply, Module.End.mul_apply, Submodule.coe_add,
    coe_restrictBivector_apply,
    LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_smul, h]
  module

variable [FiniteDimensional ℂ W]

/-- **The Clifford map** `C` of the positive half-spinors, indexed by real two-forms: it sends `α`
to `C(i α) = i c₂(α)` restricted to `W⁺`. -/
def cliffordRestriction :
    ⋀[ℝ]^2 V →ₗ[ℝ] (positiveHalfSpinors o ρ →L[ℂ] positiveHalfSpinors o ρ) where
  toFun x := Complex.I • LinearMap.toContinuousLinearMap (restrictBivector o ρ hQ x)
  map_add' x y := by
    ext ψ
    simp [coe_restrictBivector_apply]
  map_smul' r x := by
    ext ψ
    simp [coe_restrictBivector_apply, smul_comm Complex.I]

/-- `C(iα) ψ = i c₂(α) ψ` for a positive half-spinor `ψ`. -/
@[simp]
theorem coe_cliffordRestriction_apply (x : ⋀[ℝ]^2 V) (ψ : positiveHalfSpinors o ρ) :
    (cliffordRestriction o ρ hQ x ψ : W) = Complex.I • ρ (bivectorExterior Q x) ψ :=
  (rfl)

private theorem coe_cliffordRestriction (x : ⋀[ℝ]^2 V) :
    (cliffordRestriction o ρ hQ x : Module.End ℂ (positiveHalfSpinors o ρ)) =
      Complex.I • restrictBivector o ρ hQ x := rfl

/-- **The Clifford relation of `C`**: `C(iα) C(iβ) + C(iβ) C(iα) = 2 (⟪α, β⟫ + ⟪⋆α, β⟫)`. -/
theorem cliffordRestriction_mul_add_swap (hkl : 2 + 2 = finrank ℝ V) (x y : ⋀[ℝ]^2 V) :
    cliffordRestriction o ρ hQ x * cliffordRestriction o ρ hQ y +
        cliffordRestriction o ρ hQ y * cliffordRestriction o ρ hQ x =
      ((2 * (⟪x, y⟫ + ⟪o.hodgeStar hkl x, y⟫) : ℝ) : ℂ) • 1 := by
  have h := restrictBivector_mul_add_swap o ρ hQ hkl x y
  ext ψ
  have h' := congrArg (fun T ↦ ((T ψ : _) : W)) h
  simp only [LinearMap.add_apply, Module.End.mul_apply, Submodule.coe_add,
    coe_restrictBivector_apply, LinearMap.smul_apply, Module.End.one_apply,
    Submodule.coe_smul] at h'
  simp only [add_apply, mul_apply_eq_comp, Submodule.coe_add,
    coe_cliffordRestriction_apply, map_smul, smul_smul, Complex.I_mul_I, ← smul_add, h',
    smul_apply, one_apply_eq_self, Submodule.coe_smul]
  module

variable {ρ} in
/-- If the generators act skew-adjointly, `c(v)* = -c(v)`, then `C(iα)` is self-adjoint. -/
theorem isSelfAdjoint_cliffordRestriction (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (x : ⋀[ℝ]^2 V) : IsSelfAdjoint (cliffordRestriction o ρ hQ x) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro ψ φ
  simp only [ContinuousLinearMap.coe_coe, Submodule.coe_inner, coe_cliffordRestriction_apply,
    inner_smul_left, inner_smul_right, Complex.conj_I]
  rw [← LinearMap.adjoint_inner_left, adjoint_map_bivectorExterior hρ, LinearMap.neg_apply,
    inner_neg_left]
  ring

private theorem trace_restrictBivector (hkl : 2 + 2 = finrank ℝ V) (x : ⋀[ℝ]^2 V) :
    LinearMap.trace ℂ _ (restrictBivector o ρ hQ x) = 0 := by
  -- `(c₂(α) + c₂(⋆α)) / 2 = (1 + Γ) c₂(α) / 2` maps `W` into `W⁺` and agrees with `c₂(α)` there, so
  -- the trace of `c₂(α)` on `W⁺` is that of `(c₂(α) + c₂(⋆α)) / 2` on `W`.
  set a := (2⁻¹ : ℝ) • (bivectorExterior Q x + bivectorExterior Q (o.hodgeStar hkl x))
  have ha : a = (2⁻¹ : ℝ) • (1 + chirality Q o) * bivectorExterior Q x := by
    simp only [a]
    rw [bivectorExterior_hodgeStar o hQ hkl, smul_mul_assoc, add_mul, one_mul]
  have hmem (w : W) : ρ a w ∈ positiveHalfSpinors o ρ := by
    rw [mem_positiveHalfSpinors, ← Module.End.mul_apply, ← map_mul, ha, ← mul_assoc, mul_smul_comm,
      mul_add, mul_one, chirality_mul_self o hQ, add_comm]
  have hcomp : restrictBivector o ρ hQ x =
      (ρ a).codRestrict (positiveHalfSpinors o ρ) hmem ∘ₗ (positiveHalfSpinors o ρ).subtype := by
    ext ψ
    have hψ := mem_positiveHalfSpinors.1 ψ.2
    rw [coe_restrictBivector_apply, LinearMap.comp_apply, LinearMap.codRestrict_apply,
      Submodule.subtype_apply, ha, smul_mul_assoc, add_mul, one_mul,
      (commute_chirality_bivectorExterior o hQ x).eq]
    simp [hψ]
    module
  rw [hcomp, LinearMap.trace_comp_comm', LinearMap.subtype_comp_codRestrict]
  simp [a, trace_map_bivectorExterior]

/-- **`C(iα)` is trace free** on `W⁺`. -/
theorem trace_cliffordRestriction (hkl : 2 + 2 = finrank ℝ V) (x : ⋀[ℝ]^2 V) :
    LinearMap.trace ℂ (positiveHalfSpinors o ρ) (cliffordRestriction o ρ hQ x) = 0 := by
  rw [coe_cliffordRestriction, map_smul, trace_restrictBivector o ρ hQ hkl, smul_zero]

/-- The trace pairing of the Clifford map: `tr (C(iα) C(iβ)) = (⟪α, β⟫ + ⟪⋆α, β⟫) dim W⁺`. -/
theorem trace_cliffordRestriction_mul (hkl : 2 + 2 = finrank ℝ V) (x y : ⋀[ℝ]^2 V) :
    LinearMap.trace ℂ (positiveHalfSpinors o ρ)
        (cliffordRestriction o ρ hQ x * cliffordRestriction o ρ hQ y) =
      ((⟪x, y⟫ + ⟪o.hodgeStar hkl x, y⟫ : ℝ) : ℂ) * finrank ℂ (positiveHalfSpinors o ρ) := by
  -- By cyclicity, twice the trace is the trace of the anticommutator.
  have h := congrArg (LinearMap.trace ℂ (positiveHalfSpinors o ρ) ∘ ContinuousLinearMap.toLinearMap)
    (cliffordRestriction_mul_add_swap o ρ hQ hkl x y)
  simp only [Function.comp_apply, ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_mul, map_add, LinearMap.trace_mul_comm ℂ
      (cliffordRestriction o ρ hQ y : Module.End ℂ (positiveHalfSpinors o ρ)),
    ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_one, map_smul,
    LinearMap.trace_one, smul_eq_mul] at h
  push_cast at h ⊢
  linear_combination h / 2

/-- **The Hilbert–Schmidt normalization of the Clifford map**: on a positive half-spinor space of
complex dimension two, `tr (C(iα)* C(iβ)) = 4 ⟪α, β⟫` for self-dual `α`. -/
theorem trace_adjoint_cliffordRestriction_mul_of_hodgeStar_eq_self
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (hkl : 2 + 2 = finrank ℝ V)
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) {x : ⋀[ℝ]^2 V} (hx : o.hodgeStar hkl x = x)
    (y : ⋀[ℝ]^2 V) :
    LinearMap.trace ℂ (positiveHalfSpinors o ρ)
        (ContinuousLinearMap.adjoint (cliffordRestriction o ρ hQ x) *
          cliffordRestriction o ρ hQ y) =
      4 * ⟪x, y⟫ := by
  rw [← ContinuousLinearMap.star_eq_adjoint, (isSelfAdjoint_cliffordRestriction o hQ hρ x).star_eq,
    trace_cliffordRestriction_mul o ρ hQ hkl, hx, h₂]
  push_cast
  ring

/-- Anti-self-dual two-forms act by zero on `W⁺`: `C(iα) = 0` when `⋆α = -α`. -/
theorem cliffordRestriction_eq_zero_of_hodgeStar_eq_neg (hkl : 2 + 2 = finrank ℝ V)
    {x : ⋀[ℝ]^2 V} (hx : o.hodgeStar hkl x = -x) : cliffordRestriction o ρ hQ x = 0 := by
  ext ψ
  have hψ := mem_positiveHalfSpinors.1 ψ.2
  have h : ρ (bivectorExterior Q x) ψ = -ρ (bivectorExterior Q x) ψ := by
    conv_lhs => rw [← hψ, ← Module.End.mul_apply, ← map_mul,
      bivectorExterior_mul_chirality_of_hodgeStar_eq_neg o hQ hkl hx, map_neg]
    rfl
  rw [eq_neg_iff_add_eq_zero, ← two_smul ℂ, smul_eq_zero] at h
  simp [h.resolve_left two_ne_zero]

/-- A self-dual two-form squares to `2 ‖α‖²` under the Clifford map: `C(iα)² = 2 ‖α‖²`. -/
theorem cliffordRestriction_mul_self_of_hodgeStar_eq_self (hkl : 2 + 2 = finrank ℝ V)
    {x : ⋀[ℝ]^2 V} (hx : o.hodgeStar hkl x = x) :
    cliffordRestriction o ρ hQ x * cliffordRestriction o ρ hQ x = ((2 * ‖x‖ ^ 2 : ℝ) : ℂ) • 1 := by
  have h := cliffordRestriction_mul_add_swap o ρ hQ hkl x x
  rw [hx, real_inner_self_eq_norm_sq, ← two_smul ℂ] at h
  rw [← smul_right_injective _ (two_ne_zero (α := ℂ)) |>.eq_iff, h, smul_smul]
  push_cast
  ring_nf

/-- The Clifford map is faithful on self-dual two-forms: if `W⁺ ≠ 0` and `⋆α = α`, then
`C(iα) = 0` only for `α = 0`. -/
theorem cliffordRestriction_eq_zero_iff_of_hodgeStar_eq_self [Nontrivial (positiveHalfSpinors o ρ)]
    (hkl : 2 + 2 = finrank ℝ V) {x : ⋀[ℝ]^2 V} (hx : o.hodgeStar hkl x = x) :
    cliffordRestriction o ρ hQ x = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]⟩
  have hsq := cliffordRestriction_mul_self_of_hodgeStar_eq_self o ρ hQ hkl hx
  -- Evaluate `C(iα)² = 2 ‖α‖²` on a nonzero positive spinor.
  obtain ⟨ψ, hψ⟩ := exists_ne (0 : positiveHalfSpinors o ρ)
  have hsqψ := congrArg (· ψ) hsq
  simp only [h, zero_mul, zero_apply, smul_apply, one_apply_eq_self] at hsqψ
  simpa [hψ] using hsqψ.symm

variable {ρ} in
/-- `C(iα)` is a trace-free self-adjoint endomorphism of `W⁺`. -/
theorem cliffordRestriction_mem_traceFreeSelfAdjoint
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (hkl : 2 + 2 = finrank ℝ V)
    (x : ⋀[ℝ]^2 V) :
    cliffordRestriction o ρ hQ x ∈ traceFreeSelfAdjoint (positiveHalfSpinors o ρ) :=
  mem_traceFreeSelfAdjoint.2
    ⟨isSelfAdjoint_cliffordRestriction o hQ hρ x, trace_cliffordRestriction o ρ hQ hkl x⟩

variable {ρ} in
/-- The Clifford map on self-dual two-forms, with values in the trace-free self-adjoint
endomorphisms of `W⁺`. -/
private def cliffordSelfDual (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (hkl : 2 + 2 = finrank ℝ V) :
    Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 →ₗ[ℝ]
      traceFreeSelfAdjoint (positiveHalfSpinors o ρ) :=
  ((cliffordRestriction o ρ hQ).domRestrict _).codRestrict _ fun x ↦
    cliffordRestriction_mem_traceFreeSelfAdjoint o hQ hρ hkl x

private theorem bijective_cliffordSelfDual (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (hkl : 2 + 2 = finrank ℝ V) (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) :
    Function.Bijective (cliffordSelfDual o hQ hρ hkl) := by
  have : Nontrivial (positiveHalfSpinors o ρ) := Module.nontrivial_of_finrank_eq_succ h₂
  have : FiniteDimensional ℝ (positiveHalfSpinors o ρ →L[ℂ] positiveHalfSpinors o ρ) :=
    Module.Finite.trans ℂ _
  -- `C` is injective on `Λ⁺` by faithfulness, and both sides have real dimension three.
  have hinj : Function.Injective (cliffordSelfDual o hQ hρ hkl) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx ↦ Subtype.ext ?_
    have hself : o.hodgeStar hkl x = x := by simpa using Module.End.mem_eigenspace_iff.1 x.2
    exact (cliffordRestriction_eq_zero_iff_of_hodgeStar_eq_self o ρ hQ hkl hself).1
      (congrArg Subtype.val hx)
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩
  have h₃ := o.two_mul_finrank_eigenspace_hodgeStar_one even_two two_pos hkl
  rw [finrank_traceFreeSelfAdjoint, h₂]
  norm_num [Nat.choose] at h₃ ⊢
  omega

include hQ in
variable {ρ} in
/-- **The Clifford isomorphism** `C : iΛ⁺ ≃ {T : W⁺ → W⁺ | T* = T, tr T = 0}`, indexed by real
self-dual two-forms, on a positive half-spinor space of complex dimension two: it sends `α` to
`C(iα) = i c₂(α)`. -/
def cliffordRestrictionEquiv (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (hkl : 2 + 2 = finrank ℝ V) (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) :
    Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 ≃ₗ[ℝ]
      traceFreeSelfAdjoint (positiveHalfSpinors o ρ) :=
  LinearEquiv.ofBijective (cliffordSelfDual o hQ hρ hkl)
    (bijective_cliffordSelfDual o ρ hQ hρ hkl h₂)

/-- The Clifford isomorphism sends a self-dual `α` to `C(iα)`. -/
@[simp]
theorem coe_cliffordRestrictionEquiv_apply (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (hkl : 2 + 2 = finrank ℝ V) (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (x : Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1) :
    (cliffordRestrictionEquiv o hQ hρ hkl h₂ x :
        positiveHalfSpinors o ρ →L[ℂ] positiveHalfSpinors o ρ) =
      cliffordRestriction o ρ hQ x :=
  (rfl)

end TauCeti.SeibergWitten
