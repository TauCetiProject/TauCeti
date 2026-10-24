/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Trace.Free
public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Action
public import TauCeti.LinearAlgebra.CliffordAlgebra.Chirality
-- Private: the trace of a restriction is used only inside a proof.
import Mathlib.LinearAlgebra.PID

/-!
# The Clifford map from self-dual two-forms to trace-free endomorphisms of `W⁺`

Let `V` be an oriented real inner product space of dimension four, `Q v = -‖v‖²`, and let `W` be a
finite-dimensional complex inner product space carrying a real algebra map
`ρ : CliffordAlgebra Q → End_ℂ W` whose generators act skew-adjointly, `c(v)* = -c(v)`: a
Hermitian Clifford module, such as the spinors of a `Spinᶜ` structure. The chirality element `Γ`
(`CliffordAlgebra.chirality`) splits off the positive half-spinors `W⁺ = {ψ | Γ ψ = ψ}`
(`CliffordAlgebra.positiveHalfSpinors`), and two-forms preserve `W⁺` because they commute
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

The real Hilbert–Schmidt pairing `Re tr (T* U)` on all complex endomorphisms of `W⁺` gives `C` an
adjoint `τ = C*` (`TauCeti.SeibergWitten.cliffordRestrictionAdjoint`), defined on every
endomorphism. In complex dimension two, `C* C = 4` and `C C*` is `4` times the orthogonal
projection onto the trace-free self-adjoint endomorphisms, so `τ / 4` inverts `C` there. The
operator norm of `C` is `‖C(iα)‖ = √2 ‖α‖` on self-dual forms.

## Main definitions

* `TauCeti.SeibergWitten.cliffordRestriction o ρ hQ`: the real-linear map `α ↦ C(iα) = i c₂(α)`
  from two-forms to endomorphisms of `W⁺`.
* `TauCeti.SeibergWitten.cliffordRestrictionEquiv`: in complex dimension two, the restriction of
  `C` to self-dual two-forms, as an isomorphism onto `TauCeti.traceFreeSelfAdjoint W⁺`.
* `TauCeti.SeibergWitten.cliffordRestrictionAdjoint o ρ hQ hkl`: the adjoint `τ = C*`, a continuous
  real-linear map from the complex endomorphisms of `W⁺` to the self-dual two-forms.

## Main results

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
* `TauCeti.SeibergWitten.norm_cliffordRestriction_of_hodgeStar_eq_self`,
  `TauCeti.SeibergWitten.norm_cliffordRestriction_coe`: `‖C(iα)‖ = √2 ‖α‖` for self-dual `α` when
  `W⁺ ≠ 0`.
* `TauCeti.SeibergWitten.inner_cliffordRestrictionAdjoint_left`,
  `TauCeti.SeibergWitten.re_trace_adjoint_mul_cliffordRestriction`: the adjunction
  `⟪τ T, β⟫ = Re tr (T C(iβ)) = Re tr (T* C(iβ))`.
* `TauCeti.SeibergWitten.cliffordRestrictionAdjoint_smul_one`,
  `TauCeti.SeibergWitten.cliffordRestrictionAdjoint_one`: `τ(c Id) = 0`, in particular `τ(Id) = 0`.
* `TauCeti.SeibergWitten.cliffordRestrictionAdjoint_cliffordRestriction`: `C* C = 4`, and
  `TauCeti.SeibergWitten.cliffordRestriction_cliffordRestrictionAdjoint_eq_traceFreePart`:
  `C(i τ(T)) = 2 (T + T*)₀`, so `C C* = 4` on trace-free self-adjoint endomorphisms
  (`cliffordRestriction_cliffordRestrictionAdjoint_of_mem_traceFreeSelfAdjoint`).

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

/-! ### The Clifford map -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4))
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3

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
  -- `Γ (1 + Γ) = 1 + Γ`, so `Γ a = a`.
  have hΓ : chirality Q o * a = a := by
    simp [ha, ← mul_assoc, mul_add, chirality_mul_self o hQ, add_comm]
  have hmem (w : W) : ρ a w ∈ positiveHalfSpinors o ρ := by
    rw [mem_positiveHalfSpinors, ← Module.End.mul_apply, ← map_mul, hΓ]
  have hres : restrictBivector o ρ hQ x = (ρ a).restrict (fun w _ ↦ hmem w) := by
    ext ψ
    have hψ := mem_positiveHalfSpinors.1 ψ.2
    simp [coe_restrictBivector_apply, ha, add_mul, (commute_chirality_bivectorExterior o hQ x).eq,
      hψ]
    module
  rw [hres, LinearMap.trace_restrict_eq_of_forall_mem _ (ρ a) hmem]
  simp [a, trace_map_bivectorExterior]

/-- **`C(iα)` is trace free** on `W⁺`. -/
@[simp]
theorem trace_cliffordRestriction (x : ⋀[ℝ]^2 V) :
    LinearMap.trace ℂ (positiveHalfSpinors o ρ) (cliffordRestriction o ρ hQ x) = 0 := by
  have hkl : 2 + 2 = finrank ℝ V := (Fact.out : finrank ℝ V = 4).symm
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
      bivectorExterior_mul_chirality_of_hodgeStar_eq_neg o hQ hkl hx, map_neg, LinearMap.neg_apply]
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
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (x : ⋀[ℝ]^2 V) :
    cliffordRestriction o ρ hQ x ∈ traceFreeSelfAdjoint (positiveHalfSpinors o ρ) :=
  mem_traceFreeSelfAdjoint.2
    ⟨isSelfAdjoint_cliffordRestriction o hQ hρ x, trace_cliffordRestriction o ρ hQ x⟩

variable {ρ} in
/-- The Clifford map on self-dual two-forms, with values in the trace-free self-adjoint
endomorphisms of `W⁺`. -/
private def cliffordSelfDual (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (hkl : 2 + 2 = finrank ℝ V) :
    Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 →ₗ[ℝ]
      traceFreeSelfAdjoint (positiveHalfSpinors o ρ) :=
  ((cliffordRestriction o ρ hQ).domRestrict _).codRestrict _ fun x ↦
    cliffordRestriction_mem_traceFreeSelfAdjoint o hQ hρ x

private theorem bijective_cliffordSelfDual (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (hkl : 2 + 2 = finrank ℝ V) (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) :
    Function.Bijective (cliffordSelfDual o hQ hρ hkl) := by
  have : Nontrivial (positiveHalfSpinors o ρ) := Module.nontrivial_of_finrank_eq_succ h₂
  have : FiniteDimensional ℝ (positiveHalfSpinors o ρ →L[ℂ] positiveHalfSpinors o ρ) :=
    Module.Finite.trans ℂ _
  -- `C` is injective on `Λ⁺` by faithfulness, and both sides have real dimension three.
  have hinj : Function.Injective (cliffordSelfDual o hQ hρ hkl) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx ↦ Subtype.ext ?_
    exact (cliffordRestriction_eq_zero_iff_of_hodgeStar_eq_self o ρ hQ hkl
      (o.hodgeStar_coe_of_mem_eigenspace_one hkl x)).1
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

/-! ### The norm of the Clifford map -/

variable {ρ} in
/-- `C(iα)` scales the norm of every positive half-spinor by `√2 ‖α‖` when `α` is self-dual. -/
theorem norm_cliffordRestriction_apply_of_hodgeStar_eq_self
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (hkl : 2 + 2 = finrank ℝ V)
    {x : ⋀[ℝ]^2 V} (hx : o.hodgeStar hkl x = x) (ψ : positiveHalfSpinors o ρ) :
    ‖cliffordRestriction o ρ hQ x ψ‖ = √2 * ‖x‖ * ‖ψ‖ := by
  set C := cliffordRestriction o ρ hQ x
  have hsym : ⟪C ψ, C ψ⟫_ℂ = ⟪ψ, C (C ψ)⟫_ℂ :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1
      (isSelfAdjoint_cliffordRestriction o hQ hρ x) ψ (C ψ)
  have hsq : C (C ψ) = ((2 * ‖x‖ ^ 2 : ℝ) : ℂ) • ψ := by
    simpa using congrArg (· ψ) (cliffordRestriction_mul_self_of_hodgeStar_eq_self o ρ hQ hkl hx)
  -- `‖C ψ‖² = ⟪ψ, C² ψ⟫ = 2 ‖α‖² ‖ψ‖²`.
  have h : ‖C ψ‖ ^ 2 = (√2 * ‖x‖ * ‖ψ‖) ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, hsym, hsq]
    simp [inner_smul_right, mul_pow, ← Complex.ofReal_pow]
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h

variable {ρ} in
/-- **The operator norm of the Clifford map**: `‖C(iα)‖ = √2 ‖α‖` for self-dual `α`, when
`W⁺ ≠ 0`. -/
theorem norm_cliffordRestriction_of_hodgeStar_eq_self
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) [Nontrivial (positiveHalfSpinors o ρ)]
    (hkl : 2 + 2 = finrank ℝ V) {x : ⋀[ℝ]^2 V} (hx : o.hodgeStar hkl x = x) :
    ‖cliffordRestriction o ρ hQ x‖ = √2 * ‖x‖ := by
  have happly := norm_cliffordRestriction_apply_of_hodgeStar_eq_self o hQ hρ hkl hx
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ψ ↦
    (happly ψ).le) ?_
  -- Test the operator norm against a nonzero positive half-spinor.
  obtain ⟨ψ, hψ⟩ := exists_ne (0 : positiveHalfSpinors o ρ)
  have := (cliffordRestriction o ρ hQ x).le_opNorm ψ
  rw [happly] at this
  exact le_of_mul_le_mul_right this (norm_pos_iff.2 hψ)

variable {ρ} in
/-- `‖C(iα)‖ = √2 ‖α‖` for every form `α` of the self-dual eigenspace, when `W⁺ ≠ 0`. -/
theorem norm_cliffordRestriction_coe (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    [Nontrivial (positiveHalfSpinors o ρ)] (hkl : 2 + 2 = finrank ℝ V)
    (x : Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1) :
    ‖cliffordRestriction o ρ hQ x‖ = √2 * ‖x‖ :=
  norm_cliffordRestriction_of_hodgeStar_eq_self o hQ hρ hkl
    (o.hodgeStar_coe_of_mem_eigenspace_one hkl x)

/-! ### The adjoint of the Clifford map -/

/-- Instance search does not find this instance for the endomorphisms of the submodule `W⁺`, so it
is obtained from the generic one. -/
private theorem continuousSMul_real_end (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] : ContinuousSMul ℝ (E →L[ℂ] E) :=
  inferInstance

/-- The real trace pairing `β ↦ Re tr (T C(iβ))` of an endomorphism `T` of `W⁺` with the Clifford
map on self-dual forms. -/
private def tracePairing (hkl : 2 + 2 = finrank ℝ V)
    (T : positiveHalfSpinors o ρ →L[ℂ] positiveHalfSpinors o ρ) :
    StrongDual ℝ (Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1) :=
  LinearMap.toContinuousLinearMap <|
    Complex.reLm ∘ₗ (LinearMap.trace ℂ (positiveHalfSpinors o ρ)).restrictScalars ℝ ∘ₗ
      (ContinuousLinearMap.coeLM ℂ).restrictScalars ℝ ∘ₗ
      (ContinuousLinearMap.compL ℂ _ _ _ T).toLinearMap.restrictScalars ℝ ∘ₗ
      cliffordRestriction o ρ hQ ∘ₗ
      (Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1).subtype

private theorem tracePairing_apply (hkl : 2 + 2 = finrank ℝ V)
    (T : positiveHalfSpinors o ρ →L[ℂ] positiveHalfSpinors o ρ)
    (β : Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1) :
    tracePairing o ρ hQ hkl T β =
      (LinearMap.trace ℂ (positiveHalfSpinors o ρ) (T * cliffordRestriction o ρ hQ β)).re :=
  rfl

/-- **The adjoint `τ = C*` of the Clifford map** for the real Hilbert–Schmidt pairing
`Re tr (T* U)` on the complex endomorphisms of `W⁺`: the self-dual form `τ T` is characterized by
`⟪τ T, β⟫ = Re tr (T C(iβ))` (`inner_cliffordRestrictionAdjoint_left`), which is
`Re tr (T* C(iβ))` when the generators act skew-adjointly
(`re_trace_adjoint_mul_cliffordRestriction`). As for `C`, the imaginary two-form `i τ(T)` is
indexed by the real form `τ(T)`. -/
def cliffordRestrictionAdjoint (hkl : 2 + 2 = finrank ℝ V) :
    (positiveHalfSpinors o ρ →L[ℂ] positiveHalfSpinors o ρ) →L[ℝ]
      Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 :=
  haveI : FiniteDimensional ℝ (positiveHalfSpinors o ρ →L[ℂ] positiveHalfSpinors o ρ) :=
    Module.Finite.trans ℂ _
  haveI := continuousSMul_real_end (positiveHalfSpinors o ρ)
  LinearMap.toContinuousLinearMap
    { toFun T := (InnerProductSpace.toDual ℝ _).symm (tracePairing o ρ hQ hkl T)
      map_add' T U := ext_inner_right ℝ fun β ↦ by
        simp [InnerProductSpace.toDual_symm_apply, inner_add_left, tracePairing_apply, add_mul]
      map_smul' r T := ext_inner_right ℝ fun β ↦ by
        rw [real_inner_smul_left]
        simp [InnerProductSpace.toDual_symm_apply, tracePairing_apply] }

/-- The defining property of the adjoint of the Clifford map: `⟪τ T, β⟫ = Re tr (T C(iβ))`. -/
theorem inner_cliffordRestrictionAdjoint_left (hkl : 2 + 2 = finrank ℝ V)
    (T : positiveHalfSpinors o ρ →L[ℂ] positiveHalfSpinors o ρ)
    (β : Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1) :
    ⟪cliffordRestrictionAdjoint o ρ hQ hkl T, β⟫ =
      (LinearMap.trace ℂ (positiveHalfSpinors o ρ) (T * cliffordRestriction o ρ hQ β)).re := by
  simp [cliffordRestrictionAdjoint, InnerProductSpace.toDual_symm_apply, tracePairing_apply]

variable {ρ} in
/-- `τ` is the adjoint of `C` for the real Hilbert–Schmidt pairing:
`Re tr (T* C(iβ)) = ⟪τ T, β⟫`. -/
theorem re_trace_adjoint_mul_cliffordRestriction
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (hkl : 2 + 2 = finrank ℝ V)
    (T : positiveHalfSpinors o ρ →L[ℂ] positiveHalfSpinors o ρ)
    (β : Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1) :
    (LinearMap.trace ℂ (positiveHalfSpinors o ρ)
        (ContinuousLinearMap.adjoint T * cliffordRestriction o ρ hQ β)).re =
      ⟪cliffordRestrictionAdjoint o ρ hQ hkl T, β⟫ := by
  -- `T* C(iβ) = (C(iβ) T)*`, as `C(iβ)` is self-adjoint.
  have h : ContinuousLinearMap.adjoint (cliffordRestriction o ρ hQ β * T) =
      ContinuousLinearMap.adjoint T * cliffordRestriction o ρ hQ β := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_mul,
      (isSelfAdjoint_cliffordRestriction o hQ hρ β).star_eq, ContinuousLinearMap.star_eq_adjoint]
  rw [inner_cliffordRestrictionAdjoint_left, ← ContinuousLinearMap.toLinearMap_mul, ← h,
    ContinuousLinearMap.trace_adjoint]
  simp [LinearMap.trace_mul_comm]

/-- `τ` kills the complex scalars: `τ(c Id) = 0`. -/
@[simp]
theorem cliffordRestrictionAdjoint_smul_one (hkl : 2 + 2 = finrank ℝ V) (c : ℂ) :
    cliffordRestrictionAdjoint o ρ hQ hkl (c • 1) = 0 :=
  ext_inner_right ℝ fun β ↦ by
    rw [inner_cliffordRestrictionAdjoint_left]
    simp

/-- `τ` kills the scalars: `τ(Id) = 0`. -/
@[simp]
theorem cliffordRestrictionAdjoint_one (hkl : 2 + 2 = finrank ℝ V) :
    cliffordRestrictionAdjoint o ρ hQ hkl 1 = 0 := by
  simpa using cliffordRestrictionAdjoint_smul_one o ρ hQ hkl 1

/-- `C* C = 4`: on a positive half-spinor space of complex dimension two, `τ(C(iα)) = 4 α` for
self-dual `α`. -/
theorem cliffordRestrictionAdjoint_cliffordRestriction (hkl : 2 + 2 = finrank ℝ V)
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (α : Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1) :
    cliffordRestrictionAdjoint o ρ hQ hkl (cliffordRestriction o ρ hQ α) = (4 : ℝ) • α :=
  ext_inner_right ℝ fun β ↦ by
    rw [inner_cliffordRestrictionAdjoint_left, trace_cliffordRestriction_mul o ρ hQ hkl,
      o.hodgeStar_coe_of_mem_eigenspace_one hkl α, h₂, Complex.re_ofReal_mul, Complex.natCast_re,
      Submodule.coe_inner, Submodule.coe_smul, real_inner_smul_left]
    ring

variable {ρ} in
/-- `C C* = 4` on the trace-free self-adjoint endomorphisms: on a positive half-spinor space of
complex dimension two, `C(i τ(T)) = 4 T` when `T* = T` and `tr T = 0`. -/
theorem cliffordRestriction_cliffordRestrictionAdjoint_of_mem_traceFreeSelfAdjoint
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (hkl : 2 + 2 = finrank ℝ V)
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    {T : positiveHalfSpinors o ρ →L[ℂ] positiveHalfSpinors o ρ}
    (hT : T ∈ traceFreeSelfAdjoint (positiveHalfSpinors o ρ)) :
    cliffordRestriction o ρ hQ (cliffordRestrictionAdjoint o ρ hQ hkl T) = (4 : ℝ) • T := by
  obtain ⟨α, hα⟩ := (cliffordRestrictionEquiv o hQ hρ hkl h₂).surjective ⟨T, hT⟩
  have hT' : cliffordRestriction o ρ hQ α = T :=
    (coe_cliffordRestrictionEquiv_apply o ρ hQ hρ hkl h₂ α).symm.trans (congrArg Subtype.val hα)
  rw [← hT', cliffordRestrictionAdjoint_cliffordRestriction o ρ hQ hkl h₂, Submodule.coe_smul,
    map_smul]

variable {ρ} in
/-- `C C*` is `4` times the orthogonal projection onto the trace-free self-adjoint endomorphisms:
on a positive half-spinor space of complex dimension two,
`C(i τ(T)) = 2 (T + T*)₀ = 4 ((T + T*) / 2)₀`, where `U₀` is the trace-free part of `U`. -/
theorem cliffordRestriction_cliffordRestrictionAdjoint_eq_traceFreePart
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (hkl : 2 + 2 = finrank ℝ V)
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (T : positiveHalfSpinors o ρ →L[ℂ] positiveHalfSpinors o ρ) :
    cliffordRestriction o ρ hQ (cliffordRestrictionAdjoint o ρ hQ hkl T) =
      (2 : ℝ) • traceFreePart ℂ (positiveHalfSpinors o ρ) (T + ContinuousLinearMap.adjoint T) := by
  set P := traceFreePart ℂ (positiveHalfSpinors o ρ) (T + ContinuousLinearMap.adjoint T)
    with hPdef
  have hP : P ∈ traceFreeSelfAdjoint (positiveHalfSpinors o ρ) := by
    have := IsSelfAdjoint.add_star_self T
    rw [ContinuousLinearMap.star_eq_adjoint] at this
    exact this.traceFreePart_mem
  -- `P` pairs with every `C(iβ)` as `T + T*` does, hence as `2 T` does.
  have hτ : cliffordRestrictionAdjoint o ρ hQ hkl P =
      cliffordRestrictionAdjoint o ρ hQ hkl T + cliffordRestrictionAdjoint o ρ hQ hkl T :=
    ext_inner_right ℝ fun β ↦ by
      rw [inner_cliffordRestrictionAdjoint_left, hPdef,
        trace_traceFreePart_mul (trace_cliffordRestriction o ρ hQ β)]
      simpa [add_mul, inner_add_left, re_trace_adjoint_mul_cliffordRestriction o hQ hρ hkl] using
        (inner_cliffordRestrictionAdjoint_left o ρ hQ hkl T β).symm
  have h := congrArg (fun x : Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 ↦
    cliffordRestriction o ρ hQ x) hτ
  simp only [Submodule.coe_add, map_add,
    cliffordRestriction_cliffordRestrictionAdjoint_of_mem_traceFreeSelfAdjoint o hQ hρ hkl h₂ hP]
    at h
  calc _ = (2 : ℝ)⁻¹ • (cliffordRestriction o ρ hQ (cliffordRestrictionAdjoint o ρ hQ hkl T) +
        cliffordRestriction o ρ hQ (cliffordRestrictionAdjoint o ρ hQ hkl T)) := by module
    _ = (2 : ℝ) • P := by rw [← h]; module

end TauCeti.SeibergWitten
