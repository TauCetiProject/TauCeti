/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Isometry
public import TauCeti.Analysis.PDE.SeibergWitten.Bundle.QuadraticTwoForm
public import TauCeti.Topology.VectorBundle.SpinStructure.Orientation

import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# The Clifford isomorphism on the self-dual two-forms of a `Spinᶜ` structure

Let `s` be a `Spinᶜ` structure on a real vector bundle `E → X` of rank four with fibre inner
products, `W⁺ = s.halfSpinorBundle o hQ b ρ hρ 1` its positive half-spinor bundle, and
`C_x : ⋀² (E x) → End_ℂ (W⁺_x)` the Clifford map `α ↦ C(iα) = i c₂(α)` on its fibres
(`TauCeti.SpinCStructure.cliffordRestriction`). On a model Hermitian Clifford module, `C` is a real
isomorphism from the self-dual two-forms onto the trace-free self-adjoint endomorphisms of the
positive half-spinors (`TauCeti.SeibergWitten.cliffordRestrictionEquiv`), with adjoint
`τ = C*` for the real Hilbert–Schmidt pairing (`TauCeti.SeibergWitten.cliffordRestrictionAdjoint`).
This file carries both to the fibres of `s`.

**The self-dual forms of a fibre.** A point `p` of the principal bundle over `x` gives the linear
isometry `κ_p : E x ≃ V` (`TauCeti.SpinCStructure.vectorFrame`). All of them pull the model
orientation `o` of `V` back to one orientation of `E x`, the fibre orientation of `s` for the
model orientation `o` read through `b`
(`TauCeti.SpinCStructure.fiberOrientation_map_repr`), and `⋀² κ_p` intertwines the Hodge star of
this orientation with that of `o` (`TauCeti.SpinCStructure.map_vectorFrame_hodgeStar`). The
self-dual forms `Λ⁺_x` are the `1`-eigenspace of this Hodge star on `⋀² (E x)`. Hence, on the
fibres, `C_x(⋆α) = C_x(α)`, anti-self-dual forms act by zero, and the trace pairing is
`tr (C_x(α) C_x(β)) = (⟪α, β⟫ + ⟪⋆α, β⟫) dim W⁺_x`.

**The adjoint and the isomorphism.** The adjoint `τ_x : End_ℂ (W⁺_x) → Λ⁺_x` is the model `τ` in a
frame, `τ_x(T) = ⋀² κ_p⁻¹ τ([p, -]⁻¹ T [p, -])`
(`TauCeti.SpinCStructure.coe_cliffordRestrictionAdjoint_eq`). It does not depend on `p`, because it
is characterized by `⟪τ_x(T), β⟫ = Re tr (T C_x(β))` for every self-dual `β`
(`TauCeti.SpinCStructure.inner_cliffordRestrictionAdjoint_left`). In complex rank two,
`τ_x(C_x(α)) = 4 α` for self-dual `α` and `C_x(τ_x(T)) = 2 (T + T*)₀`, four times the real
orthogonal projection of `T` onto the trace-free self-adjoint endomorphisms. So `C_x` restricts to
a real isomorphism `Λ⁺_x ≃ {T | T* = T, tr T = 0}` with inverse `τ_x / 4`
(`TauCeti.SpinCStructure.cliffordRestrictionEquiv`). This is the fibrewise form of the
identification of the curvature term `F_A⁺` of the Seiberg–Witten equations with a trace-free
endomorphism of `W⁺`.

The smoothness of these fibre maps along smooth sections is not treated here.

## Main definitions

* `TauCeti.SpinCStructure.cliffordRestrictionAdjoint`: the adjoint `τ_x` of the Clifford map.
* `TauCeti.SpinCStructure.cliffordRestrictionEquiv`: the Clifford isomorphism
  `Λ⁺_x ≃ {T | T* = T, tr T = 0}` on a fibre.

## Main results

* `TauCeti.SpinCStructure.fiberOrientation_map_repr`,
  `TauCeti.SpinCStructure.map_vectorFrame_hodgeStar`: the fibre orientation in a frame, and the
  Hodge stars in a frame.
* `TauCeti.SpinCStructure.cliffordRestriction_hodgeStar`,
  `TauCeti.SpinCStructure.cliffordRestriction_eq_zero_of_hodgeStar_eq_neg`: only the self-dual
  part of a two-form acts on `W⁺_x`.
* `TauCeti.SpinCStructure.trace_cliffordRestriction_mul`,
  `TauCeti.SpinCStructure.trace_adjoint_cliffordRestriction_mul_of_hodgeStar_eq_self`: the trace
  pairing and the Hilbert–Schmidt normalization `tr (C_x(α)* C_x(β)) = 4 ⟪α, β⟫`.
* `TauCeti.SpinCStructure.inner_cliffordRestrictionAdjoint_left`,
  `TauCeti.SpinCStructure.re_trace_adjoint_mul_cliffordRestriction`: the adjunction.
* `TauCeti.SpinCStructure.cliffordRestrictionAdjoint_cliffordRestriction`: `C_x* C_x = 4`.
* `TauCeti.SpinCStructure.cliffordRestriction_cliffordRestrictionAdjoint_eq_traceFreePart`:
  `C_x C_x* = 4` times the projection onto the trace-free self-adjoint endomorphisms.

## References

* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1–§4.1.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Chapter IV, §1 and Appendix D.
-/

public section

noncomputable section

open Bundle MulOpposite Module Module.End TauCeti CliffordAlgebra TauCeti.CliffordAlgebra
open scoped InnerProductSpace

universe w

/-- The proof that the standard form on `ℝ⁴` is nonzero, on which `Spinᶜ(4)` depends. -/
local notation "hpos" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm 4 0)
local notation "SpinC" => spinCGroup (realCliffordForm 4 0) hpos

namespace TauCeti.SpinCStructure

open Orientation.HalfSpinModel

variable {X : Type*} [TopologicalSpace X] {F : Type*} {E : X → Type w}
  [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (finrank ℝ V = 4)] {Q : QuadraticForm ℝ V}
  {o : Orientation ℝ V (Fin 4)} {hQ : ∀ v, Q v = -‖v‖ ^ 2}
  {b : OrthonormalBasis (Fin 4) ℝ V}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)}

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3

/-- The dimension of `V`, in the form taken by the Hodge star of two-forms. -/
local notation "hkl" => (Eq.symm (Fact.out : finrank ℝ V = 4) : 2 + 2 = finrank ℝ V)

/-! ### The fibre orientation and the Hodge star in a frame -/

omit [Fact (finrank ℝ V = 4)] in
/-- **The fibre orientation in a frame**: the orientation of `E x` induced by `s` from the model
orientation `o` of `V`, read through `b`, is `o` pulled back along `κ_p` for every point `p` over
`x`. -/
theorem fiberOrientation_map_repr (s : SpinCStructure F E 4) {x : X} (p : s.P x) :
    s.fiberOrientation (Orientation.map (Fin 4) b.repr.toLinearEquiv o) x =
      Orientation.map (Fin 4) (s.vectorFrame b p).symm.toLinearEquiv o := by
  -- `Spinᶜ(4)` acts on frames through `SO(4)`, by transformations of determinant `1`.
  rw [s.fiberOrientation_eq_map_frameAt
    (fun g ↦ by simp [QuadraticMap.det_coe_specialOrthogonalGroup]) _ p, ← Orientation.map_trans]
  congr 2
  ext v
  simp

variable [∀ x, Fact (finrank ℝ (E x) = 4)]

/-- The dimension `Fact` makes the fibres finite-dimensional. -/
local instance (priority := 100) (x : X) : FiniteDimensional ℝ (E x) := .of_fact_finrank_eq_succ 3

/-- The dimension of the fibre `E x`, in the form taken by the Hodge star of two-forms. -/
local notation "hklE" x =>
  (Eq.symm (Fact.out : finrank ℝ (E x) = 4) : 2 + 2 = finrank ℝ (E x))

/-- The Hodge star of two-forms on the fibre `E x`, for the orientation induced by `s`. -/
local notation "⋆[" s ", " x "]" =>
  Orientation.hodgeStar (OrthonormalFrameLift.fiberOrientation (s : SpinCStructure F E 4)
    (Orientation.map (Fin 4) b.repr.toLinearEquiv o) x) (hklE x)

/-- The self-dual two-forms `Λ⁺_x` on the fibre `E x`. -/
local notation "Λ⁺[" s ", " x "]" =>
  Module.End.eigenspace ((⋆[s, x] : ⋀[ℝ]^2 (E x) ≃ₗ[ℝ] ⋀[ℝ]^2 (E x)) :
    Module.End ℝ (⋀[ℝ]^2 (E x))) 1

/-- The self-dual two-forms `Λ⁺` of the model space `V`. -/
local notation "Λ⁺V" =>
  Module.End.eigenspace (Orientation.hodgeStar o hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1

/-- **The Hodge stars in a frame**: `⋀² κ_p (⋆α) = ⋆ (⋀² κ_p α)` for the Hodge star of the fibre
orientation on `E x` and that of `o` on `V`. -/
theorem map_vectorFrame_hodgeStar (s : SpinCStructure F E 4) {x : X} (p : s.P x)
    (α : ⋀[ℝ]^2 (E x)) :
    exteriorPower.map 2 (s.vectorFrame b p).toLinearMap (⋆[s, x] α) =
      o.hodgeStar hkl (exteriorPower.map 2 (s.vectorFrame b p).toLinearMap α) := by
  set κ := s.vectorFrame b p
  have h := o.hodgeStar_map κ.symm hkl (hklE x) (exteriorPower.map 2 κ.toLinearMap α)
  rw [← fiberOrientation_map_repr s p] at h
  have hκ (y : ⋀[ℝ]^2 (E x)) :
      exteriorPower.map 2 κ.symm.toLinearMap (exteriorPower.map 2 κ.toLinearMap y) = y := by
    simp
  rw [hκ] at h
  rw [h]
  simp

/-- `⋀² κ_p` maps the self-dual forms of `E x` to those of `V`. -/
theorem map_vectorFrame_mem_eigenspace_hodgeStar (s : SpinCStructure F E 4) {x : X}
    (p : s.P x) {α : ⋀[ℝ]^2 (E x)} (hα : α ∈ Λ⁺[s, x]) :
    exteriorPower.map 2 (s.vectorFrame b p).toLinearMap α ∈ Λ⁺V := by
  rw [mem_eigenspace_iff, one_smul, LinearEquiv.coe_coe] at hα ⊢
  rw [← map_vectorFrame_hodgeStar, hα]

/-- `⋀² κ_p⁻¹` maps the self-dual forms of `V` to those of `E x`. -/
theorem map_vectorFrame_symm_mem_eigenspace_hodgeStar (s : SpinCStructure F E 4) {x : X}
    (p : s.P x) {α : ⋀[ℝ]^2 V} (hα : α ∈ Λ⁺V) :
    exteriorPower.map 2 (s.vectorFrame b p).symm.toLinearMap α ∈ Λ⁺[s, x] := by
  set κ := s.vectorFrame b p
  have hκ : exteriorPower.map 2 κ.toLinearMap (exteriorPower.map 2 κ.symm.toLinearMap α) = α := by
    simp
  rw [mem_eigenspace_iff, one_smul, LinearEquiv.coe_coe] at hα ⊢
  apply exteriorPower.map_injective_field κ.injective
  rw [map_vectorFrame_hodgeStar, hκ, hα]

/-! ### The Clifford map on the self-dual forms of a fibre -/

/-- The unitary frame `[p, -] : S⁺ ≃ W⁺_x` given by a point `p` of the principal bundle. -/
local notation "frm" p => LinearIsometryEquiv.trans
  (LinearIsometryEquiv.symm (toPositiveHalfSpinors o hQ b ρ hρ))
  (AssociatedBundle.mkLinearIsometryEquiv ℂ SpinC p)

/-- **Only the self-dual part of a two-form acts on `W⁺_x`**: `C_x(⋆α) = C_x(α)` for the Hodge star
of the fibre orientation. -/
@[simp]
theorem cliffordRestriction_hodgeStar (s : SpinCStructure F E 4) {x : X} (α : ⋀[ℝ]^2 (E x)) :
    s.cliffordRestriction o hQ b ρ hρ x (⋆[s, x] α) = s.cliffordRestriction o hQ b ρ hρ x α := by
  let p : s.P x := Classical.arbitrary _
  rw [cliffordRestriction_eq_conj s p, cliffordRestriction_eq_conj s p, map_vectorFrame_hodgeStar,
    SeibergWitten.cliffordRestriction_hodgeStar o ρ hQ hkl]

/-- **Anti-self-dual two-forms act by zero on `W⁺_x`**: `C_x(α) = 0` when `⋆α = -α`. -/
theorem cliffordRestriction_eq_zero_of_hodgeStar_eq_neg (s : SpinCStructure F E 4) {x : X}
    {α : ⋀[ℝ]^2 (E x)} (hα : ⋆[s, x] α = -α) : s.cliffordRestriction o hQ b ρ hρ x α = 0 := by
  have h := s.cliffordRestriction_hodgeStar (o := o) (hQ := hQ) (b := b) (ρ := ρ) (hρ := hρ) α
  rw [hα, map_neg, neg_eq_iff_add_eq_zero, ← two_smul ℝ, smul_eq_zero] at h
  exact h.resolve_left two_ne_zero

/-- **The trace pairing of the Clifford map on a fibre**:
`tr (C_x(α) C_x(β)) = (⟪α, β⟫ + ⟪⋆α, β⟫) dim W⁺`. -/
theorem trace_cliffordRestriction_mul (s : SpinCStructure F E 4) {x : X}
    (α β : ⋀[ℝ]^2 (E x)) :
    LinearMap.trace ℂ (s.halfSpinorBundle o hQ b ρ hρ 1 x)
        (s.cliffordRestriction o hQ b ρ hρ x α * s.cliffordRestriction o hQ b ρ hρ x β) =
      ((⟪α, β⟫_ℝ + ⟪⋆[s, x] α, β⟫_ℝ : ℝ) : ℂ) * finrank ℂ (positiveHalfSpinors o ρ) := by
  let p : s.P x := Classical.arbitrary _
  have hinner (y z : ⋀[ℝ]^2 (E x)) :
      ⟪exteriorPower.map 2 (s.vectorFrame b p).toLinearMap y,
        exteriorPower.map 2 (s.vectorFrame b p).toLinearMap z⟫_ℝ = ⟪y, z⟫_ℝ :=
    exteriorPower.inner_map_map (s.vectorFrame b p).toLinearIsometry y z
  rw [cliffordRestriction_eq_conj s p, cliffordRestriction_eq_conj s p,
    ← ContinuousLinearMap.toLinearMap_mul, ← map_mul,
    ContinuousLinearEquiv.trace_conjContinuousAlgEquiv,
    ContinuousLinearMap.toLinearMap_mul, SeibergWitten.trace_cliffordRestriction_mul o ρ hQ hkl,
    ← map_vectorFrame_hodgeStar, hinner, hinner]

/-- **The Hilbert–Schmidt normalization of the Clifford map on a fibre**: in complex rank two,
`tr (C_x(α)* C_x(β)) = 4 ⟪α, β⟫` for self-dual `α`. -/
theorem trace_adjoint_cliffordRestriction_mul_of_hodgeStar_eq_self
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) (s : SpinCStructure F E 4) {x : X}
    {α : ⋀[ℝ]^2 (E x)} (hα : ⋆[s, x] α = α) (β : ⋀[ℝ]^2 (E x)) :
    LinearMap.trace ℂ (s.halfSpinorBundle o hQ b ρ hρ 1 x)
        (ContinuousLinearMap.adjoint (s.cliffordRestriction o hQ b ρ hρ x α) *
          s.cliffordRestriction o hQ b ρ hρ x β) =
      4 * (⟪α, β⟫_ℝ : ℂ) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, (s.isSelfAdjoint_cliffordRestriction α).star_eq,
    trace_cliffordRestriction_mul, hα, h₂]
  push_cast
  ring

/-- **The Clifford map is faithful on the self-dual forms of a fibre**: if `W⁺ ≠ 0` and `⋆α = α`,
then `C_x(α) = 0` only for `α = 0`. -/
theorem cliffordRestriction_eq_zero_iff_of_hodgeStar_eq_self
    [Nontrivial (positiveHalfSpinors o ρ)] (s : SpinCStructure F E 4) {x : X}
    {α : ⋀[ℝ]^2 (E x)} (hα : ⋆[s, x] α = α) :
    s.cliffordRestriction o hQ b ρ hρ x α = 0 ↔ α = 0 := by
  let p : s.P x := Classical.arbitrary _
  have hα' : o.hodgeStar hkl (exteriorPower.map 2 (s.vectorFrame b p).toLinearMap α) =
      exteriorPower.map 2 (s.vectorFrame b p).toLinearMap α := by
    rw [← map_vectorFrame_hodgeStar, hα]
  rw [cliffordRestriction_eq_conj s p, EmbeddingLike.map_eq_zero_iff,
    SeibergWitten.cliffordRestriction_eq_zero_iff_of_hodgeStar_eq_self o ρ hQ hkl hα',
    (exteriorPower.map_injective_field (s.vectorFrame b p).injective).eq_iff' (map_zero _)]

/-! ### The adjoint of the Clifford map on a fibre -/

/-- The adjoint `τ` of the model Clifford map, in the frame `p` and carried to the fibre over `x`:
`⋀² κ_p⁻¹ τ([p, -]⁻¹ T [p, -])` is a self-dual form of `E x`. -/
private theorem map_vectorFrame_symm_cliffordRestrictionAdjoint_mem (s : SpinCStructure F E 4)
    {x : X} (p : s.P x)
    (T : s.halfSpinorBundle o hQ b ρ hρ 1 x →L[ℂ] s.halfSpinorBundle o hQ b ρ hρ 1 x) :
    exteriorPower.map 2 (s.vectorFrame b p).symm.toLinearMap
        (SeibergWitten.cliffordRestrictionAdjoint o ρ hkl
          ((ContinuousLinearEquiv.conjContinuousAlgEquiv
            (frm p).toContinuousLinearEquiv).symm T)) ∈ Λ⁺[s, x] :=
  map_vectorFrame_symm_mem_eigenspace_hodgeStar s p (Submodule.coe_mem _)

/-- The frame formula for the adjoint satisfies the defining property of the adjoint, in every
frame `p`. -/
private theorem inner_map_vectorFrame_symm_cliffordRestrictionAdjoint (s : SpinCStructure F E 4)
    {x : X} (p : s.P x)
    (T : s.halfSpinorBundle o hQ b ρ hρ 1 x →L[ℂ] s.halfSpinorBundle o hQ b ρ hρ 1 x)
    (β : Λ⁺[s, x]) :
    ⟪exteriorPower.map 2 (s.vectorFrame b p).symm.toLinearMap
        (SeibergWitten.cliffordRestrictionAdjoint o ρ hkl
          ((ContinuousLinearEquiv.conjContinuousAlgEquiv
            (frm p).toContinuousLinearEquiv).symm T)), (β : ⋀[ℝ]^2 (E x))⟫_ℝ =
      (LinearMap.trace ℂ (s.halfSpinorBundle o hQ b ρ hρ 1 x)
        (T * s.cliffordRestriction o hQ b ρ hρ x β)).re := by
  set κ := s.vectorFrame b p
  set e := ContinuousLinearEquiv.conjContinuousAlgEquiv (frm p).toContinuousLinearEquiv
  set τT := SeibergWitten.cliffordRestrictionAdjoint o ρ hkl (e.symm T)
  have hβ := map_vectorFrame_mem_eigenspace_hodgeStar s p β.property
  set β' : Λ⁺V := ⟨_, hβ⟩
  -- Move `⋀² κ_p⁻¹` across the inner product, then use the model adjunction.
  have hinner (y z : ⋀[ℝ]^2 (E x)) :
      ⟪exteriorPower.map 2 κ.toLinearMap y, exteriorPower.map 2 κ.toLinearMap z⟫_ℝ = ⟪y, z⟫_ℝ :=
    exteriorPower.inner_map_map κ.toLinearIsometry y z
  have hκ : exteriorPower.map 2 κ.toLinearMap
      (exteriorPower.map 2 κ.symm.toLinearMap (τT : ⋀[ℝ]^2 V)) = τT :=
    exteriorPower.map_map_symm κ.toLinearEquiv _
  have hmul : T * s.cliffordRestriction o hQ b ρ hρ x β =
      e (e.symm T * SeibergWitten.cliffordRestriction o ρ β') := by
    rw [map_mul, e.apply_symm_apply, cliffordRestriction_eq_conj s p]
  rw [← hinner, hκ, ← ContinuousLinearMap.toLinearMap_mul,
    hmul, ContinuousLinearEquiv.trace_conjContinuousAlgEquiv, ContinuousLinearMap.toLinearMap_mul,
    ← SeibergWitten.inner_cliffordRestrictionAdjoint_left o ρ hkl (e.symm T) β',
    Submodule.coe_inner]

variable (o hQ b ρ hρ) in
/-- **The adjoint `τ_x = C_x*` of the Clifford map on a fibre**, for the real Hilbert–Schmidt
pairing `Re tr (T* U)` on the complex endomorphisms of `W⁺_x`: the self-dual form `τ_x(T)` of `E x`
is characterized by `⟪τ_x(T), β⟫ = Re tr (T C_x(β))`
(`TauCeti.SpinCStructure.inner_cliffordRestrictionAdjoint_left`). In a frame `p` it is the model
adjoint `TauCeti.SeibergWitten.cliffordRestrictionAdjoint` carried by `⋀² κ_p⁻¹` and the unitary
frame `[p, -]` (`TauCeti.SpinCStructure.coe_cliffordRestrictionAdjoint_eq`); it is defined in a
chosen frame. -/
def cliffordRestrictionAdjoint (s : SpinCStructure F E 4) (x : X) :
    (s.halfSpinorBundle o hQ b ρ hρ 1 x →L[ℂ] s.halfSpinorBundle o hQ b ρ hρ 1 x) →L[ℝ]
      Λ⁺[s, x] :=
  let p : s.P x := Classical.arbitrary _
  haveI : FiniteDimensional ℝ
      (s.halfSpinorBundle o hQ b ρ hρ 1 x →L[ℂ] s.halfSpinorBundle o hQ b ρ hρ 1 x) :=
    Module.Finite.trans ℂ _
  -- Instance search does not find the real scalar action on these endomorphisms directly; it
  -- does for a general complex inner product space.
  haveI : ContinuousSMul ℝ
      (s.halfSpinorBundle o hQ b ρ hρ 1 x →L[ℂ] s.halfSpinorBundle o hQ b ρ hρ 1 x) :=
    (fun (H : Type _) [NormedAddCommGroup H] [InnerProductSpace ℂ H] ↦
      (inferInstance : ContinuousSMul ℝ (H →L[ℂ] H))) _
  LinearMap.toContinuousLinearMap
    { toFun T := ⟨_, map_vectorFrame_symm_cliffordRestrictionAdjoint_mem s p T⟩
      map_add' T T' := by
        ext
        simp
      map_smul' r T := by
        ext
        -- The real scalars act through the complex ones, for which `[p, -]` is linear.
        have := LinearMapClass.map_smul_of_tower (R := ℝ) (S := ℂ)
          (ContinuousLinearEquiv.conjContinuousAlgEquiv (frm p).toContinuousLinearEquiv).symm r T
        simp only [this]
        simp }

/-- **The defining property of the adjoint**: `⟪τ_x(T), β⟫ = Re tr (T C_x(β))` for every
self-dual `β`. -/
theorem inner_cliffordRestrictionAdjoint_left (s : SpinCStructure F E 4) {x : X}
    (T : s.halfSpinorBundle o hQ b ρ hρ 1 x →L[ℂ] s.halfSpinorBundle o hQ b ρ hρ 1 x)
    (β : Λ⁺[s, x]) :
    ⟪s.cliffordRestrictionAdjoint o hQ b ρ hρ x T, β⟫_ℝ =
      (LinearMap.trace ℂ (s.halfSpinorBundle o hQ b ρ hρ 1 x)
        (T * s.cliffordRestriction o hQ b ρ hρ x β)).re :=
  inner_map_vectorFrame_symm_cliffordRestrictionAdjoint s _ T β

/-- **The adjoint in a frame**: for every point `p` over `x`,
`τ_x(T) = ⋀² κ_p⁻¹ τ([p, -]⁻¹ T [p, -])`. -/
theorem coe_cliffordRestrictionAdjoint_eq (s : SpinCStructure F E 4) {x : X} (p : s.P x)
    (T : s.halfSpinorBundle o hQ b ρ hρ 1 x →L[ℂ] s.halfSpinorBundle o hQ b ρ hρ 1 x) :
    (s.cliffordRestrictionAdjoint o hQ b ρ hρ x T : ⋀[ℝ]^2 (E x)) =
      exteriorPower.map 2 (s.vectorFrame b p).symm.toLinearMap
        (SeibergWitten.cliffordRestrictionAdjoint o ρ hkl
          ((ContinuousLinearEquiv.conjContinuousAlgEquiv
            (frm p).toContinuousLinearEquiv).symm T)) := by
  suffices h : s.cliffordRestrictionAdjoint o hQ b ρ hρ x T =
      ⟨_, map_vectorFrame_symm_cliffordRestrictionAdjoint_mem s p T⟩ from
    congrArg Subtype.val h
  refine ext_inner_right ℝ fun β ↦ ?_
  rw [inner_cliffordRestrictionAdjoint_left, Submodule.coe_inner,
    inner_map_vectorFrame_symm_cliffordRestrictionAdjoint]

/-- `τ_x` is the adjoint of `C_x` for the real Hilbert–Schmidt pairing:
`Re tr (T* C_x(β)) = ⟪τ_x(T), β⟫`. -/
theorem re_trace_adjoint_mul_cliffordRestriction (s : SpinCStructure F E 4) {x : X}
    (T : s.halfSpinorBundle o hQ b ρ hρ 1 x →L[ℂ] s.halfSpinorBundle o hQ b ρ hρ 1 x)
    (β : Λ⁺[s, x]) :
    (LinearMap.trace ℂ (s.halfSpinorBundle o hQ b ρ hρ 1 x)
        (ContinuousLinearMap.adjoint T * s.cliffordRestriction o hQ b ρ hρ x β)).re =
      ⟪s.cliffordRestrictionAdjoint o hQ b ρ hρ x T, β⟫_ℝ := by
  let p : s.P x := Classical.arbitrary _
  set e := ContinuousLinearEquiv.conjContinuousAlgEquiv (frm p).toContinuousLinearEquiv
  -- In the frame `p`, write `T = e T₀`; both sides are then those of the model statement for `T₀`,
  -- because `e` preserves traces and, `[p, -]` being unitary, commutes with adjoints.
  obtain ⟨T₀, rfl⟩ := e.surjective T
  rw [inner_cliffordRestrictionAdjoint_left, cliffordRestriction_eq_conj s p,
    LinearIsometryEquiv.adjoint_conjContinuousAlgEquiv,
    ← ContinuousLinearMap.toLinearMap_mul, ← map_mul, ← ContinuousLinearMap.toLinearMap_mul,
    ← map_mul, ContinuousLinearEquiv.trace_conjContinuousAlgEquiv,
    ContinuousLinearEquiv.trace_conjContinuousAlgEquiv, ContinuousLinearMap.toLinearMap_mul,
    ContinuousLinearMap.toLinearMap_mul]
  have hβ := map_vectorFrame_mem_eigenspace_hodgeStar s p β.property
  exact (SeibergWitten.re_trace_adjoint_mul_cliffordRestriction o hρ hkl T₀ ⟨_, hβ⟩).trans
    (SeibergWitten.inner_cliffordRestrictionAdjoint_left o ρ hkl T₀ ⟨_, hβ⟩)

/-- `τ_x` kills the complex scalars: `τ_x(c Id) = 0`. -/
@[simp]
theorem cliffordRestrictionAdjoint_smul_one (s : SpinCStructure F E 4) {x : X} (c : ℂ) :
    s.cliffordRestrictionAdjoint o hQ b ρ hρ x (c • 1) = 0 := by
  -- In a frame this is the model statement `τ(c Id) = 0`, as the frame conjugation is unital.
  ext1
  rw [coe_cliffordRestrictionAdjoint_eq s (Classical.arbitrary _), map_smul, map_one,
    SeibergWitten.cliffordRestrictionAdjoint_smul_one o ρ hQ hkl, ZeroMemClass.coe_zero, map_zero,
    ZeroMemClass.coe_zero]

/-- `τ_x` kills the scalars: `τ_x(Id) = 0`. -/
@[simp]
theorem cliffordRestrictionAdjoint_one (s : SpinCStructure F E 4) {x : X} :
    s.cliffordRestrictionAdjoint o hQ b ρ hρ x 1 = 0 := by
  simpa using s.cliffordRestrictionAdjoint_smul_one (o := o) (hQ := hQ) (b := b) (ρ := ρ)
    (hρ := hρ) (x := x) 1

/-- **`C_x* C_x = 4`**: in complex rank two, `τ_x(C_x(α)) = 4 α` for self-dual `α`. -/
theorem cliffordRestrictionAdjoint_cliffordRestriction
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) (s : SpinCStructure F E 4) {x : X}
    (α : Λ⁺[s, x]) :
    s.cliffordRestrictionAdjoint o hQ b ρ hρ x (s.cliffordRestriction o hQ b ρ hρ x α) =
      (4 : ℝ) • α := by
  let p : s.P x := Classical.arbitrary _
  -- In the frame `p` this is the model statement `τ(C(iα)) = 4 α` for the self-dual `⋀² κ_p α`.
  ext1
  rw [coe_cliffordRestrictionAdjoint_eq s p, cliffordRestriction_eq_conj s p,
    ContinuousAlgEquiv.symm_apply_apply,
    SeibergWitten.cliffordRestrictionAdjoint_cliffordRestriction o ρ hQ hkl h₂
      ⟨_, map_vectorFrame_mem_eigenspace_hodgeStar s p α.property⟩,
    Submodule.coe_smul, Submodule.coe_smul, map_smul]
  simp

/-! ### The Clifford isomorphism on a fibre -/

omit [∀ x, Fact (finrank ℝ (E x) = 4)] in
/-- `C_x(α)` is a trace-free self-adjoint endomorphism of `W⁺_x`. -/
theorem cliffordRestriction_mem_traceFreeSelfAdjoint (s : SpinCStructure F E 4) {x : X}
    (α : ⋀[ℝ]^2 (E x)) :
    s.cliffordRestriction o hQ b ρ hρ x α ∈
      traceFreeSelfAdjoint (s.halfSpinorBundle o hQ b ρ hρ 1 x) :=
  mem_traceFreeSelfAdjoint.2
    ⟨s.isSelfAdjoint_cliffordRestriction α, s.trace_cliffordRestriction α⟩

/-- The Clifford map on the self-dual forms of a fibre, with values in the trace-free self-adjoint
endomorphisms of `W⁺_x`. -/
private def cliffordSelfDual (s : SpinCStructure F E 4) (x : X) :
    Λ⁺[s, x] →ₗ[ℝ] traceFreeSelfAdjoint (s.halfSpinorBundle o hQ b ρ hρ 1 x) :=
  ((s.cliffordRestriction o hQ b ρ hρ x).domRestrict _).codRestrict _ fun α ↦
    s.cliffordRestriction_mem_traceFreeSelfAdjoint (α : ⋀[ℝ]^2 (E x))

private theorem coe_cliffordSelfDual_apply (s : SpinCStructure F E 4) {x : X}
    (α : Λ⁺[s, x]) :
    (s.cliffordSelfDual (o := o) (hQ := hQ) (b := b) (ρ := ρ) (hρ := hρ) x α :
        s.halfSpinorBundle o hQ b ρ hρ 1 x →L[ℂ] s.halfSpinorBundle o hQ b ρ hρ 1 x) =
      s.cliffordRestriction o hQ b ρ hρ x α :=
  (rfl)

private theorem bijective_cliffordSelfDual (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (s : SpinCStructure F E 4) (x : X) :
    Function.Bijective (s.cliffordSelfDual (o := o) (hQ := hQ) (b := b) (ρ := ρ) (hρ := hρ) x) := by
  -- `C_x` is injective on `Λ⁺_x` because `C_x* C_x = 4`, and both sides have real dimension three.
  have hinj : Function.Injective
      (s.cliffordSelfDual (o := o) (hQ := hQ) (b := b) (ρ := ρ) (hρ := hρ) x) := by
    refine (injective_iff_map_eq_zero _).2 fun α hα ↦ ?_
    have h := s.cliffordRestrictionAdjoint_cliffordRestriction (hQ := hQ) (b := b) (hρ := hρ) h₂ α
    rw [← coe_cliffordSelfDual_apply, hα, ZeroMemClass.coe_zero, ContinuousLinearMap.map_zero,
      eq_comm, smul_eq_zero] at h
    exact h.resolve_left four_ne_zero
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩
  have h₃ := Orientation.two_mul_finrank_eigenspace_hodgeStar_one
    (s.fiberOrientation (Orientation.map (Fin 4) b.repr.toLinearEquiv o) x) even_two two_pos
    (hklE x)
  rw [finrank_traceFreeSelfAdjoint, finrank_halfSpinorBundle, ← positiveHalfSpinors_eq_eigenspace,
    h₂]
  norm_num [Nat.choose] at h₃ ⊢
  omega

variable (o hQ b ρ hρ) in
/-- **The Clifford isomorphism on a fibre**
`C_x : iΛ⁺_x ≃ {T : W⁺_x → W⁺_x | T* = T, tr T = 0}`, indexed by real self-dual two-forms of
`E x`, when the positive half-spinors have complex dimension two: it sends `α` to
`C_x(α) = C(iα)`. Its inverse is `τ_x / 4`
(`TauCeti.SpinCStructure.cliffordRestrictionEquiv_symm_apply`). -/
def cliffordRestrictionEquiv (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (s : SpinCStructure F E 4) (x : X) :
    Λ⁺[s, x] ≃ₗ[ℝ] traceFreeSelfAdjoint (s.halfSpinorBundle o hQ b ρ hρ 1 x) :=
  LinearEquiv.ofBijective (s.cliffordSelfDual x) (bijective_cliffordSelfDual h₂ s x)

/-- The Clifford isomorphism sends a self-dual `α` to `C_x(α)`. -/
@[simp]
theorem coe_cliffordRestrictionEquiv_apply (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (s : SpinCStructure F E 4) {x : X} (α : Λ⁺[s, x]) :
    (s.cliffordRestrictionEquiv o hQ b ρ hρ h₂ x α :
        s.halfSpinorBundle o hQ b ρ hρ 1 x →L[ℂ] s.halfSpinorBundle o hQ b ρ hρ 1 x) =
      s.cliffordRestriction o hQ b ρ hρ x α :=
  coe_cliffordSelfDual_apply s α

/-- **`C_x C_x*` is `4` times the orthogonal projection onto the trace-free self-adjoint
endomorphisms**: in complex rank two, `C_x(τ_x(T)) = 2 (T + T*)₀ = 4 ((T + T*) / 2)₀`, where `U₀`
is the trace-free part of `U`. -/
theorem cliffordRestriction_cliffordRestrictionAdjoint_eq_traceFreePart
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) (s : SpinCStructure F E 4) {x : X}
    (T : s.halfSpinorBundle o hQ b ρ hρ 1 x →L[ℂ] s.halfSpinorBundle o hQ b ρ hρ 1 x) :
    s.cliffordRestriction o hQ b ρ hρ x (s.cliffordRestrictionAdjoint o hQ b ρ hρ x T) =
      (2 : ℝ) • traceFreePart ℂ (s.halfSpinorBundle o hQ b ρ hρ 1 x)
        (T + ContinuousLinearMap.adjoint T) := by
  let p : s.P x := Classical.arbitrary _
  set e := ContinuousLinearEquiv.conjContinuousAlgEquiv (frm p).toContinuousLinearEquiv
  -- In the frame `p`, write `T = e T₀` and carry the model statement for `T₀` along `e`. It
  -- commutes with adjoints, as `[p, -]` is unitary, and with trace-free parts, as it is unital and
  -- preserves traces.
  obtain ⟨T₀, rfl⟩ := e.surjective T
  rw [coe_cliffordRestrictionAdjoint_eq s p, cliffordRestriction_eq_conj s p,
    LinearIsometryEquiv.adjoint_conjContinuousAlgEquiv, ← map_add,
    ContinuousLinearEquiv.traceFreePart_conjContinuousAlgEquiv,
    ← LinearMapClass.map_smul_of_tower (R := ℝ) (S := ℂ) e, e.symm_apply_apply,
    ← SeibergWitten.cliffordRestriction_cliffordRestrictionAdjoint_eq_traceFreePart o hQ hρ hkl h₂]
  simp [e]

/-- **`C_x C_x* = 4` on the trace-free self-adjoint endomorphisms**: in complex rank two,
`C_x(τ_x(T)) = 4 T` when `T* = T` and `tr T = 0`. -/
theorem cliffordRestriction_cliffordRestrictionAdjoint_of_mem_traceFreeSelfAdjoint
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) (s : SpinCStructure F E 4) {x : X}
    {T : s.halfSpinorBundle o hQ b ρ hρ 1 x →L[ℂ] s.halfSpinorBundle o hQ b ρ hρ 1 x}
    (hT : T ∈ traceFreeSelfAdjoint (s.halfSpinorBundle o hQ b ρ hρ 1 x)) :
    s.cliffordRestriction o hQ b ρ hρ x (s.cliffordRestrictionAdjoint o hQ b ρ hρ x T) =
      (4 : ℝ) • T := by
  -- Here `T + T* = T + T` is already trace free.
  rw [cliffordRestriction_cliffordRestrictionAdjoint_eq_traceFreePart h₂,
    ← ContinuousLinearMap.star_eq_adjoint, (mem_traceFreeSelfAdjoint.1 hT).1.star_eq, map_add,
    traceFreePart_of_trace_eq_zero (mem_traceFreeSelfAdjoint.1 hT).2]
  module

/-- The inverse of the Clifford isomorphism is `τ_x / 4`. -/
@[simp]
theorem cliffordRestrictionEquiv_symm_apply (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (s : SpinCStructure F E 4) {x : X}
    (T : traceFreeSelfAdjoint (s.halfSpinorBundle o hQ b ρ hρ 1 x)) :
    (s.cliffordRestrictionEquiv o hQ b ρ hρ h₂ x).symm T =
      (4 : ℝ)⁻¹ • s.cliffordRestrictionAdjoint o hQ b ρ hρ x T := by
  rw [LinearEquiv.symm_apply_eq]
  ext1
  rw [coe_cliffordRestrictionEquiv_apply, Submodule.coe_smul, map_smul,
    cliffordRestriction_cliffordRestrictionAdjoint_of_mem_traceFreeSelfAdjoint h₂ s T.property,
    smul_smul]
  norm_num

end TauCeti.SpinCStructure
