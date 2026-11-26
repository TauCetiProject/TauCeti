/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.Naturality
public import TauCeti.Topology.VectorBundle.SpinStructure.Spinor
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# The Clifford map and the quadratic two-form on the half-spinors of a `Spinᶜ` structure

Let `s` be a `Spinᶜ` structure on a real vector bundle `E → X` of rank four with fibre inner
products, and let `W⁺ = s.halfSpinorBundle o hQ b ρ hρ 1` be its positive half-spinor bundle
(`TauCeti.SpinCStructure.halfSpinorBundle`). Pointwise on a model Hermitian Clifford module, the
curvature equation `F_A⁺ = q(ψ) + η` of the Seiberg–Witten equations uses two maps:

* the Clifford map `C : α ↦ C(iα) = i c₂(α)` from two-forms to endomorphisms of the positive
  half-spinors (`TauCeti.SeibergWitten.cliffordRestriction`);
* the quadratic two-form `q(ψ) = C⁻¹ Q₀(ψ)`, a self-dual two-form with `C(q(ψ)) = Q₀(ψ)`, where
  `Q₀(ψ) = ψψ* - (‖ψ‖² / 2) Id` (`TauCeti.SeibergWitten.quadraticTwoForm`).

This file assembles them into fibrewise maps of the bundles of a `Spinᶜ` structure:

* `TauCeti.SpinCStructure.cliffordRestriction`: the real-linear map
  `C_x : ⋀² (E x) → End_ℂ (W⁺_x)`;
* `TauCeti.SpinCStructure.quadraticTwoForm`: the real-quadratic map `q_x : W⁺_x → ⋀² (E x)`.

A point `p` of the principal bundle over `x` is a unitary frame `[p, -] : S⁺ ≃ W⁺_x` and gives the
linear isometry `κ_p : E x ≃ V` (`TauCeti.SpinCStructure.vectorFrame`). In this frame `C_x` is
`C` transported by `⋀² κ_p` and `[p, -]` (`TauCeti.SpinCStructure.cliffordRestriction_mk`), and
`q_x` is `q` transported by `[p, -]⁻¹` and `⋀² κ_p⁻¹`
(`TauCeti.SpinCStructure.quadraticTwoForm_mk`).
Neither depends on `p`. Changing `p` to `p • g` changes the spinor frame by the half-spin
representation of `g` and the vector frame by its rotation, and `C` and `q` are equivariant for
this pair (`Orientation.HalfSpinModel.cliffordRestriction_map_toPositiveHalfSpinors_smul`,
`Orientation.HalfSpinModel.quadraticTwoForm_toPositiveHalfSpinors_smul`), because `[s, z]` acts
on the whole Clifford module by the unitary `z ρ(s)`, which intertwines Clifford multiplication
with the rotation of `s` (`TauCeti.SeibergWitten.cliffordRestriction_map`,
`TauCeti.SeibergWitten.quadraticTwoForm_positiveHalfSpinorsEquiv`).

The pointwise algebra of `C` and `q` then holds on every fibre: `C_x(q_x(ψ)) = Q₀(ψ)`, so
`C_x(q_x(ψ)) ψ = (‖ψ‖² / 2) ψ`; `q_x(c ψ) = |c|² q_x(ψ)`, so `q_x` is invariant under unit
phases, which is the invariance `q(u ψ) = q(ψ)` under gauge transformations `u : X → U(1)`;
`‖q_x(ψ)‖² = ‖ψ‖⁴ / 8`; each `C_x(α)` is self-adjoint and trace free; and on the wedge of
orthogonal vectors `C_x(a ∧ b) = i c(a) c(b)` is a product of Clifford multiplications
(`TauCeti.SpinCStructure.cliffordMul`).

The self-dual subbundle of `⋀² E` for the orientation chosen by `s`, and the smoothness of `C_x`
and `q_x` along smooth sections, are not constructed here.

## Main definitions

* `Orientation.HalfSpinModel.toPositiveHalfSpinors`: the model half-spinors `S⁺` as the positive
  half-spinors of the model Clifford module.
* `TauCeti.SpinCStructure.cliffordRestriction`: the Clifford map `C_x` on the fibre over `x`.
* `TauCeti.SpinCStructure.quadraticTwoForm`: the quadratic two-form `q_x` on the fibre over `x`.

## Main results

* `TauCeti.SpinCStructure.cliffordRestriction_mk`, `TauCeti.SpinCStructure.quadraticTwoForm_mk`:
  `C_x` and `q_x` in every frame.
* `TauCeti.SpinCStructure.cliffordRestriction_eq_conj`: `C_x(α)` is the model `C(i ⋀² κ_p α)`
  conjugated by the unitary frame `[p, -]`.
* `TauCeti.SpinCStructure.cliffordRestriction_quadraticTwoForm`: `C_x(q_x(ψ)) = Q₀(ψ)`.
* `TauCeti.SpinCStructure.quadraticTwoForm_smul_of_norm_eq_one`: `q_x(u ψ) = q_x(ψ)` for `|u| = 1`.
* `TauCeti.SpinCStructure.norm_quadraticTwoForm_sq`: `‖q_x(ψ)‖² = ‖ψ‖⁴ / 8`.
* `TauCeti.SpinCStructure.cliffordRestriction_ιMulti_apply_of_inner_eq_zero`:
  `C_x(a ∧ b) ψ = i c(a) c(b) ψ` for `⟪a, b⟫ = 0`.

## References

* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1–§4.1.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Appendix D.
-/

public section

noncomputable section

open Bundle MulOpposite Module Module.End TauCeti CliffordAlgebra TauCeti.CliffordAlgebra
open scoped InnerProductSpace

universe w

/-- The proof that the standard form on `ℝ⁴` is nonzero, on which `Spinᶜ(4)` depends. -/
local notation "hpos" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm 4 0)
local notation "SpinC" => spinCGroup (realCliffordForm 4 0) hpos

/-! ### Equivariance on the model half-spinors -/

namespace Orientation.HalfSpinModel

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
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

/-- The rotation of `V` by `g ∈ Spinᶜ(4)`, read through the orthonormal basis `b`: the rotation
of the corresponding element of the `Spinᶜ` group of `Q`. -/
local notation "rot" g => ((spinCGroup.toSpecialOrthogonal Q (b.ne_zero_of_neg_norm_sq hQ)
  (b.realSpinCGroupHom hQ hpos (b.ne_zero_of_neg_norm_sq hQ) g) : V ≃ₗ[ℝ] V))

variable (o hQ b ρ hρ) in
/-- The model positive half-spinors `S⁺` as the positive half-spinors of the model Clifford
module, the domain of the Clifford map `TauCeti.SeibergWitten.cliffordRestriction`. -/
def toPositiveHalfSpinors : o.HalfSpinModel hQ b ρ hρ 1 ≃ₗᵢ[ℂ] positiveHalfSpinors o ρ :=
  toEigenspace.trans (LinearIsometryEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ).symm)

/-- `toPositiveHalfSpinors` does not change the underlying vector of `W`. -/
@[simp]
theorem coe_toPositiveHalfSpinors (ψ : o.HalfSpinModel hQ b ρ hρ 1) :
    (toPositiveHalfSpinors o hQ b ρ hρ ψ : W) = toEigenspace ψ :=
  (rfl)

/-- `g ∈ Spinᶜ(4)` acts on the whole Clifford module by a unitary `U` which intertwines Clifford
multiplication with its rotation `f`, an orientation-preserving isometry of `V`, and restricts to
its action on `S⁺`. For `g = [s, z]`, `U = z ρ(s)`. -/
private theorem exists_intertwiner (g : SpinC) :
    ∃ (f : V ≃ₗᵢ[ℝ] V) (U : W ≃ₗᵢ[ℂ] W) (ho : o.map (Fin 4) f.toLinearEquiv = o)
      (hU : ∀ v, U.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
        ρ (ι Q (f v)) ∘ₗ U.toLinearEquiv.toLinearMap),
      f.toLinearEquiv = (rot g) ∧
      ∀ ψ : o.HalfSpinModel hQ b ρ hρ 1, toPositiveHalfSpinors o hQ b ρ hρ (g • ψ) =
        positiveHalfSpinorsEquiv o ρ o ρ U.toLinearEquiv (comp_chirality_eq_chirality_comp ho hU)
          (toPositiveHalfSpinors o hQ b ρ hρ ψ) := by
  obtain ⟨⟨s, z⟩, hx⟩ := spinCGroup.mk_surjective Q (b.ne_zero_of_neg_norm_sq hQ)
    (b.realSpinCGroupHom hQ hpos (b.ne_zero_of_neg_norm_sq hQ) g)
  -- The rotation of `g` is the vector action of `s`; it preserves `Q`, hence the norm.
  have hA (v : V) : (rot g) v = spinVectorAction Q s v := by
    rw [← hx, spinCGroup.toSpecialOrthogonal_mk, coe_spinToSpecialOrthogonal_apply]
  have hAnorm (v : V) : ‖(rot g) v‖ = ‖v‖ := by
    have h := spinVectorAction_map_app Q s v
    rw [← hA, hQ, hQ, neg_inj] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h
  let f : V ≃ₗᵢ[ℝ] V := { (rot g) with norm_map' := hAnorm }
  -- `ρ(s)` is unitary, since `s* s = 1`.
  have hs (w : W) : ‖ρ s w‖ = ‖w‖ := by
    rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ,
      inner_map_apply_map_apply_of_mem_spinGroup hρ s.property]
  let li : W →ₗᵢ[ℂ] W :=
    { toLinearMap := (z : ℂ) • ρ s
      norm_map' w := by rw [LinearMap.smul_apply, norm_smul, Circle.norm_coe, one_mul, hs] }
  let U : W ≃ₗᵢ[ℂ] W := li.toLinearIsometryEquiv rfl
  have ho : o.map (Fin 4) f.toLinearEquiv = o := by
    -- `f` is special orthogonal, so it has determinant one.
    rw [Orientation.map_eq_iff_det_pos _ _
      (by rw [Fintype.card_fin]; exact (Fact.out : finrank ℝ V = 4).symm), ← LinearEquiv.coe_det]
    have h := QuadraticMap.det_coe_specialOrthogonalGroup (spinCGroup.toSpecialOrthogonal Q
      (b.ne_zero_of_neg_norm_sq hQ) (b.realSpinCGroupHom hQ hpos (b.ne_zero_of_neg_norm_sq hQ) g))
    simp [f, h]
  have hU (v : V) : U.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
      ρ (ι Q (f v)) ∘ₗ U.toLinearEquiv.toLinearMap := by
    -- `ι (s v) s = s ι v` in the Clifford algebra.
    ext w
    have h := LinearMap.congr_fun (congrArg ρ (ι_spinVectorAction_apply_mul Q s v)) w
    rw [map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp] at h
    simp [U, li, f, hA, h, -ι_spinVectorAction_apply]
  refine ⟨f, U, ho, hU, rfl, fun ψ ↦ Subtype.ext ?_⟩
  rw [coe_toPositiveHalfSpinors, toEigenspace_smul, realSpinCHalfSpinSmoothHom_apply o hQ b ρ 1
    (b.ne_zero_of_neg_norm_sq hQ), ← hx]
  simp [U, li]

/-- **Clifford equivariance of the Clifford map on the model half-spinors**: `g ∈ Spinᶜ(4)`
intertwines `C(iα)` with `C(i ⋀²π(g) α)`, where `π(g)` is its rotation of `V`:
`C(i ⋀²π(g) α) (g • ψ) = g • (C(iα) ψ)`. -/
theorem cliffordRestriction_map_toPositiveHalfSpinors_smul (g : SpinC) (α : ⋀[ℝ]^2 V)
    (ψ : o.HalfSpinModel hQ b ρ hρ 1) :
    SeibergWitten.cliffordRestriction o ρ (exteriorPower.map 2 (rot g).toLinearMap α)
        (toPositiveHalfSpinors o hQ b ρ hρ (g • ψ)) =
      toPositiveHalfSpinors o hQ b ρ hρ (g • (toPositiveHalfSpinors o hQ b ρ hρ).symm
        (SeibergWitten.cliffordRestriction o ρ α (toPositiveHalfSpinors o hQ b ρ hρ ψ))) := by
  obtain ⟨f, U, ho, hU, hf, he⟩ := exists_intertwiner (o := o) (hρ := hρ) g
  have h := SeibergWitten.cliffordRestriction_map ho hU α
  rw [hf] at h
  rw [h, he, he]
  simp

/-- **`Spinᶜ` equivariance of the quadratic two-form on the model half-spinors**:
`q(g • ψ) = ⋀²π(g) q(ψ)`, where `π(g)` is the rotation of `V` by `g ∈ Spinᶜ(4)`. -/
theorem quadraticTwoForm_toPositiveHalfSpinors_smul (g : SpinC)
    (ψ : o.HalfSpinModel hQ b ρ hρ 1) :
    (SeibergWitten.quadraticTwoForm o ρ hkl (toPositiveHalfSpinors o hQ b ρ hρ (g • ψ)) :
        ⋀[ℝ]^2 V) =
      exteriorPower.map 2 (rot g).toLinearMap
        (SeibergWitten.quadraticTwoForm o ρ hkl (toPositiveHalfSpinors o hQ b ρ hρ ψ)) := by
  obtain ⟨f, U, ho, hU, hf, he⟩ := exists_intertwiner (o := o) (hρ := hρ) g
  have h := SeibergWitten.quadraticTwoForm_positiveHalfSpinorsEquiv ho hU hkl hkl
    (toPositiveHalfSpinors o hQ b ρ hρ ψ)
  rw [hf] at h
  rw [he, h]

end Orientation.HalfSpinModel

/-! ### The Clifford map and the quadratic two-form on the fibres -/

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

/-- The rotation of `V` by `g ∈ Spinᶜ(4)`, read through the orthonormal basis `b`. -/
local notation "rot" g => ((spinCGroup.toSpecialOrthogonal Q (b.ne_zero_of_neg_norm_sq hQ)
  (b.realSpinCGroupHom hQ hpos (b.ne_zero_of_neg_norm_sq hQ) g) : V ≃ₗ[ℝ] V))

omit [Fact (finrank ℝ V = 4)] in
/-- The two-form frame `⋀² κ_p` of `p • g` is that of `p` followed by `⋀² π(g)⁻¹`. -/
private theorem map_vectorFrame_eq (s : SpinCStructure F E 4) {x : X} (p : s.P x) (g : SpinC) :
    exteriorPower.map 2 (s.vectorFrame b p).toLinearMap =
      exteriorPower.map 2 (rot g).toLinearMap ∘ₗ
        exteriorPower.map 2 (s.vectorFrame b (op g • p)).toLinearMap := by
  rw [← exteriorPower.map_comp]
  congr 1
  ext v
  exact vectorFrame_eq_toSpecialOrthogonal_vectorFrame_smul s p g v

variable (o hQ b ρ hρ) in
/-- **The Clifford map** `C_x : ⋀² (E x) → End_ℂ (W⁺_x)` on the positive half-spinors of a
`Spinᶜ` structure of rank four: in a frame `p` it is the Clifford map `α ↦ C(iα) = i c₂(α)` of the
model (`TauCeti.SeibergWitten.cliffordRestriction`) applied to `⋀² κ_p α`
(`TauCeti.SpinCStructure.cliffordRestriction_mk`), which does not depend on `p`. It is defined in a
chosen frame. -/
def cliffordRestriction (s : SpinCStructure F E 4) (x : X) :
    ⋀[ℝ]^2 (E x) →ₗ[ℝ]
      (s.halfSpinorBundle o hQ b ρ hρ 1 x →L[ℂ] s.halfSpinorBundle o hQ b ρ hρ 1 x) :=
  let p : s.P x := Classical.arbitrary _
  let e := ((toPositiveHalfSpinors o hQ b ρ hρ).symm.trans
    (AssociatedBundle.mkLinearIsometryEquiv ℂ SpinC p)).toContinuousLinearEquiv
  (e.conjContinuousAlgEquiv.toAlgEquiv.toLinearMap.restrictScalars ℝ) ∘ₗ
    SeibergWitten.cliffordRestriction o ρ ∘ₗ exteriorPower.map 2 (s.vectorFrame b p).toLinearMap

/-- **The Clifford map in a frame**: `C_x(α) [p, ψ] = [p, C(i ⋀² κ_p α) ψ]` for every point `p`
of the principal bundle over `x`. -/
@[simp]
theorem cliffordRestriction_mk (s : SpinCStructure F E 4) {x : X} (p : s.P x) (α : ⋀[ℝ]^2 (E x))
    (ψ : o.HalfSpinModel hQ b ρ hρ 1) :
    s.cliffordRestriction o hQ b ρ hρ x α (AssociatedBundle.mk SpinC p ψ) =
      AssociatedBundle.mk SpinC p ((toPositiveHalfSpinors o hQ b ρ hρ).symm
        (SeibergWitten.cliffordRestriction o ρ
          (exteriorPower.map 2 (s.vectorFrame b p).toLinearMap α)
          (toPositiveHalfSpinors o hQ b ρ hρ ψ))) := by
  simp only [cliffordRestriction, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    AlgEquiv.toLinearMap_apply, ContinuousAlgEquiv.coe_toAlgEquiv,
    ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv, LinearIsometryEquiv.coe_symm_trans,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_symm, Function.comp_apply,
    AssociatedBundle.mkLinearIsometryEquiv_apply]
  -- Compare the chosen frame `p₀` with `p = p₀ • g`.
  generalize (Classical.arbitrary (s.P x)) = p₀
  rw [AssociatedBundle.mkLinearIsometryEquiv_symm_apply_mk]
  obtain ⟨g, hg⟩ : ∃ g, PrincipalBundle.division SpinC p₀ p = g := ⟨_, rfl⟩
  obtain rfl : op g • p₀ = p := hg ▸ PrincipalBundle.smul_division p₀ p
  rw [hg, map_vectorFrame_eq s p₀ g, LinearMap.comp_apply,
    cliffordRestriction_map_toPositiveHalfSpinors_smul, LinearIsometryEquiv.symm_apply_apply,
    AssociatedBundle.mk_smul]

/-- **The Clifford map as a conjugate**: for every point `p` of the principal bundle over `x`,
`C_x(α)` is the model `C(i ⋀² κ_p α)` conjugated by the unitary frame `[p, -] : S⁺ ≃ W⁺_x`. -/
theorem cliffordRestriction_eq_conj (s : SpinCStructure F E 4) {x : X} (p : s.P x)
    (α : ⋀[ℝ]^2 (E x)) :
    s.cliffordRestriction o hQ b ρ hρ x α =
      ContinuousLinearEquiv.conjContinuousAlgEquiv
        ((toPositiveHalfSpinors o hQ b ρ hρ).symm.trans
          (AssociatedBundle.mkLinearIsometryEquiv ℂ SpinC p)).toContinuousLinearEquiv
        (SeibergWitten.cliffordRestriction o ρ
          (exteriorPower.map 2 (s.vectorFrame b p).toLinearMap α)) := by
  ext ψ
  obtain ⟨ψ, rfl⟩ := (AssociatedBundle.mk_bijective (G := SpinC)
    (F := o.HalfSpinModel hQ b ρ hρ 1) p).2 ψ
  simp [cliffordRestriction_mk]

variable (o hQ b ρ hρ) in
/-- **The quadratic two-form** `q_x : W⁺_x → ⋀² (E x)` on the positive half-spinors of a `Spinᶜ`
structure of rank four: in a frame `p` it is `⋀² κ_p⁻¹` applied to the quadratic two-form
`q(ψ) = C⁻¹ Q₀(ψ)` of the model (`TauCeti.SeibergWitten.quadraticTwoForm`)
(`TauCeti.SpinCStructure.quadraticTwoForm_mk`), which does not depend on `p`. It is real-quadratic,
not linear. It is defined in a chosen frame. -/
def quadraticTwoForm (s : SpinCStructure F E 4) (x : X)
    (ψ : s.halfSpinorBundle o hQ b ρ hρ 1 x) : ⋀[ℝ]^2 (E x) :=
  let p : s.P x := Classical.arbitrary _
  exteriorPower.map 2 (s.vectorFrame b p).symm.toLinearMap
    (SeibergWitten.quadraticTwoForm o ρ hkl
      (toPositiveHalfSpinors o hQ b ρ hρ
        ((AssociatedBundle.mkLinearIsometryEquiv ℂ SpinC p).symm ψ)))

/-- **The quadratic two-form in a frame**: `q_x [p, ψ] = ⋀² κ_p⁻¹ q(ψ)` for every point `p` of the
principal bundle over `x`. -/
@[simp]
theorem quadraticTwoForm_mk (s : SpinCStructure F E 4) {x : X} (p : s.P x)
    (ψ : o.HalfSpinModel hQ b ρ hρ 1) :
    s.quadraticTwoForm o hQ b ρ hρ x (AssociatedBundle.mk SpinC p ψ) =
      exteriorPower.map 2 (s.vectorFrame b p).symm.toLinearMap
        (SeibergWitten.quadraticTwoForm o ρ hkl (toPositiveHalfSpinors o hQ b ρ hρ ψ)) := by
  simp only [quadraticTwoForm]
  -- Compare the chosen frame `p₀` with `p = p₀ • g`.
  generalize (Classical.arbitrary (s.P x)) = p₀
  rw [AssociatedBundle.mkLinearIsometryEquiv_symm_apply_mk]
  obtain ⟨g, hg⟩ : ∃ g, PrincipalBundle.division SpinC p₀ p = g := ⟨_, rfl⟩
  obtain rfl : op g • p₀ = p := hg ▸ PrincipalBundle.smul_division p₀ p
  rw [hg, quadraticTwoForm_toPositiveHalfSpinors_smul, ← LinearMap.comp_apply,
    ← exteriorPower.map_comp]
  congr 2
  ext v
  -- `κ_{p₀}⁻¹ ∘ π(g) = κ_{p₀ • g}⁻¹`, since `κ_{p₀} = π(g) ∘ κ_{p₀ • g}`.
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
  rw [LinearIsometryEquiv.symm_apply_eq, vectorFrame_eq_toSpecialOrthogonal_vectorFrame_smul s p₀ g,
    LinearIsometryEquiv.apply_symm_apply]

/-! ### The pointwise algebra on the fibres -/

/-- **`q_x` is homogeneous of degree two for the real structure**: `q_x(c ψ) = |c|² q_x(ψ)`. -/
theorem quadraticTwoForm_smul (s : SpinCStructure F E 4) {x : X} (c : ℂ)
    (ψ : s.halfSpinorBundle o hQ b ρ hρ 1 x) :
    s.quadraticTwoForm o hQ b ρ hρ x (c • ψ) = ‖c‖ ^ 2 • s.quadraticTwoForm o hQ b ρ hρ x ψ := by
  obtain ⟨p, ψ, rfl⟩ := AssociatedBundle.exists_mk ψ
  rw [← AssociatedBundle.mk_smul_scalar, quadraticTwoForm_mk, quadraticTwoForm_mk,
    LinearIsometryEquiv.map_smul, SeibergWitten.quadraticTwoForm_smul, Submodule.coe_smul,
    map_smul]

/-- **`q_x` is invariant under unit phases**: `q_x(u ψ) = q_x(ψ)` when `|u| = 1`. Applied
fibrewise, this is the invariance `q(u ψ) = q(ψ)` under every gauge transformation
`u : X → U(1)`. -/
theorem quadraticTwoForm_smul_of_norm_eq_one (s : SpinCStructure F E 4) {x : X} {u : ℂ}
    (hu : ‖u‖ = 1) (ψ : s.halfSpinorBundle o hQ b ρ hρ 1 x) :
    s.quadraticTwoForm o hQ b ρ hρ x (u • ψ) = s.quadraticTwoForm o hQ b ρ hρ x ψ := by
  rw [quadraticTwoForm_smul, hu, one_pow, one_smul]

/-- `q_x(0) = 0`. -/
@[simp]
theorem quadraticTwoForm_zero (s : SpinCStructure F E 4) {x : X} :
    s.quadraticTwoForm o hQ b ρ hρ x 0 = 0 := by
  simpa using s.quadraticTwoForm_smul (o := o) (hQ := hQ) (b := b) (hρ := hρ) (x := x) 0 0

/-- `q_x(-ψ) = q_x(ψ)`. -/
@[simp]
theorem quadraticTwoForm_neg (s : SpinCStructure F E 4) {x : X}
    (ψ : s.halfSpinorBundle o hQ b ρ hρ 1 x) :
    s.quadraticTwoForm o hQ b ρ hρ x (-ψ) = s.quadraticTwoForm o hQ b ρ hρ x ψ := by
  simpa using s.quadraticTwoForm_smul_of_norm_eq_one (u := -1) (by simp) ψ

/-- **`C_x(q_x(ψ)) = Q₀(ψ)`**: in complex rank two, `q_x(ψ)` is the two-form that the Clifford
map sends to the trace-free part `Q₀(ψ) = ψψ* - (‖ψ‖² / 2) Id` of `ψψ*`
(`TauCeti.SeibergWitten.quadraticEnd`). -/
theorem cliffordRestriction_quadraticTwoForm (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (s : SpinCStructure F E 4) {x : X} (ψ : s.halfSpinorBundle o hQ b ρ hρ 1 x) :
    s.cliffordRestriction o hQ b ρ hρ x (s.quadraticTwoForm o hQ b ρ hρ x ψ) =
      SeibergWitten.quadraticEnd ψ := by
  obtain ⟨p, ψ, rfl⟩ := AssociatedBundle.exists_mk ψ
  -- In the frame `p`, both sides are the model identity `C(q(ψ)) = Q₀(ψ)`, transported by the
  -- unitary frame `[p, -]`.
  rw [quadraticTwoForm_mk, cliffordRestriction_eq_conj s p,
    LinearIsometryEquiv.toLinearEquiv_symm, exteriorPower.map_map_symm,
    SeibergWitten.cliffordRestriction_quadraticTwoForm o hQ hkl hρ h₂,
    ← SeibergWitten.quadraticEnd_linearIsometryEquiv_apply]
  simp

/-- **`C_x(q_x(ψ)) ψ = (‖ψ‖² / 2) ψ`** in complex rank two: `ψ` is an eigenvector of the
endomorphism `C_x(q_x(ψ))`. This is the identity that turns the curvature term of the
Weitzenböck formula into `‖ψ‖⁴ / 4`. -/
theorem cliffordRestriction_quadraticTwoForm_apply_self
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) (s : SpinCStructure F E 4) {x : X}
    (ψ : s.halfSpinorBundle o hQ b ρ hρ 1 x) :
    s.cliffordRestriction o hQ b ρ hρ x (s.quadraticTwoForm o hQ b ρ hρ x ψ) ψ =
      ((‖ψ‖ : ℂ) ^ 2 / 2) • ψ := by
  rw [cliffordRestriction_quadraticTwoForm h₂, SeibergWitten.quadraticEnd_apply_self]

/-- **`q_x(ψ)` vanishes exactly when `ψ` does**, in complex rank two. -/
theorem quadraticTwoForm_eq_zero_iff (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (s : SpinCStructure F E 4) {x : X} {ψ : s.halfSpinorBundle o hQ b ρ hρ 1 x} :
    s.quadraticTwoForm o hQ b ρ hρ x ψ = 0 ↔ ψ = 0 := by
  obtain ⟨p, ψ, rfl⟩ := AssociatedBundle.exists_mk ψ
  rw [quadraticTwoForm_mk, ← AssociatedBundle.mk_zero (G := SpinC) p,
    (AssociatedBundle.mk_bijective p).injective.eq_iff,
    (exteriorPower.map_injective_field (s.vectorFrame b p).symm.injective).eq_iff' (map_zero _),
    Submodule.coe_eq_zero, SeibergWitten.quadraticTwoForm_eq_zero_iff o hQ hkl hρ h₂,
    LinearIsometryEquiv.map_eq_zero_iff]

/-- **The norm of the quadratic two-form**: `‖q_x(ψ)‖² = ‖ψ‖⁴ / 8` in complex rank two, for the
inner product of two-forms induced by the fibre metric of `E`. -/
theorem norm_quadraticTwoForm_sq (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (s : SpinCStructure F E 4) {x : X} [FiniteDimensional ℝ (E x)]
    (ψ : s.halfSpinorBundle o hQ b ρ hρ 1 x) :
    ‖s.quadraticTwoForm o hQ b ρ hρ x ψ‖ ^ 2 = ‖ψ‖ ^ 4 / 8 := by
  obtain ⟨p, ψ, rfl⟩ := AssociatedBundle.exists_mk ψ
  rw [quadraticTwoForm_mk, exteriorPower.norm_map_linearIsometryEquiv,
    AssociatedBundle.norm_mk, ← (toPositiveHalfSpinors o hQ b ρ hρ).norm_map, Submodule.norm_coe,
    SeibergWitten.norm_quadraticTwoForm_sq o hQ hkl hρ h₂]

/-- **`C_x(α)` is self-adjoint**, for the Hermitian metric of the half-spinor bundle. -/
theorem isSelfAdjoint_cliffordRestriction (s : SpinCStructure F E 4) {x : X}
    (α : ⋀[ℝ]^2 (E x)) : IsSelfAdjoint (s.cliffordRestriction o hQ b ρ hρ x α) := by
  let p : s.P x := Classical.arbitrary _
  rw [cliffordRestriction_eq_conj s p]
  exact (SeibergWitten.isSelfAdjoint_cliffordRestriction o hρ _).map
    ((toPositiveHalfSpinors o hQ b ρ hρ).symm.trans
      (AssociatedBundle.mkLinearIsometryEquiv ℂ SpinC p)).conjStarAlgEquiv

/-- **`C_x(α)` is trace free.** -/
@[simp]
theorem trace_cliffordRestriction (s : SpinCStructure F E 4) {x : X} (α : ⋀[ℝ]^2 (E x)) :
    LinearMap.trace ℂ (s.halfSpinorBundle o hQ b ρ hρ 1 x)
      (s.cliffordRestriction o hQ b ρ hρ x α) = 0 := by
  let p : s.P x := Classical.arbitrary _
  rw [cliffordRestriction_eq_conj s p]
  exact (LinearMap.trace_conj' _ ((toPositiveHalfSpinors o hQ b ρ hρ).symm.trans
    (AssociatedBundle.mkLinearIsometryEquiv ℂ SpinC p)).toLinearEquiv).trans
    (SeibergWitten.trace_cliffordRestriction o ρ hQ _)

/-- **On the wedge of orthogonal vectors the Clifford map is a product of Clifford
multiplications**: `C_x(u ∧ w) ψ = i c(u) c(w) ψ` when `⟪u, w⟫ = 0`, where `c(w) : W⁺_x → W⁻_x`
and `c(u) : W⁻_x → W⁺_x` are Clifford multiplication (`TauCeti.SpinCStructure.cliffordMul`). -/
theorem cliffordRestriction_ιMulti_apply_of_inner_eq_zero (s : SpinCStructure F E 4) {x : X}
    {u w : E x} (h : ⟪u, w⟫_ℝ = 0) (ψ : s.halfSpinorBundle o hQ b ρ hρ 1 x) :
    s.cliffordRestriction o hQ b ρ hρ x (exteriorPower.ιMulti ℝ 2 ![u, w]) ψ =
      Complex.I • s.cliffordMul o hQ b ρ hρ (ε := (-1 : ℂ)) (neg_neg (1 : ℂ)).symm x u
        (s.cliffordMul o hQ b ρ hρ (ε := (1 : ℂ)) rfl x w ψ) := by
  obtain ⟨p, ψ, rfl⟩ := AssociatedBundle.exists_mk ψ
  rw [cliffordRestriction_mk, cliffordMul_mk, cliffordMul_mk, ← AssociatedBundle.mk_smul_scalar,
    exteriorPower.map_apply_ιMulti_two]
  congr 1
  apply (toPositiveHalfSpinors o hQ b ρ hρ).injective
  apply Subtype.ext
  have h' : ⟪s.vectorFrame b p u, s.vectorFrame b p w⟫_ℝ = 0 := by
    rw [LinearIsometryEquiv.inner_map_map, h]
  rw [LinearIsometryEquiv.apply_symm_apply, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv,
    SeibergWitten.coe_cliffordRestriction_ιMulti_apply_of_inner_eq_zero o ρ hQ h']
  simp [map_mul]

end TauCeti.SpinCStructure
