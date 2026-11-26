/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.Bundle.CanonicalSpinor

/-!
# The eigenprojections `P_α`, `P_β` and Taubes's splitting `ψ = α u₀ + β` on the bundle

Let `s` be a `Spinᶜ` structure of rank four with positive half-spinor bundle `W⁺`, and let
`C_x : ⋀² (E x) → End_ℂ (W⁺_x)` be its Clifford map (`TauCeti.SpinCStructure.cliffordRestriction`).
For a two-form `ω` of the fibre over `x`, the **Clifford projection**

`P_x(ω) = (1 + C_x(ω) / 2) / 2`

(`TauCeti.SpinCStructure.cliffordProjection`) is, in every frame `p`, the model projection
`TauCeti.SeibergWitten.cliffordProjection` of `⋀² κ_p ω` conjugated by the unitary frame
`[p, -]` (`TauCeti.SpinCStructure.cliffordProjection_eq_conj`). On any fibre:

* `P_x(-ω) = 1 - P_x(ω)` (`TauCeti.SpinCStructure.cliffordProjection_neg`) and
  `C_x(ω) = 4 P_x(ω) - 2` (`TauCeti.SpinCStructure.cliffordRestriction_eq_cliffordProjection`);
* the fixed vectors of `P_x(ω)` are the `2`-eigenvectors of `C_x(ω)` and its kernel is the
  `-2`-eigenspace (`TauCeti.SpinCStructure.cliffordProjection_apply_eq_self_iff`,
  `TauCeti.SpinCStructure.cliffordProjection_apply_eq_zero_iff`);
* `P_x(ω)` is self-adjoint (`TauCeti.SpinCStructure.isSelfAdjoint_cliffordProjection`);
* the `ω`-component of the quadratic two-form is
  `⟪q_x(ψ), ω⟫ = (‖P_x(ω) ψ‖² - ‖P_x(-ω) ψ‖²) / 2`
  (`TauCeti.SpinCStructure.inner_quadraticTwoForm`).

**The canonical `Spinᶜ` structure.** On a rank-four bundle with an orthogonal complex structure
`J`, Taubes writes a positive spinor of the canonical `Spinᶜ` structure as `ψ = α u₀ + β`, where
`u₀` is the canonical spinor (`TauCeti.OrthonormalFrameBundle.canonicalSpinor`), a unit section of
the `-2i`-eigenline of `c₂(ω)` for the Kähler two-vector `ω` of `J`, and `β` lies in the
complementary line `K⁻¹`. With `P_α = P_x(ω)` and `P_β = P_x(-ω)`, when the Kähler form of the
model is self-dual and the positive half-spinors have complex rank two:

* `P_α ψ = ⟪u₀, ψ⟫ u₀` and `P_β ψ = ψ - ⟪u₀, ψ⟫ u₀`
  (`TauCeti.OrthonormalFrameBundle.cliffordProjection_kahlerForm_apply`,
  `TauCeti.OrthonormalFrameBundle.cliffordProjection_neg_kahlerForm_apply`), so `P_α` and `P_β`
  are the orthogonal projections onto the line `ℂ u₀` and its orthogonal complement
  (`TauCeti.OrthonormalFrameBundle.cliffordProjection_kahlerForm`,
  `TauCeti.OrthonormalFrameBundle.cliffordProjection_neg_kahlerForm`,
  `TauCeti.OrthonormalFrameBundle.isStarProjection_cliffordProjection_kahlerForm`,
  `TauCeti.OrthonormalFrameBundle.isStarProjection_cliffordProjection_neg_kahlerForm`), and
  `C_x(ω) ψ = 4 ⟪u₀, ψ⟫ u₀ - 2 ψ`
  (`TauCeti.OrthonormalFrameBundle.cliffordRestriction_kahlerForm_apply`);
* the `2`-eigenspace of `C_x(ω)` is the line `ℂ u₀` and its `-2`-eigenspace is `u₀⊥`
  (`TauCeti.OrthonormalFrameBundle.cliffordRestriction_kahlerForm_apply_eq_two_smul_iff`,
  `TauCeti.OrthonormalFrameBundle.cliffordRestriction_kahlerForm_apply_eq_neg_two_smul_iff`);
* the decomposition `ψ = α u₀ + β` with `⟪u₀, β⟫ = 0` is unique, `α = ⟪u₀, ψ⟫` and `β = P_β ψ`
  (`TauCeti.OrthonormalFrameBundle.cliffordProjection_kahlerForm_smul_add`,
  `TauCeti.OrthonormalFrameBundle.cliffordProjection_neg_kahlerForm_smul_add`), and
  `‖ψ‖² = |α|² + ‖β‖²`
  (`TauCeti.OrthonormalFrameBundle.norm_sq_eq_norm_inner_canonicalSpinor_sq_add_norm_sq`);
* `⟪q_x(ψ), ω⟫ = (|α|² - ‖β‖²) / 2`
  (`TauCeti.OrthonormalFrameBundle.inner_quadraticTwoForm_kahlerForm`);
* **the projected curvature term**: for `Ψ = √r ψ`, the orthogonal projection of
  `q_x(Ψ) - (r / 4) ω` onto `ℝ ω` is `(r / 4) (|α|² - ‖β‖² - 1) ω`
  (`TauCeti.OrthonormalFrameBundle.starProjection_quadraticTwoForm_sqrt_smul_sub_smul`).
  The left side indexes `F_A⁺ - F_{A₀}⁺ - η` under the perturbed curvature equation
  `F_A⁺ = q(Ψ) + F_{A₀}⁺ - i r ω / 4 + η`, so this is the pointwise identity behind Taubes's
  `π_ω (F_A - F_{A₀} - η) = (r / 4) (|α|² - |β|² - 1)` once the curvature equation holds.

These are the bundle-level statements of the pointwise algebra of
`TauCeti.Analysis.PDE.SeibergWitten.SelfDualSplitting`. The canonical connection `A₀` and the
continuity of the components `α` and `β` along continuous sections are not treated here.

## Main definitions

* `TauCeti.SpinCStructure.cliffordProjection`: the operator `P_x(ω) = (1 + C_x(ω) / 2) / 2`.

## References

* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, §1(c)–(d).
* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
-/

public section

noncomputable section

open Bundle MulOpposite Module Module.End TauCeti CliffordAlgebra TauCeti.CliffordAlgebra
open scoped InnerProductSpace

universe w

/-- The proof that the standard form on `ℝ⁴` is nonzero, on which `Spinᶜ(4)` depends. -/
local notation "hpos" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm 4 0)
local notation "SpinC" => spinCGroup (realCliffordForm 4 0) hpos

/-! ### The Clifford projection on the fibres of a `Spinᶜ` structure -/

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

variable (o hQ b ρ hρ) in
/-- **The Clifford projection** `P_x(ω) = (1 + C_x(ω) / 2) / 2` on the positive half-spinors over
`x` of a `Spinᶜ` structure of rank four, the element `TauCeti.halfOneAdd` of `C_x(ω) / 2` for the
Clifford map `C_x` (`TauCeti.SpinCStructure.cliffordRestriction`). In every frame it is the model
projection `TauCeti.SeibergWitten.cliffordProjection`
(`TauCeti.SpinCStructure.cliffordProjection_mk`). -/
def cliffordProjection (s : SpinCStructure F E 4) (x : X) (ω : ⋀[ℝ]^2 (E x)) :
    s.halfSpinorBundle o hQ b ρ hρ 1 x →L[ℂ] s.halfSpinorBundle o hQ b ρ hρ 1 x :=
  halfOneAdd ℂ ((2⁻¹ : ℂ) • s.cliffordRestriction o hQ b ρ hρ x ω)

/-- The explicit formula `P_x(ω) = (1 + C_x(ω) / 2) / 2`. -/
theorem cliffordProjection_eq_smul (s : SpinCStructure F E 4) {x : X} (ω : ⋀[ℝ]^2 (E x)) :
    s.cliffordProjection o hQ b ρ hρ x ω =
      (2⁻¹ : ℂ) • (1 + (2⁻¹ : ℂ) • s.cliffordRestriction o hQ b ρ hρ x ω) := by
  rw [cliffordProjection, halfOneAdd_def, invOf_eq_inv]

/-- **The Clifford projection as a conjugate**: for every point `p` of the principal bundle over
`x`, `P_x(ω)` is the model projection `P(⋀² κ_p ω)` conjugated by the unitary frame
`[p, -] : S⁺ ≃ W⁺_x`. -/
theorem cliffordProjection_eq_conj (s : SpinCStructure F E 4) {x : X} (p : s.P x)
    (ω : ⋀[ℝ]^2 (E x)) :
    s.cliffordProjection o hQ b ρ hρ x ω =
      ContinuousLinearEquiv.conjContinuousAlgEquiv
        ((toPositiveHalfSpinors o hQ b ρ hρ).symm.trans
          (AssociatedBundle.mkLinearIsometryEquiv ℂ SpinC p)).toContinuousLinearEquiv
        (SeibergWitten.cliffordProjection o ρ
          (exteriorPower.map 2 (s.vectorFrame b p).toLinearMap ω)) := by
  rw [cliffordProjection, cliffordRestriction_eq_conj s p, SeibergWitten.cliffordProjection_def,
    map_halfOneAdd, map_smul]

/-- **The Clifford projection in a frame**: `P_x(ω) [p, ψ] = [p, P(⋀² κ_p ω) ψ]` for every point
`p` of the principal bundle over `x`. -/
@[simp]
theorem cliffordProjection_mk (s : SpinCStructure F E 4) {x : X} (p : s.P x) (ω : ⋀[ℝ]^2 (E x))
    (ψ : o.HalfSpinModel hQ b ρ hρ 1) :
    s.cliffordProjection o hQ b ρ hρ x ω (AssociatedBundle.mk SpinC p ψ) =
      AssociatedBundle.mk SpinC p ((toPositiveHalfSpinors o hQ b ρ hρ).symm
        (SeibergWitten.cliffordProjection o ρ
          (exteriorPower.map 2 (s.vectorFrame b p).toLinearMap ω)
          (toPositiveHalfSpinors o hQ b ρ hρ ψ))) := by
  simp [cliffordProjection_eq_conj s p]

/-- `C_x(ω) = 4 P_x(ω) - 2`. -/
theorem cliffordRestriction_eq_cliffordProjection (s : SpinCStructure F E 4) {x : X}
    (ω : ⋀[ℝ]^2 (E x)) :
    s.cliffordRestriction o hQ b ρ hρ x ω =
      (4 : ℂ) • s.cliffordProjection o hQ b ρ hρ x ω - (2 : ℂ) • 1 := by
  rw [cliffordProjection_eq_smul]
  module

/-- The complementary projection: `P_x(-ω) = 1 - P_x(ω)`. -/
theorem cliffordProjection_neg (s : SpinCStructure F E 4) {x : X} (ω : ⋀[ℝ]^2 (E x)) :
    s.cliffordProjection o hQ b ρ hρ x (-ω) = 1 - s.cliffordProjection o hQ b ρ hρ x ω := by
  rw [cliffordProjection, cliffordProjection, map_neg, smul_neg, halfOneAdd_neg_eq_one_sub]

/-- `P_x(-ω) ψ = ψ - P_x(ω) ψ`. -/
theorem cliffordProjection_neg_apply (s : SpinCStructure F E 4) {x : X} (ω : ⋀[ℝ]^2 (E x))
    (ψ : s.halfSpinorBundle o hQ b ρ hρ 1 x) :
    s.cliffordProjection o hQ b ρ hρ x (-ω) ψ = ψ - s.cliffordProjection o hQ b ρ hρ x ω ψ := by
  rw [cliffordProjection_neg, sub_apply, one_apply_eq_self]

/-- Taubes's splitting of a positive spinor on the fibre: `P_x(ω) ψ + P_x(-ω) ψ = ψ`. -/
theorem cliffordProjection_apply_add_cliffordProjection_neg_apply (s : SpinCStructure F E 4)
    {x : X} (ω : ⋀[ℝ]^2 (E x)) (ψ : s.halfSpinorBundle o hQ b ρ hρ 1 x) :
    s.cliffordProjection o hQ b ρ hρ x ω ψ + s.cliffordProjection o hQ b ρ hρ x (-ω) ψ = ψ := by
  rw [cliffordProjection_neg_apply, add_sub_cancel]

/-- The fixed vectors of `P_x(ω)` are the `2`-eigenvectors of `C_x(ω)`. -/
theorem cliffordProjection_apply_eq_self_iff (s : SpinCStructure F E 4) {x : X}
    {ω : ⋀[ℝ]^2 (E x)} {ψ : s.halfSpinorBundle o hQ b ρ hρ 1 x} :
    s.cliffordProjection o hQ b ρ hρ x ω ψ = ψ ↔
      s.cliffordRestriction o hQ b ρ hρ x ω ψ = (2 : ℂ) • ψ := by
  rw [cliffordProjection, ← ContinuousLinearMap.smul_def, halfOneAdd_smul_eq_self_iff,
    ContinuousLinearMap.smul_def, smul_apply, inv_smul_eq_iff₀ two_ne_zero]

/-- The kernel of `P_x(ω)` is the `-2`-eigenspace of `C_x(ω)`. -/
theorem cliffordProjection_apply_eq_zero_iff (s : SpinCStructure F E 4) {x : X}
    {ω : ⋀[ℝ]^2 (E x)} {ψ : s.halfSpinorBundle o hQ b ρ hρ 1 x} :
    s.cliffordProjection o hQ b ρ hρ x ω ψ = 0 ↔
      s.cliffordRestriction o hQ b ρ hρ x ω ψ = (-2 : ℂ) • ψ := by
  rw [cliffordProjection, ← ContinuousLinearMap.smul_def, halfOneAdd_smul_eq_zero_iff,
    ContinuousLinearMap.smul_def, smul_apply, inv_smul_eq_iff₀ two_ne_zero, smul_neg, neg_smul]

/-- **`P_x(ω)` is self-adjoint**, for the Hermitian metric of the half-spinor bundle. -/
theorem isSelfAdjoint_cliffordProjection (s : SpinCStructure F E 4) {x : X}
    (ω : ⋀[ℝ]^2 (E x)) : IsSelfAdjoint (s.cliffordProjection o hQ b ρ hρ x ω) := by
  have h2 : IsSelfAdjoint (2⁻¹ : ℂ) := by
    rw [isSelfAdjoint_iff, star_inv₀, Complex.star_def, map_ofNat]
  exact isSelfAdjoint_halfOneAdd ℂ
    (A := s.halfSpinorBundle o hQ b ρ hρ 1 x →L[ℂ] s.halfSpinorBundle o hQ b ρ hρ 1 x)
    (h2.smul (isSelfAdjoint_cliffordRestriction (o := o) (hQ := hQ) (b := b) (hρ := hρ) s ω))

/-- **The `ω`-component of `q_x`**: `⟪q_x(ψ), ω⟫ = (‖P_x(ω) ψ‖² - ‖P_x(-ω) ψ‖²) / 2` for every
two-form `ω` of the fibre. -/
theorem inner_quadraticTwoForm (s : SpinCStructure F E 4) {x : X} [FiniteDimensional ℝ (E x)]
    (ω : ⋀[ℝ]^2 (E x)) (ψ : s.halfSpinorBundle o hQ b ρ hρ 1 x) :
    ⟪s.quadraticTwoForm o hQ b ρ hρ x ψ, ω⟫_ℝ =
      (‖s.cliffordProjection o hQ b ρ hρ x ω ψ‖ ^ 2 -
        ‖s.cliffordProjection o hQ b ρ hρ x (-ω) ψ‖ ^ 2) / 2 := by
  obtain ⟨p, ψ, rfl⟩ := AssociatedBundle.exists_mk ψ
  -- Move `ω` into the frame `p`, where both sides are the model identity.
  have hω : ω = exteriorPower.map 2 (s.vectorFrame b p).symm.toLinearMap
      (exteriorPower.map 2 (s.vectorFrame b p).toLinearMap ω) := by
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
    simp
  rw [cliffordProjection_mk, cliffordProjection_mk, AssociatedBundle.norm_mk,
    AssociatedBundle.norm_mk, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map,
    quadraticTwoForm_mk, map_neg, ← SeibergWitten.inner_quadraticTwoForm o hQ hkl]
  conv_lhs => rw [hω]
  exact exteriorPower.inner_map_map (s.vectorFrame b p).symm.toLinearIsometry _ _

end TauCeti.SpinCStructure

/-! ### Taubes's splitting on the canonical `Spinᶜ` structure -/

namespace TauCeti.OrthonormalFrameBundle

open Orientation.HalfSpinModel SeibergWitten

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : X → Type} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E] {J : ∀ x, E x ≃ₗᵢ[ℝ] E x}
  {J₀ : unitary (EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))}
  (hJ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, J v.proj v.snd⟩ : TotalSpace F E))
  (hJ₂ : ∀ x v, J x (J x v) = -v)
  (hJ₀ : ∀ v, (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    ((J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) v) = -v)
  (hF : finrank ℝ F = 4) (e : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4)))
  (h₀ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 0) = e 1)
  (h₂ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 2) = e 3)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (b : OrthonormalBasis (Fin 4) ℝ V)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
  (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3

/-- The dimension of `V`, in the form taken by the Hodge star of two-forms. -/
local notation "hkl" => (Eq.symm (Fact.out : finrank ℝ V = 4) : 2 + 2 = finrank ℝ V)

variable {JV : AlmostComplexStructure V}
  (hJV : ∀ w, JV (b.repr.symm w) =
    b.repr.symm ((J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) w))
  {u : o.HalfSpinModel hQ b ρ hρ 1}
  (hu : cliffordProjection o ρ JV.kahlerForm (toPositiveHalfSpinors o hQ b ρ hρ u) =
    toPositiveHalfSpinors o hQ b ρ hρ u)
  (hu₁ : ‖u‖ = 1)
  (hω : o.hodgeStar (Eq.symm (Fact.out : finrank ℝ V = 4) : 2 + 2 = finrank ℝ V) JV.kahlerForm =
    JV.kahlerForm)
  (hrank : finrank ℂ (positiveHalfSpinors o ρ) = 2)
  {x : X} [FiniteDimensional ℝ (E x)] {Jx : AlmostComplexStructure (E x)}
  (hJx : ∀ v, Jx v = J x v)

/-- The canonical `Spinᶜ` structure, abbreviated in this file. -/
local notation "𝔰" => canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂

/-- The canonical spinor at `x`, abbreviated in this file. -/
local notation "u₀" => canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ u x

include hJV hu hu₁ hω hrank hJx in
/-- **`P_α` is the projection onto the line of the canonical spinor**: on the positive
half-spinors of the canonical `Spinᶜ` structure, `P_α ψ = ⟪u₀, ψ⟫ u₀` for the Kähler two-vector
`ω` of `J`, so `ψ = α u₀ + β` with `α = ⟪u₀, ψ⟫` and `β = P_β ψ`. -/
theorem cliffordProjection_kahlerForm_apply (ψ : (𝔰).halfSpinorBundle o hQ b ρ hρ 1 x) :
    (𝔰).cliffordProjection o hQ b ρ hρ x Jx.kahlerForm ψ = ⟪u₀, ψ⟫_ℂ • u₀ := by
  have p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x := Classical.arbitrary _
  obtain ⟨ψ, rfl⟩ := (AssociatedBundle.mk_bijective (G := SpinC)
    (F := o.HalfSpinModel hQ b ρ hρ 1) (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p)).2 ψ
  rw [canonicalSpinor_eq_mk hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu p,
    SpinCStructure.cliffordProjection_mk,
    map_vectorFrame_canonicalSpinCStructureInl_kahlerForm hJ hJ₂ hJ₀ hF e h₀ h₂ b hJV p hJx,
    SeibergWitten.cliffordProjection_apply_eq_inner_smul o hQ hkl hω hρ hrank hu
      (by rw [LinearIsometryEquiv.norm_map, hu₁]),
    AssociatedBundle.inner_mk, LinearIsometryEquiv.inner_map_map, _root_.map_smul,
    LinearIsometryEquiv.symm_apply_apply, AssociatedBundle.mk_smul_scalar]

include hJV hu hu₁ hω hrank hJx in
/-- **`P_β` is the projection onto the orthogonal complement of the canonical spinor**:
`P_β ψ = ψ - ⟪u₀, ψ⟫ u₀`. -/
theorem cliffordProjection_neg_kahlerForm_apply (ψ : (𝔰).halfSpinorBundle o hQ b ρ hρ 1 x) :
    (𝔰).cliffordProjection o hQ b ρ hρ x (-Jx.kahlerForm) ψ = ψ - ⟪u₀, ψ⟫_ℂ • u₀ := by
  rw [SpinCStructure.cliffordProjection_neg_apply,
    cliffordProjection_kahlerForm_apply hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu hu₁ hω hrank hJx]

include hJV hu hu₁ hω hrank hJx in
/-- **`P_α` is the orthogonal projection onto the line `ℂ u₀`** of the canonical spinor. -/
theorem cliffordProjection_kahlerForm :
    (𝔰).cliffordProjection o hQ b ρ hρ x Jx.kahlerForm = (ℂ ∙ u₀).starProjection := by
  ext ψ
  rw [cliffordProjection_kahlerForm_apply hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu hu₁ hω hrank hJx,
    Submodule.starProjection_singleton, norm_canonicalSpinor, hu₁]
  simp

include hJV hu hu₁ hω hrank hJx in
/-- **`P_β` is the orthogonal projection onto the orthogonal complement `u₀⊥`** of the canonical
spinor. -/
theorem cliffordProjection_neg_kahlerForm :
    (𝔰).cliffordProjection o hQ b ρ hρ x (-Jx.kahlerForm) = (ℂ ∙ u₀)ᗮ.starProjection := by
  ext ψ
  rw [Submodule.starProjection_orthogonal_val, SpinCStructure.cliffordProjection_neg_apply,
    cliffordProjection_kahlerForm hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu hu₁ hω hrank hJx]

include hJV hu hu₁ hω hrank hJx in
/-- `P_α` is a star projection: idempotent and self-adjoint. -/
theorem isStarProjection_cliffordProjection_kahlerForm :
    IsStarProjection ((𝔰).cliffordProjection o hQ b ρ hρ x Jx.kahlerForm) := by
  rw [cliffordProjection_kahlerForm hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu hu₁ hω hrank hJx]
  exact isStarProjection_starProjection

include hJV hu hu₁ hω hrank hJx in
/-- `P_β` is a star projection: idempotent and self-adjoint. -/
theorem isStarProjection_cliffordProjection_neg_kahlerForm :
    IsStarProjection ((𝔰).cliffordProjection o hQ b ρ hρ x (-Jx.kahlerForm)) := by
  rw [cliffordProjection_neg_kahlerForm hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu hu₁ hω hrank hJx]
  exact isStarProjection_starProjection

include hJV hu hu₁ hω hrank hJx in
/-- **The Clifford action of the Kähler form on the canonical splitting**:
`C_x(ω) ψ = 4 ⟪u₀, ψ⟫ u₀ - 2 ψ`, which is `2 α u₀ - 2 β` for `ψ = α u₀ + β`. -/
theorem cliffordRestriction_kahlerForm_apply (ψ : (𝔰).halfSpinorBundle o hQ b ρ hρ 1 x) :
    (𝔰).cliffordRestriction o hQ b ρ hρ x Jx.kahlerForm ψ =
      (4 * ⟪u₀, ψ⟫_ℂ) • u₀ - (2 : ℂ) • ψ := by
  rw [SpinCStructure.cliffordRestriction_eq_cliffordProjection, sub_apply,
    smul_apply, smul_apply,
    one_apply_eq_self,
    cliffordProjection_kahlerForm_apply hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu hu₁ hω hrank hJx,
    smul_smul]

include hJV hu hu₁ hω hrank hJx in
/-- **The line `K⁻¹` is the orthogonal complement of the canonical spinor**: `C_x(ω) β = -2 β`,
that is `c₂(ω) β = 2i β`, exactly when `⟪u₀, β⟫ = 0`. -/
theorem cliffordRestriction_kahlerForm_apply_eq_neg_two_smul_iff
    {β : (𝔰).halfSpinorBundle o hQ b ρ hρ 1 x} :
    (𝔰).cliffordRestriction o hQ b ρ hρ x Jx.kahlerForm β = (-2 : ℂ) • β ↔ ⟪u₀, β⟫_ℂ = 0 := by
  have hu₀ : u₀ ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_canonicalSpinor, hu₁]
    exact one_ne_zero
  rw [cliffordRestriction_kahlerForm_apply hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu hu₁ hω hrank
    hJx, sub_eq_iff_eq_add, ← add_smul]
  norm_num [smul_eq_zero, hu₀]

include hJV hu hu₁ hω hrank hJx in
/-- **The canonical line is spanned by the canonical spinor**: `C_x(ω) φ = 2 φ`, that is
`c₂(ω) φ = -2i φ`, exactly when `φ` is a multiple of `u₀`. -/
theorem cliffordRestriction_kahlerForm_apply_eq_two_smul_iff
    {φ : (𝔰).halfSpinorBundle o hQ b ρ hρ 1 x} :
    (𝔰).cliffordRestriction o hQ b ρ hρ x Jx.kahlerForm φ = (2 : ℂ) • φ ↔ ∃ c : ℂ, c • u₀ = φ := by
  rw [← SpinCStructure.cliffordProjection_apply_eq_self_iff,
    cliffordProjection_kahlerForm_apply hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu hu₁ hω hrank hJx]
  refine ⟨fun h ↦ ⟨_, h⟩, ?_⟩
  rintro ⟨c, rfl⟩
  rw [inner_smul_right, inner_self_eq_one_of_norm_eq_one
    ((norm_canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ x).trans hu₁), mul_one]

include hJV hu hu₁ hω hrank hJx in
/-- **The components of the canonical splitting, `α`**: if `ψ = a u₀ + β` with `⟪u₀, β⟫ = 0`, then
`P_α ψ = a u₀`; in particular `a = ⟪u₀, ψ⟫`. -/
theorem cliffordProjection_kahlerForm_smul_add (a : ℂ)
    {β : (𝔰).halfSpinorBundle o hQ b ρ hρ 1 x} (hβ : ⟪u₀, β⟫_ℂ = 0) :
    (𝔰).cliffordProjection o hQ b ρ hρ x Jx.kahlerForm (a • u₀ + β) = a • u₀ := by
  rw [cliffordProjection_kahlerForm_apply hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu hu₁ hω hrank hJx,
    inner_add_right, inner_smul_right, inner_self_eq_one_of_norm_eq_one
      ((norm_canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ x).trans hu₁), hβ, mul_one]
  exact congrArg (· • _) (add_zero a)

include hJV hu hu₁ hω hrank hJx in
/-- **The components of the canonical splitting, `β`**: if `ψ = a u₀ + β` with `⟪u₀, β⟫ = 0`,
then `P_β ψ = β`. -/
theorem cliffordProjection_neg_kahlerForm_smul_add (a : ℂ)
    {β : (𝔰).halfSpinorBundle o hQ b ρ hρ 1 x} (hβ : ⟪u₀, β⟫_ℂ = 0) :
    (𝔰).cliffordProjection o hQ b ρ hρ x (-Jx.kahlerForm) (a • u₀ + β) = β := by
  rw [SpinCStructure.cliffordProjection_neg_apply,
    cliffordProjection_kahlerForm_smul_add hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu hu₁ hω hrank
      hJx a hβ, add_sub_cancel_left]

include hJV hu hu₁ hω hrank hJx in
/-- `P_β ψ` is orthogonal to the canonical spinor: `⟪u₀, P_β ψ⟫ = 0`. -/
theorem inner_canonicalSpinor_cliffordProjection_neg_kahlerForm_apply
    (ψ : (𝔰).halfSpinorBundle o hQ b ρ hρ 1 x) :
    ⟪u₀, (𝔰).cliffordProjection o hQ b ρ hρ x (-Jx.kahlerForm) ψ⟫_ℂ = 0 := by
  rw [cliffordProjection_neg_kahlerForm_apply hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu hu₁ hω
    hrank hJx, inner_sub_right, inner_smul_right, inner_self_eq_one_of_norm_eq_one
      ((norm_canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ x).trans hu₁), mul_one, sub_self]

include hJV hu hu₁ hω hrank hJx in
/-- **Pythagoras for the canonical splitting** `ψ = α u₀ + β`: `‖ψ‖² = |α|² + ‖β‖²` with
`α = ⟪u₀, ψ⟫` and `β = P_β ψ`. -/
theorem norm_sq_eq_norm_inner_canonicalSpinor_sq_add_norm_sq
    (ψ : (𝔰).halfSpinorBundle o hQ b ρ hρ 1 x) :
    ‖ψ‖ ^ 2 = ‖⟪u₀, ψ⟫_ℂ‖ ^ 2 +
      ‖(𝔰).cliffordProjection o hQ b ρ hρ x (-Jx.kahlerForm) ψ‖ ^ 2 := by
  have h := SpinCStructure.cliffordProjection_apply_add_cliffordProjection_neg_apply
    (o := o) (hQ := hQ) (b := b) (hρ := hρ) (𝔰) Jx.kahlerForm ψ
  rw [cliffordProjection_kahlerForm_apply hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu hu₁ hω hrank
    hJx] at h
  conv_lhs => rw [← h]
  rw [@norm_add_sq ℂ, inner_smul_left,
    inner_canonicalSpinor_cliffordProjection_neg_kahlerForm_apply hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ
      hρ hJV hu hu₁ hω hrank hJx,
    mul_zero, map_zero, mul_zero, add_zero, norm_smul, norm_canonicalSpinor, hu₁, mul_one]

include hJV hu hu₁ hω hrank hJx in
/-- **The `ω`-component of `q_x` on the canonical splitting**: `⟪q_x(ψ), ω⟫ = (|α|² - ‖β‖²) / 2`
with `α = ⟪u₀, ψ⟫` and `β = P_β ψ`. -/
theorem inner_quadraticTwoForm_kahlerForm (ψ : (𝔰).halfSpinorBundle o hQ b ρ hρ 1 x) :
    ⟪(𝔰).quadraticTwoForm o hQ b ρ hρ x ψ, Jx.kahlerForm⟫_ℝ =
      (‖⟪u₀, ψ⟫_ℂ‖ ^ 2 - ‖(𝔰).cliffordProjection o hQ b ρ hρ x (-Jx.kahlerForm) ψ‖ ^ 2) / 2 := by
  rw [SpinCStructure.inner_quadraticTwoForm,
    cliffordProjection_kahlerForm_apply hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu hu₁ hω hrank hJx,
    norm_smul, norm_canonicalSpinor, hu₁, mul_one]

include hJV hu hu₁ hω hrank hJx in
/-- **The projected curvature term of Taubes's equations**: for `Ψ = √r ψ`, the orthogonal
projection of `q_x(Ψ) - (r / 4) ω` onto the line `ℝ ω` is `(r / 4) (|α|² - ‖β‖² - 1) ω`, with
`α = ⟪u₀, ψ⟫` and `β = P_β ψ`. The left side indexes `F_A⁺ - F_{A₀}⁺ - η` under the perturbed
curvature equation `F_A⁺ = q(Ψ) + F_{A₀}⁺ - i r ω / 4 + η`, so this is the pointwise identity
behind Taubes's `π_ω (F_A - F_{A₀} - η) = (r / 4) (|α|² - |β|² - 1)` once the curvature equation
holds; that equation is not treated here. -/
theorem starProjection_quadraticTwoForm_sqrt_smul_sub_smul {r : ℝ} (hr : 0 ≤ r)
    (ψ : (𝔰).halfSpinorBundle o hQ b ρ hρ 1 x) :
    (ℝ ∙ Jx.kahlerForm).starProjection
        ((𝔰).quadraticTwoForm o hQ b ρ hρ x (((√r : ℝ) : ℂ) • ψ) - (r / 4) • Jx.kahlerForm) =
      (r / 4 * (‖⟪u₀, ψ⟫_ℂ‖ ^ 2 -
        ‖(𝔰).cliffordProjection o hQ b ρ hρ x (-Jx.kahlerForm) ψ‖ ^ 2 - 1)) • Jx.kahlerForm := by
  -- The Kähler two-vector of the rank-four fibre has `‖ω‖² = 2`.
  have h4 : finrank ℝ (E x) = 4 := hF ▸ ((trivializationAt F E x).continuousLinearEquivAt ℝ x
    (mem_baseSet_trivializationAt F E x)).toLinearEquiv.finrank_eq
  have hω₂ : ‖Jx.kahlerForm‖ ^ 2 = 2 := by
    rw [AlmostComplexStructure.norm_kahlerForm_sq
      (fun v w ↦ by rw [hJx, hJx, LinearIsometryEquiv.inner_map_map]), h4]
    norm_num
  rw [Submodule.starProjection_singleton, real_inner_comm, inner_sub_left,
    SpinCStructure.quadraticTwoForm_smul, real_inner_smul_left, real_inner_smul_left,
    inner_quadraticTwoForm_kahlerForm hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu hu₁ hω hrank hJx,
    real_inner_self_eq_norm_sq, hω₂, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt hr]
  congr 1
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  ring

end TauCeti.OrthonormalFrameBundle
