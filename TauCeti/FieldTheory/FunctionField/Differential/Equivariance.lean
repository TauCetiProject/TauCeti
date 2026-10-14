/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Automorphism
public import TauCeti.FieldTheory.FunctionField.Differential.Independence
public import TauCeti.RingTheory.Algebraic.Basic
public import TauCeti.RingTheory.Kaehler.MapSemilinear
import TauCeti.FieldTheory.IntermediateField.Map
import TauCeti.FieldTheory.RatFunc.Automorphism

/-!
# Automorphisms and the Kähler–Weil comparison

Let `F / k` be an algebraic function field and `σ` a `k`-automorphism of `F`. Then `σ` acts on
the Kähler differentials `Ω[F⁄k]` by functoriality, `z dx ↦ σ z d(σ x)`
(`KaehlerDifferential.mapSemilinear`), and on the Weil differentials by
`(σ • ω) a = ω (σ⁻¹ • a)` (`TauCeti.weilDifferentialRepresentation`). This file shows that the
Kähler–Weil comparison of Stichtenoth's Theorem 4.3.2 intertwines the two actions.

The key fact is that `σ` moves the Weil differential `dx` of a separating element to `d(σ x)`
(`TauCeti.weilDifferentialRepresentation_weilDifferentialOfSeparating`). The Weil differential
`dx` is the cotrace of the normalized differential of `k(X)` along the embedding `X ↦ x`, and
`σ` carries this embedding to `X ↦ σ x`. The cotrace is characterized by its values on the
repartitions constant on the fibres over the places of `k(X)` (Stichtenoth, Theorem 3.4.6), and
`σ` matches the fibres, the fibre-constant repartitions and the traces of the two embeddings.
No hypothesis on the constant field is needed.

Write `ψ_x : Ω[F⁄k] ≃ Ω_F` for the comparison built from a separating element `x`
(`TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating`, which needs `k` to be the exact
constant field). Consequently `ψ_{σ x} (σ • ω) = σ • ψ_x (ω)`
(`TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating_mapSemilinear`). Whenever the
comparison does not depend on the separating element, for instance over a perfect constant field,
it is therefore equivariant for the whole automorphism group
(`TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating_mapSemilinear_of_perfectField`):
for automorphisms, the Kähler and Weil formalisms are interchangeable.

## Main results

* `TauCeti.weilDifferentialRepresentation_weilDifferentialOfSeparating`: `σ • dx = d(σ x)` for
  Weil differentials.
* `TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating_mapSemilinear`:
  `ψ_{σ x} (σ • ω) = σ • ψ_x (ω)`.
* `TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating_mapSemilinear_of_perfectField`:
  over a perfect constant field the comparison is equivariant.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.4.6 (the cotrace) and Theorem 4.3.2 (the comparison).
-/

public section

open scoped IntermediateField

namespace TauCeti

open KaehlerDifferential

universe u v

/-! ### The cotrace along isomorphic embeddings -/

section Cotrace

variable {k : Type u} {E F₁ F₂ : Type*} [Field k] [Field E] [Field F₁] [Field F₂]
variable [Algebra k E] [Algebra k F₁] [Algebra k F₂] [i₁ : Algebra E F₁] [i₂ : Algebra E F₂]
variable [IsScalarTower k E F₁] [IsScalarTower k E F₂]
variable [FiniteDimensional E F₁] [FiniteDimensional E F₂]
variable [Algebra.IsSeparable E F₁] [Algebra.IsSeparable E F₂]

/-- Let `σ : F₁ ≃ F₂` be a `k`-isomorphism compatible with two embeddings of `E`. Then the cotrace
to `F₁` of a Weil differential `ω` of `E`, evaluated at the repartition of `F₁` obtained by moving
a fibre-constant repartition `β` of `F₂` back along `σ`, is `ω (Tr β)`: moving back along `σ`
matches the fibres over `E`, the fibre-constant repartitions and the traces of the two
extensions. -/
private theorem weilDifferentialCotrace_apply_eq_repartitionTrace (hE : IsFunctionField k E)
    (hF₁ : IsFunctionField k F₁) (σ : F₁ ≃ₐ[k] F₂)
    (hσ : ∀ r : E, σ (algebraMap E F₁ r) = algebraMap E F₂ r) (ω : ↥(weilDifferentialSpace k E))
    (β : ↥(relativeRepartitionSpace k E F₂)) (a : ↥(repartitionSpace k F₁))
    (ha : ∀ P : Place k F₁,
      (a : Place k F₁ → F₁) P = σ.symm ((β : Place k E → F₂) ((P.map σ).restrict k E))) :
    (weilDifferentialCotrace k F₁ hE hF₁ ω : Module.Dual k ↥(repartitionSpace k F₁)) a =
      (ω : Module.Dual k ↥(repartitionSpace k E)) (repartitionTrace k E F₂ hE β) := by
  let σE : F₁ ≃ₐ[E] F₂ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) hσ
  -- `σ` matches the places of `F₁` and `F₂` over each place of `E`.
  have hres (P : Place k F₁) : (P.map σ).restrict k E = P.restrict k E :=
    Place.restrict_map_restrictScalars P σE
  -- So the family moved back along `σ` is a fibre-constant repartition of `F₁`, ...
  have hmem : (fun Q ↦ σ.symm ((β : Place k E → F₂) Q)) ∈ relativeRepartitionSpace k E F₁ := by
    refine (comp_restrict_mem_repartitionSpace_iff hF₁).mp ?_
    convert a.2 using 1
    exact funext fun P ↦ by rw [ha, hres]
  have hpull : relativeRepartitionPullback k k E F₁ ⟨_, hmem⟩ = a :=
    Subtype.ext <| funext fun P ↦ by rw [relativeRepartitionPullback_apply, ha, hres]
  -- ... whose trace to `E` is the trace of `β`, because `σ` is an isomorphism over `E`.
  have htrace : repartitionTrace k E F₁ hE ⟨_, hmem⟩ = repartitionTrace k E F₂ hE β :=
    Subtype.ext <| funext fun Q ↦ by
      rw [repartitionTrace_apply, repartitionTrace_apply]
      exact Algebra.trace_eq_of_algEquiv σE.symm _
  have h := trace_weilDifferentialCotrace_apply hE hF₁ ω ⟨_, hmem⟩
  rwa [Algebra.trace_self_apply, hpull, htrace] at h

end Cotrace

/-! ### The Weil differential of a moved separating element -/

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

/-- The embedding `X ↦ σ x` of `k(X)` is the embedding `X ↦ x` followed by `σ`. -/
private theorem algebraMap_ratFuncAlgebraOfTranscendental_algEquiv_apply (σ : F ≃ₐ[k] F)
    {x : F} (hx : Transcendental k x) (r : RatFunc k) :
    σ (letI := ratFuncAlgebraOfTranscendental hx; algebraMap (RatFunc k) F r) =
      letI := ratFuncAlgebraOfTranscendental (hx.map σ σ.injective)
      algebraMap (RatFunc k) F r := by
  have hy := hx.map σ σ.injective
  -- Both sides are `k`-algebra maps out of `k(X)` sending `X` to `σ x`.
  have h : (σ : F →ₐ[k] F).comp
        (k⟮x⟯.val.comp (RatFunc.algEquivOfTranscendental x hx).toAlgHom) =
      k⟮σ x⟯.val.comp (RatFunc.algEquivOfTranscendental (σ x) hy).toAlgHom :=
    RatFunc.algHom_ext (by simp [RatFunc.algEquivOfTranscendental_X])
  rw [algebraMap_ratFuncAlgebraOfTranscendental_apply,
    algebraMap_ratFuncAlgebraOfTranscendental_apply]
  exact DFunLike.congr_fun h r

/-- **Automorphisms move the differential of a separating element**: for a `k`-automorphism `σ`
of `F` and a separating element `x`, the Weil differential `dx` is moved by `σ` to `d(σ x)`.
The separability of `F` over `k⟮σ x⟯` is `IntermediateField.isSeparable_adjoin_simple_map`. -/
theorem weilDifferentialRepresentation_weilDifferentialOfSeparating (hF : IsFunctionField k F)
    (σ : F ≃ₐ[k] F) {x : F} (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    [Algebra.IsSeparable k⟮σ x⟯ F] :
    weilDifferentialRepresentation k k F σ (weilDifferentialOfSeparating hF hx) =
      weilDifferentialOfSeparating hF (hx.map σ σ.injective) := by
  have hy := hx.map σ σ.injective
  -- The embedding `X ↦ x` and its instances.
  let A₁ := ratFuncAlgebraOfTranscendental hx
  have t₁ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  have f₁ : letI := A₁; FiniteDimensional (RatFunc k) F :=
    letI := A₁; isFunctionField_iff_functionField.mp hF
  have s₁ := isSeparable_ratFuncAlgebraOfTranscendental hx
  -- The embedding `X ↦ σ x`, used as the ambient structure from now on.
  let _ := ratFuncAlgebraOfTranscendental hy
  have _ := isScalarTower_ratFuncAlgebraOfTranscendental hy
  have _ := isFunctionField_iff_functionField.mp hF
  have _ := isSeparable_ratFuncAlgebraOfTranscendental hy
  -- `d(σ x)` is the cotrace along `X ↦ σ x`; check its defining identity on `σ • dx`.
  rw [weilDifferentialOfSeparating_def hF hy]
  refine Subtype.ext (eq_weilDifferentialCotrace (IsFunctionField.ratFunc k) hF _
    (Submodule.coe_mem _) fun β ↦ ?_)
  rw [Algebra.trace_self_apply, coe_weilDifferentialRepresentation_apply,
    Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
    weilDifferentialOfSeparating_def hF hx]
  refine weilDifferentialCotrace_apply_eq_repartitionTrace (i₁ := A₁)
    (IsFunctionField.ratFunc k) hF σ
    (algebraMap_ratFuncAlgebraOfTranscendental_algEquiv_apply σ hx) _ β _ fun P ↦ ?_
  have hσ : σ.restrictScalars k = σ := AlgEquiv.ext fun _ ↦ rfl
  simp [Place.smul_eq_map, AlgEquiv.aut_inv, hσ]

/-! ### Equivariance of the Kähler–Weil comparison -/

/-- **The Kähler–Weil comparison intertwines the automorphism actions**: for a `k`-automorphism
`σ` of `F` and a separating element `x`, the comparison built from `σ x`, applied to the image
`σ • ω` of a Kähler differential, is the image under `σ` of the Weil differential that the
comparison built from `x` attaches to `ω`. -/
theorem kaehlerDifferentialEquivWeilDifferentialOfSeparating_mapSemilinear
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (σ : F ≃ₐ[k] F) {x : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] [Algebra.IsSeparable k⟮σ x⟯ F]
    (ω : Ω[F⁄k]) :
    kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex
        (hx.map σ σ.injective) (mapSemilinear (σ : F →ₐ[k] F) ω) =
      weilDifferentialRepresentation k k F σ
        (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx ω) := by
  let _ := weilDifferentialSpaceModule hF
  -- Write `ω = c dx`; both sides are then `σ c d(σ x)`.
  obtain ⟨c, rfl⟩ : ∃ c : F, c • D k F x = ω :=
    ⟨_, by simpa using (kaehlerBasisOfSeparating hx).sum_repr ω⟩
  rw [mapSemilinear_smul, mapSemilinear_D, map_smul, map_smul, AlgEquiv.coe_toAlgHom,
    kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self,
    kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self,
    ← weilDifferentialRepresentation_weilDifferentialOfSeparating hF σ hx]
  -- The action is `σ`-semilinear for the `F`-vector space structure on Weil differentials.
  exact Subtype.ext <| by
    simp only [coe_weilDifferentialSpaceModule_smul, coe_weilDifferentialRepresentation_apply,
      repartitionRepresentation_dual_repartitionDualMul]

/-- **The Kähler–Weil comparison is equivariant over a perfect field**: over a perfect exact
constant field the comparison does not depend on the separating element
(`TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq_of_perfectField`), so it carries
the functorial action of a `k`-automorphism `σ` on Kähler differentials to its action on Weil
differentials. -/
theorem kaehlerDifferentialEquivWeilDifferentialOfSeparating_mapSemilinear_of_perfectField
    [PerfectField k] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (σ : F ≃ₐ[k] F)
    {x : F} (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] (ω : Ω[F⁄k]) :
    kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx
        (mapSemilinear (σ : F →ₐ[k] F) ω) =
      weilDifferentialRepresentation k k F σ
        (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx ω) := by
  have := IntermediateField.isSeparable_adjoin_simple_map σ (x := x)
  conv_lhs => rw [kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq_of_perfectField hF hex
    hx (hx.map σ σ.injective)]
  exact kaehlerDifferentialEquivWeilDifferentialOfSeparating_mapSemilinear hF hex σ hx ω

end TauCeti
