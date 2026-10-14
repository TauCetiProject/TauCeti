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

/-! ### The Weil differential of a moved separating element -/

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

/-- **Automorphisms move the differential of a separating element**: for a `k`-automorphism `σ`
of `F` and a separating element `x`, the Weil differential `dx` is moved by `σ` to `d(σ x)`.
The separability of `F` over `k⟮σ x⟯` is `IntermediateField.isSeparable_adjoin_simple_map`. -/
theorem weilDifferentialRepresentation_weilDifferentialOfSeparating (hF : IsFunctionField k F)
    (σ : F ≃ₐ[k] F) {x : F} (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    [Algebra.IsSeparable k⟮σ x⟯ F] :
    weilDifferentialRepresentation k k F σ (weilDifferentialOfSeparating hF hx) =
      weilDifferentialOfSeparating hF (hx.algHom σ σ.injective) := by
  have hy := hx.algHom σ σ.injective
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
    (map_algebraMap_ratFuncAlgebraOfTranscendental σ σ.injective hx) _ β _ fun P ↦ ?_
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
        (hx.algHom σ σ.injective) (mapSemilinear (σ : F →ₐ[k] F) ω) =
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
  have hmul (f : F) (η : ↥(weilDifferentialSpace k F)) : f • η = weilDifferentialSpaceMul hF f η :=
    Subtype.ext <| by rw [coe_weilDifferentialSpaceModule_smul, coe_weilDifferentialSpaceMul_apply]
  rw [hmul, hmul]
  exact (weilDifferentialRepresentation_weilDifferentialSpaceMul σ hF c _).symm

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
    hx (hx.algHom σ σ.injective)]
  exact kaehlerDifferentialEquivWeilDifferentialOfSeparating_mapSemilinear hF hex σ hx ω

end TauCeti
