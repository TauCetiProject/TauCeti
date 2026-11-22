/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Crystal.WeightTwist
public import TauCeti.RepresentationTheory.LSPath.Central.Transport
public import TauCeti.RepresentationTheory.LSPath.Crystal.Connected
import TauCeti.RepresentationTheory.LSPath.OrbitStable
import TauCeti.RepresentationTheory.LSPath.Realization

/-!
# Central transport of the crystals `B(λ)`

Let `χ` be a weight killed by the simple coroots, such as a central character of a reductive root
datum. The central transport `TauCeti.LSPath.centralTransport χ` identifies the
Lakshmibai–Seshadri paths of shape `λ` with those of shape `λ + χ`, keeping directions and
breaks; on realized paths it adds the linear path `t ↦ t χ` to the presentation by directions and
breaks. This file shows that it is an isomorphism of crystals, once the weights are twisted by the
appropriate central offsets.

For weights `χ` and `σ` killed by the simple coroots, the transport is the strict isomorphism of
normal crystals

  `T(λ, χ; σ) : B(λ)^(σ + χ) ≅ B(λ + χ)^σ`

(`TauCeti.LSPath.centralTransportIso`), where `B(μ)^a` is the crystal `B(μ)` of realized LS paths
of shape `μ` (`TauCeti.LSPath.normalCrystal`) with its weights translated by `a`
(`TauCeti.NormalCrystal.weightTwist`). It preserves the twisted weights, since the transport moves
the endpoint by `χ`. It commutes with the root operators: the realized transported path is the
central shift of the realized path (`TauCeti.LSPath.toPLPath_centralTransport`), and the root
operators commute with the central shift by a vector their coroot form kills
(`TauCeti.PLPath.raise_shiftDistinguished`). The underlying bijection does not depend on `σ`.
The isomorphisms satisfy `T(λ, 0; σ) = id`, the composition law
`T(λ + χ, ψ; σ) ∘ T(λ, χ; σ + ψ) = T(λ, χ + ψ; σ)` and the inverse formula
`T(λ, χ; σ)⁻¹ = T(λ + χ, -χ; σ + χ)`, as identities of the underlying paths; the offsets make the
sources and targets on the two sides the same weighted crystals.

The dominant shape `λ` may lie on chamber walls, `λ + χ` may be zero, `λ` may be central, and the
root system may be empty. The realization `f` is injective, with height forms agreeing with the
simple coroots on `f(M)`; no further condition on `f` is needed, because no two distinct points of
a realized Weyl orbit lie in the same ray
(`RootPairing.pairwise_not_sameRay_image_orbit_weylGroup`).

## Main definitions

* `TauCeti.LSPath.centralTransportIso`: the strict crystal isomorphism
  `T(λ, χ; σ) : B(λ)^(σ + χ) ≅ B(λ + χ)^σ`.

## Main results

* `TauCeti.LSPath.centralTransportIso_mk`: `T(λ, χ; σ)` sends the realized path of `π` to the
  realized path of `centralTransport χ π`.
* `TauCeti.LSPath.coe_centralTransportIso`: on realized paths, `T(λ, χ; σ)` is the central shift
  by `χ`.
* `TauCeti.LSPath.toEquiv_centralTransportIso`: the underlying bijection does not depend on `σ`.
* `TauCeti.LSPath.coe_centralTransportIso_zero`,
  `TauCeti.LSPath.coe_centralTransportIso_centralTransportIso`,
  `TauCeti.LSPath.coe_centralTransportIso_symm`: the zero, composition and inverse laws.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), 329--346, Section 4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, Section 4.
-/

public section

namespace TauCeti.LSPath

open RootPairing

variable {ι M N 𝕜 V : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M}
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  {f : M →+ V} {F : b.support → Module.Dual 𝕜 V}

/-! ### Realized orbits -/

/-- No two distinct points of the realized Weyl orbit `f (W λ)` lie in the same ray. -/
private theorem pairwise_not_sameRay_range
    (hF : ∀ (i : b.support) (m : M), F i (f m) = P.coroot' i m) (lam : M) :
    (Set.range fun w : P.weylGroup ↦ f (w • lam)).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v := by
  have h := P.pairwise_not_sameRay_image_orbit_weylGroup b hF lam
  rwa [MulAction.orbit, ← Set.range_comp] at h

omit [Finite ι] [P.IsReduced] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The realized Weyl orbit `f (W λ)` is stable under the reflection in each realized simple
root. -/
private theorem mapsTo_preReflection_range
    (hF : ∀ (i : b.support) (m : M), F i (f m) = P.coroot' i m) (i : b.support) (lam : M) :
    Set.MapsTo (Module.preReflection (f (P.root i)) (F i))
      (Set.range fun w : P.weylGroup ↦ f (w • lam))
      (Set.range fun w : P.weylGroup ↦ f (w • lam)) := by
  have h := P.mapsTo_preReflection_image_orbit_weylGroup (i : ι) (hF i) lam
  rwa [MulAction.orbit, ← Set.range_comp] at h

/-! ### The transport isomorphism -/

variable (hlam : lam ∈ dominantChamber P b) (hf : Function.Injective f)
  (hF : ∀ (i : b.support) (m : M), F i (f m) = P.coroot' i m)
  (χ : M) (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0)

/-- The realized paths of shape `λ` correspond to the LS paths of shape `λ`. -/
private noncomputable def rangeEquiv (hlam : lam ∈ dominantChamber P b) (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (m : M), F i (f m) = P.coroot' i m) :
    LSPath P b lam ≃ Set.range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f :=
  Equiv.ofInjective _ (toPLPath_injective hlam hf.injOn (pairwise_not_sameRay_range hF lam))

/-- The central transport of realized LS paths, as a bijection of the underlying sets of `B(λ)`
and `B(λ + χ)`. -/
private noncomputable def centralTransportEquiv :
    (Set.range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) ≃
      Set.range fun π : LSPath P b (lam + χ) ↦ π.toPLPath 𝕜 f :=
  (rangeEquiv hlam hf hF).symm.trans ((centralTransport χ hχ).trans
    (rangeEquiv (add_mem_dominantChamber_of_forall_coroot'_eq_zero P b hlam hχ) hf hF))

private theorem coe_centralTransportEquiv_mk (π : LSPath P b lam) :
    (centralTransportEquiv hlam hf hF χ hχ ⟨_, π, rfl⟩).val =
      (centralTransport χ hχ π).toPLPath 𝕜 f := by
  have h : (rangeEquiv hlam hf hF).symm ⟨_, π, rfl⟩ = π :=
    (rangeEquiv hlam hf hF).symm_apply_apply π
  rw [centralTransportEquiv, Equiv.trans_apply, h, Equiv.trans_apply]
  exact congrArg Subtype.val (Equiv.ofInjective_apply _ _ _)

private theorem coe_centralTransportEquiv_symm_mk (π : LSPath P b (lam + χ)) :
    ((centralTransportEquiv hlam hf hF χ hχ).symm ⟨_, π, rfl⟩).val =
      ((centralTransport χ hχ).symm π).toPLPath 𝕜 f := by
  have h : (rangeEquiv (add_mem_dominantChamber_of_forall_coroot'_eq_zero P b hlam hχ) hf
      hF).symm ⟨_, π, rfl⟩ = π :=
    (rangeEquiv _ hf hF).symm_apply_apply π
  rw [centralTransportEquiv, Equiv.symm_trans_apply, Equiv.symm_trans_apply, h, Equiv.symm_symm]
  exact congrArg Subtype.val (Equiv.ofInjective_apply _ _ _)

/-- On realized paths, the central transport is the central shift by `χ` of the distinguished
presentation for the realized orbit `f (W λ)`. -/
private theorem coe_centralTransportEquiv
    (x : Set.range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) :
    (centralTransportEquiv hlam hf hF χ hχ x).val =
      PLPath.shiftDistinguished (Set.range fun w : P.weylGroup ↦ f (w • lam)) (f χ) x.val := by
  obtain ⟨_, π, rfl⟩ := x
  rw [coe_centralTransportEquiv_mk, π.toPLPath_centralTransport χ hχ 𝕜 f hlam hf.injOn
    (pairwise_not_sameRay_range hF lam)]

variable (σ : M) (hσ : ∀ i ∈ b.support, P.coroot' i σ = 0)

/-- **The central transport isomorphism `T(λ, χ; σ) : B(λ)^(σ + χ) ≅ B(λ + χ)^σ`.** For a dominant
shape `λ` and weights `χ`, `σ` killed by the simple coroots, the central transport
`TauCeti.LSPath.centralTransport χ` of Lakshmibai–Seshadri paths is a strict isomorphism from the
crystal `B(λ)` with weights translated by `σ + χ` to the crystal `B(λ + χ)` with weights translated
by `σ`. On realized paths it is the central shift by `χ`
(`TauCeti.LSPath.coe_centralTransportIso`). -/
noncomputable def centralTransportIso :
    NormalCrystal.StrictIso
      ((normalCrystal hlam hf hF).weightTwist (σ + χ)
        fun i ↦ by simpa using congrArg₂ (· + ·) (hσ i i.property) (hχ i i.property))
      ((normalCrystal (add_mem_dominantChamber_of_forall_coroot'_eq_zero P b hlam hχ) hf
        hF).weightTwist σ fun i ↦ by simpa using hσ i i.property) where
  toEquiv := centralTransportEquiv hlam hf hF χ hχ
  wt_toFun x := by
    have hwt : (normalCrystal (add_mem_dominantChamber_of_forall_coroot'_eq_zero P b hlam hχ) hf
        hF).wt (centralTransportEquiv hlam hf hF χ hχ x) = (normalCrystal hlam hf hF).wt x + χ := by
      rw [PLPath.normalCrystalOn_wt_eq_iff, coe_centralTransportEquiv, map_add,
        PLPath.apply_normalCrystalOn_wt]
      obtain ⟨_, π, rfl⟩ := x
      exact PLPath.endpoint_shiftDistinguished (π.hasDistinguished_toPLPath 𝕜 f) (f χ)
    simp only [Equiv.toFun_as_coe, NormalCrystal.weightTwist_wt]
    rw [hwt]
    abel
  e_toFun i x := by
    have hx : PLPath.HasDistinguished (Set.range fun w : P.weylGroup ↦ f (w • lam)) x.val := by
      obtain ⟨π, hπ⟩ := x.property
      exact hπ ▸ π.hasDistinguished_toPLPath 𝕜 f
    have he := PLPath.unattach_normalCrystalOn_e (hf := hf) (hF := hF)
      (hS := isCrystalSet_range_toPLPath hlam f hF) i x
    simp only [Equiv.toFun_as_coe, NormalCrystal.weightTwist_e]
    rw [PLPath.normalCrystalOn_e_eq_map_iff, coe_centralTransportEquiv,
      PLPath.raise_shiftDistinguished hx (mapsTo_preReflection_range hF i lam)
        (pairwise_not_sameRay_range hF lam) (by rw [hF, hχ i i.property, Int.cast_zero]),
      ← he, Option.unattach, Option.map_map]
    exact Option.map_congr fun y _ ↦ (coe_centralTransportEquiv hlam hf hF χ hχ y).symm

/-- **`T(λ, χ; σ)` transports LS paths**: it sends the realized path of an LS path `π` of shape
`λ` to the realized path of its central transport `centralTransport χ π` of shape `λ + χ`. -/
@[simp]
theorem centralTransportIso_mk (π : LSPath P b lam) :
    centralTransportIso hlam hf hF χ hχ σ hσ ⟨π.toPLPath 𝕜 f, Set.mem_range_self π⟩ =
      ⟨(centralTransport χ hχ π).toPLPath 𝕜 f, Set.mem_range_self _⟩ :=
  Subtype.ext (coe_centralTransportEquiv_mk hlam hf hF χ hχ π)

/-- `T(λ, χ; σ)⁻¹` sends the realized path of an LS path `π` of shape `λ + χ` to the realized path
of `(centralTransport χ).symm π`. -/
@[simp]
theorem centralTransportIso_symm_mk (π : LSPath P b (lam + χ)) :
    (centralTransportIso hlam hf hF χ hχ σ hσ).symm ⟨π.toPLPath 𝕜 f, Set.mem_range_self π⟩ =
      ⟨((centralTransport χ hχ).symm π).toPLPath 𝕜 f, Set.mem_range_self _⟩ := by
  rw [← NormalCrystal.StrictIso.coe_toEquiv_symm]
  exact Subtype.ext (coe_centralTransportEquiv_symm_mk hlam hf hF χ hχ π)

/-- **`T(λ, χ; σ)` is the central shift**: it adds the linear path `t ↦ t χ` to the distinguished
presentation of a realized path for the realized orbit `f (W λ)`. -/
theorem coe_centralTransportIso (x : Set.range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) :
    (centralTransportIso hlam hf hF χ hχ σ hσ x).val =
      PLPath.shiftDistinguished (Set.range fun w : P.weylGroup ↦ f (w • lam)) (f χ) x.val :=
  coe_centralTransportEquiv hlam hf hF χ hχ x

/-- The bijection underlying `T(λ, χ; σ)` does not depend on the offset `σ`. -/
theorem toEquiv_centralTransportIso (σ' : M) (hσ' : ∀ i ∈ b.support, P.coroot' i σ' = 0) :
    (centralTransportIso hlam hf hF χ hχ σ hσ).toEquiv =
      (centralTransportIso hlam hf hF χ hχ σ' hσ').toEquiv :=
  (rfl)

/-! ### Zero, composition and inverse laws -/

/-- **`T(λ, 0; σ)` is the identity** on realized paths. -/
@[simp]
theorem coe_centralTransportIso_zero (x : Set.range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) :
    (centralTransportIso hlam hf hF 0 (fun _ _ ↦ map_zero _) σ hσ x).val = x.val := by
  revert x
  rw [Set.forall_subtype_range_iff]
  intro π
  simp only [centralTransportIso_mk, toPLPath_centralTransport_zero]

/-- **The composition law** `T(λ + χ, ψ; σ) ∘ T(λ, χ; σ + ψ) = T(λ, χ + ψ; σ)` on realized paths.
The source `B(λ)^((σ + ψ) + χ)` and target `B((λ + χ) + ψ)^σ` of the composite are those of
`T(λ, χ + ψ; σ)` up to the associativity of the offsets. -/
@[simp]
theorem coe_centralTransportIso_centralTransportIso (ψ : M)
    (hψ : ∀ i ∈ b.support, P.coroot' i ψ = 0)
    (x : Set.range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) :
    (centralTransportIso (add_mem_dominantChamber_of_forall_coroot'_eq_zero P b hlam hχ) hf hF ψ
        hψ σ hσ (centralTransportIso hlam hf hF χ hχ (σ + ψ)
          (fun i hi ↦ by rw [map_add, hσ i hi, hψ i hi, add_zero]) x)).val =
      (centralTransportIso hlam hf hF (χ + ψ)
        (fun i hi ↦ by rw [map_add, hχ i hi, hψ i hi, add_zero]) σ hσ x).val := by
  revert x
  rw [Set.forall_subtype_range_iff]
  intro π
  simp only [centralTransportIso_mk, toPLPath_centralTransport_centralTransport]

/-- **The inverse formula** `T(λ, χ; σ)⁻¹ = T(λ + χ, -χ; σ + χ)` on realized paths. The source
`B(λ + χ)^((σ + χ) - χ)` and target `B((λ + χ) - χ)^(σ + χ)` of the right side are those of
`T(λ, χ; σ)⁻¹` up to cancelling the offsets. -/
theorem coe_centralTransportIso_symm
    (y : Set.range fun π : LSPath P b (lam + χ) ↦ π.toPLPath 𝕜 f) :
    ((centralTransportIso hlam hf hF χ hχ σ hσ).symm y).val =
      (centralTransportIso (add_mem_dominantChamber_of_forall_coroot'_eq_zero P b hlam hχ) hf hF
        (-χ) (fun i hi ↦ by rw [map_neg, hχ i hi, neg_zero]) (σ + χ)
        (fun i hi ↦ by rw [map_add, hσ i hi, hχ i hi, add_zero]) y).val := by
  revert y
  rw [Set.forall_subtype_range_iff]
  intro π
  simp only [centralTransportIso_symm_mk, centralTransportIso_mk]
  exact (toPLPath_centralTransport_neg χ hχ 𝕜 f π).symm

end TauCeti.LSPath
