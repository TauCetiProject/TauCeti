/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Principal.Equiv
public import TauCeti.Topology.VectorBundle.Associated.Metric

/-!
# Associated bundles of equivalent principal bundles

An equivalence `ψ : P ≃ Q` of principal `G`-bundles over the same base
(`TauCeti.PrincipalBundle.Equiv`) identifies the bundles associated to `P` and `Q` by the same
continuous linear action of `G` on a model space `F`: the map `[p, v] ↦ [ψ p, v]` is well defined
because `ψ` is equivariant, and it is a fibrewise continuous linear equivalence
`P ×_G F ≃ Q ×_G F` (`TauCeti.PrincipalBundle.Equiv.associatedContinuousLinearEquiv`), continuous
on total spaces (`TauCeti.PrincipalBundle.Equiv.continuous_associatedContinuousLinearEquiv`). It is
functorial: the identity of `P` induces the identity, inverses induce inverses and composites
induce composites. For an isometric action it preserves the fibre norms
(`TauCeti.PrincipalBundle.Equiv.norm_associatedContinuousLinearEquiv`).

## Main definitions

* `TauCeti.PrincipalBundle.Equiv.associatedContinuousLinearEquiv`: the fibrewise continuous
  linear equivalence `P ×_G F ≃ Q ×_G F` induced by an equivalence `P ≃ Q`.

## Main results

* `TauCeti.PrincipalBundle.Equiv.associatedContinuousLinearEquiv_mk`: `[p, v] ↦ [ψ p, v]`.
* `TauCeti.PrincipalBundle.Equiv.continuous_associatedContinuousLinearEquiv`: it is continuous on
  total spaces.
* `TauCeti.PrincipalBundle.Equiv.associatedContinuousLinearEquiv_refl`,
  `TauCeti.PrincipalBundle.Equiv.associatedContinuousLinearEquiv_symm`,
  `TauCeti.PrincipalBundle.Equiv.associatedContinuousLinearEquiv_trans`: functoriality.
* `TauCeti.PrincipalBundle.Equiv.norm_associatedContinuousLinearEquiv`: for an isometric action
  it preserves norms.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, volume I, Chapter I, §5.
-/

public noncomputable section

open Bundle MulOpposite

namespace TauCeti.PrincipalBundle.Equiv

variable {𝕜 B G F : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B] [Group G] [TopologicalSpace G]
  {P Q R : B → Type*}
  [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [TopologicalSpace (TotalSpace G Q)] [∀ b, TopologicalSpace (Q b)]
  [FiberBundle G Q] [∀ b, MulAction Gᵐᵒᵖ (Q b)] [PrincipalBundle G Q]
  [TopologicalSpace (TotalSpace G R)] [∀ b, TopologicalSpace (R b)]
  [FiberBundle G R] [∀ b, MulAction Gᵐᵒᵖ (R b)] [PrincipalBundle G R]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [DistribMulAction G F] [SMulCommClass G 𝕜 F]
  [ContinuousSMul G F]

variable (𝕜 F) in
/-- **The associated bundles of equivalent principal bundles are equivalent**: an equivalence
`ψ : P ≃ Q` of principal `G`-bundles induces the fibrewise continuous linear equivalence
`P ×_G F ≃ Q ×_G F`, `[p, v] ↦ [ψ p, v]`
(`TauCeti.PrincipalBundle.Equiv.associatedContinuousLinearEquiv_mk`), for a continuous linear
action of `G` on `F`. As a bijection it is `TauCeti.AssociatedBundle.equivOfEquivariant` along the
identity of `G`; here it is continuous linear. For an isometric action it preserves norms
(`TauCeti.PrincipalBundle.Equiv.norm_associatedContinuousLinearEquiv`). It is defined through
the frame of `P` with coordinate `1` in the chart at `b`; it does not depend on that choice because
`ψ` is equivariant. -/
def associatedContinuousLinearEquiv (ψ : Equiv G P Q) (b : B) :
    AssociatedBundle G P F b ≃L[𝕜] AssociatedBundle G Q F b :=
  (AssociatedBundle.mkContinuousLinearEquiv 𝕜 G
      ((FiberBundle.homeomorphAt G P b).symm 1)).symm.trans
    (AssociatedBundle.mkContinuousLinearEquiv 𝕜 G
      (ψ.toEquiv b ((FiberBundle.homeomorphAt G P b).symm 1)))

/-- **The induced equivalence in a frame**: `[p, v] ↦ [ψ p, v]` for every point `p` of the fibre
of `P` over `b`. -/
@[simp]
theorem associatedContinuousLinearEquiv_mk (ψ : Equiv G P Q) {b : B} (p : P b) (v : F) :
    ψ.associatedContinuousLinearEquiv 𝕜 F b (AssociatedBundle.mk G p v) =
      AssociatedBundle.mk G (ψ.toEquiv b p) v := by
  rw [associatedContinuousLinearEquiv, ContinuousLinearEquiv.trans_apply,
    AssociatedBundle.mkContinuousLinearEquiv_symm_apply_mk,
    AssociatedBundle.mkContinuousLinearEquiv_apply, ← AssociatedBundle.mk_smul, ← ψ.map_smul,
    PrincipalBundle.smul_division]

/-- **The inverse of the induced equivalence in a frame**: `[ψ p, v] ↦ [p, v]`. -/
@[simp]
theorem associatedContinuousLinearEquiv_symm_mk (ψ : Equiv G P Q) {b : B} (p : P b) (v : F) :
    (ψ.associatedContinuousLinearEquiv 𝕜 F b).symm (AssociatedBundle.mk G (ψ.toEquiv b p) v) =
      AssociatedBundle.mk G p v :=
  (ContinuousLinearEquiv.symm_apply_eq _).2 (associatedContinuousLinearEquiv_mk ψ p v).symm

/-- The identity equivalence of a principal bundle induces the identity of its associated
bundles. -/
@[simp]
theorem associatedContinuousLinearEquiv_refl (b : B) :
    (Equiv.refl G P).associatedContinuousLinearEquiv 𝕜 F b = ContinuousLinearEquiv.refl 𝕜 _ := by
  ext v
  obtain ⟨p, v, rfl⟩ := AssociatedBundle.exists_mk v
  rw [associatedContinuousLinearEquiv_mk, refl_toEquiv, _root_.Equiv.refl_apply]
  rfl

/-- The inverse of an equivalence of principal bundles induces the inverse equivalence of their
associated bundles. -/
@[simp]
theorem associatedContinuousLinearEquiv_symm (ψ : Equiv G P Q) (b : B) :
    ψ.symm.associatedContinuousLinearEquiv 𝕜 F b =
      (ψ.associatedContinuousLinearEquiv 𝕜 F b).symm := by
  ext v
  obtain ⟨q, v, rfl⟩ := AssociatedBundle.exists_mk v
  rw [associatedContinuousLinearEquiv_mk, symm_toEquiv,
    ← associatedContinuousLinearEquiv_symm_mk (𝕜 := 𝕜) ψ,
    _root_.Equiv.apply_symm_apply]

/-- A composite of equivalences of principal bundles induces the composite equivalence of their
associated bundles. -/
@[simp]
theorem associatedContinuousLinearEquiv_trans (ψ : Equiv G P Q) (ψ' : Equiv G Q R) (b : B) :
    (ψ.trans ψ').associatedContinuousLinearEquiv 𝕜 F b =
      (ψ.associatedContinuousLinearEquiv 𝕜 F b).trans
        (ψ'.associatedContinuousLinearEquiv 𝕜 F b) := by
  ext v
  obtain ⟨p, v, rfl⟩ := AssociatedBundle.exists_mk v
  rw [ContinuousLinearEquiv.trans_apply, associatedContinuousLinearEquiv_mk,
    associatedContinuousLinearEquiv_mk, associatedContinuousLinearEquiv_mk, trans_toEquiv,
    _root_.Equiv.trans_apply]

/-- **The induced equivalence is continuous** on total spaces: the total space of `P ×_G F` is the
quotient of `P × F`, on which the map is `(p, v) ↦ [ψ p, v]`. -/
theorem continuous_associatedContinuousLinearEquiv (ψ : Equiv G P Q) :
    Continuous fun v : TotalSpace F (AssociatedBundle G P F) ↦
      TotalSpace.mk' F v.proj (ψ.associatedContinuousLinearEquiv 𝕜 F v.proj v.snd) := by
  refine (AssociatedBundle.isOpenQuotientMap_totalSpaceMk_mk G P F).continuous_comp_iff.1 ?_
  have hc : Continuous fun y : TotalSpace G P × F ↦
      TotalSpace.mk' F y.1.proj (AssociatedBundle.mk G (ψ.toEquiv y.1.proj y.1.snd) y.2) :=
    Continuous.totalSpaceMk_associatedBundleMk (f := fun y : TotalSpace G P × F ↦ y.1.proj)
      (ψ.continuous_toFun.comp continuous_fst) continuous_snd
  refine hc.congr fun y ↦ ?_
  exact (congrArg (TotalSpace.mk _) (associatedContinuousLinearEquiv_mk ψ y.1.snd y.2)).symm

/-- **The induced equivalence preserves norms** for an isometric action of `G` on `F`: in a frame
both `[p, v]` and `[ψ p, v]` have norm `‖v‖`. -/
@[simp]
theorem norm_associatedContinuousLinearEquiv [IsIsometricSMul G F] (ψ : Equiv G P Q) {b : B}
    (v : AssociatedBundle G P F b) : ‖ψ.associatedContinuousLinearEquiv 𝕜 F b v‖ = ‖v‖ := by
  obtain ⟨p, v, rfl⟩ := AssociatedBundle.exists_mk v
  rw [associatedContinuousLinearEquiv_mk, AssociatedBundle.norm_mk, AssociatedBundle.norm_mk]

end TauCeti.PrincipalBundle.Equiv
