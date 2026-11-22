/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Topology.Compactness.Compact
public import TauCeti.Topology.Algebra.Module.PontryaginDual.Duality

/-!
# Contragredient group actions on coefficient-linear Pontryagin duals

Given `ρ : ContRepresentation R G M`—which, following Mathlib's convention, equips each `g : G`
with a continuous `R`-linear action operator `ρ g : M →L[R] M` without assuming joint continuity of
`G × M → M`—this file defines the contragredient `ContRepresentation` `ρ.contragredient E` on
`ModulePontryaginDual R E M` via `(g · φ)(x) = φ(ρ g⁻¹ x)` and functoriality
`f.contragredient E` on continuous intertwining maps.

Joint continuity `(g, φ) ↦ ρ.contragredient E g φ` is proved separately when `G` has continuous
inversion and `ρ` acts jointly continuously on `M` (`continuous_contragredient_of_discrete` for
discrete `M`; `continuous_contragredient_of_compact` for compact `M` and discrete `E`). We also
establish central-character inversion, and `G`-equivariant biduality and full faithfulness on the
corresponding categories of continuous `G`-representations (with operatorwise continuity).

## References

* V. Paškūnas, *The image of Colmez's Montreal functor*, Publ. Math. IHÉS 118 (2013), §2.
-/

public section

universe u v w w'

open scoped ContRepresentation

section Contragredient

open TauCeti TauCeti.ModulePontryaginDual

variable {R : Type u} {G : Type*} {M : Type w} {N : Type w'}
  [CommRing R] [Group G]
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]

/-- The contragredient continuous representation of `G` on `ModulePontryaginDual R E M`, given by
`(g · φ)(x) = φ(ρ g⁻¹ x)`. Following Mathlib's `ContRepresentation`, this asserts that each
group element acts by a continuous `R`-linear operator; for joint continuity of the `G`-action, see
`TauCeti.ModulePontryaginDual.continuous_contragredient_of_discrete` and
`TauCeti.ModulePontryaginDual.continuous_contragredient_of_compact`. -/
def ContRepresentation.contragredient (ρ : ContRepresentation R G M) (E : Type v)
    [AddCommGroup E] [Module R E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousConstSMul R E] :
    ContRepresentation R G (ModulePontryaginDual R E M) where
  toMonoidHom :=
    { toFun := fun g ↦ (ρ g⁻¹).pontryaginDualMap (E := E)
      map_one' := by ext φ x; simp
      map_mul' := fun g h ↦ by ext φ x; simp [mul_inv_rev, map_mul] }

@[simp] theorem ContRepresentation.contragredient_apply (ρ : ContRepresentation R G M)
    (E : Type v) [AddCommGroup E] [Module R E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousConstSMul R E] (g : G) (φ : ModulePontryaginDual R E M) (x : M) :
    ρ.contragredient E g φ x = φ (ρ g⁻¹ x) :=
  (ρ g⁻¹).pontryaginDualMap_apply φ x

/-- A continuous intertwining map dualizes to one between the contragredient representations. -/
def ContIntertwiningMap.contragredient {ρ₁ : ContRepresentation R G M}
    {ρ₂ : ContRepresentation R G N} (f : ρ₁ →ⁱL ρ₂) (E : Type v)
    [AddCommGroup E] [Module R E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousConstSMul R E] :
    ρ₂.contragredient E →ⁱL ρ₁.contragredient E where
  toContinuousLinearMap := f.toContinuousLinearMap.pontryaginDualMap (E := E)
  isIntertwining' g := by
    ext ψ x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.pontryaginDualMap_apply,
      ContRepresentation.contragredient_apply, ContIntertwiningMap.toContinuousLinearMap_apply]
    rw [f.isIntertwining g⁻¹ x]

@[simp] theorem ContIntertwiningMap.contragredient_apply {ρ₁ : ContRepresentation R G M}
    {ρ₂ : ContRepresentation R G N} (f : ρ₁ →ⁱL ρ₂) (E : Type v)
    [AddCommGroup E] [Module R E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousConstSMul R E] (ψ : ModulePontryaginDual R E N) (x : M) :
    f.contragredient E ψ x = ψ (f x) :=
  f.toContinuousLinearMap.pontryaginDualMap_apply ψ x

/-- Evaluation into the double dual intertwines `ρ` with its double contragredient. -/
theorem ContRepresentation.contragredient_contragredient_eval (ρ : ContRepresentation R G M)
    (E : Type v) [AddCommGroup E] [Module R E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousConstSMul R E] (g : G) (x : M) :
    (ρ.contragredient E).contragredient E g (eval R E M x) = eval R E M (ρ g x) :=
  ModulePontryaginDual.ext fun _ ↦ by simp

end Contragredient

namespace TauCeti.ModulePontryaginDual

section Basic

variable {R : Type u} (E : Type v) {G : Type*} {M : Type w} {N : Type w'}
  [CommRing R] [Group G]
  [AddCommGroup E] [Module R E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousConstSMul R E]
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]

/-- Scalar action by a unit `u : Rˣ` on `M` dualizes to scalar action by `u⁻¹` on `M^∨`. -/
theorem contragredient_eq_inv_smul (ρ : ContRepresentation R G M) {g : G} {u : Rˣ}
    (hg : ∀ x : M, ρ g x = (u : R) • x) (φ : ModulePontryaginDual R E M) :
    ρ.contragredient E g φ = ((u⁻¹ : Rˣ) : R) • φ := by
  ext x
  have hmul : (u : R) • ρ g⁻¹ x = x := by
    rw [← hg, ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
  have hinv : ρ g⁻¹ x = ((u⁻¹ : Rˣ) : R) • x := by
    rw [← one_smul R (ρ g⁻¹ x), ← Units.inv_mul u, mul_smul, hmul]
  rw [ρ.contragredient_apply, hinv, map_smul, smul_apply]

section JointContinuity

variable [TopologicalSpace G] [ContinuousInv G]

/-- If `M` is discrete and `G` acts jointly continuously on `M`, then the contragredient action
of `G` on `ModulePontryaginDual R E M` is jointly continuous. -/
theorem continuous_contragredient_of_discrete [DiscreteTopology M]
    (ρ : ContRepresentation R G M) (hρ : Continuous (fun p : G × M ↦ ρ p.1 p.2)) :
    Continuous (fun p : G × ModulePontryaginDual R E M ↦ ρ.contragredient E p.1 p.2) :=
  have heval : Continuous fun p : M × ModulePontryaginDual R E M ↦ p.2 p.1 :=
    continuous_prod_of_discrete_left.mpr fun m ↦ continuous_eval_const m
  continuous_of_continuous_eval fun x ↦
    (heval.comp <|
      (hρ.comp ((continuous_inv.comp continuous_fst).prodMk (continuous_const (y := x)))).prodMk
        continuous_snd).congr fun _ ↦ (ρ.contragredient_apply E _ _ _).symm

/-- If `M` is compact, `E` is discrete, and `G` acts jointly continuously on `M`, then the
contragredient action of `G` on `ModulePontryaginDual R E M` is jointly continuous. -/
theorem continuous_contragredient_of_compact [CompactSpace M] [DiscreteTopology E]
    (ρ : ContRepresentation R G M) (hρ : Continuous (fun p : G × M ↦ ρ p.1 p.2)) :
    Continuous (fun p : G × ModulePontryaginDual R E M ↦ ρ.contragredient E p.1 p.2) :=
  continuous_prod_of_discrete_right.mpr fun φ ↦
    isInducing_toContinuousMap.continuous_iff.mpr <|
      ContinuousMap.continuous_of_continuous_uncurry _ <|
        ((map_continuous φ).comp
          (hρ.comp ((continuous_inv.comp continuous_fst).prodMk continuous_snd))).congr
            fun _ ↦ by simp [Function.uncurry]

/-- For a compact continuous `G`-module `M` and discrete `E`, every level set
`{g : G | ρ.contragredient E g φ = ψ}` is open in `G`. -/
theorem isOpen_setOf_contragredient_eq_of_compact [CompactSpace M] [DiscreteTopology E]
    (ρ : ContRepresentation R G M) (hρ : Continuous (fun p : G × M ↦ ρ p.1 p.2))
    (φ ψ : ModulePontryaginDual R E M) : IsOpen {g : G | ρ.contragredient E g φ = ψ} :=
  (isOpen_discrete {ψ}).preimage
    ((continuous_contragredient_of_compact E ρ hρ).comp (continuous_id.prodMk continuous_const))

/-- If `M` is compact, `E` is discrete, and `G` acts jointly continuously on `M`, then every
element of `ModulePontryaginDual R E M` has an open stabilizer in `G`. -/
theorem isOpen_stabilizer_contragredient_of_compact [CompactSpace M] [DiscreteTopology E]
    (ρ : ContRepresentation R G M) (hρ : Continuous (fun p : G × M ↦ ρ p.1 p.2))
    (φ : ModulePontryaginDual R E M) : IsOpen {g : G | ρ.contragredient E g φ = φ} :=
  isOpen_setOf_contragredient_eq_of_compact E ρ hρ φ φ

end JointContinuity

private theorem comp_intertwining_apply {P : Type*} [AddCommGroup P] [Module R P]
    [TopologicalSpace P] [IsTopologicalAddGroup P] {ρ₁ : ContRepresentation R G M}
    {ρ₂ : ContRepresentation R G N} {ρ₃ : ContRepresentation R G P}
    (g : ρ₂ →ⁱL ρ₃) (f : ρ₁ →ⁱL ρ₂) (x : M) :
    (g.comp f) x = g (f x) :=
  rfl

/-- Full faithfulness of `ContIntertwiningMap.contragredient` follows from `G`-equivariant
biduality equivalences. -/
private theorem bijective_mapIntertwining_of_equiv
    {ρ₁ : ContRepresentation R G M} {ρ₂ : ContRepresentation R G N}
    (e₁ : ρ₁.Equiv ((ρ₁.contragredient E).contragredient E))
    (e₂ : ρ₂.Equiv ((ρ₂.contragredient E).contragredient E))
    (he₁ : ∀ x φ, e₁ x φ = φ x) (he₂ : ∀ x φ, e₂ x φ = φ x) :
    Function.Bijective
      (ContIntertwiningMap.contragredient (E := E) (ρ₁ := ρ₁) (ρ₂ := ρ₂)) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨fun g ↦
    e₂.symm.toContIntertwiningMap.comp ((g.contragredient E).comp e₁.toContIntertwiningMap),
    fun f ↦ by
      ext x
      have h2 : (f.contragredient E).contragredient E (e₁ x) = e₂ (f x) :=
        ext fun φ ↦ by simp [he₁, he₂]
      simp only [ContIntertwiningMap.toContinuousLinearMap_apply, comp_intertwining_apply,
        ContRepresentation.Equiv.coe_toContIntertwiningMap]
      rw [h2, e₂.symm_apply_apply],
    fun g ↦ by
      ext φ x
      simp only [ContIntertwiningMap.toContinuousLinearMap_apply,
        ContIntertwiningMap.contragredient_apply, comp_intertwining_apply,
        ContRepresentation.Equiv.coe_toContIntertwiningMap]
      rw [← he₂ _ φ, e₂.apply_symm_apply, ContIntertwiningMap.contragredient_apply, he₁]⟩

end Basic

section CompactBiduality

variable {R : Type u} (E : Type v) {G : Type*}
  [CommRing R] [TopologicalSpace R] [CompactSpace R] [Group G]
  [AddCommGroup E] [Module R E] [TopologicalSpace E] [DiscreteTopology E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul R E] [Module.Injective R E] [Small.{v} R]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
include hE

/-- `G`-equivariant biduality for a compact `ContRepresentation` (operatorwise continuous
`G`-action, without assuming joint continuity on `G × N`). -/
noncomputable def evalEquivOfCompactRep
    {N : Type w} [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    (hN : IsCompactModule R N) (ρ : ContRepresentation R G N) :
    ρ.Equiv ((ρ.contragredient E).contragredient E) :=
  ContRepresentation.Equiv.mk (evalEquivOfCompact (E := E) hE hN) fun g ↦ by
    have heval (y : N) :
        (evalEquivOfCompact (E := E) hE hN : N → ModulePontryaginDual R E _) y = eval R E N y :=
      ext fun φ ↦ (evalEquivOfCompact_apply hE hN y φ).trans (eval_apply y φ).symm
    refine ContinuousLinearMap.ext fun x ↦ ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, heval]
    exact (ρ.contragredient_contragredient_eval E g x).symm

@[simp] theorem evalEquivOfCompactRep_apply
    {N : Type w} [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    (hN : IsCompactModule R N) (ρ : ContRepresentation R G N) (x : N)
    (φ : ModulePontryaginDual R E N) :
    evalEquivOfCompactRep E hE hN ρ x φ = φ x := evalEquivOfCompact_apply hE hN x φ

/-- Full faithfulness of `ContIntertwiningMap.contragredient` on compact `ContRepresentation`s
(operatorwise continuous `G`-actions). -/
theorem bijective_mapIntertwining_of_compact {N₁ N₂ : Type*}
    [AddCommGroup N₁] [Module R N₁] [TopologicalSpace N₁] [IsTopologicalAddGroup N₁]
    [AddCommGroup N₂] [Module R N₂] [TopologicalSpace N₂] [IsTopologicalAddGroup N₂]
    (hN₁ : IsCompactModule R N₁) (hN₂ : IsCompactModule R N₂)
    (ρ₁ : ContRepresentation R G N₁) (ρ₂ : ContRepresentation R G N₂) :
    Function.Bijective
      (ContIntertwiningMap.contragredient (E := E) (ρ₁ := ρ₁) (ρ₂ := ρ₂)) :=
  bijective_mapIntertwining_of_equiv E
    (evalEquivOfCompactRep E hE hN₁ ρ₁) (evalEquivOfCompactRep E hE hN₂ ρ₂)
    (evalEquivOfCompactRep_apply E hE hN₁ ρ₁) (evalEquivOfCompactRep_apply E hE hN₂ ρ₂)

end CompactBiduality

section DiscreteBiduality

variable {R : Type u} (E : Type v) {G : Type*}
  [CommRing R] [IsLocalRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [TotallyDisconnectedSpace R] [Group G]
  [AddCommGroup E] [Module R E] [TopologicalSpace E] [DiscreteTopology E]
  [ContinuousSMul R E] [Module.Injective R E] [Small.{v} R]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
include hE

/-- `G`-equivariant biduality for a discrete `ContRepresentation` (operatorwise continuous
`G`-action) with continuous `R`-action. -/
noncomputable def evalEquivOfDiscreteRep
    {M : Type w} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul R M] (ρ : ContRepresentation R G M) :
    ρ.Equiv ((ρ.contragredient E).contragredient E) :=
  ContRepresentation.Equiv.mk (evalEquivOfDiscrete (E := E) hE) fun g ↦ by
    have heval (y : M) :
        (evalEquivOfDiscrete (E := E) hE : M → ModulePontryaginDual R E _) y = eval R E M y :=
      ext fun φ ↦ (evalEquivOfDiscrete_apply hE y φ).trans (eval_apply y φ).symm
    refine ContinuousLinearMap.ext fun x ↦ ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, heval]
    exact (ρ.contragredient_contragredient_eval E g x).symm

@[simp] theorem evalEquivOfDiscreteRep_apply
    {M : Type w} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul R M] (ρ : ContRepresentation R G M) (x : M) (φ : ModulePontryaginDual R E M) :
    evalEquivOfDiscreteRep E hE ρ x φ = φ x := evalEquivOfDiscrete_apply hE x φ

/-- Full faithfulness of `ContIntertwiningMap.contragredient` on discrete `ContRepresentation`s
(operatorwise continuous `G`-actions) with continuous `R`-action. -/
theorem bijective_mapIntertwining_of_discrete {M₁ M₂ : Type*}
    [AddCommGroup M₁] [Module R M₁] [TopologicalSpace M₁] [DiscreteTopology M₁]
    [ContinuousSMul R M₁]
    [AddCommGroup M₂] [Module R M₂] [TopologicalSpace M₂] [DiscreteTopology M₂]
    [ContinuousSMul R M₂]
    (ρ₁ : ContRepresentation R G M₁) (ρ₂ : ContRepresentation R G M₂) :
    Function.Bijective
      (ContIntertwiningMap.contragredient (E := E) (ρ₁ := ρ₁) (ρ₂ := ρ₂)) :=
  bijective_mapIntertwining_of_equiv E
    (evalEquivOfDiscreteRep E hE ρ₁) (evalEquivOfDiscreteRep E hE ρ₂)
    (evalEquivOfDiscreteRep_apply E hE ρ₁) (evalEquivOfDiscreteRep_apply E hE ρ₂)

end DiscreteBiduality

end TauCeti.ModulePontryaginDual
