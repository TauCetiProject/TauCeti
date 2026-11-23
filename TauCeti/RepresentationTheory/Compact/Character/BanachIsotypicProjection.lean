/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Character.IsotypicProjection
public import TauCeti.RepresentationTheory.GFinite
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import TauCeti.RepresentationTheory.Compact.GFiniteDensity
import TauCeti.RepresentationTheory.Continuous.StronglyContinuous

/-!
# Isotypic projectors on Banach representations of compact groups

Let `π` be a strongly continuous representation of a compact group `G` on a Banach space `V` over
`ℝ` or `ℂ`: every orbit `g ↦ π g v` is continuous, while `g ↦ π g` need not be continuous in the
operator norm. A continuous function `f` on `G` acts on `V` by the **strong integrated operator**

`π(f) v = ∫ g, f g • π g v ∂(haarProb G)`,

a bounded operator by the Banach–Steinhaus theorem. When `π` is continuous in the operator norm it
is main's `integratedOperator`. For a class function it commutes with the action, and it is natural
with respect to continuous intertwiners.

For a finite-dimensional continuous irreducible `σ` over an algebraically closed field, the kernel
`dim(σ) · conj(χ_σ)` of `ContRepresentation.isotypicKernel` gives the **isotypic projector**
`e_σ = π(dim(σ) · conj(χ_σ))`, a continuous self-intertwiner of `π`. On an operator-norm
continuous representation, in particular a finite-dimensional one, it is main's
`isotypicProjector`. It is idempotent, and `e_σ ∘ e_τ = 0` for inequivalent irreducibles `σ`,
`τ`: both identities hold on each `G`-finite vector, where `e_σ` is the finite-dimensional
projector of the orbit span, and the `G`-finite vectors are dense
(`ContRepresentation.dense_gFiniteSubmodule`).

## Main definitions

* `ContRepresentation.strongIntegratedOperator π hπ f`: the operator `v ↦ ∫ g, f g • π g v`.
* `ContRepresentation.banachIsotypicProjector π hπ σ hσ`: the isotypic projector `e_σ`, a
  continuous self-intertwiner of `π`.

## Main results

* `ContRepresentation.strongIntegratedOperator_eq_integratedOperator`: for an operator-norm
  continuous representation the strong integrated operator is `integratedOperator`.
* `ContRepresentation.strongIntegratedOperator_comp`: a class function acts by an intertwiner.
* `ContRepresentation.comp_strongIntegratedOperator`: naturality in continuous intertwiners.
* `ContRepresentation.banachIsotypicProjector_eq_isotypicProjector`: on an operator-norm
  continuous representation `e_σ` is `isotypicProjector`.
* `ContRepresentation.banachIsotypicProjector_comp_self`: `e_σ` is idempotent.
* `ContRepresentation.banachIsotypicProjector_comp_of_not_equiv`: `e_σ ∘ e_τ = 0` for
  inequivalent irreducibles `σ` and `τ`.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter III.
* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, §4.1.
-/

public section

noncomputable section

open MeasureTheory TauCeti
open scoped MonoidAlgebra

namespace ContRepresentation

variable {k G V : Type*} [RCLike k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace k V] [NormedSpace ℝ V] [SMulCommClass ℝ k V]

/-! ### The strong integrated operator -/

section Strong

variable (π : ContRepresentation k G V) (hπ : ∀ v, Continuous fun g ↦ π g v)

/-- The continuous map `g ↦ f g • π g v` integrated by the strong integrated operator. -/
private def weightedOrbit (f : C(G, k)) (v : V) : C(G, V) :=
  ⟨fun g ↦ f g • π g v, f.continuous.smul (hπ v)⟩

omit [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedSpace ℝ V] [SMulCommClass ℝ k V] in
private theorem weightedOrbit_apply (f : C(G, k)) (v : V) (g : G) :
    weightedOrbit π hπ f v g = f g • π g v :=
  (rfl)

/-- The strong integrated operator as a linear map. -/
private def strongIntegratedOperatorₗ (f : C(G, k)) : V →ₗ[k] V where
  toFun v := haarAverage G (𝕜 := k) (weightedOrbit π hπ f v)
  map_add' v w := by
    rw [← map_add]
    congr 1
    ext g
    simp [weightedOrbit_apply]
  map_smul' c v := by
    rw [RingHom.id_apply, ← map_smul]
    congr 1
    ext g
    simp [weightedOrbit_apply, smul_comm (f g) c]

variable [CompleteSpace V]

/-- The **strong integrated operator** `π(f) v = ∫ g, f g • π g v` of a continuous function `f` on
a strongly continuous Banach representation of a compact group. It is bounded because the
operators `π g` are uniformly bounded, by the Banach–Steinhaus theorem. -/
def strongIntegratedOperator (f : C(G, k)) : V →L[k] V :=
  (strongIntegratedOperatorₗ π hπ f).mkContinuousOfExistsBound <| by
    obtain ⟨C, hC⟩ := banach_steinhaus (g := fun g : G ↦ (π g : V →L[k] V)) fun v ↦ by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hπ v).continuousOn
      exact ⟨C, fun g ↦ hC g (Set.mem_univ g)⟩
    refine ⟨‖f‖ * C, fun v ↦ (norm_haarAverage_apply_le G _).trans ?_⟩
    refine ContinuousMap.norm_le _ (by
      have := (norm_nonneg _).trans (hC 1)
      positivity) |>.2 fun g ↦ ?_
    rw [weightedOrbit_apply, norm_smul, mul_assoc]
    exact mul_le_mul (f.norm_coe_le_norm g) (((π g : V →L[k] V).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hC g) (norm_nonneg v))) (norm_nonneg _) (norm_nonneg _)

/-- The strong integrated operator is the Haar integral of the weighted orbit. -/
theorem strongIntegratedOperator_apply (f : C(G, k)) (v : V) :
    strongIntegratedOperator π hπ f v = ∫ g, f g • π g v ∂haarProb G :=
  haarAverage_apply G _

/-- For a representation that is continuous in the operator norm, the strong integrated operator
is `integratedOperator`. -/
theorem strongIntegratedOperator_eq_integratedOperator (hπ' : Continuous π) (f : C(G, k)) :
    strongIntegratedOperator π hπ f = integratedOperator π hπ' f := by
  ext v
  rw [strongIntegratedOperator_apply, integratedOperator_apply]

/-- **A class function acts by an intertwiner.** -/
theorem strongIntegratedOperator_comp {f : C(G, k)} (hf : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (h : G) :
    (strongIntegratedOperator π hπ f).comp (π h) =
      (π h : V →L[k] V).comp (strongIntegratedOperator π hπ f) := by
  ext v
  have hint : Integrable (fun g ↦ f g • π g v) (haarProb G) :=
    integrable_continuousMap G (weightedOrbit π hπ f v)
  have hclass (g : G) : f (g * h⁻¹) = f (h⁻¹ * g) := by
    simpa [mul_assoc] using (hf (g * h⁻¹) h⁻¹).symm
  simp only [ContinuousLinearMap.comp_apply]
  rw [strongIntegratedOperator_apply, strongIntegratedOperator_apply,
    ← (π h : V →L[k] V).integral_comp_comm hint]
  calc ∫ g, f g • π g (π h v) ∂haarProb G
      = ∫ g, f (g * h⁻¹) • π g v ∂haarProb G := by
        rw [← integral_mul_right_eq_self (fun g ↦ f g • π g (π h v)) h⁻¹]
        congr 1 with g
        simp only [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel_right]
    _ = ∫ g, f (h⁻¹ * g) • π g v ∂haarProb G := by simp only [hclass]
    _ = ∫ g, (π h : V →L[k] V) (f g • π g v) ∂haarProb G := by
        rw [← integral_mul_left_eq_self (fun g ↦ (π h : V →L[k] V) (f g • π g v)) h⁻¹]
        congr 1 with g
        rw [map_smul, ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left]

/-- **Naturality.** A continuous intertwiner between strongly continuous Banach representations
commutes with the strong integrated operators of the same function. -/
theorem comp_strongIntegratedOperator {W : Type*} [NormedAddCommGroup W] [NormedSpace k W]
    [NormedSpace ℝ W] [SMulCommClass ℝ k W] [CompleteSpace W] (ρ : ContRepresentation k G W)
    (hρ : ∀ w, Continuous fun g ↦ ρ g w) (T : ContIntertwiningMap π ρ) (f : C(G, k)) :
    T.toContinuousLinearMap.comp (strongIntegratedOperator π hπ f) =
      (strongIntegratedOperator ρ hρ f).comp T.toContinuousLinearMap := by
  ext v
  have hint : Integrable (fun g ↦ f g • π g v) (haarProb G) :=
    integrable_continuousMap G (weightedOrbit π hπ f v)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    strongIntegratedOperator_apply, strongIntegratedOperator_apply,
    ← T.toContinuousLinearMap.integral_comp_comm hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  simp only [map_smul]
  congr 1
  exact T.isIntertwining g v

end Strong

/-! ### The isotypic projector -/

variable [CompleteSpace V] (π : ContRepresentation k G V) (hπ : ∀ v, Continuous fun g ↦ π g v)
  {W W' : Type*} [NormedAddCommGroup W] [NormedSpace k W] [FiniteDimensional k W]
  [NormedAddCommGroup W'] [NormedSpace k W'] [FiniteDimensional k W']

/-- The **isotypic projector** `e_σ = ∫ g, dim(σ) conj(χ_σ g) • π g` of a strongly continuous
Banach representation of a compact group, for a finite-dimensional continuous representation `σ`,
as a continuous self-intertwiner. For `σ` irreducible over an algebraically closed field it is
idempotent (`banachIsotypicProjector_comp_self`). -/
def banachIsotypicProjector (σ : ContRepresentation k G W) (hσ : Continuous σ) :
    ContIntertwiningMap π π where
  __ := strongIntegratedOperator π hπ (isotypicKernel σ hσ)
  isIntertwining' := strongIntegratedOperator_comp π hπ (isotypicKernel_conj σ hσ)

/-- The continuous linear map underlying `e_σ` is the strong integrated operator of the
isotypic kernel. -/
@[simp]
theorem toContinuousLinearMap_banachIsotypicProjector (σ : ContRepresentation k G W)
    (hσ : Continuous σ) :
    (banachIsotypicProjector π hπ σ hσ).toContinuousLinearMap =
      strongIntegratedOperator π hπ (isotypicKernel σ hσ) :=
  (rfl)

/-- The defining integral formula for `e_σ`. -/
theorem banachIsotypicProjector_apply (σ : ContRepresentation k G W) (hσ : Continuous σ) (v : V) :
    banachIsotypicProjector π hπ σ hσ v = ∫ g, isotypicKernel σ hσ g • π g v ∂haarProb G :=
  strongIntegratedOperator_apply π hπ _ v

/-- On a representation continuous in the operator norm, for instance a finite-dimensional
continuous one, `e_σ` is the isotypic projector `isotypicProjector`. -/
theorem banachIsotypicProjector_eq_isotypicProjector (hπ' : Continuous π)
    (σ : ContRepresentation k G W) (hσ : Continuous σ) :
    banachIsotypicProjector π hπ σ hσ = isotypicProjector π hπ' σ hσ := by
  ext v
  simp [strongIntegratedOperator_eq_integratedOperator π hπ hπ']

/-- On the span of the orbit of a `G`-finite vector, `e_σ` is the finite-dimensional isotypic
projector of the restricted representation. -/
private theorem banachIsotypicProjector_apply_coe (σ : ContRepresentation k G W)
    (hσ : Continuous σ) {S : Submodule k V} [FiniteDimensional k S]
    (hS : ∀ g, ∀ v ∈ S, π g v ∈ S) (w : S) :
    banachIsotypicProjector π hπ σ hσ (w : V) =
      (isotypicProjector (π.subrepresentation S hS)
        (continuous_clm_apply.2 fun u ↦ continuous_subrepresentation_apply hπ u) σ hσ w : V) := by
  let ρ := π.subrepresentation S hS
  have hρ : Continuous ρ := continuous_clm_apply.2 fun u ↦ continuous_subrepresentation_apply hπ u
  let ι : ContIntertwiningMap ρ π :=
    { toContinuousLinearMap := S.subtypeL
      isIntertwining' := fun g ↦ by
        ext x
        exact coe_subrepresentation_apply g x }
  have h := congrArg (fun T : S →L[k] V ↦ T w)
    (comp_strongIntegratedOperator ρ (fun u ↦ continuous_subrepresentation_apply hπ u) π hπ ι
      (isotypicKernel σ hσ))
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [strongIntegratedOperator_eq_integratedOperator ρ _ hρ] at h
  calc banachIsotypicProjector π hπ σ hσ (w : V)
      = (banachIsotypicProjector π hπ σ hσ).toContinuousLinearMap (ι.toContinuousLinearMap w) :=
        (ContIntertwiningMap.toContinuousLinearMap_apply _ _).symm
    _ = ι.toContinuousLinearMap (integratedOperator ρ hρ (isotypicKernel σ hσ) w) := h.symm
    _ = _ := by
        rw [← toContinuousLinearMap_isotypicProjector ρ hρ σ hσ,
          ContIntertwiningMap.toContinuousLinearMap_apply]
        rfl

variable [IsAlgClosed k]

omit [CompleteSpace V] [FiniteDimensional k W'] [IsAlgClosed k] in
/-- The projector of a finite-dimensional continuous representation vanishes on the isotypic
component of an inequivalent irreducible. -/
private theorem isotypicProjector_apply_eq_zero [FiniteDimensional k V] (hπ' : Continuous π)
    (σ : ContRepresentation k G W) (hσ : Continuous σ)
    (hσirr : Representation.IsIrreducible σ.toRepresentation)
    (τ : ContRepresentation k G W') (hτirr : Representation.IsIrreducible τ.toRepresentation)
    (hne : IsEmpty (τ.toRepresentation.asModule ≃ₗ[k[G]] σ.toRepresentation.asModule))
    (x : π.toRepresentation.asModule)
    (hx : x ∈ isotypicComponent k[G] π.toRepresentation.asModule τ.toRepresentation.asModule) :
    isotypicProjector π hπ' σ hσ (π.toRepresentation.asModuleEquiv x) = 0 := by
  let _ : IsSimpleModule k[G] τ.toRepresentation.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp hτirr
  rw [isotypicComponent, sSup_eq_iSup'] at hx
  refine Submodule.iSup_induction
    (motive := fun x ↦ isotypicProjector π hπ' σ hσ (π.toRepresentation.asModuleEquiv x) = 0)
    (fun m : {m : Submodule k[G] π.toRepresentation.asModule |
      Nonempty (m ≃ₗ[k[G]] τ.toRepresentation.asModule)} ↦ m.val) hx ?_ ?_ ?_
  · intro m x hx
    let t : Subrepresentation π.toRepresentation := Subrepresentation.ofSubmodule' m.val
    have ht : IsAtom t := Subrepresentation.isSimpleModule_asSubmodule_iff.mp
      (IsSimpleModule.congr m.property.some)
    have hne' : IsEmpty (t.asSubmodule ≃ₗ[k[G]] σ.toRepresentation.asModule) :=
      ⟨fun e ↦ hne.false (m.property.some.symm.trans e)⟩
    rw [Representation.asModuleEquiv_apply]
    exact isotypicProjector_apply_subtype_of_not_equiv π hπ' σ hσ hσirr ht hne'
      (⟨x, hx⟩ : t.toSubmodule)
  · exact map_zero (isotypicProjector π hπ' σ hσ)
  · intro x y hx hy
    rw [map_add, map_add, hx, hy, add_zero]

omit [MeasurableSpace G] [BorelSpace G] [NormedSpace ℝ V] [SMulCommClass ℝ k V] [IsAlgClosed k] in
include hπ in
/-- Two continuous operators that agree on the `G`-finite vectors are equal. -/
private theorem ext_of_isGFinite {T T' : V →L[k] V}
    (h : ∀ v, π.toRepresentation.IsGFinite v → T v = T' v) : T = T' :=
  ContinuousLinearMap.coeFn_injective <| T.continuous.ext_on (dense_gFiniteSubmodule π hπ)
    T'.continuous fun v hv ↦ h v ((Representation.mem_gFiniteSubmodule _).1 hv)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] [NormedSpace ℝ V] [SMulCommClass ℝ k V] [CompleteSpace V] [IsAlgClosed k] in
/-- A `G`-finite vector lies in a finite-dimensional invariant subspace, the span of its orbit. -/
private theorem exists_orbitSpan {v : V} (hv : π.toRepresentation.IsGFinite v) :
    ∃ (S : Submodule k V) (_ : FiniteDimensional k S) (_ : ∀ g, ∀ u ∈ S, π g u ∈ S),
      v ∈ S :=
  ⟨Submodule.span k (Set.range fun g : G ↦ π g v), (π.toRepresentation.isGFinite_iff v).1 hv,
    fun g _ hu ↦ π.toRepresentation.apply_mem_span_range_apply v g hu,
    Submodule.subset_span ⟨1, by simp⟩⟩

/-- **`e_σ` is idempotent** for an irreducible `σ`. -/
theorem banachIsotypicProjector_comp_self (σ : ContRepresentation k G W) (hσ : Continuous σ)
    (hirr : Representation.IsIrreducible σ.toRepresentation) :
    (banachIsotypicProjector π hπ σ hσ).comp (banachIsotypicProjector π hπ σ hσ) =
      banachIsotypicProjector π hπ σ hσ := by
  refine ContIntertwiningMap.toContinuousLinearMap_injective (ext_of_isGFinite π hπ fun v hv ↦ ?_)
  obtain ⟨S, _, hS, hvS⟩ := exists_orbitSpan π hv
  have hρ : Continuous (π.subrepresentation S hS) :=
    continuous_clm_apply.2 fun u ↦ continuous_subrepresentation_apply hπ u
  have hP := congrArg (fun T ↦ T ⟨v, hvS⟩)
    (isotypicProjector_idempotent (π.subrepresentation S hS) hρ σ hσ hirr)
  simp only [ContIntertwiningMap.toContinuousLinearMap_comp, ContinuousLinearMap.comp_apply,
    ContIntertwiningMap.toContinuousLinearMap_apply]
  rw [show v = ((⟨v, hvS⟩ : S) : V) from rfl, banachIsotypicProjector_apply_coe π hπ σ hσ hS,
    banachIsotypicProjector_apply_coe π hπ σ hσ hS]
  exact congrArg Subtype.val hP

/-- **Orthogonality.** For inequivalent irreducibles `σ` and `τ`, `e_σ ∘ e_τ = 0`. -/
theorem banachIsotypicProjector_comp_of_not_equiv (σ : ContRepresentation k G W)
    (hσ : Continuous σ) (hσirr : Representation.IsIrreducible σ.toRepresentation)
    (τ : ContRepresentation k G W') (hτ : Continuous τ)
    (hτirr : Representation.IsIrreducible τ.toRepresentation)
    (hne : IsEmpty (τ.toRepresentation.asModule ≃ₗ[k[G]] σ.toRepresentation.asModule)) :
    (banachIsotypicProjector π hπ σ hσ).comp (banachIsotypicProjector π hπ τ hτ) = 0 := by
  refine ContIntertwiningMap.toContinuousLinearMap_injective (ext_of_isGFinite π hπ fun v hv ↦ ?_)
  obtain ⟨S, _, hS, hvS⟩ := exists_orbitSpan π hv
  let ρ := π.subrepresentation S hS
  have hρ : Continuous ρ := continuous_clm_apply.2 fun u ↦ continuous_subrepresentation_apply hπ u
  let w := isotypicProjector ρ hρ τ hτ ⟨v, hvS⟩
  have hw : ρ.toRepresentation.asModuleEquiv.symm w ∈
      isotypicComponent k[G] ρ.toRepresentation.asModule τ.toRepresentation.asModule := by
    rw [← range_isotypicProjector ρ hρ τ hτ hτirr]
    exact (Subrepresentation.mem_asSubmodule_iff
      (σ := (isotypicProjector ρ hρ τ hτ).toIntertwiningMap.range)).mpr
        ((Representation.IntertwiningMap.mem_range _ _ _ _).mpr ⟨_, rfl⟩)
  have h0 := isotypicProjector_apply_eq_zero ρ hρ σ hσ hσirr τ hτirr hne _ hw
  rw [LinearEquiv.apply_symm_apply] at h0
  simp only [ContIntertwiningMap.toContinuousLinearMap_comp, ContinuousLinearMap.comp_apply,
    ContIntertwiningMap.toContinuousLinearMap_apply, ContIntertwiningMap.toContinuousLinearMap_zero,
    zero_apply]
  rw [show v = ((⟨v, hvS⟩ : S) : V) from rfl, banachIsotypicProjector_apply_coe π hπ τ hτ hS,
    banachIsotypicProjector_apply_coe π hπ σ hσ hS]
  exact congrArg Subtype.val h0

end ContRepresentation
