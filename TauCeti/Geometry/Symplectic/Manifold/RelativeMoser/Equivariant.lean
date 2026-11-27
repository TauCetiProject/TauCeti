/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.RelativeMoser
public import TauCeti.Geometry.Manifold.DifferentialForm.Average
import TauCeti.Geometry.Manifold.GroupAction.InvariantCutoff
import TauCeti.RepresentationTheory.Compact.Haar
import TauCeti.Topology.Algebra.ConstMulAction

/-!
# The equivariant relative Moser theorem

Let a compact group `G`, itself a smooth manifold, act smoothly on a boundaryless Hausdorff manifold
`M`, modelled on a finite-dimensional space, preserving two closed two-forms `σ₀` and `σ₁`. Let `K`
be an invariant compact set, and suppose that near `K` the difference `σ₁ - σ₀ = dβ` is exact, for a
smooth one-form `β` vanishing along `K` which need not be invariant, and that the path
`σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, is nondegenerate along `K`. The **equivariant relative Moser
theorem** (`TauCeti.SmoothTwoForm.exists_equivariant_diffeomorph_fix_eventually_mpullback_eq`)
gives a diffeomorphism `Φ` of `M` which

* fixes every point of `K` and moves only the points of a compact set,
* pulls `σ₁` back to `σ₀` on a neighbourhood of `K`,
* has identity differential at each point of `K` along whose orbit `β` has zero first jet,
* and commutes with the action: `Φ (a • x) = a • Φ x`.

The proof makes every ingredient of Moser's argument invariant. The primitive is replaced by its
average `β' = ∫ a^* β da` over the normalized Haar measure
(`TauCeti.SmoothForm.measureAverage`), which is invariant, still vanishes along the invariant set
`K`, keeps a zero first jet at a point when `β` has one along its orbit, and still satisfies
`dβ' = σ₁ - σ₀` on the largest invariant open subset of the region where `dβ = σ₁ - σ₀`, since
averaging commutes with `d` and fixes the invariant form `σ₁ - σ₀`. The Moser field is cut off
by an invariant function
(`IsCompact.exists_contMDiff_one_nhds_tsupport_subset_of_smul_mem`). The diffeomorphism given by
Moser's theorem with a given primitive and cut-off
(`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_eventually_mpullback_eq_of_cutoff`) commutes with
every diffeomorphism preserving these data, in particular with every element of `G`.

Equivariant relative Moser theorems are the input of the equivariant normal forms of Hamiltonian
group actions: near a fixed point (equivariant Darboux), along a submanifold of fixed points, and
along an orbit (the Marle–Guillemin–Sternberg local model).

## References

* V. Guillemin and S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984, Section 22 (equivariant Moser and Darboux theorems).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorem 7.4 and Homework 21.
-/

public section

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold Topology ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {EG HG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [ChartedSpace HG G] [IsManifold IG ∞ G] [MulAction G M]
  [ContMDiffSMul IG I ∞ G M]

variable (G IG) in
include IG in
/-- **The equivariant relative Moser theorem.** Let a compact Lie group `G` act smoothly on a
boundaryless Hausdorff manifold, preserving closed two-forms `σ₀` and `σ₁`. Let `K` be an invariant
compact set and `β` a smooth one-form, vanishing along `K`, with `dβ = σ₁ - σ₀` on an open
neighbourhood `U` of `K`, and suppose the path `σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, is nondegenerate
along `K`. Then there is a diffeomorphism `Φ` which commutes with the action, fixes every point of
`K`, moves only the points of a compact set and pulls `σ₁` back to `σ₀` on a neighbourhood of `K`.
At each point of `K` along whose orbit `β` has zero first jet, the differential of `Φ` is the
identity. -/
theorem exists_equivariant_diffeomorph_fix_eventually_mpullback_eq {σ₀ σ₁ : SmoothTwoForm I M}
    (h₀ : σ₀.IsClosed) (h₁ : σ₁.IsClosed)
    (hG₀ : ∀ a : G, mpullback I I (a • ·) σ₀.val = σ₀.val)
    (hG₁ : ∀ a : G, mpullback I I (a • ·) σ₁.val = σ₁.val)
    {β : SmoothForm I M ℝ 1} {U : Set M} (hU : IsOpen U)
    (hβ : ∀ x ∈ U, mextDeriv β.val x = (σ₁ - σ₀).val x)
    {K : Set M} (hK : IsCompact K) (hKG : ∀ (a : G), ∀ x ∈ K, a • x ∈ K) (hKU : K ⊆ U)
    (hβK : ∀ x ∈ K, β.val x = 0)
    (hnd : ∀ x ∈ K, ∀ s ∈ Icc (0 : ℝ) 1, ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt x).Nondegenerate) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, (∀ x ∈ K, Φ x = x) ∧ (∃ C, IsCompact C ∧ ∀ x ∉ C, Φ x = x) ∧
      (∀ᶠ x in 𝓝ˢ K, (SmoothForm.mpullback Φ Φ.contMDiff σ₁).val x = σ₀.val x) ∧
      (∀ x ∈ K, (∀ a : G, HasFDerivAt (RoughForm.inChartAt β.val (a • x))
        (0 : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ) (extChartAt I (a • x) (a • x))) →
        mfderiv I I Φ x = ContinuousLinearMap.id ℝ (TangentSpace I x)) ∧
      ∀ (a : G) (x : M), Φ (a • x) = a • Φ x := by
  borelize G
  have := ContMDiffSMul.continuousSMul (I := IG) (I' := I) (G := G) (M := M) ∞
  set μ := TauCeti.haarProb G
  set β' := SmoothForm.measureAverage IG μ β
  -- On the largest invariant open subset of `U`, the average primitive still has
  -- `dβ' = σ₁ - σ₀`: averaging commutes with `d` and fixes the invariant form `σ₁ - σ₀`.
  set U' := {x : M | ∀ a : G, a • x ∈ U}
  have hdβ' (x : M) (hx : x ∈ U') : mextDeriv β'.val x = (σ₁ - σ₀).val x := by
    have h := congrArg (fun α : SmoothForm I M ℝ 2 ↦ α.val x)
      (SmoothForm.mextDerivₗ_measureAverage IG μ β)
    simp only [mextDerivₗ_apply] at h
    rw [h]
    ext v
    have hpull (a : G) : (mextDeriv β.val) (a • x) (fun i ↦ mfderiv I I (a • ·) x (v i)) =
        (σ₁ - σ₀).val x v := by
      rw [hβ _ (hx a), ← mpullback_apply, AddSubgroupClass.coe_sub, mpullback_sub, hG₀, hG₁]
    simp [SmoothForm.measureAverage_apply, mextDerivₗ_apply, hpull]
  -- An invariant cut-off supported where `dβ' = σ₁ - σ₀` and the path is nondegenerate.
  obtain ⟨N, hN, hKN, hndN⟩ := exists_isOpen_forall_nondegenerate hK hnd
  obtain ⟨ρ, hρ, hρ1, hρc, hρW, -, hρG⟩ :=
    hK.exists_contMDiff_one_nhds_tsupport_subset_of_smul_mem I IG
      ((TauCeti.isOpen_setOf_forall_smul_mem (G := G) hU).inter hN)
      (fun x hx ↦ ⟨fun a ↦ hKU (hKG a x hx), hKN hx⟩) hKG
  obtain ⟨Φ, hΦK, hΦρ, hΦ, hΦ1, hΦG⟩ := exists_diffeomorph_fix_eventually_mpullback_eq_of_cutoff
    h₀ h₁ hρ hρc (fun x hx ↦ hdβ' x (hρW hx).1) (fun x hx ↦ hndN x (hρW hx).2) hK
    (fun x hx ↦ SmoothForm.measureAverage_eq_zero_of_forall_smul IG μ β fun a ↦
      hβK _ (hKG a x hx)) hρ1
  refine ⟨Φ, hΦK, ⟨tsupport ρ, hρc, hΦρ⟩, hΦ, fun x hx hjet ↦ hΦ1 x hx ?_, fun a x ↦
    hΦG (Diffeomorph.smul IG I ∞ a) (hG₀ a) (hG₁ a)
      (SmoothForm.mpullback_smul_measureAverage IG μ β a) (hρG a) x⟩
  -- Averaging keeps a zero first jet along the orbit.
  exact SmoothForm.hasFDerivAt_inChartAt_measureAverage_of_forall_smul IG μ β
    (fun a ↦ hβK _ (hKG a x hx)) hjet

end TauCeti.SmoothTwoForm
