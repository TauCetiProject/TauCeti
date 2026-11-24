/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Cutoff
public import TauCeti.CategoryTheory.ComposableArrows.FiberSum
public import TauCeti.Topology.CategoryTheory.ComposableArrows

/-!
# Continuous cutoff contraction on the nerve

On a Hausdorff locally compact étale groupoid, weighted insertion and averaging preserve
continuous cochains if the weight is continuous and its support is proper over the tail.
If the weight also has fiber sums equal to one, every continuous positive-degree cocycle
is the coboundary of a continuous cochain. All arrows are counted, including ineffective
isotropy. The support condition on the tail follows by base change from the arrow space.

## References

* M. Crainic, *Differentiable and algebroid cohomology, van Est isomorphisms, and characteristic
  classes*, Comment. Math. Helv. **78** (2003), Section 2.
-/

public noncomputable section

open CategoryTheory Set Topology

universe w

namespace TauCeti.nerveCochainComplex

variable {C k M : Type w} [Category.{w} C] [IsGroupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)] [IsTopologicalGroupoid C]
  [T2Space (Quiver.Total C)] [LocallyCompactSpace (Quiver.Total C)]
  [CommRing k] [TopologicalSpace k] [AddCommGroup M] [Module k M] [TopologicalSpace M]
  [ContinuousAdd M] [ContinuousSMul k M]

/-- Weighted insertion of an initial arrow preserves continuous nerve cochains on an étale
groupoid with Hausdorff locally compact arrow space, if the weight is continuous and
its support pulled back along target is proper over source. -/
theorem continuous_cutoffPrepend {c : C → k} (hcs : Continuous c)
    (hc : ∀ ⦃K : Set C⦄, IsCompact K →
      IsCompact (Quiver.Total.left ⁻¹' K ∩ Quiver.Total.right ⁻¹' tsupport c))
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    {n : ℕ} {φ : ComposableArrows C (n + 1) → M} (hφ : Continuous φ) :
    Continuous (cutoffPrepend (M := ModuleCat.of k M) c n φ) := by
  let : T2Space C := (IsTopologicalGroupoid.isEmbedding_unit C).t2Space
  have ht := (IsTopologicalGroupoid.isLocalHomeomorph_source_iff_target C).mp hs
  have hcomp := IsTopologicalGroupoid.continuous_comp (C := C)
  simp only [Quiver.Total.comp_def] at hcomp
  let := ComposableArrows.locallyCompactSpace hs.continuous
    IsTopologicalGroupoid.continuous_unit hcomp ht.continuous n
  have hsource := ComposableArrows.continuous_obj (n := n + 1) hs.continuous 0
  have hw : Continuous fun τ : ComposableArrows C (n + 1) ↦ c τ.left • φ τ :=
    (hcs.comp hsource).smul hφ
  have hp := ComposableArrows.isLocalHomeomorph_δ₀ hs.continuous
    IsTopologicalGroupoid.continuous_unit hcomp ht n
  have hcinv ⦃K : Set C⦄ (hK : IsCompact K) :
      IsCompact (Quiver.Total.right ⁻¹' K ∩ Quiver.Total.left ⁻¹' tsupport c) := by
    convert (IsTopologicalGroupoid.inverseHomeomorph C).isClosedEmbedding.isCompact_preimage
      (hc hK) using 1
    ext a
    simp
  have hsum := hp.continuous_finsum_mem_preimage_singleton hw
    (fun K hK ↦ (ComposableArrows.isCompact_preimage_δ₀_inter hs.continuous
      IsTopologicalGroupoid.continuous_unit hcomp ht.continuous hcinv hK).of_isClosed_subset
        ((hK.isClosed.preimage hp.continuous).inter (isClosed_tsupport _))
        (inter_subset_inter_right _ ((tsupport_smul_subset_left _ _).trans
          (tsupport_comp_subset_preimage c hsource))))
  convert hsum using 1
  funext σ
  rw [cutoffPrepend_apply, ComposableArrows.finsum_mem_preimage_δ₀_singleton]
  exact finsum_congr fun _ ↦ rfl

/-- The degree-zero cutoff average is continuous on continuous cochains, for a continuous
weight with support pulled back along target proper over source on a Hausdorff locally
compact étale groupoid. -/
theorem continuous_cutoffAverage {c : C → k} (hcs : Continuous c)
    (hc : ∀ ⦃K : Set C⦄, IsCompact K →
      IsCompact (Quiver.Total.left ⁻¹' K ∩ Quiver.Total.right ⁻¹' tsupport c))
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    {φ : ComposableArrows C 0 → M} (hφ : Continuous φ) :
    Continuous (cutoffAverage (M := ModuleCat.of k M) c φ) := by
  let e := ComposableArrows.zeroHomeomorph hs.continuous IsTopologicalGroupoid.continuous_unit
  have he : (e.symm : C → ComposableArrows C 0) = ComposableArrows.mk₀ :=
    funext (ComposableArrows.zeroHomeomorph_symm_apply hs.continuous
      IsTopologicalGroupoid.continuous_unit)
  have hmk : Continuous (ComposableArrows.mk₀ : C → ComposableArrows C 0) :=
    he ▸ e.continuous_symm
  have hleft : Continuous (fun τ : ComposableArrows C 1 ↦ τ.left) :=
    ComposableArrows.continuous_obj hs.continuous 0
  convert continuous_cutoffPrepend hcs hc hs (hφ.comp (hmk.comp hleft)) using 1
  funext σ
  rw [cutoffAverage_apply, cutoffPrepend_apply]
  exact finsum_congr fun _ ↦ rfl

/-- On a Hausdorff locally compact étale groupoid, a continuous positive-degree cocycle is
the coboundary of a continuous cochain if there is a continuous weight with incoming fiber
sums equal to one whose support pulled back along target is proper over source. -/
theorem exists_continuous_valuesEquiv_d_eq_of_d_eq_zero {c : C → k} (hcs : Continuous c)
    (hc : ∀ ⦃K : Set C⦄, IsCompact K →
      IsCompact (Quiver.Total.left ⁻¹' K ∩ Quiver.Total.right ⁻¹' tsupport c))
    (hn : ∀ x : C, ∑ᶠ b : Quiver.Costar x, c b.1 = 1)
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    {n : ℕ} {φ : (nerveCochainComplex C k (ModuleCat.of k M)).X (n + 1)}
    (hφ : Continuous (valuesEquiv (n + 1) φ))
    (hz : (nerveCochainComplex C k (ModuleCat.of k M)).d (n + 1) (n + 2) φ = 0) :
    ∃ ψ : (nerveCochainComplex C k (ModuleCat.of k M)).X n,
      Continuous (valuesEquiv n ψ) ∧
        (nerveCochainComplex C k (ModuleCat.of k M)).d n (n + 1) ψ = φ := by
  refine ⟨cutoffPrependHom (ModuleCat.of k M) hn n φ, ?_,
    d_cutoffPrependHom_of_d_eq_zero hn hz⟩
  rw [valuesEquiv_cutoffPrependHom]
  exact continuous_cutoffPrepend hcs hc hs hφ

end TauCeti.nerveCochainComplex
