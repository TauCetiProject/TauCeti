/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.RegularValue.Level.Graph
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Topology.ConnectedComponents

/-!
# Connected components of transverse levels in cylindrical coordinates

If the height derivative is bounded away from zero in a cylindrical slab and the
central values are close to the target level, each vertical line meets the level
once. For a compact connected cross-section, the smooth graph is an embedded
connected component of the ambient level.

## References

* B. Kleiner and J. Lott, *Notes on Perelman's papers*, Theorem 46.1.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Function Set
open scoped ContDiff Manifold Topology

namespace PartialDiffeomorph

variable {E H P E' H' M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace P] [ChartedSpace H P] [CompactSpace P] [ConnectedSpace P]
  [TopologicalSpace M] [ChartedSpace H' M] [T2Space M]
  {n : ℕ∞ω} [IsManifold I n P] [IsManifold J n M]

/-- A level crossing every fibre of a cylindrical coordinate slab transversely and with
central oscillation less than the derivative bound times the half-width gives an embedded
copy of the cross-section. Its image is the whole intersection of the level and the open slab
and is a connected component of the level in the ambient manifold.

For a spherical cross-section, this is a sphere lying in the actual neck, with the ambient
level component determined by the cylindrical coordinates. No metric comparison is needed
for this step. -/
theorem exists_isSmoothEmbedding_levelComponent
    (Φ : PartialDiffeomorph (I.prod 𝓘(ℝ)) J (P × ℝ) M n) {f : M → ℝ}
    (hf : ContMDiffOn J 𝓘(ℝ) n f Φ.target) (hn : 1 ≤ n)
    {W m c : ℝ} (hm : 0 < m)
    (hslab : (univ ×ˢ Icc (-W) W) ⊆ Φ.source)
    (hderiv : ∀ q t, t ∈ Ioo (-W) W → m ≤ |deriv (fun s ↦ f (Φ (q, s))) t|)
    (hcenter : ∀ q, |f (Φ (q, 0)) - c| < m * W) :
    ∃ h : P → ℝ, ContMDiff I 𝓘(ℝ) n h ∧ (∀ q, h q ∈ Ioo (-W) W) ∧
      Manifold.IsSmoothEmbedding I J n (fun q ↦ Φ (q, h q)) ∧
      range (fun q ↦ Φ (q, h q)) = Φ '' (univ ×ˢ Ioo (-W) W) ∩ f ⁻¹' {c} ∧
      ∀ q, range (fun p ↦ Φ (p, h p)) = connectedComponentIn (f ⁻¹' {c}) (Φ (q, h q)) := by
  let slab : Set (P × ℝ) := univ ×ˢ Ioo (-W) W
  have hsub : slab ⊆ Φ.source := fun _ hz ↦ hslab ⟨hz.1, Ioo_subset_Icc_self hz.2⟩
  have hφ : ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ) n (f ∘ Φ) Φ.source :=
    hf.comp Φ.contMDiffOn_toFun fun _ hz ↦ Φ.map_source hz
  obtain ⟨h, hh, hheight, hroot⟩ :=
    TauCeti.exists_contMDiff_levelGraph Φ.open_source hφ hn hm hslab hderiv hcenter
  let e : P → M := fun q ↦ Φ (q, h q)
  have hmem (p : P) : (p, h p) ∈ Φ.source := hsub ⟨mem_univ _, hheight p⟩
  have he : ContMDiff I J n e :=
    Φ.contMDiffOn_toFun.comp_contMDiff (contMDiff_id.prodMk hh) hmem
  have hleft : LeftInverse (fun x ↦ (Φ.symm x).1) e :=
    fun p ↦ congrArg Prod.fst (Φ.left_inv (hmem p))
  have hdiff (p : P) : MDifferentiableAt J I (fun x ↦ (Φ.symm x).1) (e p) :=
    (contMDiffAt_fst.comp _ (Φ.contMDiffOn_invFun.contMDiffAt
      (Φ.open_target.mem_nhds (Φ.map_source (hmem p))))).mdifferentiableAt
        (zero_lt_one.trans_le hn).ne'
  have hemb : Manifold.IsSmoothEmbedding I J n e :=
    ⟨he.isImmersion_of_leftInverse hn hdiff hleft,
      (he.continuous.isClosedEmbedding hleft.injective).isEmbedding⟩
  have hrange : range e = Φ '' slab ∩ f ⁻¹' {c} := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨⟨(q, h q), ⟨mem_univ _, hheight q⟩, rfl⟩,
        (hroot q (h q) (hheight q)).2 rfl⟩
    · rintro ⟨⟨⟨q, t⟩, hqt, rfl⟩, htc⟩
      have ht := (hroot q t hqt.2).1 htc
      subst t
      exact mem_range_self q
  have hopen : IsOpen (Φ '' slab) :=
    Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      (isOpen_univ.prod isOpen_Ioo) hsub
  have hclosed : closure (range e) ∩ f ⁻¹' {c} ⊆ range e := by
    rw [(isCompact_range he.continuous).isClosed.closure_eq]
    exact inter_subset_left
  exact ⟨h, hh, hheight, hemb, hrange, fun q ↦
    ((isPreconnected_range he.continuous).connectedComponentIn_eq_of_closure_inter_subset
      (mem_range_self q) hopen hrange.symm hclosed).symm⟩

end PartialDiffeomorph
