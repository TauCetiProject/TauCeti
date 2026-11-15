/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Cutoff
public import TauCeti.CategoryTheory.ComposableArrows.FiberSum
public import TauCeti.Topology.CategoryTheory.ComposableArrows
public import TauCeti.Topology.CategoryTheory.Groupoid.Basic
public import TauCeti.Topology.CategoryTheory.Cutoff
public import TauCeti.Topology.IsLocalHomeomorph.FiberSum

/-!
# Continuous cutoff contraction on the nerve

The algebraic insertion `TauCeti.nerveCochainComplex.cutoffPrepend`, which defines
`TauCeti.nerveCochainComplex.cutoffHomotopy`, preserves continuous cochains on a
Hausdorff locally compact étale groupoid. Consequently every continuous positive-degree
cocycle has a continuous primitive, given by the same explicit weighted insertion operator.
All arrows are counted, including ineffective isotropy.

The analytic input is properness of the cutoff support, not finiteness of the groupoid.
For the map deleting the first vertex of a string, that support is proper by base change
from the arrow space. Summation along this local homeomorphism therefore preserves continuity.
This is a statement about continuous functions on the topological nerve, not singular
cochains on its realization, nor differential forms on its levels.

## References

* M. Crainic, *Differentiable and algebroid cohomology, van Est isomorphisms, and characteristic
  classes*, Comment. Math. Helv. **78** (2003), Section 2.
-/

public noncomputable section

open CategoryTheory Set Topology

namespace TauCeti.nerveCochainComplex

variable {C : Type} [Category C] [IsGroupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)] [IsTopologicalGroupoid C]

variable [T2Space C]

/-- The cutoff support on strings is proper over the tail: compact sets of tails meet
only a compact set of strings whose first vertex lies in the cutoff support. -/
theorem isCompact_preimage_δ₀_inter {c : C → ℝ} (hc : TauCeti.Quiver.IsCutoff c)
    {n : ℕ} {K : Set (ComposableArrows C n)} (hK : IsCompact K) :
    IsCompact ((fun τ : ComposableArrows C (n + 1) ↦ τ.δ₀) ⁻¹' K ∩
      (fun τ ↦ τ.left) ⁻¹' tsupport c) := by
  let e := ComposableArrows.precompHomeomorph IsTopologicalGroupoid.continuous_source
    IsTopologicalGroupoid.continuous_unit (by
      simpa only [Quiver.Total.comp_def] using
        (IsTopologicalGroupoid.continuous_comp (C := C))) n
  have hA : IsCompact (Quiver.Total.right ⁻¹'
      ((fun F : ComposableArrows C n ↦ F.obj 0) '' K) ∩
        Quiver.Total.left ⁻¹' tsupport c) := by
    convert (IsTopologicalGroupoid.inverseHomeomorph C).isClosedEmbedding.isCompact_preimage
      (hc.isCompact_preimage_inter
        (hK.image (ComposableArrows.continuous_obj IsTopologicalGroupoid.continuous_source 0)))
      using 1
    ext a
    simp
  have hclosed : IsClosed {p : Quiver.Total C × ComposableArrows C n |
      p.1.right = p.2.left} := isClosed_eq
    (IsTopologicalGroupoid.continuous_target.comp continuous_fst)
    ((ComposableArrows.continuous_obj
      IsTopologicalGroupoid.continuous_source 0).comp continuous_snd)
  have hprod := (hA.prod hK).inter_right hclosed
  have hcompact := hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage hprod
  convert e.isClosedEmbedding.isCompact_preimage hcompact using 1
  ext τ
  simp only [e, mem_preimage, mem_inter_iff, mem_prod,
    ComposableArrows.precompHomeomorph_apply, ComposableArrows.totalArrow_left,
    ComposableArrows.totalArrow_right, mem_ofPred_eq]
  constructor
  · intro h
    exact ⟨⟨⟨⟨τ.δ₀, h.1, rfl⟩, h.2⟩, h.1⟩, rfl⟩
  · intro h
    exact ⟨h.1.2, h.1.1.2⟩

variable [T2Space (Quiver.Total C)] [LocallyCompactSpace (Quiver.Total C)]
  {M : Type} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
  [ContinuousAdd M] [ContinuousSMul ℝ M]

omit [T2Space C] in
/-- Weighted insertion of an initial arrow preserves continuous nerve cochains. -/
theorem continuous_cutoffPrepend {c : C → ℝ} (hc : TauCeti.Quiver.IsCutoff c)
    (hcs : Continuous c)
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    {n : ℕ} {φ : ComposableArrows C (n + 1) → M} (hφ : Continuous φ) :
    Continuous (cutoffPrepend (M := ModuleCat.of ℝ M) c n φ) := by
  let : T2Space C := IsTopologicalGroupoid.isEmbedding_unit C |>.t2Space
  have ht := (IsTopologicalGroupoid.isLocalHomeomorph_source_iff_target C).mp hs
  have hcomp := IsTopologicalGroupoid.continuous_comp (C := C)
  simp only [Quiver.Total.comp_def] at hcomp
  have hq : IsOpenQuotientMap (Quiver.Total.left : Quiver.Total C → C) :=
    ⟨fun x ↦ ⟨⟨x, x, 𝟙 x⟩, rfl⟩, hs.continuous, hs.isOpenMap⟩
  let := hq.locallyCompactSpace
  have hsep (k : ℕ) : T2Space (ComposableArrows C k) := by
    induction k with
    | zero => exact (ComposableArrows.zeroHomeomorph
        IsTopologicalGroupoid.continuous_source
        IsTopologicalGroupoid.continuous_unit).isEmbedding.t2Space
    | succ k ih =>
      let := ih
      exact (ComposableArrows.precompHomeomorph IsTopologicalGroupoid.continuous_source
        IsTopologicalGroupoid.continuous_unit hcomp k).isEmbedding.t2Space
  let := hsep n
  let := hsep (n + 1)
  let := ComposableArrows.locallyCompactSpace IsTopologicalGroupoid.continuous_source
    IsTopologicalGroupoid.continuous_unit hcomp ht.continuous n
  have hw : Continuous fun τ : ComposableArrows C (n + 1) ↦ c τ.left • φ τ :=
    (hcs.comp (ComposableArrows.continuous_obj IsTopologicalGroupoid.continuous_source 0)).smul hφ
  have hp := ComposableArrows.isLocalHomeomorph_δ₀ IsTopologicalGroupoid.continuous_source
    IsTopologicalGroupoid.continuous_unit hcomp ht n
  have hsum := hp.continuous_finsum_mem_preimage_singleton hw
    (fun K hK ↦ (isCompact_preimage_δ₀_inter hc hK).of_isClosed_subset
      ((hK.isClosed.preimage (ComposableArrows.continuous_whiskerLeft
        (Fin.succFunctor (n + 1)))).inter (isClosed_tsupport _))
      (inter_subset_inter_right _ ((tsupport_smul_subset_left _ _).trans
        (tsupport_comp_subset_preimage c
          (ComposableArrows.continuous_obj IsTopologicalGroupoid.continuous_source 0)))))
  convert hsum using 1
  funext σ
  rw [cutoffPrepend_apply, ComposableArrows.finsum_mem_preimage_δ₀]
  apply finsum_congr
  intro b
  rfl

omit [T2Space C] in
/-- A continuous positive-degree cocycle on the nerve has a continuous primitive. The
primitive is the algebraic cutoff insertion, so its coboundary is the given cocycle with
the native alternating-face signs. -/
theorem exists_continuous_primitive {c : C → ℝ} (hc : TauCeti.Quiver.IsCutoff c)
    (hcs : Continuous c)
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    {n : ℕ} {φ : (nerveCochainComplex C ℝ (ModuleCat.of ℝ M)).X (n + 1)}
    (hφ : Continuous (valuesEquiv (n + 1) φ))
    (hz : (nerveCochainComplex C ℝ (ModuleCat.of ℝ M)).d (n + 1) (n + 2) φ = 0) :
    ∃ ψ : (nerveCochainComplex C ℝ (ModuleCat.of ℝ M)).X n,
      Continuous (valuesEquiv n ψ) ∧
        (nerveCochainComplex C ℝ (ModuleCat.of ℝ M)).d n (n + 1) ψ = φ := by
  have hn (x : C) : ∑ᶠ b : Quiver.Costar x, c b.1 = 1 :=
    (Quiver.Total.finsum_costar_eq_finsum_mem_preimage_left_singleton c x).trans
      (hc.finsum_eq_one x)
  refine ⟨cutoffPrependHom (ModuleCat.of ℝ M) hn n φ, ?_,
    d_cutoffPrependHom_of_d_eq_zero hn hz⟩
  rw [valuesEquiv_cutoffPrependHom]
  exact continuous_cutoffPrepend hc hcs hs hφ

end TauCeti.nerveCochainComplex
