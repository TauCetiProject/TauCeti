/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Lattice.Basic
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Measure.Haar.OfBasis

/-!
# The lattice-normalized Lebesgue measure on the dual of a lattice

Let `i : N →+ V` be an integral lattice (`TauCeti.Toric.IsIntegralLattice`), for instance the
integral cocharacters of a torus in its Lie algebra `𝔱 = V`. Moment maps take values in the dual
`V* = StrongDual ℝ V`, and volumes there are measured by the Lebesgue measure for which the
*weight lattice*

`Λ* = {x ∈ V* | x (i n) ∈ ℤ for every n ∈ N}` (`TauCeti.Toric.weightLattice`)

has covolume one. This file constructs that measure,
`TauCeti.Toric.IsIntegralLattice.dualMeasure`, and proves that it is canonical.

Every integral basis `b` of `N` gives a real basis `i ∘ b` of `V`, and hence a dual basis of
`V*` (`TauCeti.Toric.IsIntegralLattice.dualBasis`), whose coordinates are `x ↦ x (i (b j))`. The
`ℤ`-span of this dual basis is the weight lattice, whatever `b` is
(`TauCeti.Toric.IsIntegralLattice.span_dualBasis`). The Haar measure normalized by the
dual basis therefore gives measure one to a fundamental domain of `Λ*`, and so does not depend on
`b` (`TauCeti.Toric.IsIntegralLattice.addHaar_dualBasis`): two fundamental domains of the same
lattice have the same measure. This is the measure `dualMeasure`; the weight lattice has covolume
one for it (`TauCeti.Toric.IsIntegralLattice.covolume_weightLattice`), and the coordinates of any
dual basis carry it to Lebesgue measure on `ℝ^κ`
(`TauCeti.Toric.IsIntegralLattice.measurePreserving_dualBasis_equivFun`).

The measure is natural. A lattice isomorphism `f : N ≃+ N'` with compatible real-linear
`g : V ≃L[ℝ] V'` has transpose `y ↦ y ∘ g` carrying one lattice-normalized measure to the other
(`TauCeti.Toric.IsIntegralLattice.map_comp_dualMeasure`), and on a product of lattices the
measure is the product measure, under `V* × V'* ≃ (V × V')*`
(`TauCeti.Toric.IsIntegralLattice.dualMeasure_prod`).

This is the normalization in which the Duistermaat–Heckman density of a Hamiltonian torus action
and the volume formula `vol(M) = (2π)^n vol(Δ)` for a symplectic toric manifold with moment polytope
`Δ` are stated. The volumes of explicit Delzant polytopes are computed in
`TauCeti/Geometry/Toric/Delzant/Volume.lean`.

## Main definitions

* `TauCeti.Toric.IsIntegralLattice.dualMeasure h`: the lattice-normalized Lebesgue measure on `V*`.

## Main results

* `TauCeti.Toric.IsIntegralLattice.addHaar_dualBasis`: the Haar measure of any dual basis is
  `dualMeasure`.
* `TauCeti.Toric.IsIntegralLattice.covolume_weightLattice`: the weight lattice has covolume one.
* `TauCeti.Toric.IsIntegralLattice.measurePreserving_dualBasis_equivFun`: dual coordinates carry
  `dualMeasure` to Lebesgue measure.
* `TauCeti.Toric.IsIntegralLattice.dualMeasure_preimage_dualBasis_equivFun`: so the measure of a
  set described in dual coordinates is the Lebesgue measure of its coordinate description.
* `TauCeti.Toric.IsIntegralLattice.map_comp_dualMeasure`: naturality under lattice isomorphisms.
* `TauCeti.Toric.IsIntegralLattice.dualMeasure_prod`: products.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 29–30.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory Module Set Submodule

namespace TauCeti.Toric.IsIntegralLattice

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V] {i : N →+ V}
  (h : IsIntegralLattice i) {κ : Type*} [Fintype κ]

/-! ### The lattice-normalized measure -/

variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]

/-- The Haar measures normalized by the dual bases of two integral bases agree: both give measure
one to the fundamental domains of the weight lattice. -/
private theorem addHaar_dualBasis_eq {κ' : Type*} [Fintype κ'] (b : Basis κ ℤ N)
    (b' : Basis κ' ℤ N) :
    (h.dualBasis b).addHaar = (h.dualBasis b').addHaar := by
  set B := h.dualBasis b
  set B' := h.dualBasis b'
  have := B.finiteDimensional_of_finite
  have hB := ZSpan.isAddFundamentalDomain B B'.addHaar
  have hB' := ZSpan.isAddFundamentalDomain B' B'.addHaar
  rw [h.span_dualBasis b, ← h.span_dualBasis b'] at hB
  have : VAddInvariantMeasure (span ℤ (range B')) (StrongDual ℝ V) B'.addHaar :=
    inferInstanceAs (VAddInvariantMeasure (span ℤ (range B')).toAddSubgroup _ _)
  rw [B.addHaar_eq_iff, Basis.coe_parallelepiped,
    ← measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped B B'.addHaar), hB.measure_eq hB',
    measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped B' B'.addHaar), B'.addHaar_self]

/-- **The lattice-normalized Lebesgue measure** on `V*`: the Haar measure for which the weight
lattice `{x | ∀ n, x (i n) ∈ ℤ}` has covolume one. It is defined through the dual basis of an
arbitrary integral basis of `N`, on which it does not depend
(`TauCeti.Toric.IsIntegralLattice.addHaar_dualBasis`). -/
def dualMeasure : Measure (StrongDual ℝ V) :=
  have := h.free
  have := h.finite
  (h.dualBasis (Free.chooseBasis ℤ N)).addHaar

/-- The Haar measure normalized by the dual basis of any integral basis is the lattice-normalized
measure. -/
@[simp]
theorem addHaar_dualBasis (b : Basis κ ℤ N) : (h.dualBasis b).addHaar = h.dualMeasure :=
  have := h.free
  have := h.finite
  h.addHaar_dualBasis_eq b _

instance isAddHaarMeasure_dualMeasure : h.dualMeasure.IsAddHaarMeasure := by
  have := h.free
  have := h.finite
  rw [← h.addHaar_dualBasis (Free.chooseBasis ℤ N)]
  infer_instance

/-- The parallelepiped spanned by any dual basis has measure one. -/
theorem dualMeasure_parallelepiped (b : Basis κ ℤ N) :
    h.dualMeasure (parallelepiped (h.dualBasis b)) = 1 := by
  rw [← h.addHaar_dualBasis b, Basis.addHaar_self]

/-- **The weight lattice has covolume one** for the lattice-normalized measure. -/
theorem covolume_weightLattice : ZLattice.covolume (weightLattice i) h.dualMeasure = 1 := by
  have := h.free
  have := h.finite
  let b := Free.chooseBasis ℤ N
  have := (h.dualBasis b).finiteDimensional_of_finite
  rw [← h.span_dualBasis b, ZLattice.covolume_eq_measure_fundamentalDomain _ _
      (ZSpan.isAddFundamentalDomain (h.dualBasis b) h.dualMeasure),
    measureReal_def, measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ _),
    h.dualMeasure_parallelepiped, ENNReal.toReal_one]

/-- **Dual coordinates are measure preserving.** The coordinates `x ↦ (x (i (b j)))_j` in the dual
basis of an integral basis carry the lattice-normalized measure to Lebesgue measure on `ℝ^κ`. -/
theorem measurePreserving_dualBasis_equivFun (b : Basis κ ℤ N) :
    MeasurePreserving (h.dualBasis b).equivFun h.dualMeasure volume := by
  have := (h.dualBasis b).finiteDimensional_of_finite
  have hmap := (h.dualBasis b).map_addHaar (h.dualBasis b).equivFunL
  have hb : (h.dualBasis b).map (h.dualBasis b).equivFunL.toLinearEquiv = Pi.basisFun ℝ κ := by
    classical
    ext j k
    simp [Pi.single_apply, Finsupp.single_apply, eq_comm]
  rw [h.addHaar_dualBasis, hb, Basis.addHaar_basisFun] at hmap
  have hcoe : ⇑(h.dualBasis b).equivFunL = (h.dualBasis b).equivFun :=
    funext fun x ↦ funext fun j ↦ by rw [Basis.equivFunL_apply, Basis.equivFun_apply]
  rw [← hcoe]
  exact ⟨(h.dualBasis b).equivFunL.continuous.measurable, hmap⟩

/-- **Volumes in dual coordinates.** The lattice-normalized measure of the set of functionals whose
coordinates `(x (i (b j)))_j` in the dual basis of an integral basis `b` lie in `S ⊆ ℝ^κ` is the
Lebesgue measure of `S`, for every set `S`. -/
theorem dualMeasure_preimage_dualBasis_equivFun (b : Basis κ ℤ N) (S : Set (κ → ℝ)) :
    h.dualMeasure ((h.dualBasis b).equivFun ⁻¹' S) = volume S := by
  have := (h.dualBasis b).finiteDimensional_of_finite
  have hemb : MeasurableEmbedding (h.dualBasis b).equivFun := by
    simpa using (h.dualBasis b).equivFun.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  exact (h.measurePreserving_dualBasis_equivFun b).measure_preimage_emb hemb S

/-! ### Naturality and products -/

variable {N' V' : Type*} [AddCommGroup N'] [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {i' : N' →+ V'} [MeasurableSpace (StrongDual ℝ V')] [BorelSpace (StrongDual ℝ V')]

/-- **Naturality of the lattice-normalized measure.** If a lattice isomorphism `f : N ≃+ N'` and a
real-linear isomorphism `g : V ≃L[ℝ] V'` are compatible, `g ∘ i = i' ∘ f`, then the transpose
`y ↦ y ∘ g` carries the lattice-normalized measure of `i'` to that of `i`. -/
theorem map_comp_dualMeasure (h' : IsIntegralLattice i') (f : N ≃+ N') (g : V ≃L[ℝ] V')
    (hfg : ∀ n, g (i n) = i' (f n)) :
    h'.dualMeasure.map (fun y : StrongDual ℝ V' ↦ y.comp (g : V →L[ℝ] V')) = h.dualMeasure := by
  classical
  have := h.free
  have := h.finite
  let b := Free.chooseBasis ℤ N
  let T : StrongDual ℝ V' ≃L[ℝ] StrongDual ℝ V :=
    g.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have hT : ⇑T = fun y : StrongDual ℝ V' ↦ y.comp (g : V →L[ℝ] V') := by
    ext y v
    simp [T]
  have hB : (h'.dualBasis (b.map f.toIntLinearEquiv)).map T.toLinearEquiv = h.dualBasis b := by
    refine Basis.eq_of_apply_eq fun j ↦ (h.dualBasis b).ext_elem fun k ↦ ?_
    have hk := h'.dualBasis_repr (b.map f.toIntLinearEquiv)
      (h'.dualBasis (b.map f.toIntLinearEquiv) j) k
    simp only [Basis.repr_self, Basis.map_apply, AddEquiv.coe_toIntLinearEquiv] at hk
    simp [hT, hfg, ← hk]
  have := (h.dualBasis b).finiteDimensional_of_finite
  rw [← hT, ← h'.addHaar_dualBasis (b.map f.toIntLinearEquiv), Basis.map_addHaar, hB,
    h.addHaar_dualBasis]

variable [MeasurableSpace (StrongDual ℝ (V × V'))] [BorelSpace (StrongDual ℝ (V × V'))]

/-- **The lattice-normalized measure of a product lattice** is the product measure, transported
along the identification `V* × V'* ≃ (V × V')*`, `(y, y') ↦ y.coprod y'`. -/
theorem dualMeasure_prod (h' : IsIntegralLattice i') :
    (h.prod h').dualMeasure =
      (h.dualMeasure.prod h'.dualMeasure).map (ContinuousLinearMap.coprodEquivL ℝ) := by
  classical
  have := h.free
  have := h.finite
  have := h'.free
  have := h'.finite
  let b := Free.chooseBasis ℤ N
  let b' := Free.chooseBasis ℤ N'
  have := (h.dualBasis b).finiteDimensional_of_finite
  have := (h'.dualBasis b').finiteDimensional_of_finite
  have hB : ((h.dualBasis b).prod (h'.dualBasis b')).map
      (ContinuousLinearMap.coprodEquivL ℝ).toLinearEquiv = (h.prod h').dualBasis (b.prod b') := by
    refine Basis.eq_of_apply_eq fun j ↦ ((h.prod h').dualBasis (b.prod b')).ext_elem fun k ↦ ?_
    rcases j with j | j <;> rcases k with k | k <;> simp [Finsupp.single_apply, eq_comm]
  have := ((h.prod h').dualBasis (b.prod b')).finiteDimensional_of_finite
  rw [← h.addHaar_dualBasis b, ← h'.addHaar_dualBasis b', ← Basis.prod_addHaar,
    Basis.map_addHaar, hB, addHaar_dualBasis]

end TauCeti.Toric.IsIntegralLattice
