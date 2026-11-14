/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.ComplexManifold
public import TauCeti.Analysis.Complex.Wirtinger.Polydisc
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.ModelSpace

/-!
# Local exactness for smooth forms of type `(0,q)`

On a complex vector space, the Dolbeault differential of a smooth `(0,1)`-form `η` on `v,w` is
`∂bar η(v,w) = ∂bar(η(w))(v) - ∂bar(η(v))(w)` (`SmoothForm.delBar_apply_pair`), so the
conjugate coordinate derivatives of the coefficients of a closed `(0,1)`-form are symmetric.

A smooth form of type `(0,q+1)` on `ι → ℂ` whose Dolbeault differential vanishes on a finite
product of planar domains has a smooth primitive of type `(0,q)` near every compact subproduct.
Both the input and the primitive are `SmoothForm`s. The coefficients of the input are closed for
the coordinate operator `TauCeti.delBarCoeff` (`SmoothForm.conjCoeff_delBar`), the
coordinate Dolbeault–Grothendieck lemma solves for the coefficients of a primitive near the compact
product, and these are extended smoothly and assembled into a form
(`SmoothForm.exists_isOfType_conjCoeff_eq`). Exactness is asserted near the compact product, and
on polydiscs on every smaller concentric polydisc, with no claim of exactness on the whole original
domain.

## Main declarations

* `TauCeti.SmoothForm.conjWirtingerDeriv_apply_single_eq`: the symmetry of conjugate
  coordinate derivatives of a Dolbeault-closed one-form.
* `TauCeti.SmoothForm.IsOfType.exists_delBar_eventually_eq_of_pi`: local exactness of closed
  `(0,q+1)`-forms on products of planar domains.
* `TauCeti.SmoothForm.IsOfType.exists_delBar_eq_of_polydisc`: exactness of closed
  `(0,q+1)`-forms on a polydisc, on every smaller concentric polydisc.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 2.3.3.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0, §2.
-/

public section

noncomputable section

open Complex Filter Set Topology
open scoped Manifold ContDiff TauCeti.ComplexManifold ComplexConjugate

namespace TauCeti.SmoothForm

open SmoothAlmostComplexStructure

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

section Coordinates

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- A Dolbeault-closed smooth one-form has symmetric conjugate coordinate derivatives. -/
theorem conjWirtingerDeriv_apply_single_eq
    (η : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F 1) {z : ι → ℂ}
    (hz : ((ofComplexManifold (ι → ℂ) (ι → ℂ)).delBar η).1 z = 0) (i j : ι) :
    conjWirtingerDeriv (fun y ↦ η.1 y ![Pi.single j 1]) z (Pi.single i 1) =
      conjWirtingerDeriv (fun y ↦ η.1 y ![Pi.single i 1]) z (Pi.single j 1) := by
  apply sub_eq_zero.mp
  rw [← delBar_apply_pair η, hz]
  rfl

variable [CompleteSpace F]

omit [DecidableEq ι] in
/-- **The Dolbeault–Grothendieck lemma for `(0,q)`-forms on product domains.** A smooth form `η` of
type `(0,q+1)` on `ι → ℂ`, with coefficients in a complex Banach space, whose Dolbeault differential
vanishes on a product `∏ U_i` of open subsets of `ℂ`, is Dolbeault-exact near every compact
subproduct `∏ K_i`, `K_i ⊆ U_i`: some smooth form `f` of type `(0,q)` satisfies `∂bar f = η`
there. -/
theorem IsOfType.exists_delBar_eventually_eq_of_pi {q : ℕ}
    {η : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F (q + 1)}
    (hη : η.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) 0 (q + 1))
    {U K : ι → Set ℂ} (hU : ∀ i, IsOpen (U i)) (hK : ∀ i, IsCompact (K i))
    (hKU : ∀ i, K i ⊆ U i)
    (hclosed : ∀ z ∈ univ.pi U,
      ((ofComplexManifold (ι → ℂ) (ι → ℂ)).delBar η).1 z = 0) :
    ∃ f : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F q,
      f.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) 0 q ∧ ∀ᶠ z in 𝓝ˢ (univ.pi K),
        ((ofComplexManifold (ι → ℂ) (ι → ℂ)).delBar f).1 z = η.1 z := by
  classical
  -- Order the coordinates, to index the coefficients of forms by increasing families.
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  -- Solve for the coefficients of a primitive near `∏ K_i`.
  obtain ⟨u, hu⟩ := exists_contDiffAt_delBarCoeff_eventually_eq_of_pi hU (f := η.conjCoeff)
    (fun I _ ↦ (contDiff_conjCoeff η I).contDiffOn)
    (fun z hz I hI ↦ by
      rw [← conjCoeff_delBar η, conjCoeff_of_card_eq _ hI, hclosed z hz]
      rfl) hK hKU
  obtain ⟨V, hV, hKV, hVu⟩ := eventually_nhdsSet_iff_exists.1 hu
  -- Extend them to smooth functions on `ι → ℂ`, and assemble these into a form of type `(0,q)`.
  have hext (J : Finset ι) :
      ∃ g : (ι → ℂ) → F, ContDiff ℝ ∞ g ∧ ∀ z ∈ univ.pi K, g =ᶠ[𝓝 z] u J := by
    have huV : ContDiffOn ℝ ∞ (u J) V := fun z hz ↦ ((hVu z hz).1 J).contDiffWithinAt
    obtain ⟨g, hg, -, -, -, hgu⟩ :=
      huV.exists_contDiff_eventuallyEq_on_isCompact (isCompact_univ_pi hK) hV hKV
    exact ⟨g, hg, hgu⟩
  choose g hg hgu using hext
  obtain ⟨f, hf, hfg⟩ := exists_isOfType_conjCoeff_eq (k := q) fun J _ ↦ hg J
  refine ⟨f, hf, eventually_nhdsSet_iff_forall.2 fun z hz ↦ ?_⟩
  have hgu' : ∀ᶠ y in 𝓝 z, ∀ J, g J =ᶠ[𝓝 y] u J :=
    eventually_all.2 fun J ↦ (hgu J z hz).eventuallyEq_nhds
  filter_upwards [hV.mem_nhds (hKV hz), hgu'] with y hyV hy
  -- Both sides have type `(0,q+1)`, and their coefficients agree.
  refine hf.delBar.apply_eq_of_conjCoeff_eq hη fun I hI ↦ ?_
  rw [conjCoeff_delBar f, ← (hVu y hyV).2 I hI]
  refine delBarCoeff_congr fun j hj ↦ ?_
  rw [hfg _ (by rw [Finset.card_erase_of_mem hj, hI, Nat.add_sub_cancel])]
  exact hy _

omit [DecidableEq ι] in
/-- **The Dolbeault–Grothendieck lemma for `(0,q)`-forms on polydiscs.** A smooth form `η` of type
`(0,q+1)` on `ι → ℂ`, with coefficients in a complex Banach space, whose Dolbeault differential
vanishes on the polydisc `∏ B(c_i, r_i)`, is Dolbeault-exact on every concentric polydisc
`∏ B(c_i, r'_i)` with `r'_i < r_i`: some smooth form `f` of type `(0,q)` satisfies `∂bar f = η`
there. -/
theorem IsOfType.exists_delBar_eq_of_polydisc {q : ℕ}
    {η : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F (q + 1)}
    (hη : η.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) 0 (q + 1)) {c : ι → ℂ} {r r' : ι → ℝ}
    (hr : ∀ i, r' i < r i)
    (hclosed : ∀ z ∈ univ.pi fun i ↦ Metric.ball (c i) (r i),
      ((ofComplexManifold (ι → ℂ) (ι → ℂ)).delBar η).1 z = 0) :
    ∃ f : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F q,
      f.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) 0 q ∧
        ∀ z ∈ univ.pi fun i ↦ Metric.ball (c i) (r' i),
          ((ofComplexManifold (ι → ℂ) (ι → ℂ)).delBar f).1 z = η.1 z := by
  obtain ⟨f, hf, hfη⟩ := hη.exists_delBar_eventually_eq_of_pi (fun i ↦ Metric.isOpen_ball)
    (fun i ↦ isCompact_closedBall (c i) (r' i)) (fun i ↦ Metric.closedBall_subset_ball (hr i))
    hclosed
  exact ⟨f, hf, fun z hz ↦ hfη.self_of_nhdsSet z
    (pi_mono (fun i _ ↦ Metric.ball_subset_closedBall) hz)⟩

end Coordinates


end TauCeti.SmoothForm
