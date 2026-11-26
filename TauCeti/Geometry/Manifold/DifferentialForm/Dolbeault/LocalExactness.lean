/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.ComplexManifold
public import TauCeti.Analysis.Complex.Polydisc.Basic
public import TauCeti.Analysis.Complex.Wirtinger.Polydisc
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Leibniz
import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.ModelSpace
import TauCeti.Geometry.Manifold.DifferentialForm.Opens.ModelSpace

/-!
# Local exactness for smooth forms of type `(p,q)`

A smooth form of type `(p,q+1)` on `ι → ℂ` whose Dolbeault differential vanishes on a finite
product of planar domains has a smooth primitive of type `(p,q)` near every compact subproduct.
Both the input and the primitive are smooth on all of `ι → ℂ`, with coefficients in a complex
Banach space; only closedness and the primitive equation are restricted to the indicated sets.

On a whole open polydisc `TauCeti.polydisc c r`, regarded as an open complex submanifold of
`ι → ℂ`, every smooth `∂bar`-closed form of type `(p,q+1)` is `∂bar` of a smooth form of type
`(p,q)` on the same polydisc: this is the Dolbeault–Grothendieck lemma on polydiscs. Here neither
form is assumed to extend smoothly across the boundary of the polydisc.

## Main declarations

* `TauCeti.SmoothForm.IsOfType.exists_delBar_eventually_eq_of_pi`: local exactness of closed
  `(p,q+1)`-forms on products of planar domains.
* `TauCeti.SmoothForm.IsOfType.exists_delBar_eq_of_polydisc_of_lt`: exactness of closed
  `(p,q+1)`-forms on `ι → ℂ` on every polydisc strictly smaller than a polydisc where they are
  closed, with a primitive smooth on all of `ι → ℂ`.
* `TauCeti.SmoothForm.IsOfType.exists_delBar_eq_of_polydisc`: the Dolbeault–Grothendieck lemma
  for smooth `(p,q+1)`-forms on a whole open polydisc.

## Implementation notes

For forms of type `(0,q+1)` the coefficients of the input are closed for the coordinate operator
`TauCeti.delBarCoeff` (`SmoothForm.conjCoeff_delBar`), the coordinate Dolbeault–Grothendieck lemma
solves for the coefficients of a primitive near the compact product, or on the whole polydisc
(`TauCeti.exists_contDiffOn_delBarCoeff_eq_of_polydisc`), and these are assembled into a form
(`SmoothForm.exists_isOfType_conjCoeff_eq`, `SmoothForm.conjCoeffForm`).

The general case reduces to this one by induction on `p`. Applying the output-scaled contraction
`ι_v - I • ι_{I • v}`, lowers the type `(p+1,q)` to `(p,q)`
(`ContinuousAlternatingMap.IsOfType.curryLeftTopological_sub_I_smul`), and for a constant vector
`v` it anticommutes with `∂bar`. The contractions `η_j` of a closed form `η` of type
`(p+1,q+1)` with the coordinate vectors are therefore closed of type `(p,q+1)`, with primitives
`g_j`. The Euler identity `∑ j, dz_j ∧ η_j = 2 (p + 1) • η`
(`ContinuousAlternatingMap.IsOfType.alternatizeUncurryFin_curryLeft_sub_I_smul_comp`), the graded
Leibniz rule and `∂bar dz_j = 0` then show that `-(2 (p + 1))⁻¹ • ∑ j, dz_j ∧ g_j` is a primitive
of `η` of type `(p+1,q)`.

On the polydisc these pointwise identities are read off forms on `ι → ℂ`: near each point a form
of type `(p,q)` on the polydisc agrees with a smooth form of type `(p,q)` on `ι → ℂ`, the type
component of a cut-off of its ambient representative, and `∂bar` commutes with restriction to open
subsets because the inclusions are holomorphic.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 2.3.3.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0, §2.
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter I, (3.29).
-/

public section

noncomputable section

open Complex Filter Set Topology
open scoped Manifold ContDiff TauCeti.ComplexManifold ComplexConjugate

namespace TauCeti.SmoothForm

open SmoothAlmostComplexStructure

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

open ContinuousAlternatingMap (holCurry)

section Coordinates

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- **Euler identity for smooth forms.** If the values at `z` of the forms `β i` are those of the
`(1,0)`-contractions of a form `η` of type `(p,q)` with the coordinate vectors, then
`∑ i, dz_i ∧ β i` takes the value `2 p • η` at `z`. -/
private theorem sum_wedgeWith_dz_apply {k p q : ℕ} {η : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F (k + 1)}
    (hη : η.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) p q)
    (β : ι → SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F k) {z : ι → ℂ}
    (hβ : ∀ i, (β i).val z = (holInterior (Pi.single i 1) η).val z) :
    (∑ i, LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F n)
      (Nat.add_comm 1 k) (wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ) (dz i) (β i))).val z =
      (2 * p : ℂ) • η.val z := by
  rw [← sum_wedgeWith_dz_holInterior_apply hη z]
  ext v
  simp only [Submodule.coe_sum, Finset.sum_apply, ContinuousAlternatingMap.sum_apply, cast_apply,
    coe_wedgeWith, RoughForm.wedgeWith_apply', hβ]

omit [DecidableEq ι] in
/-- **The inductive step.** On a complex manifold, let `w_i` be `∂bar`-closed forms of type `(1,0)`
and let `g_i` be forms of type `(p,q)` such that `∑ i, w_i ∧ ∂bar g_i = 2 (p + 1) • η` near a set
`S`. Then `-(2 (p + 1))⁻¹ • ∑ i, w_i ∧ g_i` is a primitive of `η` of type `(p+1,q)` near `S`. -/
private theorem exists_delBar_eventually_eq_of_sum_wedgeWith {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] {m p q : ℕ} (hm : p + q = m)
    {η : SmoothForm 𝓘(ℝ, E) M F (m + 1 + 1)} {S : Set M} (w : ι → SmoothForm 𝓘(ℝ, E) M ℂ 1)
    (hw : ∀ i, (w i).IsOfType (ofComplexManifold E M) 1 0)
    (hwc : ∀ i, (ofComplexManifold E M).delBar (w i) = 0) (g : ι → SmoothForm 𝓘(ℝ, E) M F m)
    (hg : ∀ i, (g i).IsOfType (ofComplexManifold E M) p q)
    (hgη : ∀ᶠ z in 𝓝ˢ S, (∑ i, LinearEquiv.cast (R := ℝ)
      (M := fun n ↦ SmoothForm 𝓘(ℝ, E) M F n) (Nat.add_comm 1 (m + 1))
        (wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ) (w i)
          ((ofComplexManifold E M).delBar (g i)))).val z =
      (2 * ((p + 1 : ℕ) : ℂ)) • η.val z) :
    ∃ f : SmoothForm 𝓘(ℝ, E) M F (m + 1),
      f.IsOfType (ofComplexManifold E M) (p + 1) q ∧ ∀ᶠ z in 𝓝ˢ S,
        ((ofComplexManifold E M).delBar f).val z = η.val z := by
  let μ : ℂ →L[ℝ] F →L[ℝ] F := ContinuousLinearMap.lsmul ℝ ℂ
  have hμ₁ (c : ℂ) (a : ℂ) (b : F) : μ (c • a) b = c • μ a b := by simp [μ, mul_smul]
  have hμ₂ (c : ℂ) (a : ℂ) (b : F) : μ a (c • b) = c • μ a b := by simp [μ, smul_comm a c]
  let c : ℂ := -(2 * ((p + 1 : ℕ) : ℂ))⁻¹
  have hwg (i : ι) := (hw i).wedgeWith hμ₁ hμ₂ (hg i)
  rw [Nat.add_comm 1 p, Nat.zero_add] at hwg
  refine ⟨c • ∑ i, LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm 𝓘(ℝ, E) M F n)
    (Nat.add_comm 1 m) (SmoothForm.wedgeWith μ (w i) (g i)), ?_, ?_⟩
  · refine IsOfType.smul (Finset.sum_induction _
      (fun φ : SmoothForm 𝓘(ℝ, E) M F (m + 1) ↦ φ.IsOfType (ofComplexManifold E M) (p + 1) q)
      (fun _ _ ha hb ↦ ha.add hb) (isOfType_zero_iff.2 (by omega))
      fun i _ ↦ (hwg i).cast _) c
  -- By the Leibniz rule and `∂bar w_i = 0`, `∂bar` of the primitive is `-c • ∑ w_i ∧ ∂bar g_i`.
  have hdf : (ofComplexManifold E M).delBar (c • ∑ i, LinearEquiv.cast (R := ℝ)
      (M := fun n ↦ SmoothForm 𝓘(ℝ, E) M F n) (Nat.add_comm 1 m)
        (SmoothForm.wedgeWith μ (w i) (g i))) =
      (-c) • ∑ i, LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm 𝓘(ℝ, E) M F n)
        (Nat.add_comm 1 (m + 1))
          (SmoothForm.wedgeWith μ (w i) ((ofComplexManifold E M).delBar (g i))) := by
    simp only [map_smul, map_sum, delBar_cast, delBar_wedgeWith _ hμ₁ hμ₂, hwc,
      map_zero, LinearMap.zero_apply, zero_add, cast_cast, pow_one]
    -- `simp` does not match `neg_one_smul` against the real action on smooth forms directly.
    have hneg (φ : SmoothForm 𝓘(ℝ, E) M F (m + 1 + 1)) : (-1 : ℝ) • φ = -φ :=
      neg_one_smul ℝ φ
    simp only [hneg, Finset.sum_neg_distrib, smul_neg]
    exact (neg_smul c _).symm
  filter_upwards [hgη] with z hz
  have hc : -c * (2 * ((p + 1 : ℕ) : ℂ)) = 1 := by
    rw [_root_.neg_neg]
    exact inv_mul_cancel₀ (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.2 p.succ_ne_zero))
  rw [hdf, smul_toRoughForm, Pi.smul_apply, hz, smul_smul, hc, one_smul]

variable [CompleteSpace F]

omit [DecidableEq ι] in
/-- The case `p = 0`: the coefficients of a closed form of type `(0,q+1)` are solved for by the
coordinate Dolbeault–Grothendieck lemma, extended smoothly and assembled into a form. -/
private theorem IsOfType.exists_delBar_eventually_eq_of_pi_zero {q : ℕ}
    {η : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F (q + 1)}
    (hη : η.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) 0 (q + 1))
    {U K : ι → Set ℂ} (hU : ∀ i, IsOpen (U i)) (hK : ∀ i, IsCompact (K i))
    (hKU : ∀ i, K i ⊆ U i)
    (hclosed : ∀ z ∈ univ.pi U,
      ((ofComplexManifold (ι → ℂ) (ι → ℂ)).delBar η).val z = 0) :
    ∃ f : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F q,
      f.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) 0 q ∧ ∀ᶠ z in 𝓝ˢ (univ.pi K),
        ((ofComplexManifold (ι → ℂ) (ι → ℂ)).delBar f).val z = η.val z := by
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
/-- **The Dolbeault–Grothendieck lemma for `(p,q)`-forms on product domains.** Let `η` be smooth
on all of `ι → ℂ`, of type `(p,q+1)`, with coefficients in a complex Banach space. If its
Dolbeault differential vanishes on a product `∏ U_i` of open subsets of `ℂ`, then it is
Dolbeault-exact near every compact subproduct `∏ K_i`, `K_i ⊆ U_i`: some form `f`, smooth on
all of `ι → ℂ` and of type `(p,q)`, satisfies `∂bar f = η` there. -/
theorem IsOfType.exists_delBar_eventually_eq_of_pi {k p q : ℕ}
    {η : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F (k + 1)}
    (hη : η.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) p (q + 1))
    {U K : ι → Set ℂ} (hU : ∀ i, IsOpen (U i)) (hK : ∀ i, IsCompact (K i))
    (hKU : ∀ i, K i ⊆ U i)
    (hclosed : ∀ z ∈ univ.pi U,
      ((ofComplexManifold (ι → ℂ) (ι → ℂ)).delBar η).val z = 0) :
    ∃ f : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F k,
      f.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) p q ∧ ∀ᶠ z in 𝓝ˢ (univ.pi K),
        ((ofComplexManifold (ι → ℂ) (ι → ℂ)).delBar f).val z = η.val z := by
  classical
  induction p generalizing k with
  | zero =>
    obtain rfl : k = q := by have := hη.add_eq; omega
    exact hη.exists_delBar_eventually_eq_of_pi_zero hU hK hKU hclosed
  | succ p ih =>
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨p + q, by have := hη.add_eq; omega⟩
    -- The `(1,0)`-contractions of `η` with the coordinate vectors are closed on `∏ U_i`, so they
    -- are exact near `∏ K_i` by the inductive hypothesis.
    have hstep (i : ι) : ∃ g : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F m,
        g.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) p q ∧ ∀ᶠ z in 𝓝ˢ (univ.pi K),
          ((ofComplexManifold (ι → ℂ) (ι → ℂ)).delBar g).val z =
            (SmoothForm.holInterior (Pi.single i 1) η).val z := by
      refine ih (isOfType_holInterior hη _) fun z hz ↦ ?_
      rw [delBar_holInterior, Submodule.coe_neg, Pi.neg_apply, holInterior_val, hclosed z hz]
      exact neg_eq_zero.2 (map_zero (holCurry (Pi.single i 1)))
    choose g hg hgη using hstep
    refine exists_delBar_eventually_eq_of_sum_wedgeWith (by have := hη.add_eq; omega) dz
      isOfType_dz delBar_dz g hg ?_
    filter_upwards [eventually_all.2 hgη] with z hz
    exact sum_wedgeWith_dz_apply hη _ hz

omit [DecidableEq ι] in
/-- **The Dolbeault–Grothendieck lemma for `(p,q)`-forms on polydiscs.** Let `η` be smooth on
all of `ι → ℂ`, of type `(p,q+1)`, with coefficients in a complex Banach space. If its Dolbeault
differential vanishes on `∏ B(c_i, r_i)`, then it is Dolbeault-exact on every concentric
polydisc `∏ B(c_i, r'_i)` with `r'_i < r_i`: some form `f`, smooth on all of `ι → ℂ` and of type
`(p,q)`, satisfies `∂bar f = η` there. -/
theorem IsOfType.exists_delBar_eq_of_polydisc_of_lt {k p q : ℕ}
    {η : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F (k + 1)}
    (hη : η.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) p (q + 1)) {c : ι → ℂ} {r r' : ι → ℝ}
    (hr : ∀ i, r' i < r i)
    (hclosed : ∀ z ∈ univ.pi fun i ↦ Metric.ball (c i) (r i),
      ((ofComplexManifold (ι → ℂ) (ι → ℂ)).delBar η).val z = 0) :
    ∃ f : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F k,
      f.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) p q ∧
        ∀ z ∈ univ.pi fun i ↦ Metric.ball (c i) (r' i),
          ((ofComplexManifold (ι → ℂ) (ι → ℂ)).delBar f).val z = η.val z := by
  obtain ⟨f, hf, hfη⟩ := hη.exists_delBar_eventually_eq_of_pi (fun i ↦ Metric.isOpen_ball)
    (fun i ↦ isCompact_closedBall (c i) (r' i)) (fun i ↦ Metric.closedBall_subset_ball (hr i))
    hclosed
  exact ⟨f, hf, fun z hz ↦ hfη.self_of_nhdsSet z
    (pi_mono (fun i _ ↦ Metric.ball_subset_closedBall) hz)⟩

end Coordinates

section Opens

open TopologicalSpace

variable {k : ℕ}

/-- On an open subset `U` of a complex vector space `E`, the Dolbeault differential of a form `η`
at a point `z` is that of any smooth form on `E` agreeing near `z` with an ambient representative
`η₀` of `η`. -/
private theorem delBar_val_eq_of_eventuallyEq {U : Opens E} {η : SmoothForm 𝓘(ℝ, E) U F k}
    {η₀ : E → E [⋀^Fin k]→L[ℝ] F} (hη₀ : ∀ x : U, η.val x = η₀ x)
    {G : SmoothForm 𝓘(ℝ, E) E F k} {z : U} (hG : G.val =ᶠ[𝓝 (z : E)] η₀) :
    ((ofComplexManifold E U).delBar η).val z = ((ofComplexManifold E E).delBar G).val z := by
  obtain ⟨t, htG, ht, hzt⟩ := eventually_nhds_iff.1 hG
  let V : Opens E := ⟨t ∩ U, ht.inter U.isOpen⟩
  have hVU : V ≤ U := inter_subset_right
  -- The restrictions of `η` and `G` to `V` agree, and restriction commutes with `∂bar`.
  have hres : mpullback (Opens.inclusion hVU) (contMDiff_inclusion hVU) η =
      mpullback (Subtype.val : V → E) contMDiff_subtypeVal G := by
    refine Subtype.ext (funext fun y ↦ ?_)
    rw [coe_mpullback, mpullback_inclusion_apply, coe_mpullback_subtype_val_apply, hη₀,
      htG _ y.property.1]
  have h := congrArg (fun φ ↦ ((ofComplexManifold E V).delBar φ).val ⟨z, hzt, z.property⟩) hres
  simp only [← mpullback_delBar _ _ (isPseudoholomorphic_ofComplexManifold_inclusion hVU),
    ← mpullback_delBar _ _ (isPseudoholomorphic_ofComplexManifold_subtype_val V)] at h
  rwa [coe_mpullback, mpullback_inclusion_apply, coe_mpullback_subtype_val_apply] at h

variable [FiniteDimensional ℂ E]

/-- Near a point of an open subset `U` of a finite-dimensional complex vector space `E`, a field
`η₀` smooth on `U` agrees with a smooth form on `E`. -/
private theorem exists_eventuallyEq_of_opens {U : Opens E} {η₀ : E → E [⋀^Fin k]→L[ℝ] F}
    (hc : ContDiffOn ℝ ∞ η₀ U) (z : U) :
    ∃ G : SmoothForm 𝓘(ℝ, E) E F k, G.val =ᶠ[𝓝 (z : E)] η₀ := by
  obtain ⟨g, hg, -, -, -, hgη⟩ := hc.exists_contDiff_eventuallyEq_on_isCompact isCompact_singleton
    U.isOpen (singleton_subset_iff.2 z.property)
  exact ⟨⟨g, (isSmoothForm_modelSpace_iff.mpr hg).mem_smoothBundleForms⟩, hgη _ rfl⟩

/-- Near a point of an open subset `U` of a finite-dimensional complex vector space `E`, a form of
type `(p,q)` on `U`, with an ambient representative `η₀` smooth on `U`, agrees with a smooth form of
type `(p,q)` on `E`: the type-`(p,q)` component of any smooth form on `E` agreeing with `η₀` near
the point. -/
private theorem IsOfType.exists_isOfType_eventuallyEq_of_opens {U : Opens E} {p q : ℕ}
    {η : SmoothForm 𝓘(ℝ, E) U F k} (hη : η.IsOfType (ofComplexManifold E U) p q)
    {η₀ : E → E [⋀^Fin k]→L[ℝ] F} (hη₀ : ∀ x : U, η.val x = η₀ x)
    (hc : ContDiffOn ℝ ∞ η₀ U) (z : U) :
    ∃ G : SmoothForm 𝓘(ℝ, E) E F k,
      G.IsOfType (ofComplexManifold E E) p q ∧ G.val =ᶠ[𝓝 (z : E)] η₀ := by
  obtain ⟨G, hG⟩ := exists_eventuallyEq_of_opens hc z
  refine ⟨(ofComplexManifold E E).typeProjection p q G,
    (ofComplexManifold E E).isOfType_typeProjection hη.add_eq G, ?_⟩
  filter_upwards [hG, U.isOpen.mem_nhds z.property] with y hy hyU
  have h := hη.apply ⟨y, hyU⟩
  rw [toEndomorphism_ofComplexManifold, hη₀] at h
  simp only [coe_typeProjection, toEndomorphism_ofComplexManifold, hy]
  exact h.typeProjection_self

/-- The `(1,0)`-contraction `ι_v - I • ι_{I • v}` by a constant vector `v` of a `∂bar`-closed form
of type `(p+1,q)` on an open subset of `E` is a `∂bar`-closed form of type `(p,q)`. -/
private theorem IsOfType.exists_holCurry_eq_of_opens {U : Opens E} {m p q : ℕ}
    {η : SmoothForm 𝓘(ℝ, E) U F (m + 1)} (hη : η.IsOfType (ofComplexManifold E U) (p + 1) q)
    (hclosed : (ofComplexManifold E U).delBar η = 0) (v : E) :
    ∃ β : SmoothForm 𝓘(ℝ, E) U F m,
      (∀ z, β.val z = holCurry v (η.val z : E [⋀^Fin (m + 1)]→L[ℝ] F)) ∧
        β.IsOfType (ofComplexManifold E U) p q ∧ (ofComplexManifold E U).delBar β = 0 := by
  obtain ⟨η₀, hη₀c, hη₀⟩ := η.isSmoothForm.exists_contDiffOn_opens
  let C := (holCurry (k := m) (F := F) v).restrictScalars ℝ
  let β : SmoothForm 𝓘(ℝ, E) U F m :=
    ⟨fun x ↦ C (η₀ x), ((isSmoothForm_opens_iff fun _ ↦ rfl).2
      (C.contDiff.comp_contDiffOn hη₀c)).mem_smoothBundleForms⟩
  have hβ (z : U) : β.val z = holCurry v (η.val z : E [⋀^Fin (m + 1)]→L[ℝ] F) := by
    rw [hη₀]
    -- The value of `β` is its defining field, with `C` the contraction as a real-linear map.
    rfl
  -- Near each point `β` agrees with the contraction of a smooth form on `E` of type `(p+1,q)`.
  have hloc (z : U) : ∃ G : SmoothForm 𝓘(ℝ, E) E F (m + 1),
      G.IsOfType (ofComplexManifold E E) (p + 1) q ∧
        (holInterior v G).val =ᶠ[𝓝 (z : E)] (fun x ↦ C (η₀ x)) ∧
        ((ofComplexManifold E E).delBar G).val z = 0 := by
    obtain ⟨G, hGt, hG⟩ := hη.exists_isOfType_eventuallyEq_of_opens hη₀ hη₀c z
    refine ⟨G, hGt, ?_, ?_⟩
    · filter_upwards [hG] with y hy
      rw [holInterior_val, hy]
      -- `C` is the contraction `holCurry v` as a real-linear map.
      rfl
    · rw [← delBar_val_eq_of_eventuallyEq hη₀ hG, hclosed]
      -- The value of the zero form is zero.
      rfl
  refine ⟨β, hβ, isOfType_iff_forall.2 ⟨by have := hη.add_eq; omega, fun z ↦ ?_⟩,
    Subtype.ext (funext fun z ↦ ?_)⟩
  · obtain ⟨G, hGt, hG, -⟩ := hloc z
    have h := (isOfType_holInterior hGt v).apply_modelSpace z
    rw [hG.self_of_nhds] at h
    rw [toEndomorphism_ofComplexManifold]
    exact h
  · obtain ⟨G, -, hG, hGc⟩ := hloc z
    rw [delBar_val_eq_of_eventuallyEq (fun _ ↦ rfl) hG, delBar_holInterior, neg_toRoughForm,
      Pi.neg_apply, holInterior_val, hGc]
    exact neg_eq_zero.2 (map_zero (holCurry v))

end Opens

section Polydisc

open Metric TopologicalSpace
open scoped Finset

variable {ι : Type*} [Fintype ι]

/-- On an open subset `U` of `ι → ℂ`, the coefficients of the Dolbeault differential of a form `φ`
are obtained by `TauCeti.delBarCoeff` from any family `a` of functions agreeing on `U` with the
coefficients of an ambient representative `φ₀` of `φ`. -/
private theorem delBar_val_apply_orderEmbOfFin_of_opens [LinearOrder ι] {U : Opens (ι → ℂ)}
    {k : ℕ} {φ : SmoothForm 𝓘(ℝ, ι → ℂ) U F k} {φ₀ : (ι → ℂ) → (ι → ℂ) [⋀^Fin k]→L[ℝ] F}
    (hφ₀ : ∀ x : U, φ.val x = φ₀ x) (hc : ContDiffOn ℝ ∞ φ₀ U) {a : Finset ι → (ι → ℂ) → F}
    (ha : ∀ J (hJ : #J = k), ∀ y ∈ U, a J y = φ₀ y fun i ↦ Pi.single (J.orderEmbOfFin hJ i) 1)
    (z : U) {I : Finset ι} (hI : #I = k + 1) :
    ((ofComplexManifold (ι → ℂ) U).delBar φ).val z
      (fun i ↦ Pi.single (I.orderEmbOfFin hI i) 1) = delBarCoeff a I z := by
  obtain ⟨G, hG⟩ := exists_eventuallyEq_of_opens hc z
  have hcoeff (j : ι) (hj : j ∈ I) : a (I.erase j) =ᶠ[𝓝 (z : ι → ℂ)] G.conjCoeff (I.erase j) := by
    have hcard : #(I.erase j) = k := by rw [Finset.card_erase_of_mem hj, hI, Nat.add_sub_cancel]
    filter_upwards [hG, U.isOpen.mem_nhds z.property] with y hy hyU
    rw [ha _ hcard y hyU, conjCoeff_of_card_eq _ hcard, hy]
    -- Both sides evaluate `φ₀ y` on the same coordinate vectors, read in the tangent space.
    rfl
  rw [delBarCoeff_congr hcoeff, ← conjCoeff_delBar, conjCoeff_of_card_eq _ hI,
    delBar_val_eq_of_eventuallyEq hφ₀ hG]
  -- Both sides evaluate on the same coordinate vectors, read in the tangent space.
  rfl

variable [CompleteSpace F]

/-- The case `p = 0` of `TauCeti.SmoothForm.IsOfType.exists_delBar_eq_of_polydisc`: the
coefficients of a closed form of type `(0,q+1)` are solved for on the whole polydisc by the
coordinate Dolbeault–Grothendieck lemma and assembled into a form. -/
private theorem IsOfType.exists_delBar_eq_of_polydisc_zero {c : ι → ℂ} {r : ι → ℝ} {q : ℕ}
    {η : SmoothForm 𝓘(ℝ, ι → ℂ) (polydisc c r) F (q + 1)}
    (hη : η.IsOfType (ofComplexManifold (ι → ℂ) (polydisc c r)) 0 (q + 1))
    (hclosed : (ofComplexManifold (ι → ℂ) (polydisc c r)).delBar η = 0) :
    ∃ f : SmoothForm 𝓘(ℝ, ι → ℂ) (polydisc c r) F q,
      f.IsOfType (ofComplexManifold (ι → ℂ) (polydisc c r)) 0 q ∧
        (ofComplexManifold (ι → ℂ) (polydisc c r)).delBar f = η := by
  classical
  -- Order the coordinates, to index the coefficients of forms by increasing families.
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  obtain ⟨η₀, hη₀c, hη₀⟩ := η.isSmoothForm.exists_contDiffOn_opens
  -- The coefficients of `η`, read off its ambient representative, are closed on the polydisc.
  let a : Finset ι → (ι → ℂ) → F := fun I z ↦
    if h : #I = q + 1 then η₀ z fun i ↦ Pi.single (I.orderEmbOfFin h i) 1 else 0
  have ha {I : Finset ι} (hI : #I = q + 1) (z : ι → ℂ) :
      a I z = η₀ z fun i ↦ Pi.single (I.orderEmbOfFin hI i) 1 := by
    simp [a, hI]
  have hmem {z : ι → ℂ} : z ∈ univ.pi (fun i ↦ ball (c i) (r i)) ↔ z ∈ polydisc c r := by
    rw [← SetLike.mem_coe, coe_polydisc]
  obtain ⟨u, hu, hua⟩ := exists_contDiffOn_delBarCoeff_eq_of_polydisc (f := a)
    (fun I hI ↦ by
      rw [show a I = _ from funext (ha hI), ← coe_polydisc]
      exact (ContinuousAlternatingMap.apply ℝ (ι → ℂ) F _).contDiff.comp_contDiffOn hη₀c)
    fun z hz I hI ↦ by
      rw [← delBar_val_apply_orderEmbOfFin_of_opens hη₀ hη₀c (fun J hJ y _ ↦ ha hJ y)
        ⟨z, hmem.1 hz⟩ hI, hclosed]
      -- The value of the zero form is zero.
      rfl
  -- Assemble the solution into the form `∑_J u_J d(conj z)_J` on the polydisc.
  have hf₀ : ContDiffOn ℝ ∞ (fun z ↦ conjCoeffForm q fun J ↦ u J z) (polydisc c r) := by
    rw [coe_polydisc]
    exact contDiffOn_conjCoeffForm fun J _ ↦ hu J
  let f₀ : RoughForm 𝓘(ℝ, ι → ℂ) (polydisc c r) F q := fun z ↦ conjCoeffForm q fun J ↦ u J z
  let f : SmoothForm 𝓘(ℝ, ι → ℂ) (polydisc c r) F q :=
    ⟨f₀, ((isSmoothForm_opens_iff (show ∀ z : polydisc c r,
      f₀ z = conjCoeffForm q fun J ↦ u J z from fun _ ↦ rfl)).2 hf₀).mem_smoothBundleForms⟩
  have hf : f.IsOfType (ofComplexManifold (ι → ℂ) (polydisc c r)) 0 q :=
    isOfType_iff_forall.2 ⟨zero_add q, fun z ↦ by
      rw [toEndomorphism_ofComplexManifold]
      exact isOfType_conjCoeffForm _⟩
  refine ⟨f, hf, Subtype.ext (funext fun z ↦ ?_)⟩
  -- Both sides have type `(0,q+1)` at `z`, and their coefficients agree.
  have h₁ := hf.delBar.apply z
  have h₂ := hη.apply z
  rw [toEndomorphism_ofComplexManifold] at h₁ h₂
  let A : (ι → ℂ) [⋀^Fin (q + 1)]→L[ℝ] F :=
    ((ofComplexManifold (ι → ℂ) (polydisc c r)).delBar f).val z
  let B : (ι → ℂ) [⋀^Fin (q + 1)]→L[ℝ] F := η.val z
  suffices A - B = 0 from sub_eq_zero.1 this
  refine (h₁.sub h₂).eq_zero_of_forall_apply_orderEmbOfFin fun I hI ↦ ?_
  refine (ContinuousAlternatingMap.sub_apply A B _).trans (sub_eq_zero.2 ?_)
  refine (delBar_val_apply_orderEmbOfFin_of_opens (φ := f) (fun _ ↦ rfl) hf₀ (a := u)
    (fun J hJ y _ ↦ (conjCoeffForm_apply_orderEmbOfFin (fun J ↦ u J y) hJ).symm) z hI).trans ?_
  rw [hua z (hmem.2 z.property) I hI, ha hI, ← hη₀]

/-- **The Dolbeault–Grothendieck lemma on polydiscs.** A smooth `∂bar`-closed form of type
`(p,q+1)` on a whole open polydisc in `ι → ℂ`, with coefficients in a complex Banach space, is
`∂bar` of a smooth form of type `(p,q)` on the same polydisc. -/
theorem IsOfType.exists_delBar_eq_of_polydisc {c : ι → ℂ} {r : ι → ℝ} {k p q : ℕ}
    {η : SmoothForm 𝓘(ℝ, ι → ℂ) (polydisc c r) F (k + 1)}
    (hη : η.IsOfType (ofComplexManifold (ι → ℂ) (polydisc c r)) p (q + 1))
    (hclosed : (ofComplexManifold (ι → ℂ) (polydisc c r)).delBar η = 0) :
    ∃ f : SmoothForm 𝓘(ℝ, ι → ℂ) (polydisc c r) F k,
      f.IsOfType (ofComplexManifold (ι → ℂ) (polydisc c r)) p q ∧
        (ofComplexManifold (ι → ℂ) (polydisc c r)).delBar f = η := by
  classical
  induction p generalizing k with
  | zero =>
    obtain rfl : k = q := by have := hη.add_eq; omega
    exact hη.exists_delBar_eq_of_polydisc_zero hclosed
  | succ p ih =>
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨p + q, by have := hη.add_eq; omega⟩
    -- The `(1,0)`-contractions of `η` with the coordinate vectors are closed of type
    -- `(p,q+1)`, so they are exact on the polydisc by the inductive hypothesis.
    choose β hβη hβ hβc using fun i : ι ↦ hη.exists_holCurry_eq_of_opens hclosed (Pi.single i 1)
    choose g hg hgβ using fun i ↦ ih (hβ i) (hβc i)
    -- The holomorphic coordinate one-forms, restricted to the polydisc.
    have hval := isPseudoholomorphic_ofComplexManifold_subtype_val (E := ι → ℂ) (polydisc c r)
    let w (i : ι) : SmoothForm 𝓘(ℝ, ι → ℂ) (polydisc c r) ℂ 1 :=
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (dz i)
    have hw (i : ι) : (w i).IsOfType (ofComplexManifold (ι → ℂ) (polydisc c r)) 1 0 :=
      (isOfType_dz i).mpullback contMDiff_subtypeVal hval
    have hwc (i : ι) : (ofComplexManifold (ι → ℂ) (polydisc c r)).delBar (w i) = 0 := by
      rw [← mpullback_delBar _ _ hval, delBar_dz, map_zero]
    obtain ⟨η₀, hη₀c, hη₀⟩ := η.isSmoothForm.exists_contDiffOn_opens
    obtain ⟨f, hf, hfη⟩ := exists_delBar_eventually_eq_of_sum_wedgeWith (η := η) (S := univ)
      (by have := hη.add_eq; omega) w hw hwc g hg (Eventually.of_forall fun z ↦ by
        -- The Euler identity at `z`, read off a smooth form on `ι → ℂ` agreeing with `η` near `z`.
        obtain ⟨G, hGt, hG⟩ := hη.exists_isOfType_eventuallyEq_of_opens hη₀ hη₀c z
        have hGz : G.val z = η.val z := hG.self_of_nhds.trans (hη₀ z).symm
        have hE (v : Fin (m + 1 + 1) → TangentSpace 𝓘(ℝ, ι → ℂ) (z : ι → ℂ)) :=
          congrArg (fun A ↦ A v) (sum_wedgeWith_dz_holInterior_apply hGt z)
        simp only [Submodule.coe_sum, Finset.sum_apply, ContinuousAlternatingMap.sum_apply,
          cast_apply, coe_wedgeWith, RoughForm.wedgeWith_apply', holInterior_val, hGz] at hE
        ext v
        simp only [Submodule.coe_sum, Finset.sum_apply, ContinuousAlternatingMap.sum_apply,
          cast_apply, coe_wedgeWith, RoughForm.wedgeWith_apply', hgβ, hβη, w,
          coe_mpullback_subtype_val_apply, ContinuousAlternatingMap.smul_apply]
        exact hE v)
    rw [nhdsSet_univ] at hfη
    exact ⟨f, hf, Subtype.ext (funext fun z ↦ eventually_top.1 hfη z)⟩

end Polydisc

end TauCeti.SmoothForm
