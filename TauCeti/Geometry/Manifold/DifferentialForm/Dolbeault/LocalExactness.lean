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
import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Opens.Contraction

/-!
# Local exactness for smooth forms of type `(p,q)`

A smooth form of type `(p,q+1)` on `ι → ℂ` whose Dolbeault differential vanishes on a finite
product of planar domains has a smooth primitive of type `(p,q)` near every compact subproduct.
Both the input and the primitive are smooth on all of `ι → ℂ`, with coefficients in a complex
Banach space; only closedness and the primitive equation are restricted to the indicated sets.

On a whole open polydisc `TauCeti.polydisc c r`, regarded as an open complex submanifold of
`ι → ℂ`, every smooth `∂bar`-closed form of type `(p,q+1)`, with coefficients in a complex
Banach space, is `∂bar` of a smooth form of type
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
(`SmoothForm.exists_isOfType_conjCoeff_eq`, `TauCeti.conjCoeffForm`).

The general case reduces to this one by induction on `p`. Applying the output-scaled contraction
`ι_v - I • ι_{I • v}`, lowers the type `(p+1,q)` to `(p,q)`
(`ContinuousAlternatingMap.IsOfType.curryLeftTopological_sub_I_smul`), and for a constant vector
`v` it anticommutes with `∂bar`. The contractions `η_j` of a closed form `η` of type
`(p+1,q+1)` with the coordinate vectors are therefore closed of type `(p,q+1)`, with primitives
`g_j`. The Euler identity `∑ j, dz_j ∧ η_j = 2 (p + 1) • η`
(`ContinuousAlternatingMap.IsOfType.alternatizeUncurryFin_curryLeft_sub_I_smul_comp`), the graded
Leibniz rule and `∂bar dz_j = 0` then show that `-(2 (p + 1))⁻¹ • ∑ j, dz_j ∧ g_j` is a primitive
of `η` of type `(p+1,q)`.

On the polydisc the type and Euler identities apply directly to each fibre value. Differential
identities are transported through smooth ambient germs, using that `∂bar` commutes with
restriction to open subsets because the inclusions are holomorphic.

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
    exact sum_wedgeWith_dz_apply hη dz (fun i ↦ dz_val i z) _
      (fun i ↦ (hz i).trans (holInterior_val _ _ _))

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

section Polydisc

open Metric TopologicalSpace
open scoped Finset

variable {ι : Type*} [Fintype ι]

variable [CompleteSpace F]

/-- A smooth closed `(0,q+1)`-form on a whole open polydisc, with complex Banach
coefficients, has a smooth `(0,q)`-primitive `f` on that same polydisc satisfying `∂bar f = η`. -/
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
    ContinuousAlternatingMap.conjCoeff (η₀ z) I
  have ha {I : Finset ι} (hI : #I = q + 1) (z : ι → ℂ) :
      a I z = η₀ z fun i ↦ Pi.single (I.orderEmbOfFin hI i) 1 := by
    exact ContinuousAlternatingMap.conjCoeff_of_card_eq _ hI
  have hmem {z : ι → ℂ} : z ∈ univ.pi (fun i ↦ ball (c i) (r i)) ↔ z ∈ polydisc c r := by
    rw [← SetLike.mem_coe, coe_polydisc]
  obtain ⟨u, hu, hua⟩ := exists_contDiffOn_delBarCoeff_eq_of_polydisc (f := a)
    (fun I hI ↦ by
      rw [funext (ha hI), ← coe_polydisc]
      exact (ContinuousAlternatingMap.apply ℝ (ι → ℂ) F _).contDiff.comp_contDiffOn hη₀c)
    fun z hz I hI ↦ by
      rw [← delBar_val_apply_orderEmbOfFin_of_opens hη₀ (fun J hJ y _ ↦ ha hJ y)
        ⟨z, hmem.1 hz⟩ hI, hclosed]
      -- The value of the zero form is zero.
      rfl
  obtain ⟨f, hf, hfval⟩ := exists_isOfType_conjCoeff_eq_of_opens
    (U := polydisc c r) (u := u) (fun J _ ↦ by rw [coe_polydisc]; exact hu J)
  refine ⟨f, hf, Subtype.ext (funext fun z ↦ ?_)⟩
  -- Both sides have type `(0,q+1)` at `z`, and their coefficients agree.
  have h₁ := hf.delBar.apply z
  have h₂ := hη.apply z
  rw [toEndomorphism_ofComplexManifold] at h₁ h₂
  -- The tangent and coefficient fibres at `z` are definitionally the model spaces;
  -- explicitly type both values so coefficient extensionality uses these identifications.
  let A : (ι → ℂ) [⋀^Fin (q + 1)]→L[ℝ] F :=
    ((ofComplexManifold (ι → ℂ) (polydisc c r)).delBar f).val z
  let B : (ι → ℂ) [⋀^Fin (q + 1)]→L[ℝ] F := η.val z
  refine ContinuousAlternatingMap.IsOfType.eq_of_conjCoeff_eq (φ := A) (ψ := B) h₁ h₂
    fun I hI ↦ ?_
  rw [ContinuousAlternatingMap.conjCoeff_of_card_eq _ hI,
    ContinuousAlternatingMap.conjCoeff_of_card_eq _ hI]
  obtain ⟨f₀, _, hf₀⟩ := f.isSmoothForm.exists_contDiffOn_opens
  refine (delBar_val_apply_orderEmbOfFin_of_opens (φ := f) hf₀ (a := u)
    (fun J hJ y hy ↦ by rw [← hf₀ ⟨y, hy⟩]; exact (hfval J hJ ⟨y, hy⟩).symm) z hI).trans ?_
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
    let β (i : ι) := holInteriorOpens (Pi.single i 1) η
    have hβc (i : ι) : (ofComplexManifold (ι → ℂ) (polydisc c r)).delBar (β i) = 0 := by
      dsimp only [β]
      rw [delBar_holInteriorOpens, hclosed]
      rw [map_zero, neg_zero]
    choose g hg hgβ using fun i ↦ ih (isOfType_holInteriorOpens hη (Pi.single i 1)) (hβc i)
    -- The holomorphic coordinate one-forms, restricted to the polydisc.
    have hval := isPseudoholomorphic_ofComplexManifold_subtype_val (E := ι → ℂ) (polydisc c r)
    let w (i : ι) : SmoothForm 𝓘(ℝ, ι → ℂ) (polydisc c r) ℂ 1 :=
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (dz i)
    have hw (i : ι) : (w i).IsOfType (ofComplexManifold (ι → ℂ) (polydisc c r)) 1 0 :=
      (isOfType_dz i).mpullback contMDiff_subtypeVal hval
    have hwc (i : ι) : (ofComplexManifold (ι → ℂ) (polydisc c r)).delBar (w i) = 0 := by
      rw [← mpullback_delBar _ _ hval, delBar_dz, map_zero]
    obtain ⟨f, hf, hfη⟩ := exists_delBar_eventually_eq_of_sum_wedgeWith (η := η) (S := univ)
      (by have := hη.add_eq; omega) w hw hwc g hg (Eventually.of_forall fun z ↦ by
        apply sum_wedgeWith_dz_apply hη w (fun i ↦ ?_) _ (fun i ↦ ?_)
        · -- The restricted coordinate covector at `z`, read in the model fibre at `(z : ι → ℂ)`.
          exact (coe_mpullback_subtype_val_apply (dz i) z).trans (dz_val i z)
        · exact congrArg (fun φ ↦ φ.val z) (hgβ i) |>.trans (holInteriorOpens_val _ _ _))
    rw [nhdsSet_univ] at hfη
    exact ⟨f, hf, Subtype.ext (funext fun z ↦ eventually_top.1 hfη z)⟩

end Polydisc

end TauCeti.SmoothForm
