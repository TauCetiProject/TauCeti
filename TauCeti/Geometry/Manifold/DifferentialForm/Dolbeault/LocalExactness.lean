/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.ComplexManifold
public import TauCeti.Analysis.Complex.Wirtinger.Polydisc
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Normed.Module.Alternating.Curry
import TauCeti.Analysis.Normed.Module.Alternating.Uncurry.AlmostComplexType
import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Uncurry
import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Leibniz
import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.ModelSpace

/-!
# Local exactness for smooth forms of type `(p,q)`

A smooth form of type `(p,q+1)` on `ι → ℂ` whose Dolbeault differential vanishes on a finite
product of planar domains has a smooth primitive of type `(p,q)` near every compact subproduct.
Both the input and the primitive are `SmoothForm`s, with coefficients in a complex Banach space.
Exactness is asserted near the compact product, and on polydiscs on every smaller concentric
polydisc, with no claim of exactness on the whole original domain.

## Main declarations

* `TauCeti.SmoothForm.IsOfType.exists_delBar_eventually_eq_of_pi`: local exactness of closed
  `(p,q+1)`-forms on products of planar domains.
* `TauCeti.SmoothForm.IsOfType.exists_delBar_eq_of_polydisc`: exactness of closed
  `(p,q+1)`-forms on a polydisc, on every smaller concentric polydisc.

## Implementation notes

For forms of type `(0,q+1)` the coefficients of the input are closed for the coordinate operator
`TauCeti.delBarCoeff` (`SmoothForm.conjCoeff_delBar`), the coordinate Dolbeault–Grothendieck lemma
solves for the coefficients of a primitive near the compact product, and these are extended
smoothly and assembled into a form (`SmoothForm.exists_isOfType_conjCoeff_eq`).

The general case reduces to this one by induction on `p`. Inserting `2 v^(1,0)`, that is applying
`ι_v - I • ι_{I • v}`, lowers the type `(p+1,q)` to `(p,q)`
(`ContinuousAlternatingMap.IsOfType.curryLeftTopological_sub_I_smul`), and for a constant vector
`v` it anticommutes with `∂bar`. The contractions `η_j` of a closed form `η` of type
`(p+1,q+1)` with the coordinate vectors are therefore closed of type `(p,q+1)`, with primitives
`g_j` near the compact product. The Euler identity `∑ j, dz_j ∧ η_j = 2 (p + 1) • η`
(`ContinuousAlternatingMap.IsOfType.alternatizeUncurryFin_curryLeft_sub_I_smul_comp`), the graded
Leibniz rule and `∂bar dz_j = 0` then show that `-(2 (p + 1))⁻¹ • ∑ j, dz_j ∧ g_j` is a primitive
of `η` of type `(p+1,q)`.

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

section Contraction

variable {k : ℕ}

/-- The interior products `φ ↦ ι_v φ - I • ι_{I • v} φ` with `2 v^(1,0)`, as a continuous
real-linear family in `v`. -/
private def holCurry : E →L[ℝ] (E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] E [⋀^Fin k]→L[ℝ] F :=
  (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
      (n := k)).toContinuousLinearMap.flip -
    I • (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
      (n := k)).toContinuousLinearMap.flip ∘L (I • ContinuousLinearMap.id ℝ E)

private theorem holCurry_apply (v : E) (φ : E [⋀^Fin (k + 1)]→L[ℝ] F) :
    holCurry v φ = φ.curryLeft v - I • φ.curryLeft (I • v) := by
  simp [holCurry]

private theorem holCurry_map_smul (v : E) (c : ℂ) (φ : E [⋀^Fin (k + 1)]→L[ℝ] F) :
    holCurry v (c • φ) = c • holCurry v φ := by
  ext w
  simp [holCurry_apply, smul_sub, smul_smul, mul_comm]

private theorem holCurry_smul (c : ℂ) (v : E) :
    holCurry (k := k) (F := F) (c • v) = c • holCurry v := by
  have hc : c • v = c.re • v + c.im • (I • v) := by
    rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, Complex.re_add_im]
  have hI : holCurry (k := k) (F := F) (I • v) = I • holCurry v := by
    ext φ w
    simp [holCurry_apply, smul_smul, smul_sub]
    abel
  rw [hc, map_add, map_smul, map_smul, hI]
  ext φ w
  simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply]
  rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, Complex.re_add_im]

/-- The interior product of a smooth form on a complex vector space with the constant vector
`2 v^(1,0)`, that is, `ι_v - I • ι_{I • v}`. -/
private def holInterior (v : E) (η : SmoothForm 𝓘(ℝ, E) E F (k + 1)) :
    SmoothForm 𝓘(ℝ, E) E F k :=
  ⟨fun z ↦ holCurry v (η.val z : E [⋀^Fin (k + 1)]→L[ℝ] F),
    (isSmoothForm_modelSpace_iff.mpr ((holCurry v).contDiff.comp
      (isSmoothForm_modelSpace_iff.1 η.isSmoothForm))).mem_smoothBundleForms⟩

private theorem holInterior_val (v : E) (η : SmoothForm 𝓘(ℝ, E) E F (k + 1)) (z : E) :
    (holInterior v η).val z = holCurry v (η.val z : E [⋀^Fin (k + 1)]→L[ℝ] F) :=
  (rfl)

/-- The `(1,0)`-contraction lowers the holomorphic degree. -/
private theorem isOfType_holInterior {p q : ℕ} {η : SmoothForm 𝓘(ℝ, E) E F (k + 1)}
    (hη : η.IsOfType (ofComplexManifold E E) (p + 1) q) (v : E) :
    (holInterior v η).IsOfType (ofComplexManifold E E) p q := by
  refine isOfType_iff_forall.2 ⟨by have := hη.add_eq; omega, fun z ↦ ?_⟩
  let φ : E [⋀^Fin (k + 1)]→L[ℝ] F := η.val z
  have hφ : φ.IsOfType (I • ContinuousLinearMap.id ℝ E) (p + 1) q := hη.apply_modelSpace z
  have h := hφ.curryLeftTopological_sub_I_smul (fun w ↦ by simp [smul_smul]) v
  simp only [smul_apply, ContinuousLinearMap.id_apply,
    ← ContinuousAlternatingMap.curryLeft_eq_curryLeftTopological, ← holCurry_apply] at h
  rw [toEndomorphism_ofComplexManifold]
  -- The value of the contraction at `z` is `holCurry v φ`, read in the tangent space at `z`.
  exact h

/-- The `(1,0)`-contraction with a constant vector anticommutes with `∂bar`. -/
private theorem delBar_holInterior (v : E) (η : SmoothForm 𝓘(ℝ, E) E F (k + 1)) :
    (ofComplexManifold E E).delBar (holInterior v η) =
      -holInterior v ((ofComplexManifold E E).delBar η) := by
  refine Subtype.ext (funext fun z ↦ ?_)
  let Θ : E → E [⋀^Fin (k + 1)]→L[ℝ] F := η.val
  let Jm : E →L[ℝ] E := I • ContinuousLinearMap.id ℝ E
  have hdz : DifferentiableAt ℝ Θ z :=
    (isSmoothForm_modelSpace_iff.1 η.isSmoothForm).differentiable (by simp) z
  set D := fderiv ℝ Θ z
  set L : E →L[ℝ] E [⋀^Fin (k + 1)]→L[ℝ] F := (2 : ℂ)⁻¹ • (D + I • D ∘L Jm) with hL
  -- The coefficient field of the contraction is `holCurry v ∘ Θ`.
  have hval : ((holInterior v η).val : E → E [⋀^Fin k]→L[ℝ] F) = holCurry v ∘ Θ := rfl
  have hfd : fderiv ℝ ((holInterior v η).val : E → E [⋀^Fin k]→L[ℝ] F) z = holCurry v ∘L D :=
    (congrArg (fderiv ℝ · z) hval).trans ((holCurry v).fderiv_comp_left hdz)
  -- The value of a negated form is the negated value, read in the model fibre.
  have hR : (-holInterior v ((ofComplexManifold E E).delBar η)).val z =
      -holCurry v (((ofComplexManifold E E).delBar η).val z : E [⋀^Fin (k + 2)]→L[ℝ] F) :=
    (rfl)
  -- `L` is the conjugate Wirtinger derivative of `Θ` at `z`, so it is conjugate-linear.
  have hLI : L (I • v) = -I • L v := by
    have hLw (u : E) : L u = conjWirtingerDeriv Θ z u := by
      simp [hL, Jm, conjWirtingerDeriv_apply, D]
    rw [hLw, hLw, map_smulₛₗ, conj_I]
  -- `∂bar` of the contraction is the alternation of `holCurry v ∘ L`.
  have hCL : (2 : ℂ)⁻¹ • (holCurry v ∘L D + I • (holCurry v ∘L D) ∘L Jm) = holCurry v ∘L L := by
    ext u : 1
    simp [hL, holCurry_map_smul]
  have hsplit : holCurry v ∘L L =
      (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
        (n := k)).toContinuousLinearMap.flip v ∘L L -
      I • (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
        (n := k)).toContinuousLinearMap.flip (I • v) ∘L L := by
    ext u : 1
    simp [holCurry_apply]
  have hcartan (y : E) := eq_sub_of_add_eq
    (ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft_comp_add_curryLeft L y)
  have hδ : (((ofComplexManifold E E).delBar η).val z : E [⋀^Fin (k + 2)]→L[ℝ] F) =
      ContinuousAlternatingMap.alternatizeUncurryFin L :=
    delBar_eq_alternatizeUncurryFin η z
  rw [hR, hδ, delBar_eq_alternatizeUncurryFin, hfd, hCL, hsplit,
    ContinuousAlternatingMap.alternatizeUncurryFin_sub,
    ContinuousAlternatingMap.alternatizeUncurryFin_smul, hcartan, hcartan, hLI, holCurry_apply]
  simp only [smul_sub, smul_smul, mul_neg, I_mul_I, _root_.neg_neg, one_smul]
  abel

end Contraction

section Coordinates

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The holomorphic coordinate one-form `dz_i` on `ι → ℂ`. -/
private def dz (i : ι) : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) ℂ 1 :=
  SmoothForm.const (ContinuousAlternatingMap.ofSubsingleton ℝ (ι → ℂ) ℂ (0 : Fin 1)
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℂ) i))

omit [DecidableEq ι] in
private theorem dz_val (i : ι) (z : ι → ℂ) :
    ((dz i).val z : (ι → ℂ) [⋀^Fin 1]→L[ℝ] ℂ) = ContinuousAlternatingMap.ofSubsingleton ℝ (ι → ℂ)
      ℂ (0 : Fin 1) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℂ) i) := by
  ext v
  rw [dz, const_apply]
  -- `NormedSpace.fromTangentSpace` is the identity of the model space.
  rfl

omit [DecidableEq ι] in
private theorem isOfType_dz (i : ι) : (dz i).IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) 1 0 := by
  refine isOfType_iff_forall.2 ⟨rfl, fun z ↦ ?_⟩
  have h : (ContinuousAlternatingMap.ofSubsingleton ℝ (ι → ℂ) ℂ (0 : Fin 1)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℂ) i)).IsOfType
        (I • ContinuousLinearMap.id ℝ (ι → ℂ)) 1 0 :=
    (ContinuousAlternatingMap.isOfType_one_zero_iff _).2 fun v ↦ by simp
  rw [toEndomorphism_ofComplexManifold, dz_val]
  -- The tangent space at `z` is the model space `ι → ℂ`.
  exact h

omit [DecidableEq ι] in
private theorem delBar_dz (i : ι) : (ofComplexManifold (ι → ℂ) (ι → ℂ)).delBar (dz i) = 0 := by
  have hd : mextDerivₗ 𝓘(ℝ, ι → ℂ) 1 (dz i) = 0 := Subtype.ext <| by
    rw [mextDerivₗ_apply, ZeroMemClass.coe_zero]
    exact (isClosed_def _).1 (isClosed_const _)
  rw [(isOfType_dz i).delBar_eq, hd, map_zero]

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
  let φ : (ι → ℂ) [⋀^Fin (k + 1)]→L[ℝ] F := η.val z
  -- The coordinate expansion of the contractions with the vectors `u`.
  have hsum : ∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℂ) i).smulRight
      (holCurry (Pi.single i 1) φ) = φ.curryLeft - I • φ.curryLeft ∘L
        (I • ContinuousLinearMap.id ℝ (ι → ℂ)) := by
    ext u : 1
    have hu := congrArg (fun w ↦ holCurry (k := k) (F := F) w φ) (pi_eq_sum_univ' u)
    simp only [map_sum, holCurry_smul, sum_apply] at hu
    simp [← holCurry_apply, hu]
  ext v
  simp only [Submodule.coe_sum, Finset.sum_apply, ContinuousAlternatingMap.sum_apply, cast_apply,
    coe_wedgeWith, RoughForm.wedgeWith_apply', hβ, dz_val, holInterior_val]
  refine (Finset.sum_congr rfl fun i _ ↦
    (ContinuousAlternatingMap.alternatizeUncurryFin_smulRight_apply (E := ι → ℂ)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℂ) i) (holCurry (Pi.single i 1) φ)
        v).symm).trans ?_
  have hfin : ∑ i, ContinuousAlternatingMap.alternatizeUncurryFin
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℂ) i).smulRight
        (holCurry (Pi.single i 1) φ)) = (2 * p : ℂ) • φ := by
    simp only [← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, ← map_sum, hsum]
    have hφ : φ.IsOfType (I • ContinuousLinearMap.id ℝ (ι → ℂ)) p q := hη.apply_modelSpace z
    exact hφ.alternatizeUncurryFin_curryLeft_sub_I_smul_comp
  -- Evaluate `hfin` at `v`, whose entries lie in the tangent space at `z`, that is, in `ι → ℂ`.
  exact (ContinuousAlternatingMap.sum_apply _ _).symm.trans (congrArg (fun A ↦ A v) hfin)

/-- **The inductive step.** If the `(1,0)`-contractions of a form `η` of type `(p+1,q+1)` with
the coordinate vectors have primitives `g_i` of type `(p,q)` near a set `S`, then
`-(2 (p + 1))⁻¹ • ∑ i, dz_i ∧ g_i` is a primitive of `η` of type `(p+1,q)` near `S`. -/
private theorem IsOfType.exists_delBar_eventually_eq_of_holInterior {m p q : ℕ}
    {η : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F (m + 1 + 1)}
    (hη : η.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) (p + 1) (q + 1)) {S : Set (ι → ℂ)}
    (g : ι → SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F m)
    (hg : ∀ i, (g i).IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) p q)
    (hgη : ∀ i, ∀ᶠ z in 𝓝ˢ S, ((ofComplexManifold (ι → ℂ) (ι → ℂ)).delBar (g i)).val z =
      (SmoothForm.holInterior (Pi.single i 1) η).val z) :
    ∃ f : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F (m + 1),
      f.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) (p + 1) q ∧ ∀ᶠ z in 𝓝ˢ S,
        ((ofComplexManifold (ι → ℂ) (ι → ℂ)).delBar f).val z = η.val z := by
  let μ : ℂ →L[ℝ] F →L[ℝ] F := ContinuousLinearMap.lsmul ℝ ℂ
  have hμ₁ (c : ℂ) (a : ℂ) (b : F) : μ (c • a) b = c • μ a b := by simp [μ, mul_smul]
  have hμ₂ (c : ℂ) (a : ℂ) (b : F) : μ a (c • b) = c • μ a b := by simp [μ, smul_comm a c]
  let c : ℂ := -(2 * ((p + 1 : ℕ) : ℂ))⁻¹
  have hdz (i : ι) := (isOfType_dz i).wedgeWith hμ₁ hμ₂ (hg i)
  rw [Nat.add_comm 1 p, Nat.zero_add] at hdz
  refine ⟨c • ∑ i, LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F n)
    (Nat.add_comm 1 m) (SmoothForm.wedgeWith μ (dz i) (g i)), ?_, ?_⟩
  · refine IsOfType.smul (Finset.sum_induction _
      (fun φ : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F (m + 1) ↦
        φ.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) (p + 1) q)
      (fun _ _ ha hb ↦ ha.add hb) (isOfType_zero_iff.2 (by have := hη.add_eq; omega))
      fun i _ ↦ (hdz i).cast _) c
  -- By the Leibniz rule and `∂bar dz_i = 0`, `∂bar` of the primitive is `-c • ∑ dz_i ∧ ∂bar g_i`.
  have hdf : (ofComplexManifold (ι → ℂ) (ι → ℂ)).delBar (c • ∑ i, LinearEquiv.cast (R := ℝ)
      (M := fun n ↦ SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F n) (Nat.add_comm 1 m)
        (SmoothForm.wedgeWith μ (dz i) (g i))) =
      (-c) • ∑ i, LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F n)
        (Nat.add_comm 1 (m + 1))
          (SmoothForm.wedgeWith μ (dz i) ((ofComplexManifold (ι → ℂ) (ι → ℂ)).delBar (g i))) := by
    simp only [map_smul, map_sum, delBar_cast, delBar_wedgeWith _ hμ₁ hμ₂, delBar_dz,
      map_zero, LinearMap.zero_apply, zero_add, cast_cast, pow_one]
    -- The sign `(-1) ^ 1` of the Leibniz rule acts through the coefficient action.
    have hneg (φ : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F (m + 1 + 1)) : (-1 : ℝ) • φ = -φ :=
      Subtype.ext ((smul_toRoughForm _ φ).trans (neg_one_smul ℝ _))
    simp only [hneg, Finset.sum_neg_distrib, smul_neg]
    exact (neg_smul c _).symm
  filter_upwards [eventually_all.2 hgη] with z hz
  have hc : -c * (2 * ((p + 1 : ℕ) : ℂ)) = 1 := by
    rw [_root_.neg_neg]
    exact inv_mul_cancel₀ (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.2 p.succ_ne_zero))
  rw [hdf, smul_toRoughForm, Pi.smul_apply, sum_wedgeWith_dz_apply hη _ hz, smul_smul, hc,
    one_smul]

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
/-- **The Dolbeault–Grothendieck lemma for `(p,q)`-forms on product domains.** A smooth form `η`
of type `(p,q+1)` on `ι → ℂ`, with coefficients in a complex Banach space, whose Dolbeault
differential vanishes on a product `∏ U_i` of open subsets of `ℂ`, is Dolbeault-exact near every
compact subproduct `∏ K_i`, `K_i ⊆ U_i`: some smooth form `f` of type `(p,q)` satisfies
`∂bar f = η` there. -/
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
    exact hη.exists_delBar_eventually_eq_of_holInterior g hg hgη

omit [DecidableEq ι] in
/-- **The Dolbeault–Grothendieck lemma for `(p,q)`-forms on polydiscs.** A smooth form `η` of
type `(p,q+1)` on `ι → ℂ`, with coefficients in a complex Banach space, whose Dolbeault
differential vanishes on the polydisc `∏ B(c_i, r_i)`, is Dolbeault-exact on every concentric
polydisc `∏ B(c_i, r'_i)` with `r'_i < r_i`: some smooth form `f` of type `(p,q)` satisfies
`∂bar f = η` there. -/
theorem IsOfType.exists_delBar_eq_of_polydisc {k p q : ℕ}
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

end TauCeti.SmoothForm
