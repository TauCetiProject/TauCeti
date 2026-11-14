/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.ComplexManifold
public import TauCeti.Analysis.Complex.Wirtinger.Forms
import TauCeti.Analysis.Calculus.FDeriv.AlmostComplexType
import TauCeti.Data.Finset.Sort

/-!
# Dolbeault differentiation on a complex vector space

On a complex vector space, the Dolbeault differential of a smooth function is its conjugate
Wirtinger derivative. On an arbitrary smooth `k`-form `η` it is the alternating sum
`∂bar η(v₀, …, v_k) = ∑ i, (-1)^i ∂bar(η(v₀, …, v_k without vᵢ))(vᵢ)` of the conjugate
Wirtinger derivatives of its evaluations on constant vectors. For a form of pure type `(p,q)`,
the real derivative splits into complex-linear and conjugate-linear parts; alternatizing them
gives the components of `dη` of types `(p+1,q)` and `(p,q+1)`. Additivity and the type
decomposition give the same formula without a type hypothesis. This allows the coordinate
calculus to be applied to mixed types as well as purely antiholomorphic forms. In degree one,
`∂bar η(v,w) = ∂bar(η(w))(v) - ∂bar(η(v))(w)`.

On `ι → ℂ` for a linearly ordered finite `ι`, the coefficients `SmoothForm.conjCoeff` of a form
are its values on increasing families of coordinate vectors. Those of `∂bar η` are obtained from
those of `η` by the coordinate operator `TauCeti.delBarCoeff` of the coordinate
Dolbeault–Grothendieck lemma (`SmoothForm.conjCoeff_delBar`). Forms of type `(0,k)`
correspond exactly to their families of smooth coefficients: they are determined by their
coefficients (`SmoothForm.IsOfType.ext_conjCoeff`), and every family of smooth coefficients is
that of the form `∑_J u_J d(conj z)_J` (`SmoothForm.exists_isOfType_conjCoeff_eq`).

## Main declarations

* `TauCeti.SmoothForm.delBar_apply_eq_conjWirtingerDeriv`: `∂bar` of a function.
* `TauCeti.SmoothForm.IsOfType.apply_modelSpace`: the type equation of a form at a point.
* `TauCeti.SmoothForm.delBar_eq_alternatizeUncurryFin`: `∂bar` as alternation of the
  conjugate-linear derivative.
* `TauCeti.SmoothForm.delBar_apply`: evaluation of `∂bar` of an arbitrary smooth form.
* `TauCeti.SmoothForm.conjCoeff`: the coefficients of a form on `ι → ℂ`.
* `TauCeti.SmoothForm.conjCoeff_delBar`: coordinate evaluation intertwines `∂bar` with
  `TauCeti.delBarCoeff`.
* `TauCeti.SmoothForm.IsOfType.apply_eq_of_conjCoeff_eq`,
  `TauCeti.SmoothForm.IsOfType.ext_conjCoeff`: `(0,k)`-forms are determined by their
  coefficients.
* `TauCeti.SmoothForm.exists_isOfType_conjCoeff_eq`: `(0,k)`-forms with prescribed smooth
  coefficients.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Section 2.1.
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

/-- On a complex model space the Dolbeault differential of a smooth zero-form is the conjugate
Wirtinger derivative of its value function. -/
theorem delBar_apply_eq_conjWirtingerDeriv (f : SmoothForm 𝓘(ℝ, E) E F 0) (z v : E) :
    ((ofComplexManifold E E).delBar f).1 z ![v] =
      conjWirtingerDeriv (fun y ↦ f.1 y 0) z v := by
  have h := delBar_apply_apply (ofComplexManifold E E) f z v
  -- Identify the model-space tangent fibre and its identity comparison with `E`.
  simp only [ofComplexManifold_apply, mvfderiv_eq_fderiv] at h
  rw [conjWirtingerDeriv_apply]
  convert h using 1; rfl

/-- On a complex model space, the value at a point of a form of type `(p,q)` has type `(p,q)` for
multiplication by `i`. -/
theorem IsOfType.apply_modelSpace {k p q : ℕ} {φ : SmoothForm 𝓘(ℝ, E) E F k}
    (hφ : φ.IsOfType (ofComplexManifold E E) p q) (z : E) :
    (φ.1 z : E [⋀^Fin k]→L[ℝ] F).IsOfType (I • ContinuousLinearMap.id ℝ E) p q := by
  have h := hφ.apply z
  rw [toEndomorphism_ofComplexManifold] at h
  -- The manifold tangent and coefficient fibres here are the underlying model spaces.
  convert h using 1

section ModelSpace

variable {k : ℕ}

/-- On a form of pure type, `∂bar` is the alternation of the conjugate-linear part of the
real derivative of its coefficient field. -/
private theorem delBar_eq_alternatizeUncurryFin_of_isOfType {p q : ℕ}
    {η : SmoothForm 𝓘(ℝ, E) E F k} (hη : η.IsOfType (ofComplexManifold E E) p q) (z : E) :
    ((ofComplexManifold E E).delBar η).1 z =
      ContinuousAlternatingMap.alternatizeUncurryFin (E := E) (F := F) ((2 : ℂ)⁻¹ •
        (fderiv ℝ (η.1 : E → E [⋀^Fin k]→L[ℝ] F) z +
          I • (fderiv ℝ (η.1 : E → E [⋀^Fin k]→L[ℝ] F) z) ∘L
            (I • ContinuousLinearMap.id ℝ E))) := by
  let Θ : E → E [⋀^Fin k]→L[ℝ] F := η.1
  let Jm : E →L[ℝ] E := I • ContinuousLinearMap.id ℝ E
  let L : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F := fderiv ℝ Θ z
  have hJm (w : E) : Jm (Jm w) = -w := by simp [Jm, smul_smul]
  -- The derivative of a family of forms of type `(p,q)` still has that type.
  have htype (w : E) : (L w).IsOfType Jm p q := by
    simpa only [fderivWithin_univ] using ContinuousAlternatingMap.isOfType_fderivWithin (Θ := Θ)
      (J := Jm) uniqueDiffWithinAt_univ (mem_univ z) (Eventually.of_forall hη.apply_modelSpace) w
  have hflat : (mextDerivₗ 𝓘(ℝ, E) k η).1 z = extDeriv Θ z := by
    have h := mextDeriv_eq_extDeriv η.1 z
    rw [← mextDerivₗ_apply] at h
    -- Only the model tangent and trivial coefficient fibres differ in this comparison.
    convert h using 1
  -- `∂bar η` is the alternation of the conjugate-linear part of the derivative of `Θ`.
  have hδ : ((ofComplexManifold E E).delBar η).1 z =
      ContinuousAlternatingMap.alternatizeUncurryFin ((2 : ℂ)⁻¹ • (L + I • L ∘L Jm)) := by
    rw [hη.delBar_eq, coe_typeProjection]
    refine (congrArg (fun A : E →L[ℝ] E ↦ A.typeProjection p (q + 1)
      ((mextDerivₗ 𝓘(ℝ, E) k η).1 z)) (toEndomorphism_ofComplexManifold (E := E) z)).trans ?_
    rw [hflat]
    exact ContinuousAlternatingMap.typeProjection_alternatizeUncurryFin_succ_right hJm htype
  exact hδ

/-- **The Dolbeault differential on a complex vector space.** On any smooth form, `∂bar` is
obtained by alternatizing the conjugate-linear part of the real derivative of its coefficient
field. No purity-of-type assumption is required. -/
theorem delBar_eq_alternatizeUncurryFin (η : SmoothForm 𝓘(ℝ, E) E F k) (z : E) :
    ((ofComplexManifold E E).delBar η).1 z =
      ContinuousAlternatingMap.alternatizeUncurryFin (E := E) (F := F) ((2 : ℂ)⁻¹ •
        (fderiv ℝ (η.1 : E → E [⋀^Fin k]→L[ℝ] F) z +
          I • (fderiv ℝ (η.1 : E → E [⋀^Fin k]→L[ℝ] F) z) ∘L
            (I • ContinuousLinearMap.id ℝ E))) := by
  let field : SmoothForm 𝓘(ℝ, E) E F k → E → E [⋀^Fin k]→L[ℝ] F := fun φ y ↦ φ.1 y
  let C (Φ : E → E [⋀^Fin k]→L[ℝ] F) :=
    ContinuousAlternatingMap.alternatizeUncurryFin ((2 : ℂ)⁻¹ •
      (fderiv ℝ Φ z + I • (fderiv ℝ Φ z) ∘L (I • ContinuousLinearMap.id ℝ E)))
  let A : SmoothForm 𝓘(ℝ, E) E F k →+ E [⋀^Fin (k + 1)]→L[ℝ] F :=
    { toFun φ := ((ofComplexManifold E E).delBar φ).1 z
      map_zero' := by simp; rfl
      map_add' φ ψ := by simp; rfl }
  let B : SmoothForm 𝓘(ℝ, E) E F k →+ E [⋀^Fin (k + 1)]→L[ℝ] F :=
    { toFun φ := C (field φ)
      map_zero' := by
        have hzero : field 0 = fun _ ↦ 0 := rfl
        simp only [hzero, C, fderiv_const_apply, ContinuousLinearMap.zero_comp, smul_zero, add_zero]
        exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F)
      map_add' φ ψ := by
        have hφ : DifferentiableAt ℝ (field φ) z :=
          (isSmoothForm_modelSpace_iff.1 φ.isSmoothForm).differentiable (by simp) z
        have hψ : DifferentiableAt ℝ (field ψ) z :=
          (isSmoothForm_modelSpace_iff.1 ψ.isSmoothForm).differentiable (by simp) z
        have hadd : field (φ + ψ) = field φ + field ψ := rfl
        simp only [hadd, C, fderiv_add hφ hψ, ContinuousLinearMap.add_comp, smul_add,
          ContinuousAlternatingMap.alternatizeUncurryFin_add]
        abel }
  exact (ofComplexManifold E E).map_eq_of_forall_isOfType (f := A) (g := B)
    (fun _ _ _ _ hφ ↦ delBar_eq_alternatizeUncurryFin_of_isOfType hφ z) η

/-- **Evaluation of `∂bar` on a complex vector space.** For an arbitrary smooth `k`-form `η`,
`∂bar η(v₀, …, v_k) = ∑ i, (-1)^i ∂bar(η(v₀, …, v_k without vᵢ))(vᵢ)`, using evaluations on
constant tangent vectors and the conjugate Wirtinger derivative. -/
theorem delBar_apply (η : SmoothForm 𝓘(ℝ, E) E F k) (z : E) (v : Fin (k + 1) → E) :
    ((ofComplexManifold E E).delBar η).1 z v =
      ∑ i : Fin (k + 1), (-1 : ℂ) ^ (i : ℕ) •
        conjWirtingerDeriv (fun y ↦ η.1 y (i.removeNth v)) z (v i) := by
  let Θ : E → E [⋀^Fin k]→L[ℝ] F := η.1
  have hdz : DifferentiableAt ℝ Θ z :=
    (isSmoothForm_modelSpace_iff.1 η.isSmoothForm).differentiable (by simp) z
  rw [delBar_eq_alternatizeUncurryFin]
  -- Evaluate in the model fibre `E`; the tangent-space synonym prevents rewriting otherwise.
  change (ContinuousAlternatingMap.alternatizeUncurryFin ((2 : ℂ)⁻¹ •
    (fderiv ℝ Θ z + I • (fderiv ℝ Θ z) ∘L (I • ContinuousLinearMap.id ℝ E))) :
      E [⋀^Fin (k + 1)]→L[ℝ] F) v =
    ∑ i : Fin (k + 1), (-1 : ℂ) ^ (i : ℕ) •
      conjWirtingerDeriv (fun y ↦ Θ y (i.removeNth v)) z (v i)
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [conjWirtingerDeriv_apply, fderiv_continuousAlternatingMap_apply_const_apply hdz,
    fderiv_continuousAlternatingMap_apply_const_apply hdz]
  simp only [smul_apply, _root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]
  norm_cast

/-- On a smooth one-form the Dolbeault differential is the alternating conjugate Wirtinger
derivative of its evaluations on constant tangent vectors. -/
theorem delBar_apply_pair (η : SmoothForm 𝓘(ℝ, E) E F 1) (z v w : E) :
    ((ofComplexManifold E E).delBar η).1 z ![v, w] =
      conjWirtingerDeriv (fun y ↦ η.1 y ![w]) z v -
        conjWirtingerDeriv (fun y ↦ η.1 y ![v]) z w := by
  have h0 : Fin.removeNth 0 ![v, w] = ![w] := by ext i; fin_cases i; rfl
  have h1 : Fin.removeNth 1 ![v, w] = ![v] := by ext i; fin_cases i; rfl
  -- Read the evaluated vectors in `E` rather than in its tangent-space synonym.
  change ((ofComplexManifold E E).delBar η).1 z (![v, w] : Fin 2 → E) =
    conjWirtingerDeriv (fun y ↦ η.1 y (![w] : Fin 1 → E)) z v -
      conjWirtingerDeriv (fun y ↦ η.1 y (![v] : Fin 1 → E)) z w
  rw [delBar_apply η z ![v, w], Fin.sum_univ_two, h0, h1]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul,
    Matrix.cons_val_zero, Matrix.cons_val_one, sub_eq_add_neg]

end ModelSpace

section Coefficients

open Finset

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {k : ℕ}

/-- The value of a `k`-form `φ` on `ι → ℂ` on the coordinate vectors `e_j`, `j ∈ J`, in
increasing order; it vanishes unless `J` has `k` elements. When `φ` has type `(0,k)`, this is its
coefficient of `d(conj z)_J`, the wedge product of the `d(conj z_j)`, `j ∈ J`, in increasing
order: these are the coefficients consumed by the coordinate operator `TauCeti.delBarCoeff`. -/
def conjCoeff (φ : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F k) (J : Finset ι) (z : ι → ℂ) : F :=
  if h : #J = k then φ.1 z fun a ↦ Pi.single (J.orderEmbOfFin h a) 1 else 0

/-- A coefficient indexed by a set with `k` elements is a value of the form. -/
theorem conjCoeff_of_card_eq (φ : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F k) {J : Finset ι}
    (h : #J = k) (z : ι → ℂ) :
    φ.conjCoeff J z = φ.1 z fun a ↦ Pi.single (J.orderEmbOfFin h a) 1 := by
  simp [conjCoeff, h]

/-- The coefficients indexed by sets without `k` elements vanish. -/
theorem conjCoeff_of_card_ne (φ : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F k) {J : Finset ι}
    (h : #J ≠ k) : φ.conjCoeff J = 0 :=
  funext fun _ ↦ by simp [conjCoeff, h]

/-- The coefficients of a smooth form are smooth. -/
theorem contDiff_conjCoeff (φ : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F k) (J : Finset ι) :
    ContDiff ℝ ∞ (φ.conjCoeff J) := by
  by_cases h : #J = k
  · rw [show φ.conjCoeff J = _ from funext (φ.conjCoeff_of_card_eq h)]
    exact (ContinuousAlternatingMap.apply ℝ (ι → ℂ) F _).contDiff.comp
      (isSmoothForm_modelSpace_iff.1 φ.isSmoothForm)
  · rw [φ.conjCoeff_of_card_ne h]
    exact contDiff_const

/-- Coordinate evaluation intertwines the Dolbeault differential of an arbitrary smooth form
with `TauCeti.delBarCoeff`. For forms of type `(0,q)` these evaluations are the coefficients in
the antiholomorphic coordinate coframe. -/
theorem conjCoeff_delBar {q : ℕ} (η : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F q) :
    ((ofComplexManifold (ι → ℂ) (ι → ℂ)).delBar η).conjCoeff = delBarCoeff η.conjCoeff := by
  ext I z
  by_cases hI : #I = q + 1
  · let e := I.orderEmbOfFin hI
    rw [conjCoeff_of_card_eq _ hI, delBar_apply, delBarCoeff_def]
    conv_rhs => rw [← Finset.sum_coe_sort I, ← (I.orderIsoOfFin hI).toEquiv.sum_comp]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have hcard : #(I.erase (e a)) = q := by
      rw [card_erase_of_mem (I.orderEmbOfFin_mem hI a), hI, Nat.add_sub_cancel]
    -- Removing the `a`-th coordinate vector leaves the increasing enumeration of `I \ {e a}`.
    have herase := removeNth_orderEmbOfFin_symm_eq (e a) I (I.orderEmbOfFin_mem hI a) hI hcard
    rw [show (⟨e a, _⟩ : I) = I.orderIsoOfFin hI a from
      Subtype.ext (coe_orderIsoOfFin_apply ..).symm, OrderIso.symm_apply_apply] at herase
    have hcoeff : η.conjCoeff (I.erase (e a)) =
        fun y ↦ η.1 y (a.removeNth fun b ↦ (Pi.single (e b) 1 : ι → ℂ)) := by
      funext y
      rw [conjCoeff_of_card_eq _ hcard, ← herase]
      exact congrArg _ (funext fun b ↦
        (Fin.removeNth_apply a (fun b ↦ (Pi.single (e b) 1 : ι → ℂ)) b).symm)
    rw [RelIso.coe_fn_toEquiv, coe_orderIsoOfFin_apply, card_filter_lt_orderEmbOfFin, hcoeff]
  · rw [conjCoeff_of_card_ne _ hI, Pi.zero_apply, delBarCoeff_def]
    refine (Finset.sum_eq_zero fun j hj ↦ ?_).symm
    have hcard : #(I.erase j) ≠ q := by
      rw [card_erase_of_mem hj]
      have := Finset.card_pos.2 ⟨j, hj⟩
      omega
    rw [η.conjCoeff_of_card_ne hcard, conjWirtingerDeriv_apply]
    simp

/-- Two smooth forms of type `(0,k)` on `ι → ℂ` agree at a point where all their coefficients
agree. -/
theorem IsOfType.apply_eq_of_conjCoeff_eq {φ ψ : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F k}
    (hφ : φ.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) 0 k)
    (hψ : ψ.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) 0 k) {z : ι → ℂ}
    (h : ∀ J, #J = k → φ.conjCoeff J z = ψ.conjCoeff J z) : φ.1 z = ψ.1 z := by
  -- The tangent and coefficient fibres at `z` are the model spaces `ι → ℂ` and `F`.
  let A : (ι → ℂ) [⋀^Fin k]→L[ℝ] F := φ.1 z
  let B : (ι → ℂ) [⋀^Fin k]→L[ℝ] F := ψ.1 z
  suffices A - B = 0 from sub_eq_zero.1 this
  refine ((hφ.apply_modelSpace z).sub (hψ.apply_modelSpace z)).eq_zero_of_forall_apply_orderEmbOfFin
    fun J hJ ↦ ?_
  refine (ContinuousAlternatingMap.sub_apply A B _).trans (sub_eq_zero.2 ?_)
  exact (φ.conjCoeff_of_card_eq hJ z).symm.trans ((h J hJ).trans (ψ.conjCoeff_of_card_eq hJ z))

/-- Smooth forms of type `(0,k)` on `ι → ℂ` are determined by their coefficients. -/
theorem IsOfType.ext_conjCoeff {φ ψ : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F k}
    (hφ : φ.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) 0 k)
    (hψ : ψ.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) 0 k)
    (h : ∀ J, #J = k → φ.conjCoeff J = ψ.conjCoeff J) : φ = ψ :=
  Subtype.ext <| funext fun z ↦ hφ.apply_eq_of_conjCoeff_eq hψ fun J hJ ↦ congrFun (h J hJ) z

/-- **Forms with prescribed coefficients.** Smooth functions `u_J`, indexed by the sets `J` with
`k` elements, are the coefficients of a smooth form of type `(0,k)` on `ι → ℂ`, namely of
`∑_J u_J d(conj z)_J`. -/
theorem exists_isOfType_conjCoeff_eq {u : Finset ι → (ι → ℂ) → F}
    (hu : ∀ J, #J = k → ContDiff ℝ ∞ (u J)) :
    ∃ φ : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F k,
      φ.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) 0 k ∧ ∀ J, #J = k → φ.conjCoeff J = u J := by
  classical
  -- `β J f` is the form `f d(conj z)_J` when `J` has `k` elements, and `0` otherwise.
  let L : F →L[ℝ] ℂ →L[ℝ] F := (ContinuousLinearMap.lsmul ℝ ℂ).flip
  let β (J : Finset ι) (f : F) : (ι → ℂ) [⋀^Fin k]→L[ℝ] F :=
    if h : #J = k then (L f).compContinuousAlternatingMap
      (ContinuousAlternatingMap.conjCoordForm (J.orderEmbOfFin h)) else 0
  let Φ : (ι → ℂ) → (ι → ℂ) [⋀^Fin k]→L[ℝ] F := fun z ↦ ∑ J, β J (u J z)
  have hΦ : ContDiff ℝ ∞ Φ := by
    refine ContDiff.sum fun J _ ↦ ?_
    by_cases h : #J = k
    · simp only [β, h, ↓reduceDIte]
      exact ((ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ (ι → ℂ) ℂ F (Fin k) ∘L
        L).contDiff.comp (hu J h)).clm_apply contDiff_const
    · simp only [β, h, ↓reduceDIte]
      exact contDiff_const
  let φ : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F k :=
    ⟨Φ, (isSmoothForm_modelSpace_iff.mpr hΦ).mem_smoothBundleForms⟩
  refine ⟨φ, isOfType_iff_forall.2 ⟨zero_add k, fun z ↦ ?_⟩, fun J hJ ↦ funext fun z ↦ ?_⟩
  · rw [toEndomorphism_ofComplexManifold]
    refine ContinuousAlternatingMap.IsOfType.sum (zero_add k) fun J _ ↦ ?_
    by_cases h : #J = k
    · simp only [β, h, ↓reduceDIte]
      exact (ContinuousAlternatingMap.isOfType_conjCoordForm _).compContinuousAlternatingMap
        fun c x ↦ by simp [L, smul_smul]
    · simp only [β, h, ↓reduceDIte]
      exact ContinuousAlternatingMap.isOfType_zero_iff.2 (zero_add k)
  · rw [conjCoeff_of_card_eq _ hJ]
    -- The value of `φ` at `z` is `Φ z`, a form with coefficients in `F` on the model space.
    change (∑ K, β K (u K z)) (fun a ↦ Pi.single (J.orderEmbOfFin hJ a) 1) = u J z
    rw [ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single J]
    · simp [β, hJ, L, ContinuousAlternatingMap.conjCoordForm_apply_single_self
        (J.orderEmbOfFin hJ).injective]
    · intro K _ hKJ
      by_cases hK : #K = k
      · -- Some element of `J` lies outside `K`, so `d(conj z)_K` vanishes on the coordinate
        -- vectors indexed by `J`.
        obtain ⟨x, hxJ, hxK⟩ := Finset.not_subset.1 fun hJK ↦
          hKJ (Finset.eq_of_subset_of_card_le hJK (hK.trans hJ.symm).le).symm
        obtain ⟨a, rfl⟩ : x ∈ Set.range (J.orderEmbOfFin hJ) := by
          rwa [Finset.range_orderEmbOfFin]
        have h₀ := ContinuousAlternatingMap.conjCoordForm_apply_single_eq_zero
          (K.orderEmbOfFin hK) (f := J.orderEmbOfFin hJ) (a := a)
          (by rwa [Finset.range_orderEmbOfFin])
        simp [β, hK, L, h₀]
      · simp [β, hK]
    · simp

end Coefficients

end TauCeti.SmoothForm
