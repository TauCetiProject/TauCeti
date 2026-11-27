/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Opens.Basic
public import TauCeti.Analysis.Complex.Wirtinger.Forms
import TauCeti.Geometry.Manifold.DifferentialForm.Closed

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
`∂bar η(v,w) = ∂bar(η(w))(v) - ∂bar(η(v))(w)`, so the conjugate coordinate derivatives of the
coordinate evaluations of a Dolbeault-closed one-form on `ι → ℂ` are symmetric.

On `ι → ℂ` for a linearly ordered finite `ι`, the coefficients `SmoothForm.conjCoeff` of a form
are its values on increasing families of coordinate vectors. Those of `∂bar η` are obtained from
those of `η` by the coordinate operator `TauCeti.delBarCoeff` of the coordinate
Dolbeault–Grothendieck lemma (`SmoothForm.conjCoeff_delBar`). Forms of type `(0,k)`
correspond exactly to their families of smooth coefficients: they are determined by their
coefficients (`SmoothForm.IsOfType.ext_conjCoeff`), and every family of smooth coefficients is
that of the form `∑_J u_J d(conj z)_J` (`SmoothForm.exists_isOfType_conjCoeff_eq`).

## Main declarations

* `TauCeti.SmoothForm.dz`, `TauCeti.SmoothForm.isOfType_dz`, `TauCeti.SmoothForm.delBar_dz`:
  holomorphic coordinate one-forms on `ι → ℂ`.
* `TauCeti.SmoothForm.sum_wedgeWith_dz_apply`: the coordinate Euler identity.
* `TauCeti.SmoothForm.delBar_apply_eq_conjWirtingerDeriv`: `∂bar` of a function.
* `TauCeti.SmoothForm.IsOfType.apply_modelSpace`: the type equation of a form at a point.
* `TauCeti.SmoothForm.delBar_eq_alternatizeUncurryFin`: `∂bar` as alternation of the
  conjugate-linear derivative.
* `TauCeti.SmoothForm.delBar_apply`: evaluation of `∂bar` of an arbitrary smooth form.
* `TauCeti.SmoothForm.conjWirtingerDeriv_apply_single_eq`: the symmetry of conjugate
  coordinate derivatives of a Dolbeault-closed one-form.
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
    ((ofComplexManifold E E).delBar f).val z ![v] =
      conjWirtingerDeriv (fun y ↦ f.val y 0) z v := by
  have h := delBar_apply_apply (ofComplexManifold E E) f z v
  -- Identify the model-space tangent fibre and its identity comparison with `E`.
  simp only [ofComplexManifold_apply, mvfderiv_eq_fderiv] at h
  rw [conjWirtingerDeriv_apply]
  convert h using 1; rfl

/-- On a complex model space, the value at a point of a form of type `(p,q)` has type `(p,q)` for
multiplication by `i`. -/
theorem IsOfType.apply_modelSpace {k p q : ℕ} {φ : SmoothForm 𝓘(ℝ, E) E F k}
    (hφ : φ.IsOfType (ofComplexManifold E E) p q) (z : E) :
    (φ.val z : E [⋀^Fin k]→L[ℝ] F).IsOfType (I • ContinuousLinearMap.id ℝ E) p q := by
  have h := hφ.apply z
  rw [toEndomorphism_ofComplexManifold] at h
  -- The manifold tangent and coefficient fibres here are the underlying model spaces.
  convert h using 1

section ModelSpace

variable {k : ℕ}

/-- **The Dolbeault differential on a complex vector space.** On any smooth form, `∂bar` is
obtained by alternatizing the conjugate-linear part of the real derivative of its coefficient
field. No purity-of-type assumption is required. -/
theorem delBar_eq_alternatizeUncurryFin (η : SmoothForm 𝓘(ℝ, E) E F k) (z : E) :
    ((ofComplexManifold E E).delBar η).val z =
      ContinuousAlternatingMap.alternatizeUncurryFin (E := E) (F := F)
        (ContinuousLinearMap.complexAntilinearPartL
          (fderiv ℝ (η.val : E → E [⋀^Fin k]→L[ℝ] F) z)) := by
  rw [delBar_val_eq_mpullback_top]
  exact delBar_eq_alternatizeUncurryFin_of_opens _
    (fun y ↦ coe_mpullback_subtype_val_apply η y) ⟨z, mem_univ z⟩

/-- **Evaluation of `∂bar` on a complex vector space.** For an arbitrary smooth `k`-form `η`,
`∂bar η(v₀, …, v_k) = ∑ i, (-1)^i ∂bar(η(v₀, …, v_k without vᵢ))(vᵢ)`, using evaluations on
constant tangent vectors and the conjugate Wirtinger derivative. -/
theorem delBar_apply (η : SmoothForm 𝓘(ℝ, E) E F k) (z : E) (v : Fin (k + 1) → E) :
    ((ofComplexManifold E E).delBar η).val z v =
      ∑ i : Fin (k + 1), (-1 : ℂ) ^ (i : ℕ) •
        conjWirtingerDeriv (fun y ↦ η.val y (i.removeNth v)) z (v i) := by
  rw [delBar_eq_alternatizeUncurryFin]
  exact alternatizeUncurryFin_complexAntilinearPartL_fderiv_apply
    ((isSmoothForm_modelSpace_iff.1 η.isSmoothForm).differentiable (by simp) z) v

/-- On a smooth one-form the Dolbeault differential is the alternating conjugate Wirtinger
derivative of its evaluations on constant tangent vectors. -/
theorem delBar_apply_pair (η : SmoothForm 𝓘(ℝ, E) E F 1) (z v w : E) :
    ((ofComplexManifold E E).delBar η).val z ![v, w] =
      conjWirtingerDeriv (fun y ↦ η.val y ![w]) z v -
        conjWirtingerDeriv (fun y ↦ η.val y ![v]) z w := by
  have h0 : Fin.removeNth 0 ![v, w] = ![w] := by ext i; fin_cases i; rfl
  have h1 : Fin.removeNth 1 ![v, w] = ![v] := by ext i; fin_cases i; rfl
  -- Read the evaluated vectors in `E` rather than in its tangent-space synonym.
  change ((ofComplexManifold E E).delBar η).val z (![v, w] : Fin 2 → E) =
    conjWirtingerDeriv (fun y ↦ η.val y (![w] : Fin 1 → E)) z v -
      conjWirtingerDeriv (fun y ↦ η.val y (![v] : Fin 1 → E)) z w
  rw [delBar_apply η z ![v, w], Fin.sum_univ_two, h0, h1]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul,
    Matrix.cons_val_zero, Matrix.cons_val_one, sub_eq_add_neg]

end ModelSpace

open ContinuousAlternatingMap (holCurry)

section Coordinates

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- A Dolbeault-closed smooth one-form has symmetric conjugate coordinate derivatives. -/
theorem conjWirtingerDeriv_apply_single_eq
    (η : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F 1) {z : ι → ℂ}
    (hz : ((ofComplexManifold (ι → ℂ) (ι → ℂ)).delBar η).val z = 0) (i j : ι) :
    conjWirtingerDeriv (fun y ↦ η.val y ![Pi.single j 1]) z (Pi.single i 1) =
      conjWirtingerDeriv (fun y ↦ η.val y ![Pi.single i 1]) z (Pi.single j 1) := by
  apply sub_eq_zero.mp
  rw [← delBar_apply_pair η, hz]
  rfl

end Coordinates

section Coefficients

open Finset

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {k : ℕ}

/-- The value of a `k`-form `φ` on `ι → ℂ` on the coordinate vectors `e_j`, `j ∈ J`, in
increasing order; it vanishes unless `J` has `k` elements. When `φ` has type `(0,k)`, this is its
coefficient of `d(conj z)_J`, the wedge product of the `d(conj z_j)`, `j ∈ J`, in increasing
order: these are the coefficients consumed by the coordinate operator `TauCeti.delBarCoeff`. -/
def conjCoeff (φ : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F k) (J : Finset ι) (z : ι → ℂ) : F :=
  ContinuousAlternatingMap.conjCoeff (φ.val z : (ι → ℂ) [⋀^Fin k]→L[ℝ] F) J

/-- A coefficient indexed by a set with `k` elements is a value of the form. -/
theorem conjCoeff_of_card_eq (φ : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F k) {J : Finset ι}
    (h : #J = k) (z : ι → ℂ) :
    φ.conjCoeff J z = φ.val z fun a ↦ Pi.single (J.orderEmbOfFin h a) 1 := by
  exact ContinuousAlternatingMap.conjCoeff_of_card_eq _ h

/-- The coefficients indexed by sets without `k` elements vanish. -/
theorem conjCoeff_of_card_ne (φ : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F k) {J : Finset ι}
    (h : #J ≠ k) : φ.conjCoeff J = 0 :=
  funext fun _ ↦ ContinuousAlternatingMap.conjCoeff_of_card_ne _ h

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
  · rw [conjCoeff_of_card_eq _ hI, delBar_eq_alternatizeUncurryFin]
    exact (delBarCoeff_eq_alternatizeUncurryFin
      ((isSmoothForm_modelSpace_iff.1 η.isSmoothForm).differentiable (by simp) z)
      hI (fun _ _ ↦ Filter.EventuallyEq.rfl)).symm
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
    (h : ∀ J, #J = k → φ.conjCoeff J z = ψ.conjCoeff J z) : φ.val z = ψ.val z := by
  exact (hφ.apply_modelSpace z).eq_of_conjCoeff_eq (hψ.apply_modelSpace z) h

/-- Smooth forms of type `(0,k)` on `ι → ℂ` are determined by their coefficients. -/
theorem IsOfType.ext_conjCoeff {φ ψ : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F k}
    (hφ : φ.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) 0 k)
    (hψ : ψ.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) 0 k)
    (h : ∀ J, #J = k → φ.conjCoeff J = ψ.conjCoeff J) : φ = ψ :=
  Subtype.ext <| funext fun z ↦ hφ.apply_eq_of_conjCoeff_eq hψ fun J hJ ↦ congrFun (h J hJ) z

/-- Smooth coefficient functions on an open coordinate domain assemble into a smooth form
of type `(0,k)` with those coefficients. -/
theorem exists_isOfType_conjCoeff_eq_of_opens {U : TopologicalSpace.Opens (ι → ℂ)}
    {u : Finset ι → (ι → ℂ) → F}
    (hu : ∀ J, #J = k → ContDiffOn ℝ ∞ (u J) U) :
    ∃ φ : SmoothForm 𝓘(ℝ, ι → ℂ) U F k,
      φ.IsOfType (ofComplexManifold (ι → ℂ) U) 0 k ∧
        ∀ J (hJ : #J = k) (z : U),
          φ.val z (fun i ↦ Pi.single (J.orderEmbOfFin hJ i) 1) = u J z := by
  have hΦ : ContDiffOn ℝ ∞ (fun z ↦ conjCoeffForm k fun J ↦ u J z) U :=
    contDiffOn_conjCoeffForm hu
  let φ : SmoothForm 𝓘(ℝ, ι → ℂ) U F k :=
    ⟨_, ((isSmoothForm_opens_iff (fun _ ↦ rfl)).2 hΦ).mem_smoothBundleForms⟩
  refine ⟨φ, isOfType_iff_forall.2 ⟨zero_add k, fun z ↦ ?_⟩, fun J hJ z ↦ ?_⟩
  · rw [toEndomorphism_ofComplexManifold]
    exact isOfType_conjCoeffForm _
  · -- Tangent and coefficient fibres at `z` are definitionally the model spaces.
    exact conjCoeffForm_apply_orderEmbOfFin _ hJ

/-- **Forms with prescribed coefficients.** Smooth functions `u_J`, indexed by the sets `J` with
`k` elements, are the coefficients of a smooth form of type `(0,k)` on `ι → ℂ`, namely of
`∑_J u_J d(conj z)_J`. -/
theorem exists_isOfType_conjCoeff_eq {u : Finset ι → (ι → ℂ) → F}
    (hu : ∀ J, #J = k → ContDiff ℝ ∞ (u J)) :
    ∃ φ : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F k,
      φ.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) 0 k ∧ ∀ J, #J = k → φ.conjCoeff J = u J := by
  have hΦ : ContDiff ℝ ∞ fun z ↦ conjCoeffForm k fun J ↦ u J z :=
    contDiffOn_univ.1 (contDiffOn_conjCoeffForm fun J hJ ↦ (hu J hJ).contDiffOn)
  let φ : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F k :=
    ⟨_, (isSmoothForm_modelSpace_iff.mpr hΦ).mem_smoothBundleForms⟩
  refine ⟨φ, isOfType_iff_forall.2 ⟨zero_add k, fun z ↦ ?_⟩, fun J hJ ↦ funext fun z ↦ ?_⟩
  · rw [toEndomorphism_ofComplexManifold]
    exact isOfType_conjCoeffForm _
  · rw [conjCoeff_of_card_eq _ hJ]
    -- The value of `φ` at `z` is the assembled alternating map, read in the model fibres.
    exact conjCoeffForm_apply_orderEmbOfFin _ hJ

end Coefficients

open ContinuousAlternatingMap (holCurry)

section Coordinates

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The holomorphic coordinate one-form `dz_i` on `ι → ℂ`. -/
def dz (i : ι) : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) ℂ 1 :=
  SmoothForm.const (ContinuousAlternatingMap.ofSubsingleton ℝ (ι → ℂ) ℂ (0 : Fin 1)
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℂ) i))

omit [DecidableEq ι] in
/-- The value of the holomorphic coordinate one-form is the coordinate covector. -/
@[simp]
theorem dz_val (i : ι) (z : ι → ℂ) :
    ((dz i).val z : (ι → ℂ) [⋀^Fin 1]→L[ℝ] ℂ) = ContinuousAlternatingMap.ofSubsingleton ℝ (ι → ℂ)
      ℂ (0 : Fin 1) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℂ) i) := by
  ext v
  rw [dz, const_apply]
  -- `NormedSpace.fromTangentSpace` is the identity of the model space.
  rfl

omit [DecidableEq ι] in
/-- A holomorphic coordinate one-form has type `(1,0)`. -/
theorem isOfType_dz (i : ι) : (dz i).IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) 1 0 :=
  isOfType_one_zero_iff.2 fun z v ↦ by
    simp only [toEndomorphism_ofComplexManifold, dz_val]
    -- The tangent space at `z` is the model space `ι → ℂ`, where `I` acts coordinatewise.
    rfl

omit [DecidableEq ι] in
/-- Holomorphic coordinate one-forms have zero Dolbeault differential. -/
@[simp]
theorem delBar_dz (i : ι) : (ofComplexManifold (ι → ℂ) (ι → ℂ)).delBar (dz i) = 0 := by
  rw [(isOfType_dz i).delBar_eq, (isClosed_iff_mextDerivₗ_eq_zero (dz i)).1 (isClosed_const _),
    map_zero]

/-- The coordinate Euler identity at a point, for forms on any complex manifold modelled on
`ι → ℂ`, given the values of the coordinate covectors and holomorphic contractions there. -/
theorem sum_wedgeWith_dz_apply {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ι → ℂ) M] [IsManifold 𝓘(ℂ, ι → ℂ) ∞ M] {k p q : ℕ}
    {η : SmoothForm 𝓘(ℝ, ι → ℂ) M F (k + 1)}
    (hη : η.IsOfType (ofComplexManifold (ι → ℂ) M) p q)
    (w : ι → SmoothForm 𝓘(ℝ, ι → ℂ) M ℂ 1) {z : M}
    (hw : ∀ i, (w i).val z = ContinuousAlternatingMap.ofSubsingleton ℝ (ι → ℂ) ℂ
      (0 : Fin 1) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℂ) i))
    (β : ι → SmoothForm 𝓘(ℝ, ι → ℂ) M F k)
    (hβ : ∀ i, (β i).val z = holCurry (Pi.single i 1)
      (η.val z : (ι → ℂ) [⋀^Fin (k + 1)]→L[ℝ] F)) :
    (∑ i, LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm 𝓘(ℝ, ι → ℂ) M F n)
      (Nat.add_comm 1 k) (wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ) (w i) (β i))).val z =
        (2 * p : ℂ) • η.val z := by
  have h := hη.apply z
  rw [toEndomorphism_ofComplexManifold] at h
  ext v
  simp only [Submodule.coe_sum, Finset.sum_apply, ContinuousAlternatingMap.sum_apply,
    cast_apply, coe_wedgeWith, RoughForm.wedgeWith_apply', hw, hβ,
    ContinuousAlternatingMap.smul_apply]
  exact h.sum_wedgeWith_holCurry v

end Coordinates

end TauCeti.SmoothForm
