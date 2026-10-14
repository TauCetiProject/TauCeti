/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Liouville

/-!
# Fibrewise negation and magnetic translation of a linear cotangent space

On the normed linear cotangent space `V × V'` (with `V'` the continuous dual), with Liouville form
`λ_(q,p)(δq, δp) = p(δq)` and canonical symplectic form `ω = -dλ`
(`TauCeti.strongDualCotangentSymplecticForm`), this file records how two fibrewise maps act on
these forms. They are the linear models of the maps that compare sign conventions for cotangent
bundles and that remove an exact magnetic term.

* The **fibrewise negation** `ν(q, p) = (q, -p)` (`TauCeti.cotangentFiberNeg`) covers the
  identity of `V`, satisfies `ν^*λ = -λ` and reverses `ω`. It therefore identifies the cotangent
  space with the symplectic form `dλ = -ω` of the opposite sign convention with the cotangent
  space with `ω`, and it carries the Liouville primitive `λ` of `dλ` to the primitive `-λ` of `ω`.
  Its Liouville vector field is the radial field `Z(q, p) = (0, p)`, that is `p ∂_p`
  (`TauCeti.cotangentLiouvilleField`): `ι_Z ω = -λ`.
* The **magnetic translation** `Ψ_σ(q, p) = (q, p - σ_q)` by a one-form `σ` on `V`
  (`TauCeti.cotangentFiberTranslate`) also covers the identity of `V`. It satisfies
  `Ψ_σ^*λ = λ - π^*σ` and `Ψ_σ^*ω = ω + π^*dσ`, where `π` is the projection to `V`. So it is a
  symplectomorphism from the magnetic form `ω + π^*dσ` to `ω`, and for a closed `σ` it preserves
  `ω`. The two statements need `σ` to be differentiable only at the base point, and the second is
  proved by direct computation, without the second derivative of `σ`.

Conjugating a magnetic translation by `ν` changes the sign of the one-form
(`TauCeti.cotangentFiberNeg_cotangentFiberTranslate_cotangentFiberNeg`).

## Main declarations

* `TauCeti.cotangentFiberNeg`, with `TauCeti.cotangentLiouvilleForm_cotangentFiberNeg` and
  `TauCeti.strongDualCotangentSymplecticForm_cotangentFiberNeg`.
* `TauCeti.cotangentLiouvilleField`, with
  `TauCeti.strongDualCotangentSymplecticForm_cotangentLiouvilleField`.
* `TauCeti.cotangentFiberTranslate`, with its derivative `TauCeti.fderiv_cotangentFiberTranslate`,
  `TauCeti.cotangentLiouvilleForm_cotangentFiberTranslate` (`Ψ_σ^*λ = λ - π^*σ`) and
  `TauCeti.strongDualCotangentSymplecticForm_fderiv_cotangentFiberTranslate`
  (`Ψ_σ^*ω = ω + π^*dσ`).

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2 (cotangent bundles and the Liouville form).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953: the sign conventions for cotangent
  bundles and the magnetic cotangent bundles of Corollary D.
-/

public section

open ContinuousAlternatingMap

noncomputable section

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Fibrewise negation -/

/-- The **fibrewise negation** `(q, p) ↦ (q, -p)` of the linear cotangent space. -/
def cotangentFiberNeg : (V × StrongDual ℝ V) ≃L[ℝ] (V × StrongDual ℝ V) :=
  (ContinuousLinearEquiv.refl ℝ V).prodCongr (ContinuousLinearEquiv.neg ℝ)

/-- The fibrewise negation keeps the base point and negates the covector. -/
@[simp]
lemma cotangentFiberNeg_apply (x : V × StrongDual ℝ V) :
    cotangentFiberNeg x = (x.1, -x.2) :=
  (rfl)

/-- The fibrewise negation is an involution. -/
@[simp]
lemma cotangentFiberNeg_symm : (cotangentFiberNeg (V := V)).symm = cotangentFiberNeg := by
  ext x <;> simp [cotangentFiberNeg]

/-- The fibrewise negation pulls the Liouville form back to its negative: `ν^*λ = -λ`. The
derivative of `ν` at every point is `ν` itself (`ContinuousLinearEquiv.fderiv`). -/
lemma cotangentLiouvilleForm_cotangentFiberNeg (x : V × StrongDual ℝ V) :
    (cotangentLiouvilleForm (cotangentFiberNeg x)).compContinuousLinearMap
        ((cotangentFiberNeg (V := V)) : (V × StrongDual ℝ V) →L[ℝ] (V × StrongDual ℝ V)) =
      -cotangentLiouvilleForm x := by
  ext v
  simp

/-- The fibrewise negation reverses the canonical symplectic form: `ν^*ω = -ω`. -/
lemma strongDualCotangentSymplecticForm_cotangentFiberNeg (v w : V × StrongDual ℝ V) :
    strongDualCotangentSymplecticForm (cotangentFiberNeg v) (cotangentFiberNeg w) =
      -strongDualCotangentSymplecticForm v w := by
  simp only [strongDualCotangentSymplecticForm_apply, cotangentFiberNeg_apply, _root_.neg_apply]
  ring

/-! ### The radial Liouville field -/

/-- The radial vector field `p ∂_p` of the linear cotangent space, `(q, p) ↦ (0, p)`, as a
continuous linear map. It is the Liouville vector field of the primitive `-λ` of `ω`
(`strongDualCotangentSymplecticForm_cotangentLiouvilleField`). -/
def cotangentLiouvilleField : (V × StrongDual ℝ V) →L[ℝ] (V × StrongDual ℝ V) :=
  (ContinuousLinearMap.inr ℝ V (StrongDual ℝ V)).comp
    (ContinuousLinearMap.snd ℝ V (StrongDual ℝ V))

/-- The radial field at `(q, p)` is the vertical vector `(0, p)`. -/
@[simp]
lemma cotangentLiouvilleField_apply (x : V × StrongDual ℝ V) :
    cotangentLiouvilleField x = (0, x.2) :=
  (rfl)

/-- The radial field is the Liouville field of `-λ` for `ω`: `ι_Z ω = -λ`. -/
lemma strongDualCotangentSymplecticForm_cotangentLiouvilleField (x v : V × StrongDual ℝ V) :
    strongDualCotangentSymplecticForm (cotangentLiouvilleField x) v =
      -cotangentLiouvilleForm x (fun _ ↦ v) := by
  simp

/-- The fibrewise negation preserves the radial field. -/
lemma cotangentLiouvilleField_cotangentFiberNeg (x : V × StrongDual ℝ V) :
    cotangentLiouvilleField (cotangentFiberNeg x) =
      cotangentFiberNeg (cotangentLiouvilleField x) := by
  simp

/-! ### Magnetic translation -/

/-- The **magnetic translation** `(q, p) ↦ (q, p - σ_q)` of the linear cotangent space by a
one-form `σ` on `V`. The covector `σ_q` is the one-form `σ q` read as a continuous linear map. -/
def cotangentFiberTranslate (σ : V → V [⋀^Fin 1]→L[ℝ] ℝ) (x : V × StrongDual ℝ V) :
    V × StrongDual ℝ V :=
  (x.1, x.2 - (ofSubsingletonLIE (0 : Fin 1)).symm (σ x.1))

/-- A magnetic translation covers the identity of `V`. -/
@[simp]
lemma cotangentFiberTranslate_fst (σ : V → V [⋀^Fin 1]→L[ℝ] ℝ) (x : V × StrongDual ℝ V) :
    (cotangentFiberTranslate σ x).1 = x.1 :=
  (rfl)

/-- A magnetic translation subtracts `σ_q` from the covector at `q`. -/
@[simp]
lemma cotangentFiberTranslate_snd_apply (σ : V → V [⋀^Fin 1]→L[ℝ] ℝ) (x : V × StrongDual ℝ V)
    (v : V) :
    (cotangentFiberTranslate σ x).2 v = x.2 v - σ x.1 (fun _ ↦ v) :=
  (rfl)

/-- The magnetic translation by the zero one-form is the identity. -/
@[simp]
lemma cotangentFiberTranslate_zero :
    cotangentFiberTranslate (0 : V → V [⋀^Fin 1]→L[ℝ] ℝ) = id := by
  funext x
  ext v <;> simp

/-- Magnetic translations compose by adding the one-forms. -/
lemma cotangentFiberTranslate_add (σ τ : V → V [⋀^Fin 1]→L[ℝ] ℝ) (x : V × StrongDual ℝ V) :
    cotangentFiberTranslate (σ + τ) x =
      cotangentFiberTranslate σ (cotangentFiberTranslate τ x) := by
  ext v
  · simp
  · simp only [cotangentFiberTranslate_snd_apply, cotangentFiberTranslate_fst, Pi.add_apply,
      ContinuousAlternatingMap.add_apply]
    ring

/-- Translating by `-σ` undoes the translation by `σ`. -/
lemma leftInverse_cotangentFiberTranslate_neg (σ : V → V [⋀^Fin 1]→L[ℝ] ℝ) :
    Function.LeftInverse (cotangentFiberTranslate (-σ)) (cotangentFiberTranslate σ) := fun x ↦ by
  rw [← cotangentFiberTranslate_add, neg_add_cancel, cotangentFiberTranslate_zero, id_eq]

/-- Translating by `σ` undoes the translation by `-σ`. -/
lemma rightInverse_cotangentFiberTranslate_neg (σ : V → V [⋀^Fin 1]→L[ℝ] ℝ) :
    Function.RightInverse (cotangentFiberTranslate (-σ)) (cotangentFiberTranslate σ) :=
  fun x ↦ by simpa only [neg_neg] using leftInverse_cotangentFiberTranslate_neg (-σ) x

/-- Conjugation by the fibrewise negation changes the sign of the one-form: `ν ∘ Ψ_σ ∘ ν` is the
fibre translation `(q, p) ↦ (q, p + σ_q)`. -/
lemma cotangentFiberNeg_cotangentFiberTranslate_cotangentFiberNeg
    (σ : V → V [⋀^Fin 1]→L[ℝ] ℝ) (x : V × StrongDual ℝ V) :
    cotangentFiberNeg (cotangentFiberTranslate σ (cotangentFiberNeg x)) =
      cotangentFiberTranslate (-σ) x := by
  ext v
  · simp
  · simp only [cotangentFiberNeg_apply, _root_.neg_apply, cotangentFiberTranslate_snd_apply,
      Pi.neg_apply, ContinuousAlternatingMap.neg_apply]
    ring

/-- The magnetic translation by a `C^n` one-form is `C^n`. -/
lemma contDiff_cotangentFiberTranslate {n : WithTop ℕ∞} {σ : V → V [⋀^Fin 1]→L[ℝ] ℝ}
    (hσ : ContDiff ℝ n σ) : ContDiff ℝ n (cotangentFiberTranslate σ) :=
  contDiff_fst.prodMk <| contDiff_snd.sub <|
    (ofSubsingletonLIE (0 : Fin 1)).symm.contDiff.comp (hσ.comp contDiff_fst)

/-- The derivative of a magnetic translation: `DΨ_σ (δq, δp) = (δq, δp - (Dσ δq)_q)`. -/
lemma hasFDerivAt_cotangentFiberTranslate {σ : V → V [⋀^Fin 1]→L[ℝ] ℝ}
    {x : V × StrongDual ℝ V} (hσ : DifferentiableAt ℝ σ x.1) :
    HasFDerivAt (cotangentFiberTranslate σ)
      ((ContinuousLinearMap.fst ℝ V (StrongDual ℝ V)).prod
        (ContinuousLinearMap.snd ℝ V (StrongDual ℝ V) -
          ((ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ) (0 : Fin 1)).symm :
            (V [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] StrongDual ℝ V).comp
            ((fderiv ℝ σ x.1).comp (ContinuousLinearMap.fst ℝ V (StrongDual ℝ V))))) x :=
  hasFDerivAt_fst.prodMk <| hasFDerivAt_snd.sub <|
    (ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ) (0 : Fin 1)).symm.hasFDerivAt.comp x
      (hσ.hasFDerivAt.comp x hasFDerivAt_fst)

/-- The derivative of a magnetic translation on a tangent vector. -/
lemma fderiv_cotangentFiberTranslate {σ : V → V [⋀^Fin 1]→L[ℝ] ℝ} {x : V × StrongDual ℝ V}
    (hσ : DifferentiableAt ℝ σ x.1) (v : V × StrongDual ℝ V) :
    fderiv ℝ (cotangentFiberTranslate σ) x v =
      (v.1, v.2 - (ofSubsingletonLIE (0 : Fin 1)).symm (fderiv ℝ σ x.1 v.1)) := by
  simp [(hasFDerivAt_cotangentFiberTranslate hσ).fderiv]

/-- **The magnetic translation pulls the Liouville form back to `λ - π^*σ`.** -/
lemma cotangentLiouvilleForm_cotangentFiberTranslate {σ : V → V [⋀^Fin 1]→L[ℝ] ℝ}
    {x : V × StrongDual ℝ V} (hσ : DifferentiableAt ℝ σ x.1) :
    (cotangentLiouvilleForm (cotangentFiberTranslate σ x)).compContinuousLinearMap
        (fderiv ℝ (cotangentFiberTranslate σ) x) =
      cotangentLiouvilleForm x -
        (σ x.1).compContinuousLinearMap (ContinuousLinearMap.fst ℝ V (StrongDual ℝ V)) := by
  ext v
  have hv : Prod.fst ∘ v = fun _ ↦ (v 0).1 := by
    funext i
    simp [Subsingleton.elim i 0]
  simp [fderiv_cotangentFiberTranslate hσ, hv]

/-- **The magnetic translation pulls `ω` back to the magnetic form `ω + π^*dσ`.** On tangent
vectors `v` and `w` at `x`,
`ω(DΨ_σ v, DΨ_σ w) = ω(v, w) + dσ_q(δq_v, δq_w)`, where `q = π x`. Only the differentiability of
`σ` at `q` is used. -/
lemma strongDualCotangentSymplecticForm_fderiv_cotangentFiberTranslate
    {σ : V → V [⋀^Fin 1]→L[ℝ] ℝ} {x : V × StrongDual ℝ V} (hσ : DifferentiableAt ℝ σ x.1)
    (v w : V × StrongDual ℝ V) :
    strongDualCotangentSymplecticForm (fderiv ℝ (cotangentFiberTranslate σ) x v)
        (fderiv ℝ (cotangentFiberTranslate σ) x w) =
      strongDualCotangentSymplecticForm v w + extDeriv σ x.1 ![v.1, w.1] := by
  -- The two one-element sublists of `![v.1, w.1]` that enter the formula for `dσ`.
  have h0 : Fin.removeNth 0 ![v.1, w.1] = fun _ ↦ w.1 := by
    funext i
    simp [Subsingleton.elim i 0, Fin.removeNth]
  have h1 : Fin.removeNth 1 ![v.1, w.1] = fun _ ↦ v.1 := by
    funext i
    simp [Subsingleton.elim i 0, Fin.removeNth]
  rw [extDeriv_apply hσ, Fin.sum_univ_two, h0, h1]
  simp only [fderiv_cotangentFiberTranslate hσ,
    fderiv_continuousAlternatingMap_apply_const_apply hσ, ofSubsingletonLIE_symm_apply,
    strongDualCotangentSymplecticForm_apply, _root_.sub_apply, ofSubsingleton_symm_apply_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, one_smul, neg_smul]
  ring

/-- For a one-form `σ` that is closed at `q = π x`, the derivative of the magnetic translation at
`x` preserves the canonical symplectic form. -/
lemma strongDualCotangentSymplecticForm_fderiv_cotangentFiberTranslate_of_extDeriv_eq_zero
    {σ : V → V [⋀^Fin 1]→L[ℝ] ℝ} {x : V × StrongDual ℝ V} (hσ : DifferentiableAt ℝ σ x.1)
    (hdσ : extDeriv σ x.1 = 0) (v w : V × StrongDual ℝ V) :
    strongDualCotangentSymplecticForm (fderiv ℝ (cotangentFiberTranslate σ) x v)
        (fderiv ℝ (cotangentFiberTranslate σ) x w) =
      strongDualCotangentSymplecticForm v w := by
  simp [strongDualCotangentSymplecticForm_fderiv_cotangentFiberTranslate hσ, hdσ]

end TauCeti

end
