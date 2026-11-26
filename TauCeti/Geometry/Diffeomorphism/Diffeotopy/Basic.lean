/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Topology.Homotopy.Isotopy.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Smooth ambient isotopies

A `Diffeotopy J n M` is a `C^n` motion of a real manifold `M` through
self-diffeomorphisms, starting at the identity.  It is bundled by its level-preserving total
diffeomorphism of `I × M`: this makes invertibility in the time and space variables part of the
data and ensures that no unrelated choices of inverse maps are carried by the structure.

The time interval is Mathlib's `unitInterval`, with its manifold-with-boundary structure modelled
on `𝓡∂ 1`.  The total diffeomorphism is required to preserve the time coordinate.  Its slice at
each `t : I` is therefore a self-diffeomorphism of `M`; `Diffeotopy.timeSlice` packages that fact.
Diffeotopies coerce to their spatial component, so `Φ (t, x)` is the point of `M` reached from
`x` at time `t`.
Diffeotopies compose and invert, and forgetting smoothness gives the existing
`TauCeti.AmbientIsotopy`.

The notion is defined for an arbitrary manifold `M`, before any specialization to knots.  The
non-ambient smooth isotopy of arbitrary maps is separate and is not defined here.  The
specialization to bundled smooth embeddings, used for geometric knot presentations, is in
`TauCeti.Geometry.Manifold.SmoothEmbedding.SmoothAmbientIsotopy.Basic`.

## Main definitions

* `TauCeti.Diffeotopy`: a level-preserving diffeomorphism of `I × M` starting at the identity.
* `TauCeti.Diffeotopy.timeSlice`: the self-diffeomorphism of `M` at a fixed time.
* `TauCeti.Diffeotopy.final`: the self-diffeomorphism at time one.
* `TauCeti.Diffeotopy.cylinderMap`: the motion `(x, t) ↦ Φ (t, x)` on the cylinder `M × I`.
* `TauCeti.Diffeotopy.refl`, `trans`, and `symm`: the constant, composite, and inverse
  diffeotopies.
* `TauCeti.Diffeotopy.toAmbientIsotopy`: forget smoothness to obtain a continuous ambient
  isotopy.

## Main results

* `TauCeti.Diffeotopy.timeSlice_trans` and `timeSlice_symm`: time slices commute with composition
  and inversion.
* `TauCeti.Diffeotopy.final_trans` and `final_symm`: the corresponding calculus for final
  diffeomorphisms.
* `TauCeti.Diffeotopy.final_symm_trans`: `φ_t ∘ ψ_t⁻¹` ends at `φ₁ * ψ₁⁻¹`.
* `TauCeti.Diffeotopy.timeSlice_transDiffeomorph_eq_mul_mul_inv` and
  `final_transDiffeomorph_eq_mul_mul_inv`: conjugating a diffeotopy by a self-diffeomorphism `f`
  conjugates its time slices by `f` in the self-diffeomorphism group.
* `TauCeti.Diffeotopy.comp_cylinderMap_of_semiconj`: a map intertwining two diffeotopies at every
  time intertwines their motions on the cylinders; `semiconj_symm_timeSlice_transDiffeomorph`
  is the instance `f⁻¹` for a conjugated diffeotopy.
* `TauCeti.Diffeotopy.eqOn_id_trans`, `eqOn_id_symm` and `eqOn_id_transDiffeomorph`: being the
  identity outside a set at every time passes to composites, inverses and conjugates.
* `TauCeti.Diffeotopy.toAmbientIsotopy_final_apply`: forgetting smoothness preserves the final
  action.
* `TauCeti.Diffeotopy.final_eq_of_homotopy`: diffeotopies whose motions are joined by a homotopy
  stationary at the final time have the same final diffeomorphism.
* `TauCeti.Diffeotopy.mfderiv_cylinderMap_inl`: the spatial derivative of the motion is the
  differential of the time slice.
* `TauCeti.Diffeotopy.mfderiv_cylinderMap_mfderiv_cylinderMap_symm`: the derivative of
  `φ_t (φ_t⁻¹ x) = x` on the cylinder.
* `TauCeti.Diffeotopy.mfderiv_timeSlice_mfderiv_cylinderMap_symm_inl`: `dφ_t ∘ d(φ_t⁻¹) = id`.

## References

* G. Burde and H. Zieschang, *Knots*, 2nd ed., de Gruyter (2003), Chapter 1, for ambient
  isotopy of knots.
* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §8.1, for smooth
  isotopies and diffeotopies.
-/

public section

noncomputable section

namespace TauCeti

open unitInterval
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- A `C^n` **diffeotopy** of a real manifold `M`: a level-preserving diffeomorphism of
`I × M` which is the identity at time zero.

Bundling the level-preserving total map as a `Diffeomorph` makes every time slice invertible and
makes its inverse canonical. -/
structure Diffeotopy (J : ModelWithCorners ℝ E H) (n : ℕ∞ω) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] where
  /-- The level-preserving total diffeomorphism of `I × M`. -/
  toDiffeomorph :
    (I × M) ≃ₘ^n⟮(𝓡∂ 1).prod J, (𝓡∂ 1).prod J⟯ I × M
  /-- The total diffeomorphism preserves the time coordinate. -/
  fst_apply (p : I × M) : (toDiffeomorph p).1 = p.1
  /-- The motion starts at the identity. -/
  snd_apply_zero' (x : M) : (toDiffeomorph (0, x)).2 = x

namespace Diffeotopy

/-- Apply a diffeotopy as `Φ (t, x)`: the spatial component of the total diffeomorphism. -/
instance instCoeFun : CoeFun (Diffeotopy J n M) fun _ => I × M → M where
  coe Φ p := (Φ.toDiffeomorph p).2

attribute [simp] Diffeotopy.fst_apply

variable (Φ : Diffeotopy J n M)

/-! ### Ambient coordinate changes -/

variable {P : Type*} [TopologicalSpace P] [ChartedSpace H P]

/-- Transport a diffeotopy across an ambient diffeomorphism by conjugation. -/
def transDiffeomorph (f : M ≃ₘ^n⟮J, J⟯ P) (Φ : Diffeotopy J n M) : Diffeotopy J n P where
  toDiffeomorph :=
    (Diffeomorph.prodCongr (_root_.Diffeomorph.refl (𝓡∂ 1) I n) f.symm).trans
      (Φ.toDiffeomorph.trans
        (Diffeomorph.prodCongr (_root_.Diffeomorph.refl (𝓡∂ 1) I n) f))
  fst_apply p := by
    unfold Diffeomorph.trans
    exact Φ.fst_apply _
  snd_apply_zero' x := by
    simpa only [Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.coe_prodCongr,
      Prod.map_apply, Prod.map_snd, Diffeomorph.coe_refl, id_eq] using
      (congrArg f (Φ.snd_apply_zero' (f.symm x))).trans (f.apply_symm_apply x)

@[simp]
theorem transDiffeomorph_apply (f : M ≃ₘ^n⟮J, J⟯ P) (Φ : Diffeotopy J n M) (p : I × P) :
    Φ.transDiffeomorph f p = f (Φ (p.1, f.symm p.2)) :=
  (rfl)


/-- Applying a diffeotopy returns the spatial component of its total diffeomorphism. -/
@[simp]
theorem coe_apply (p : I × M) : Φ p = (Φ.toDiffeomorph p).2 :=
  (rfl)

/-- The total diffeomorphism of a diffeotopy sends `(t, x)` to `(t, Φ (t, x))`. -/
theorem toDiffeomorph_apply (p : I × M) : Φ.toDiffeomorph p = (p.1, Φ p) := by
  exact Prod.ext (Φ.fst_apply p) rfl

/-- A diffeotopy starts at the identity. -/
@[simp]
theorem apply_zero (x : M) : Φ (0, x) = x :=
  Φ.snd_apply_zero' x

/-- A diffeotopy is a `C^n` map of time and space into the ambient manifold. -/
theorem contMDiff : ContMDiff ((𝓡∂ 1).prod J) J n Φ :=
  contMDiff_snd.comp Φ.toDiffeomorph.contMDiff

/-- The inverse total diffeomorphism also preserves the time coordinate. -/
@[simp]
theorem fst_symm_apply (p : I × M) : (Φ.toDiffeomorph.symm p).1 = p.1 := by
  have h := Φ.fst_apply (Φ.toDiffeomorph.symm p)
  rw [Φ.toDiffeomorph.apply_symm_apply] at h
  exact h.symm

/-- The inverse total diffeomorphism sends `p` to its time coordinate paired with its spatial
component. -/
theorem toDiffeomorph_symm_apply (p : I × M) :
    Φ.toDiffeomorph.symm p = (p.1, (Φ.toDiffeomorph.symm p).2) := by
  exact Prod.ext (Φ.fst_symm_apply p) rfl

/-- The time-`t` slice of a diffeotopy, bundled as a self-diffeomorphism of `M`. -/
def timeSlice (t : I) : M ≃ₘ^n⟮J, J⟯ M where
  toEquiv :=
    { toFun := fun x ↦ Φ (t, x)
      invFun := fun y ↦ (Φ.toDiffeomorph.symm (t, y)).2
      left_inv := fun x ↦ by
        simp only [coe_apply]
        have hp : (t, (Φ.toDiffeomorph (t, x)).2) = Φ.toDiffeomorph (t, x) :=
          (Φ.toDiffeomorph_apply (t, x)).symm
        rw [hp, Φ.toDiffeomorph.symm_apply_apply]
      right_inv := fun y ↦ by
        simp only [coe_apply]
        have hp : (t, (Φ.toDiffeomorph.symm (t, y)).2) =
            Φ.toDiffeomorph.symm (t, y) := (Φ.toDiffeomorph_symm_apply (t, y)).symm
        rw [hp, Φ.toDiffeomorph.apply_symm_apply] }
  contMDiff_toFun :=
    Φ.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)
  contMDiff_invFun :=
    contMDiff_snd.comp
      (Φ.toDiffeomorph.symm.contMDiff.comp (contMDiff_const.prodMk contMDiff_id))

/-- Evaluating the time-`t` diffeomorphism is evaluating the diffeotopy at `(t, x)`. -/
@[simp]
theorem timeSlice_apply (t : I) (x : M) : Φ.timeSlice t x = Φ (t, x) :=
  (rfl)

/-- The time-zero slice of a diffeotopy is the identity diffeomorphism. -/
@[simp]
theorem timeSlice_zero : Φ.timeSlice 0 = _root_.Diffeomorph.refl J M n := by
  apply _root_.Diffeomorph.ext
  exact Φ.apply_zero

/-- The time-`1` self-diffeomorphism of a diffeotopy. -/
def final : M ≃ₘ^n⟮J, J⟯ M :=
  Φ.timeSlice 1

/-- The final diffeomorphism is the time-one slice. -/
theorem final_def : Φ.final = Φ.timeSlice 1 :=
  (rfl)

/-- The final diffeomorphism acts by the time-one slice. -/
@[simp]
theorem final_apply (x : M) : Φ.final x = Φ (1, x) :=
  (rfl)

/-- The final diffeomorphism preserves any set containing a set outside which the diffeotopy
is the identity. No compactness or openness assumption is needed. -/
theorem mapsTo_final_of_eqOn_compl {K U : Set M} (hKU : K ⊆ U)
    (hΦK : ∀ t, Set.EqOn (fun z ↦ Φ (t, z)) id Kᶜ) : Set.MapsTo Φ.final U U := by
  have hfix : Set.EqOn Φ.final id Uᶜ := by
    intro z hz
    simpa only [final_apply] using hΦK 1 (fun hzK => hz (hKU hzK))
  simpa only [compl_compl] using
    ((Set.surjOn_id Uᶜ).congr hfix.symm).mapsTo_compl Φ.final.injective

/-- The time slices of a conjugated diffeotopy are the conjugated time slices. -/
theorem timeSlice_transDiffeomorph (f : M ≃ₘ^n⟮J, J⟯ P) (t : I) :
    (Φ.transDiffeomorph f).timeSlice t = (f.symm.trans (Φ.timeSlice t)).trans f :=
  _root_.Diffeomorph.ext fun x ↦ by simp

/-- The final diffeomorphism of a conjugated diffeotopy is the conjugated final diffeomorphism. -/
theorem final_transDiffeomorph (f : M ≃ₘ^n⟮J, J⟯ P) :
    (Φ.transDiffeomorph f).final = (f.symm.trans Φ.final).trans f :=
  _root_.Diffeomorph.ext fun x ↦ by simp

/-- The time slices of a diffeotopy conjugated by a self-diffeomorphism `f` are the conjugates
`f * φ_t * f⁻¹` in the self-diffeomorphism group. -/
theorem timeSlice_transDiffeomorph_eq_mul_mul_inv (f : M ≃ₘ^n⟮J, J⟯ M) (t : I) :
    (Φ.transDiffeomorph f).timeSlice t = f * Φ.timeSlice t * f⁻¹ :=
  _root_.Diffeomorph.ext fun x ↦ by simp

/-- The final diffeomorphism of a diffeotopy conjugated by a self-diffeomorphism `f` is the
conjugate `f * φ₁ * f⁻¹` in the self-diffeomorphism group. -/
theorem final_transDiffeomorph_eq_mul_mul_inv (f : M ≃ₘ^n⟮J, J⟯ M) :
    (Φ.transDiffeomorph f).final = f * Φ.final * f⁻¹ :=
  Φ.timeSlice_transDiffeomorph_eq_mul_mul_inv f 1

/-! ### The motion on the cylinder -/

/-- The motion of a diffeotopy read on the cylinder `M × I`, with time as the second
coordinate: `(x, t) ↦ Φ (t, x)`. This is the order used by `TauCeti.homotopyOperator`. -/
def cylinderMap : M × I → M :=
  fun p ↦ Φ (p.2, p.1)

@[simp]
theorem cylinderMap_apply (p : M × I) : Φ.cylinderMap p = Φ (p.2, p.1) :=
  (rfl)

theorem contMDiff_cylinderMap : ContMDiff (J.prod (𝓡∂ 1)) J n Φ.cylinderMap :=
  Φ.contMDiff.comp (contMDiff_snd.prodMk contMDiff_fst)

/-- The cylinder map at time zero is the identity. -/
theorem cylinderMap_comp_zero : Φ.cylinderMap ∘ (fun x ↦ (x, (0 : I))) = id :=
  funext Φ.apply_zero

/-- The cylinder map at time one is the final diffeomorphism. -/
theorem cylinderMap_comp_one : Φ.cylinderMap ∘ (fun x ↦ (x, (1 : I))) = Φ.final :=
  funext fun x ↦ (Φ.final_apply x).symm

/-- The motion of a conjugated diffeotopy is the conjugated motion. -/
theorem cylinderMap_transDiffeomorph (f : M ≃ₘ^n⟮J, J⟯ P) :
    (Φ.transDiffeomorph f).cylinderMap = f ∘ Φ.cylinderMap ∘ Prod.map f.symm id :=
  funext fun p ↦ by simp

/-- The inverse `f⁻¹` intertwines the conjugated diffeotopy `f ∘ φ_t ∘ f⁻¹` with `φ_t`. -/
theorem semiconj_symm_timeSlice_transDiffeomorph (f : M ≃ₘ^n⟮J, J⟯ P) (t : I) :
    Function.Semiconj f.symm ((Φ.transDiffeomorph f).timeSlice t) (Φ.timeSlice t) :=
  fun _ ↦ by
    simp only [timeSlice_apply, transDiffeomorph_apply, _root_.Diffeomorph.symm_apply_apply]

/-- If a map `g` intertwines two diffeotopies at every time, `g ∘ φ'_t = φ_t ∘ g`, then it
intertwines their motions on the cylinders: `g ∘ Φ' = Φ ∘ (g × id)`. -/
theorem comp_cylinderMap_of_semiconj {E' H' M' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {J' : ModelWithCorners ℝ E' H'} [TopologicalSpace M']
    [ChartedSpace H' M'] {Φ' : Diffeotopy J' n M'} {g : M' → M}
    (h : ∀ t, Function.Semiconj g (Φ'.timeSlice t) (Φ.timeSlice t)) :
    g ∘ Φ'.cylinderMap = Φ.cylinderMap ∘ Prod.map g id :=
  funext fun p ↦ by
    simpa only [Function.comp_apply, cylinderMap_apply, Prod.map_fst, Prod.map_snd, id_eq,
      timeSlice_apply] using h p.2 p.1

/-- If the motion of `Φ` is joined to the motion of `Ψ` by a homotopy `G` that is stationary at the
final time, then `Φ` and `Ψ` have the same final diffeomorphism. -/
theorem final_eq_of_homotopy {Ψ : Diffeotopy J n M} {G : (M × I) × I → M}
    (hG₁ : ∀ p, G (p, 1) = Ψ.cylinderMap p) (h₁ : ∀ x s, G ((x, 1), s) = Φ.final x) :
    Ψ.final = Φ.final :=
  _root_.Diffeomorph.ext fun x ↦ by
    rw [final_apply, ← cylinderMap_apply Ψ (x, 1), ← hG₁, h₁]

/-- The constant diffeotopy at the identity. -/
def refl (J : ModelWithCorners ℝ E H) (n : ℕ∞ω) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] : Diffeotopy J n M where
  toDiffeomorph := _root_.Diffeomorph.refl ((𝓡∂ 1).prod J) (I × M) n
  fst_apply _ := rfl
  snd_apply_zero' _ := rfl

/-- The constant diffeotopy fixes every point at every time. -/
@[simp]
theorem refl_apply (p : I × M) : refl J n M p = p.2 :=
  (rfl)

/-- The time slice of the constant diffeotopy is the identity. -/
@[simp]
theorem timeSlice_refl (t : I) : (refl J n M).timeSlice t =
    _root_.Diffeomorph.refl J M n := by
  apply _root_.Diffeomorph.ext
  intro x
  rfl

/-- The final diffeomorphism of the constant diffeotopy is the identity. -/
@[simp]
theorem final_refl : (refl J n M).final = _root_.Diffeomorph.refl J M n := by
  rw [final_def, timeSlice_refl]

/-- Compose two diffeotopies pointwise, first `Φ` and then `Ψ`. -/
def trans (Φ Ψ : Diffeotopy J n M) : Diffeotopy J n M where
  toDiffeomorph := Φ.toDiffeomorph.trans Ψ.toDiffeomorph
  fst_apply p := by
    rw [congr_fun (_root_.Diffeomorph.coe_trans Φ.toDiffeomorph Ψ.toDiffeomorph) p,
      Function.comp_apply, Ψ.fst_apply, Φ.fst_apply]
  snd_apply_zero' x := by
    rw [congr_fun (_root_.Diffeomorph.coe_trans Φ.toDiffeomorph Ψ.toDiffeomorph) (0, x),
      Function.comp_apply, Φ.toDiffeomorph_apply, Φ.apply_zero]
    exact Ψ.apply_zero x

/-- Evaluating a composite diffeotopy applies `Φ` and then `Ψ` at the same time. -/
@[simp]
theorem trans_apply (Ψ : Diffeotopy J n M) (p : I × M) :
    Φ.trans Ψ p = Ψ (p.1, Φ p) := by
  simp only [coe_apply]
  unfold trans
  rw [congr_fun (_root_.Diffeomorph.coe_trans Φ.toDiffeomorph Ψ.toDiffeomorph) p,
    Function.comp_apply, Φ.toDiffeomorph_apply]

/-- The motion of a composite diffeotopy is the motion of `Ψ` after the level-preserving motion
`(x, t) ↦ (Φ (t, x), t)` of `Φ`. -/
theorem cylinderMap_trans (Ψ : Diffeotopy J n M) :
    (Φ.trans Ψ).cylinderMap = Ψ.cylinderMap ∘ fun p ↦ (Φ.cylinderMap p, p.2) :=
  funext fun p ↦ by simp

/-- The level-preserving motion `(x, t) ↦ (Φ (t, x), t)` of a `C^n` diffeotopy is `C^n`. -/
theorem contMDiff_cylinderMap_prodMk_snd :
    ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)) n fun p : M × I ↦ (Φ.cylinderMap p, p.2) :=
  Φ.contMDiff_cylinderMap.prodMk contMDiff_snd

/-- The level-preserving motion `(x, t) ↦ (Φ (t, x), t)` of a `C^n` diffeotopy, `1 ≤ n`, acts on
tangent vectors by `w ↦ (dΦ w, w₂)`. -/
theorem mfderiv_cylinderMap_prodMk_snd (hn : 1 ≤ n) (p : M × I)
    (w : TangentSpace (J.prod (𝓡∂ 1)) p) :
    mfderiv (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)) (fun q ↦ (Φ.cylinderMap q, q.2)) p w =
      (mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap p w, w.2) := by
  rw [mfderiv_prodMk (Φ.contMDiff_cylinderMap.mdifferentiableAt
      (zero_lt_one.trans_le (by exact_mod_cast hn)).ne') mdifferentiableAt_snd]
  -- `mfderiv_prodMk` returns a map into `TangentSpace J _ × TangentSpace (𝓡∂ 1) _`, the tangent
  -- space of the product only up to unfolding `TangentSpace`, so `ContinuousLinearMap.prod_apply`
  -- is applied by `exact` rather than rewritten.
  exact (ContinuousLinearMap.prod_apply _ _ w).trans (congrArg (Prod.mk _) (mfderiv_snd_apply p w))

/-- The time slice of a composite diffeotopy is the composite of its time slices. -/
@[simp]
theorem timeSlice_trans (Ψ : Diffeotopy J n M) (t : I) :
    (Φ.trans Ψ).timeSlice t = (Φ.timeSlice t).trans (Ψ.timeSlice t) := by
  apply _root_.Diffeomorph.ext
  intro x
  simpa only [timeSlice_apply, _root_.Diffeomorph.coe_trans, Function.comp_apply] using
    Φ.trans_apply Ψ (t, x)

/-- The final diffeomorphism of a composite diffeotopy is the composite of the final
diffeomorphisms. -/
@[simp]
theorem final_trans (Ψ : Diffeotopy J n M) :
    (Φ.trans Ψ).final = Φ.final.trans Ψ.final := by
  simpa only [final_def] using Φ.timeSlice_trans Ψ 1

/-- Reverse a diffeotopy by taking the inverse of its level-preserving total diffeomorphism. -/
def symm (Φ : Diffeotopy J n M) : Diffeotopy J n M where
  toDiffeomorph := Φ.toDiffeomorph.symm
  fst_apply := Φ.fst_symm_apply
  snd_apply_zero' x := by
    have hp : Φ.toDiffeomorph (0, x) = (0, x) := by
      rw [Φ.toDiffeomorph_apply, Φ.apply_zero]
    rw [← hp, Φ.toDiffeomorph.symm_apply_apply]

/-- Evaluating the inverse diffeotopy uses the spatial component of the inverse total
diffeomorphism. -/
@[simp]
theorem symm_apply (p : I × M) : Φ.symm p = (Φ.toDiffeomorph.symm p).2 :=
  (rfl)

/-- The inverse of the time-`t` slice acts by the inverse diffeotopy at time `t`. -/
@[simp]
theorem symm_timeSlice_apply (t : I) (x : M) :
    (Φ.timeSlice t).symm x = Φ.symm (t, x) :=
  (rfl)

/-- The time slice of the inverse diffeotopy is the inverse time slice. -/
@[simp]
theorem timeSlice_symm (t : I) :
    Φ.symm.timeSlice t = (Φ.timeSlice t).symm := by
  apply _root_.Diffeomorph.ext
  intro x
  rw [timeSlice_apply, symm_timeSlice_apply]

/-- A diffeotopy followed by its inverse fixes every point. -/
@[simp]
theorem symm_apply_apply (p : I × M) :
    (Φ.toDiffeomorph.symm (p.1, (Φ.toDiffeomorph p).2)).2 = p.2 := by
  have hp : (p.1, (Φ.toDiffeomorph p).2) = Φ.toDiffeomorph p :=
    Prod.ext (Φ.fst_apply p).symm rfl
  rw [hp, Φ.toDiffeomorph.symm_apply_apply]

/-- The inverse diffeotopy followed by the original fixes every point. -/
@[simp]
theorem apply_symm_apply (p : I × M) :
    (Φ.toDiffeomorph (p.1, (Φ.toDiffeomorph.symm p).2)).2 = p.2 := by
  have hp : (p.1, (Φ.toDiffeomorph.symm p).2) = Φ.toDiffeomorph.symm p :=
    Prod.ext (Φ.fst_symm_apply p).symm rfl
  rw [hp, Φ.toDiffeomorph.apply_symm_apply]

/-- The inverse diffeotopy at time `t` undoes the diffeotopy at time `t`. -/
theorem symm_apply_mk_apply (t : I) (x : M) : Φ.symm (t, Φ (t, x)) = x := by
  rw [← Φ.timeSlice_apply, ← Φ.symm_timeSlice_apply]
  exact (Φ.timeSlice t).symm_apply_apply x

/-- The diffeotopy at time `t` undoes the inverse diffeotopy at time `t`. -/
theorem apply_mk_symm_apply (t : I) (x : M) : Φ (t, Φ.symm (t, x)) = x := by
  rw [← Φ.symm_timeSlice_apply, ← Φ.timeSlice_apply]
  exact (Φ.timeSlice t).apply_symm_apply x

/-- The final diffeomorphism of the inverse diffeotopy is the inverse final diffeomorphism. -/
@[simp]
theorem final_symm : Φ.symm.final = Φ.final.symm := by
  simpa only [final_def] using Φ.timeSlice_symm 1

/-- If `ψ ∘ Φ₁ = φ`, then the inverse diffeotopy satisfies `φ ∘ (Φ⁻¹)₁ = ψ`. -/
theorem mul_final_symm_eq_of_mul_final_eq {φ ψ : M ≃ₘ^n⟮J, J⟯ M} (h : ψ * Φ.final = φ) :
    φ * Φ.symm.final = ψ := by
  rw [final_symm]
  exact mul_inv_eq_of_eq_mul h.symm

/-- Following the inverse of `ψ_t` by `φ_t` ends at `φ₁ * ψ₁⁻¹` in the self-diffeomorphism
group. -/
theorem final_symm_trans (Ψ : Diffeotopy J n M) :
    (Ψ.symm.trans Φ).final = Φ.final * Ψ.final⁻¹ := by
  rw [final_trans, final_symm, _root_.Diffeomorph.mul_def, _root_.Diffeomorph.inv_def]

/-- Applying the inverse diffeotopy at time `t` after the diffeotopy at time `t` returns the
starting point. -/
theorem symm_apply_apply_mk (t : I) (x : M) : Φ.symm (t, Φ (t, x)) = x := by
  have h := (Φ.timeSlice t).symm_apply_apply x
  rwa [timeSlice_apply, symm_timeSlice_apply] at h

/-- Applying the diffeotopy at time `t` after the inverse diffeotopy at time `t` returns the
starting point. -/
theorem apply_symm_apply_mk (t : I) (x : M) : Φ (t, Φ.symm (t, x)) = x := by
  have h := (Φ.timeSlice t).apply_symm_apply x
  rwa [symm_timeSlice_apply, timeSlice_apply] at h

/-- A point is fixed by the inverse diffeotopy at time `t` exactly when it is fixed by the
diffeotopy at time `t`. -/
theorem symm_apply_eq_self_iff {t : I} {x : M} : Φ.symm (t, x) = x ↔ Φ (t, x) = x := by
  rw [← symm_timeSlice_apply, ← timeSlice_apply]
  constructor
  · intro h
    conv_lhs => rw [← h]
    exact (Φ.timeSlice t).apply_symm_apply x
  · intro h
    conv_lhs => rw [← h]
    exact (Φ.timeSlice t).symm_apply_apply x

/-- If two diffeotopies are the identity outside `K` and outside `L` at every time, their
pointwise composite is the identity outside `K ∪ L` at every time. -/
theorem eqOn_id_trans {Φ Ψ : Diffeotopy J n M} {K L : Set M}
    (hΦ : ∀ t, Set.EqOn (fun x ↦ Φ (t, x)) id Kᶜ) (hΨ : ∀ t, Set.EqOn (fun x ↦ Ψ (t, x)) id Lᶜ)
    (t : I) : Set.EqOn (fun x ↦ Φ.trans Ψ (t, x)) id (K ∪ L)ᶜ := fun x hx ↦ by
  rw [Set.compl_union] at hx
  simp only [trans_apply, hΦ t hx.1, id_eq]
  exact hΨ t hx.2

/-- If a diffeotopy is the identity outside `K` at every time, so is its pointwise inverse. -/
theorem eqOn_id_symm {Φ : Diffeotopy J n M} {K : Set M}
    (hΦ : ∀ t, Set.EqOn (fun x ↦ Φ (t, x)) id Kᶜ) (t : I) :
    Set.EqOn (fun x ↦ Φ.symm (t, x)) id Kᶜ := fun _ hx ↦ Φ.symm_apply_eq_self_iff.2 (hΦ t hx)

/-- If a diffeotopy is the identity outside `K` at every time, its conjugate `f ∘ φ_t ∘ f⁻¹` by
a diffeomorphism `f` is the identity outside `f '' K` at every time. -/
theorem eqOn_id_transDiffeomorph {Φ : Diffeotopy J n M} {K : Set M} (f : M ≃ₘ^n⟮J, J⟯ P)
    (hΦ : ∀ t, Set.EqOn (fun x ↦ Φ (t, x)) id Kᶜ) (t : I) :
    Set.EqOn (fun x ↦ Φ.transDiffeomorph f (t, x)) id (f '' K)ᶜ := fun x hx ↦ by
  have hx' : f.symm x ∉ K := fun h ↦ hx ⟨_, h, f.apply_symm_apply x⟩
  simp only [transDiffeomorph_apply, hΦ t hx', id_eq, Diffeomorph.apply_symm_apply]

/-- Forgetting smoothness turns a diffeotopy into a continuous ambient isotopy. -/
def toAmbientIsotopy : AmbientIsotopy M where
  toContinuousMap := ⟨Φ, Φ.contMDiff.continuous⟩
  isHomeomorph_total' := by
    have hfun : (fun p : I × M ↦ (p.1, Φ p)) = Φ.toDiffeomorph := by
      funext p
      exact (Φ.toDiffeomorph_apply p).symm
    rw [hfun]
    exact Φ.toDiffeomorph.toHomeomorph.isHomeomorph
  map_zero_left' := Φ.apply_zero

/-- Forgetting smoothness does not change the ambient motion. -/
@[simp]
theorem toAmbientIsotopy_apply (p : I × M) : Φ.toAmbientIsotopy.toContinuousMap p = Φ p :=
  (rfl)

/-- Forgetting smoothness commutes with taking the final map. -/
@[simp 1100]
theorem toAmbientIsotopy_final_apply (x : M) :
    Φ.toAmbientIsotopy.final x = Φ.final x := by
  rw [AmbientIsotopy.final_apply, toAmbientIsotopy_apply, final_apply]

/-- Forgetting smoothness commutes with composition of diffeotopies. -/
@[simp]
theorem toAmbientIsotopy_trans (Ψ : Diffeotopy J n M) :
    (Φ.trans Ψ).toAmbientIsotopy = Φ.toAmbientIsotopy.trans Ψ.toAmbientIsotopy := by
  apply AmbientIsotopy.ext
  intro p
  rw [toAmbientIsotopy_apply, AmbientIsotopy.trans_apply, toAmbientIsotopy_apply,
    toAmbientIsotopy_apply, trans_apply]

/-- Forgetting smoothness commutes with inversion of diffeotopies. -/
@[simp]
theorem toAmbientIsotopy_symm :
    Φ.symm.toAmbientIsotopy = Φ.toAmbientIsotopy.symm := by
  have htotal : Φ.toAmbientIsotopy.totalHomeomorph = Φ.toDiffeomorph.toHomeomorph := by
    apply Homeomorph.ext
    intro p
    rw [AmbientIsotopy.totalHomeomorph_apply]
    simpa only [toAmbientIsotopy_apply, _root_.Diffeomorph.coe_toHomeomorph] using
      (Φ.toDiffeomorph_apply p).symm
  apply AmbientIsotopy.ext
  intro p
  rw [toAmbientIsotopy_apply, AmbientIsotopy.symm_apply, htotal, symm_apply]
  simp only [_root_.Diffeomorph.coe_toHomeomorph_symm]

/-- Two diffeotopies are equal when their ambient motions agree pointwise. -/
@[ext]
theorem ext {Φ Ψ : Diffeotopy J n M} (h : ∀ p, Φ p = Ψ p) : Φ = Ψ := by
  cases Φ with
  | mk φ hφ hφ0 =>
    cases Ψ with
    | mk ψ hψ hψ0 =>
      congr 1
      apply _root_.Diffeomorph.ext
      intro p
      exact Prod.ext ((hφ p).trans (hψ p).symm) (h p)

/-- The constant diffeotopy is a left identity for composition. -/
@[simp]
theorem refl_trans : (refl J n M).trans Φ = Φ := by
  apply ext
  intro p
  simp

/-- The constant diffeotopy is a right identity for composition. -/
@[simp]
theorem trans_refl : Φ.trans (refl J n M) = Φ := by
  apply ext
  intro p
  simp

/-- Composition of diffeotopies is associative. -/
theorem trans_assoc (Ψ Θ : Diffeotopy J n M) :
    (Φ.trans Ψ).trans Θ = Φ.trans (Ψ.trans Θ) := by
  apply ext
  intro p
  simp

/-- Inverting a diffeotopy twice recovers the original diffeotopy. -/
@[simp]
theorem symm_symm : Φ.symm.symm = Φ := by
  have htotal : Φ.symm.toDiffeomorph.symm = Φ.toDiffeomorph := by
    apply _root_.Diffeomorph.ext
    intro p
    rfl
  apply ext
  intro p
  rw [symm_apply, htotal, coe_apply]

/-- A diffeotopy followed by its inverse is the constant diffeotopy. -/
@[simp]
theorem self_trans_symm : Φ.trans Φ.symm = refl J n M := by
  apply ext
  intro p
  simp

/-- A diffeotopy inverse followed by the original is the constant diffeotopy. -/
@[simp]
theorem symm_trans_self : Φ.symm.trans Φ = refl J n M := by
  apply ext
  intro p
  simp

/-! ### Derivatives of the motion and its inverse -/

/-- **The spatial derivative of the motion.** The motion `(x, t) ↦ φ_t x` of a diffeotopy of
positive order acts on spatial tangent vectors at `(x, t)` by the differential of the time slice
`φ_t`. -/
theorem mfderiv_cylinderMap_inl (hn : 1 ≤ n) (p : M × I) (v : E) :
    mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap p (v, (0 : TangentSpace (𝓡∂ 1) p.2)) =
      mfderiv J J (Φ.timeSlice p.2) p.1 v := by
  refine (mfderiv_prod_eq_add_apply (Φ.contMDiff_cylinderMap.mdifferentiableAt
    (zero_lt_one.trans_le (by exact_mod_cast hn)).ne')).trans ?_
  have hslice : (fun z ↦ Φ.cylinderMap (z, p.2)) = Φ.timeSlice p.2 :=
    funext fun z ↦ by rw [cylinderMap_apply, timeSlice_apply]
  rw [hslice]
  exact add_eq_left.2 (map_zero _)

/-- **The motion followed by its inverse.** Differentiating `φ_t (φ_t⁻¹ x) = x` on the cylinder: for
a tangent vector `w = (u, s)` at `(x, t)`, the differential of the motion at `(φ_t⁻¹ x, t)` sends
the image `(d(φ⁻¹) w, s)` of `w` under the level-preserving inverse motion to `u`. -/
theorem mfderiv_cylinderMap_mfderiv_cylinderMap_symm (hn : 1 ≤ n) (p : M × I)
    (w : TangentSpace (J.prod (𝓡∂ 1)) p) :
    mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (Φ.symm.cylinderMap p, p.2)
      (mfderiv (J.prod (𝓡∂ 1)) J Φ.symm.cylinderMap p w, w.2) = w.1 := by
  have hn₀ : n ≠ 0 := (zero_lt_one.trans_le (by exact_mod_cast hn)).ne'
  -- The motion of `φ_t ∘ φ_t⁻¹`, the constant diffeotopy, is the projection to `M`.
  have hcomp : Φ.cylinderMap ∘ (fun q ↦ (Φ.symm.cylinderMap q, q.2)) = Prod.fst := by
    rw [← cylinderMap_trans, symm_trans_self]
    exact funext fun q ↦ by simp
  have h := mfderiv_comp_apply p (Φ.contMDiff_cylinderMap.mdifferentiableAt hn₀)
    (Φ.symm.contMDiff_cylinderMap_prodMk_snd.mdifferentiableAt hn₀) w
  rw [hcomp, mfderiv_fst] at h
  exact (congrArg _ (Φ.symm.mfderiv_cylinderMap_prodMk_snd hn p w)).symm.trans h.symm

/-- **The spatial derivative of the inverse diffeotopy.** The differential of `φ_t` undoes the
spatial derivative `d(φ_t⁻¹)` of the inverse diffeotopy at `(x, t)`. -/
theorem mfderiv_timeSlice_mfderiv_cylinderMap_symm_inl (hn : 1 ≤ n) (t : I) (x : M) (u : E) :
    mfderiv J J (Φ.timeSlice t) (Φ.symm (t, x))
        (mfderiv (J.prod (𝓡∂ 1)) J Φ.symm.cylinderMap (x, t)
          (u, (0 : TangentSpace (𝓡∂ 1) t))) = u := by
  rw [← Φ.symm.cylinderMap_apply (x, t)]
  exact (Φ.mfderiv_cylinderMap_inl hn (Φ.symm.cylinderMap (x, t), t) _).symm.trans
    (Φ.mfderiv_cylinderMap_mfderiv_cylinderMap_symm hn (x, t) (u, 0))

end Diffeotopy

end TauCeti
