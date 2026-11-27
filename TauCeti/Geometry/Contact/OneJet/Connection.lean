/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.OneJet
import TauCeti.Geometry.Contact.Pullback
import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Leibniz
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity

/-!
# The one-jet contact form of a connection on the trivial line bundle

Let `M` be a manifold and give the trivial real line bundle `M × ℝ → M` the connection
`∇ = d + a` of a smooth one-form `a`, so that `∇ s = ds + s a` for a function `s`. Its space of
first jets is `J¹ = T*M × ℝ`, with coordinates `(q, p, z)`: a point records a value `z` and a
covariant derivative `p ∈ T*_q M`. On it the tautological fibre coordinates give the one-form

`θ_a = ∇z - p = dz + z a - λ`

(`TauCeti.CotangentBundle.connectionOneJetForm a`), where `λ` is the Liouville form of `T*M`
and `a` is pulled back along the projection `(q, p, z) ↦ q`. For the flat connection `a = 0` it
is the standard contact form `dz - λ` of the one-jet space
(`TauCeti.CotangentBundle.connectionOneJetForm_zero`), in coordinates `dz - Σ pᵢ dqᵢ`.

This file proves that the form depends on the connection only up to a strict contactomorphism.
The **connection shift** `(q, p, z) ↦ (q, p - z a_q, z)`
(`TauCeti.CotangentBundle.connectionShift a`) is a diffeomorphism of `T*M × ℝ`, and the shifts
compose by adding the one-forms (`TauCeti.CotangentBundle.connectionShift_trans`). It pulls
`dz - λ` back to `θ_a`, and more generally `θ_a` back to `θ_(a + b)` for the shift by `b`
(`TauCeti.CotangentBundle.mpullback_connectionShift_connectionOneJetForm`): changing the connection
by the one-form `b` shifts the covariant derivative coordinate by `-z b`. In particular every
`θ_a` is a contact form (`TauCeti.CotangentBundle.isContactForm_connectionOneJetForm`). The
direction of the shift matters: the opposite shift `(q, p, z) ↦ (q, p + z a_q, z)` pulls `dz - λ`
back to `θ_(-a)`, the form of the connection `d - a`.

Changing the trivialization changes the form by a conformal factor. For a smooth nowhere vanishing
function `g` on `M`, the connection `d + a` reads `d + a'` with `a' = a - g⁻¹ dg` in the frame
`e / g`, and a section `z e` with covariant derivative `p e` reads `(g z) (e / g)` with covariant
derivative `(g p) (e / g)`. Accordingly the **frame change** `(q, p, z) ↦ (q, g q p, g q z)`
(`TauCeti.CotangentBundle.connectionFrameChange`), whose composites are the frame changes by the
products (`TauCeti.CotangentBundle.connectionFrameChange_trans`), pulls `θ_(a')` back to `g θ_a`
(`TauCeti.CotangentBundle.mpullback_connectionFrameChange_connectionOneJetForm`), so it is a
contactomorphism from `ker θ_a` to `ker θ_(a')`
(`TauCeti.CotangentBundle.kerDistribution_mpullback_connectionFrameChange_connectionOneJetForm`).

The **covariant one-jet** of a function `g` is the section `q ↦ (dg_q + g q a_q, g q)`: its
covariant derivative coordinate is `∇g`. A section `q ↦ (α_q, g q)` pulls `θ_a` back to
`dg + g a - α` (`TauCeti.CotangentBundle.mpullback_prodMk_connectionOneJetForm`), so it is
horizontal for the contact structure `ker θ_a` exactly when `α = dg + g a`
(`TauCeti.CotangentBundle.isHorizontalMap_connectionOneJetForm_iff`), and covariant one-jets are
Legendrian embeddings (`TauCeti.CotangentBundle.isLegendrianEmbedding_connectionOneJetForm`). For
`g = 0` this is the zero section, which is Legendrian for every connection.

These forms are the local model of the contact form `∇z - p` on the first jets of a real line
bundle with a connection, read in a trivialization of the line bundle; the frame change is the
transition law between two trivializations.

## Main definitions

* `TauCeti.CotangentBundle.connectionOneJetForm a`: the one-form `dz + z a - λ` on `T*M × ℝ`.
* `TauCeti.CotangentBundle.connectionShift a`: the diffeomorphism `(q, p, z) ↦ (q, p - z a_q, z)`.
* `TauCeti.CotangentBundle.connectionFrameChange`: the diffeomorphism
  `(q, p, z) ↦ (q, g q p, g q z)`.

## Main results

* `TauCeti.CotangentBundle.mpullback_connectionShift_connectionOneJetForm`: the shift by `b` pulls
  `θ_a` back to `θ_(a + b)`.
* `TauCeti.CotangentBundle.isContactForm_connectionOneJetForm`: `θ_a` is a contact form.
* `TauCeti.CotangentBundle.mpullback_connectionFrameChange_connectionOneJetForm`: the frame change
  by `g` pulls `θ_(a - g⁻¹ dg)` back to `g θ_a`.
* `TauCeti.CotangentBundle.isHorizontalMap_connectionOneJetForm_iff`: the graph criterion for
  `θ_a`.
* `TauCeti.CotangentBundle.isLegendrianEmbedding_connectionOneJetForm`: covariant one-jets are
  Legendrian embeddings.

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  Springer (1993), §17 (connections and first jets).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Chapter 2 (the space of one-jets and Legendrian submanifolds).
-/

public section

noncomputable section

open Bundle Function Module Manifold
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- The projection `(q, p, z) ↦ q` of the one-jet space `T*M × ℝ` is smooth. -/
private theorem contMDiff_proj_fst :
    ContMDiff ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) I ∞
      fun w : CotangentBundle I M × ℝ ↦ w.1.proj :=
  (contMDiff_proj (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)).comp contMDiff_fst

/-! ### The one-jet form of a connection -/

/-- The **one-jet contact form of the connection `d + a`** on the trivial line bundle over `M`:
the one-form `θ_a = dz + z a - λ` on the one-jet space `T*M × ℝ`, where `z` is the real
coordinate, `λ` the Liouville form of `T*M`, and `a` is pulled back along the projection
`(q, p, z) ↦ q`. It is `∇z - p` for the tautological value `z` and covariant derivative `p`. -/
def connectionOneJetForm (a : SmoothForm I M ℝ 1) :
    SmoothForm ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) (CotangentBundle I M × ℝ) ℝ 1 :=
  (liouvilleForm I M).contactization +
    SmoothForm.funSMulₗ ContMDiffMap.snd
      (SmoothForm.mpullback (fun w : CotangentBundle I M × ℝ ↦ w.1.proj) contMDiff_proj_fst a)

/-- The one-jet form of `d + a` is the sum of `dz - λ` and the pullback of `a` to `T*M × ℝ`
multiplied by the coordinate `z`. -/
theorem connectionOneJetForm_def (a : SmoothForm I M ℝ 1) :
    connectionOneJetForm a = (liouvilleForm I M).contactization +
      SmoothForm.funSMulₗ ContMDiffMap.snd
        (SmoothForm.mpullback (fun w : CotangentBundle I M × ℝ ↦ w.1.proj)
          ((contMDiff_proj (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)).comp contMDiff_fst) a) :=
  (rfl)

/-- The one-jet form of `d + a` evaluates a tangent vector `v` at `w = (q, p, z)` as `dz - λ`
does, plus `z` times `a` on the image of `v` in `T_q M`. -/
@[simp]
theorem connectionOneJetForm_apply (a : SmoothForm I M ℝ 1) (w : CotangentBundle I M × ℝ)
    (v : TangentSpace ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) w) :
    (connectionOneJetForm a).val w ![v] =
      (liouvilleForm I M).contactization.val w ![v] +
        w.2 * a.val w.1.proj ![mfderiv ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) I
          (fun w : CotangentBundle I M × ℝ ↦ w.1.proj) w v] := by
  rw [connectionOneJetForm_def, SmoothForm.add_toRoughForm, Pi.add_apply,
    ContinuousAlternatingMap.add_apply, SmoothForm.coe_funSMulₗ,
    ContinuousAlternatingMap.smul_apply, SmoothForm.mpullback_apply_one, smul_eq_mul,
    ContMDiffMap.snd_apply]

/-- For the flat connection `d`, the one-jet form is the standard contact form `dz - λ` of the
one-jet space. -/
@[simp]
theorem connectionOneJetForm_zero :
    connectionOneJetForm (0 : SmoothForm I M ℝ 1) = (liouvilleForm I M).contactization := by
  rw [connectionOneJetForm_def, map_zero, map_zero, add_zero]

/-! ### Change of connection -/

/-- The connection shift is smooth. -/
private theorem contMDiff_connectionShift (a : SmoothForm I M ℝ 1) :
    ContMDiff ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) ∞
      fun w : CotangentBundle I M × ℝ ↦
        ((TotalSpace.mk' (E →L[ℝ] ℝ) w.1.proj
          (w.1.snd - w.2 • SmoothForm.degreeOneEquiv a w.1.proj) : CotangentBundle I M), w.2) := by
  -- The covector `p` of `w = (q, p, z)`, as a section along `w ↦ q`.
  have hp : ContMDiff ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      fun w : CotangentBundle I M × ℝ ↦
        (TotalSpace.mk' (E →L[ℝ] ℝ) w.1.proj w.1.snd : CotangentBundle I M) :=
    contMDiff_fst
  -- The covector `z a_q`, as a section along the same map.
  have ha : ContMDiff ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      fun w : CotangentBundle I M × ℝ ↦
        (TotalSpace.mk' (E →L[ℝ] ℝ) w.1.proj (w.2 • SmoothForm.degreeOneEquiv a w.1.proj) :
          CotangentBundle I M) :=
    contMDiff_snd.smul_totalSpace ((SmoothForm.degreeOneEquiv a).contMDiff.comp contMDiff_proj_fst)
  exact (hp.sub_sectionAlong ha).prodMk contMDiff_snd

variable (I) in
/-- The **connection shift** `(q, p, z) ↦ (q, p - z a_q, z)` of the one-jet space `T*M × ℝ`, for a
smooth one-form `a` on `M`. It is a diffeomorphism, with inverse the shift by `-a`
(`TauCeti.CotangentBundle.connectionShift_symm`), and it pulls the one-jet form of a connection
`d + b` back to that of `d + b + a`
(`TauCeti.CotangentBundle.mpullback_connectionShift_connectionOneJetForm`). -/
def connectionShift (a : SmoothForm I M ℝ 1) :
    (CotangentBundle I M × ℝ) ≃ₘ⟮(I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ),
      (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)⟯ (CotangentBundle I M × ℝ) where
  toFun w := ((TotalSpace.mk' (E →L[ℝ] ℝ) w.1.proj
    (w.1.snd - w.2 • SmoothForm.degreeOneEquiv a w.1.proj) : CotangentBundle I M), w.2)
  invFun w := ((TotalSpace.mk' (E →L[ℝ] ℝ) w.1.proj
    (w.1.snd - w.2 • SmoothForm.degreeOneEquiv (-a) w.1.proj) : CotangentBundle I M), w.2)
  left_inv w := by simp
  right_inv w := by simp
  contMDiff_toFun := contMDiff_connectionShift a
  contMDiff_invFun := contMDiff_connectionShift (-a)

/-- The connection shift by `a` subtracts `z a_q` from the covector of `(q, p, z)`. -/
@[simp]
theorem connectionShift_apply (a : SmoothForm I M ℝ 1) (w : CotangentBundle I M × ℝ) :
    connectionShift I a w =
      (TotalSpace.mk' (E →L[ℝ] ℝ) w.1.proj
        (w.1.snd - w.2 • SmoothForm.degreeOneEquiv a w.1.proj), w.2) :=
  (rfl)

/-- The connection shift by `a` changes the covector `p` of `(q, p, z)` to `p - z a_q`. -/
theorem connectionShift_fst_snd_apply (a : SmoothForm I M ℝ 1) (w : CotangentBundle I M × ℝ)
    (x : TangentSpace I w.1.proj) :
    (connectionShift I a w).1.snd x = w.1.snd x - w.2 * a.val w.1.proj ![x] := by
  rw [connectionShift_apply]
  simp

/-- The inverse of the connection shift by `a` is the shift by `-a`. -/
@[simp]
theorem connectionShift_symm (a : SmoothForm I M ℝ 1) :
    (connectionShift I a).symm = connectionShift I (-a) :=
  Diffeomorph.ext fun _ ↦ rfl

/-- The connection shift by the zero one-form is the identity. -/
@[simp]
theorem connectionShift_zero :
    connectionShift I (0 : SmoothForm I M ℝ 1) =
      Diffeomorph.refl ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) (CotangentBundle I M × ℝ) ∞ :=
  Diffeomorph.ext fun w ↦ by simp

/-- Successive connection shifts add the one-forms. -/
@[simp]
theorem connectionShift_trans (a b : SmoothForm I M ℝ 1) :
    (connectionShift I a).trans (connectionShift I b) = connectionShift I (a + b) :=
  Diffeomorph.ext fun w ↦ by simp [sub_sub, smul_add]

/-- A smooth map `ψ : T*M × ℝ → T*M` over the projection `(q, p, z) ↦ q` pulls the Liouville
form back to the form evaluating a tangent vector through `ψ` on its image in `T_q M`. -/
private theorem mpullback_liouvilleForm_apply_of_proj_fst
    (ψ : CotangentBundle I M × ℝ → CotangentBundle I M)
    (hψ : ContMDiff ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ ψ)
    (hψπ : ∀ w, (ψ w).proj = w.1.proj) (w : CotangentBundle I M × ℝ)
    (v : Fin 1 → TangentSpace ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) w) :
    (SmoothForm.mpullback ψ hψ (liouvilleForm I M)).val w v =
      (ψ w).snd (mfderiv ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) I
        (fun w : CotangentBundle I M × ℝ ↦ w.1.proj) w (v 0)) := by
  rw [SmoothForm.coe_mpullback]
  exact mpullback_liouvilleForm_apply_of_proj_comp_eq hψπ ((hψ w).mdifferentiableAt (by simp)) v

/-- The connection shift by `a` pulls the Liouville form, read on the first factor of
`T*M × ℝ`, back to `λ - z a`: it changes the covector `p` of `(q, p, z)` by `-z a_q` and fixes
`q`. -/
private theorem mpullback_connectionShift_mpullback_fst_liouvilleForm (a : SmoothForm I M ℝ 1) :
    SmoothForm.mpullback (connectionShift I a) (connectionShift I a).contMDiff
        (SmoothForm.mpullback Prod.fst contMDiff_fst (liouvilleForm I M)) =
      SmoothForm.mpullback Prod.fst contMDiff_fst (liouvilleForm I M) -
        SmoothForm.funSMulₗ ContMDiffMap.snd
          (SmoothForm.mpullback (fun w : CotangentBundle I M × ℝ ↦ w.1.proj)
            contMDiff_proj_fst a) := by
  rw [SmoothForm.mpullback_mpullback]
  apply Subtype.ext
  funext w
  ext v
  -- Both maps to `T*M` lie over `w ↦ q`, so the Liouville form evaluates through `dπ`.
  have hv : (fun i ↦ mfderiv ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) I
      (fun w : CotangentBundle I M × ℝ ↦ w.1.proj) w (v i)) =
        fun _ ↦ mfderiv ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) I
          (fun w : CotangentBundle I M × ℝ ↦ w.1.proj) w (v 0) :=
    funext fun i ↦ by rw [Subsingleton.elim i 0]
  rw [mpullback_liouvilleForm_apply_of_proj_fst (Prod.fst ∘ connectionShift I a) _ (fun _ ↦ rfl),
    Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply,
    mpullback_liouvilleForm_apply_of_proj_fst Prod.fst contMDiff_fst (fun _ ↦ rfl),
    SmoothForm.coe_funSMulₗ,
    ContinuousAlternatingMap.smul_apply, SmoothForm.mpullback_apply, hv]
  rw [Function.comp_apply, connectionShift_fst_snd_apply, Matrix.vec_single_eq_const,
    ContMDiffMap.snd_apply, smul_eq_mul]

/-- **The connection shift turns the flat one-jet form into the one-jet form of a connection.**
The shift `(q, p, z) ↦ (q, p - z a_q, z)` pulls the contact form `dz - λ` back to
`θ_a = dz + z a - λ`. -/
theorem mpullback_connectionShift_contactization_liouvilleForm (a : SmoothForm I M ℝ 1) :
    SmoothForm.mpullback (connectionShift I a) (connectionShift I a).contMDiff
        (liouvilleForm I M).contactization = connectionOneJetForm a := by
  -- The shift fixes the coordinate `z`, so it fixes `dz`.
  have hdz : SmoothForm.mpullback (connectionShift I a) (connectionShift I a).contMDiff
      (SmoothForm.mpullback Prod.snd contMDiff_snd SmoothForm.realLineCoordForm) =
        SmoothForm.mpullback Prod.snd contMDiff_snd SmoothForm.realLineCoordForm := by
    rw [SmoothForm.mpullback_mpullback]
    rfl
  rw [SmoothForm.contactization_def, map_sub, hdz,
    mpullback_connectionShift_mpullback_fst_liouvilleForm, connectionOneJetForm_def,
    SmoothForm.contactization_def]
  abel

/-- **Change of connection.** The connection shift by `b`, `(q, p, z) ↦ (q, p - z b_q, z)`, pulls
the one-jet form `θ_a` of the connection `d + a` back to the one-jet form `θ_(a + b)` of
`d + a + b`. So the one-jet forms of two connections on the trivial line bundle are identified by
a strict contactomorphism, the shift by their difference. -/
theorem mpullback_connectionShift_connectionOneJetForm (a b : SmoothForm I M ℝ 1) :
    SmoothForm.mpullback (connectionShift I b) (connectionShift I b).contMDiff
        (connectionOneJetForm a) = connectionOneJetForm (a + b) := by
  rw [← mpullback_connectionShift_contactization_liouvilleForm a, ← SmoothForm.mpullback_trans,
    connectionShift_trans, add_comm, mpullback_connectionShift_contactization_liouvilleForm]

/-- **The one-jet form of a connection is a contact form.** For every smooth one-form `a`, the
form `θ_a = dz + z a - λ` on `T*M × ℝ` is a contact form: it is the pullback of the contact form
`dz - λ` by the connection shift by `a`, a diffeomorphism. -/
theorem isContactForm_connectionOneJetForm (a : SmoothForm I M ℝ 1) :
    (connectionOneJetForm a).IsContactForm := by
  rw [← mpullback_connectionShift_contactization_liouvilleForm,
    Diffeomorph.isContactForm_mpullback_iff]
  exact isContactForm_contactization_liouvilleForm

/-! ### Change of trivialization -/

/-- The frame change is smooth. -/
private theorem contMDiff_connectionFrameChange {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g) :
    ContMDiff ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) ∞
      fun w : CotangentBundle I M × ℝ ↦
        ((TotalSpace.mk' (E →L[ℝ] ℝ) w.1.proj (g w.1.proj • w.1.snd) : CotangentBundle I M),
          g w.1.proj * w.2) :=
  ((hg.comp contMDiff_proj_fst).smul_totalSpace contMDiff_fst).prodMk
    ((hg.comp contMDiff_proj_fst).mul contMDiff_snd)

variable (I) in
/-- The **frame change** `(q, p, z) ↦ (q, g q p, g q z)` of the one-jet space `T*M × ℝ`, for a
smooth nowhere vanishing function `g` on `M`. It is the change of coordinates of the first jets
of the trivial line bundle under the change of frame `e ↦ e / g`: a section `z e` is `(g z) (e / g)`
and its covariant derivative `p e` is `(g p) (e / g)`. It pulls the one-jet form of the connection
`d + a - g⁻¹ dg`, the connection `d + a` read in the new frame, back to `g` times the one-jet form
of `d + a` (`TauCeti.CotangentBundle.mpullback_connectionFrameChange_connectionOneJetForm`). -/
def connectionFrameChange {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g) (hg₀ : ∀ x, g x ≠ 0) :
    (CotangentBundle I M × ℝ) ≃ₘ⟮(I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ),
      (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)⟯ (CotangentBundle I M × ℝ) where
  toFun w := ((TotalSpace.mk' (E →L[ℝ] ℝ) w.1.proj (g w.1.proj • w.1.snd) : CotangentBundle I M),
    g w.1.proj * w.2)
  invFun w := ((TotalSpace.mk' (E →L[ℝ] ℝ) w.1.proj ((g w.1.proj)⁻¹ • w.1.snd) :
    CotangentBundle I M), (g w.1.proj)⁻¹ * w.2)
  left_inv w := by simp [smul_smul, hg₀]
  right_inv w := by simp [smul_smul, hg₀]
  contMDiff_toFun := contMDiff_connectionFrameChange hg
  contMDiff_invFun := contMDiff_connectionFrameChange (hg.inv₀ hg₀)

/-- The frame change by `g` multiplies the covector and the value of `(q, p, z)` by `g q`. -/
@[simp]
theorem connectionFrameChange_apply {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g) (hg₀ : ∀ x, g x ≠ 0)
    (w : CotangentBundle I M × ℝ) :
    connectionFrameChange I hg hg₀ w =
      ((TotalSpace.mk' (E →L[ℝ] ℝ) w.1.proj (g w.1.proj • w.1.snd) : CotangentBundle I M),
        g w.1.proj * w.2) :=
  (rfl)

/-- The inverse of the frame change by `g` is the frame change by `g⁻¹`. -/
@[simp]
theorem connectionFrameChange_symm {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (hg₀ : ∀ x, g x ≠ 0) :
    (connectionFrameChange I hg hg₀).symm =
      connectionFrameChange I (hg.inv₀ hg₀) fun x ↦ inv_ne_zero (hg₀ x) :=
  Diffeomorph.ext fun _ ↦ rfl

/-- The frame change by the constant function `1` is the identity. -/
@[simp]
theorem connectionFrameChange_one :
    connectionFrameChange I (contMDiff_const (c := (1 : ℝ))) (fun _ ↦ one_ne_zero) =
      Diffeomorph.refl ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) (CotangentBundle I M × ℝ) ∞ :=
  Diffeomorph.ext fun w ↦ by simp

/-- Successive frame changes multiply the functions. -/
@[simp]
theorem connectionFrameChange_trans {g h : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (hg₀ : ∀ x, g x ≠ 0) (hh : ContMDiff I 𝓘(ℝ) ∞ h) (hh₀ : ∀ x, h x ≠ 0) :
    (connectionFrameChange I hg hg₀).trans (connectionFrameChange I hh hh₀) =
      connectionFrameChange I (hh.mul hg) fun x ↦ mul_ne_zero (hh₀ x) (hg₀ x) :=
  Diffeomorph.ext fun w ↦ by simp [smul_smul, mul_assoc]

/-- The frame change by `g` multiplies `z` by `g q`, so by the Leibniz rule it pulls `dz` back to
`g dz + z dg`, where `g` and `dg` are read at the base point. -/
private theorem mpullback_connectionFrameChange_mpullback_snd_realLineCoordForm {g : M → ℝ}
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) (hg₀ : ∀ x, g x ≠ 0) (w : CotangentBundle I M × ℝ) :
    (SmoothForm.mpullback (connectionFrameChange I hg hg₀)
        (connectionFrameChange I hg hg₀).contMDiff
        (SmoothForm.mpullback Prod.snd contMDiff_snd SmoothForm.realLineCoordForm)).val w =
      g w.1.proj • (SmoothForm.mpullback Prod.snd contMDiff_snd
          SmoothForm.realLineCoordForm).val w +
        w.2 • TauCeti.mpullback ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) I
          (fun w : CotangentBundle I M × ℝ ↦ w.1.proj)
          (mextDeriv (RoughForm.ofFunction I g)) w := by
  have hP := contMDiff_proj_fst (I := I) (M := M)
  -- The coordinate `z` of the image is `g q * z`, by the definition of the frame change.
  have hmul : Prod.snd ∘ connectionFrameChange I hg hg₀ =
      (g ∘ fun w : CotangentBundle I M × ℝ ↦ w.1.proj) * Prod.snd :=
    rfl
  rw [SmoothForm.mpullback_mpullback, SmoothForm.coe_mpullback,
    SmoothForm.mpullback_realLineCoordForm, SmoothForm.coe_mpullback,
    SmoothForm.mpullback_realLineCoordForm, hmul,
    mextDeriv_ofFunction_mul (((hg.comp hP) w).mdifferentiableAt (by simp)) mdifferentiableAt_snd,
    mpullback_mextDeriv_ofFunction (hP.mdifferentiable (by simp)) (hg.mdifferentiable (by simp)),
    Function.comp_apply]

/-- The frame change by `g` multiplies the covector by `g q` and fixes `q`, so it pulls the
Liouville form, read on the first factor of `T*M × ℝ`, back to `g λ`. -/
private theorem mpullback_connectionFrameChange_mpullback_fst_liouvilleForm {g : M → ℝ}
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) (hg₀ : ∀ x, g x ≠ 0) (w : CotangentBundle I M × ℝ) :
    (SmoothForm.mpullback (connectionFrameChange I hg hg₀)
        (connectionFrameChange I hg hg₀).contMDiff
        (SmoothForm.mpullback Prod.fst contMDiff_fst (liouvilleForm I M))).val w =
      g w.1.proj • (SmoothForm.mpullback Prod.fst contMDiff_fst (liouvilleForm I M)).val w := by
  rw [SmoothForm.mpullback_mpullback]
  ext v
  rw [ContinuousAlternatingMap.smul_apply,
    mpullback_liouvilleForm_apply_of_proj_fst (Prod.fst ∘ connectionFrameChange I hg hg₀) _
      (fun _ ↦ rfl),
    mpullback_liouvilleForm_apply_of_proj_fst Prod.fst contMDiff_fst (fun _ ↦ rfl),
    Function.comp_apply, connectionFrameChange_apply, smul_apply]

/-- **Change of trivialization.** Let `g` be a smooth nowhere vanishing function on `M`, and let
`a' = a - g⁻¹ dg` be the connection form of `d + a` in the frame `e / g`. Then the frame change
`(q, p, z) ↦ (q, g q p, g q z)` pulls the one-jet form `θ_(a')` back to `g θ_a`, where `g` is read
at the base point. So it is a contactomorphism from `ker θ_a` to `ker θ_(a')`, not a strict one. -/
theorem mpullback_connectionFrameChange_connectionOneJetForm {g : M → ℝ}
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) (hg₀ : ∀ x, g x ≠ 0) {a a' : SmoothForm I M ℝ 1}
    (ha' : a'.val = a.val - fun x ↦ (g x)⁻¹ • mextDeriv (RoughForm.ofFunction I g) x)
    (w : CotangentBundle I M × ℝ) :
    (SmoothForm.mpullback (connectionFrameChange I hg hg₀)
        (connectionFrameChange I hg hg₀).contMDiff (connectionOneJetForm a')).val w =
      g w.1.proj • (connectionOneJetForm a).val w := by
  set Ψ := connectionFrameChange I hg hg₀
  have hP := contMDiff_proj_fst (I := I) (M := M)
  -- The differential of `g q` on `T*M × ℝ`.
  set D := TauCeti.mpullback ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) I
    (fun w : CotangentBundle I M × ℝ ↦ w.1.proj) (mextDeriv (RoughForm.ofFunction I g))
  -- The frame change fixes `q` and multiplies `z` by `g q`, so it pulls `z a'` back to `g z a'`.
  have hβ : (SmoothForm.mpullback Ψ Ψ.contMDiff (SmoothForm.funSMulₗ ContMDiffMap.snd
      (SmoothForm.mpullback (fun w : CotangentBundle I M × ℝ ↦ w.1.proj) hP a'))).val w =
        (g w.1.proj * w.2) •
          ((SmoothForm.mpullback (fun w : CotangentBundle I M × ℝ ↦ w.1.proj) hP a).val w -
            (g w.1.proj)⁻¹ • D w) := by
    -- The frame change fixes the base point `q`.
    have hπ : (fun w : CotangentBundle I M × ℝ ↦ w.1.proj) ∘ Ψ = fun w ↦ w.1.proj := rfl
    rw [SmoothForm.coe_mpullback, SmoothForm.coe_funSMulₗ, mpullback_fun_smul,
      ← SmoothForm.coe_mpullback Ψ Ψ.contMDiff, SmoothForm.mpullback_mpullback,
      SmoothForm.coe_mpullback, SmoothForm.coe_mpullback, ha', mpullback_sub, mpullback_fun_smul,
      hπ]
    simp only [Ψ, ContMDiffMap.snd_apply, connectionFrameChange_apply, Pi.sub_apply, D]
  simp only [connectionOneJetForm_def, SmoothForm.contactization_def, map_add, map_sub,
    Submodule.coe_add, Submodule.coe_sub, Pi.add_apply, Pi.sub_apply]
  rw [mpullback_connectionFrameChange_mpullback_snd_realLineCoordForm,
    mpullback_connectionFrameChange_mpullback_fst_liouvilleForm, hβ, SmoothForm.coe_funSMulₗ]
  -- The terms `z dg` cancel, as `g q * z * (g q)⁻¹ = z`.
  have hc : g w.1.proj * w.2 * (g w.1.proj)⁻¹ = w.2 := by field_simp [hg₀ w.1.proj]
  simp only [ContMDiffMap.snd_apply, smul_add, smul_sub, smul_smul, hc]
  abel

/-- The frame change by `g` carries the contact structure `ker θ_a` onto `ker θ_(a')`, for the
connection form `a' = a - g⁻¹ dg` of `d + a` in the frame `e / g`. -/
theorem kerDistribution_mpullback_connectionFrameChange_connectionOneJetForm {g : M → ℝ}
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) (hg₀ : ∀ x, g x ≠ 0) {a a' : SmoothForm I M ℝ 1}
    (ha' : a'.val = a.val - fun x ↦ (g x)⁻¹ • mextDeriv (RoughForm.ofFunction I g) x) :
    (SmoothForm.mpullback (connectionFrameChange I hg hg₀)
        (connectionFrameChange I hg hg₀).contMDiff (connectionOneJetForm a')).kerDistribution =
      (connectionOneJetForm a).kerDistribution :=
  SmoothForm.kerDistribution_of_eq_smul (f := fun w ↦ g w.1.proj) (fun w ↦ hg₀ w.1.proj)
    (mpullback_connectionFrameChange_connectionOneJetForm hg hg₀ ha')

/-! ### Covariant one-jets -/

/-- For smooth one-forms `a` and `α` and a smooth function `g` on `M`, the section
`q ↦ (α_q, g q)` of the one-jet space pulls the one-jet form `θ_a` of `d + a` back to
`dg + g a - α`. -/
theorem mpullback_prodMk_connectionOneJetForm (a α : SmoothForm I M ℝ 1) {g : M → ℝ}
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) :
    (SmoothForm.mpullback
        (fun x ↦ (TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x), g x))
        ((SmoothForm.degreeOneEquiv α).contMDiff.prodMk hg) (connectionOneJetForm a)).val =
      mextDeriv (RoughForm.ofFunction I g) + (fun x ↦ g x • a.val x) - α.val := by
  set j : M → CotangentBundle I M × ℝ :=
    fun x ↦ (TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x), g x)
  have hj : ContMDiff I ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) ∞ j :=
    (SmoothForm.degreeOneEquiv α).contMDiff.prodMk hg
  -- The section lies over the identity of `M`, so it pulls the forms `a` on `T*M × ℝ` back to `a`,
  -- and its coordinate `z` is `g`.
  have ha : SmoothForm.mpullback j hj
      (SmoothForm.mpullback (fun w : CotangentBundle I M × ℝ ↦ w.1.proj) contMDiff_proj_fst a) =
        a := by
    rw [SmoothForm.mpullback_mpullback,
      SmoothForm.mpullback_congr (f := (fun w : CotangentBundle I M × ℝ ↦ w.1.proj) ∘ j) _
        contMDiff_id rfl,
      SmoothForm.mpullback_id, LinearMap.id_apply]
  have hz : (SmoothForm.mpullback j hj (SmoothForm.funSMulₗ ContMDiffMap.snd
      (SmoothForm.mpullback (fun w : CotangentBundle I M × ℝ ↦ w.1.proj) contMDiff_proj_fst
        a))).val = fun x ↦ g x • a.val x := by
    rw [SmoothForm.coe_mpullback, SmoothForm.coe_funSMulₗ, mpullback_fun_smul,
      ← SmoothForm.coe_mpullback j hj, ha]
    simp only [ContMDiffMap.snd_apply, j]
  rw [connectionOneJetForm_def, map_add, SmoothForm.add_toRoughForm, hz,
    SmoothForm.mpullback_prodMk_contactization _ (SmoothForm.degreeOneEquiv α).contMDiff hg,
    mpullback_liouvilleForm]
  abel

/-- **The graph criterion for the one-jet form of a connection.** For smooth one-forms `a` and
`α` and a smooth function `g` on `M`, the section `q ↦ (α_q, g q)` of the one-jet space is
horizontal for the kernel of `θ_a = dz + z a - λ` exactly when `α = dg + g a`, that is when its
covector coordinate is the covariant derivative of `g` for the connection `d + a`. -/
theorem isHorizontalMap_connectionOneJetForm_iff (a α : SmoothForm I M ℝ 1) {g : M → ℝ}
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) :
    IsHorizontalMap I (connectionOneJetForm a).kerDistribution
        (fun x ↦ (TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x), g x)) ↔
      α.val = mextDeriv (RoughForm.ofFunction I g) + fun x ↦ g x • a.val x := by
  rw [SmoothForm.isHorizontalMap_kerDistribution_iff_mpullback_eq_zero _
      ((SmoothForm.degreeOneEquiv α).contMDiff.prodMk hg), Subtype.ext_iff,
    mpullback_prodMk_connectionOneJetForm a α hg, ZeroMemClass.coe_zero, sub_eq_zero, eq_comm]

/-- For a smooth function `g`, the section `q ↦ (α_q, g q)` of the one-jet space defined by a
smooth one-form `α` is a Legendrian embedding for the one-jet form of the connection `d + a`
exactly when `α = dg + g a`. -/
theorem isLegendrianEmbedding_connectionOneJetForm_iff [FiniteDimensional ℝ E] [I.Boundaryless]
    (a α : SmoothForm I M ℝ 1) {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g) :
    IsLegendrianEmbedding I (connectionOneJetForm a).kerDistribution
        (fun x ↦ (TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x), g x)) ↔
      α.val = mextDeriv (RoughForm.ofFunction I g) + fun x ↦ g x • a.val x :=
  (isLegendrianEmbedding_iff_isHorizontalMap (isContactForm_connectionOneJetForm a) α hg).trans
    (isHorizontalMap_connectionOneJetForm_iff a α hg)

/-- **Covariant one-jets are Legendrian.** For a smooth one-form `a` and a smooth function `g` on
`M`, let `α = dg + g a` be the covariant derivative of `g` for the connection `d + a`. Then the
covariant one-jet `q ↦ (α_q, g q)` is a Legendrian embedding of `M` into the one-jet space
`T*M × ℝ` with the contact form `θ_a = dz + z a - λ`. For `g = 0` and `α = 0` this is the zero
section, which is Legendrian for every connection. -/
theorem isLegendrianEmbedding_connectionOneJetForm [FiniteDimensional ℝ E] [I.Boundaryless]
    (a α : SmoothForm I M ℝ 1) {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (hα : α.val = mextDeriv (RoughForm.ofFunction I g) + fun x ↦ g x • a.val x) :
    IsLegendrianEmbedding I (connectionOneJetForm a).kerDistribution
      (fun x ↦ (TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x), g x)) :=
  (isLegendrianEmbedding_connectionOneJetForm_iff a α hg).2 hα

end CotangentBundle

end TauCeti
