/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ActionAngle
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.LatticeQuotient

import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# Global action–angle coordinates on the torus bundle of an exact coframe

Let `B` be a boundaryless Hausdorff manifold modelled on a finite-dimensional space, let `p > 0`,
and let `a : B → ℝ^ι` be a smooth map whose differentials, scaled by `p`, form a global frame
`α i = p • d a_i` of `T*B`. These are the period one-forms of a lattice `Λ ⊂ T*B` which are exact,
with the global *developing map* `a`. The quotient `T*B/Λ`
(`TauCeti.CotangentBundle.LatticeQuotient α hα`) is the regular Lagrangian torus fibration of this
lattice, with the symplectic form descended from `ω = -dλ`. This file constructs global
action–angle coordinates on it.

A covector `ξ` over `x` has coordinates `c(ξ)` in the frame, `ξ = ∑ i, c_i(ξ) α_i x`. Write
`κ(θ, I) = ∑ j, I_j dθ_j` at `[θ]` for the action–angle covering map of the cotangent bundle
`T*Tⁿ` of the torus `Tⁿ = ι → AddCircle p` (`TauCeti.CotangentBundle.actionAngleCover`). The
**action–angle chart** (`TauCeti.CotangentBundle.LatticeQuotient.actionAngleChart`) is

`Φ([ξ]) = κ(-p c(ξ), a(x))`.

The lattice translations shift `c` by integer vectors, which `κ` absorbs since it is
`p`-periodic in the angles, so `Φ` is well defined on `T*B/Λ`. Its actions are the values of the
developing map, `Φ(z)(e_i) = a_i(π z)` (`actionAngleChart_snd_apply_single`), and:

* `Φ` is a local diffeomorphism (`isLocalDiffeomorph_actionAngleChart`);
* `Φ` pulls the canonical form of `T*Tⁿ` back to the symplectic form of `T*B/Λ`
  (`mpullback_actionAngleChart_symplecticForm`);
* `Φ` is injective exactly when `a` is (`actionAngleChart_injective_iff`);
* its range is the set of covectors whose actions are values of `a`
  (`range_actionAngleChart`).

So when the developing map is injective, `Φ`, an open map as a local diffeomorphism, is a
symplectomorphism of `T*B/Λ` onto the open subset of `T*Tⁿ` of covectors with actions in
`a(B) ⊆ ℝ^ι`, in which `ω = ∑ j, dθ_j ∧ dI_j` and the projection `T*B/Λ → B` reads `I = a`. When
`a` is not injective, neither is `Φ`: two points of `B` with the same value of `a` give distinct
fibres of `T*B/Λ` with the same image.

The symplectic identity is proved on the cover `ℝ^ι × B → T*B`, `(c, x) ↦ ∑ i, c_i α_i x`. There
the Liouville forms are related by `Ψ^* λ = G^* λ + d (p c ⬝ a)`, where `Ψ` is this cover and
`G(c, x) = κ(-p c, a(x))`, so the canonical forms `ω = -dλ` agree after pullback.

## Main definitions

* `TauCeti.CotangentBundle.LatticeQuotient.actionAngleChart`: the action–angle chart `Φ`.

## Main results

* `actionAngleChart_snd_apply_single`: the actions of `Φ(z)` are `a(π z)`.
* `contMDiff_actionAngleChart`, `isLocalDiffeomorph_actionAngleChart`: `Φ` is a smooth local
  diffeomorphism.
* `mpullback_actionAngleChart_symplecticForm`: `Φ` is symplectic.
* `actionAngleChart_injective_iff`, `range_actionAngleChart`: `Φ` is injective exactly when `a`
  is, with image the covectors whose actions lie in `a(B)`.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706 (the period lattice `Λ ⊂ T*B`, the torus bundle `T*B/Λ` and the obstructions to global
  action–angle coordinates).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (action–angle variables).
-/

public section

noncomputable section

open Bundle Set Function
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

namespace LatticeQuotient

open LatticeCover

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {B : Type*} [TopologicalSpace B] [ChartedSpace H B]
  [IsManifold I ∞ B] {ι : Type*} [Fintype ι] {α : ι → SmoothForm I B ℝ 1}
  (hα : IsLocalFrameOn I (E →L[ℝ] ℝ) ∞ (fun i x ↦ SmoothForm.degreeOneEquiv (α i) x) univ)
  (p : ℝ) [Fact (0 < p)] (a : B → ι → ℝ)

/-! ### The action–angle chart -/

/-- The action–angle chart, read on a covector `ξ` of `T*B`: `κ(-p c(ξ), a(π ξ))`, where `c(ξ)` are
the coordinates of `ξ` in the frame. -/
private def chartCover (z : CotangentBundle I B) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p) :=
  actionAngleCover p (-(p • coord hα z), a z.proj)

/-- Translating a covector by a lattice vector does not change its action–angle chart. -/
private theorem chartCover_add_sum (x : B) (q : TangentSpace I x →L[ℝ] ℝ) (k : ι → ℤ) :
    chartCover hα p a ⟨x, q + ∑ i, (k i : ℝ) • SmoothForm.degreeOneEquiv (α i) x⟩ =
      chartCover hα p a ⟨x, q⟩ := by
  simp only [chartCover, coord_add_sum hα x q k]
  rw [← actionAngleCover_add_intCast_mul p (-(p • coord hα ⟨x, q⟩)) (a x) (-k)]
  congr 2
  ext i
  simp only [Pi.neg_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Int.cast_neg]
  ring

/-- **The action–angle chart** `Φ : T*B/Λ → T*Tⁿ` of the torus bundle of a frame `α`, for the torus
`Tⁿ = ι → AddCircle p` and a map `a : B → ℝ^ι`. It sends the class of a covector `ξ` over `x`,
with coordinates `c(ξ)` in the frame, to the covector `κ(-p c(ξ), a(x)) = ∑ j, a_j(x) dθ_j` at the
point `[-p c(ξ)]` of the torus. It is well defined because the lattice translations shift `c(ξ)` by
integer vectors. When `a` is smooth and `α i = p • d a_i`, it is a symplectic local
diffeomorphism, and it is injective exactly when `a` is. -/
def actionAngleChart (z : LatticeQuotient α hα) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p) :=
  Quotient.liftOn z (fun w ↦ chartCover hα p a ((ofCotangent hα).symm w)) fun z w h ↦ by
    have hzw : mk hα ((ofCotangent hα).symm z) = mk hα ((ofCotangent hα).symm w) := by
      simpa only [mk_def, Equiv.apply_symm_apply] using Quotient.sound h
    obtain ⟨k, hk⟩ := (mk_eq_mk_iff hα).1 hzw
    rw [hk]
    exact chartCover_add_sum hα p a _ _ k

/-- The action–angle chart of the class of a covector `ξ` is `κ(-p c(ξ), a(π ξ))`, where `c(ξ)` are
the coordinates of `ξ` in the frame. -/
@[simp]
theorem actionAngleChart_mk (z : CotangentBundle I B) :
    actionAngleChart hα p a (mk hα z) = actionAngleCover p (-(p • coord hα z), a z.proj) := by
  rw [mk_def]
  exact congrArg (chartCover hα p a) ((ofCotangent hα).symm_apply_apply z)

/-- The action–angle chart of the class of `∑ j, c_j α_j x` is `κ(-p c, a(x))`. -/
theorem actionAngleChart_mk_sum_smul (x : B) (c : ι → ℝ) :
    actionAngleChart hα p a
        (mk hα (TotalSpace.mk' (E →L[ℝ] ℝ) x (∑ j, c j • SmoothForm.degreeOneEquiv (α j) x))) =
      actionAngleCover p (-(p • c), a x) := by
  rw [actionAngleChart_mk]
  congr 4
  funext i
  rw [coord_apply]
  exact hα.coeff_sum_smul (mem_univ x) c i

/-- **The actions of the action–angle chart are the values of `a`**: the covector `Φ(z)` takes the
value `a_i(π z)` on the `i`-th coordinate vector of the torus. -/
@[simp]
theorem actionAngleChart_snd_apply_single [DecidableEq ι] (z : LatticeQuotient α hα) (i : ι) :
    (actionAngleChart hα p a z).snd (Pi.single i 1) = a (proj hα z) i := by
  obtain ⟨z, rfl⟩ := mk_surjective hα z
  rw [actionAngleChart_mk, actionAngleCover_snd_apply_single, proj_mk]

/-! ### The cover by frame coordinates -/

variable (α) in
/-- The cover `Ψ(c, x) = ∑ j, c_j α_j x` of `T*B` by frame coordinates. -/
private def frameCover (x : (ι → ℝ) × B) : CotangentBundle I B :=
  TotalSpace.mk' (E →L[ℝ] ℝ) x.2 (∑ j, x.1 j • SmoothForm.degreeOneEquiv (α j) x.2)

/-- The covector `Ψ(c, x)` evaluates a tangent vector `w` at `x` as `∑ j, c_j α_j x w`. -/
private theorem frameCover_snd_apply (x : (ι → ℝ) × B) (w : E) :
    (frameCover α x).snd w = ∑ j, x.1 j * SmoothForm.degreeOneEquiv (α j) x.2 w := by
  -- Read `w` as a tangent vector at `x.2`, so that `sum_apply` applies to the covectors on
  -- `TangentSpace I x.2`; each summand `(c • φ) w = c * φ w` then holds by definition.
  let w' : TangentSpace I x.2 := w
  exact (sum_apply Finset.univ
    (fun j ↦ x.1 j • SmoothForm.degreeOneEquiv (α j) x.2) w').trans
    (Finset.sum_congr rfl fun j _ ↦ rfl)

/-- The cover by frame coordinates is smooth: it is `contMDiff_sum_smul` with the factors of
the product swapped. -/
private theorem contMDiff_frameCover :
    ContMDiff (𝓘(ℝ, ι → ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (frameCover α) :=
  (contMDiff_sum_smul (α := α)).comp (contMDiff_snd.prodMk contMDiff_fst)

/-- The angles and actions `(-p c, a(x))` of the action–angle chart at `Ψ(c, x)`. -/
private def anglesActions (x : (ι → ℝ) × B) : (ι → ℝ) × (ι → ℝ) := (-(p • x.1), a x.2)

variable {a}

omit [IsManifold I ∞ B] [Fact (0 < p)] in
/-- The map `(c, x) ↦ (-p c, a(x))` is smooth. -/
private theorem contMDiff_anglesActions (ha : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ a) :
    ContMDiff (𝓘(ℝ, ι → ℝ).prod I) 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) ∞ (anglesActions p a) :=
  ((-(p • ContinuousLinearMap.id ℝ (ι → ℝ))).contMDiff.comp contMDiff_fst).prodMk_space
    (ha.comp contMDiff_snd)

omit [IsManifold I ∞ B] [Fact (0 < p)] in
/-- The map `(c, x) ↦ (-p c, a(x))` has derivative `(u, w) ↦ (-p u, da_x w)`. -/
private theorem hasMFDerivAt_anglesActions (ha : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ a)
    (x : (ι → ℝ) × B) :
    HasMFDerivAt (𝓘(ℝ, ι → ℝ).prod I) 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) (anglesActions p a) x
      (((-(p • ContinuousLinearMap.id ℝ (ι → ℝ))).comp
        (ContinuousLinearMap.fst ℝ (ι → ℝ) E)).prod
        ((mfderiv I 𝓘(ℝ, ι → ℝ) a x.2).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) E))) := by
  have h₁ := (-(p • ContinuousLinearMap.id ℝ (ι → ℝ))).hasMFDerivAt.comp x
    (hasMFDerivAt_fst (I := 𝓘(ℝ, ι → ℝ)) (I' := I) x)
  have h₂ := ((ha x.2).mdifferentiableAt (by simp)).hasMFDerivAt.comp x
    (hasMFDerivAt_snd (I := 𝓘(ℝ, ι → ℝ)) (I' := I) x)
  -- The model of `(ι → ℝ) × (ι → ℝ)` is that of a normed space, so the derivatives pair up.
  exact ⟨h₁.1.prodMk h₂.1, h₁.2.prodMk h₂.2⟩

omit [IsManifold I ∞ B] in
/-- The action–angle chart after the cover, `G(c, x) = κ(-p c, a(x))`, is smooth. -/
private theorem contMDiff_actionAngleCover_comp (ha : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ a) :
    ContMDiff (𝓘(ℝ, ι → ℝ).prod I) ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
      𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ (actionAngleCover p ∘ anglesActions p a) :=
  (contMDiff_actionAngleCover p).comp (contMDiff_anglesActions p ha)

/-- The negated pairing `(u, w) ↦ -∑ j, u_j w_j`. -/
private def dotNeg (q : (ι → ℝ) × (ι → ℝ)) : ℝ := -∑ j, q.1 j * q.2 j

/-- The negated pairing is smooth. -/
private theorem contDiff_dotNeg : ContDiff ℝ ∞ (dotNeg (ι := ι)) :=
  (ContDiff.sum fun j _ ↦
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) j).contDiff.comp contDiff_fst).mul
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) j).contDiff.comp
        contDiff_snd)).neg

/-- The function `p (c ⬝ a(x))` whose differential relates the two Liouville forms on the cover. -/
private def pairing (ha : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ a) :
    C^∞⟮𝓘(ℝ, ι → ℝ).prod I, (ι → ℝ) × B; 𝓘(ℝ, ℝ), ℝ⟯ :=
  ⟨dotNeg ∘ anglesActions p a, contDiff_dotNeg.comp_contMDiff (contMDiff_anglesActions p ha)⟩

omit [IsManifold I ∞ B] [Fact (0 < p)] in
/-- The function `pairing` is the negated pairing of `(-p c, a(x))`, that is `p (c ⬝ a(x))`. -/
private theorem coe_pairing (ha : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ a) :
    ⇑(pairing p ha) = dotNeg ∘ anglesActions p a :=
  (rfl)

/-- The derivative `(u', w') ↦ -∑ j, (u_j w'_j + w_j u'_j)` of the negated pairing at `(u, w)`. -/
private def dotNegDeriv (q : (ι → ℝ) × (ι → ℝ)) : (ι → ℝ) × (ι → ℝ) →L[ℝ] ℝ :=
  -∑ j, (q.1 j • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) j).comp
      (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)) +
    q.2 j • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) j).comp
      (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)))

/-- The derivative of the negated pairing at `q` sends `q'` to
`-∑ j, (q.1 j * q'.2 j + q.2 j * q'.1 j)`. -/
private theorem dotNegDeriv_apply (q q' : (ι → ℝ) × (ι → ℝ)) :
    dotNegDeriv q q' = -∑ j, (q.1 j * q'.2 j + q.2 j * q'.1 j) := by
  simp [dotNegDeriv]

/-- The derivative of the negated pairing at `q` is `dotNegDeriv q`. -/
private theorem hasFDerivAt_dotNeg (q : (ι → ℝ) × (ι → ℝ)) :
    HasFDerivAt (dotNeg (ι := ι)) (dotNegDeriv q) q := by
  convert (HasFDerivAt.sum (u := Finset.univ) fun j _ ↦
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) j).hasFDerivAt.comp q
      hasFDerivAt_fst).mul
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) j).hasFDerivAt.comp q
        hasFDerivAt_snd)).neg using 1
  · funext q'
    simp [dotNeg]
  · ext q' <;> simp [dotNegDeriv]

omit [IsManifold I ∞ B] [Fact (0 < p)] in
/-- The differential of `p (c ⬝ a(x))` at `(c, x)` sends `(u, e)` to
`-∑ j, (-p c_j da_j(e) - p a_j(x) u_j)`. -/
private theorem mfderiv_pairing_apply (ha : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ a) (x : (ι → ℝ) × B)
    (w : TangentSpace (𝓘(ℝ, ι → ℝ).prod I) x) :
    mfderiv (𝓘(ℝ, ι → ℝ).prod I) 𝓘(ℝ, ℝ) (pairing p ha) x w =
      -∑ j, (-(p * x.1 j) * mfderiv I 𝓘(ℝ, ι → ℝ) a x.2 w.2 j + a x.2 j * -(p * w.1 j)) := by
  rw [coe_pairing, ((hasFDerivAt_dotNeg (anglesActions p a x)).hasMFDerivAt.comp x
    (hasMFDerivAt_anglesActions p ha x)).mfderiv]
  -- The derivative is `dotNegDeriv (-p c, a x)` applied to the derivative `(-p u, da e)` of the
  -- map `(c, x) ↦ (-p c, a x)`. A tangent vector of the product is a pair in the model space
  -- `(ι → ℝ) × E`, so the coordinates of both pairs are the summands of the right side by
  -- definition.
  exact (ContinuousLinearMap.comp_apply _ _ _).trans (dotNegDeriv_apply _ _)

omit [Fact (0 < p)] in
/-- The exact form `d (p (c ⬝ a(x)))` takes the value `-∑ j, (-p c_j da_j(e) - p a_j(x) u_j)` on
`w = (u, e)`. -/
private theorem mextDerivₗ_pairing_apply (ha : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ a) (x : (ι → ℝ) × B)
    (w : TangentSpace (𝓘(ℝ, ι → ℝ).prod I) x) :
    (mextDerivₗ (𝓘(ℝ, ι → ℝ).prod I) 0 (SmoothForm.ofFunction (pairing p ha))).val x ![w] =
      -∑ j, (-(p * x.1 j) * mfderiv I 𝓘(ℝ, ι → ℝ) a x.2 w.2 j + a x.2 j * -(p * w.1 j)) := by
  rw [mextDerivₗ_zero_apply, SmoothForm.ofFunction_apply_zero, mvfderiv_apply_eq_mfderiv_apply]
  exact mfderiv_pairing_apply p ha x w

omit [Fact (0 < p)] in
/-- The pullback `Ψ^* λ` takes the value `∑ j, c_j α_j(e) = ∑ j, p c_j da_j(e)` on `w = (u, e)`. -/
private theorem mpullback_frameCover_liouvilleForm_apply
    (hαa : ∀ i x v, SmoothForm.degreeOneEquiv (α i) x v = p * mfderiv I 𝓘(ℝ, ι → ℝ) a x v i)
    (x : (ι → ℝ) × B) (w : TangentSpace (𝓘(ℝ, ι → ℝ).prod I) x) :
    (SmoothForm.mpullback (frameCover α) contMDiff_frameCover (liouvilleForm I B)).val x ![w] =
      ∑ j, x.1 j * (p * mfderiv I 𝓘(ℝ, ι → ℝ) a x.2 w.2 j) := by
  rw [SmoothForm.coe_mpullback, mpullback_liouvilleForm_apply_of_proj_comp_eq (g := Prod.snd)
      (fun _ ↦ rfl) ((contMDiff_frameCover x).mdifferentiableAt (by simp)), Matrix.cons_val_zero,
    mfderiv_snd]
  exact (frameCover_snd_apply x w.2).trans
    (Finset.sum_congr rfl fun j _ ↦ congrArg (x.1 j * ·) (hαa j x.2 w.2))

/-- The pullback `G^* λ` takes the value `∑ j, a_j(x) (-p u_j)` on `w = (u, e)`. -/
private theorem mpullback_actionAngleCover_comp_liouvilleForm_apply
    (ha : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ a) (x : (ι → ℝ) × B)
    (w : TangentSpace (𝓘(ℝ, ι → ℝ).prod I) x) :
    (SmoothForm.mpullback (actionAngleCover p ∘ anglesActions p a)
        (contMDiff_actionAngleCover_comp p ha)
        (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))).val x ![w] =
      ∑ j, a x.2 j * -(p * w.1 j) := by
  rw [← SmoothForm.mpullback_mpullback _ _ (contMDiff_anglesActions p ha)
      (contMDiff_actionAngleCover p), SmoothForm.mpullback_apply_one, SmoothForm.coe_mpullback,
    mpullback_liouvilleForm_actionAngleCover_apply, (hasMFDerivAt_anglesActions p ha x).mfderiv]
  -- The derivative `(u, e) ↦ (-p u, da_x e)` has first coordinates `-(p * u_j)` by definition.
  rfl

variable {p}

/-- **The Liouville forms on the cover.** The cover `Ψ` and the chart after the cover
`G = κ ∘ (c, x) ↦ (-p c, a(x))` pull the Liouville forms back to forms differing by an exact
form: `Ψ^* λ = G^* λ + d (p (c ⬝ a(x)))`. -/
private theorem mpullback_frameCover_liouvilleForm (ha : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ a)
    (hαa : ∀ i x v, SmoothForm.degreeOneEquiv (α i) x v = p * mfderiv I 𝓘(ℝ, ι → ℝ) a x v i) :
    SmoothForm.mpullback (frameCover α) contMDiff_frameCover (liouvilleForm I B) =
      SmoothForm.mpullback (actionAngleCover p ∘ anglesActions p a)
          (contMDiff_actionAngleCover_comp p ha)
          (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) +
        mextDerivₗ (𝓘(ℝ, ι → ℝ).prod I) 0 (SmoothForm.ofFunction (pairing p ha)) := by
  refine SmoothBundleForm.ext fun x v ↦ ?_
  obtain ⟨w, rfl⟩ : ∃ w, v = ![w] := ⟨v 0, by ext i; fin_cases i; rfl⟩
  rw [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply,
    mpullback_frameCover_liouvilleForm_apply p hαa,
    mpullback_actionAngleCover_comp_liouvilleForm_apply p ha,
    mextDerivₗ_pairing_apply p ha, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **The canonical forms on the cover.** The cover `Ψ` and the chart after the cover
`G = κ ∘ (c, x) ↦ (-p c, a(x))` pull the canonical symplectic forms back to the same form, since
their pulled back Liouville forms differ by an exact form. -/
private theorem mpullback_frameCover_symplecticForm (ha : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ a)
    (hαa : ∀ i x v, SmoothForm.degreeOneEquiv (α i) x v = p * mfderiv I 𝓘(ℝ, ι → ℝ) a x v i) :
    SmoothForm.mpullback (frameCover α) contMDiff_frameCover (CotangentBundle.symplecticForm I B) =
      SmoothForm.mpullback (actionAngleCover p ∘ anglesActions p a)
        (contMDiff_actionAngleCover_comp p ha)
        (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
          (ι → AddCircle p)) := by
  rw [symplecticForm_eq_neg_mextDerivₗ, symplecticForm_eq_neg_mextDerivₗ, map_neg, map_neg,
    ← SmoothForm.mextDerivₗ_mpullback, ← SmoothForm.mextDerivₗ_mpullback,
    mpullback_frameCover_liouvilleForm ha hαa, map_add]
  -- The exact term `d (d f)` vanishes.
  refine congrArg Neg.neg (add_eq_left.2 ?_)
  exact (SmoothForm.isClosed_iff_mextDerivₗ_eq_zero _).1 (SmoothForm.isClosed_mextDerivₗ _)

/-- Every class in `T*B/Λ` is the class of `∑ j, c_j α_j x` for some `(c, x)`. -/
private theorem surjective_mk_comp_frameCover : Surjective (mk hα ∘ frameCover α) := fun z ↦ by
  obtain ⟨z, rfl⟩ := mk_surjective hα z
  exact ⟨(fun i ↦ hα.coeff i z.proj z.snd, z.proj),
    congrArg (mk hα) (congrArg (TotalSpace.mk' (E →L[ℝ] ℝ) z.proj)
      (hα.coeff_sum_eq (fun _ ↦ z.snd) (mem_univ z.proj)).symm)⟩

/-- After the cover, the action–angle chart is `G(c, x) = κ(-p c, a(x))`. -/
private theorem actionAngleChart_comp_mk_comp_frameCover :
    actionAngleChart hα p a ∘ (mk hα ∘ frameCover α) = actionAngleCover p ∘ anglesActions p a :=
  funext fun x ↦ actionAngleChart_mk_sum_smul hα p a x.2 x.1

/-- **The action–angle chart is injective exactly when the developing map `a` is.** -/
theorem actionAngleChart_injective_iff : Injective (actionAngleChart hα p a) ↔ Injective a := by
  refine ⟨fun h x y hxy ↦ ?_, fun h z z' hzz' ↦ ?_⟩
  · -- Two base points with the same value of `a` carry zero covectors with the same image.
    have hz := actionAngleChart_mk_sum_smul hα p a x 0
    rw [hxy, ← actionAngleChart_mk_sum_smul hα p a y 0] at hz
    simpa using congrArg (proj hα) (h hz)
  -- Two classes with the same image have the same actions, hence base points with the same value
  -- of `a`, and angles differing by `p ℤ^ι`, hence frame coordinates differing by an integer
  -- vector.
  obtain ⟨⟨c, x⟩, rfl⟩ := surjective_mk_comp_frameCover hα z
  obtain ⟨⟨c', x'⟩, rfl⟩ := surjective_mk_comp_frameCover hα z'
  simp only [comp_apply, frameCover, actionAngleChart_mk_sum_smul,
    actionAngleCover_eq_actionAngleCover_iff] at hzz' ⊢
  obtain ⟨hxx', m, hm⟩ := hzz'
  obtain rfl := h hxx'
  refine (mk_mk_eq_mk_mk_iff hα).2 ⟨m, ?_⟩
  -- The angles `-p c'` and `-p c + m p` agree, so `c = c' + m`.
  have hc : c = c' + fun i ↦ (m i : ℝ) := by
    funext i
    have hi := congrFun hm i
    simp only [Pi.neg_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hi ⊢
    have hp : p ≠ 0 := (Fact.out : 0 < p).ne'
    apply mul_left_cancel₀ hp
    linarith
  simp [hc, add_smul, Finset.sum_add_distrib]

/-- **The range of the action–angle chart** is the set of covectors of `T*Tⁿ` whose actions are
values of the developing map `a`. -/
theorem range_actionAngleChart [DecidableEq ι] :
    range (actionAngleChart hα p a) = {z | (fun i ↦ z.snd (Pi.single i 1)) ∈ range a} := by
  refine Subset.antisymm ?_ fun z ⟨x, hx⟩ ↦ ?_
  · rintro _ ⟨z, rfl⟩
    exact ⟨proj hα z, funext fun i ↦ (actionAngleChart_snd_apply_single hα p a z i).symm⟩
  obtain ⟨⟨θ, J⟩, rfl⟩ := surjective_actionAngleCover p z
  have hJ : J = a x := by
    rw [hx]
    exact funext fun i ↦ (actionAngleCover_snd_apply_single p (θ, J) i).symm
  refine ⟨mk hα (frameCover α (-(p⁻¹ • θ), x)), ?_⟩
  rw [frameCover, actionAngleChart_mk_sum_smul, hJ]
  congr 2
  rw [smul_neg, neg_neg, smul_inv_smul₀ (Fact.out : 0 < p).ne']

section Manifold

variable [FiniteDimensional ℝ E] [T2Space B] [BoundarylessManifold I B]

omit [Fact (0 < p)] [FiniteDimensional ℝ E] [T2Space B] [BoundarylessManifold I B] in
include hα in
/-- The developing map has injective differential: its differentials, scaled by `p`, span every
cotangent space. -/
theorem injective_mfderiv
    (hαa : ∀ i x v, SmoothForm.degreeOneEquiv (α i) x v = p * mfderiv I 𝓘(ℝ, ι → ℝ) a x v i)
    (x : B) : Injective (mfderiv I 𝓘(ℝ, ι → ℝ) a x) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
  -- Every covector at `x` is a combination of the `α j x`, which vanish on `v`.
  have h (q : TangentSpace I x →L[ℝ] ℝ) : q v = 0 := by
    rw [hα.coeff_sum_eq (fun _ ↦ q) (mem_univ x), sum_apply]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [smul_apply, hαa, hv]
    exact smul_eq_zero_of_right _ (mul_eq_zero_of_right _ rfl)
  exact SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) (V := E) h

omit [T2Space B] in
include hα in
/-- The chart after the cover, `G(c, x) = κ(-p c, a(x))`, is a local diffeomorphism. -/
private theorem isLocalDiffeomorphAt_actionAngleCover_comp (ha : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ a)
    (hαa : ∀ i x v, SmoothForm.degreeOneEquiv (α i) x v = p * mfderiv I 𝓘(ℝ, ι → ℝ) a x v i)
    (x : (ι → ℝ) × B) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ι → ℝ).prod I) ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
      𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ (actionAngleCover p ∘ anglesActions p a) x := by
  have hL := hasMFDerivAt_anglesActions p ha x
  refine isLocalDiffeomorphAt_of_injective_mfderiv
    (contMDiff_actionAngleCover_comp p ha).contMDiffOn isOpen_univ (mem_univ x)
    BoundarylessManifold.isInteriorPoint (by simp) ?_ ?_
  · rw [mfderiv_comp x ((contMDiff_actionAngleCover (ι := ι) p _).mdifferentiableAt (by simp))
      hL.mdifferentiableAt, hL.mfderiv]
    refine ((isLocalDiffeomorph_actionAngleCover (ι := ι) p _).isInvertible_mfderiv
      (by simp)).injective.comp ((injective_iff_map_eq_zero _).2 fun w hw ↦ ?_)
    have h₁ : -(p • w.1) = 0 := congrArg Prod.fst hw
    have h₂ : mfderiv I 𝓘(ℝ, ι → ℝ) a x.2 w.2 = 0 := congrArg Prod.snd hw
    refine Prod.ext ?_ ((injective_iff_map_eq_zero _).1 (injective_mfderiv hα hαa x.2) _ h₂)
    rw [neg_eq_zero, smul_eq_zero] at h₁
    exact h₁.resolve_left (Fact.out : 0 < p).ne'
  · simp [Module.finrank_prod, hα.card_eq_finrank (mem_univ x.2),
      ContinuousLinearMap.dual_finrank_eq]

omit [T2Space B] in
include hα in
/-- The cover by frame coordinates is a local diffeomorphism. A vector killed by its differential
pairs to zero with every vector under the pullback of the canonical form, which is also the
pullback along the local diffeomorphism `G` of a nondegenerate form. -/
private theorem isLocalDiffeomorphAt_frameCover (ha : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ a)
    (hαa : ∀ i x v, SmoothForm.degreeOneEquiv (α i) x v = p * mfderiv I 𝓘(ℝ, ι → ℝ) a x v i)
    (x : (ι → ℝ) × B) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ι → ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (frameCover α) x := by
  refine isLocalDiffeomorphAt_of_injective_mfderiv contMDiff_frameCover.contMDiffOn isOpen_univ
    (mem_univ x) BoundarylessManifold.isInteriorPoint (by simp)
    ((injective_iff_map_eq_zero _).2 fun v hv ↦ ?_) ?_
  · obtain ⟨e, he⟩ := (isLocalDiffeomorphAt_actionAngleCover_comp hα ha hαa x).isInvertible_mfderiv
      (by simp)
    -- The image of `v` under the differential of `G` pairs to zero with every vector.
    have h : ∀ w, SmoothBundleForm.eval₂
        (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
        ((actionAngleCover p ∘ anglesActions p a) x) (e v) w = 0 := fun w ↦ by
      obtain ⟨w, rfl⟩ := e.surjective w
      rw [← ContinuousLinearEquiv.coe_coe, he,
        ← SmoothForm.eval₂_mpullback _ (contMDiff_actionAngleCover_comp p ha),
        ← mpullback_frameCover_symplecticForm ha hαa,
        SmoothForm.eval₂_mpullback, hv, ← SmoothForm.bilinFormAt_apply, LinearMap.map_zero₂]
    exact e.injective ((SmoothTwoForm.isNondegenerate_iff_separatingLeft.1
      CotangentBundle.isSymplectic_symplecticForm.isNondegenerate _ _ h).trans e.map_zero.symm)
  · simp [Module.finrank_prod, hα.card_eq_finrank (mem_univ x.2),
      ContinuousLinearMap.dual_finrank_eq]

include hα in
/-- The class map `(c, x) ↦ [∑ j, c_j α_j x]` is a local diffeomorphism. -/
private theorem isLocalDiffeomorph_mk_comp_frameCover (ha : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ a)
    (hαa : ∀ i x v, SmoothForm.degreeOneEquiv (α i) x v = p * mfderiv I 𝓘(ℝ, ι → ℝ) a x v i) :
    IsLocalDiffeomorph (𝓘(ℝ, ι → ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (mk hα ∘ frameCover α) :=
  fun x ↦ (isLocalDiffeomorphAt_frameCover hα ha hαa x).comp (hg := isLocalDiffeomorph_mk hα _)

/-- **The action–angle chart is smooth.** -/
theorem contMDiff_actionAngleChart (ha : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ a)
    (hαa : ∀ i x v, SmoothForm.degreeOneEquiv (α i) x v = p * mfderiv I 𝓘(ℝ, ι → ℝ) a x v i) :
    ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
      𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ (actionAngleChart hα p a) :=
  ((isLocalDiffeomorph_mk_comp_frameCover hα ha hαa).contMDiff_comp_iff
    (surjective_mk_comp_frameCover hα) le_rfl).1
    (by rw [actionAngleChart_comp_mk_comp_frameCover]; exact contMDiff_actionAngleCover_comp p ha)

/-- **The action–angle chart is a local diffeomorphism.** -/
theorem isLocalDiffeomorph_actionAngleChart (ha : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ a)
    (hαa : ∀ i x v, SmoothForm.degreeOneEquiv (α i) x v = p * mfderiv I 𝓘(ℝ, ι → ℝ) a x v i) :
    IsLocalDiffeomorph (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
      𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ (actionAngleChart hα p a) := fun z ↦ by
  obtain ⟨x, rfl⟩ := surjective_mk_comp_frameCover hα z
  have h := isLocalDiffeomorphAt_actionAngleCover_comp hα ha hαa x
  rw [← actionAngleChart_comp_mk_comp_frameCover hα] at h
  exact h.of_comp_right (isLocalDiffeomorph_mk_comp_frameCover hα ha hαa x)

/-- **The action–angle chart is symplectic**: it pulls the canonical symplectic form
`ω = ∑ j, dθ_j ∧ dI_j` of `T*Tⁿ` back to the symplectic form of `T*B/Λ`. -/
theorem mpullback_actionAngleChart_symplecticForm (ha : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ a)
    (hαa : ∀ i x v, SmoothForm.degreeOneEquiv (α i) x v = p * mfderiv I 𝓘(ℝ, ι → ℝ) a x v i) :
    SmoothForm.mpullback (actionAngleChart hα p a) (contMDiff_actionAngleChart hα ha hαa)
        (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) =
      symplecticForm hα
        (fun i ↦ SmoothForm.isClosed_of_degreeOneEquiv_eq_mul_mfderiv_apply ha (hαa i)) := by
  have hΨ := isLocalDiffeomorph_mk_comp_frameCover hα ha hαa
  have hclosed i := SmoothForm.isClosed_of_degreeOneEquiv_eq_mul_mfderiv_apply ha (hαa i)
  -- Both forms pull back along the cover `(c, x) ↦ [∑ j, c_j α_j x]` to `Ψ^* ω = G^* ω`.
  have key : SmoothForm.mpullback (mk hα ∘ frameCover α) hΨ.contMDiff
      (SmoothForm.mpullback (actionAngleChart hα p a) (contMDiff_actionAngleChart hα ha hαa)
        (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
          (ι → AddCircle p))) =
      SmoothForm.mpullback (mk hα ∘ frameCover α) hΨ.contMDiff
        (symplecticForm hα hclosed) := by
    rw [SmoothForm.mpullback_mpullback_of_comp_eq hΨ.contMDiff
      (contMDiff_actionAngleChart hα ha hαa) contMDiff_id (contMDiff_actionAngleCover_comp p ha)
      (actionAngleChart_comp_mk_comp_frameCover hα), SmoothForm.mpullback_id,
      LinearMap.id_apply, ← mpullback_frameCover_symplecticForm ha hαa,
      ← mpullback_mk_symplecticForm hα hclosed,
      SmoothForm.mpullback_mpullback]
  refine Subtype.ext (hΨ.mpullback_injective (by simp) (surjective_mk_comp_frameCover hα) ?_)
  rw [← SmoothForm.coe_mpullback _ hΨ.contMDiff, ← SmoothForm.coe_mpullback _ hΨ.contMDiff, key]

end Manifold

end LatticeQuotient

end CotangentBundle

end TauCeti
