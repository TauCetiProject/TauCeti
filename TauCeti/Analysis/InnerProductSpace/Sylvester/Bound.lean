/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-! # An operator-norm bound for the Sylvester equation

For bounded symmetric operators `A` on `E` and `B` on `F` over `𝕜 = ℝ, ℂ`,
and operators `X, Y : F →L[𝕜] E`, this file bounds the solution `X` of the
Sylvester-type equations

* `A ∘L X + X ∘L B = Y` with `A, B` both `δ`-coercive:  `‖X‖ ≤ ‖Y‖ / (2δ)`;
* `A ∘L X - X ∘L B = Y` with the quadratic forms of `A` and `B` separated by
  a gap `g` (that of `A` at least `c + g`, that of `B` at most `c`):
  `‖X‖ ≤ ‖Y‖ / g`.

The separated form is the estimate behind the operator-norm Davis–Kahan
`sin Θ` theorem: there `A` and `B` are compressions of two symmetric
operators to spectral subspaces whose eigenvalue blocks are separated by `g`,
`X` is the compressed cross-projection, and `Y` is a compression of the
perturbation.

The proof is elementary and integral-free.  From the equation,
`((‖A‖ + ‖B‖ : ℝ) : 𝕜) • X = Y + ((‖A‖ : 𝕜) • 1 - A) ∘L X + X ∘L ((‖B‖ : 𝕜) • 1 - B)`,
and the two correction operators have norm at most `‖A‖ - δ` and `‖B‖ - δ`
because a symmetric operator whose quadratic form lies in `[0, κ‖·‖²]` has
norm at most `κ` (via `ContinuousLinearMap.norm_eq_iSup_rayleighQuotient`).
Taking norms and absorbing the two correction terms leaves `2δ‖X‖ ≤ ‖Y‖`.

Neither completeness nor finite-dimensionality is assumed, so the results
apply to bounded symmetric operators on any inner product space; symmetry is
taken in the `LinearMap.IsSymmetric` sense, with no reference to adjoints.

## Main results

* `ContinuousLinearMap.norm_le_of_abs_re_inner_map_self_le`: a
  symmetric operator with `|re ⟪C x, x⟫| ≤ κ * ‖x‖ ^ 2` has `‖C‖ ≤ κ`.
* `ContinuousLinearMap.opNorm_le_div_of_comp_add_comp_eq`: the
  coercive (Lyapunov) form, `‖X‖ ≤ ‖Y‖ / (2 * δ)`.
* `ContinuousLinearMap.opNorm_le_div_of_comp_sub_comp_eq`: the
  separated (Davis–Kahan-facing) form, `‖X‖ ≤ ‖Y‖ / g`.

## References

* R. Bhatia, *Matrix Analysis*, Chapter VII.2 (the Sylvester equation and the
  Davis–Kahan theorems); the bound proved here is the half-line-separation
  case of Theorem VII.2.3, by a different, integral-free proof.
* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a
  perturbation. III*, SIAM J. Numer. Anal. 7 (1970), 1–46.
-/

public section


open scoped InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace ContinuousLinearMap

/-- A symmetric operator whose quadratic form is bounded by `κ * ‖x‖ ^ 2` in
absolute value has operator norm at most `κ`.  Quantitative counterpart of
`ContinuousLinearMap.norm_eq_iSup_rayleighQuotient`. -/
theorem norm_le_of_abs_re_inner_map_self_le {C : E →L[𝕜] E} (hC : C.IsSymmetric)
    {κ : ℝ} (hκ : 0 ≤ κ) (h : ∀ x, |RCLike.re ⟪C x, x⟫_𝕜| ≤ κ * ‖x‖ ^ 2) : ‖C‖ ≤ κ := by
  rw [C.norm_eq_iSup_rayleighQuotient hC]
  refine ciSup_le fun x => ?_
  -- names the application so the norm bound applies to it directly.
  change |C.reApplyInnerSelf x / ‖x‖ ^ 2| ≤ κ
  rcases eq_or_ne x 0 with rfl | hx
  · simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using hκ
  · rw [ContinuousLinearMap.reApplyInnerSelf_apply, abs_div, abs_sq,
      div_le_iff₀ (by positivity)]
    exact h x

section SylvesterBound

variable {A : E →L[𝕜] E} {B : F →L[𝕜] F} {X Y : F →L[𝕜] E}

/-- The quadratic form of the real shift `(r : 𝕜) • 1 - A`.  Auxiliary. -/
private theorem re_inner_ofReal_smul_one_sub_apply_self (A : E →L[𝕜] E) (r : ℝ) (x : E) :
    RCLike.re ⟪((r : 𝕜) • (1 : E →L[𝕜] E) - A) x, x⟫_𝕜
      = r * ‖x‖ ^ 2 - RCLike.re ⟪A x, x⟫_𝕜 := by
  simp only [sub_apply, smul_apply,
    one_apply_eq_self, inner_sub_left, inner_smul_left, RCLike.conj_ofReal,
    map_sub, RCLike.re_ofReal_mul, inner_self_eq_norm_sq]

/-- The real shift `(r : 𝕜) • 1 - A` of a symmetric operator is symmetric.
Auxiliary. -/
private theorem isSymmetric_ofReal_smul_one_sub (hA : A.IsSymmetric) (r : ℝ) :
    (((r : 𝕜) • (1 : E →L[𝕜] E) - A)).IsSymmetric := fun x y => by
  simp only [ContinuousLinearMap.coe_coe, sub_apply,
    smul_apply, one_apply_eq_self, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, RCLike.conj_ofReal]
  congr 1
  exact hA x y

/-- Coercivity forces the norm from below: if `δ * ‖x‖ ^ 2 ≤ re ⟪A x, x⟫` and
some vector is nonzero, then `δ ≤ ‖A‖`.  Auxiliary. -/
private theorem le_opNorm_of_le_re_inner_map_self {δ : ℝ}
    (hAc : ∀ x, δ * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜) {x₀ : E} (hx₀ : x₀ ≠ 0) : δ ≤ ‖A‖ := by
  have hupper : RCLike.re ⟪A x₀, x₀⟫_𝕜 ≤ ‖A‖ * ‖x₀‖ ^ 2 :=
    calc RCLike.re ⟪A x₀, x₀⟫_𝕜 ≤ ‖⟪A x₀, x₀⟫_𝕜‖ := RCLike.re_le_norm _
      _ ≤ ‖A x₀‖ * ‖x₀‖ := norm_inner_le_norm _ _
      _ ≤ ‖A‖ * ‖x₀‖ * ‖x₀‖ := by gcongr; exact A.le_opNorm x₀
      _ = ‖A‖ * ‖x₀‖ ^ 2 := by ring
  have hx₀2 : (0 : ℝ) < ‖x₀‖ ^ 2 := by positivity
  nlinarith [hAc x₀]

/-- The correction operator `(‖A‖ : 𝕜) • 1 - A` in the absorption identity is a
contraction up to `‖A‖ - δ`: if the quadratic form of the symmetric `A` is at
least `δ * ‖·‖ ^ 2`, its operator norm is at most `‖A‖ - δ`.  Auxiliary for the
Sylvester bounds. -/
private theorem norm_opNorm_smul_one_sub_le (hA : A.IsSymmetric) {δ : ℝ} (hδA : δ ≤ ‖A‖)
    (hAc : ∀ x, δ * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜) :
    ‖(‖A‖ : 𝕜) • (1 : E →L[𝕜] E) - A‖ ≤ ‖A‖ - δ := by
  refine norm_le_of_abs_re_inner_map_self_le (isSymmetric_ofReal_smul_one_sub hA ‖A‖)
    (by linarith) fun x => ?_
  rw [re_inner_ofReal_smul_one_sub_apply_self]
  have hupper : RCLike.re ⟪A x, x⟫_𝕜 ≤ ‖A‖ * ‖x‖ ^ 2 :=
    calc RCLike.re ⟪A x, x⟫_𝕜 ≤ ‖⟪A x, x⟫_𝕜‖ := RCLike.re_le_norm _
      _ ≤ ‖A x‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ ‖A‖ * ‖x‖ * ‖x‖ := by gcongr; exact A.le_opNorm x
      _ = ‖A‖ * ‖x‖ ^ 2 := by ring
  rw [abs_of_nonneg (by linarith)]
  linarith [hAc x]

/-- The correction term in the absorption identity is small: if the quadratic
form of `A` is at least `δ * ‖·‖ ^ 2`, then `(‖A‖ : 𝕜) • w - A w` has norm at
most `(‖A‖ - δ) * ‖w‖`.  Auxiliary for the Sylvester bound. -/
private theorem norm_opNorm_smul_sub_apply_le (hA : A.IsSymmetric) {δ : ℝ} (hδA : δ ≤ ‖A‖)
    (hAc : ∀ x, δ * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜) (w : E) :
    ‖(‖A‖ : 𝕜) • w - A w‖ ≤ (‖A‖ - δ) * ‖w‖ :=
  calc ‖(‖A‖ : 𝕜) • w - A w‖ = ‖((‖A‖ : 𝕜) • (1 : E →L[𝕜] E) - A) w‖ := rfl
    _ ≤ ‖(‖A‖ : 𝕜) • (1 : E →L[𝕜] E) - A‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ w
    _ ≤ (‖A‖ - δ) * ‖w‖ := by gcongr; exact norm_opNorm_smul_one_sub_le hA hδA hAc

/-- **Polar-absorption Sylvester bound.**  Let `H` be symmetric and
coercive by `r + g`, let `T` have operator norm at most `r`, and suppose

`H X - Z T = Y`

where `Z` has the same operator norm as `X`.  Then `g ‖X‖ ≤ ‖Y‖`.

This is the dimension-free analytic core of the sharp interval/exterior
Davis--Kahan theorem.  In the finite spectral specialization, `H = |A-mI|`,
`Z = U⁻¹X`, and `U` is the unitary polar factor of `A-mI`.  The theorem itself
uses neither finite dimensionality nor a spectral theorem. -/
theorem gap_mul_opNorm_le_of_comp_sub_comp_eq
    {H : E →L[𝕜] E} {T : F →L[𝕜] F} {X Z Y : F →L[𝕜] E}
    (hH : H.IsSymmetric) {r g : ℝ} (_hr : 0 ≤ r) (_hg : 0 < g)
    (hHc : ∀ x, (r + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪H x, x⟫_𝕜)
    (hT : ‖T‖ ≤ r) (hZX : ‖Z‖ = ‖X‖)
    (hEq : H ∘L X - Z ∘L T = Y) :
    g * ‖X‖ ≤ ‖Y‖ := by
  rcases eq_or_ne X 0 with rfl | hX
  · simp
  obtain ⟨v₀, hv₀⟩ := DFunLike.ne_iff.mp hX
  simp only [zero_apply] at hv₀
  have hrgH : r + g ≤ ‖H‖ :=
    le_opNorm_of_le_re_inner_map_self hHc hv₀
  have hcorr : ‖(‖H‖ : 𝕜) • (1 : E →L[𝕜] E) - H‖ ≤ ‖H‖ - (r + g) :=
    norm_opNorm_smul_one_sub_le hH hrgH hHc
  have habsorb : ((‖H‖ : ℝ) : 𝕜) • X =
      Y + (((‖H‖ : 𝕜) • (1 : E →L[𝕜] E) - H) ∘L X) + Z ∘L T := by
    ext v
    have hv : H (X v) - Z (T v) = Y v := by
      simpa [sub_apply, ContinuousLinearMap.comp_apply] using
        congrArg (fun W : F →L[𝕜] E => W v) hEq
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      sub_apply, one_apply_eq_self]
    rw [← hv]
    module
  have hmain : ‖H‖ * ‖X‖ ≤
      ‖Y‖ + (‖H‖ - (r + g)) * ‖X‖ + ‖X‖ * r := by
    calc
      ‖H‖ * ‖X‖ = ‖((‖H‖ : ℝ) : 𝕜) • X‖ := by
        rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg H)]
      _ = ‖Y + (((‖H‖ : 𝕜) • (1 : E →L[𝕜] E) - H) ∘L X) + Z ∘L T‖ := by
        rw [habsorb]
      _ ≤ ‖Y‖ + ‖((‖H‖ : 𝕜) • (1 : E →L[𝕜] E) - H) ∘L X‖ + ‖Z ∘L T‖ :=
        norm_add₃_le
      _ ≤ ‖Y‖ + ‖(‖H‖ : 𝕜) • (1 : E →L[𝕜] E) - H‖ * ‖X‖ + ‖Z‖ * ‖T‖ := by
        gcongr
        · exact ContinuousLinearMap.opNorm_comp_le _ _
        · exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖Y‖ + (‖H‖ - (r + g)) * ‖X‖ + ‖X‖ * r := by
        rw [hZX]
        exact add_le_add
          (add_le_add_right (mul_le_mul_of_nonneg_right hcorr (norm_nonneg X)) ‖Y‖)
          (mul_le_mul_of_nonneg_left hT (norm_nonneg X))
  linarith


end SylvesterBound

/-! ### Rectangular abstract Sylvester bounds

## Staging note

Staged for Tau Ceti, roadmap topic T16.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/SylvesterBound.lean`
(new file).
Formalized by Claude Fable 5 (claude-fable-5[1m]).  The classical proofs of
this bound run through an operator-valued integral `∫₀^∞ e^{−tA} Y e^{−tB} dt`
(Bhatia VII.2) or a contour integral (Sylvester–Rosenblum); the proof here is
a purely algebraic absorption argument discovered while planning: writing
`(a + b) • X = Y + (a • 1 − A) X + X (b • 1 − B)` with `a = ‖A‖`, `b = ‖B‖`
and bounding the two correction terms by `(a − δ)‖X‖` and `(b − δ)‖X‖` lets
the operator norm of `X` be solved for directly.  No integrals, no spectral
theorem, no finite-dimensionality, no completeness.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForMathlib` at Davis--Kahan commit
  `5c65c95`; it has had no prior home.
* Extraction class: **authored in place**, for Tau Ceti — `ForMathlib` was
  retired on 2026-07-29 and `ForTauCeti` is the single staging library, whose
  destination is Tau Ceti and not Mathlib (`ForTauCeti/README.md`).
* Intended Mathlib home: additions to `Mathlib/Analysis/InnerProductSpace/SylvesterBound.
* Original authors / copyright: Jon Crall, Claude Fable 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — the `ForTauCeti` import firewall admits only
  Mathlib, `TauCeti` and `ForTauCeti` (enforced by `scripts/check_dependency_layers.py`).

Moved from
`ForTauCeti/Analysis/InnerProductSpace/SylvesterBound.lean` to
`ForTauCeti/Analysis/InnerProductSpace/Sylvester/Bound.lean`.  The `Sylvester/`
directory already held `Basic`, `Interval`, `SpectralDistance` and `Internal/`, while
six siblings of the same family used a flat `Sylvester*` prefix in the directory above;
one family now has one convention.  Path change and import repoint only — no statement,
signature, proof, attribute, declaration name or namespace changed.
-/

section RectangularAbstractSylvesterBound

variable {A : F →L[𝕜] F} {B : E →L[𝕜] E} {X Y : E →L[𝕜] F}
variable {N : (E →L[𝕜] F) → ℝ}
  (hadd : ∀ f g : E →L[𝕜] F, N (f + g) ≤ N f + N g)
  (hsmul : ∀ (a : 𝕜) (f : E →L[𝕜] F), N (a • f) = ‖a‖ * N f)
  (hidealL : ∀ C : F →L[𝕜] F, ∀ f : E →L[𝕜] F,
    N (C ∘L f) ≤ ‖C‖ * N f)
  (hidealR : ∀ f : E →L[𝕜] F, ∀ C : E →L[𝕜] E,
    N (f ∘L C) ≤ N f * ‖C‖)

include hadd hsmul in
private theorem rectangular_nonneg_of_add_le_of_smul (f : E →L[𝕜] F) : 0 ≤ N f := by
  have hN0 : N 0 = 0 := by
    have h := hsmul 0 0
    rwa [zero_smul, norm_zero, zero_mul] at h
  have hneg : N (-f) = N f := by
    rw [show -f = (-1 : 𝕜) • f by rw [neg_one_smul], hsmul,
      norm_neg, norm_one, one_mul]
  have h := hadd f (-f)
  rw [add_neg_cancel, hN0, hneg] at h
  linarith

include hadd hsmul hidealL hidealR in
/-- **Rectangular polar-absorption Sylvester bound in an arbitrary operator
seminorm.**  Let `H` be symmetric and coercive by `r + g`, let `T` have
operator norm at most `r`, and suppose

`H X - Z T = Y`,

where `Z` has the same seminorm as `X`.  Then `g * N X ≤ N Y`.

This is the operator-ideal generalization of
`gap_mul_opNorm_le_of_comp_sub_comp_eq`.  Its hypotheses are exactly the
subadditivity, absolute homogeneity, and two-sided ideal inequalities carried
by every rectangular unitarily invariant norm.  No finite-dimensionality,
spectral theorem, completeness, or singular-value argument is used. -/
theorem gap_mul_le_of_comp_sub_comp_eq_rectangular
    {H : F →L[𝕜] F} {T : E →L[𝕜] E} {X Z Y : E →L[𝕜] F}
    (hH : H.IsSymmetric) {r g : ℝ} (_hr : 0 ≤ r) (_hg : 0 < g)
    (hHc : ∀ x, (r + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪H x, x⟫_𝕜)
    (hT : ‖T‖ ≤ r) (hZX : N Z = N X)
    (hEq : H ∘L X - Z ∘L T = Y) :
    g * N X ≤ N Y := by
  rcases eq_or_ne X 0 with rfl | hX
  · have hN0 : N (0 : E →L[𝕜] F) = 0 := by
      have h := hsmul 0 0
      rwa [zero_smul, norm_zero, zero_mul] at h
    simpa [hN0] using rectangular_nonneg_of_add_le_of_smul hadd hsmul Y
  · obtain ⟨v₀, hv₀⟩ := DFunLike.ne_iff.mp hX
    simp only [zero_apply] at hv₀
    have hrgH : r + g ≤ ‖H‖ :=
      le_opNorm_of_le_re_inner_map_self hHc hv₀
    have hcorr : ‖(‖H‖ : 𝕜) • (1 : F →L[𝕜] F) - H‖ ≤ ‖H‖ - (r + g) :=
      norm_opNorm_smul_one_sub_le hH hrgH hHc
    have habsorb : ((‖H‖ : ℝ) : 𝕜) • X =
        Y + (((‖H‖ : 𝕜) • (1 : F →L[𝕜] F) - H) ∘L X) + Z ∘L T := by
      ext v
      have hv : H (X v) - Z (T v) = Y v := by
        simpa [sub_apply, ContinuousLinearMap.comp_apply] using
          congrArg (fun W : E →L[𝕜] F => W v) hEq
      simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
        sub_apply, one_apply_eq_self]
      rw [← hv]
      module
    have hNX : 0 ≤ N X := rectangular_nonneg_of_add_le_of_smul hadd hsmul X
    have hNZ : 0 ≤ N Z := rectangular_nonneg_of_add_le_of_smul hadd hsmul Z
    have hmain : ‖H‖ * N X ≤
        N Y + (‖H‖ - (r + g)) * N X + N X * r := by
      calc
        ‖H‖ * N X = N (((‖H‖ : ℝ) : 𝕜) • X) := by
          rw [hsmul, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg H)]
        _ = N (Y + (((‖H‖ : 𝕜) • (1 : F →L[𝕜] F) - H) ∘L X) + Z ∘L T) := by
          rw [habsorb]
        _ ≤ N Y + N (((‖H‖ : 𝕜) • (1 : F →L[𝕜] F) - H) ∘L X) +
              N (Z ∘L T) := by
          have h1 := hadd
            (Y + (((‖H‖ : 𝕜) • (1 : F →L[𝕜] F) - H) ∘L X))
            (Z ∘L T)
          have h2 := hadd Y (((‖H‖ : 𝕜) • (1 : F →L[𝕜] F) - H) ∘L X)
          linarith
        _ ≤ N Y + (‖H‖ - (r + g)) * N X + N X * r := by
          gcongr
          · calc
              N (((‖H‖ : 𝕜) • (1 : F →L[𝕜] F) - H) ∘L X)
                  ≤ ‖(‖H‖ : 𝕜) • (1 : F →L[𝕜] F) - H‖ * N X :=
                    hidealL _ _
              _ ≤ (‖H‖ - (r + g)) * N X := by
                    exact mul_le_mul_of_nonneg_right hcorr hNX
          · calc
              N (Z ∘L T) ≤ N Z * ‖T‖ := hidealR _ _
              _ ≤ N Z * r := mul_le_mul_of_nonneg_left hT hNZ
              _ = N X * r := by rw [hZX]
    linarith

include hadd hsmul hidealL hidealR in
/-- Rectangular coercive Sylvester bound in any operator seminorm with
left and right ideal inequalities. -/
theorem le_div_of_comp_add_comp_eq_rectangular
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ)
    (hAc : ∀ x, δ * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hBc : ∀ x, δ * ‖x‖ ^ 2 ≤ RCLike.re ⟪B x, x⟫_𝕜)
    (hXY : A ∘L X + X ∘L B = Y) : N X ≤ N Y / (2 * δ) := by
  have hNY : 0 ≤ N Y := rectangular_nonneg_of_add_le_of_smul hadd hsmul Y
  rcases eq_or_ne X 0 with rfl | hX
  · have hN0 : N (0 : E →L[𝕜] F) = 0 := by
      have h := hsmul 0 0
      rwa [zero_smul, norm_zero, zero_mul] at h
    rw [hN0]
    positivity
  · obtain ⟨x₀, hx₀⟩ := DFunLike.ne_iff.mp hX
    simp only [zero_apply] at hx₀
    have hδA : δ ≤ ‖A‖ := le_opNorm_of_le_re_inner_map_self hAc hx₀
    have hδB : δ ≤ ‖B‖ :=
      le_opNorm_of_le_re_inner_map_self hBc (x₀ := x₀) fun hx₀' =>
        hx₀ (by rw [hx₀']; exact map_zero X)
    have habsorb : ((‖A‖ + ‖B‖ : ℝ) : 𝕜) • X
        = Y + ((‖A‖ : 𝕜) • 1 - A) ∘L X + X ∘L ((‖B‖ : 𝕜) • 1 - B) := by
      ext v
      have hv : A (X v) + X (B v) = Y v := by
        simpa [add_apply, ContinuousLinearMap.comp_apply] using
          congrArg (fun W : E →L[𝕜] F => W v) hXY
      simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, sub_apply,
        one_apply_eq_self, map_sub, map_smul]
      rw [← hv]
      push_cast
      module
    have hkey : (‖A‖ + ‖B‖) * N X
        ≤ N Y + (‖A‖ - δ) * N X + N X * (‖B‖ - δ) :=
      calc
        (‖A‖ + ‖B‖) * N X
            = N (((‖A‖ + ‖B‖ : ℝ) : 𝕜) • X) := by
                rw [hsmul, RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
        _ = N (Y + ((‖A‖ : 𝕜) • 1 - A) ∘L X
              + X ∘L ((‖B‖ : 𝕜) • 1 - B)) := by rw [habsorb]
        _ ≤ N Y + N (((‖A‖ : 𝕜) • 1 - A) ∘L X)
              + N (X ∘L ((‖B‖ : 𝕜) • 1 - B)) := by
                have h1 := hadd
                  (Y + ((‖A‖ : 𝕜) • 1 - A) ∘L X)
                  (X ∘L ((‖B‖ : 𝕜) • 1 - B))
                have h2 := hadd Y (((‖A‖ : 𝕜) • 1 - A) ∘L X)
                linarith
        _ ≤ N Y + (‖A‖ - δ) * N X + N X * (‖B‖ - δ) := by
                gcongr
                · calc
                    N (((‖A‖ : 𝕜) • 1 - A) ∘L X)
                        ≤ ‖(‖A‖ : 𝕜) • 1 - A‖ * N X := hidealL _ _
                    _ ≤ (‖A‖ - δ) * N X := by
                        gcongr ?_ * _
                        · exact rectangular_nonneg_of_add_le_of_smul hadd hsmul X
                        · exact norm_opNorm_smul_one_sub_le hA hδA hAc
                · calc
                    N (X ∘L ((‖B‖ : 𝕜) • 1 - B))
                        ≤ N X * ‖(‖B‖ : 𝕜) • 1 - B‖ := hidealR _ _
                    _ ≤ N X * (‖B‖ - δ) := by
                        gcongr _ * ?_
                        · exact rectangular_nonneg_of_add_le_of_smul hadd hsmul X
                        · exact norm_opNorm_smul_one_sub_le hB hδB hBc
    have hexpand : (‖A‖ - δ) * N X + N X * (‖B‖ - δ)
        = (‖A‖ + ‖B‖) * N X - 2 * δ * N X := by ring
    have hfinal : 2 * δ * N X ≤ N Y := by linarith [hkey, hexpand]
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact hfinal

include hadd hsmul hidealL hidealR in
/-- Rectangular separated Sylvester bound in any operator seminorm with
left and right ideal inequalities. -/
theorem le_div_of_comp_sub_comp_eq_rectangular
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {c g : ℝ} (hg : 0 < g)
    (hAc : ∀ x, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hBc : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hXY : A ∘L X - X ∘L B = Y) : N X ≤ N Y / g := by
  set r : ℝ := c + g / 2 with hr
  have hA' : (A - (r : 𝕜) • (1 : F →L[𝕜] F)).IsSymmetric := fun x y => by
    simp only [ContinuousLinearMap.coe_coe, sub_apply, smul_apply, one_apply_eq_self,
      inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      RCLike.conj_ofReal]
    congr 1
    exact hA x y
  have hB' : ((r : 𝕜) • (1 : E →L[𝕜] E) - B).IsSymmetric :=
    isSymmetric_ofReal_smul_one_sub hB r
  have hAc' : ∀ x, g / 2 * ‖x‖ ^ 2
      ≤ RCLike.re ⟪(A - (r : 𝕜) • (1 : F →L[𝕜] F)) x, x⟫_𝕜 := by
    intro x
    have hneg : (A - (r : 𝕜) • (1 : F →L[𝕜] F)) x
        = -(((r : 𝕜) • (1 : F →L[𝕜] F) - A) x) := by
      simp [neg_sub]
    rw [hneg, inner_neg_left, map_neg,
      re_inner_ofReal_smul_one_sub_apply_self, hr]
    linarith [hAc x]
  have hBc' : ∀ x, g / 2 * ‖x‖ ^ 2
      ≤ RCLike.re ⟪((r : 𝕜) • (1 : E →L[𝕜] E) - B) x, x⟫_𝕜 := by
    intro x
    rw [re_inner_ofReal_smul_one_sub_apply_self, hr]
    linarith [hBc x]
  have hXY' : (A - (r : 𝕜) • (1 : F →L[𝕜] F)) ∘L X
      + X ∘L ((r : 𝕜) • (1 : E →L[𝕜] E) - B) = Y := by
    ext v
    have hv : A (X v) - X (B v) = Y v := by
      simpa [sub_apply, ContinuousLinearMap.comp_apply] using
        congrArg (fun W : E →L[𝕜] F => W v) hXY
    simp only [add_apply, ContinuousLinearMap.comp_apply, sub_apply, smul_apply,
      one_apply_eq_self, map_sub, map_smul, ← hv]
    module
  have hfin := le_div_of_comp_add_comp_eq_rectangular hadd hsmul hidealL hidealR
    hA' hB' (by linarith : (0 : ℝ) < g / 2) hAc' hBc' hXY'
  rwa [show 2 * (g / 2) = g by ring] at hfin

end RectangularAbstractSylvesterBound

/-! ### The operator-norm case

The operator-norm bounds are the rectangular abstract bounds at `N = ‖·‖`,
whose four hypotheses are `norm_add_le`, `norm_smul` and `opNorm_comp_le`
twice.  Two of the three are stated below as exactly that instantiation.

The third, `gap_mul_opNorm_le_of_comp_sub_comp_eq`, stays a direct proof above
because the abstract bounds *use* it: the polar absorption is where the
operator norm is genuinely needed, and the seminorm `N` never enters it. -/

section OperatorNormSylvesterBound

variable {A : E →L[𝕜] E} {B : F →L[𝕜] F} {X Y : F →L[𝕜] E}

/-- **Operator-norm bound for the Sylvester equation, coercive (Lyapunov)
form.**  If `A` and `B` are symmetric with quadratic forms at least
`δ * ‖·‖ ^ 2`, and `A ∘L X + X ∘L B = Y`, then `‖X‖ ≤ ‖Y‖ / (2 * δ)`.

The argument is integral-free: from the equation,
`((‖A‖ + ‖B‖ : ℝ) : 𝕜) • X = Y + ((‖A‖ : 𝕜) • 1 - A) ∘L X + X ∘L ((‖B‖ : 𝕜) • 1 - B)`,
the two correction operators have norms at most `‖A‖ - δ` and `‖B‖ - δ`, and
taking norms lets `‖X‖` be solved for.  It is carried out once, in
`le_div_of_comp_add_comp_eq_rectangular`; this is that bound at `N = ‖·‖`. -/
theorem opNorm_le_div_of_comp_add_comp_eq (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ)
    (hAc : ∀ x, δ * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hBc : ∀ v, δ * ‖v‖ ^ 2 ≤ RCLike.re ⟪B v, v⟫_𝕜)
    (hXY : A ∘L X + X ∘L B = Y) : ‖X‖ ≤ ‖Y‖ / (2 * δ) :=
  le_div_of_comp_add_comp_eq_rectangular (N := fun f : F →L[𝕜] E => ‖f‖)
    (fun f g => norm_add_le f g) (fun a f => norm_smul a f)
    (fun C f => ContinuousLinearMap.opNorm_comp_le C f)
    (fun f C => ContinuousLinearMap.opNorm_comp_le f C)
    hA hB hδ hAc hBc hXY

/-- **Operator-norm bound for the Sylvester equation, separated (Davis–Kahan)
form.**  If the quadratic form of `A` is at least `c + g` and that of `B` at
most `c`, and `A ∘L X - X ∘L B = Y`, then `‖X‖ ≤ ‖Y‖ / g`.

This is the constant-one estimate behind the dimension-free `sin Θ` theorem:
the gap `g` divides the residual with no `π / 2` and no dimensional factor.
It is `le_div_of_comp_sub_comp_eq_rectangular` at `N = ‖·‖`. -/
theorem opNorm_le_div_of_comp_sub_comp_eq (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {c g : ℝ} (hg : 0 < g)
    (hAc : ∀ x, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hBc : ∀ v, RCLike.re ⟪B v, v⟫_𝕜 ≤ c * ‖v‖ ^ 2)
    (hXY : A ∘L X - X ∘L B = Y) : ‖X‖ ≤ ‖Y‖ / g :=
  le_div_of_comp_sub_comp_eq_rectangular (N := fun f : F →L[𝕜] E => ‖f‖)
    (fun f g => norm_add_le f g) (fun a f => norm_smul a f)
    (fun C f => ContinuousLinearMap.opNorm_comp_le C f)
    (fun f C => ContinuousLinearMap.opNorm_comp_le f C)
    hA hB hg hAc hBc hXY

end OperatorNormSylvesterBound

/-! ### The square case

`E →L[𝕜] E` is the rectangular case at `F = E`, and these three declarations are
exactly that instantiation.  They existed as independent proofs — the same
`set r := c + g/2`, the same symmetry computation, the same absorption — until
2026-07-30, when the two sections were found to be character-for-character
identical modulo the letter `F`.  They keep their names because callers use
them and because the square case is the one a reader looks for first. -/

section AbstractSylvesterBound

variable {A B X Y : E →L[𝕜] E} {N : (E →L[𝕜] E) → ℝ}
  (hadd : ∀ f g : E →L[𝕜] E, N (f + g) ≤ N f + N g)
  (hsmul : ∀ (a : 𝕜) (f : E →L[𝕜] E), N (a • f) = ‖a‖ * N f)
  (hidealL : ∀ C f : E →L[𝕜] E, N (C ∘L f) ≤ ‖C‖ * N f)
  (hidealR : ∀ f C : E →L[𝕜] E, N (f ∘L C) ≤ N f * ‖C‖)

include hadd hsmul in
/-- An operator seminorm is nonnegative.  From subadditivity and absolute
homogeneity alone. -/
private theorem nonneg_of_add_le_of_smul (f : E →L[𝕜] E) : 0 ≤ N f :=
  rectangular_nonneg_of_add_le_of_smul hadd hsmul f

include hadd hsmul hidealL hidealR in
/-- **Abstract Sylvester bound, separated (Davis–Kahan) form.**  For any
operator seminorm `N` with the two-sided ideal property, if the quadratic form
of `A` is at least `c + g` and that of `B` at most `c`, then `A X - X B = Y`
forces `N X ≤ N Y / g`.

The square case of `le_div_of_comp_sub_comp_eq_rectangular`. -/
theorem le_div_of_comp_sub_comp_eq (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {c g : ℝ} (hg : 0 < g)
    (hAc : ∀ x, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hBc : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hXY : A ∘L X - X ∘L B = Y) : N X ≤ N Y / g :=
  le_div_of_comp_sub_comp_eq_rectangular hadd hsmul hidealL hidealR
    hA hB hg hAc hBc hXY

end AbstractSylvesterBound


end ContinuousLinearMap
