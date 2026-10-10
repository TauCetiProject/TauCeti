/-
Staged for Tau Ceti, roadmap topic T17.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/RotationSharp.lean`
(new file).

Formalized by Claude Fable 5 (claude-fable-5[1m]).  Davis's classical
proof chooses a unimodular phase making the off-diagonal entry of the 2×2
compression real; the proof here avoids phases entirely — subtracting the two
eigenvector equations and taking real parts collapses the mixed term via
`re (c²·w − s²·conj w) = (c² − s²)·re w`, and the classical half-angle rotation
is realized by test vectors with *polynomial* coefficients
(`1 − 2cs = (c − s)²`, `1 + 2cs = (c + s)²`), so no square roots, inverses, or
normalizations appear anywhere.  No finite-dimensionality is assumed: the
subspace only needs an orthogonal projection.

For the `tan 2θ` theorem, under the vanishing-pinch hypotheses (`H` has no
diagonal blocks with respect to `U ⊕ Uᗮ`) the same block energy identity collapses to
`c·s·(re⟪y,Ty⟫ − re⟪z,Tz⟫) = (c² − s²)·re⟪y,Hz⟫`, and bounding the single
mixed term directly (no rotation, no half-angle) gives
`(b − a)·(‖Px‖·‖x − Px‖) ≤ |‖Px‖² − ‖x − Px‖²|·ε`, i.e. `tan 2θ ≤ 2ε/(b − a)`,
with no smallness assumption on the perturbation.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! # The Davis sin 2θ theorem (per-eigenvector, product form)

Let `T` be a symmetric operator, `U` a `T`-invariant subspace on which the
quadratic form of `T` is at least `b * ‖·‖ ^ 2` while on `Uᗮ` it is at most
`a * ‖·‖ ^ 2`, and let `x` be a unit eigenvector of the perturbed operator
`T + H`, with **no assumption on the location of its eigenvalue**.  Writing
`P` for the orthogonal projection onto `U` and `θ` for the angle between `x`
and `U` (`cos θ = ‖P x‖`, `sin θ = ‖x - P x‖`), Davis's sharp two-subspace
estimate bounds the *double* angle:

`sin 2θ ≤ 2 ‖H‖ / (b - a)`.

This file proves it in the product form `(b - a) * (‖P x‖ * ‖x - P x‖) ≤ ε`
(no angle, no division, no positivity side conditions), together with the
`Real.arccos` corollary in the literature-facing `sin 2θ` form.

The proof is elementary and phase-free.  Decompose `x = y + z` with `y = P x`,
`z = x - P x`, and pair the eigenvector equation with `y` and with `z`; the two
resulting scalar equations combine (eliminating the eigenvalue) into the real
identity

`‖z‖² re ⟪y, T y⟫ - ‖y‖² re ⟪z, T z⟫ + ‖z‖² re ⟪y, H y⟫ - ‖y‖² re ⟪z, H z⟫
+ (‖z‖² - ‖y‖²) re ⟪y, H z⟫ = 0`,

with no complex phase alignment needed (`re (c² w - s² conj w) = (c² - s²) re w`
identically).  Testing the quadratic form of `H` against the two orthogonal
vectors `s(c-s) • y + c(c+s) • z` and `-s(c+s) • y + c(c-s) • z` (where
`c = ‖y‖`, `s = ‖z‖`; each has squared norm `2c²s²` since `c² + s² = 1`)
recovers the left-hand side of the identity and yields
`4 c³s³ (b - a) ≤ 4 c²s² ε`.

## Main results

* `TauCeti.sin_two_theta_le`: the product form
  `(b - a) * (‖P x‖ * ‖x - P x‖) ≤ ε`.
* `TauCeti.sin_two_arccos_le`: the literature-facing form
  `(b - a) * sin (2 * arccos ‖P x‖) ≤ 2 * ε`.
* `TauCeti.tan_two_theta_le` / `…_of_mem`: Davis's `tan 2θ` theorem under
  the vanishing-pinch hypotheses, in product form
  `(b - a) * (‖P x‖ * ‖x - P x‖) ≤ |‖P x‖ ^ 2 - ‖x - P x‖ ^ 2| * ε`.
* `TauCeti.map_mem_orthogonal_of_forall_map_mem`: the orthogonal complement
  of an invariant subspace of a symmetric operator is invariant.

## References

* C. Davis, *The rotation of eigenvectors by a perturbation*,
  J. Math. Anal. Appl. 6 (1963), 159–173 (the sharp two-subspace estimate).
* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a
  perturbation. III*, SIAM J. Numer. Anal. 7 (1970), 1–46 (the sin 2Θ theorem).

## Sources

The double-angle identity for the vector case follows Davis--Kahan's
`sin 2Θ`/`tan 2Θ` development; see
`prose/distilled_literature/DavisKahan1970_part_III.tex` and, for the branch
selection this avoids, `prose/distilled_literature/DoubleAngle_branch_selection_dossier.tex`.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/FiniteDimensional/DoubleAngle/Vector.lean`
before the whole remaining sin-Θ closure moved into
the staging layer.  Statements, proofs, signatures and namespaces are unchanged;
the declarations already lived in `TauCeti.*`, so the move was a path change and
an import repoint.

Y3(b2) and Y3(b3) are what made it possible: before them this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.

-/

public section

namespace TauCeti
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {T H : E →ₗ[𝕜] E}

/-- The orthogonal complement of an invariant subspace of a symmetric operator
is invariant: if `T u ∈ U` for all `u ∈ U` and `T` is symmetric, then
`T w ∈ Uᗮ` for all `w ∈ Uᗮ`. -/
theorem map_mem_orthogonal_of_forall_map_mem (hT : T.IsSymmetric)
    {U : Submodule 𝕜 E} (hU : ∀ u ∈ U, T u ∈ U) {w : E} (hw : w ∈ Uᗮ) : T w ∈ Uᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [← hT u w]
  exact Submodule.inner_right_of_mem_orthogonal (hU u hu) hw

/-- Real parts of the two mixed entries of a symmetric operator agree; the
reason no complex phase alignment is needed anywhere in this file. -/
private theorem re_inner_map_symm (hH : H.IsSymmetric) (y z : E) :
    RCLike.re ⟪z, H y⟫_𝕜 = RCLike.re ⟪y, H z⟫_𝕜 := by
  rw [← hH z y, ← inner_conj_symm, RCLike.conj_re]

/-- Quadratic form of an operator at a real linear combination of two vectors,
expanded into the four scalar entries.  Pure sesquilinear algebra. -/
private theorem re_inner_smul_add_smul_map (H : E →ₗ[𝕜] E) (y z : E) (γ σ : ℝ) :
    RCLike.re ⟪(γ : 𝕜) • y + (σ : 𝕜) • z, H ((γ : 𝕜) • y + (σ : 𝕜) • z)⟫_𝕜
      = γ ^ 2 * RCLike.re ⟪y, H y⟫_𝕜 + σ ^ 2 * RCLike.re ⟪z, H z⟫_𝕜
        + γ * σ * (RCLike.re ⟪y, H z⟫_𝕜 + RCLike.re ⟪z, H y⟫_𝕜) := by
  simp only [map_add, LinearMap.map_smul, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, RCLike.conj_ofReal, RCLike.re_ofReal_mul]
  ring

/-- Squared norm of a real linear combination of two orthogonal vectors. -/
private theorem norm_smul_add_smul_sq {y z : E} (hyz : ⟪y, z⟫_𝕜 = 0) (γ σ : ℝ) :
    ‖(γ : 𝕜) • y + (σ : 𝕜) • z‖ ^ 2 = γ ^ 2 * ‖y‖ ^ 2 + σ ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := 𝕜), inner_smul_left, inner_smul_right, hyz]
  simp [norm_smul, mul_pow, sq_abs]

/-- **The block energy identity** (phase-free form of Davis's 2×2 compression).  If
`y ∈ U`, `z ∈ Uᗮ` for a `T`-invariant subspace `U` of a symmetric operator,
and `y + z` is an eigenvector of `T + H` with real eigenvalue `μ`, then

`‖z‖² re ⟪y, T y⟫ - ‖y‖² re ⟪z, T z⟫ + ‖z‖² re ⟪y, H y⟫ - ‖y‖² re ⟪z, H z⟫
+ (‖z‖² - ‖y‖²) re ⟪y, H z⟫ = 0`.

The eigenvalue `μ` is eliminated; no location assumption on it is ever used.
This identity is the shared engine of both the sin 2θ and the tan 2θ theorem
below. -/
private theorem eigenvector_block_energy_identity (hT : T.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} (hUinv : ∀ u ∈ U, T u ∈ U)
    {y z : E} (hyU : y ∈ U) (hzU : z ∈ Uᗮ) {μ : ℝ}
    (hμ : T (y + z) + H (y + z) = (μ : 𝕜) • (y + z)) :
    ‖z‖ ^ 2 * RCLike.re ⟪y, T y⟫_𝕜 - ‖y‖ ^ 2 * RCLike.re ⟪z, T z⟫_𝕜
      + ‖z‖ ^ 2 * RCLike.re ⟪y, H y⟫_𝕜 - ‖y‖ ^ 2 * RCLike.re ⟪z, H z⟫_𝕜
      + (‖z‖ ^ 2 - ‖y‖ ^ 2) * RCLike.re ⟪y, H z⟫_𝕜 = 0 := by
  have hyz : ⟪y, z⟫_𝕜 = 0 := Submodule.inner_right_of_mem_orthogonal hyU hzU
  have hzy : ⟪z, y⟫_𝕜 = 0 := Submodule.inner_left_of_mem_orthogonal hyU hzU
  have hTy : T y ∈ U := hUinv y hyU
  have hTz : T z ∈ Uᗮ := map_mem_orthogonal_of_forall_map_mem hT hUinv hzU
  -- Pair the eigenvector equation with `y`.
  have e1 : RCLike.re ⟪y, T y⟫_𝕜 + RCLike.re ⟪y, H y⟫_𝕜 + RCLike.re ⟪y, H z⟫_𝕜
      = μ * ‖y‖ ^ 2 := by
    have h0 : ⟪y, T (y + z) + H (y + z)⟫_𝕜 = ⟪y, (μ : 𝕜) • (y + z)⟫_𝕜 := by rw [hμ]
    simp only [map_add, inner_add_right, inner_smul_right] at h0
    rw [Submodule.inner_right_of_mem_orthogonal hyU hTz, hyz, add_zero, add_zero] at h0
    have h1 := congrArg RCLike.re h0
    simp only [map_add, RCLike.re_ofReal_mul, inner_self_eq_norm_sq] at h1
    linarith
  -- Pair the eigenvector equation with `z`.
  have e2 : RCLike.re ⟪z, T z⟫_𝕜 + RCLike.re ⟪z, H y⟫_𝕜 + RCLike.re ⟪z, H z⟫_𝕜
      = μ * ‖z‖ ^ 2 := by
    have h0 : ⟪z, T (y + z) + H (y + z)⟫_𝕜 = ⟪z, (μ : 𝕜) • (y + z)⟫_𝕜 := by rw [hμ]
    simp only [map_add, inner_add_right, inner_smul_right] at h0
    rw [Submodule.inner_left_of_mem_orthogonal hTy hzU, hzy, zero_add, zero_add] at h0
    have h1 := congrArg RCLike.re h0
    simp only [map_add, RCLike.re_ofReal_mul, inner_self_eq_norm_sq] at h1
    linarith
  -- `‖z‖² · e1 - ‖y‖² · e2` eliminates `μ`; the mixed terms combine by symmetry
  -- of `H` at the level of real parts.
  have hW := re_inner_map_symm hH y z
  set c₂ : ℝ := ‖y‖ ^ 2
  set s₂ : ℝ := ‖z‖ ^ 2
  linear_combination s₂ * e1 - c₂ * e2 + c₂ * hW

/-- **Davis's sin 2θ theorem, orthogonal-decomposition form.**  Let `T`, `H`
be symmetric, `U` a `T`-invariant subspace with the quadratic form of `T` at
least `b * ‖·‖ ^ 2` on `U` and at most `a * ‖·‖ ^ 2` on `Uᗮ`, and let
`y + z` (`y ∈ U`, `z ∈ Uᗮ`) be a unit eigenvector of `T + H` with real
eigenvalue `μ` — **no location assumption on `μ`**.  If `‖H v‖ ≤ ε * ‖v‖` for
all `v`, then

`(b - a) * (‖y‖ * ‖z‖) ≤ ε`.

Since `2 * ‖y‖ * ‖z‖ = sin 2θ` for the angle `θ` between the eigenvector and
`U`, this is Davis's sharp two-subspace estimate `sin 2θ ≤ 2ε / (b - a)`; see
`sin_two_theta_le` for the orthogonal-projection form and `sin_two_arccos_le`
for the angle form.  The conclusion is vacuously true when `b ≤ a`, so no
gap-positivity hypothesis is needed; no orthogonal projection onto `U` is
assumed to exist. -/
theorem sin_two_theta_le_of_mem (hT : T.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} (hUinv : ∀ u ∈ U, T u ∈ U) {a b ε : ℝ}
    (hb : ∀ u ∈ U, b * ‖u‖ ^ 2 ≤ RCLike.re ⟪T u, u⟫_𝕜)
    (ha : ∀ w ∈ Uᗮ, RCLike.re ⟪T w, w⟫_𝕜 ≤ a * ‖w‖ ^ 2)
    (hε : ∀ v, ‖H v‖ ≤ ε * ‖v‖)
    {y z : E} (hyU : y ∈ U) (hzU : z ∈ Uᗮ) (hx : ‖y + z‖ = 1) {μ : ℝ}
    (hμ : T (y + z) + H (y + z) = (μ : 𝕜) • (y + z)) :
    (b - a) * (‖y‖ * ‖z‖) ≤ ε := by
  have hε0 : 0 ≤ ε := by
    have h := hε (y + z)
    rw [hx, mul_one] at h
    exact (norm_nonneg _).trans h
  have hyz : ⟪y, z⟫_𝕜 = 0 := Submodule.inner_right_of_mem_orthogonal hyU hzU
  -- Pythagoras: `‖y‖² + ‖z‖² = 1`.
  have hpyth : ‖y‖ ^ 2 + ‖z‖ ^ 2 = 1 := by
    have h := norm_add_sq (𝕜 := 𝕜) y z
    rw [hx, hyz, map_zero, mul_zero, add_zero, one_pow] at h
    linarith
  -- Degenerate cases: the product vanishes.
  rcases eq_or_ne ‖y‖ 0 with hc0 | hc0
  · rw [hc0, zero_mul, mul_zero]; exact hε0
  rcases eq_or_ne ‖z‖ 0 with hs0 | hs0
  · rw [hs0, mul_zero, mul_zero]; exact hε0
  have hc : 0 < ‖y‖ := (norm_nonneg y).lt_of_ne' hc0
  have hs : 0 < ‖z‖ := (norm_nonneg z).lt_of_ne' hs0
  have hcs : 0 < ‖y‖ * ‖z‖ := mul_pos hc hs
  -- The block energy identity and the two quadratic-form bounds.
  have key := eigenvector_block_energy_identity hT hH hUinv hyU hzU hμ
  have hby : b * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, T y⟫_𝕜 := by
    have h := hb y hyU
    rwa [← inner_conj_symm, RCLike.conj_re] at h
  have haz : RCLike.re ⟪z, T z⟫_𝕜 ≤ a * ‖z‖ ^ 2 := by
    have h := ha z hzU
    rwa [← inner_conj_symm, RCLike.conj_re] at h
  have hquad : ∀ u : E, |RCLike.re ⟪u, H u⟫_𝕜| ≤ ε * ‖u‖ ^ 2 := fun u =>
    calc |RCLike.re ⟪u, H u⟫_𝕜| ≤ ‖⟪u, H u⟫_𝕜‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖u‖ * ‖H u‖ := norm_inner_le_norm _ _
      _ ≤ ‖u‖ * (ε * ‖u‖) := by gcongr; exact hε u
      _ = ε * ‖u‖ ^ 2 := by ring
  -- Test the quadratic form of `H` against the two rotation vectors
  -- `s(c-s) • y + c(c+s) • z` and `-s(c+s) • y + c(c-s) • z`
  -- (the polynomial realization of the classical half-angle rotation:
  -- `1 - 2cs = (c-s)²`, `1 + 2cs = (c+s)²`).
  have hW := re_inner_map_symm hH y z
  have hb1 := hquad ((((‖z‖ * (‖y‖ - ‖z‖)) : ℝ) : 𝕜) • y
    + (((‖y‖ * (‖y‖ + ‖z‖)) : ℝ) : 𝕜) • z)
  rw [re_inner_smul_add_smul_map, norm_smul_add_smul_sq hyz, hW] at hb1
  have hb2 := hquad ((((-(‖z‖ * (‖y‖ + ‖z‖))) : ℝ) : 𝕜) • y
    + (((‖y‖ * (‖y‖ - ‖z‖)) : ℝ) : 𝕜) • z)
  rw [re_inner_smul_add_smul_map, norm_smul_add_smul_sq hyz, hW] at hb2
  -- Both rotation vectors have squared norm `2‖y‖²‖z‖²`.
  have hN1 : (‖z‖ * (‖y‖ - ‖z‖)) ^ 2 * ‖y‖ ^ 2 + (‖y‖ * (‖y‖ + ‖z‖)) ^ 2 * ‖z‖ ^ 2
      = 2 * (‖y‖ ^ 2 * ‖z‖ ^ 2) := by
    linear_combination (2 * ‖y‖ ^ 2 * ‖z‖ ^ 2) * hpyth
  have hN2 : (-(‖z‖ * (‖y‖ + ‖z‖))) ^ 2 * ‖y‖ ^ 2 + (‖y‖ * (‖y‖ - ‖z‖)) ^ 2 * ‖z‖ ^ 2
      = 2 * (‖y‖ ^ 2 * ‖z‖ ^ 2) := by
    linear_combination (2 * ‖y‖ ^ 2 * ‖z‖ ^ 2) * hpyth
  rw [hN1] at hb1
  rw [hN2] at hb2
  have habs1 := abs_le.mp hb1
  have habs2 := abs_le.mp hb2
  -- The difference of the two tested forms is `4cs (s² re⟪y,Ty⟫ - c² re⟪z,Tz⟫)`
  -- by the block energy identity; multiply it by `4cs` to keep everything
  -- linear over monomials.
  have key4 : 4 * (‖y‖ * ‖z‖)
      * (‖z‖ ^ 2 * RCLike.re ⟪y, T y⟫_𝕜 - ‖y‖ ^ 2 * RCLike.re ⟪z, T z⟫_𝕜
        + ‖z‖ ^ 2 * RCLike.re ⟪y, H y⟫_𝕜 - ‖y‖ ^ 2 * RCLike.re ⟪z, H z⟫_𝕜
        + (‖z‖ ^ 2 - ‖y‖ ^ 2) * RCLike.re ⟪y, H z⟫_𝕜) = 0 := by
    rw [key, mul_zero]
  have hstep1 : 4 * (‖y‖ * ‖z‖)
      * (‖z‖ ^ 2 * RCLike.re ⟪y, T y⟫_𝕜 - ‖y‖ ^ 2 * RCLike.re ⟪z, T z⟫_𝕜)
      ≤ ε * (4 * (‖y‖ ^ 2 * ‖z‖ ^ 2)) := by
    linarith [habs1.2, habs2.1, key4]
  -- Insert the two form bounds and divide by `4c²s² > 0`.
  have hmid : ‖y‖ ^ 2 * ‖z‖ ^ 2 * (b - a)
      ≤ ‖z‖ ^ 2 * RCLike.re ⟪y, T y⟫_𝕜 - ‖y‖ ^ 2 * RCLike.re ⟪z, T z⟫_𝕜 :=
    have h1 := mul_le_mul_of_nonneg_left hby (sq_nonneg ‖z‖)
    have h2 := mul_le_mul_of_nonneg_left haz (sq_nonneg ‖y‖)
    by linarith
  have hstep2 : 4 * (‖y‖ ^ 2 * ‖z‖ ^ 2) * ((b - a) * (‖y‖ * ‖z‖))
      ≤ 4 * (‖y‖ * ‖z‖)
        * (‖z‖ ^ 2 * RCLike.re ⟪y, T y⟫_𝕜 - ‖y‖ ^ 2 * RCLike.re ⟪z, T z⟫_𝕜) :=
    have h3 := mul_le_mul_of_nonneg_left hmid (by positivity : (0 : ℝ) ≤ 4 * (‖y‖ * ‖z‖))
    by linarith
  have hfinal : 4 * (‖y‖ ^ 2 * ‖z‖ ^ 2) * ((b - a) * (‖y‖ * ‖z‖))
      ≤ 4 * (‖y‖ ^ 2 * ‖z‖ ^ 2) * ε := by linarith
  have h4 : (0 : ℝ) < 4 * (‖y‖ ^ 2 * ‖z‖ ^ 2) := by
    have := mul_pos hcs hcs
    nlinarith [this]
  exact le_of_mul_le_mul_left hfinal h4

/-- **Davis's sin 2θ theorem, per-eigenvector product form.**  Under the
hypotheses of `sin_two_theta_le_of_mem`, for a unit eigenvector `x` of
`T + H` and `P = U.starProjection`,

`(b - a) * (‖P x‖ * ‖x - P x‖) ≤ ε`,

i.e. `sin 2θ ≤ 2ε / (b - a)` for the angle `θ` between `x` and `U`. -/
theorem sin_two_theta_le (hT : T.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hUinv : ∀ u ∈ U, T u ∈ U) {a b ε : ℝ}
    (hb : ∀ u ∈ U, b * ‖u‖ ^ 2 ≤ RCLike.re ⟪T u, u⟫_𝕜)
    (ha : ∀ w ∈ Uᗮ, RCLike.re ⟪T w, w⟫_𝕜 ≤ a * ‖w‖ ^ 2)
    (hε : ∀ v, ‖H v‖ ≤ ε * ‖v‖)
    {x : E} (hx : ‖x‖ = 1) {μ : ℝ} (hμ : T x + H x = (μ : 𝕜) • x) :
    (b - a) * (‖U.starProjection x‖ * ‖x - U.starProjection x‖) ≤ ε := by
  have hxsum : U.starProjection x + (x - U.starProjection x) = x := by abel
  exact sin_two_theta_le_of_mem hT hH hUinv hb ha hε
    (U.starProjection_apply_mem x) (U.sub_starProjection_mem_orthogonal x)
    (by rw [hxsum]; exact hx) (by rw [hxsum]; exact hμ)

/-- **Davis's sin 2θ theorem, angle form.**  Under the hypotheses of
`sin_two_theta_le`, with `θ = arccos ‖P x‖` the angle between the unit
eigenvector `x` and the invariant subspace `U`,

`(b - a) * sin (2θ) ≤ 2 * ε`. -/
theorem sin_two_arccos_le (hT : T.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hUinv : ∀ u ∈ U, T u ∈ U) {a b ε : ℝ}
    (hb : ∀ u ∈ U, b * ‖u‖ ^ 2 ≤ RCLike.re ⟪T u, u⟫_𝕜)
    (ha : ∀ w ∈ Uᗮ, RCLike.re ⟪T w, w⟫_𝕜 ≤ a * ‖w‖ ^ 2)
    (hε : ∀ v, ‖H v‖ ≤ ε * ‖v‖)
    {x : E} (hx : ‖x‖ = 1) {μ : ℝ} (hμ : T x + H x = (μ : 𝕜) • x) :
    (b - a) * Real.sin (2 * Real.arccos ‖U.starProjection x‖) ≤ 2 * ε := by
  have hmain := sin_two_theta_le hT hH hUinv hb ha hε hx hμ
  set y := U.starProjection x with hy
  set z := x - y with hzdef
  have hyU : y ∈ U := U.starProjection_apply_mem x
  have hzU : z ∈ Uᗮ := U.sub_starProjection_mem_orthogonal x
  have hyz : ⟪y, z⟫_𝕜 = 0 := Submodule.inner_right_of_mem_orthogonal hyU hzU
  have hxsum : y + z = x := by rw [hzdef]; abel
  have hpyth : ‖y‖ ^ 2 + ‖z‖ ^ 2 = 1 := by
    have h := norm_add_sq (𝕜 := 𝕜) y z
    simp only [hxsum, hx, hyz, map_zero, mul_zero, add_zero, one_pow] at h
    linarith
  have hc1 : ‖y‖ ≤ 1 := by nlinarith [norm_nonneg y, sq_nonneg ‖z‖, sq_nonneg (‖y‖ - 1)]
  rw [Real.sin_two_mul, Real.cos_arccos (by linarith [norm_nonneg y]) hc1, Real.sin_arccos]
  have hsqrt : Real.sqrt (1 - ‖y‖ ^ 2) = ‖z‖ := by
    rw [show (1 : ℝ) - ‖y‖ ^ 2 = ‖z‖ ^ 2 by linarith]
    exact Real.sqrt_sq (norm_nonneg z)
  rw [hsqrt]
  nlinarith [hmain]

/-- **Davis's tan 2θ theorem, orthogonal-decomposition form.**  Same setup as
`sin_two_theta_le_of_mem`, but with the *vanishing-pinch* hypotheses: `H` has
no diagonal blocks with respect to the splitting `U ⊕ Uᗮ`, i.e.
`⟪u, H u'⟫ = 0` for `u, u' ∈ U` and `⟪w, H w'⟫ = 0` for `w, w' ∈ Uᗮ`.  Then

`(b - a) * (‖y‖ * ‖z‖) ≤ |‖y‖ ^ 2 - ‖z‖ ^ 2| * ε`.

Since `2 * ‖y‖ * ‖z‖ = sin 2θ` and `‖y‖ ^ 2 - ‖z‖ ^ 2 = cos 2θ` for a unit
eigenvector, this is Davis's `tan 2θ ≤ 2ε / (b - a)`, with **no smallness
assumption** on the perturbation (the diagonal-block hypothesis replaces it).
Unlike the angle form, the product form carries no `θ ≠ π/4` side condition.
The proof reuses the `eigenvector_block_energy_identity` engine of the sin 2θ
theorem: the two
vanishing-block hypotheses kill the two diagonal `H`-terms, so the identity
collapses to `‖z‖² re⟪y,Ty⟫ - ‖y‖² re⟪z,Tz⟫ = (‖y‖² - ‖z‖²) re⟪y,Hz⟫`, and the
single mixed term is bounded directly with no rotation trick. -/
theorem tan_two_theta_le_of_mem (hT : T.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} (hUinv : ∀ u ∈ U, T u ∈ U) {a b ε : ℝ}
    (hb : ∀ u ∈ U, b * ‖u‖ ^ 2 ≤ RCLike.re ⟪T u, u⟫_𝕜)
    (ha : ∀ w ∈ Uᗮ, RCLike.re ⟪T w, w⟫_𝕜 ≤ a * ‖w‖ ^ 2)
    (hε : ∀ v, ‖H v‖ ≤ ε * ‖v‖)
    (hHU : ∀ u ∈ U, ∀ u' ∈ U, ⟪u, H u'⟫_𝕜 = 0)
    (hHUperp : ∀ w ∈ Uᗮ, ∀ w' ∈ Uᗮ, ⟪w, H w'⟫_𝕜 = 0)
    {y z : E} (hyU : y ∈ U) (hzU : z ∈ Uᗮ) (hx : ‖y + z‖ = 1) {μ : ℝ}
    (hμ : T (y + z) + H (y + z) = (μ : 𝕜) • (y + z)) :
    (b - a) * (‖y‖ * ‖z‖) ≤ |‖y‖ ^ 2 - ‖z‖ ^ 2| * ε := by
  have hε0 : 0 ≤ ε := by
    have h := hε (y + z)
    rw [hx, mul_one] at h
    exact (norm_nonneg _).trans h
  have key := eigenvector_block_energy_identity hT hH hUinv hyU hzU hμ
  have hyH : RCLike.re ⟪y, H y⟫_𝕜 = 0 := by rw [hHU y hyU y hyU]; simp
  have hzH : RCLike.re ⟪z, H z⟫_𝕜 = 0 := by rw [hHUperp z hzU z hzU]; simp
  have hby : b * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, T y⟫_𝕜 := by
    have h := hb y hyU
    rwa [← inner_conj_symm, RCLike.conj_re] at h
  have haz : RCLike.re ⟪z, T z⟫_𝕜 ≤ a * ‖z‖ ^ 2 := by
    have h := ha z hzU
    rwa [← inner_conj_symm, RCLike.conj_re] at h
  have hmix : |RCLike.re ⟪y, H z⟫_𝕜| ≤ ‖y‖ * ‖z‖ * ε :=
    calc |RCLike.re ⟪y, H z⟫_𝕜| ≤ ‖⟪y, H z⟫_𝕜‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖y‖ * ‖H z‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (ε * ‖z‖) := by gcongr; exact hε z
      _ = ‖y‖ * ‖z‖ * ε := by ring
  -- The vanishing diagonal blocks collapse the block energy identity.
  have hcollapse : ‖z‖ ^ 2 * RCLike.re ⟪y, T y⟫_𝕜 - ‖y‖ ^ 2 * RCLike.re ⟪z, T z⟫_𝕜
      = (‖y‖ ^ 2 - ‖z‖ ^ 2) * RCLike.re ⟪y, H z⟫_𝕜 := by
    rw [hyH, hzH] at key
    linear_combination key
  -- The two quadratic-form bounds give the lower bound on the collapsed LHS.
  have hlow : ‖y‖ ^ 2 * ‖z‖ ^ 2 * (b - a)
      ≤ ‖z‖ ^ 2 * RCLike.re ⟪y, T y⟫_𝕜 - ‖y‖ ^ 2 * RCLike.re ⟪z, T z⟫_𝕜 := by
    nlinarith [mul_le_mul_of_nonneg_left hby (sq_nonneg ‖z‖),
      mul_le_mul_of_nonneg_left haz (sq_nonneg ‖y‖)]
  -- Chain: `‖y‖²‖z‖²(b-a) ≤ (Y-Z)·W ≤ |Y-Z|·‖y‖‖z‖·ε`.
  have hchain : ‖y‖ ^ 2 * ‖z‖ ^ 2 * (b - a)
      ≤ |‖y‖ ^ 2 - ‖z‖ ^ 2| * (‖y‖ * ‖z‖ * ε) :=
    calc ‖y‖ ^ 2 * ‖z‖ ^ 2 * (b - a)
        ≤ ‖z‖ ^ 2 * RCLike.re ⟪y, T y⟫_𝕜 - ‖y‖ ^ 2 * RCLike.re ⟪z, T z⟫_𝕜 := hlow
      _ = (‖y‖ ^ 2 - ‖z‖ ^ 2) * RCLike.re ⟪y, H z⟫_𝕜 := hcollapse
      _ ≤ |(‖y‖ ^ 2 - ‖z‖ ^ 2) * RCLike.re ⟪y, H z⟫_𝕜| := le_abs_self _
      _ = |‖y‖ ^ 2 - ‖z‖ ^ 2| * |RCLike.re ⟪y, H z⟫_𝕜| := abs_mul _ _
      _ ≤ |‖y‖ ^ 2 - ‖z‖ ^ 2| * (‖y‖ * ‖z‖ * ε) := by gcongr
  -- Divide by `‖y‖‖z‖`; degenerate case handled by nonnegativity.
  rcases (mul_nonneg (norm_nonneg y) (norm_nonneg z)).eq_or_lt with hn | hn
  · rw [← hn, mul_zero]
    exact mul_nonneg (abs_nonneg _) hε0
  · have hh : (‖y‖ * ‖z‖) * ((b - a) * (‖y‖ * ‖z‖))
        ≤ (‖y‖ * ‖z‖) * (|‖y‖ ^ 2 - ‖z‖ ^ 2| * ε) := by
      linear_combination hchain
    exact le_of_mul_le_mul_left hh hn

/-- **Davis's tan 2θ theorem, per-eigenvector product form.**  Under the
hypotheses of `tan_two_theta_le_of_mem`, for a unit eigenvector `x` of `T + H`
and `P = U.starProjection`,

`(b - a) * (‖P x‖ * ‖x - P x‖) ≤ |‖P x‖ ^ 2 - ‖x - P x‖ ^ 2| * ε`,

i.e. `tan 2θ ≤ 2ε / (b - a)` for the angle `θ` between `x` and `U`. -/
theorem tan_two_theta_le (hT : T.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hUinv : ∀ u ∈ U, T u ∈ U) {a b ε : ℝ}
    (hb : ∀ u ∈ U, b * ‖u‖ ^ 2 ≤ RCLike.re ⟪T u, u⟫_𝕜)
    (ha : ∀ w ∈ Uᗮ, RCLike.re ⟪T w, w⟫_𝕜 ≤ a * ‖w‖ ^ 2)
    (hε : ∀ v, ‖H v‖ ≤ ε * ‖v‖)
    (hHU : ∀ u ∈ U, ∀ u' ∈ U, ⟪u, H u'⟫_𝕜 = 0)
    (hHUperp : ∀ w ∈ Uᗮ, ∀ w' ∈ Uᗮ, ⟪w, H w'⟫_𝕜 = 0)
    {x : E} (hx : ‖x‖ = 1) {μ : ℝ} (hμ : T x + H x = (μ : 𝕜) • x) :
    (b - a) * (‖U.starProjection x‖ * ‖x - U.starProjection x‖)
      ≤ |‖U.starProjection x‖ ^ 2 - ‖x - U.starProjection x‖ ^ 2| * ε := by
  have hxsum : U.starProjection x + (x - U.starProjection x) = x := by abel
  exact tan_two_theta_le_of_mem hT hH hUinv hb ha hε hHU hHUperp
    (U.starProjection_apply_mem x) (U.sub_starProjection_mem_orthogonal x)
    (by rw [hxsum]; exact hx) (by rw [hxsum]; exact hμ)

end TauCeti
