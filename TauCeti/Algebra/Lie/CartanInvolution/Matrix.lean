/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.Algebra.Lie.Matrix.NegConjTranspose
public import TauCeti.Analysis.Matrix.Frobenius
import TauCeti.Algebra.Lie.AdjointAction.Basic
import TauCeti.Algebra.Lie.Submodule.Atom
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative
import TauCeti.LinearAlgebra.BilinearForm.SkewAdjoint

/-!
# Cartan involutions of matrix Lie algebras

Let `𝕜` be `ℝ` or `ℂ` and let `𝔤₀` be a real Lie subalgebra of `𝔤𝔩_n(𝕜)` closed under conjugate
transpose. Then `θ X = -Xᴴ` is an involutive automorphism of `𝔤₀`, and it is a Cartan involution
exactly when the centre of `𝔤₀` is trivial; in particular it is a Cartan involution when `𝔤₀` is
semisimple (Knapp, Prop. 6.28).

The proof uses the real inner product `⟪X, Y⟫ = Re tr(X Yᴴ)` on matrices (`TauCeti.reTraceForm`):
for `X ∈ 𝔤₀` the adjoint of `ad X` for this inner product is `ad Xᴴ`, so
`-B(X, θ Y) = tr(ad X ∘ ad Yᴴ)` and `-B(X, θ X) = tr(ad X ∘ (ad X)*)`, which is nonnegative and
vanishes only when `ad X = 0`, that is, when `X` is central.

On each simple ideal `I` of a semisimple such `𝔤₀`, the inner product `B_θ(X, Y) = -B(X, θ Y)` is a
positive multiple of `Re tr(X Yᴴ)`. Both forms are positive definite, and `ad Z` has adjoint `ad Zᴴ`
for both, so the endomorphism `A` with `B_θ(A X, Y) = Re tr(X Yᴴ)` is self-adjoint and commutes with
every `ad Z`. Its eigenspaces are then ideals, and since `A` preserves `I = ⁅I, 𝔤₀⁆`, the ideal `I`
lies in one of them.

The applications to `𝔰𝔬(p, q)`, `𝔰𝔲(p, q)` and `𝔰𝔭(2n, ℝ)` are in
`TauCeti.Algebra.Lie.Orthogonal.Cartan`, `TauCeti.Algebra.Lie.IndefiniteUnitary.Cartan` and
`TauCeti.Algebra.Lie.Symplectic.Cartan`.

## Main results

* `TauCeti.reTraceForm_lie_apply`: `⟪[X, Y], Z⟫ = ⟪Y, [Xᴴ, Z]⟫`.
* `LieSubalgebra.mem_fixedSubalgebra_restrictNegConjTranspose_iff`,
  `LieSubalgebra.mem_cartanP_restrictNegConjTranspose_iff`: for `θ X = -Xᴴ`, `𝔨` is the
  skew-Hermitian and `𝔭` the Hermitian elements of `𝔤₀`.
* `LieSubalgebra.killingForm_restrictNegConjTranspose`: `B(X, θ Y) = -tr(ad X ∘ ad Yᴴ)`.
* `LieSubalgebra.isCartanInvolution_restrictNegConjTranspose_iff`: `X ↦ -Xᴴ` is a Cartan
  involution of a real Lie subalgebra closed under conjugate transpose exactly when its centre is
  trivial.
* `LieSubalgebra.isCartanInvolution_restrictNegConjTranspose`: it is a Cartan involution of a real
  Lie subalgebra with trivial radical (for instance a semisimple one) closed under conjugate
  transpose.
* `LieSubalgebra.exists_twistedKillingForm_eq_mul_reTraceForm`: on a minimal nonzero ideal of
  such a Lie subalgebra, `B_θ(X, Y) = c Re tr(X Yᴴ)` for some `c > 0`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §2, Proposition 6.28.
-/

public section

open LieAlgebra Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The adjoint of `ad X` for `Re tr(X Yᴴ)` is `ad Xᴴ`: `⟪[X, Y], Z⟫ = ⟪Y, [Xᴴ, Z]⟫`. -/
theorem reTraceForm_lie_apply (X Y Z : Matrix n n 𝕜) :
    reTraceForm 𝕜 n n ⁅X, Y⁆ Z = reTraceForm 𝕜 n n Y ⁅Xᴴ, Z⁆ := by
  simp only [reTraceForm_eq_frobenius_real_inner, frobenius_real_inner_eq_re_inner (𝕜 := 𝕜),
    frobenius_inner_lie_left]

end TauCeti

namespace LieSubalgebra

open TauCeti

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
  (L : LieSubalgebra ℝ (Matrix n n 𝕜)) (hL : ∀ X ∈ L, Xᴴ ∈ L)

/-- The fixed subalgebra `𝔨` of `θ X = -Xᴴ` consists of the skew-Hermitian elements. -/
theorem mem_fixedSubalgebra_restrictNegConjTranspose_iff {X : L} :
    X ∈ (L.restrictNegConjTranspose hL).toLieHom.fixedSubalgebra ↔
      (X : Matrix n n 𝕜)ᴴ = -(X : Matrix n n 𝕜) := by
  simp [LieHom.mem_fixedSubalgebra, Subtype.ext_iff, neg_eq_iff_eq_neg]

/-- The `-1`-eigenspace `𝔭` of `θ X = -Xᴴ` consists of the Hermitian elements. -/
theorem mem_cartanP_restrictNegConjTranspose_iff {X : L} :
    X ∈ (L.restrictNegConjTranspose hL).cartanP ↔ (X : Matrix n n 𝕜)ᴴ = (X : Matrix n n 𝕜) := by
  simp [LieEquiv.mem_cartanP, Subtype.ext_iff]

/-- The Killing form twisted by `θ X = -Xᴴ` is minus the trace pairing of `ad X` and `ad Yᴴ`:
`B(X, θ Y) = -tr(ad X ∘ ad Yᴴ)`. -/
theorem killingForm_restrictNegConjTranspose (x y : L) :
    killingForm ℝ L x (L.restrictNegConjTranspose hL y) =
      -LinearMap.trace ℝ L (ad ℝ L x * ad ℝ L ⟨(y : Matrix n n 𝕜)ᴴ, hL _ y.property⟩) := by
  have hθ : L.restrictNegConjTranspose hL y = -⟨(y : Matrix n n 𝕜)ᴴ, hL _ y.property⟩ :=
    Subtype.ext (by simp)
  rw [hθ, map_neg, killingForm_apply_apply, ← Module.End.mul_eq_comp]

/-- The trace form `Re tr(X Yᴴ)` restricted to `L`. -/
private noncomputable def reTraceFormRestrict : LinearMap.BilinForm ℝ L :=
  (reTraceForm 𝕜 n n).restrict L.toSubmodule

private theorem reTraceFormRestrict_apply (x y : L) :
    reTraceFormRestrict L x y = reTraceForm 𝕜 n n x y :=
  -- `L.toSubmodule` and `L` have the same elements.
  rfl

/-- For a real Lie subalgebra `L` closed under conjugate transpose, `B(X, -Xᴴ) < 0` for every
noncentral `X` in `L`. -/
private theorem killingForm_restrictNegConjTranspose_neg (x : L) (hx : x ∉ center ℝ L) :
    killingForm ℝ L x (L.restrictNegConjTranspose hL x) < 0 := by
  let x' : L := ⟨(x : Matrix n n 𝕜)ᴴ, hL _ x.property⟩
  let P := reTraceFormRestrict L
  have hP (y z : L) : P y z = reTraceForm 𝕜 n n y z := reTraceFormRestrict_apply L y z
  have hsymm : P.IsSymm := ⟨fun y z ↦ by rw [hP, hP]; exact (isSymm_reTraceForm 𝕜 n n).eq y z⟩
  have hpos : P.toQuadraticMap.PosDef := fun y hy ↦ by
    simpa only [LinearMap.BilinMap.toQuadraticMap_apply, hP] using
      posDef_reTraceForm 𝕜 n n (y : Matrix n n 𝕜) (by simpa using hy)
  have hadj : LinearMap.IsAdjointPair P P (ad ℝ L x) (ad ℝ L x') := fun y z ↦ by
    simp only [ad_apply, hP, LieSubalgebra.coe_bracket]
    exact reTraceForm_lie_apply _ _ _
  have hne : ad ℝ L x ≠ 0 := fun h ↦ hx (TauCeti.LieAlgebra.ad_eq_zero_iff.mp h)
  rw [killingForm_restrictNegConjTranspose, neg_lt_zero]
  exact (LinearMap.BilinForm.trace_mul_nonneg_of_isAdjointPair P hsymm hpos hadj).lt_of_ne'
    ((LinearMap.BilinForm.trace_mul_eq_zero_iff_of_isAdjointPair P hsymm hpos hadj).not.mpr hne)

/-- **Knapp, Prop. 6.28.** For a real Lie subalgebra `L` of `𝔤𝔩_n(𝕜)` closed under conjugate
transpose, `X ↦ -Xᴴ` is a Cartan involution of `L` exactly when the centre of `L` is trivial. -/
theorem isCartanInvolution_restrictNegConjTranspose_iff :
    (L.restrictNegConjTranspose hL).IsCartanInvolution ↔ center ℝ L = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ LieEquiv.isCartanInvolution_iff.mpr
    ⟨L.restrictNegConjTranspose_involutive hL, fun x hx ↦
      killingForm_restrictNegConjTranspose_neg L hL x (by rwa [h, LieSubmodule.mem_bot])⟩⟩
  have := h.isSemisimple
  exact center_eq_bot ℝ L

/-- **Knapp, Prop. 6.28.** For a real Lie subalgebra `L` of `𝔤𝔩_n(𝕜)` with trivial radical (for
instance a semisimple one) closed under conjugate transpose, `X ↦ -Xᴴ` is a Cartan involution. -/
theorem isCartanInvolution_restrictNegConjTranspose [HasTrivialRadical ℝ L] :
    (L.restrictNegConjTranspose hL).IsCartanInvolution :=
  (L.isCartanInvolution_restrictNegConjTranspose_iff hL).mpr (center_eq_bot ℝ L)

end LieSubalgebra

/-! ### The twisted Killing form on a simple ideal -/

namespace LieSubalgebra

open TauCeti

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
  (L : LieSubalgebra ℝ (Matrix n n 𝕜)) (hL : ∀ X ∈ L, Xᴴ ∈ L)

variable [HasTrivialRadical ℝ L]

/-- The endomorphism `A` of `L` with `B_θ(A x, y) = Re tr(x yᴴ)`. -/
private noncomputable def traceFormRatio : Module.End ℝ L :=
  (reTraceFormRestrict L).symmCompOfNondegenerate
    (L.restrictNegConjTranspose hL).twistedKillingForm
    (L.isCartanInvolution_restrictNegConjTranspose hL).nondegenerate_twistedKillingForm

private theorem twistedKillingForm_traceFormRatio (x y : L) :
    (L.restrictNegConjTranspose hL).twistedKillingForm (traceFormRatio L hL x) y =
      reTraceForm 𝕜 n n x y := by
  rw [traceFormRatio, LinearMap.BilinForm.comp_symmCompOfNondegenerate_apply,
    reTraceFormRestrict_apply]

/-- `A` commutes with every `ad z`. -/
private theorem traceFormRatio_lie (z x : L) :
    traceFormRatio L hL ⁅z, x⁆ = ⁅z, traceFormRatio L hL x⁆ := by
  refine sub_eq_zero.1
    ((L.isCartanInvolution_restrictNegConjTranspose hL).nondegenerate_twistedKillingForm.1 _
      fun y ↦ ?_)
  simp only [map_sub, LinearMap.sub_apply, twistedKillingForm_traceFormRatio,
    (L.restrictNegConjTranspose hL).twistedKillingForm_lie_apply
      (L.restrictNegConjTranspose_involutive hL),
    LieSubalgebra.coe_bracket, reTraceForm_lie_apply, NegMemClass.coe_neg,
    coe_restrictNegConjTranspose_apply, neg_neg, sub_self]

/-- `A` is self-adjoint for `B_θ`. -/
private theorem isSelfAdjoint_traceFormRatio :
    (L.restrictNegConjTranspose hL).twistedKillingForm.IsSelfAdjoint (traceFormRatio L hL) :=
  fun x y ↦ by
    rw [twistedKillingForm_traceFormRatio,
      (L.isCartanInvolution_restrictNegConjTranspose hL).isSymm_twistedKillingForm.eq x,
      twistedKillingForm_traceFormRatio,
      (isSymm_reTraceForm 𝕜 n n).eq]

/-- `A` as a morphism of Lie modules, since it commutes with every `ad z`. -/
private noncomputable def traceFormRatioHom : L →ₗ⁅ℝ,L⁆ L :=
  { traceFormRatio L hL with map_lie' := traceFormRatio_lie L hL _ _ }

private theorem traceFormRatioHom_apply (x : L) :
    traceFormRatioHom L hL x = traceFormRatio L hL x :=
  rfl

/-- **`B_θ` is a positive multiple of `Re tr(X Yᴴ)` on each simple ideal.** For a real Lie
subalgebra `L` of `𝔤𝔩_n(𝕜)` with trivial radical, closed under conjugate transpose, and a minimal
nonzero ideal `I` of `L`, there is `c > 0` with
`B_θ(X, Y) = c Re tr(X Yᴴ)` for `X ∈ I` and every `Y`, where `θ X = -Xᴴ`. -/
theorem exists_twistedKillingForm_eq_mul_reTraceForm {I : LieIdeal ℝ L} (hI : IsAtom I) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ I, ∀ y : L,
      (L.restrictNegConjTranspose hL).twistedKillingForm x y = c * reTraceForm 𝕜 n n x y := by
  have hθ := L.isCartanInvolution_restrictNegConjTranspose hL
  set A := traceFormRatio L hL
  -- `⁅L, I⁆ = I`, since `L` has trivial centre; so `A I ⊆ I`, as `A ⁅x, y⁆ = ⁅x, A y⁆`.
  have hA (x : L) (hx : x ∈ I) : A x ∈ I :=
    map_le_of_top_lie_eq (top_lie_eq_self_of_isAtom (center_eq_bot ℝ L) hI)
      (traceFormRatioHom L hL) (LieSubmodule.mem_map_of_mem hx)
  -- `A` is diagonalizable, so `I` is the sum of its intersections with the eigenspaces of `A`;
  -- these are ideals, so one of them is `I`.
  have htop : ⨆ μ : ℝ, A.eigenspace μ = ⊤ :=
    LinearMap.IsSelfAdjoint.iSup_eigenspace_eq_top hθ.posDef_twistedKillingForm
      (isSelfAdjoint_traceFormRatio L hL)
  have hsum : I.toSubmodule = ⨆ μ : ℝ, I.toSubmodule ⊓ A.eigenspace μ := by
    rw [← Submodule.inf_iSup_genEigenspace hA, htop, inf_top_eq]
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, I.toSubmodule ⊓ A.eigenspace μ ≠ ⊥ := by
    by_contra! h
    exact hI.1 ((LieSubmodule.toSubmodule_eq_bot _).1 (hsum.trans (iSup_eq_bot.2 h)))
  -- The eigenspace of `A` for `μ` is the kernel of the Lie module morphism `A - μ`.
  set E := (traceFormRatioHom L hL - μ • 1).ker
  have hE : E.toSubmodule = A.eigenspace μ := by
    ext x
    simp [E, A, sub_eq_zero, traceFormRatioHom_apply]
  have hIμ : I ≤ E := by
    refine inf_eq_left.1 ((hI.le_iff.1 inf_le_left).resolve_left fun h ↦ hμ ?_)
    have h' := congrArg LieSubmodule.toSubmodule h
    rwa [LieSubmodule.inf_toSubmodule, LieSubmodule.bot_toSubmodule, hE] at h'
  have hAx (x : L) (hx : x ∈ I) (y : L) :
      reTraceForm 𝕜 n n x y = μ * (L.restrictNegConjTranspose hL).twistedKillingForm x y := by
    have : A x = μ • x := Module.End.mem_eigenspace_iff.1 (hE ▸ hIμ hx)
    rw [← twistedKillingForm_traceFormRatio L hL, this, LinearMap.map_smul₂, smul_eq_mul]
  -- `μ > 0`: both forms are positive definite.
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (fun h ↦ hI.1 ((LieSubmodule.toSubmodule_eq_bot _).1 h))
  have hP : 0 < reTraceForm 𝕜 n n x x :=
    posDef_reTraceForm 𝕜 n n (x : Matrix n n 𝕜) (by simpa using hx0)
  have hB : 0 < (L.restrictNegConjTranspose hL).twistedKillingForm x x :=
    hθ.posDef_twistedKillingForm x hx0
  have hμ0 : 0 < μ := pos_of_mul_pos_left (hAx x hx x ▸ hP) hB.le
  refine ⟨μ⁻¹, inv_pos.2 hμ0, fun x hx y ↦ ?_⟩
  rw [hAx x hx y, inv_mul_cancel_left₀ hμ0.ne']

end LieSubalgebra
