/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.Basic
public import TauCeti.MeasureTheory.Function.Lp.ContinuousFunctions

/-!
# Toeplitz operators on boundary Hardy space

For an essentially bounded symbol `a` on `UnitAddCircle`, the Toeplitz operator `T_a` is the
compression `P M_a |H²` of the multiplication operator `M_a` on circle `L²` to the boundary Hardy
space `H²`, where `P` is the orthogonal projection onto `H²`. This file bundles the symbol map
`a ↦ T_a` as a bounded complex-linear map `TauCeti.toeplitz` and proves its basic properties:

* `TauCeti.toeplitz_apply_eq_zero_iff`: `T_a f = 0` exactly when `a f` lies in the orthogonal
  complement of Hardy space;
* `TauCeti.inner_hardyBasis_toeplitz_hardyBasis`: in the Hardy basis `e₀, e₁, …` the matrix
  entry `(i, j)` of `T_a` is the Fourier coefficient `â(i - j)`;
* `TauCeti.adjoint_toeplitz`: the adjoint of `T_a` is the Toeplitz operator of the complex
  conjugate symbol;
* `TauCeti.toeplitz_const`, `TauCeti.toeplitz_algebraMap`, `TauCeti.toeplitz_fourierLp_zero`,
  `TauCeti.toeplitz_toLp_one`: a constant symbol acts by scalar multiplication, and `e_0` or
  `1 : C(UnitAddCircle, ℂ)` induces the identity operator;
* `TauCeti.toeplitz_fourierLp_natCast_hardyBasis`, `TauCeti.toeplitz_fourierLp_one_hardyBasis`:
  the Toeplitz operator of `e_m`, `m ≥ 0`, raises the Hardy basis by `m`; in particular the
  forward shift `S = T_z` sends `eₙ` to `eₙ₊₁`;
* `TauCeti.coe_toeplitz_fourierLp_natCast_apply`, `TauCeti.isometry_toeplitz_fourierLp_natCast`,
  `TauCeti.toeplitz_fourierLp_natCast`: for `m ≥ 0`, the Toeplitz operator of `e_m` is
  multiplication by `e_m`, an isometry, and the `m`th power of the forward shift;
* `TauCeti.toeplitz_fourierLp_neg`: the Toeplitz operator of `e_(-k)` is the adjoint of that of
  `e_k`;
* `TauCeti.toeplitz_fourierLp_neg_one_hardyBasis_zero`,
  `TauCeti.toeplitz_fourierLp_neg_one_hardyBasis_succ`,
  `TauCeti.toeplitz_fourierLp_neg_one_comp_one`, `TauCeti.toeplitz_fourierLp_one_comp_neg_one`,
  `TauCeti.ker_toeplitz_fourierLp_one`, `TauCeti.toeplitz_fourierLp_neg_one_surjective`,
  `TauCeti.ker_toeplitz_fourierLp_neg_one`: the backward shift `S† = T_(e_{-1})` annihilates `e₀`,
  sends `eₙ₊₁` to `eₙ`, satisfies `S† ∘L S = id` and `S ∘L S† = id - P_{e₀}`, and is surjective with
  kernel `ℂ ∙ e₀`, while `S` has trivial kernel;
* `TauCeti.norm_toeplitz`: the operator norm of `T_a` is exactly `‖a‖∞`, so the symbol map is an
  isometry (`TauCeti.isometry_toeplitz`) and in particular injective
  (`TauCeti.toeplitz_injective`).

The inequality `‖T_a‖ ≤ ‖a‖∞` is immediate from the compression. For the reverse inequality,
multiplication by a Fourier monomial `e_N` is unitary on circle `L²` and commutes with `M_a`, and
for `N` large it moves any two trigonometric polynomials `f, g` into `H²`. Hence
`|⟪f, a g⟫| = |⟪e_N f, T_a (e_N g)⟫| ≤ ‖T_a‖ ‖f‖ ‖g‖`, which extends by density to all of `L²`
and gives `‖M_a‖ ≤ ‖T_a‖`; the operator norm of `M_a` is `‖a‖∞`. This norm-equality
argument follows Böttcher–Silbermann, *Analysis of Toeplitz Operators*, §2.

The conventions are those of Conway, *A Course in Functional Analysis*, second edition, and of
E. Park, *Toeplitz operators*: normalized Haar measure, the modes `exp (2πint)` and inner products
conjugate linear in the first variable.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TauCeti

/-- Compressing multiplication by `a` to Hardy space does not increase the operator norm. -/
private theorem norm_compress_multiplicationOperator_le
    (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    ‖hardySubmodule.orthogonalProjectionOnto ∘L Lp.multiplicationOperator a ∘L
      hardySubmodule.subtypeL‖ ≤ ‖a‖ := by
  calc _ ≤ ‖hardySubmodule.orthogonalProjectionOnto‖ *
        (‖Lp.multiplicationOperator (E := ℂ) a‖ * ‖hardySubmodule.subtypeL‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖a‖ * 1) := by
        gcongr
        · exact hardySubmodule.orthogonalProjectionOnto_norm_le
        · exact Lp.norm_multiplicationOperator_le a
        · exact Submodule.norm_subtypeL_le _
    _ = ‖a‖ := by ring

/-- The Toeplitz operator map, sending an essentially bounded symbol `a` on the unit circle to the
compression `T_a = P M_a |H²` of multiplication by `a` to boundary Hardy space. -/
def toeplitz :
    Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)) →L[ℂ] HardySpace →L[ℂ] HardySpace :=
  LinearMap.mkContinuous
    { toFun a := hardySubmodule.orthogonalProjectionOnto ∘L Lp.multiplicationOperator a ∘L
        hardySubmodule.subtypeL
      map_add' a b := by
        simp only [Lp.multiplicationOperator_add, ContinuousLinearMap.add_comp,
          ContinuousLinearMap.comp_add]
      map_smul' c a := by
        simp only [Lp.multiplicationOperator_smul, ContinuousLinearMap.smul_comp,
          ContinuousLinearMap.comp_smul, RingHom.id_apply] }
    1 fun a ↦ (one_mul ‖a‖).symm ▸ norm_compress_multiplicationOperator_le a

/-- The Toeplitz operator of `a` compresses the multiplication operator of `a` to Hardy space. -/
theorem toeplitz_apply (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    toeplitz a = hardySubmodule.orthogonalProjectionOnto ∘L
      Lp.multiplicationOperator a ∘L hardySubmodule.subtypeL :=
  (rfl)

/-- The ambient value of `T_a f` is the Hardy projection of the product `a f`. -/
theorem coe_toeplitz_apply (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) (f : HardySpace) :
    (toeplitz a f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) =
      hardySubmodule.starProjection (a • (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))) := by
  rw [toeplitz_apply, Submodule.starProjection_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, Lp.multiplicationOperator_apply]

/-- A Hardy function `f` lies in the kernel of the Toeplitz operator `T_a` exactly when the
product `a f` lies in the orthogonal complement of Hardy space, that is, when `a f` has only
negative Fourier modes. -/
theorem toeplitz_apply_eq_zero_iff (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)))
    (f : HardySpace) :
    toeplitz a f = 0 ↔
      a • (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) ∈ hardySubmoduleᗮ := by
  simp only [toeplitz_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    Lp.multiplicationOperator_apply, Submodule.orthogonalProjectionOnto_eq_zero_iff]

/-- Compressing to Hardy space does not change inner products against Hardy functions. -/
theorem inner_toeplitz_apply (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)))
    (f g : HardySpace) :
    ⟪f, toeplitz a g⟫_ℂ =
      ⟪(f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))),
        a • (g : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))⟫_ℂ := by
  rw [toeplitz_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, Submodule.subtypeL_apply,
    Lp.multiplicationOperator_apply]

/-- The Hardy coordinates of `T_a f` are the nonnegative Fourier coefficients of `a f`. -/
@[simp]
theorem hardyBasis_repr_toeplitz_apply (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)))
    (f : HardySpace) (i : ℕ) :
    hardyBasis.repr (toeplitz a f) i =
      fourierCoeff (a • (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))) (i : ℤ) := by
  rw [HilbertBasis.repr_apply_apply, inner_toeplitz_apply, coe_hardyBasis,
    ← HilbertBasis.repr_apply_apply, fourierBasis_repr]

/-- **Matrix formula.** In the Hardy basis `e₀, e₁, …`, the `(i, j)` entry of the Toeplitz
operator `T_a` is the Fourier coefficient `â(i - j)`. -/
theorem inner_hardyBasis_toeplitz_hardyBasis (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)))
    (i j : ℕ) :
    ⟪hardyBasis i, toeplitz a (hardyBasis j)⟫_ℂ = fourierCoeff a ((i : ℤ) - j) := by
  rw [← HilbertBasis.repr_apply_apply, hardyBasis_repr_toeplitz_apply, coe_hardyBasis,
    fourierCoeff_smul_fourierBasis]

/-- The adjoint of the Toeplitz operator `T_a` is the Toeplitz operator of the complex conjugate
symbol. -/
@[simp]
theorem adjoint_toeplitz (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    ContinuousLinearMap.adjoint (toeplitz a) = toeplitz (star a) := by
  rw [toeplitz_apply, toeplitz_apply, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp, Submodule.adjoint_subtypeL,
    Submodule.adjoint_orthogonalProjectionOnto, Lp.adjoint_multiplicationOperator,
    ContinuousLinearMap.comp_assoc]

/-- A constant symbol acts on Hardy space by scalar multiplication. -/
@[simp]
theorem toeplitz_const (c : ℂ) :
    toeplitz (Lp.const ∞ (AddCircle.haarAddCircle (T := 1)) c) =
      c • ContinuousLinearMap.id ℂ HardySpace := by
  ext f : 2
  rw [coe_toeplitz_apply, ← Lp.multiplicationOperator_apply, Lp.multiplicationOperator_const]
  simp [Submodule.starProjection_eq_self_iff.mpr (hardySubmodule.smul_mem c f.property)]

/-- A symbol in the scalar embedding acts on Hardy space by scalar multiplication. -/
@[simp]
theorem toeplitz_algebraMap (c : ℂ) :
    toeplitz (algebraMap ℂ (Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) c) =
      c • ContinuousLinearMap.id ℂ HardySpace := by
  rw [Lp.algebraMap_eq_const, Algebra.algebraMap_self_apply, toeplitz_const]

/-- The continuous symbol `1` induces the identity Toeplitz operator on `HardySpace`.

Not `@[simp]`, because `simp` already reduces the left-hand side via `ContinuousMap.toLp_one`,
`toeplitz_const`, and `one_smul`. -/
theorem toeplitz_toLp_one :
    toeplitz (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ (1 : C(UnitAddCircle, ℂ))) =
      ContinuousLinearMap.id ℂ HardySpace := by
  rw [ContinuousMap.toLp_one, toeplitz_const, one_smul]

/-- The Toeplitz operator of the Fourier monomial `e_m`, `m ≥ 0`, raises the Hardy basis by
`m`. -/
@[simp]
theorem toeplitz_fourierLp_natCast_hardyBasis (m n : ℕ) :
    toeplitz (fourierLp (T := 1) ∞ (m : ℤ)) (hardyBasis n) = hardyBasis (m + n) := by
  apply Subtype.ext
  rw [coe_toeplitz_apply, coe_hardyBasis, fourierLp_smul_fourierBasis, coe_hardyBasis,
    Nat.cast_add]
  exact Submodule.starProjection_eq_self_iff.mpr
    (by exact_mod_cast fourierBasis_mem_hardySubmodule (m + n))

/-- The forward shift `S = T_z` on Hardy space sends `eₙ` to `eₙ₊₁`. -/
@[simp]
theorem toeplitz_fourierLp_one_hardyBasis (n : ℕ) :
    toeplitz (fourierLp (T := 1) ∞ 1) (hardyBasis n) = hardyBasis (n + 1) := by
  simpa [add_comm] using toeplitz_fourierLp_natCast_hardyBasis 1 n

/-- For `m ≥ 0`, the Toeplitz operator of the Fourier monomial `e_m` is multiplication by `e_m`. -/
theorem coe_toeplitz_fourierLp_natCast_apply (m : ℕ) (f : HardySpace) :
    (toeplitz (fourierLp (T := 1) ∞ (m : ℤ)) f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) =
      fourierLp (T := 1) ∞ (m : ℤ) • (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) := by
  rw [coe_toeplitz_apply]
  exact Submodule.starProjection_eq_self_iff.mpr
    (fourierLp_natCast_smul_mem_hardySubmodule m f.property)

/-- The forward shift `S = T_{e_1}` is multiplication by `e_1`. -/
theorem coe_toeplitz_fourierLp_one_apply (f : HardySpace) :
    (toeplitz (fourierLp (T := 1) ∞ 1) f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) =
      fourierLp (T := 1) ∞ 1 • (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) := by
  exact_mod_cast coe_toeplitz_fourierLp_natCast_apply 1 f

/-- For `m ≥ 0`, the Toeplitz operator of the Fourier monomial `e_m` preserves norms. The norms
are taken in `L²`, the simp normal form of norms of Hardy functions. -/
@[simp]
theorem norm_toeplitz_fourierLp_natCast_apply (m : ℕ) (f : HardySpace) :
    ‖(toeplitz (fourierLp (T := 1) ∞ (m : ℤ)) f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))‖ =
      ‖(f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))‖ := by
  rw [coe_toeplitz_fourierLp_natCast_apply, ← Lp.multiplicationOperator_apply]
  exact Lp.norm_multiplicationOperator_apply_of_ae_norm_eq_one (ae_norm_fourierLp_eq_one ∞ _) _

/-- For `m ≥ 0`, the Toeplitz operator of the Fourier monomial `e_m` is an isometry of Hardy
space. -/
theorem isometry_toeplitz_fourierLp_natCast (m : ℕ) :
    Isometry (toeplitz (fourierLp (T := 1) ∞ (m : ℤ))) :=
  AddMonoidHomClass.isometry_of_norm _ fun f => by
    rw [← Submodule.norm_coe, ← Submodule.norm_coe f, norm_toeplitz_fourierLp_natCast_apply]

/-- The Toeplitz operator of the Fourier monomial `e_m`, `m ≥ 0`, is the `m`th power of the
forward shift `S = T_{e_1}`. -/
theorem toeplitz_fourierLp_natCast (m : ℕ) :
    toeplitz (fourierLp (T := 1) ∞ (m : ℤ)) = toeplitz (fourierLp (T := 1) ∞ 1) ^ m := by
  induction m with
  | zero =>
    ext f : 1
    apply Subtype.ext
    rw [pow_zero, one_apply_eq_self]
    exact_mod_cast (coe_toeplitz_fourierLp_natCast_apply 0 f).trans (fourierLp_zero_smul _)
  | succ m ih =>
    ext f : 1
    apply Subtype.ext
    rw [pow_succ', ← ih, mul_apply_eq_comp, coe_toeplitz_fourierLp_one_apply,
      coe_toeplitz_fourierLp_natCast_apply, coe_toeplitz_fourierLp_natCast_apply,
      fourierLp_smul_fourierLp_smul, Nat.cast_succ, add_comm]

/-- The Toeplitz operator of the constant mode `e_0` is the identity on `HardySpace`. -/
@[simp]
theorem toeplitz_fourierLp_zero :
    toeplitz (fourierLp (T := 1) ∞ 0) = ContinuousLinearMap.id ℂ HardySpace := by
  simpa [ContinuousLinearMap.one_def] using toeplitz_fourierLp_natCast 0

/-- The Toeplitz operator of the Fourier monomial `e_(-k)` is the adjoint of that of `e_k`. -/
theorem toeplitz_fourierLp_neg (k : ℤ) :
    toeplitz (fourierLp (T := 1) ∞ (-k)) =
      ContinuousLinearMap.adjoint (toeplitz (fourierLp (T := 1) ∞ k)) := by
  rw [adjoint_toeplitz, star_fourierLp]

/-- The backward shift `T_(e_{-1})` annihilates the constant Hardy mode `hardyBasis 0`. -/
@[simp]
theorem toeplitz_fourierLp_neg_one_hardyBasis_zero :
    toeplitz (fourierLp (T := 1) ∞ (-1)) (hardyBasis 0) = 0 := by
  apply hardyBasis.repr.injective
  rw [hardyBasis.repr.map_zero]
  apply lp.ext
  funext i
  rw [lp.coeFn_zero, Pi.zero_apply, hardyBasis_repr_toeplitz_apply, coe_hardyBasis,
    fourierLp_smul_fourierBasis, Nat.cast_zero, add_zero, coe_fourierBasis,
    fourierCoeff_fourierLp, ite_eq_right (by omega)]

/-- The backward shift `T_(e_{-1})` lowers every positive Hardy basis mode by `1`. -/
@[simp]
theorem toeplitz_fourierLp_neg_one_hardyBasis_succ (n : ℕ) :
    toeplitz (fourierLp (T := 1) ∞ (-1)) (hardyBasis (n + 1)) = hardyBasis n := by
  apply hardyBasis.repr.injective
  apply lp.ext
  funext i
  have hidx : (-1 : ℤ) + ((n + 1 : ℕ) : ℤ) = (n : ℤ) := by omega
  rw [hardyBasis_repr_toeplitz_apply, coe_hardyBasis, fourierLp_smul_fourierBasis, hidx,
    ← coe_hardyBasis, ← hardyBasis_repr]

/-- The backward shift is a left inverse to the forward shift: `S† ∘L S = id`. -/
@[simp]
theorem toeplitz_fourierLp_neg_one_comp_one :
    toeplitz (fourierLp (T := 1) ∞ (-1)) ∘L toeplitz (fourierLp (T := 1) ∞ 1) =
      ContinuousLinearMap.id ℂ HardySpace := by
  apply ContinuousLinearMap.ext_on (s := Set.range hardyBasis) (by
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, hardyBasis.dense_span]
    rfl)
  rintro _ ⟨n, rfl⟩
  simp

/-- **Shift defect identity.** Composing the forward shift after the backward shift differs from
the identity by the rank-one orthogonal projection onto `ℂ ∙ hardyBasis 0`. -/
theorem toeplitz_fourierLp_one_comp_neg_one :
    toeplitz (fourierLp (T := 1) ∞ 1) ∘L toeplitz (fourierLp (T := 1) ∞ (-1)) =
      ContinuousLinearMap.id ℂ HardySpace - (ℂ ∙ hardyBasis 0).starProjection := by
  apply ContinuousLinearMap.ext_on (s := Set.range hardyBasis) (by
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, hardyBasis.dense_span]
    rfl)
  rintro _ ⟨k, rfl⟩
  cases k <;> simp [span_hardyBasis_starProjection_hardyBasis]

/-- The forward shift `S = T_(e_1)` is injective: its kernel is trivial. -/
theorem ker_toeplitz_fourierLp_one :
    LinearMap.ker (toeplitz (fourierLp (T := 1) ∞ 1) : HardySpace →ₗ[ℂ] HardySpace) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (by simpa using (isometry_toeplitz_fourierLp_natCast 1).injective)

/-- The backward shift `S† = T_(e_{-1})` is surjective. -/
theorem toeplitz_fourierLp_neg_one_surjective :
    Function.Surjective (toeplitz (fourierLp (T := 1) ∞ (-1))) := fun g =>
  ⟨toeplitz (fourierLp (T := 1) ∞ 1) g,
    congrArg (fun T => T g) toeplitz_fourierLp_neg_one_comp_one⟩

/-- The kernel of the backward shift `S† = T_(e_{-1})` is the one-dimensional subspace spanned by
`hardyBasis 0`. -/
theorem ker_toeplitz_fourierLp_neg_one :
    LinearMap.ker (toeplitz (fourierLp (T := 1) ∞ (-1)) : HardySpace →ₗ[ℂ] HardySpace) =
      ℂ ∙ hardyBasis 0 := by
  refine le_antisymm (fun f hf => ?_) ?_
  · rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hf
    have h := congrArg (fun T => T f) toeplitz_fourierLp_one_comp_neg_one
    rw [ContinuousLinearMap.comp_apply, hf, map_zero, sub_apply, ContinuousLinearMap.id_apply,
      eq_comm, sub_eq_zero] at h
    rw [h, Submodule.starProjection_apply]
    exact Submodule.coe_mem _
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe]
    exact toeplitz_fourierLp_neg_one_hardyBasis_zero

/-- The operator norm of the Toeplitz operator `T_a` is at most the `L∞` norm of its symbol. -/
theorem norm_toeplitz_le (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    ‖toeplitz a‖ ≤ ‖a‖ :=
  norm_compress_multiplicationOperator_le a

private theorem norm_inner_le_norm_orthogonalProjectionOnto_comp_subtypeL
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (H : Submodule ℂ (Lp E 2 (AddCircle.haarAddCircle (T := 1)))) [H.HasOrthogonalProjection]
    (M : Lp E 2 (AddCircle.haarAddCircle (T := 1)) →L[ℂ] Lp E 2 (AddCircle.haarAddCircle (T := 1)))
    {f g : Lp E 2 (AddCircle.haarAddCircle (T := 1))}
    (hf : ∀ᶠ N : ℤ in Filter.atTop,
      (fourierLp (T := 1) ∞ N • f : Lp E 2 (AddCircle.haarAddCircle (T := 1))) ∈ H)
    (hg : ∀ᶠ N : ℤ in Filter.atTop,
      (fourierLp (T := 1) ∞ N • g : Lp E 2 (AddCircle.haarAddCircle (T := 1))) ∈ H)
    (hcomm : ∀ (N : ℤ) (h : Lp E 2 (AddCircle.haarAddCircle (T := 1))),
      M (fourierLp (T := 1) ∞ N • h) = fourierLp (T := 1) ∞ N • M h) :
    ‖⟪f, M g⟫_ℂ‖ ≤ ‖H.orthogonalProjectionOnto ∘L M ∘L H.subtypeL‖ * ‖f‖ * ‖g‖ := by
  obtain ⟨N, hfN, hgN⟩ := (hf.and hg).exists
  have hu := ae_norm_fourierLp_eq_one (T := 1) ∞ N
  have hnorm (h : Lp E 2 (AddCircle.haarAddCircle (T := 1))) :
      ‖(fourierLp (T := 1) ∞ N • h : Lp E 2 (AddCircle.haarAddCircle (T := 1)))‖ = ‖h‖ := by
    rw [← Lp.multiplicationOperator_apply,
      Lp.norm_multiplicationOperator_apply_of_ae_norm_eq_one hu]
  set T := H.orthogonalProjectionOnto ∘L M ∘L H.subtypeL
  have hinner : ⟪f, M g⟫_ℂ = ⟪(⟨_, hfN⟩ : ↥H), T ⟨_, hgN⟩⟫_ℂ := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, Submodule.coe_mk,
      Submodule.subtypeL_apply, hcomm N g, ← Lp.multiplicationOperator_apply,
      ← Lp.multiplicationOperator_apply]
    exact ((LinearMap.norm_map_iff_inner_map_map
      (Lp.multiplicationOperator (E := E) (fourierLp (T := 1) ∞ N))).1
        (Lp.norm_multiplicationOperator_apply_of_ae_norm_eq_one hu) f (M g)).symm
  calc ‖⟪f, M g⟫_ℂ‖ ≤ ‖(⟨_, hfN⟩ : ↥H)‖ * (‖T‖ * ‖(⟨_, hgN⟩ : ↥H)‖) := by
        rw [hinner]; exact (norm_inner_le_norm _ _).trans (by gcongr; exact T.le_opNorm _)
    _ = ‖T‖ * ‖f‖ * ‖g‖ := by
        rw [← Submodule.norm_coe, ← Submodule.norm_coe, Submodule.coe_mk, Submodule.coe_mk,
          hnorm, hnorm]; ring

/-- If `M` on `Lp E 2 haarAddCircle` commutes with `fourierLp ∞ N • ·` and high modes eventually
shift a dense set `s` into `H`, then `‖M‖ ≤ ‖H.orthogonalProjectionOnto ∘L M ∘L H.subtypeL‖`. -/
theorem norm_le_norm_orthogonalProjectionOnto_comp_subtypeL
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (H : Submodule ℂ (Lp E 2 (AddCircle.haarAddCircle (T := 1)))) [H.HasOrthogonalProjection]
    (M : Lp E 2 (AddCircle.haarAddCircle (T := 1)) →L[ℂ] Lp E 2 (AddCircle.haarAddCircle (T := 1)))
    {s : Set (Lp E 2 (AddCircle.haarAddCircle (T := 1)))} (hs : Dense s)
    (hshift : ∀ g ∈ s, ∀ᶠ N : ℤ in Filter.atTop,
      (fourierLp (T := 1) ∞ N • g : Lp E 2 (AddCircle.haarAddCircle (T := 1))) ∈ H)
    (hcomm : ∀ (N : ℤ) (g : Lp E 2 (AddCircle.haarAddCircle (T := 1))),
      M (fourierLp (T := 1) ∞ N • g) = fourierLp (T := 1) ∞ N • M g) :
    ‖M‖ ≤ ‖H.orthogonalProjectionOnto ∘L M ∘L H.subtypeL‖ := by
  set T := H.orthogonalProjectionOnto ∘L M ∘L H.subtypeL
  have hbound : ∀ p : Lp E 2 (AddCircle.haarAddCircle (T := 1)) ×
      Lp E 2 (AddCircle.haarAddCircle (T := 1)), ‖⟪p.1, M p.2⟫_ℂ‖ ≤ ‖T‖ * ‖p.1‖ * ‖p.2‖ :=
    (hs.prod hs).induction (fun p hp ↦ norm_inner_le_norm_orthogonalProjectionOnto_comp_subtypeL H M
      (hshift p.1 hp.1) (hshift p.2 hp.2) hcomm) (isClosed_le (by fun_prop) (by fun_prop))
  refine ContinuousLinearMap.opNorm_le_of_re_inner_le (norm_nonneg T) fun x y hx hy ↦ ?_
  calc RCLike.re ⟪M x, y⟫_ℂ ≤ ‖⟪M x, y⟫_ℂ‖ := RCLike.re_le_norm _
    _ = ‖⟪y, M x⟫_ℂ‖ := norm_inner_symm _ _
    _ ≤ ‖T‖ := by simpa only [hx, hy, mul_one] using hbound (y, x)

/-- Multiplication by `a` on circle `L²` has norm at most the norm of `T_a`. -/
private theorem norm_multiplicationOperator_le_norm_toeplitz
    (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    ‖Lp.multiplicationOperator (E := ℂ) a‖ ≤ ‖toeplitz a‖ := by
  rw [toeplitz_apply]
  refine norm_le_norm_orthogonalProjectionOnto_comp_subtypeL hardySubmodule
    (Lp.multiplicationOperator a)
    (Submodule.dense_iff_topologicalClosure_eq_top.2 (fourierBasis (T := 1)).dense_span)
    (fun _ hg ↦ eventually_fourierLp_smul_mem_hardySubmodule hg) fun N g ↦ ?_
  simpa only [mul_apply_eq_comp, Lp.multiplicationOperator_apply] using
    congrArg (· g) (Lp.commute_multiplicationOperator (E := ℂ) (fourierLp (T := 1) ∞ N) a).eq.symm

/-- **Symbol norm.** The operator norm of the Toeplitz operator `T_a` is the `L∞` norm of its
symbol. -/
@[simp]
theorem norm_toeplitz (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    ‖toeplitz a‖ = ‖a‖ := by
  refine le_antisymm (norm_toeplitz_le a) ?_
  rw [← Lp.norm_multiplicationOperator (E := ℂ) a]
  exact norm_multiplicationOperator_le_norm_toeplitz a

/-- The Toeplitz symbol map `a ↦ T_a` is an isometry. -/
theorem isometry_toeplitz : Isometry toeplitz :=
  AddMonoidHomClass.isometry_of_norm toeplitz norm_toeplitz

/-- A symbol is determined by its Toeplitz operator. -/
theorem toeplitz_injective : Function.Injective toeplitz :=
  isometry_toeplitz.injective

end TauCeti
