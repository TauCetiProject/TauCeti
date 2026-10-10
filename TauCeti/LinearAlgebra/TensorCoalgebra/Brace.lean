/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.OddSquare
import Mathlib.Tactic.LinearCombination

/-!
# The brace and the Gerstenhaber bracket of suspended Hochschild cochains

Let `M` carry an internal `ℤ`-grading `G` and let `T = Tᶜ(M)` be its reduced tensor coalgebra.  A
linear map `F : T ⟶ M` of degree `p` (a suspended Hochschild cochain, when `M` is a suspension
`sA`) has a graded Taylor expansion `D F = ReducedTensorWords.gradedCoderiv G F p`, the
coderivation of twist parameter `p` with letter component `F`.  Following Getzler and Jones, the
**brace** of `F` with `g` of degree `q` is

`F{g} = F ∘ D g`,

which inserts `g` into every block of consecutive letters with the Koszul sign of moving it past
the letters before the block, and the **Gerstenhaber bracket** is its graded commutator

`[F, g] = F{g} - (-1)^(p * q) • g{F}`.

The whole structure comes from one fact about coderivations: the graded commutator
`b₁ ∘ b₂ - (-1)^(p * q) • b₂ ∘ b₁` of graded coderivations, homogeneous of the degrees `p` and `q`
of their twist parameters, is a graded coderivation of twist parameter `p + q`
(`IsGradedCoderivation.comp_sub_smul_comp`).  Since a graded coderivation is determined by its
letter component, `D [F, g]` is the graded commutator of `D F` and `D g`
(`gradedCoderiv_gerstenhaberBracket`), and the identities of a graded Lie algebra follow from those
of graded commutators of endomorphisms: the brace is a graded right pre-Lie product, and the
bracket is graded antisymmetric and satisfies the graded Jacobi identity.

For a Taylor map `F` of odd degree, `F{F}` is the letter component of the square `D F ∘ D F`,
which is an ordinary coderivation; so `D F` squares to zero exactly when `F{F} = 0`.  In degree one
this identifies square-zero bar differentials, that is `A∞` structures, with solutions of the
brace equation `m{m} = 0`.

## Main definitions

* `TauCeti.ReducedTensorWords.brace`: the brace `F{g}` of two Taylor maps.
* `TauCeti.ReducedTensorWords.gerstenhaberBracket`: their Gerstenhaber bracket `[F, g]`.

## Main results

* `TauCeti.ReducedTensorWords.IsGradedCoderivation.comp_sub_smul_comp`: the graded commutator of
  homogeneous graded coderivations is a graded coderivation.
* `TauCeti.ReducedTensorWords.gradedCoderiv_gerstenhaberBracket`: the coderivation of a
  Gerstenhaber bracket is the graded commutator of the coderivations.
* `TauCeti.ReducedTensorWords.gradedCoderiv_comp_self_eq_zero_iff`: for odd degree, the
  coderivation squares to zero exactly when the brace equation `F{F} = 0` holds.
* `TauCeti.ReducedTensorWords.brace_brace_sub_smul_brace_brace`: the graded right pre-Lie identity
  `F{g}{h} - (-1)^(q * r) • F{h}{g} = F{[g, h]}`.
* `TauCeti.ReducedTensorWords.gerstenhaberBracket_swap`: graded antisymmetry of the bracket.
* `TauCeti.ReducedTensorWords.leibniz_gerstenhaberBracket`: the graded Jacobi
  identity, in Leibniz form.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Illinois
  Journal of Mathematics 34 (1990), 256--283, Sections 1--2.
* M. Gerstenhaber, *The cohomology structure of an associative ring*, Annals of Mathematics 78
  (1963), 267--288.
-/

public section

open scoped TensorProduct

universe uR uM

namespace TauCeti

namespace ReducedTensorWords

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]
  {G : InternalGrading R M}

/-- The co-Leibniz identity of a graded coderivation, with both terms written through
`TensorProduct.map`. -/
private theorem IsGradedCoderivation.deconcatenation_comp_eq {q : ℤ}
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hb : IsGradedCoderivation G q b) :
    deconcatenation R M ∘ₗ b =
      (TensorProduct.map b LinearMap.id +
        TensorProduct.map (ReducedTensorWords.map (R := R) (G.koszulTwist q)) b) ∘ₗ
          deconcatenation R M := by
  rw [isGradedCoderivation_iff.mp hb, LinearMap.add_comp, LinearMap.rTensor_def,
    LinearMap.lTensor_comp_rTensor]

/-- Deconcatenation after a composite of two graded coderivations: the four terms of the
expansion of the product of the two co-Leibniz rules. -/
private theorem IsGradedCoderivation.deconcatenation_comp_comp_eq {p q : ℤ}
    {b₁ b₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hb₁ : IsGradedCoderivation G p b₁) (hb₂ : IsGradedCoderivation G q b₂) :
    deconcatenation R M ∘ₗ b₁ ∘ₗ b₂ =
      (TensorProduct.map (b₁ ∘ₗ b₂) LinearMap.id +
        TensorProduct.map (b₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q)) b₂ +
        TensorProduct.map (ReducedTensorWords.map (R := R) (G.koszulTwist p) ∘ₗ b₂) b₁ +
        TensorProduct.map (ReducedTensorWords.map (R := R) (G.koszulTwist (p + q)))
          (b₁ ∘ₗ b₂)) ∘ₗ deconcatenation R M := by
  rw [← LinearMap.comp_assoc, hb₁.deconcatenation_comp_eq, LinearMap.comp_assoc,
    hb₂.deconcatenation_comp_eq, ← LinearMap.comp_assoc, ← G.koszulTwist_comp,
    ReducedTensorWords.map_comp]
  congr 1
  simp only [LinearMap.add_comp, LinearMap.comp_add, ← TensorProduct.map_comp, LinearMap.id_comp,
    LinearMap.comp_id]
  abel

/-- **The graded commutator of graded coderivations is a graded coderivation.**  If `b₁` and `b₂`
are graded coderivations of twist parameters `p` and `q`, homogeneous of the degrees `p` and `q`,
then `b₁ ∘ b₂ - (-1)^(p * q) • b₂ ∘ b₁` is a graded coderivation of twist parameter `p + q`. -/
theorem IsGradedCoderivation.comp_sub_smul_comp {p q : ℤ}
    {b₁ b₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hb₁ : IsGradedCoderivation G p b₁)
    (hh₁ : LinearMap.IsHomogeneous b₁ (gradedPiece G) (gradedPiece G) p)
    (hb₂ : IsGradedCoderivation G q b₂)
    (hh₂ : LinearMap.IsHomogeneous b₂ (gradedPiece G) (gradedPiece G) q) :
    IsGradedCoderivation G (p + q) (b₁ ∘ₗ b₂ - negOnePowCast R (p * q) • (b₂ ∘ₗ b₁)) := by
  -- Cache the additive group instances of `T` and `T ⊗ T`: without them, instance synthesis fails
  -- to find the additive group structure on linear maps into `T ⊗ T`.
  let : AddCommGroup (ReducedTensorWords R M) := inferInstance
  let : AddCommGroup (ReducedTensorWords R M ⊗[R] ReducedTensorWords R M) := inferInstance
  rw [isGradedCoderivation_iff, LinearMap.comp_sub, LinearMap.comp_smul,
    hb₁.deconcatenation_comp_comp_eq hb₂, hb₂.deconcatenation_comp_comp_eq hb₁, add_comm q p,
    hh₂.map_koszulTwist_comp p, hh₁.map_koszulTwist_comp q, ← negOnePowCast_eq_intCast,
    ← negOnePowCast_eq_intCast, mul_comm q p, LinearMap.rTensor_def,
    LinearMap.lTensor_comp_rTensor]
  have hl (f g h : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) :
      TensorProduct.map (f - g) h = TensorProduct.map f h - TensorProduct.map g h := by
    rw [eq_sub_iff_add_eq, ← TensorProduct.map_add_left, sub_add_cancel]
  have hr (f g h : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) :
      TensorProduct.map h (f - g) = TensorProduct.map h f - TensorProduct.map h g := by
    rw [eq_sub_iff_add_eq, ← TensorProduct.map_add_right, sub_add_cancel]
  simp only [hl, hr, TensorProduct.map_smul_left, TensorProduct.map_smul_right,
    LinearMap.sub_comp, LinearMap.add_comp, LinearMap.smul_comp, smul_add, smul_smul,
    ← negOnePowCast_add, ← two_mul, negOnePowCast_two_mul, one_smul]
  abel

/-! ### The brace and the Gerstenhaber bracket -/

variable (G) in
/-- The **brace** `F{g}` of two Taylor maps, Gerstenhaber's composition product of suspended
Hochschild cochains: `F` after the graded Taylor expansion of `g` at twist parameter `q`.  On a
word of homogeneous letters it inserts `g` into every block of consecutive letters, with the
Koszul sign of moving `g` past the letters before the block, and applies `F` to the result. -/
noncomputable def brace (F g : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) :
    ReducedTensorWords R M →ₗ[R] M :=
  F ∘ₗ gradedCoderiv G g q

theorem brace_def (F g : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) :
    brace G F g q = F ∘ₗ gradedCoderiv G g q := (rfl)

/-- The brace of a Taylor map of degree `p` with one of degree `q` has degree `p + q`. -/
theorem isHomogeneous_brace {F g : ReducedTensorWords R M →ₗ[R] M} {p q : ℤ}
    (hF : LinearMap.IsHomogeneous F (gradedPiece G) G.piece p)
    (hg : LinearMap.IsHomogeneous g (gradedPiece G) G.piece q) :
    LinearMap.IsHomogeneous (brace G F g q) (gradedPiece G) G.piece (p + q) := by
  rw [add_comm]
  exact hF.comp (isHomogeneous_gradedCoderiv G g q q hg)

/-- The brace is the letter component of the composite of the two graded coderivations. -/
theorem letter_comp_gradedCoderiv_comp_gradedCoderiv (F g : ReducedTensorWords R M →ₗ[R] M)
    (p q : ℤ) :
    letter R M ∘ₗ gradedCoderiv G F p ∘ₗ gradedCoderiv G g q = brace G F g q := by
  rw [← LinearMap.comp_assoc, letter_comp_gradedCoderiv, brace_def]

/-- The brace is additive in its first argument. -/
theorem brace_add_left (F₁ F₂ g : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) :
    brace G (F₁ + F₂) g q = brace G F₁ g q + brace G F₂ g q :=
  LinearMap.add_comp _ _ _

/-- The brace is `R`-linear in its first argument. -/
theorem brace_smul_left (c : R) (F g : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) :
    brace G (c • F) g q = c • brace G F g q :=
  LinearMap.smul_comp _ _ _

/-- The brace of the zero map with any Taylor map vanishes. -/
@[simp]
theorem brace_zero_left (g : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) :
    brace G 0 g q = 0 :=
  LinearMap.zero_comp _

/-- The brace is additive in its second argument, since the graded Taylor expansion is. -/
theorem brace_add_right (F g₁ g₂ : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) :
    brace G F (g₁ + g₂) q = brace G F g₁ q + brace G F g₂ q := by
  have h := congrArg Subtype.val (map_add (gradedCoderivEquivTaylor G q).symm g₁ g₂)
  simp only [gradedCoderivEquivTaylor_symm_apply, Submodule.coe_add] at h
  rw [brace_def, h, LinearMap.comp_add, brace_def, brace_def]

/-- The brace is `R`-linear in its second argument, since the graded Taylor expansion is. -/
theorem brace_smul_right (c : R) (F g : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) :
    brace G F (c • g) q = c • brace G F g q := by
  have h := congrArg Subtype.val (map_smul (gradedCoderivEquivTaylor G q).symm c g)
  simp only [gradedCoderivEquivTaylor_symm_apply, Submodule.coe_smul] at h
  rw [brace_def, h, LinearMap.comp_smul, brace_def]

/-- The brace of a Taylor map with the zero map vanishes. -/
@[simp]
theorem brace_zero_right (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) :
    brace G F 0 q = 0 := by
  simpa using brace_smul_right (G := G) (0 : R) F 0 q

variable (G) in
/-- The **Gerstenhaber bracket** `[F, g] = F{g} - (-1)^(p * q) g{F}` of a Taylor map `F` of
degree `p` with a Taylor map `g` of degree `q`, the graded commutator of the brace. -/
noncomputable def gerstenhaberBracket (p q : ℤ) (F g : ReducedTensorWords R M →ₗ[R] M) :
    ReducedTensorWords R M →ₗ[R] M :=
  brace G F g q - negOnePowCast R (p * q) • brace G g F p

theorem gerstenhaberBracket_def (p q : ℤ) (F g : ReducedTensorWords R M →ₗ[R] M) :
    gerstenhaberBracket G p q F g = brace G F g q - negOnePowCast R (p * q) • brace G g F p :=
  (rfl)

/-- The Gerstenhaber bracket is additive in its first argument. -/
theorem gerstenhaberBracket_add_left (p q : ℤ) (F₁ F₂ g : ReducedTensorWords R M →ₗ[R] M) :
    gerstenhaberBracket G p q (F₁ + F₂) g =
      gerstenhaberBracket G p q F₁ g + gerstenhaberBracket G p q F₂ g := by
  simp only [gerstenhaberBracket_def, brace_add_left, brace_add_right, smul_add]
  abel

/-- The Gerstenhaber bracket is additive in its second argument. -/
theorem gerstenhaberBracket_add_right (p q : ℤ) (F g₁ g₂ : ReducedTensorWords R M →ₗ[R] M) :
    gerstenhaberBracket G p q F (g₁ + g₂) =
      gerstenhaberBracket G p q F g₁ + gerstenhaberBracket G p q F g₂ := by
  simp only [gerstenhaberBracket_def, brace_add_left, brace_add_right, smul_add]
  abel

/-- The Gerstenhaber bracket is `R`-linear in its first argument. -/
theorem gerstenhaberBracket_smul_left (p q : ℤ) (c : R)
    (F g : ReducedTensorWords R M →ₗ[R] M) :
    gerstenhaberBracket G p q (c • F) g = c • gerstenhaberBracket G p q F g := by
  rw [gerstenhaberBracket_def, gerstenhaberBracket_def, brace_smul_left, brace_smul_right,
    smul_sub, smul_comm c]

/-- The Gerstenhaber bracket is `R`-linear in its second argument. -/
theorem gerstenhaberBracket_smul_right (p q : ℤ) (c : R)
    (F g : ReducedTensorWords R M →ₗ[R] M) :
    gerstenhaberBracket G p q F (c • g) = c • gerstenhaberBracket G p q F g := by
  rw [gerstenhaberBracket_def, gerstenhaberBracket_def, brace_smul_left, brace_smul_right,
    smul_sub, smul_comm c]

/-- The Gerstenhaber bracket of the zero map with any Taylor map vanishes. -/
@[simp]
theorem gerstenhaberBracket_zero_left (p q : ℤ) (g : ReducedTensorWords R M →ₗ[R] M) :
    gerstenhaberBracket G p q 0 g = 0 := by
  simp [gerstenhaberBracket_def]

/-- The Gerstenhaber bracket of a Taylor map with the zero map vanishes. -/
@[simp]
theorem gerstenhaberBracket_zero_right (p q : ℤ) (F : ReducedTensorWords R M →ₗ[R] M) :
    gerstenhaberBracket G p q F 0 = 0 := by
  simp [gerstenhaberBracket_def]

/-- The Gerstenhaber bracket of Taylor maps of degrees `p` and `q` has degree `p + q`. -/
theorem isHomogeneous_gerstenhaberBracket {F g : ReducedTensorWords R M →ₗ[R] M} {p q : ℤ}
    (hF : LinearMap.IsHomogeneous F (gradedPiece G) G.piece p)
    (hg : LinearMap.IsHomogeneous g (gradedPiece G) G.piece q) :
    LinearMap.IsHomogeneous (gerstenhaberBracket G p q F g) (gradedPiece G)
      G.piece (p + q) := by
  refine (isHomogeneous_brace hF hg).sub ?_
  rw [add_comm]
  exact (isHomogeneous_brace hg hF).smul _

/-- **The graded coderivation of a Gerstenhaber bracket is the graded commutator of the graded
coderivations.**  For Taylor maps `F` of degree `p` and `g` of degree `q`,
`D [F, g] = D F ∘ D g - (-1)^(p * q) • D g ∘ D F`, where `D` is the graded Taylor expansion at
twist parameter equal to the degree. -/
theorem gradedCoderiv_gerstenhaberBracket {F g : ReducedTensorWords R M →ₗ[R] M} {p q : ℤ}
    (hF : LinearMap.IsHomogeneous F (gradedPiece G) G.piece p)
    (hg : LinearMap.IsHomogeneous g (gradedPiece G) G.piece q) :
    gradedCoderiv G (gerstenhaberBracket G p q F g) (p + q) =
      gradedCoderiv G F p ∘ₗ gradedCoderiv G g q -
        negOnePowCast R (p * q) • (gradedCoderiv G g q ∘ₗ gradedCoderiv G F p) := by
  refine IsGradedCoderivation.eq_of_letter_comp_eq (isGradedCoderivation_gradedCoderiv G _ _)
    ((isGradedCoderivation_gradedCoderiv G F p).comp_sub_smul_comp
      (isHomogeneous_gradedCoderiv G F p p hF) (isGradedCoderivation_gradedCoderiv G g q)
      (isHomogeneous_gradedCoderiv G g q q hg)) ?_
  rw [letter_comp_gradedCoderiv, LinearMap.comp_sub, LinearMap.comp_smul,
    letter_comp_gradedCoderiv_comp_gradedCoderiv, letter_comp_gradedCoderiv_comp_gradedCoderiv,
    gerstenhaberBracket_def]

/-- **The square-zero equation is the brace equation.**  For a Taylor map `F` of odd degree `q`,
the graded Taylor expansion of `F` squares to zero exactly when `F{F} = 0`. -/
theorem gradedCoderiv_comp_self_eq_zero_iff {F : ReducedTensorWords R M →ₗ[R] M} {q : ℤ}
    (hF : LinearMap.IsHomogeneous F (gradedPiece G) G.piece q) (hq : Odd q) :
    gradedCoderiv G F q ∘ₗ gradedCoderiv G F q = 0 ↔ brace G F F q = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← letter_comp_gradedCoderiv_comp_gradedCoderiv, h, LinearMap.comp_zero]
  · -- The square of an odd graded coderivation is an ordinary coderivation, and its letter
    -- component is the brace.
    have hsq := (isGradedCoderivation_gradedCoderiv G F q).isCoderivation_comp_self_of_isHomogeneous
      (isHomogeneous_gradedCoderiv G F q q hF) (by rw [Int.negOnePow_odd _ (hq.mul hq)]; simp)
    refine IsGradedCoderivation.eq_of_letter_comp_eq (hsq.isGradedCoderivation G)
      ((mem_gradedCoderivations G).1 (gradedCoderivations G 0).zero_mem) ?_
    rw [letter_comp_gradedCoderiv_comp_gradedCoderiv, h, LinearMap.comp_zero]

/-- The Gerstenhaber bracket is graded antisymmetric:
`[g, F] = -(-1)^(p * q) • [F, g]` for `F` of degree `p` and `g` of degree `q`. -/
theorem gerstenhaberBracket_swap (p q : ℤ) (F g : ReducedTensorWords R M →ₗ[R] M) :
    gerstenhaberBracket G q p g F = -negOnePowCast R (p * q) • gerstenhaberBracket G p q F g := by
  rw [gerstenhaberBracket_def, gerstenhaberBracket_def, mul_comm q p, smul_sub, smul_smul, neg_mul,
    negOnePowCast_mul_self]
  module

/-- **The brace is a right graded pre-Lie product.**  The graded commutator of the two ways of
bracing `F` successively with `g` of degree `q` and `h` of degree `r` is the brace of `F` with
their Gerstenhaber bracket:
`F{g}{h} - (-1)^(q * r) • F{h}{g} = F{[g, h]}`. -/
theorem brace_brace_sub_smul_brace_brace (F : ReducedTensorWords R M →ₗ[R] M)
    {g h : ReducedTensorWords R M →ₗ[R] M} {q r : ℤ}
    (hg : LinearMap.IsHomogeneous g (gradedPiece G) G.piece q)
    (hh : LinearMap.IsHomogeneous h (gradedPiece G) G.piece r) :
    brace G (brace G F g q) h r - negOnePowCast R (q * r) • brace G (brace G F h r) g q =
      brace G F (gerstenhaberBracket G q r g h) (q + r) := by
  rw [brace_def F (gerstenhaberBracket G q r g h), gradedCoderiv_gerstenhaberBracket hg hh,
    LinearMap.comp_sub, LinearMap.comp_smul]
  simp only [brace_def, LinearMap.comp_assoc]

/-- **The graded Jacobi identity** for the Gerstenhaber bracket, in Leibniz form: bracketing with
`F` of degree `p` is a graded derivation of the bracket of `g` of degree `q` and `h` of
degree `r`,
`[F, [g, h]] = [[F, g], h] + (-1)^(p * q) • [g, [F, h]]`. -/
theorem leibniz_gerstenhaberBracket {F g h : ReducedTensorWords R M →ₗ[R] M}
    {p q r : ℤ} (hF : LinearMap.IsHomogeneous F (gradedPiece G) G.piece p)
    (hg : LinearMap.IsHomogeneous g (gradedPiece G) G.piece q)
    (hh : LinearMap.IsHomogeneous h (gradedPiece G) G.piece r) :
    gerstenhaberBracket G p (q + r) F (gerstenhaberBracket G q r g h) =
      gerstenhaberBracket G (p + q) r (gerstenhaberBracket G p q F g) h +
        negOnePowCast R (p * q) •
          gerstenhaberBracket G q (p + r) g (gerstenhaberBracket G p r F h) := by
  -- Cache the additive group instance of the endomorphisms of words, which `linear_combination`
  -- otherwise fails to synthesize.
  let : AddCommGroup (ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) := inferInstance
  -- Each bracket is the letter component of the corresponding commutator of coderivations.
  have key (x : ReducedTensorWords R M →ₗ[R] M) (n : ℤ) :
      x = letter R M ∘ₗ gradedCoderiv G x n :=
    (letter_comp_gradedCoderiv G x n).symm
  rw [key (gerstenhaberBracket G p (q + r) F _) (p + (q + r)),
    key (gerstenhaberBracket G (p + q) r _ h) (p + q + r),
    key (gerstenhaberBracket G q (p + r) g _) (q + (p + r)),
    gradedCoderiv_gerstenhaberBracket hF (isHomogeneous_gerstenhaberBracket hg hh),
    gradedCoderiv_gerstenhaberBracket (isHomogeneous_gerstenhaberBracket hF hg) hh,
    gradedCoderiv_gerstenhaberBracket hg (isHomogeneous_gerstenhaberBracket hF hh),
    gradedCoderiv_gerstenhaberBracket hF hg, gradedCoderiv_gerstenhaberBracket hg hh,
    gradedCoderiv_gerstenhaberBracket hF hh]
  rw [← LinearMap.comp_smul (letter R M), ← LinearMap.comp_add]
  congr 1
  set a := gradedCoderiv G F p
  set b := gradedCoderiv G g q
  set c := gradedCoderiv G h r
  simp only [LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_smul, LinearMap.smul_comp,
    LinearMap.comp_assoc, smul_sub, smul_smul, mul_add, add_mul, negOnePowCast_add]
  rw [mul_comm q p]
  -- What remains is the graded Jacobi identity for commutators of endomorphisms; the two sides
  -- differ by `(-1)^(p * q) * (-1)^(p * q) - 1 = 0` times two triple composites.
  linear_combination (norm := module)
    negOnePowCast_mul_self (R := R) (p * q) • (negOnePowCast R (q * r) • (a ∘ₗ c ∘ₗ b) -
      (negOnePowCast R (p * r) * negOnePowCast R (q * r)) • (c ∘ₗ a ∘ₗ b))

end ReducedTensorWords

end TauCeti
