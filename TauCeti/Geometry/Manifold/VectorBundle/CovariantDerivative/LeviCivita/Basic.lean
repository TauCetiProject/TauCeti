/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearTensor

/-!
# The Koszul formula for Levi-Civita connections

A covariant derivative `∇` on the tangent bundle of a Riemannian manifold is a *Levi-Civita
connection*, or *Riemannian connection*, if it is torsion free and compatible with the metric.
Mathlib states this as `CovariantDerivative.IsLeviCivitaConnection`, constructs such a connection,
`CovariantDerivative.leviCivitaConnection`, and proves that it is unique on differentiable sections,
`CovariantDerivative.IsLeviCivitaConnection.uniqueness`. This file develops the right-hand side of
the Koszul formula

`2 ⟪∇_X Y, Z⟫ = X ⟪Y, Z⟫ + Y ⟪Z, X⟫ - Z ⟪X, Y⟫ + ⟪[X, Y], Z⟫ - ⟪[X, Z], Y⟫ - ⟪[Y, Z], X⟫`

as an object in its own right. It involves the metric only, so it is packaged as a standalone
function `TauCeti.Manifold.koszul`. The Koszul formula in that form is
`IsLeviCivitaConnection.two_inner_eq_koszul`, and for Mathlib's connection
`two_inner_leviCivitaConnection_eq_koszul`; this is the shape in which
`TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity` reads the
connection in a local frame. The converse direction `isLeviCivitaConnection_iff` shows nothing is
lost in the passage to `koszul`: a connection satisfying the Koszul formula is automatically torsion
free and metric.

Two covariant derivatives can only be compared through sections that are differentiable at the
point under consideration, because `CovariantDerivative` puts no constraint whatsoever on the
value of `∇ σ` for a nowhere differentiable section `σ`. Mathlib's uniqueness is accordingly
stated for `Y` differentiable at `x`; `IsLeviCivitaConnection.difference_eq_zero` repackages it as
the vanishing of the endomorphism-valued one-form `CovariantDerivative.difference ∇ ∇'`.

## Main definitions and results

* `TauCeti.Manifold.koszul` and `TauCeti.Manifold.koszul_apply`: the right-hand side of the Koszul
  formula, a function of the Riemannian metric alone, and its defining formula.
* `CovariantDerivative.IsLeviCivitaConnection.two_inner_eq_koszul`: the Koszul formula, and
  `CovariantDerivative.two_inner_leviCivitaConnection_eq_koszul` for Mathlib's connection.
* `CovariantDerivative.isLeviCivitaConnection_iff`: the Koszul formula characterises the
  Levi-Civita connections.
* `CovariantDerivative.IsLeviCivitaConnection.difference_eq_zero`: uniqueness of the Levi-Civita
  connection, as the vanishing of the difference of two of them.
* `TauCeti.Manifold.koszul_sub_koszul_swap_first_two` and
  `TauCeti.Manifold.koszul_add_koszul_swap_last_two`: the two symmetries of the Koszul expression
  from which the converse direction is read off.
* `TauCeti.Manifold.tensorialAt_koszul_third` and `TauCeti.Manifold.tensorialAt_koszul_first`: the
  Koszul expression is tensorial in its last argument and in its first.
* `TauCeti.Manifold.koszul_add_second` and `TauCeti.Manifold.koszul_smul_second`: additivity and
  the Leibniz rule in the middle argument, the slot which the connection differentiates.
* `TauCeti.Manifold.koszulBilinear_mpullback`: the Koszul expression of a pairing is natural under
  maps with invertible differentials pulling one pairing back to the other.
* `TauCeti.Manifold.koszulBilinear_sub_two_mul_apply_eq_derivBilinearTensor`: along a torsion-free
  connection, the Koszul expression of a symmetric pairing `b` differs from `2 b(∇_X Y, Z)` by
  `(∇_X b)(Y, Z) + (∇_Y b)(X, Z) - (∇_Z b)(X, Y)`.

## References

* [mathlib4#36845](https://github.com/leanprover-community/mathlib4/pull/36845): the first-slot
  tensoriality and second-slot Leibniz identities follow its design.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 2, Thm. 3.6.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2018, Thm. 5.10.
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.K, Theorem 1.174: the first
  variation of the Levi-Civita connection, obtained by differentiating the Koszul formula.
-/

public section

open Bundle FiberBundle NormedSpace VectorField
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-! ### Nondegeneracy of the metric along differentiable sections -/

section Nondegenerate

variable {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)] [FiberBundle F V]

variable {V' : M → Type*} [TopologicalSpace (TotalSpace F' V')]
  [∀ x, AddCommGroup (V' x)] [∀ x, Module ℝ (V' x)] [∀ x, TopologicalSpace (V' x)]
  [FiberBundle F' V']

variable (F F') in
/-- Two continuous linear maps between fibres are equal if their values on differentiable sections
have the same inner products against every differentiable section of the target bundle. -/
theorem continuousLinearMap_ext_of_forall_inner_section_eq {x : M} {A B : V' x →L[ℝ] V x}
    (h : ∀ σ : ∀ y : M, V' y, MDiffAt (T% σ) x → ∀ τ : ∀ y : M, V y,
      MDiffAt (T% τ) x → inner ℝ (A (σ x)) (τ x) = inner ℝ (B (σ x)) (τ x)) : A = B := by
  refine VectorBundle.injective_eval_mdifferentiableAt_sec I F' V' (V x) x ?_
  ext σ hσ
  refine injective_inner_mdifferentiableAt_section I F V x ?_
  ext τ hτ
  exact h σ hσ τ hτ

end Nondegenerate

/-! ### The Koszul expression -/

namespace Manifold

variable (I) in
/-- The right-hand side of the Koszul formula for a pointwise bilinear pairing `b`. -/
def koszulBilinear
    (b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X Y Z : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  mvfderiv I (fun y ↦ b y (Y y) (Z y)) x (X x)
    + mvfderiv I (fun y ↦ b y (Z y) (X y)) x (Y x)
    - mvfderiv I (fun y ↦ b y (X y) (Y y)) x (Z x)
    + b x (mlieBracket I X Y x) (Z x)
    - b x (mlieBracket I X Z x) (Y x)
    - b x (mlieBracket I Y Z x) (X x)

/-- The defining formula for the Koszul expression of a pointwise bilinear pairing. -/
theorem koszulBilinear_apply
    (b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    koszulBilinear I b X Y Z x =
      mvfderiv I (fun y ↦ b y (Y y) (Z y)) x (X x)
        + mvfderiv I (fun y ↦ b y (Z y) (X y)) x (Y x)
        - mvfderiv I (fun y ↦ b y (X y) (Y y)) x (Z x)
        + b x (mlieBracket I X Y x) (Z x)
        - b x (mlieBracket I X Z x) (Y x)
        - b x (mlieBracket I Y Z x) (X x) := (rfl)

variable
  {b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
  {X Y Z : Π x : M, TangentSpace I x} {x : M}

/-- Antisymmetrizing the bilinear Koszul expression in its first two arguments returns twice the
pairing of the Lie bracket with the third argument. -/
theorem koszulBilinear_sub_koszulBilinear_swap_first_two
    (hb : ∀ x v w, b x v w = b x w v) :
    koszulBilinear I b X Y Z x - koszulBilinear I b Y X Z x =
      2 * b x (mlieBracket I X Y x) (Z x) := by
  have hsection (U V : Π x : M, TangentSpace I x) :
      (fun y ↦ b y (U y) (V y)) = fun y ↦ b y (V y) (U y) :=
    funext fun y ↦ hb y _ _
  rw [koszulBilinear, koszulBilinear, hsection Z Y, hsection Y X, hsection X Z,
    mlieBracket_swap_apply (V := Y) (W := X)]
  simp only [map_neg, neg_apply]
  ring

/-- Symmetrizing the bilinear Koszul expression in its last two arguments returns twice the
derivative of their pairing along the first argument. -/
theorem koszulBilinear_add_koszulBilinear_swap_last_two
    (hb : ∀ x v w, b x v w = b x w v) :
    koszulBilinear I b Z X Y x + koszulBilinear I b Z Y X x =
      2 * mvfderiv I (fun y ↦ b y (X y) (Y y)) x (Z x) := by
  have hsection (U V : Π x : M, TangentSpace I x) :
      (fun y ↦ b y (U y) (V y)) = fun y ↦ b y (V y) (U y) :=
    funext fun y ↦ hb y _ _
  rw [koszulBilinear, koszulBilinear, hsection Y X, hsection Y Z, hsection X Z,
    mlieBracket_swap_apply (V := Y) (W := X)]
  simp only [map_neg, neg_apply]
  ring

/-- The Koszul identity for a symmetric pointwise bilinear pairing implies its metric product
rule along differentiable vector fields. -/
theorem metricProductRule_of_two_apply_eq_koszulBilinear
    [IsManifold I 1 M]
    {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
    (hb : ∀ x v w, b x v w = b x w v)
    (h : ∀ ⦃x : M⦄ ⦃X Y Z : Π x : M, TangentSpace I x⦄,
      MDiffAt (T% X) x → MDiffAt (T% Y) x → MDiffAt (T% Z) x →
      2 * b x (cov Y x (X x)) (Z x) = koszulBilinear I b X Y Z x) :
    ∀ ⦃x : M⦄ ⦃X Y Z : Π x : M, TangentSpace I x⦄,
      MDiffAt (T% X) x → MDiffAt (T% Y) x → MDiffAt (T% Z) x →
      mvfderiv I (fun y ↦ b y (Y y) (Z y)) x (X x) =
        b x (cov Y x (X x)) (Z x) + b x (Y x) (cov Z x (X x)) := by
  intro x X Y Z hX hY hZ
  have hXY := h hX hY hZ
  have hYX := h hX hZ hY
  have key := koszulBilinear_add_koszulBilinear_swap_last_two hb
    (X := Y) (Y := Z) (Z := X) (x := x)
  rw [hb x (Y x) (cov Z x (X x))]
  linarith

/-- The Koszul identity for a symmetric nondegenerate pointwise bilinear pairing implies that the
connection is torsion free. -/
theorem torsion_eq_zero_of_two_apply_eq_koszulBilinear [FiniteDimensional ℝ E]
    [IsManifold I 2 M] {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
    (hb : ∀ x v w, b x v w = b x w v)
    (hinjective : ∀ x, Function.Injective fun u : TangentSpace I x ↦
      fun (Z : Π x : M, TangentSpace I x) (_ : MDiffAt (T% Z) x) ↦ b x u (Z x))
    (h : ∀ ⦃x : M⦄ ⦃X Y Z : Π x : M, TangentSpace I x⦄,
      MDiffAt (T% X) x → MDiffAt (T% Y) x → MDiffAt (T% Z) x →
      2 * b x (cov Y x (X x)) (Z x) = koszulBilinear I b X Y Z x) :
    cov.torsion = 0 := by
  refine cov.torsion_eq_zero_iff.mpr fun {X Y x} hX hY ↦ ?_
  refine hinjective x ?_
  ext Z hZ
  have hXY := h hX hY hZ
  have hYX := h hY hX hZ
  have key := koszulBilinear_sub_koszulBilinear_swap_first_two hb
    (X := X) (Y := Y) (Z := Z) (x := x)
  simp only [map_sub, sub_apply]
  linarith

section BilinearTensorial

variable [IsManifold I 2 M] [CompleteSpace E]
  {X' Y' : Π x : M, TangentSpace I x} {f : M → ℝ}
  (hdiff : ∀ {Y Z : Π x : M, TangentSpace I x},
    MDiffAt (T% Y) x → MDiffAt (T% Z) x → MDiffAt (fun y ↦ b y (Y y) (Z y)) x)

include hdiff

/-- The Koszul expression is additive in the differentiated vector field. -/
theorem koszulBilinear_add_second (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hY' : MDiffAt (T% Y') x) (hZ : MDiffAt (T% Z) x) :
    koszulBilinear I b X (Y + Y') Z x =
      koszulBilinear I b X Y Z x + koszulBilinear I b X Y' Z x := by
  simp only [koszulBilinear_apply, Pi.add_apply, map_add, add_apply,
    mvfderiv_fun_add (hdiff hY hZ) (hdiff hY' hZ),
    mvfderiv_fun_add (hdiff hX hY) (hdiff hX hY'),
    mlieBracket_add_right hY hY', mlieBracket_add_left hY hY']
  ring

/-- The Koszul expression obeys the connection Leibniz rule in its second argument. -/
theorem koszulBilinear_smul_second
    (hb : ∀ x v w, b x v w = b x w v) (hf : MDiffAt f x) (hX : MDiffAt (T% X) x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszulBilinear I b X (f • Y) Z x =
      f x * koszulBilinear I b X Y Z x + 2 * d% f x (X x) * b x (Y x) (Z x) := by
  simp only [koszulBilinear_apply, Pi.smul_apply', map_smul, smul_apply,
    smul_eq_mul, mvfderiv_fun_mul hf (hdiff hY hZ),
    mvfderiv_fun_mul hf (hdiff hX hY),
    mlieBracket_smul_right hf hY, mlieBracket_smul_left (W := Z) hf hY]
  simp only [map_add, map_smul, map_neg, add_apply,
    smul_apply, smul_eq_mul, neg_smul, neg_apply]
  rw [hb x (Y x) (X x)]
  ring

/-- The Koszul expression is additive in its first argument. -/
theorem koszulBilinear_add_first
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszulBilinear I b (X + X') Y Z x =
      koszulBilinear I b X Y Z x + koszulBilinear I b X' Y Z x := by
  simp only [koszulBilinear_apply, Pi.add_apply, map_add, add_apply,
    mvfderiv_fun_add (hdiff hZ hX) (hdiff hZ hX'),
    mvfderiv_fun_add (hdiff hX hY) (hdiff hX' hY),
    mlieBracket_add_left hX hX']
  ring

/-- The Koszul expression is tensorial in its first argument: replacing `X` by `f • X` multiplies
it by `f x`. -/
theorem koszulBilinear_smul_first
    (hb : ∀ x v w, b x v w = b x w v) (hf : MDiffAt f x) (hX : MDiffAt (T% X) x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszulBilinear I b (f • X) Y Z x = f x * koszulBilinear I b X Y Z x := by
  have hsmul := koszulBilinear_smul_second hdiff hb (I := I) (X := Y) (Y := X) (Z := Z) hf hY hX hZ
  have hswap := koszulBilinear_sub_koszulBilinear_swap_first_two hb
    (I := I) (X := f • X) (Y := Y) (Z := Z) (x := x)
  have hswapX := koszulBilinear_sub_koszulBilinear_swap_first_two hb
    (I := I) (X := X) (Y := Y) (Z := Z) (x := x)
  rw [mlieBracket_smul_left hf hX] at hswap
  simp only [map_add, add_apply, neg_smul, map_neg, neg_apply, map_smul, smul_apply,
    smul_eq_mul] at hswap
  linear_combination hswap + hsmul - f x * hswapX

/-- The Koszul expression is tensorial in its first argument. Together with
`TauCeti.Manifold.tensorialAt_koszulBilinear_third`, in finite dimension this yields a continuous
bilinear form on the tangent fibre via `TensorialAt.mkHom₂`, as used to build the Levi-Civita
connection. -/
theorem tensorialAt_koszulBilinear_first
    (hb : ∀ x v w, b x v w = b x w v) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    TensorialAt I E (fun X : Π y : M, TangentSpace I y ↦ koszulBilinear I b X Y Z x) x where
  smul hf hX := by simpa using koszulBilinear_smul_first hdiff hb hf hX hY hZ
  add hX hX' := koszulBilinear_add_first hdiff hX hX' hY hZ

/-- The Koszul expression is tensorial in its third argument. -/
theorem tensorialAt_koszulBilinear_third
    (hb : ∀ x v w, b x v w = b x w v) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    TensorialAt I E (fun Z : Π y : M, TangentSpace I y ↦ koszulBilinear I b X Y Z x) x where
  smul {f Z} hf hZ := by
    simp only [koszulBilinear_apply, Pi.smul_apply', map_smul, smul_apply,
      smul_eq_mul, mvfderiv_fun_mul hf (hdiff hY hZ),
      mvfderiv_fun_mul hf (hdiff hZ hX),
      mlieBracket_smul_right hf hZ]
    simp only [map_add, map_smul, add_apply,
      smul_apply, smul_eq_mul]
    rw [hb x (Z x) (Y x)]
    ring
  add {Z Z'} hZ hZ' := by
    simp only [koszulBilinear_apply, Pi.add_apply, map_add, add_apply,
      mvfderiv_fun_add (hdiff hY hZ) (hdiff hY hZ'),
      mvfderiv_fun_add (hdiff hZ hX) (hdiff hZ' hX),
      mlieBracket_add_right hZ hZ']
    ring

end BilinearTensorial

section DerivBilinearTensor

variable [FiniteDimensional ℝ E] [IsManifold I 2 M]

/-- **The Koszul expression of a symmetric field of bilinear forms along a torsion-free
connection.** For a torsion-free covariant derivative `∇` on the tangent bundle and a symmetric
field of bilinear forms `b` which pairs differentiable vector fields to differentiable functions,

`K_b(X, Y, Z) - 2 b(∇_X Y, Z) = (∇_X b)(Y, Z) + (∇_Y b)(X, Z) - (∇_Z b)(X, Y)`,

where `K_b` is the Koszul expression of `b` and `∇b` is
`CovariantDerivative.derivBilinearTensor`. When `∇` is compatible with `b`, the right-hand side
vanishes and this is the Koszul formula. For a family of metrics `gₜ` with Levi-Civita connections
`∇ᵗ` and `h = ∂ₜ gₜ`, differentiating the Koszul formula `2 gₜ(∇ᵗ_X Y, Z) = K_{gₜ}(X, Y, Z)` in
`t` gives `2 g((∂ₜ∇)_X Y, Z) = K_h(X, Y, Z) - 2 h(∇_X Y, Z)`; this identity, applied to `b = h`,
rewrites the right-hand side as the covariant derivative of `h`. -/
theorem koszulBilinear_sub_two_mul_apply_eq_derivBilinearTensor
    {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)} (htorsion : cov.torsion = 0)
    (hsymm : ∀ x v w, b x v w = b x w v)
    (hb : ∀ ⦃V W : Π x : M, TangentSpace I x⦄, MDiffAt (T% V) x → MDiffAt (T% W) x →
      MDiffAt (fun y ↦ b y (V y) (W y)) x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszulBilinear I b X Y Z x - 2 * b x (cov Y x (X x)) (Z x) =
      cov.derivBilinearTensor b x (Y x) (Z x) (X x) +
        cov.derivBilinearTensor b x (X x) (Z x) (Y x) -
        cov.derivBilinearTensor b x (X x) (Y x) (Z x) := by
  have hpair (U W : Π x : M, TangentSpace I x) :
      (fun y ↦ b y (U y) (W y)) = fun y ↦ b y (W y) (U y) :=
    funext fun y ↦ hsymm y _ _
  have ht {U W : Π x : M, TangentSpace I x} (hU : MDiffAt (T% U) x) (hW : MDiffAt (T% W) x) :=
    (cov.torsion_eq_zero_iff.mp htorsion) hU hW
  rw [koszulBilinear_apply, cov.derivBilinearTensor_apply hb hY hZ,
    cov.derivBilinearTensor_apply hb hX hZ, cov.derivBilinearTensor_apply hb hX hY, hpair Z X,
    ← ht hX hY, ← ht hX hZ, ← ht hY hZ]
  simp only [map_sub, sub_apply]
  rw [hsymm x (Y x) (cov Z x (X x)), hsymm x (X x) (cov Z x (Y x)),
    hsymm x (X x) (cov Y x (Z x))]
  ring

end DerivBilinearTensor

section Naturality

variable [CompleteSpace E] [IsManifold I 2 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 2 N]
  {b' : (y : N) → TangentSpace J y →L[ℝ] TangentSpace J y →L[ℝ] ℝ} {f : M → N}

/-- **Naturality of the bilinear Koszul expression.** Let `f : M → N` be a map with invertible
differentials, `C²` at `x`, which pulls the pairing `b'` on `N` back to the pairing `b` on `M`,
`b_y(v, w) = b'_{f y}(df_y v, df_y w)`. Suppose that `b'` pairs vector fields differentiable at
`f x` to a function differentiable at `f x`. Then the Koszul expression of `b` on the pullbacks of
three vector fields differentiable at `f x` is the Koszul expression of `b'` on the fields
themselves, evaluated at `f x`. -/
theorem koszulBilinear_mpullback (hf : ContMDiffAt I J 2 f x)
    (hinv : ∀ y, (mfderiv I J f y).IsInvertible)
    (hb : ∀ y (v w : TangentSpace I y),
      b y v w = b' (f y) (mfderiv I J f y v) (mfderiv I J f y w))
    (hb' : ∀ ⦃V W : Π y : N, TangentSpace J y⦄, MDiffAt (T% V) (f x) → MDiffAt (T% W) (f x) →
      MDiffAt (fun y ↦ b' y (V y) (W y)) (f x))
    {X Y Z : Π y : N, TangentSpace J y} (hX : MDiffAt (T% X) (f x))
    (hY : MDiffAt (T% Y) (f x)) (hZ : MDiffAt (T% Z) (f x)) :
    koszulBilinear I b (mpullback I J f X) (mpullback I J f Y) (mpullback I J f Z) x =
      koszulBilinear J b' X Y Z (f x) := by
  -- Pairing two pulled-back fields with `b` is pairing the fields with `b'`, composed with `f`.
  have hpair (V W : Π y : N, TangentSpace J y) :
      (fun y ↦ b y (mpullback I J f V y) (mpullback I J f W y)) =
        (fun y ↦ b' y (V y) (W y)) ∘ f := by
    funext y
    simp only [hb, mpullback_apply, (hinv y).self_apply_inverse, Function.comp_apply]
  -- Directional derivatives of the pairings: the chain rule through `f`.
  have hd {V W : Π y : N, TangentSpace J y} (U : Π y : N, TangentSpace J y)
      (hV : MDiffAt (T% V) (f x)) (hW : MDiffAt (T% W) (f x)) :
      mvfderiv I (fun y ↦ b y (mpullback I J f V y) (mpullback I J f W y)) x
          (mpullback I J f U x) =
        mvfderiv J (fun y ↦ b' y (V y) (W y)) (f x) (U (f x)) := by
    rw [hpair, mvfderiv_comp_apply x (hb' hV hW) (hf.mdifferentiableAt (by simp)),
      mpullback_apply, (hinv x).self_apply_inverse]
  -- Lie brackets: Mathlib's naturality of the Lie bracket under pullback.
  have hbr {V W : Π y : N, TangentSpace J y} (hV : MDiffAt (T% V) (f x))
      (hW : MDiffAt (T% W) (f x)) :
      mlieBracket I (mpullback I J f V) (mpullback I J f W) x =
        mpullback I J f (mlieBracket J V W) x := by
    let _ : IsManifold I (minSmoothness ℝ 2) M := by
      rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
    let _ : IsManifold J (minSmoothness ℝ 2) N := by
      rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
    exact (mpullback_mlieBracket hV hW hf (by simp)).symm
  have hval (V W : Π y : N, TangentSpace J y) :
      b x (mpullback I J f V x) (mpullback I J f W x) = b' (f x) (V (f x)) (W (f x)) :=
    congr_fun (hpair V W) x
  rw [koszulBilinear_apply, koszulBilinear_apply, hd X hY hZ, hd Y hZ hX, hd Z hX hY, hbr hX hY,
    hbr hX hZ, hbr hY hZ, hval, hval, hval]

end Naturality

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

variable (I) in
/-- The right-hand side of the Koszul formula,

`X ⟪Y, Z⟫ + Y ⟪Z, X⟫ - Z ⟪X, Y⟫ + ⟪[X, Y], Z⟫ - ⟪[X, Z], Y⟫ - ⟪[Y, Z], X⟫`,

evaluated at `x`. It depends on the Riemannian metric alone; for the Levi-Civita connection `∇` of
that metric it computes `2 ⟪∇_X Y, Z⟫`, by
`CovariantDerivative.IsLeviCivitaConnection.two_inner_eq_koszul`. -/
def koszul (X Y Z : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  koszulBilinear I (fun _ ↦ innerSL ℝ) X Y Z x

/-- The defining formula for the Koszul expression, available outside the module where
`TauCeti.Manifold.koszul` is defined. -/
theorem koszul_apply (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    koszul I X Y Z x =
      mvfderiv I (fun y ↦ inner ℝ (Y y) (Z y)) x (X x)
        + mvfderiv I (fun y ↦ inner ℝ (Z y) (X y)) x (Y x)
        - mvfderiv I (fun y ↦ inner ℝ (X y) (Y y)) x (Z x)
        + inner ℝ (mlieBracket I X Y x) (Z x)
        - inner ℝ (mlieBracket I X Z x) (Y x)
        - inner ℝ (mlieBracket I Y Z x) (X x) := (rfl)

/-- Antisymmetrising the Koszul expression in its first two arguments returns twice the inner
product of the Lie bracket with the third argument. This is the identity behind the torsion-free
half of `CovariantDerivative.isLeviCivitaConnection_iff`. -/
theorem koszul_sub_koszul_swap_first_two :
    koszul I X Y Z x - koszul I Y X Z x = 2 * inner ℝ (mlieBracket I X Y x) (Z x) := by
  simpa only [koszul, innerSL_apply_apply ℝ] using
    (koszulBilinear_sub_koszulBilinear_swap_first_two
      (b := fun _ ↦ innerSL ℝ) (fun _ v w ↦ real_inner_comm w v) (X := X) (Y := Y)
        (Z := Z) (x := x))

/-- Symmetrising the Koszul expression in its last two arguments returns twice the derivative of
their inner product along the first argument. This is the identity behind the metric half of
`CovariantDerivative.isLeviCivitaConnection_iff`. -/
theorem koszul_add_koszul_swap_last_two :
    koszul I Z X Y x + koszul I Z Y X x =
      2 * mvfderiv I (fun y ↦ inner ℝ (X y) (Y y)) x (Z x) := by
  simpa only [koszul, innerSL_apply_apply ℝ] using
    (koszulBilinear_add_koszulBilinear_swap_last_two
      (b := fun _ ↦ innerSL ℝ) (fun _ v w ↦ real_inner_comm w v) (X := X) (Y := Y)
        (Z := Z) (x := x))

section InnerDifferentiability

variable [IsManifold I 1 M]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- The pointwise inner product of two sections of the tangent bundle that are differentiable at
`x` is differentiable at `x`. This is the tangent-bundle specialisation of
`MDifferentiableAt.inner_bundle`, whose bundle argument Lean cannot infer from hypotheses phrased
through `TangentSpace`. -/
theorem mdifferentiableAt_inner (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    MDiffAt (fun y ↦ inner ℝ (Y y) (Z y)) x :=
  MDifferentiableAt.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x)
    (b := id) hY hZ

end InnerDifferentiability

section Tensorial

variable [IsManifold I 2 M] [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [CompleteSpace E]

/-! ### Behaviour in the first two arguments

The Koszul expression is tensorial in its first argument, just as it is in its third, and obeys a
Leibniz rule in its second. These are the identities from which a connection is built out of the
Koszul formula, as Mathlib builds `CovariantDerivative.leviCivitaConnection`.
-/

variable {X' Y' : Π x : M, TangentSpace I x} {f : M → ℝ}

/-- The Koszul expression is additive in its second argument. -/
theorem koszul_add_second (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hY' : MDiffAt (T% Y') x) (hZ : MDiffAt (T% Z) x) :
    koszul I X (Y + Y') Z x = koszul I X Y Z x + koszul I X Y' Z x := by
  simpa only [koszul, innerSL_apply_apply ℝ] using
    (koszulBilinear_add_second (b := fun _ ↦ innerSL ℝ)
      (fun hU hV ↦ mdifferentiableAt_inner hU hV) hX hY hY' hZ)

/-- The Leibniz rule for the Koszul expression in its second argument: replacing `Y` by `f • Y`
multiplies the expression by `f x` and adds `2 (df X) ⟪Y, Z⟫`. This is the identity behind the
Leibniz axiom of the connection built from the Koszul formula. -/
theorem koszul_smul_second (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    koszul I X (f • Y) Z x =
      f x * koszul I X Y Z x + 2 * d% f x (X x) * inner ℝ (Y x) (Z x) := by
  simpa only [koszul, innerSL_apply_apply ℝ] using
    (koszulBilinear_smul_second (b := fun _ ↦ innerSL ℝ)
      (fun hU hV ↦ mdifferentiableAt_inner hU hV)
      (fun _ v w ↦ real_inner_comm w v) hf hX hY hZ)

/-- The Koszul expression is additive in its first argument. -/
theorem koszul_add_first (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszul I (X + X') Y Z x = koszul I X Y Z x + koszul I X' Y Z x := by
  simpa only [koszul, innerSL_apply_apply ℝ] using
    (koszulBilinear_add_first (b := fun _ ↦ innerSL ℝ)
      (fun hU hV ↦ mdifferentiableAt_inner hU hV) hX hX' hY hZ)

/-- The Koszul expression is tensorial in its first argument: replacing `X` by `f • X` multiplies
it by `f x`. -/
theorem koszul_smul_first (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) : koszul I (f • X) Y Z x = f x * koszul I X Y Z x := by
  simpa only [koszul, innerSL_apply_apply ℝ] using
    (koszulBilinear_smul_first (b := fun _ ↦ innerSL ℝ)
      (fun hU hV ↦ mdifferentiableAt_inner hU hV)
      (fun _ v w ↦ real_inner_comm w v) hf hX hY hZ)

/-- The Koszul expression is tensorial in its first argument. Together with
`TauCeti.Manifold.tensorialAt_koszul_third`, in finite dimension this yields a continuous bilinear
form on the tangent fibre via `TensorialAt.mkHom₂`, as used to build the Levi-Civita connection. -/
theorem tensorialAt_koszul_first (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    TensorialAt I E (fun X : Π y : M, TangentSpace I y ↦ koszul I X Y Z x) x := by
  simpa only [koszul, innerSL_apply_apply ℝ] using
    (tensorialAt_koszulBilinear_first (b := fun _ ↦ innerSL ℝ)
      (fun hU hV ↦ mdifferentiableAt_inner hU hV)
      (fun _ v w ↦ real_inner_comm w v) hY hZ)

/-- The Koszul expression is tensorial in its third argument: replacing `Z` by `f • Z` multiplies
it by `f x`, and it is additive in `Z`. Together with
`CovariantDerivative.isLeviCivitaConnection_iff` this is what turns the Koszul formula from a
characterisation of the Levi-Civita connection into a construction of it. -/
theorem tensorialAt_koszul_third (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    TensorialAt I E (fun Z : Π y : M, TangentSpace I y ↦ koszul I X Y Z x) x := by
  simpa only [koszul, innerSL_apply_apply ℝ] using
    (tensorialAt_koszulBilinear_third (b := fun _ ↦ innerSL ℝ)
      (fun hU hV ↦ mdifferentiableAt_inner hU hV)
      (fun _ v w ↦ real_inner_comm w v) hX hY)

end Tensorial

end Manifold

end TauCeti

/-! ### Levi-Civita connections and the Koszul expression -/

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
  {cov cov' : CovariantDerivative I F V}

/-- Two covariant derivatives have zero difference if they agree on every section differentiable
at the point where they are evaluated. -/
theorem difference_eq_zero_of_forall
    (h : ∀ (x : M) (Y : Π x : M, V x), MDiffAt (T% Y) x → cov Y x = cov' Y x) :
    cov.difference cov' = 0 := by
  ext x v
  have hv : MDiffAt (T% (extend F v : Π y : M, V y)) x :=
    mdifferentiableAt_extend I F v
  have hd := IsCovariantDerivativeOn.difference_apply cov.isCovariantDerivativeOnUniv
    cov'.isCovariantDerivativeOnUniv (x := x) (Set.mem_univ x) hv
  rw [extend_apply_self] at hd
  simp [CovariantDerivative.difference, hd, h x (extend F v) hv]

end CovariantDerivative

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {cov cov' : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  {X Y Z : Π x : M, TangentSpace I x} {x : M}

/-- **The Koszul formula**: for a Levi-Civita connection, `2 ⟪∇_X Y, Z⟫` is the Koszul expression
of the metric. Mathlib's `CovariantDerivative.IsLeviCivitaConnection.apply_eq` is the same identity
with the expression written out; this form is the one `TauCeti.Manifold.koszul` controls. -/
theorem IsLeviCivitaConnection.two_inner_eq_koszul (h : cov.IsLeviCivitaConnection)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    2 * inner ℝ (cov Y x (X x)) (Z x) = TauCeti.Manifold.koszul I X Y Z x := by
  have hk := h.apply_eq I hX hY hZ
  -- Reduce the beta-redexes introduced by the local notations in `apply_eq`.
  simp only at hk
  rw [hk, TauCeti.Manifold.koszul_apply, mlieBracket_swap_apply (V := Y),
    mlieBracket_swap_apply (V := Z) (W := Y), real_inner_comm (Y x) (mlieBracket I X Z x),
    real_inner_comm (Z x) (mlieBracket I X Y x), real_inner_comm (X x) (mlieBracket I Y Z x)]
  simp only [inner_neg_right]
  ring

/-- A covariant derivative on the tangent bundle is a Levi-Civita connection exactly when it
satisfies the Koszul formula. -/
theorem isLeviCivitaConnection_iff :
    cov.IsLeviCivitaConnection ↔ ∀ ⦃x : M⦄ ⦃X Y Z : Π x : M, TangentSpace I x⦄,
      MDiffAt (T% X) x → MDiffAt (T% Y) x → MDiffAt (T% Z) x →
      2 * inner ℝ (cov Y x (X x)) (Z x) = TauCeti.Manifold.koszul I X Y Z x := by
  refine ⟨fun h _ _ _ _ hX hY hZ ↦ h.two_inner_eq_koszul hX hY hZ, fun h ↦ ⟨?_, ?_⟩⟩
  · rw [CovariantDerivative.isMetricCompatible_iff]
    intro x X Y Z hX hY hZ
    simpa only [innerSL_apply_apply ℝ] using
      (TauCeti.Manifold.metricProductRule_of_two_apply_eq_koszulBilinear
        (b := fun _ ↦ innerSL ℝ) (fun _ v w ↦ real_inner_comm w v)
        (by
          intro x X Y Z hX hY hZ
          simpa only [TauCeti.Manifold.koszul, innerSL_apply_apply ℝ] using h hX hY hZ)
        hX hY hZ)
  · have hinjective (x : M) : Function.Injective fun u : TangentSpace I x ↦
        fun (Z : Π x : M, TangentSpace I x) (_ : MDiffAt (T% Z) x) ↦
          innerSL ℝ u (Z x) := by
      simpa only [innerSL_apply_apply ℝ] using
        injective_inner_mdifferentiableAt_section I E (TangentSpace I) x
    exact TauCeti.Manifold.torsion_eq_zero_of_two_apply_eq_koszulBilinear
      (b := fun _ ↦ innerSL ℝ) (fun _ v w ↦ real_inner_comm w v) hinjective
      (by
        intro x X Y Z hX hY hZ
        simpa only [TauCeti.Manifold.koszul, innerSL_apply_apply ℝ] using h hX hY hZ)

/-- **Uniqueness of the Levi-Civita connection**, as the vanishing of the endomorphism-valued
one-form measuring the difference of two connections. On a single differentiable section this is
Mathlib's `CovariantDerivative.IsLeviCivitaConnection.uniqueness`. -/
theorem IsLeviCivitaConnection.difference_eq_zero (h : cov.IsLeviCivitaConnection)
    (h' : cov'.IsLeviCivitaConnection) : cov.difference cov' = 0 :=
  difference_eq_zero_of_forall fun _ _ hY ↦
    ContinuousLinearMap.ext (h.uniqueness (hcov' := h') (hY := hY))

/-- **The Koszul formula** for Mathlib's Levi-Civita connection
`CovariantDerivative.leviCivitaConnection`, in terms of `TauCeti.Manifold.koszul`. -/
theorem two_inner_leviCivitaConnection_eq_koszul (hX : MDiffAt (T% X) x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    2 * inner ℝ (leviCivitaConnection I M Y x (X x)) (Z x) =
      TauCeti.Manifold.koszul I X Y Z x :=
  (isLeviCivitaConnection_leviCivitaConnection (I := I) (M := M)).two_inner_eq_koszul hX hY hZ

end CovariantDerivative
