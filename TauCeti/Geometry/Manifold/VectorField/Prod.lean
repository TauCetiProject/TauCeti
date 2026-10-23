/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# Product vector fields

Vector fields `X` on `M` and `Y` on `N` combine to the vector field `(X, Y)` on `M × N`, whose value
at `(x, y)` is `(X x, Y y)` under the identification of the tangent space of a product with the
product of the tangent spaces. Such a field is differentiable, respectively `C^n`, at `(x, y)` when
`X` is at `x` and `Y` is at `y`, and the Lie bracket of two product fields is computed factor by
factor: `[(X₁, X₂), (Y₁, Y₂)] = ([X₁, Y₁], [X₂, Y₂])`.

Product fields are the fields along which the geometry of a product manifold splits. The tangent
space at every point is spanned by values of product fields, and differential operators such as the
Levi-Civita connection of a product metric are computed on them.

A vector-valued function on `M` composed with the projection `M × N → M` differentiates a product
field `(X, Y)` along `X` only (`TauCeti.mvfderiv_comp_fst_apply`), and symmetrically for `N`; this
is what makes the bracket of product fields split.

## Main definitions

* `TauCeti.Manifold.prodVectorField`: the vector field `(X, Y)` on `M × N`.

## Main results

* `TauCeti.Manifold.mdifferentiableAt_prodVectorField`,
  `TauCeti.Manifold.contMDiffAt_prodVectorField` and `TauCeti.Manifold.contMDiff_prodVectorField`:
  regularity of product fields.
* `TauCeti.Manifold.mlieBracket_prodVectorField`: the Lie bracket of product fields is the product
  of the Lie brackets.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 8
  (vector fields and Lie brackets).
-/

public section

noncomputable section

open Bundle Manifold VectorField
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-! ### Product vector fields -/

/-- The vector field on `M × N` whose value at `p` is `(X p.1, Y p.2)`. -/
def prodVectorField (X : Π x : M, TangentSpace I x) (Y : Π y : N, TangentSpace J y) :
    Π p : M × N, TangentSpace (I.prod J) p :=
  fun p ↦ (X p.1, Y p.2)

/-- The components of a product field are the values of its factors. Not a `simp` lemma, since
`simp` already removes `tangentSpaceProdEquiv` by `TauCeti.Manifold.tangentSpaceProdEquiv_apply`. -/
theorem tangentSpaceProdEquiv_prodVectorField (X : Π x : M, TangentSpace I x)
    (Y : Π y : N, TangentSpace J y) (p : M × N) :
    tangentSpaceProdEquiv p (prodVectorField X Y p) = (X p.1, Y p.2) := by
  rw [tangentSpaceProdEquiv_apply]
  rfl

/-- The first component of a product field is the value of its first factor. -/
@[simp]
theorem prodVectorField_fst (X : Π x : M, TangentSpace I x) (Y : Π y : N, TangentSpace J y)
    (p : M × N) : (prodVectorField X Y p).1 = X p.1 :=
  (rfl)

/-- The second component of a product field is the value of its second factor. -/
@[simp]
theorem prodVectorField_snd (X : Π x : M, TangentSpace I x) (Y : Π y : N, TangentSpace J y)
    (p : M × N) : (prodVectorField X Y p).2 = Y p.2 :=
  (rfl)

section Regularity

variable [IsManifold I 1 M] [IsManifold J 1 N] {X : Π x : M, TangentSpace I x}
  {Y : Π y : N, TangentSpace J y} {p : M × N}

/-- A product of vector fields is `C^n` at `p` when the factors are `C^n` at `p.1` and `p.2`. -/
theorem contMDiffAt_prodVectorField {n : ℕ∞ω} (hX : ContMDiffAt I I.tangent n (T% X) p.1)
    (hY : ContMDiffAt J J.tangent n (T% Y) p.2) :
    ContMDiffAt (I.prod J) (I.prod J).tangent n (T% (prodVectorField X Y)) p :=
  (contMDiff_equivTangentBundleProd_symm (I := I) (M := M) (I' := J) (M' := N) _).comp p
    ((hX.comp p contMDiffAt_fst).prodMk (hY.comp p contMDiffAt_snd))

/-- A product of `C^n` vector fields is `C^n`. -/
theorem contMDiff_prodVectorField {n : ℕ∞ω} (hX : ContMDiff I I.tangent n (T% X))
    (hY : ContMDiff J J.tangent n (T% Y)) :
    ContMDiff (I.prod J) (I.prod J).tangent n (T% (prodVectorField X Y)) :=
  fun p ↦ contMDiffAt_prodVectorField (hX p.1) (hY p.2)

/-- A product of vector fields is differentiable at `p` when the factors are differentiable at
`p.1` and `p.2`. -/
theorem mdifferentiableAt_prodVectorField (hX : MDifferentiableAt I I.tangent (T% X) p.1)
    (hY : MDifferentiableAt J J.tangent (T% Y) p.2) :
    MDifferentiableAt (I.prod J) (I.prod J).tangent (T% (prodVectorField X Y)) p :=
  ((contMDiff_equivTangentBundleProd_symm (I := I) (M := M) (I' := J) (M' := N)
    (n := 1)).mdifferentiable one_ne_zero _).comp p
    ((hX.comp p mdifferentiableAt_fst).prodMk (hY.comp p mdifferentiableAt_snd))

end Regularity

/-! ### The Lie bracket of product vector fields -/

section LieBracket

variable [CompleteSpace E] [CompleteSpace E'] [IsManifold I (minSmoothness 𝕜 2) M]
  [IsManifold J (minSmoothness 𝕜 2) N] {X₁ Y₁ : Π x : M, TangentSpace I x}
  {X₂ Y₂ : Π y : N, TangentSpace J y} {p : M × N}

private theorem fst_mlieBracket_prodVectorField (hX₁ : MDifferentiableAt I I.tangent (T% X₁) p.1)
    (hY₁ : MDifferentiableAt I I.tangent (T% Y₁) p.1)
    (hX₂ : MDifferentiableAt J J.tangent (T% X₂) p.2)
    (hY₂ : MDifferentiableAt J J.tangent (T% Y₂) p.2) :
    (mlieBracket (I.prod J) (prodVectorField X₁ X₂) (prodVectorField Y₁ Y₂) p).1 =
      mlieBracket I X₁ Y₁ p.1 := by
  have h1 : (1 : ℕ∞ω) ≤ minSmoothness 𝕜 2 :=
    (show (1 : ℕ∞ω) ≤ 2 by norm_num).trans le_minSmoothness
  have : IsManifold I 1 M := .of_le h1
  have : IsManifold J 1 N := .of_le h1
  -- Test the bracket of the product fields against the chart of `M` at `p.1`, composed with
  -- the projection: this differentiates product fields through their `M`-component only.
  set φ := extChartAt I p.1
  have hφ : ContMDiffAt I 𝓘(𝕜, E) (minSmoothness 𝕜 2) φ p.1 := contMDiffAt_extChartAt
  have hprod := mvfderiv_mlieBracket (hφ.comp p contMDiffAt_fst) le_rfl
    (mdifferentiableAt_prodVectorField hX₁ hX₂) (mdifferentiableAt_prodVectorField hY₁ hY₂)
  have hW (W₁ : Π x : M, TangentSpace I x) (W₂ : Π y : N, TangentSpace J y) :
      (fun q ↦ mvfderiv (I.prod J) (φ ∘ Prod.fst) q (prodVectorField W₁ W₂ q)) =
        (fun x ↦ mvfderiv I φ x (W₁ x)) ∘ Prod.fst :=
    funext fun q ↦ mvfderiv_comp_fst_apply φ q _
  rw [hW, hW, mvfderiv_comp_fst_apply, mvfderiv_comp_fst_apply, mvfderiv_comp_fst_apply,
    prodVectorField_fst, prodVectorField_fst] at hprod
  exact eq_mlieBracket_of_mvfderiv_extChartAt hX₁ hY₁ hprod

private theorem snd_mlieBracket_prodVectorField (hX₁ : MDifferentiableAt I I.tangent (T% X₁) p.1)
    (hY₁ : MDifferentiableAt I I.tangent (T% Y₁) p.1)
    (hX₂ : MDifferentiableAt J J.tangent (T% X₂) p.2)
    (hY₂ : MDifferentiableAt J J.tangent (T% Y₂) p.2) :
    (mlieBracket (I.prod J) (prodVectorField X₁ X₂) (prodVectorField Y₁ Y₂) p).2 =
      mlieBracket J X₂ Y₂ p.2 := by
  have h1 : (1 : ℕ∞ω) ≤ minSmoothness 𝕜 2 :=
    (show (1 : ℕ∞ω) ≤ 2 by norm_num).trans le_minSmoothness
  have : IsManifold I 1 M := .of_le h1
  have : IsManifold J 1 N := .of_le h1
  -- Test the bracket of the product fields against the chart of `N` at `p.2`, composed with
  -- the projection: this differentiates product fields through their `N`-component only.
  set φ := extChartAt J p.2
  have hφ : ContMDiffAt J 𝓘(𝕜, E') (minSmoothness 𝕜 2) φ p.2 := contMDiffAt_extChartAt
  have hprod := mvfderiv_mlieBracket (hφ.comp p contMDiffAt_snd) le_rfl
    (mdifferentiableAt_prodVectorField hX₁ hX₂) (mdifferentiableAt_prodVectorField hY₁ hY₂)
  have hW (W₁ : Π x : M, TangentSpace I x) (W₂ : Π y : N, TangentSpace J y) :
      (fun q ↦ mvfderiv (I.prod J) (φ ∘ Prod.snd) q (prodVectorField W₁ W₂ q)) =
        (fun y ↦ mvfderiv J φ y (W₂ y)) ∘ Prod.snd :=
    funext fun q ↦ mvfderiv_comp_snd_apply φ q _
  rw [hW, hW, mvfderiv_comp_snd_apply, mvfderiv_comp_snd_apply, mvfderiv_comp_snd_apply,
    prodVectorField_snd, prodVectorField_snd] at hprod
  exact eq_mlieBracket_of_mvfderiv_extChartAt hX₂ hY₂ hprod

/-- The Lie bracket of two product vector fields is the product of the Lie brackets of their
factors: `[(X₁, X₂), (Y₁, Y₂)] = ([X₁, Y₁], [X₂, Y₂])` at every point where the four factors are
differentiable. -/
theorem mlieBracket_prodVectorField (hX₁ : MDifferentiableAt I I.tangent (T% X₁) p.1)
    (hY₁ : MDifferentiableAt I I.tangent (T% Y₁) p.1)
    (hX₂ : MDifferentiableAt J J.tangent (T% X₂) p.2)
    (hY₂ : MDifferentiableAt J J.tangent (T% Y₂) p.2) :
    mlieBracket (I.prod J) (prodVectorField X₁ X₂) (prodVectorField Y₁ Y₂) p =
      prodVectorField (mlieBracket I X₁ Y₁) (mlieBracket J X₂ Y₂) p :=
  Prod.ext (fst_mlieBracket_prodVectorField hX₁ hY₁ hX₂ hY₂)
    (snd_mlieBracket_prodVectorField hX₁ hY₁ hX₂ hY₂)

end LieBracket

end TauCeti.Manifold
