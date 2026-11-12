/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Joint regularity of derivatives in families

For a jointly `C^m` family of maps from a normed space to another normed space, the derivative
in the vector-space variable is jointly `C^n` when `n + 1 ≤ m`. The parameter may range over
a manifold. Iterating, the `i`-th derivative in the vector-space variable loses `i` orders of
joint regularity; the order `i` counts only derivatives in that variable. This supplies derivative
regularity for parameter-dependent coordinate formulas, including the Christoffel symbols of a
metric family and every finite jet of its coefficients.

The same holds for a jointly `C^m` family of maps `f q : M → N` between manifolds: the tangent
maps `T(f q) : TM → TN` form a jointly `C^n` map `Q × TM → TN`
(`ContMDiff.contMDiff_tangentMap_family`). This is how differentials of a smooth family of
diffeomorphisms act smoothly on tangent tensors, for instance in pulling back a family of almost
complex structures along a family of diffeomorphisms.

## Main results

* `ContMDiffAt.fderiv_right`: the derivative in the vector-space variable of a jointly `C^m`
  family is jointly `C^n` when `n + 1 ≤ m`.
* `ContMDiffAt.iteratedFDeriv_right`: the `i`-th iterated derivative in the vector-space variable
  of a jointly `C^n` family is jointly `C^m` when `m + i ≤ n`.
* `ContMDiff.contMDiff_tangentMap_family`: the tangent maps of a jointly `C^m` family of maps
  between manifolds form a jointly `C^n` map when `n + 1 ≤ m`.

## Formal sources

* Mathlib's `ContMDiffAt.mfderiv` and `ContDiffAt.iteratedFDeriv_right`.
* Mathlib's `ContMDiff.contMDiff_tangentMap` and `contMDiff_equivTangentBundleProd_symm`: the
  tangent map of a member of a family is that of the uncurried family on the vectors `(0, v)`.
-/

public section

open scoped ContDiff Manifold


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners 𝕜 G H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold J 1 P]
  {g : P → E → F} {m n : ℕ∞ω} {z : P × E}

/-- The derivative in the vector-space variable of a jointly `C^m` family is jointly `C^n`
at a point when `n + 1 ≤ m`. No finite-dimensionality or completeness is required. -/
theorem ContMDiffAt.fderiv_right
    (hg : ContMDiffAt (J.prod 𝓘(𝕜, E)) 𝓘(𝕜, F) m (Function.uncurry g) z)
    (hnm : n + 1 ≤ m) :
    ContMDiffAt (J.prod 𝓘(𝕜, E)) 𝓘(𝕜, E →L[𝕜] F) n
      (fun q : P × E ↦ fderiv 𝕜 (g q.1) q.2) z := by
  have hfamily : ContMDiffAt ((J.prod 𝓘(𝕜, E)).prod 𝓘(𝕜, E)) 𝓘(𝕜, F) m
      (fun q : (P × E) × E ↦ g q.1.1 q.2) (z, z.2) :=
    hg.comp (z, z.2) ((contMDiffAt_fst.comp _ contMDiffAt_fst).prodMk contMDiffAt_snd)
  have h := hfamily.mfderiv (fun q : P × E ↦ g q.1) Prod.snd contMDiffAt_snd hnm
  convert h using 1
  ext q : 1
  -- `mfderiv` uses the normed-space instances on tangent fibres, whereas the model-space
  -- lemma uses those on E and F. `erw` unfolds these fibre instances; `rw` cannot match them.
  erw [inTangentCoordinates_model_space (I := 𝓘(𝕜, E)) (I' := 𝓘(𝕜, F))]
  exact (mfderiv_eq_fderiv (𝕜 := 𝕜) (f := g q.1) (x := q.2)).symm

/-- The `i`-th iterated derivative in the vector-space variable of a jointly `C^n` family is
jointly `C^m` at a point when `m + i ≤ n`. -/
theorem ContMDiffAt.iteratedFDeriv_right {i : ℕ}
    (hg : ContMDiffAt (J.prod 𝓘(𝕜, E)) 𝓘(𝕜, F) n (Function.uncurry g) z)
    (hmn : m + i ≤ n) :
    ContMDiffAt (J.prod 𝓘(𝕜, E)) 𝓘(𝕜, E [×i]→L[𝕜] F) m
      (fun q : P × E ↦ iteratedFDeriv 𝕜 i (g q.1) q.2) z := by
  induction i generalizing m with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact (continuousMultilinearCurryFin0 𝕜 E F).symm.contDiff.contMDiff.contMDiffAt.comp z
      (hg.of_le (by simpa using hmn))
  | succ i ih =>
    have hi := ih (m := m + 1) (by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm 1 (i : ℕ∞ω)] using hmn)
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    exact (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (i + 1) ↦ E) F).symm.contDiff
      |>.contMDiff.contMDiffAt.comp z
        (hi.fderiv_right (g := fun p ↦ iteratedFDeriv 𝕜 i (g p)) le_rfl)

section TangentMap

open Bundle

variable {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace 𝕜 EQ] [TopologicalSpace HQ]
  {IQ : ModelWithCorners 𝕜 EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
  {HM M : Type*} [TopologicalSpace HM] {I : ModelWithCorners 𝕜 E HM}
  [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I 1 M]
  {HN N : Type*} [TopologicalSpace HN] {I' : ModelWithCorners 𝕜 F HN}
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold I' 1 N]

/-- For a jointly `C^m` family of maps `f q : M → N` between manifolds, the tangent maps of the
members of the family form a jointly `C^n` map `Q × TM → TN` when `n + 1 ≤ m`. -/
theorem ContMDiff.contMDiff_tangentMap_family [IsManifold IQ m Q] {f : Q → M → N}
    (hf : ContMDiff (IQ.prod I) I' m (Function.uncurry f)) (hnm : n + 1 ≤ m) :
    ContMDiff (IQ.prod I.tangent) I'.tangent n
      (fun p : Q × TangentBundle I M ↦ tangentMap I I' (f p.1) p.2) := by
  have h1 : 1 ≤ m := le_add_self.trans hnm
  have : IsManifold IQ 1 Q := .of_le h1
  have : IsManifold IQ (n + 1) Q := .of_le hnm
  have : ContMDiffVectorBundle n EQ (TangentSpace IQ : Q → Type _) IQ :=
    TangentBundle.contMDiffVectorBundle
  -- The tangent map of `f q` at `v` is that of the uncurried family at `(0, v)`.
  have h := (hf.contMDiff_tangentMap hnm).comp
    (contMDiff_equivTangentBundleProd_symm.comp
      (((contMDiff_zeroSection 𝕜 (TangentSpace IQ : Q → Type _)).comp contMDiff_fst).prodMk
        contMDiff_snd))
  refine h.congr fun ⟨q, x, v⟩ ↦ ?_
  -- `tangentMap`, `equivTangentBundleProd.symm`, `zeroSection` and `Function.uncurry` unfold to
  -- this by `rfl`. The vectors live in `TangentSpace`s, which are only definitionally the model
  -- spaces, so the goal is stated with `change` rather than reached by `simp`.
  change (⟨f q x, mfderiv I I' (f q) x v⟩ : TangentBundle I' N) =
    ⟨f q x, mfderiv (IQ.prod I) I' (Function.uncurry f) (q, x) (0, v)⟩
  congr 1
  -- The product rule, whose first summand vanishes at the zero vector.
  have hd := (mfderiv_prod_eq_add_apply ((hf.mdifferentiable (zero_lt_one.trans_le h1).ne')
    (q, x)) (v := ((0, v) : EQ × E))).trans ((congrArg (· + _) (map_zero _)).trans (zero_add _))
  exact hd.symm

end TangentMap
