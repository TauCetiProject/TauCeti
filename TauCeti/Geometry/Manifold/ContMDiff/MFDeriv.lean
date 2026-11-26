/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Regularity of differentials applied to sections and of derivatives in families

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

The differential of a vector-valued function is a section of the bundle of linear maps;
its regularity at a point also loses one derivative.

## Main results

* `ContMDiff.contMDiff_totalSpaceMk_mvfderiv`: the differential of a `C^(n+1)` function is a
  `C^n` section of the bundle of linear maps;
  `ContMDiffAt.contMDiffAt_totalSpaceMk_mvfderiv` is the pointwise statement.
* `ContMDiffAt.contMDiffAt_totalSpaceMk_mvfderiv_uncurry`,
  `ContMDiff.contMDiff_totalSpaceMk_mvfderiv_uncurry`: the differentials of a jointly `C^(n+1)`
  family of functions are jointly `C^n`, at a point or globally.

* `ContMDiffAt.mfderiv_right`: the differentials of the members of a jointly `C^m` family of
  maps between manifolds, in tangent coordinates, are jointly `C^n` when `n + 1 ≤ m`.
* `ContMDiffAt.fderiv_right`: the derivative in the vector-space variable of a jointly `C^m`
  family is jointly `C^n` when `n + 1 ≤ m`.
* `ContMDiffAt.deriv_uncurry`: the partial derivative in a scalar parameter of a jointly `C^m`
  function is jointly `C^n` when `n + 1 ≤ m`.
* `ContMDiffAt.iteratedFDeriv_right`: the `i`-th iterated derivative in the vector-space variable
  of a jointly `C^n` family is jointly `C^m` when `m + i ≤ n`.
* `ContMDiff.contMDiff_tangentMap_family`: the tangent maps of a jointly `C^m` family of maps
  between manifolds form a jointly `C^n` map when `n + 1 ≤ m`.

Applying the differential of a `C^(n+1)` map to a `C^n` tangent section gives a `C^n`
tangent field along the map (`ContMDiffAt.mfderiv_apply_sectionAlong`).

## Formal sources

* Mathlib's `ContMDiffAt.mfderiv` and `ContDiffAt.iteratedFDeriv_right`.
* Mathlib's `ContMDiff.contMDiff_tangentMap` and `contMDiff_equivTangentBundleProd_symm`: the
  tangent map of a member of a family is that of the uncurried family on the vectors `(0, v)`.
-/

public section

open scoped ContDiff Manifold

section SectionAlong

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  [TopologicalSpace HP] [TopologicalSpace P] [ChartedSpace HP P]
  {IP : ModelWithCorners 𝕜 EP HP} {b : P → M}
  {f : M → N} {s : ∀ y : P, TangentSpace I (b y)} {x : P} {m n : ℕ∞ω} {u : Set P}

/-- The differential of a map regular at a point sends a tangent section regular within a
set to a field along the map, losing one derivative of the map. No metric or
finite-dimensionality assumption is needed. -/
theorem ContMDiffWithinAt.mfderiv_apply_sectionAlong
    (hs : ContMDiffWithinAt IP (I.prod 𝓘(𝕜, E)) n
      (fun y ↦ Bundle.TotalSpace.mk' E (b y) (s y)) u x)
    (hf : ContMDiffAt I J m f (b x)) (hnm : n + 1 ≤ m) :
    ContMDiffWithinAt IP (J.prod 𝓘(𝕜, F)) n
      (fun y ↦ Bundle.TotalSpace.mk' F (f (b y)) (mfderiv I J f (b y) (s y))) u x := by
  -- The tangent map composed with a section is the bundled differential applied to that section.
  simpa only [Function.comp_def, tangentMap] using
    (hf.contMDiffAt_tangentMap hnm).comp_contMDiffWithinAt x hs

/-- The differential of a `C^m` map sends a `C^n` tangent section to a `C^n` field along
it when `n + 1 ≤ m`. No metric or finite-dimensionality assumption is needed. -/
theorem ContMDiffAt.mfderiv_apply_sectionAlong (hf : ContMDiffAt I J m f (b x))
    (hs : ContMDiffAt IP (I.prod 𝓘(𝕜, E)) n
      (fun y ↦ Bundle.TotalSpace.mk' E (b y) (s y)) x)
    (hnm : n + 1 ≤ m) :
    ContMDiffAt IP (J.prod 𝓘(𝕜, F)) n
      (fun y ↦ Bundle.TotalSpace.mk' F (f (b y)) (mfderiv I J f (b y) (s y))) x :=
  ContMDiffWithinAt.mfderiv_apply_sectionAlong hs hf hnm

/-- The differential sends a tangent field along a base map, regular on a set, to a regular
field along the composite when the map is regular at the image points and `n + 1 ≤ m`. -/
theorem ContMDiffOn.mfderiv_apply_sectionAlong
    (hs : ContMDiffOn IP (I.prod 𝓘(𝕜, E)) n
      (fun y ↦ Bundle.TotalSpace.mk' E (b y) (s y)) u)
    (hf : ∀ x ∈ u, ContMDiffAt I J m f (b x)) (hnm : n + 1 ≤ m) :
    ContMDiffOn IP (J.prod 𝓘(𝕜, F)) n
      (fun y ↦ Bundle.TotalSpace.mk' F (f (b y)) (mfderiv I J f (b y) (s y))) u :=
  fun x hx ↦ (hs x hx).mfderiv_apply_sectionAlong (hf x hx) hnm

/-- The differential of a `C^m` map sends a `C^n` tangent field along any base map to a
`C^n` field along the composite when `n + 1 ≤ m`. -/
theorem ContMDiff.mfderiv_apply_sectionAlong (hf : ContMDiff I J m f)
    (hs : ContMDiff IP (I.prod 𝓘(𝕜, E)) n
      (fun y ↦ Bundle.TotalSpace.mk' E (b y) (s y))) (hnm : n + 1 ≤ m) :
    ContMDiff IP (J.prod 𝓘(𝕜, F)) n
      (fun y ↦ Bundle.TotalSpace.mk' F (f (b y)) (mfderiv I J f (b y) (s y))) :=
  fun x ↦ (hf (b x)).mfderiv_apply_sectionAlong (hs x) hnm

end SectionAlong

section Family

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  [TopologicalSpace HP] [TopologicalSpace P] [ChartedSpace HP P]
  {IP : ModelWithCorners 𝕜 EP HP} [IsManifold IP 1 P] {m n : ℕ∞ω}

/-- The differentials of the members of a jointly `C^n` family of maps `f p : M → N`, written in
tangent coordinates, are jointly `C^m` in the parameter and the point when `m + 1 ≤ n`. -/
theorem ContMDiffAt.mfderiv_right {f : P → M → N} {p₀ : P × M}
    (hf : ContMDiffAt (IP.prod I) J n (Function.uncurry f) p₀) (hmn : m + 1 ≤ n) :
    ContMDiffAt (IP.prod I) 𝓘(𝕜, E →L[𝕜] F) m
      (inTangentCoordinates I J Prod.snd (fun p : P × M ↦ f p.1 p.2)
        (fun p ↦ mfderiv I J (f p.1) p.2) p₀) p₀ :=
  (hf.comp (p₀, p₀.2) ((contMDiffAt_fst.comp _ contMDiffAt_fst).prodMk contMDiffAt_snd)).mfderiv
    (fun (p : P × M) (x : M) ↦ f p.1 x) Prod.snd contMDiffAt_snd hmn

end Family

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
  convert hg.mfderiv_right hnm using 1
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

/-- **Regularity of the partial derivative in a scalar parameter.** If `(t, a) ↦ f t a` is `C^m`
at `p₀` and `n + 1 ≤ m`, then the partial derivative `(t, a) ↦ ∂_t f t a` is `C^n` at `p₀`. -/
theorem ContMDiffAt.deriv_uncurry {f : 𝕜 → P → F} {p₀ : 𝕜 × P}
    (hf : ContMDiffAt (𝓘(𝕜).prod J) 𝓘(𝕜, F) m (Function.uncurry f) p₀) (hnm : n + 1 ≤ m) :
    ContMDiffAt (𝓘(𝕜).prod J) 𝓘(𝕜, F) n (fun p : 𝕜 × P ↦ deriv (fun s ↦ f s p.2) p.1) p₀ := by
  -- Swap the factors to use the derivative in the vector-space variable of a family.
  have hswap : ContMDiffAt (J.prod 𝓘(𝕜)) 𝓘(𝕜, F) m
      (Function.uncurry fun (a : P) (s : 𝕜) ↦ f s a) (p₀.2, p₀.1) :=
    hf.comp (p₀.2, p₀.1) (contMDiffAt_snd.prodMk contMDiffAt_fst)
  have h := (hswap.fderiv_right hnm).comp p₀ (contMDiffAt_snd.prodMk contMDiffAt_fst)
  simpa only [Function.comp_def, ContinuousLinearMap.apply_apply, fderiv_apply_one_eq_deriv]
    using (ContinuousLinearMap.apply 𝕜 F (1 : 𝕜)).contMDiff.contMDiffAt.comp p₀ h

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
  exact ((hf.mdifferentiable (zero_lt_one.trans_le h1).ne' (q, x)).mfderiv_uncurry_apply_zero_mk
    v).symm

end TangentMap

section VectorValued

open Bundle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The differential of a function that is `C^(n+1)` at a point is a `C^n` section of the
bundle of linear maps at that point. -/
theorem ContMDiffAt.contMDiffAt_totalSpaceMk_mvfderiv [IsManifold I 1 M]
    {n : WithTop ℕ∞} {f : M → F} {x : M} (hf : ContMDiffAt I 𝓘(ℝ, F) (n + 1) f x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] F)) n (fun y ↦ TotalSpace.mk' (E →L[ℝ] F)
      (E := fun y : M ↦ TangentSpace I y →L[ℝ] F) y (mvfderiv I f y)) x := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, (hf.mfderiv_const le_rfl).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y ↦ ?_)⟩
  -- The target trivialization and its tangent coordinates are identities; the remaining
  -- comparison is the evaluation lemma for the vector-valued derivative.
  simp only [ContinuousLinearMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
    Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_comp,
    inTangentCoordinates, TangentBundle.continuousLinearMapAt_model_space]
  ext v
  exact mvfderiv_apply_eq_mfderiv_apply f y _

/-- **The differential of a `C^(n+1)` function is a `C^n` covector field**: `x ↦ df_x` is a `C^n`
section of the bundle of linear maps `TangentSpace I x →L[ℝ] F`, which is the cotangent bundle
when `F = ℝ`. -/
theorem ContMDiff.contMDiff_totalSpaceMk_mvfderiv [IsManifold I 1 M] {n : WithTop ℕ∞}
    {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) (n + 1) f) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) n (fun x ↦ TotalSpace.mk' (E →L[ℝ] F)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] F) x (mvfderiv I f x)) :=
  fun x ↦ (hf x).contMDiffAt_totalSpaceMk_mvfderiv

/-- **The differential of a jointly `C^(n+1)` family is jointly `C^n` at a point.** For a family of
functions `f : N → M → F` which is jointly `C^(n+1)` at `q = (p, x)`, the differentials
`(p', x') ↦ d(f p')_{x'}` form a map into the bundle of linear maps `TangentSpace I x' →L[ℝ] F`
which is `C^n` at `q`. -/
theorem ContMDiffAt.contMDiffAt_totalSpaceMk_mvfderiv_uncurry [IsManifold I 1 M]
    {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
    {n : WithTop ℕ∞} {f : N → M → F} {q : N × M}
    (hf : ContMDiffAt (J.prod I) 𝓘(ℝ, F) (n + 1) (Function.uncurry f) q) :
    ContMDiffAt (J.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) n (fun q : N × M ↦ TotalSpace.mk' (E →L[ℝ] F)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] F) q.2 (mvfderiv I (f q.1) q.2)) q := by
  have hf' : ContMDiffAt ((J.prod I).prod I) 𝓘(ℝ, F) (n + 1) (fun p : (N × M) × M ↦ f p.1.1 p.2)
      (q, q.2) :=
    hf.comp (q, q.2) ((contMDiffAt_fst.comp _ contMDiffAt_fst).prodMk contMDiffAt_snd)
  have hd := ContMDiffAt.mfderiv (fun p : N × M ↦ f p.1) Prod.snd hf' contMDiffAt_snd le_rfl
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_snd, hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p ↦ ?_)⟩
  -- In the trivial bundle and in the tangent bundle of the model space `F`, the coordinate
  -- changes are the identity, and `mvfderiv` is `mfderiv` read in `F`.
  simp only [ContinuousLinearMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
    Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_comp,
    inTangentCoordinates, TangentBundle.continuousLinearMapAt_model_space]
  ext v
  exact mvfderiv_apply_eq_mfderiv_apply (f p.1) p.2 _

/-- **The differential of a jointly `C^(n+1)` family is jointly `C^n`.** For a family of functions
`f : N → M → F` which is jointly `C^(n+1)` on `N × M`, the differentials `(p, x) ↦ d(f p)_x` form a
`C^n` map into the bundle of linear maps `TangentSpace I x →L[ℝ] F`, lying over the projection
`N × M → M`. For `N = ℝ` this is the regularity in time and space of the differential of a
time-dependent function. -/
theorem ContMDiff.contMDiff_totalSpaceMk_mvfderiv_uncurry [IsManifold I 1 M]
    {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
    {n : WithTop ℕ∞} {f : N → M → F}
    (hf : ContMDiff (J.prod I) 𝓘(ℝ, F) (n + 1) (Function.uncurry f)) :
    ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) n (fun q : N × M ↦ TotalSpace.mk' (E →L[ℝ] F)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] F) q.2 (mvfderiv I (f q.1) q.2)) :=
  fun q ↦ (hf q).contMDiffAt_totalSpaceMk_mvfderiv_uncurry

end VectorValued
