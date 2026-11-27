/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.ContinuousMultilinearMap
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import TauCeti.Geometry.Manifold.VectorBundle.ContinuousMultilinearMap.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# The induced connection on a bundle of continuous multilinear maps

Let `V` and `W` be vector bundles over a manifold `M`, with `V` of finite rank, and `ι` a finite
index type. Connections `∇` on `V` and `W` induce a connection on the bundle
`Mult^ι(V, W)` with fibres `ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)`
(`CovariantDerivative.continuousMultilinearMap`), by the evaluation rule

`(∇_v A)(s₁, …, sₖ) = ∇_v (A(s₁, …, sₖ)) - ∑ᵢ A(s₁, …, ∇_v sᵢ, …, sₖ)`

(`CovariantDerivative.continuousMultilinearMap_apply`). This rule determines the induced
connection on differentiable sections (`CovariantDerivative.continuousMultilinearMap_eq_of_apply`).
Changing the connections on `V` and `W` changes it by their difference tensors
(`CovariantDerivative.continuousMultilinearMap_apply_sub_continuousMultilinearMap_apply`).
Smooth connections on `V` and `W` induce a smooth connection
(`CovariantDerivative.contMDiff_continuousMultilinearMap` and the
`ContMDiffCovariantDerivative` instance), so the construction can be applied again to the
covariant derivative of a smooth section.

For `V = TM` the sections of `Mult^ι(TM, W)` with `ι = Fin j` are the `W`-valued covariant
tensor fields of rank `j`. With a connection on `TM` and one on `W`, the induced connection
differentiates them, which is how the iterated covariant derivatives `∇ʲσ` of a section `σ` of
`W` are formed.

The convention follows J. M. Lee, *Introduction to Riemannian Manifolds*, second edition,
Chapter 4 (induced connections on tensor bundles); the `Hom` case is
`CovariantDerivative.hom`.

## Main definitions

* `covV.continuousMultilinearMap ι covW`: the connection induced on the bundle of continuous
  multilinear maps `(V x)^ι → W x` by connections `covV` on `V` and `covW` on `W`.

## Main results

* `CovariantDerivative.continuousMultilinearMap_apply`: the evaluation rule.
* `CovariantDerivative.covariantDerivative_continuousMultilinearMap_apply`: the Leibniz rule
  `∇_v (A(s₁, …, sₖ)) = (∇_v A)(s₁, …, sₖ) + ∑ᵢ A(s₁, …, ∇_v sᵢ, …, sₖ)`.
* `CovariantDerivative.continuousMultilinearMap_eq_of_apply`: uniqueness.
* `CovariantDerivative.continuousMultilinearMap_apply_sub_continuousMultilinearMap_apply`:
  dependence on the connections through their difference tensors.
* `CovariantDerivative.contMDiff_continuousMultilinearMap`: the covariant derivative of a smooth
  section is a smooth section of `Hom(TM, Mult^ι(V, W))`.

## Implementation notes

The right-hand side of the evaluation rule is tensorial in each `sᵢ`: it is additive and linear
over differentiable functions, since the Leibniz terms `df ⊗ A(…, sᵢ, …)` of the two sides
cancel. Mathlib's tensoriality criterion (`TensorialAt.pointwise`) then shows that it only depends
on the values `sᵢ(x)`. The resulting multilinear map on the fibre `V x` is continuous because
`V x` is finite-dimensional, and its dependence on the tangent vector `v` is continuous because
it is read on the normed model fibres through `ContinuousMultilinearMap.flipLinear`. At a point
where `A` is not differentiable the operator is defined to be zero, since the axioms of a native
covariant derivative concern differentiable inputs.
-/

public section

open Bundle FiberBundle Function
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle 1 F V I]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul 𝕜 (W x)] [FiberBundle G W] [VectorBundle 𝕜 G W]
  {ι : Type*} [Fintype ι]
  (covV : CovariantDerivative I F V) (covW : CovariantDerivative I G W)

open scoped Classical in
/-- The right-hand side `∇ (A(s₁, …, sₖ)) - ∑ᵢ A(s₁, …, ∇ sᵢ, …, sₖ)` of the evaluation rule at
`x`, as a function of the family of sections `s`. -/
private def multilinearAux (A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x))
    (s : ι → Π x : M, V x) (x : M) : TangentSpace I x →L[𝕜] W x :=
  covW (fun y ↦ A y (fun i ↦ s i y)) x -
    ∑ i, ((A x).toContinuousLinearMap (fun j ↦ s j x) i).comp (covV (s i) x)

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle 1 F V I] [VectorBundle 𝕜 G W] in
private theorem multilinearAux_apply [DecidableEq ι]
    (A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x))
    (s : ι → Π x : M, V x) (x : M) (v : TangentSpace I x) :
    multilinearAux covV covW A s x v = covW (fun y ↦ A y (fun i ↦ s i y)) x v -
      ∑ i, A x (update (fun j ↦ s j x) i (covV (s i) x v)) := by
  simp only [multilinearAux, sub_apply, FunLike.coe_sum,
    Finset.sum_apply, ContinuousLinearMap.coe_comp, comp_apply,
    ContinuousMultilinearMap.toContinuousLinearMap_apply]
  congr! 4

omit [∀ x, IsTopologicalAddGroup (V x)] [Fintype ι] in
/-- Extending the fibre vectors of a family with one slot replaced replaces the same slot of the
extensions. -/
private theorem extend_comp_update [DecidableEq ι] {x : M} {X : Type*} (g : X → V x)
    (u : ι → X) (i : ι) (w : X) :
    (fun j ↦ FiberBundle.extend F (g (update u i w j))) =
      update (fun j ↦ FiberBundle.extend F (g (u j))) i (FiberBundle.extend F (g w)) :=
  comp_update (fun w ↦ FiberBundle.extend F (g w)) u i w

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul 𝕜 (W x)] [Fintype ι] in
/-- Replacing the `i`-th section by `f • t` in one term `A(s₁, …, ∇_v sⱼ, …, sₖ)` of the evaluation
rule multiplies it by `f x`, up to the Leibniz term `df(v) A(s₁, …, t, …, sₖ)` when `j = i`. -/
private theorem apply_update_update_smul [DecidableEq ι] {x : M}
    (Ax : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)) (s : ι → Π x : M, V x)
    {t : Π x : M, V x} {f : M → 𝕜} (hf : MDiffAt f x) (ht : MDiffAt (T% t) x) (i j : ι)
    (v : TangentSpace I x) :
    Ax (update (update (fun k ↦ s k x) i ((f • t) x)) j (covV (update s i (f • t) j) x v)) =
      f x • Ax (update (update (fun k ↦ s k x) i (t x)) j (covV (update s i t j) x v)) +
        if j = i then (d% f x v) • Ax (update (fun k ↦ s k x) i (t x)) else 0 := by
  rcases eq_or_ne j i with rfl | hji
  · simp [covV.isCovariantDerivativeOnUniv.leibniz ht hf,
      ContinuousMultilinearMap.map_update_add, ContinuousMultilinearMap.map_update_smul]
  · simp only [update_comm hji.symm, update_of_ne hji, hji, ↓reduceIte, add_zero,
      Pi.smul_apply']
    rw [ContinuousMultilinearMap.map_update_smul]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul 𝕜 (W x)] [Fintype ι] in
/-- Replacing the `i`-th section by `t + t'` in one term `A(s₁, …, ∇_v sⱼ, …, sₖ)` of the
evaluation rule gives the sum of the terms for `t` and `t'`. -/
private theorem apply_update_update_add [DecidableEq ι] {x : M}
    (Ax : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)) (s : ι → Π x : M, V x)
    {t t' : Π x : M, V x} (ht : MDiffAt (T% t) x) (ht' : MDiffAt (T% t') x) (i j : ι)
    (v : TangentSpace I x) :
    Ax (update (update (fun k ↦ s k x) i ((t + t') x)) j (covV (update s i (t + t') j) x v)) =
      Ax (update (update (fun k ↦ s k x) i (t x)) j (covV (update s i t j) x v)) +
        Ax (update (update (fun k ↦ s k x) i (t' x)) j (covV (update s i t' j) x v)) := by
  rcases eq_or_ne j i with rfl | hji
  · simp [covV.isCovariantDerivativeOnUniv.add ht ht', ContinuousMultilinearMap.map_update_add]
  · simp only [update_comm hji.symm, update_of_ne hji, Pi.add_apply]
    rw [ContinuousMultilinearMap.map_update_add]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
  [ContMDiffVectorBundle 1 F V I] in
/-- **The evaluation rule is tensorial in each slot.** For a differentiable section `A` and
differentiable sections `sⱼ`, the right-hand side of the evaluation rule is tensorial in the
`i`-th section. -/
private theorem tensorialAt_multilinearAux [DecidableEq ι]
    {A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)} {x : M}
    (hA : MDifferentiableAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G))
      (fun y ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V z) (W z)) y (A y)) x)
    {s : ι → Π x : M, V x} (hs : ∀ j, MDiffAt (T% (s j)) x) (i : ι) :
    TensorialAt I F (fun t ↦ multilinearAux covV covW A (update s i t) x) x := by
  -- Evaluating the family with its `i`-th section replaced replaces the `i`-th value.
  have update_apply_eq (t : Π x : M, V x) (y : M) :
      (fun j ↦ update s i t j y) = update (fun j ↦ s j y) i (t y) :=
    funext fun j ↦ apply_update (fun _ σ ↦ σ y) s i t j
  have hupd {t : Π x : M, V x} (ht : MDiffAt (T% t) x) :
      ∀ j, MDiffAt (T% (update s i t j)) x := fun j ↦ by
    rcases eq_or_ne j i with rfl | hji
    · simpa using ht
    · simpa [hji] using hs j
  have happ {t : Π x : M, V x} (ht : MDiffAt (T% t) x) :
      MDiffAt (T% (fun y ↦ A y (update (fun j ↦ s j y) i (t y)))) x := by
    simpa only [update_apply_eq] using hA.continuousMultilinearMap_bundle_apply (hupd ht)
  refine ⟨fun {f t} hf ht ↦ ?_, fun {t t'} ht ht' ↦ ?_⟩
  · ext v
    have hsmul : (fun y ↦ A y (update (fun j ↦ s j y) i ((f • t) y))) =
        f • fun y ↦ A y (update (fun j ↦ s j y) i (t y)) := by
      funext y
      simp [ContinuousMultilinearMap.map_update_smul]
    simp only [multilinearAux_apply, update_apply_eq, hsmul,
      covW.isCovariantDerivativeOnUniv.leibniz (happ ht) hf,
      apply_update_update_smul covV (A x) s hf ht, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, ← Finset.smul_sum,
      add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
    simp only [smul_sub]
    abel
  · ext v
    have hadd : (fun y ↦ A y (update (fun j ↦ s j y) i ((t + t') y))) =
        (fun y ↦ A y (update (fun j ↦ s j y) i (t y))) +
          fun y ↦ A y (update (fun j ↦ s j y) i (t' y)) := by
      funext y
      simp [ContinuousMultilinearMap.map_update_add]
    simp only [multilinearAux_apply, update_apply_eq, hadd,
      covW.isCovariantDerivativeOnUniv.add (happ ht) (happ ht'),
      apply_update_update_add covV (A x) s ht ht', Finset.sum_add_distrib,
      add_apply]
    abel

/-- **The evaluation rule only depends on the values of the sections.** -/
private theorem multilinearAux_congr
    {A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)} {x : M}
    (hA : MDifferentiableAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G))
      (fun y ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V z) (W z)) y (A y)) x)
    {s s' : ι → Π x : M, V x} (hs : ∀ j, MDiffAt (T% (s j)) x)
    (hs' : ∀ j, MDiffAt (T% (s' j)) x) (hss' : ∀ j, s j x = s' j x) :
    multilinearAux covV covW A s x = multilinearAux covV covW A s' x := by
  classical
  -- Replace the sections one slot at a time, along the finite set of replaced slots.
  have key (T : Finset ι) :
      multilinearAux covV covW A s x = multilinearAux covV covW A (T.piecewise s' s) x := by
    induction T using Finset.induction_on with
    | empty => simp
    | insert j T _ ih =>
      have hT : ∀ k, MDiffAt (T% (T.piecewise s' s k)) x := fun k ↦ by
        by_cases hk : k ∈ T
        · simpa [Finset.piecewise_eq_of_mem _ _ _ hk] using hs' k
        · simpa [Finset.piecewise_eq_of_notMem _ _ _ hk] using hs k
      rw [ih, Finset.piecewise_insert]
      conv_lhs => rw [← update_eq_self j (T.piecewise s' s)]
      refine (tensorialAt_multilinearAux covV covW hA hT j).pointwise (hT j) (hs' j) ?_
      by_cases hk : j ∈ T
      · simp [Finset.piecewise_eq_of_mem _ _ _ hk]
      · simp [Finset.piecewise_eq_of_notMem _ _ _ hk, hss' j]
  simpa using key Finset.univ

/-- The evaluation rule on extensions of fibre vectors is additive in each fibre vector. -/
private theorem multilinearAux_update_extend_add
    {A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)} {x : M}
    (hA : MDifferentiableAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G))
      (fun y ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V z) (W z)) y (A y)) x)
    [DecidableEq ι] (u : ι → V x) (i : ι) (a b : V x) :
    multilinearAux covV covW A
        (update (fun j ↦ FiberBundle.extend F (u j)) i (FiberBundle.extend F (a + b))) x =
      multilinearAux covV covW A
          (update (fun j ↦ FiberBundle.extend F (u j)) i (FiberBundle.extend F a)) x +
        multilinearAux covV covW A
          (update (fun j ↦ FiberBundle.extend F (u j)) i (FiberBundle.extend F b)) x := by
  have hT := tensorialAt_multilinearAux covV covW hA (fun j ↦ mdifferentiableAt_extend I F (u j)) i
  rw [hT.pointwise (mdifferentiableAt_extend I F (a + b)) (mdifferentiableAt_add_section
      (mdifferentiableAt_extend I F a) (mdifferentiableAt_extend I F b)) (by simp),
    hT.add (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)]

/-- The evaluation rule on extensions of fibre vectors is homogeneous in each fibre vector. -/
private theorem multilinearAux_update_extend_smul
    {A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)} {x : M}
    (hA : MDifferentiableAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G))
      (fun y ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V z) (W z)) y (A y)) x)
    [DecidableEq ι] (u : ι → V x) (i : ι) (c : 𝕜) (a : V x) :
    multilinearAux covV covW A
        (update (fun j ↦ FiberBundle.extend F (u j)) i (FiberBundle.extend F (c • a))) x =
      c • multilinearAux covV covW A
          (update (fun j ↦ FiberBundle.extend F (u j)) i (FiberBundle.extend F a)) x := by
  have hT := tensorialAt_multilinearAux covV covW hA (fun j ↦ mdifferentiableAt_extend I F (u j)) i
  let σ : Π y : M, V y := (fun _ : M ↦ c) • FiberBundle.extend F a
  have hσ : MDiffAt (T% σ) x :=
    mdifferentiableAt_const.smul_section (mdifferentiableAt_extend ..)
  rw [hT.pointwise (mdifferentiableAt_extend I F (c • a)) hσ (by simp [σ]),
    hT.smul mdifferentiableAt_const (mdifferentiableAt_extend ..)]

open scoped Classical in
/-- The value at `x` of the induced connection on a section `A`: the continuous linear map
`v ↦ ((s₁, …, sₖ) ↦ (∇_v A)(s₁, …, sₖ))` given by the evaluation rule, or zero where `A` is not
differentiable. Continuity in `v` is obtained on the normed model fibres. -/
private def multilinearValue (A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x))
    (x : M) : TangentSpace I x →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x) :=
  if hA : MDifferentiableAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G))
      (fun y ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V z) (W z)) y (A y)) x then
    let φ := VectorBundle.continuousLinearEquivAt 𝕜 F V x
    let ψ := VectorBundle.continuousLinearEquivAt 𝕜 G W x
    let L : MultilinearMap (RingHom.id 𝕜) (fun _ : ι ↦ F) (E →L[𝕜] G) :=
      { toFun u := ((ψ : W x →L[𝕜] G).comp
          (multilinearAux covV covW A (fun i ↦ FiberBundle.extend F (φ.symm (u i))) x) :
            E →L[𝕜] G)
        map_update_add' u i a b := by
          ext v
          simp only [extend_comp_update, map_add, multilinearAux_update_extend_add covV covW hA]
          -- The maps are typed on the model `E` but built on `TangentSpace I x`, so the
          -- application lemmas of `ContinuousLinearMap.comp` do not fire; the goal is
          -- `ψ ((f + g) v) = ψ (f v) + ψ (g v)` by definition.
          exact map_add (ψ : W x →L[𝕜] G) _ _
        map_update_smul' u i c a := by
          ext v
          simp only [extend_comp_update, map_smul, multilinearAux_update_extend_smul covV covW hA]
          -- As above, the goal is `ψ ((c • f) v) = c • ψ (f v)` by definition.
          exact map_smul (ψ : W x →L[𝕜] G) _ _ }
    let D : E →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G :=
      ContinuousMultilinearMap.flipLinear ⟨L, L.continuous_of_finiteDimensional⟩
    ((ψ.symm.continuousMultilinearMapCongrRight (fun _ : ι ↦ F)).trans
        (ContinuousLinearEquiv.continuousMultilinearMapCongrLeft (W x) fun _ ↦ φ) :
          ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G →L[𝕜] _).comp D
  else 0

private theorem multilinearValue_apply
    {A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)} {x : M}
    (hA : MDifferentiableAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G))
      (fun y ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V z) (W z)) y (A y)) x)
    {s : ι → Π x : M, V x} (hs : ∀ j, MDiffAt (T% (s j)) x)
    (v : TangentSpace I x) :
    multilinearValue covV covW A x v (fun i ↦ s i x) = multilinearAux covV covW A s x v := by
  simp only [multilinearValue, hA, ↓reduceDIte]
  -- The value is the composite of `flipLinear` with the transport `f ↦ ψ⁻¹ ∘ f ∘ φ` along the
  -- fibre trivializations; their application lemmas are stated over the model `E` rather than
  -- `TangentSpace I x`, so the evaluation is unfolded by `change` instead.
  change (VectorBundle.continuousLinearEquivAt 𝕜 G W x).symm
      ((VectorBundle.continuousLinearEquivAt 𝕜 G W x)
        (multilinearAux covV covW A (fun i ↦ FiberBundle.extend F
          ((VectorBundle.continuousLinearEquivAt 𝕜 F V x).symm
            ((VectorBundle.continuousLinearEquivAt 𝕜 F V x) (s i x)))) x v)) = _
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rw [multilinearAux_congr covV covW hA (fun i ↦ mdifferentiableAt_extend ..) hs (by simp)]

variable (ι) in
/-- **The connection induced on the bundle of continuous multilinear maps** `(V x)^ι → W x` by
connections on `V` and `W`. It is characterized on differentiable inputs by the evaluation rule
`(∇_v A)(s₁, …, sₖ) = ∇_v (A(s₁, …, sₖ)) - ∑ᵢ A(s₁, …, ∇_v sᵢ, …, sₖ)`
(`CovariantDerivative.continuousMultilinearMap_apply`). -/
def continuousMultilinearMap :
    CovariantDerivative I (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
      (fun x ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)) where
  toFun := multilinearValue covV covW
  isCovariantDerivativeOnUniv := {
    add := by
      classical
      intro A B x hA hB _
      ext v u
      let s : ι → Π y : M, V y := fun i ↦ FiberBundle.extend F (u i)
      have hs : ∀ i, MDiffAt (T% (s i)) x := fun i ↦ mdifferentiableAt_extend ..
      have heq : (fun i ↦ s i x) = u := funext fun i ↦ extend_apply_self ..
      have hcov : covW (fun y ↦ (A + B) y (fun i ↦ s i y)) x =
          covW (fun y ↦ A y (fun i ↦ s i y)) x + covW (fun y ↦ B y (fun i ↦ s i y)) x :=
        covW.isCovariantDerivativeOnUniv.add (hA.continuousMultilinearMap_bundle_apply hs)
          (hB.continuousMultilinearMap_bundle_apply hs)
      rw [← heq]
      simp only [add_apply]
      rw [multilinearValue_apply covV covW (mdifferentiableAt_add_section hA hB) hs,
        multilinearValue_apply covV covW hA hs, multilinearValue_apply covV covW hB hs,
        multilinearAux_apply, multilinearAux_apply, multilinearAux_apply, hcov]
      simp only [add_apply, Pi.add_apply, Finset.sum_add_distrib]
      abel
    leibniz := by
      classical
      intro A f x hA hf _
      ext v u
      let s : ι → Π y : M, V y := fun i ↦ FiberBundle.extend F (u i)
      have hs : ∀ i, MDiffAt (T% (s i)) x := fun i ↦ mdifferentiableAt_extend ..
      have heq : (fun i ↦ s i x) = u := funext fun i ↦ extend_apply_self ..
      have hcov : covW (fun y ↦ (f • A) y (fun i ↦ s i y)) x =
          f x • covW (fun y ↦ A y (fun i ↦ s i y)) x +
            (d% f x).smulRight (A x (fun i ↦ s i x)) :=
        covW.isCovariantDerivativeOnUniv.leibniz (hA.continuousMultilinearMap_bundle_apply hs) hf
      rw [← heq]
      simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
      rw [multilinearValue_apply covV covW (hf.smul_section hA) hs,
        multilinearValue_apply covV covW hA hs, multilinearAux_apply, multilinearAux_apply, hcov]
      simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, Pi.smul_apply',
        ← Finset.smul_sum, smul_sub]
      abel }

/-- **The evaluation rule of the induced connection.** For a differentiable section `A` of the
bundle of continuous multilinear maps and differentiable sections `sᵢ` of `V`,
`(∇_v A)(s₁, …, sₖ) = ∇_v (A(s₁, …, sₖ)) - ∑ᵢ A(s₁, …, ∇_v sᵢ, …, sₖ)`. -/
theorem continuousMultilinearMap_apply [DecidableEq ι]
    {A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)} {x : M}
    (hA : MDifferentiableAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G))
      (fun y ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V z) (W z)) y (A y)) x)
    {s : ι → Π x : M, V x} (hs : ∀ i, MDiffAt (T% (s i)) x)
    (v : TangentSpace I x) :
    covV.continuousMultilinearMap ι covW A x v (fun i ↦ s i x) =
      covW (fun y ↦ A y (fun i ↦ s i y)) x v -
        ∑ i, A x (update (fun j ↦ s j x) i (covV (s i) x v)) := by
  rw [← multilinearAux_apply]
  exact multilinearValue_apply covV covW hA hs v

/-- **Leibniz rule for a multilinear map applied to sections.** For a differentiable section `A`
of the bundle of continuous multilinear maps and differentiable sections `sᵢ` of `V`,
`∇_v (A(s₁, …, sₖ)) = (∇_v A)(s₁, …, sₖ) + ∑ᵢ A(s₁, …, ∇_v sᵢ, …, sₖ)`. -/
theorem covariantDerivative_continuousMultilinearMap_apply [DecidableEq ι]
    {A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)} {x : M}
    (hA : MDifferentiableAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G))
      (fun y ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V z) (W z)) y (A y)) x)
    {s : ι → Π x : M, V x} (hs : ∀ i, MDiffAt (T% (s i)) x)
    (v : TangentSpace I x) :
    covW (fun y ↦ A y (fun i ↦ s i y)) x v =
      covV.continuousMultilinearMap ι covW A x v (fun i ↦ s i x) +
        ∑ i, A x (update (fun j ↦ s j x) i (covV (s i) x v)) := by
  rw [continuousMultilinearMap_apply covV covW hA hs v, sub_add_cancel]

/-- Evaluate the induced connection on fibre vectors through their local extensions. -/
theorem continuousMultilinearMap_apply_eq_extend [DecidableEq ι]
    {A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)} {x : M}
    (hA : MDifferentiableAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G))
      (fun y ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V z) (W z)) y (A y)) x)
    (v : TangentSpace I x) (u : ι → V x) :
    covV.continuousMultilinearMap ι covW A x v u =
      covW (fun y ↦ A y (fun i ↦ FiberBundle.extend F (u i) y)) x v -
        ∑ i, A x (update u i (covV (FiberBundle.extend F (u i)) x v)) := by
  simpa using continuousMultilinearMap_apply covV covW hA
    (s := fun i ↦ FiberBundle.extend F (u i)) (fun i ↦ mdifferentiableAt_extend ..) v

/-- At a nondifferentiable section the induced connection uses the zero extension. -/
@[simp] theorem continuousMultilinearMap_eq_zero_of_not_mdifferentiableAt
    {A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)} {x : M}
    (hA : ¬ MDifferentiableAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G))
      (fun y ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V z) (W z)) y (A y)) x) :
    covV.continuousMultilinearMap ι covW A x = 0 := by
  simp [continuousMultilinearMap, multilinearValue, hA]

/-- The evaluation rule uniquely determines the covariant derivative of a differentiable section
of the bundle of continuous multilinear maps at a point. -/
theorem continuousMultilinearMap_eq_of_apply [DecidableEq ι]
    {A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)} {x : M}
    (hA : MDifferentiableAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G))
      (fun y ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V z) (W z)) y (A y)) x)
    (D : TangentSpace I x →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x))
    (hD : ∀ s : ι → Π x : M, V x, (∀ i, MDiffAt (T% (s i)) x) → ∀ v : TangentSpace I x,
      D v (fun i ↦ s i x) = covW (fun y ↦ A y (fun i ↦ s i y)) x v -
        ∑ i, A x (update (fun j ↦ s j x) i (covV (s i) x v))) :
    D = covV.continuousMultilinearMap ι covW A x := by
  ext v u
  have hs : ∀ i, MDiffAt (T% (FiberBundle.extend F (u i))) x := fun i ↦
    mdifferentiableAt_extend ..
  simpa using (hD _ hs v).trans (continuousMultilinearMap_apply covV covW hA hs v).symm

section Difference

variable [FiniteDimensional 𝕜 G] [ContMDiffVectorBundle 1 G W I]

/-- **Changing the connections changes the induced connection by the difference tensors.** For a
differentiable section `A`, replacing `covV` and `covW` by `covV'` and `covW'` changes
`(∇_v A)(u₁, …, uₖ)` by `Δ_W(A(u₁, …, uₖ), v) - ∑ᵢ A(u₁, …, Δ_V(uᵢ, v), …, uₖ)`, where
`Δ_V` and `Δ_W`
are the difference tensors `CovariantDerivative.difference` of the two pairs of connections. -/
theorem continuousMultilinearMap_apply_sub_continuousMultilinearMap_apply [DecidableEq ι]
    (covV' : CovariantDerivative I F V) (covW' : CovariantDerivative I G W)
    {A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)} {x : M}
    (hA : MDifferentiableAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G))
      (fun y ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V z) (W z)) y (A y)) x)
    (v : TangentSpace I x) (u : ι → V x) :
    covV.continuousMultilinearMap ι covW A x v u -
        covV'.continuousMultilinearMap ι covW' A x v u =
      covW.difference covW' x (A x u) v -
        ∑ i, A x (update u i (covV.difference covV' x (u i) v)) := by
  have hs : ∀ i, MDiffAt (T% (FiberBundle.extend F (u i))) x := fun i ↦
    mdifferentiableAt_extend ..
  have hW := covW.difference_apply covW' (hA.continuousMultilinearMap_bundle_apply hs)
  have hV (i : ι) := covV.difference_apply covV' (hs i)
  simp only [extend_apply_self] at hW hV
  rw [continuousMultilinearMap_apply_eq_extend covV covW hA,
    continuousMultilinearMap_apply_eq_extend covV' covW' hA, hW]
  simp only [hV, sub_apply, ContinuousMultilinearMap.map_update_sub, Finset.sum_sub_distrib]
  abel

end Difference

end General

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul ℝ (W x)] [FiberBundle G W] [VectorBundle ℝ G W]
  [ContMDiffVectorBundle ∞ G W I]
  {ι : Type*} [Fintype ι]
  (covV : CovariantDerivative I F V) (covW : CovariantDerivative I G W)
  [ContMDiffCovariantDerivative covV ∞] [ContMDiffCovariantDerivative covW ∞]

/-- **The covariant derivative of a smooth section of the bundle of continuous multilinear maps is
smooth**, as a section of `Hom(TM, Mult^ι(V, W))`. Smoothness of the connections on `V` and `W`
suffices. -/
theorem contMDiff_continuousMultilinearMap
    {A : Π x : M, ContinuousMultilinearMap ℝ (fun _ : ι ↦ V x) (W x)}
    (hA : ContMDiff I (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : ι ↦ F) G)) ∞
      (fun x ↦ TotalSpace.mk' (ContinuousMultilinearMap ℝ (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap ℝ (fun _ : ι ↦ V z) (W z)) x (A x))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : ι ↦ F) G)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : ι ↦ F) G)
        (E := fun y ↦ TangentSpace I y →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : ι ↦ V y) (W y))
        x (covV.continuousMultilinearMap ι covW A x)) := by
  classical
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro X hX
  apply (TauCeti.Manifold.contMDiff_continuousMultilinearMap_iff _).2
  intro s hs
  -- The `i`-th family: `s` with its `i`-th section replaced by `∇_X sᵢ`.
  have hupd (i : ι) : ∀ j, CMDiff ∞ (T% (update s i (fun y ↦ covV (s i) y (X y)) j)) := by
    intro j
    rcases eq_or_ne j i with rfl | hji
    · simpa using covV.contMDiff_apply hX (by simpa using hs j)
    · simpa [hji] using hs j
  have hW := covW.contMDiff_apply hX (by simpa using hA.continuousMultilinearMap_bundle_apply hs)
  have hsum : CMDiff ∞ (T% (fun y ↦ ∑ i, A y (fun j ↦
      update s i (fun z ↦ covV (s i) z (X z)) j y))) :=
    ContMDiff.sum_section fun i _ ↦ hA.continuousMultilinearMap_bundle_apply (hupd i)
  refine (hW.sub_section hsum).congr fun x ↦ ?_
  have heq (i : ι) : (fun j ↦ update s i (fun z ↦ covV (s i) z (X z)) j x) =
      update (fun j ↦ s j x) i (covV (s i) x (X x)) := by
    funext j
    exact apply_update (fun _ σ ↦ σ x) s i _ j
  simp only [Pi.sub_apply, heq]
  exact congrArg (TotalSpace.mk' G x) (continuousMultilinearMap_apply covV covW
    (hA.mdifferentiableAt (by simp)) (fun i ↦ (hs i).mdifferentiableAt (by simp)) (X x))

/-- Smooth connections induce a smooth connection on the bundle of continuous multilinear maps. -/
instance : ContMDiffCovariantDerivative (covV.continuousMultilinearMap ι covW) ∞ where
  contMDiff.contMDiff {A} hA := by
    rw [contMDiffOn_univ] at hA ⊢
    exact contMDiff_continuousMultilinearMap covV covW (by simpa using hA)

end Smooth

end CovariantDerivative
