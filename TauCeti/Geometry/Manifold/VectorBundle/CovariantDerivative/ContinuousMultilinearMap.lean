/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.ContinuousMultilinearMap
public import TauCeti.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# The induced connection on a bundle of continuous multilinear maps

Let `V` and `W` be vector bundles over a manifold `M`, with `V` of finite rank, and `ι` a finite
index type. Connections on `V` and `W` induce a connection on the bundle with fibres
`ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)`
(`TauCeti.Geometry.Manifold.VectorBundle.ContinuousMultilinearMap`), the bundle
`(V*)^{⊗ι} ⊗ W` in multilinear form. Its evaluation rule is the Leibniz rule

`((∇_v A)(s₁, …, sₖ)) = ∇_v (A(s₁, …, sₖ)) - ∑ᵢ A(s₁, …, ∇_v sᵢ, …, sₖ)`,

which determines the induced connection on differentiable sections
(`CovariantDerivative.continuousMultilinearMap_apply`,
`CovariantDerivative.continuousMultilinearMap_eq_of_apply`). Changing the connections on `V` and
`W` changes it by their difference tensors
(`CovariantDerivative.continuousMultilinearMap_apply_sub_continuousMultilinearMap_apply`).
Smooth connections induce a smooth connection
(`CovariantDerivative.contMDiff_continuousMultilinearMap`).

For `ι = Fin j` and `V = TM` this is the connection on `j`-fold covariant tensors with values in
`W`, so that iterated covariant derivatives `∇ʲσ` of a section `σ` of `W` live in one bundle
family indexed uniformly by `j`; iterating the native Hom-bundle connection
(`CovariantDerivative.hom`) cannot provide this, because the typeclass instances of iterated Hom
bundles cannot be produced by recursion on `j`.

The right side of the evaluation rule is tensorial in each `sᵢ`, so it defines a multilinear
map on the fibre (`TensorialAt.mkMultilinear`). The base is finite-dimensional, so that this
fibrewise map is continuous in the tangent vector `v`. At a point where `A` is not
differentiable the operator is defined to be zero, since the axioms of a native covariant
derivative concern differentiable inputs.

The convention follows J. M. Lee, *Introduction to Riemannian Manifolds*, second edition,
Chapter 4 (connections on tensor bundles).
-/

public section

open Bundle FiberBundle
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

/-- Evaluating a family of sections, one of which is replaced, at a point. -/
private theorem apply_update_apply {M ι : Type*} [DecidableEq ι] {V : M → Type*}
    (σ : ι → Π x : M, V x) (i : ι) (τ : Π x : M, V x) (y : M) :
    (fun j ↦ Function.update σ i τ j y) = Function.update (fun j ↦ σ j y) i (τ y) :=
  funext fun j ↦ Function.apply_update (fun _ s ↦ s y) σ i τ j

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
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
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (covV : CovariantDerivative I F V) (covW : CovariantDerivative I G W)

/-- The right side of the evaluation rule, on a family of sections. -/
private def multilinearAux (A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x))
    (x : M) (v : TangentSpace I x) (s : ι → Π x : M, V x) : W x :=
  covW (fun y ↦ A y (fun i ↦ s i y)) x v -
    ∑ i, A x (Function.update (fun j ↦ s j x) i (covV (s i) x v))

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I] [VectorBundle 𝕜 G W] in
/-- The right side of the evaluation rule, with the dependence on one argument isolated. -/
private theorem multilinearAux_update
    (A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)) (x : M)
    (v : TangentSpace I x) (σ : ι → Π x : M, V x) (i : ι) (τ : Π x : M, V x) :
    multilinearAux covV covW A x v (Function.update σ i τ) =
      covW (fun y ↦ A y (Function.update (fun j ↦ σ j y) i (τ y))) x v -
        A x (Function.update (fun j ↦ σ j x) i (covV τ x v)) -
        ∑ j ∈ Finset.univ.erase i,
          A x (Function.update (Function.update (fun k ↦ σ k x) j (covV (σ j) x v)) i (τ x)) := by
  rw [multilinearAux, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), sub_add_eq_sub_sub]
  simp only [apply_update_apply, Function.update_self, Function.update_idem]
  congr 1
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  rw [Function.update_of_ne hji, Function.update_comm hji.symm]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  [ContMDiffVectorBundle 1 F V I] in
/-- The right side of the evaluation rule is tensorial in each argument. -/
private theorem tensorialAt_multilinearAux
    {A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)} {x : M}
    (hA : MDifferentiableAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G))
      (fun y ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V z) (W z)) y (A y)) x)
    (v : TangentSpace I x) (σ : ι → Π x : M, V x) (hσ : ∀ i, MDiffAt (T% (σ i)) x) (i : ι) :
    TensorialAt I F (fun τ ↦ multilinearAux covV covW A x v (Function.update σ i τ)) x := by
  have hupd {τ : Π x : M, V x} (hτ : MDiffAt (T% τ) x) :
      ∀ j, MDiffAt (T% (Function.update σ i τ j)) x :=
    (Function.forall_update_iff σ fun _ s ↦ MDiffAt (T% s) x).2 ⟨hτ, fun j _ ↦ hσ j⟩
  have hev {τ : Π x : M, V x} (hτ : MDiffAt (T% τ) x) :
      MDiffAt (fun y ↦ TotalSpace.mk' G y
        (A y (Function.update (fun j ↦ σ j y) i (τ y)))) x := by
    simpa only [apply_update_apply] using hA.continuousMultilinearMap_bundle_apply (hupd hτ)
  refine ⟨fun {f τ} hf hτ ↦ ?_, fun {τ τ'} hτ hτ' ↦ ?_⟩
  · simp only [multilinearAux_update]
    have hsmul : (fun y ↦ A y (Function.update (fun j ↦ σ j y) i ((f • τ) y))) =
        f • fun y ↦ A y (Function.update (fun j ↦ σ j y) i (τ y)) := by
      ext y
      simp [ContinuousMultilinearMap.map_update_smul]
    rw [hsmul, covW.isCovariantDerivativeOnUniv.leibniz (hev hτ) hf,
      covV.isCovariantDerivativeOnUniv.leibniz hτ hf]
    simp only [add_apply, smul_apply, Pi.smul_apply', ContinuousLinearMap.smulRight_apply,
      ContinuousMultilinearMap.map_update_add, ContinuousMultilinearMap.map_update_smul, smul_sub,
      Finset.smul_sum]
    abel
  · simp only [multilinearAux_update]
    have hadd : (fun y ↦ A y (Function.update (fun j ↦ σ j y) i ((τ + τ') y))) =
        (fun y ↦ A y (Function.update (fun j ↦ σ j y) i (τ y))) +
          fun y ↦ A y (Function.update (fun j ↦ σ j y) i (τ' y)) := by
      ext y
      simp [ContinuousMultilinearMap.map_update_add]
    rw [hadd, covW.isCovariantDerivativeOnUniv.add (hev hτ) (hev hτ'),
      covV.isCovariantDerivativeOnUniv.add hτ hτ']
    simp only [add_apply, Pi.add_apply,
      ContinuousMultilinearMap.map_update_add, Finset.sum_add_distrib]
    abel

open scoped Classical in
/-- The value at `x` of the induced connection, as a map on tangent vectors. -/
private def multilinearValue (A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x))
    (x : M) : TangentSpace I x →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x) :=
  haveI : FiniteDimensional 𝕜 (TangentSpace I x) := inferInstanceAs (FiniteDimensional 𝕜 E)
  if hA : MDifferentiableAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G))
      (fun y ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V z) (W z)) y (A y)) x then
    LinearMap.toContinuousLinearMap
      { toFun v := TensorialAt.mkMultilinear (multilinearAux covV covW A x v) x
          (tensorialAt_multilinearAux covV covW hA v)
        map_add' v v' := by
          ext u
          simp only [TensorialAt.mkMultilinear_apply_eq_extend, multilinearAux, map_add,
            add_apply, ContinuousMultilinearMap.map_update_add,
            Finset.sum_add_distrib]
          abel
        map_smul' c v := by
          ext u
          simp only [TensorialAt.mkMultilinear_apply_eq_extend, multilinearAux, map_smul,
            smul_apply, ContinuousMultilinearMap.map_update_smul,
            RingHom.id_apply, smul_sub, Finset.smul_sum] }
  else 0

private theorem multilinearValue_apply
    {A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)} {x : M}
    (hA : MDifferentiableAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G))
      (fun y ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V z) (W z)) y (A y)) x)
    {s : ι → Π x : M, V x} (hs : ∀ i, MDiffAt (T% (s i)) x) (v : TangentSpace I x) :
    multilinearValue covV covW A x v (fun i ↦ s i x) =
      covW (fun y ↦ A y (fun i ↦ s i y)) x v -
        ∑ i, A x (Function.update (fun j ↦ s j x) i (covV (s i) x v)) := by
  simp only [multilinearValue, dite_eq_left hA, LinearMap.coe_toContinuousLinearMap',
    LinearMap.coe_mk, AddHom.coe_mk]
  exact TensorialAt.mkMultilinear_apply _ hs

/-- `multilinearValue_apply` on fibre vectors, through their local extensions. -/
private theorem multilinearValue_apply_eq_extend
    {A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)} {x : M}
    (hA : MDifferentiableAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G))
      (fun y ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V z) (W z)) y (A y)) x)
    (v : TangentSpace I x) (u : ι → V x) :
    multilinearValue covV covW A x v u =
      covW (fun y ↦ A y (fun i ↦ extend F (u i) y)) x v -
        ∑ i, A x (Function.update u i (covV (extend F (u i)) x v)) := by
  simpa using multilinearValue_apply covV covW hA
    (s := fun i ↦ extend F (u i)) (fun _ ↦ mdifferentiableAt_extend ..) v

/-- The connection on the bundle of continuous multilinear maps `(V x)^ι → W x` induced by
connections on `V` and `W`. It is characterized on differentiable inputs by the Leibniz rule
`(∇_v A)(s₁, …, sₖ) = ∇_v (A(s₁, …, sₖ)) - ∑ᵢ A(s₁, …, ∇_v sᵢ, …, sₖ)`
(`CovariantDerivative.continuousMultilinearMap_apply`). -/
def continuousMultilinearMap :
    CovariantDerivative I (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
      (fun x ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)) where
  toFun := multilinearValue covV covW
  isCovariantDerivativeOnUniv := {
    add := by
      intro A B x hA hB _
      ext v u
      have hs (i : ι) : MDiffAt (T% (extend F (u i))) x := mdifferentiableAt_extend ..
      have hsum : (fun y ↦ (A + B) y (fun i ↦ extend F (u i) y)) =
          (fun y ↦ A y (fun i ↦ extend F (u i) y)) + fun y ↦ B y (fun i ↦ extend F (u i) y) := by
        ext y
        simp
      simp only [add_apply,
        multilinearValue_apply_eq_extend covV covW (mdifferentiableAt_add_section hA hB),
        multilinearValue_apply_eq_extend covV covW hA,
        multilinearValue_apply_eq_extend covV covW hB, hsum,
        covW.isCovariantDerivativeOnUniv.add (hA.continuousMultilinearMap_bundle_apply hs)
          (hB.continuousMultilinearMap_bundle_apply hs)]
      simp only [Pi.add_apply, add_apply, Finset.sum_add_distrib]
      abel
    leibniz := by
      intro A f x hA hf _
      ext v u
      have hs (i : ι) : MDiffAt (T% (extend F (u i))) x := mdifferentiableAt_extend ..
      have hsmul : (fun y ↦ (f • A) y (fun i ↦ extend F (u i) y)) =
          f • fun y ↦ A y (fun i ↦ extend F (u i) y) := by
        ext y
        simp
      rw [multilinearValue_apply_eq_extend covV covW (hf.smul_section hA), hsmul,
        covW.isCovariantDerivativeOnUniv.leibniz (hA.continuousMultilinearMap_bundle_apply hs) hf]
      simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
        multilinearValue_apply_eq_extend covV covW hA, Pi.smul_apply', smul_sub, Finset.smul_sum,
        extend_apply_self]
      abel }

/-- **Evaluation of the induced connection** on a differentiable section `A` of the bundle of
continuous multilinear maps and differentiable sections `sᵢ`:
`(∇_v A)(s₁, …, sₖ) = ∇_v (A(s₁, …, sₖ)) - ∑ᵢ A(s₁, …, ∇_v sᵢ, …, sₖ)`. -/
theorem continuousMultilinearMap_apply
    {A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)} {x : M}
    (hA : MDifferentiableAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G))
      (fun y ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V z) (W z)) y (A y)) x)
    {s : ι → Π x : M, V x} (hs : ∀ i, MDiffAt (T% (s i)) x) (v : TangentSpace I x) :
    covV.continuousMultilinearMap covW A x v (fun i ↦ s i x) =
      covW (fun y ↦ A y (fun i ↦ s i y)) x v -
        ∑ i, A x (Function.update (fun j ↦ s j x) i (covV (s i) x v)) :=
  multilinearValue_apply covV covW hA hs v

/-- **Leibniz rule for a multilinear map applied to sections.** For a differentiable section `A`
of the bundle of continuous multilinear maps and differentiable sections `sᵢ`,
`∇_v (A(s₁, …, sₖ)) = (∇_v A)(s₁, …, sₖ) + ∑ᵢ A(s₁, …, ∇_v sᵢ, …, sₖ)`. -/
theorem covariantDerivative_continuousMultilinearMap_apply
    {A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)} {x : M}
    (hA : MDifferentiableAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G))
      (fun y ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V z) (W z)) y (A y)) x)
    {s : ι → Π x : M, V x} (hs : ∀ i, MDiffAt (T% (s i)) x) (v : TangentSpace I x) :
    covW (fun y ↦ A y (fun i ↦ s i y)) x v =
      covV.continuousMultilinearMap covW A x v (fun i ↦ s i x) +
        ∑ i, A x (Function.update (fun j ↦ s j x) i (covV (s i) x v)) := by
  rw [continuousMultilinearMap_apply covV covW hA hs v, sub_add_cancel]

/-- Evaluate the induced connection on fibre vectors using their local extensions. -/
theorem continuousMultilinearMap_apply_eq_extend
    {A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)} {x : M}
    (hA : MDifferentiableAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G))
      (fun y ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V z) (W z)) y (A y)) x)
    (v : TangentSpace I x) (u : ι → V x) :
    covV.continuousMultilinearMap covW A x v u =
      covW (fun y ↦ A y (fun i ↦ extend F (u i) y)) x v -
        ∑ i, A x (Function.update u i (covV (extend F (u i)) x v)) :=
  multilinearValue_apply_eq_extend covV covW hA v u

/-- At a nondifferentiable section the induced connection uses the zero extension. -/
@[simp] theorem continuousMultilinearMap_eq_zero_of_not_mdifferentiableAt
    {A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)} {x : M}
    (hA : ¬ MDifferentiableAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G))
      (fun y ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V z) (W z)) y (A y)) x) :
    covV.continuousMultilinearMap covW A x = 0 := by
  simp [continuousMultilinearMap, multilinearValue, hA]

/-- The evaluation rule uniquely determines the covariant derivative of a differentiable section
of the bundle of continuous multilinear maps at a point. -/
theorem continuousMultilinearMap_eq_of_apply
    {A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)} {x : M}
    (hA : MDifferentiableAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G))
      (fun y ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V z) (W z)) y (A y)) x)
    (D : TangentSpace I x →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x))
    (hD : ∀ s : ι → Π x : M, V x, (∀ i, MDiffAt (T% (s i)) x) → ∀ v : TangentSpace I x,
      D v (fun i ↦ s i x) = covW (fun y ↦ A y (fun i ↦ s i y)) x v -
        ∑ i, A x (Function.update (fun j ↦ s j x) i (covV (s i) x v))) :
    D = covV.continuousMultilinearMap covW A x := by
  ext v u
  have hs (i : ι) : MDiffAt (T% (extend F (u i))) x := mdifferentiableAt_extend ..
  simpa using (hD _ hs v).trans (continuousMultilinearMap_apply covV covW hA hs v).symm

section Difference

variable [FiniteDimensional 𝕜 G] [ContMDiffVectorBundle 1 G W I]

/-- **Changing the connections changes the induced connection by the difference tensors.**
For a differentiable section `A`, replacing `covV` and `covW` by `covV'` and `covW'` changes
`(∇_v A)(u₁, …, uₖ)` by `Δ_W(A(u), v) - ∑ᵢ A(u₁, …, Δ_V(uᵢ, v), …, uₖ)`, where `Δ_V` and `Δ_W`
are the difference tensors `CovariantDerivative.difference` of the two pairs of connections. -/
theorem continuousMultilinearMap_apply_sub_continuousMultilinearMap_apply
    (covV' : CovariantDerivative I F V) (covW' : CovariantDerivative I G W)
    {A : Π x : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)} {x : M}
    (hA : MDifferentiableAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G))
      (fun y ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V z) (W z)) y (A y)) x)
    (v : TangentSpace I x) (u : ι → V x) :
    covV.continuousMultilinearMap covW A x v u -
        covV'.continuousMultilinearMap covW' A x v u =
      covW.difference covW' x (A x u) v -
        ∑ i, A x (Function.update u i (covV.difference covV' x (u i) v)) := by
  have hs (i : ι) : MDiffAt (T% (extend F (u i))) x := mdifferentiableAt_extend ..
  rw [continuousMultilinearMap_apply_eq_extend covV covW hA,
    continuousMultilinearMap_apply_eq_extend covV' covW' hA]
  have hW := covW.difference_apply covW' (hA.continuousMultilinearMap_bundle_apply hs) (x := x)
  simp only [extend_apply_self] at hW
  simp only [hW, covV.difference_apply_eq_extend covV', sub_apply,
    ContinuousMultilinearMap.map_update_sub, Finset.sum_sub_distrib]
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
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (covV : CovariantDerivative I F V) (covW : CovariantDerivative I G W)
  [ContMDiffCovariantDerivative covV ∞] [ContMDiffCovariantDerivative covW ∞]

/-- The covariant derivative of a smooth section of the bundle of continuous multilinear maps is
a smooth section of `Hom(TM, ContinuousMultilinearMap (V^ι) W)`. Smoothness of the original
connections suffices. -/
theorem contMDiff_continuousMultilinearMap
    {A : Π x : M, ContinuousMultilinearMap ℝ (fun _ : ι ↦ V x) (W x)}
    (hA : ContMDiff I (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : ι ↦ F) G)) ∞
      (fun x ↦ TotalSpace.mk' (ContinuousMultilinearMap ℝ (fun _ : ι ↦ F) G)
        (E := fun y ↦ ContinuousMultilinearMap ℝ (fun _ : ι ↦ V y) (W y)) x (A x))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : ι ↦ F) G)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : ι ↦ F) G)
        (E := fun y ↦ TangentSpace I y →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : ι ↦ V y) (W y))
        x (covV.continuousMultilinearMap covW A x)) := by
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro X hX
  apply (TauCeti.Manifold.contMDiff_continuousMultilinearMap_iff _).2
  intro s hs
  have hW := covW.contMDiff_apply hX (by simpa using hA.continuousMultilinearMap_bundle_apply hs)
  have hV (i : ι) := covV.contMDiff_apply hX (by simpa using hs i)
  -- Each term `A(s₁, …, ∇_X sᵢ, …, sₖ)` of the evaluation rule is smooth.
  have hterm (i : ι) : ContMDiff I (I.prod 𝓘(ℝ, G)) ∞ (fun x ↦ TotalSpace.mk' G x
      (A x (Function.update (fun j ↦ s j x) i (covV (s i) x (X x))))) := by
    simpa only [apply_update_apply] using hA.continuousMultilinearMap_bundle_apply
      ((Function.forall_update_iff s fun _ t ↦ CMDiff ∞ (T% t)).2 ⟨hV i, fun j _ ↦ hs j⟩)
  have hsum := ContMDiff.sum_section (s := Finset.univ)
    (t := fun i x ↦ A x (Function.update (fun j ↦ s j x) i (covV (s i) x (X x))))
    fun i _ ↦ hterm i
  refine (hW.sub_section hsum).congr fun x ↦ ?_
  exact congrArg (TotalSpace.mk' G x) (continuousMultilinearMap_apply covV covW
    (hA.mdifferentiableAt (by simp)) (fun i ↦ (hs i).mdifferentiableAt (by simp)) (X x))

/-- Smooth connections induce a smooth connection on the bundle of continuous multilinear
maps. -/
instance : ContMDiffCovariantDerivative (covV.continuousMultilinearMap covW (ι := ι)) ∞ where
  contMDiff.contMDiff {A} hA := by
    rw [contMDiffOn_univ] at hA ⊢
    exact contMDiff_continuousMultilinearMap covV covW (by simpa using hA)

end Smooth

end CovariantDerivative
