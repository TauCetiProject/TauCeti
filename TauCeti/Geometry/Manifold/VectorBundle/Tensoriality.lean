/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Tensoriality of globally `C^n` operations

This file complements Mathlib's pointwise tensoriality API with a criterion for operations whose
additivity and `C^n`-function linearity laws are available for globally `C^n` sections.
The criterion applies to finite-rank `C^n` real vector bundles (`n ≤ ∞`) over
finite-dimensional Hausdorff `C^n` manifolds; on a trivial bundle the constant sections form a
global frame, and no hypothesis on the base is needed. The target only needs addition and scalar
multiplication; no algebraic laws on these operations are required beyond the stated laws for the
section operation.

## Main results

* `TauCeti.Manifold.eq_of_contMDiff_smul_of_eventuallyEq`: `C^n`-function linearity (`n ≤ ∞`)
  implies locality.
* `TauCeti.Manifold.eq_of_contMDiff_tensorial`: an operation satisfying these laws for `n ≤ ∞`
  has equal values on globally `C^n` sections which agree at the point of evaluation.
* `TauCeti.Manifold.eq_zero_of_contMDiff_tensorial_of_const`: on the trivial bundle with
  finite-dimensional fibre, an operation satisfying these laws and vanishing on constant sections
  vanishes, over any base.

It also extends Mathlib's two-argument criterion `TensorialAt.mkHom₂` to operations on families
of sections indexed by a finite type `ι`, as needed for tensors with several arguments:

* `TensorialAt.pointwise_pi`: an operation which is tensorial at `x` in each argument, while the
  other arguments are differentiable at `x`, depends only on the values of the arguments at `x`.
* `TensorialAt.mkMultilinear`: such an operation is a continuous multilinear map on the fibre at
  `x`, with evaluation rule `TensorialAt.mkMultilinear_apply`.
-/

public section

open Bundle FiberBundle Module
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

/-- An operation on sections which is additive on globally `C^n` sections takes equal values on
two finite sums of globally `C^n` sections whenever it takes equal values on the summands.  The
target needs only an addition, without any algebraic laws. -/
theorem map_sum_eq_of_contMDiff_additive
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
    [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [∀ x, TopologicalSpace (W x)]
    [FiberBundle G W] [VectorBundle 𝕜 G W]
    {A : Type*} [Add A] (Φ : (Π x : M, W x) → A)
    (hadd : ∀ {s s' : Π x : M, W x}, CMDiff n (T% s) → CMDiff n (T% s') →
      Φ (s + s') = Φ s + Φ s')
    {ι : Type*} (q : Finset ι) (u v : ι → Π x : M, W x)
    (hu : ∀ i ∈ q, CMDiff n (T% (u i))) (hv : ∀ i ∈ q, CMDiff n (T% (v i)))
    (huv : ∀ i ∈ q, Φ (u i) = Φ (v i)) :
    Φ (∑ i ∈ q, u i) = Φ (∑ i ∈ q, v i) := by
  classical
  induction q using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]
  | @insert i q hi ih =>
      rw [Finset.forall_mem_insert] at hu hv huv
      -- Partial sums of globally `C^n` sections are globally `C^n`.
      have hsum {w : ι → Π x : M, W x} (hw : ∀ j ∈ q, CMDiff n (T% (w j))) :
          CMDiff n (T% (∑ j ∈ q, w j)) := by
        simpa only [Finset.sum_apply] using ContMDiff.sum_section hw
      simp only [Finset.sum_insert hi]
      rw [hadd hu.1 (hsum hu.2), hadd hv.1 (hsum hv.2), huv.1, ih hu.2 hv.2 huv.2]

/-- An operation on smooth `F`-valued functions on `M` which is additive and linear over smooth
functions vanishes on every smooth function as soon as it vanishes on the constant functions: the
constant functions given by a basis of `F` form a global frame of the trivial bundle `M × F`.
Unlike `TauCeti.Manifold.eq_of_contMDiff_tensorial`, this needs no Hausdorff or
finite-dimensionality hypothesis on `M`. -/
theorem eq_zero_of_contMDiff_tensorial_of_const
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {n : ℕ∞ω}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {W : M → Type*} [∀ x, AddCommMonoid (W x)] [∀ x, Module 𝕜 (W x)]
    (Φ : (M → F) → Π x, W x)
    (hadd : ∀ u v : M → F, ContMDiff I 𝓘(𝕜, F) n u → ContMDiff I 𝓘(𝕜, F) n v →
      Φ (u + v) = Φ u + Φ v)
    (hsmul : ∀ (f : M → 𝕜) (u : M → F), ContMDiff I 𝓘(𝕜) n f → ContMDiff I 𝓘(𝕜, F) n u →
      Φ (f • u) = f • Φ u)
    (hconst : ∀ c : F, Φ (fun _ ↦ c) = 0) {u : M → F} (hu : ContMDiff I 𝓘(𝕜, F) n u) :
    Φ u = 0 := by
  classical
  let b := Module.finBasis 𝕜 F
  -- The coefficients of `u` in the basis `b` are smooth.
  let c (i) : M → 𝕜 := fun x ↦ b.coord i (u x)
  have hc (i) : ContMDiff I 𝓘(𝕜) n (c i) :=
    (LinearMap.toContinuousLinearMap (b.coord i)).contDiff.comp_contMDiff hu
  have hterm (i) : ContMDiff I 𝓘(𝕜, F) n (c i • fun _ ↦ b i) :=
    (hc i).smul contMDiff_const
  have hsum (s : Finset (Fin (Module.finrank 𝕜 F))) :
      Φ (∑ i ∈ s, c i • fun _ ↦ b i) = 0 := by
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty]
      exact hconst 0
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, hadd _ _ (hterm i) (contMDiff_finsetSum' fun j _ ↦ hterm j),
        hsmul _ _ (hc i) contMDiff_const, hconst, smul_zero, ih, add_zero]
  have hu_eq : u = ∑ i, c i • fun _ ↦ b i := by
    ext x
    simp [c, Finset.sum_apply, b.sum_repr]
  rw [hu_eq]
  exact hsum _

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {n : ℕ∞ω} [ENat.LEInfty n] [IsManifold I n M]

/-- An operation on sections which respects multiplication by globally `C^n` functions (`n ≤ ∞`)
at two sections takes equal values on them whenever they agree near the evaluation point. The
sections need not be `C^n`, and neither additivity nor any laws for scalar multiplication on the
target are required. This is the bump-function version of `TensorialAt.local`, whose cutoff need
only be differentiable at the evaluation point. -/
theorem eq_of_contMDiff_smul_of_eventuallyEq
    {W : M → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
    {A : Type*} [SMul ℝ A] (Φ : (Π x : M, W x) → A) (x : M) {s s' : Π x : M, W x}
    (hsmul : ∀ {f : M → ℝ}, ContMDiff I 𝓘(ℝ) n f → Φ (f • s) = f x • Φ s)
    (hsmul' : ∀ {f : M → ℝ}, ContMDiff I 𝓘(ℝ) n f → Φ (f • s') = f x • Φ s')
    (hss' : ∀ᶠ y in 𝓝 x, s y = s' y) : Φ s = Φ s' := by
  obtain ⟨ρ, -, hρ⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hss').mem_iff.mp hss'
  have hcut : (ρ : M → ℝ) • s = (ρ : M → ℝ) • s' := by
    funext y
    by_cases hy : ρ y = 0
    · simp [hy]
    · exact congrArg (ρ y • ·) (hρ hy)
  -- Multiplying by `ρ`, which is one at `x`, does not change the value of `Φ`: the scalar law for
  -- the constant function one supplies the identity on that value.
  have hρΦ {u : Π x : M, W x}
      (hu : ∀ {f : M → ℝ}, ContMDiff I 𝓘(ℝ) n f → Φ (f • u) = f x • Φ u) :
      Φ ((ρ : M → ℝ) • u) = Φ u := by
    rw [hu ρ.contMDiff_of_isManifold, ρ.eq_one]
    simpa only [Pi.smul_def', one_smul] using (hu (f := fun _ ↦ 1) contMDiff_const).symm
  rw [← hρΦ hsmul, ← hρΦ hsmul', hcut]

/-- On a finite-rank `C^n` real vector bundle over a finite-dimensional Hausdorff `C^n` manifold
(`n ≤ ∞`), an operation which is additive and linear over globally `C^n` functions on globally
`C^n` sections depends only on the value of such a section at the point of evaluation.
The target need only carry addition and scalar multiplication, without any algebraic laws. -/
theorem eq_of_contMDiff_tensorial
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
    [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
    [FiberBundle G W] [VectorBundle ℝ G W] [ContMDiffVectorBundle n G W I]
    {A : Type*} [Add A] [SMul ℝ A]
    (Φ : (Π x : M, W x) → A) (x : M)
    (hadd : ∀ {s s' : Π x : M, W x}, CMDiff n (T% s) → CMDiff n (T% s') →
      Φ (s + s') = Φ s + Φ s')
    (hsmul : ∀ {f : M → ℝ} {s : Π x : M, W x}, ContMDiff I 𝓘(ℝ) n f →
      CMDiff n (T% s) → Φ (f • s) = f x • Φ s)
    {s s' : Π x : M, W x} (hs : CMDiff n (T% s)) (hs' : CMDiff n (T% s'))
    (hss' : s x = s' x) : Φ s = Φ s' := by
  -- Cut off local frame sections by a bump function which is one near `x`.  This gives globally
  -- `C^n` frame sections and coefficients while preserving the trivialization expansion near `x`.
  let t := trivializationAt G W x
  have hxt : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt G W x
  have ht : t.baseSet ∈ 𝓝 x := t.open_baseSet.mem_nhds hxt
  obtain ⟨ρ, hρt, -⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) ht).mem_iff.mp ht
  let b := Module.finBasis ℝ G
  let frame' (i) : Π y : M, W y := (ρ : M → ℝ) • fun y ↦ t.symm y (b i)
  let coeff' (u : Π x : M, W x) (i) (y : M) := ρ y * b.coord i (t ⟨y, u y⟩).2
  have hframe (i) : CMDiff n (T% (frame' i)) :=
    ρ.contMDiff_of_isManifold.contMDiffOn.smul_section_of_tsupport t.open_baseSet hρt
      (contMDiffOn_symm_baseSet (I := I) (e := t) (b i))
  have hcoeff' (u : Π x : M, W x) (hu : CMDiff n (T% u)) (i) :
      ContMDiff I 𝓘(ℝ) n (coeff' u i) := by
    refine contMDiff_of_tsupport fun y hy ↦ ?_
    have hy : y ∈ t.baseSet := hρt (tsupport_mul_subset_left hy)
    have hnhds : t.baseSet ∈ 𝓝 y := t.open_baseSet.mem_nhds hy
    have hcoord : ContMDiffOn I 𝓘(ℝ, G) n (fun z ↦ (t ⟨z, u z⟩).2) t.baseSet :=
      t.contMDiffOn_section_baseSet_iff.mp hu.contMDiffOn
    exact ρ.contMDiff_of_isManifold.contMDiffAt.mul
      ((LinearMap.toContinuousLinearMap (b.coord i)).contDiff.comp_contMDiffAt
        (hcoord.contMDiffAt hnhds))
  have hterm (u : Π x : M, W x) (hu : CMDiff n (T% u)) (i) :
      CMDiff n (T% (coeff' u i • frame' i)) :=
    (hcoeff' u hu i).smul_section (hframe i)
  -- Near `x`, a `C^n` section agrees with its expansion in the cut-off frame, which is `C^n`.
  have hexpansion (u : Π x : M, W x) (hu : CMDiff n (T% u)) :
      Φ u = Φ (∑ i, coeff' u i • frame' i) := by
    refine eq_of_contMDiff_smul_of_eventuallyEq Φ x (hsmul · hu) (hsmul · ?_) ?_
    · simpa only [Finset.sum_apply] using ContMDiff.sum_section fun i _ ↦ hterm u hu i
    · filter_upwards [ρ.eventuallyEq_one, ht] with y hyρ hy
      have hyρ' : ρ y = 1 := hyρ
      calc u y
        _ = t.symm y (t ⟨y, u y⟩).2 := (t.symm_apply_apply_mk hy (u y)).symm
        _ = t.symmL ℝ y (t ⟨y, u y⟩).2 := (t.symmL_apply hy _).symm
        _ = t.symmL ℝ y (∑ i, b.coord i (t ⟨y, u y⟩).2 • b i) := by
          simp only [Basis.coord_apply, b.sum_repr]
        _ = ∑ i, b.coord i (t ⟨y, u y⟩).2 • t.symmL ℝ y (b i) := by
          rw [map_sum]; exact Finset.sum_congr rfl fun i _ ↦ map_smul _ _ _
        _ = ∑ i, coeff' u i y • frame' i y := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simp [coeff', frame', hyρ', t.symmL_apply hy]
        _ = (∑ i, coeff' u i • frame' i) y := by simp only [Finset.sum_apply, Pi.smul_apply']
  rw [hexpansion s hs, hexpansion s' hs']
  refine map_sum_eq_of_contMDiff_additive Φ hadd Finset.univ _ _ (fun i _ ↦ hterm s hs i)
    (fun i _ ↦ hterm s' hs' i) fun i _ ↦ ?_
  rw [hsmul (hcoeff' s hs i) (hframe i), hsmul (hcoeff' s' hs' i) (hframe i)]
  simp only [coeff', ρ.eq_one, one_mul, hss']

end TauCeti.Manifold

/-! ### Tensoriality in several arguments -/

namespace TensorialAt

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
  {A : Type*} [AddCommGroup A] [Module 𝕜 A]
  {ι : Type*} [hdec : DecidableEq ι]

/-- If an operation `Φ` on families of sections of a vector bundle `V`, indexed by a finite type
`ι`, is tensorial at `x` in each argument whenever the other arguments are differentiable at `x`,
then it depends only on the values of the sections at `x`. For two arguments this is
`TensorialAt.pointwise₂`. -/
theorem pointwise_pi [Finite ι] {Φ : (ι → Π x : M, V x) → A} {x : M}
    (hΦ : ∀ σ : ι → Π x : M, V x, (∀ i, MDiffAt (T% (σ i)) x) →
      ∀ i, TensorialAt I F (fun τ ↦ Φ (Function.update σ i τ)) x)
    {σ σ' : ι → Π x : M, V x} (hσ : ∀ i, MDiffAt (T% (σ i)) x)
    (hσ' : ∀ i, MDiffAt (T% (σ' i)) x) (hσσ' : ∀ i, σ i x = σ' i x) :
    Φ σ = Φ σ' := by
  have := Fintype.ofFinite ι
  -- Replace the arguments of `σ` by those of `σ'` one at a time.
  suffices h : ∀ s : Finset ι, Φ (s.piecewise σ' σ) = Φ σ by
    simpa using (h Finset.univ).symm
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    set τ := s.piecewise σ' σ
    have hτ (j : ι) : MDiffAt (T% (τ j)) x := by
      by_cases hj : j ∈ s
      · simpa [τ, hj] using hσ' j
      · simpa [τ, hj] using hσ j
    have hτi : τ i = σ i := by simp [τ, hi]
    rw [Finset.piecewise_insert, ← ih]
    conv_rhs => rw [← Function.update_eq_self i τ]
    exact (hΦ τ hτ i).pointwise (hσ' i) (hτ i) (by rw [hτi, hσσ'])

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [TopologicalSpace A] [ContinuousAdd A] [ContinuousSMul 𝕜 A]

/-- Given an `A`-valued operation `Φ` on families of sections of a vector bundle `V`, indexed by
a finite type `ι`, which is tensorial at `x` in each argument whenever the other arguments are
differentiable at `x`, the construction `TensorialAt.mkMultilinear` provides the associated
continuous multilinear map on the fibre `V x`. Its value on vectors `vᵢ` is the value of `Φ` on
any differentiable sections through them (`TensorialAt.mkMultilinear_apply`). -/
noncomputable def mkMultilinear [Finite ι]
    -- `Φ` and `x` explicit to make it easier to generate the side condition at point of use
    (Φ : (ι → Π x : M, V x) → A) (x : M)
    (hΦ : ∀ σ : ι → Π x : M, V x, (∀ i, MDiffAt (T% (σ i)) x) →
      ∀ i, TensorialAt I F (fun τ ↦ Φ (Function.update σ i τ)) x) :
    ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) A :=
  have : T2Space (V x) := FiberBundle.t2Space F V x
  have : FiniteDimensional 𝕜 (V x) := VectorBundle.finiteDimensional 𝕜 F V x
  -- Extending the vectors to sections, the value of `Φ` changes in one argument only by
  -- operations on sections with the same value at `x`.
  have hext (u : ι → V x) (i : ι) (c : V x) :
      (fun j ↦ extend F (Function.update u i c j)) =
        Function.update (fun j ↦ extend F (u j)) i (extend F c) :=
    funext fun j ↦ Function.apply_update (fun _ ↦ extend F) u i c j
  have hdiff (u : ι → V x) (j : ι) : MDiffAt (T% ((fun j ↦ extend F (u j)) j)) x :=
    mdifferentiableAt_extend ..
  let f : MultilinearMap (RingHom.id 𝕜) (fun _ : ι ↦ V x) A :=
    { toFun u := Φ (fun i ↦ extend F (u i))
      map_update_add' := by
        intro inst u i a b
        obtain rfl : hdec = inst := Subsingleton.elim _ _
        simp only [hext]
        rw [← (hΦ _ (hdiff u) i).add (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)]
        exact (hΦ _ (hdiff u) i).pointwise (mdifferentiableAt_extend ..)
          (mdifferentiableAt_add_section (mdifferentiableAt_extend ..)
            (mdifferentiableAt_extend ..)) (by simp)
      map_update_smul' := by
        intro inst u i c a
        obtain rfl : hdec = inst := Subsingleton.elim _ _
        simp only [hext, RingHom.id_apply]
        rw [← (hΦ _ (hdiff u) i).smul (f := fun _ ↦ c) (mdifferentiable_const ..)
          (mdifferentiableAt_extend ..)]
        exact (hΦ _ (hdiff u) i).pointwise (mdifferentiableAt_extend ..)
          (mdifferentiableAt_const.smul_section (mdifferentiableAt_extend ..)) (by simp) }
  ⟨f, f.continuous_of_finiteDimensional⟩

/-- The multilinear map of a tensorial operation evaluates the operation on the local extensions
`FiberBundle.extend` of the vectors. -/
theorem mkMultilinear_apply_eq_extend [Finite ι] {Φ : (ι → Π x : M, V x) → A} {x : M}
    (hΦ : ∀ σ : ι → Π x : M, V x, (∀ i, MDiffAt (T% (σ i)) x) →
      ∀ i, TensorialAt I F (fun τ ↦ Φ (Function.update σ i τ)) x)
    (u : ι → V x) :
    mkMultilinear Φ x hΦ u = Φ (fun i ↦ extend F (u i)) :=
  (rfl)

/-- The multilinear map of a tensorial operation, evaluated on the values at `x` of sections
differentiable at `x`, is the value of the operation on those sections. -/
theorem mkMultilinear_apply [Finite ι] {Φ : (ι → Π x : M, V x) → A} {x : M}
    (hΦ : ∀ σ : ι → Π x : M, V x, (∀ i, MDiffAt (T% (σ i)) x) →
      ∀ i, TensorialAt I F (fun τ ↦ Φ (Function.update σ i τ)) x)
    {σ : ι → Π x : M, V x} (hσ : ∀ i, MDiffAt (T% (σ i)) x) :
    mkMultilinear Φ x hΦ (fun i ↦ σ i x) = Φ σ := by
  rw [mkMultilinear_apply_eq_extend]
  exact pointwise_pi hΦ (fun _ ↦ mdifferentiableAt_extend ..) hσ (by simp)

end TensorialAt
