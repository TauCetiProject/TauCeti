/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
public import Mathlib.LinearAlgebra.Alternating.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
import Mathlib.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Tensoriality of globally smooth operations

This file complements Mathlib's pointwise tensoriality API with a criterion for operations whose
additivity and smooth-function linearity laws are available for globally smooth sections.
The criterion applies to finite-rank smooth real vector bundles over finite-dimensional Hausdorff
manifolds; on a trivial bundle the constant sections form a global frame, and no hypothesis on the
base is needed. The target only needs addition and scalar multiplication; no algebraic laws on
these operations are required beyond the stated laws for the section operation.

## Main results

* `TauCeti.Manifold.eq_of_contMDiff_smul_of_eventuallyEq`: smooth-function linearity
  implies locality.
* `TauCeti.Manifold.eq_of_contMDiff_tensorial`: an operation satisfying these laws has equal
  values on globally smooth sections which agree at the point of evaluation.
* `TauCeti.Manifold.eq_zero_of_contMDiff_tensorial_of_const`: on the trivial bundle with
  finite-dimensional fibre, an operation satisfying these laws and vanishing on constant sections
  vanishes, over any base.
* `MultilinearMap.contMDiffSection_eval_congr` and `AlternatingMap.contMDiffSection_eval_congr`:
  `C^∞(M, ℝ)`-multilinear and alternating maps on sections depend pointwise on section values.
-/

public section

open Bundle FiberBundle Module
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

/-- An operation on sections which is additive on globally smooth sections takes equal values on
two finite sums of globally smooth sections whenever it takes equal values on the summands.  The
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
      -- Partial sums of globally smooth sections are globally smooth.
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
  let b := Module.finBasis 𝕜 F; let c (i) : M → 𝕜 := fun x ↦ b.coord i (u x)
  have hc (i) : ContMDiff I 𝓘(𝕜) n (c i) :=
    (LinearMap.toContinuousLinearMap (b.coord i)).contDiff.comp_contMDiff hu
  have hterm (i) : ContMDiff I 𝓘(𝕜, F) n (c i • fun _ ↦ b i) := (hc i).smul contMDiff_const
  have hsum (s : Finset (Fin (Module.finrank 𝕜 F))) : Φ (∑ i ∈ s, c i • fun _ ↦ b i) = 0 := by
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty]; exact hconst 0
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, hadd _ _ (hterm i) (contMDiff_finsetSum' fun j _ ↦ hterm j),
        hsmul _ _ (hc i) contMDiff_const, hconst, smul_zero, ih, add_zero]
  have hu_eq : u = ∑ i, c i • fun _ ↦ b i := by ext x; simp [c, Finset.sum_apply, b.sum_repr]
  rw [hu_eq]; exact hsum _

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- An operation on sections which respects multiplication by globally smooth functions at two
sections takes equal values on them whenever they agree near the evaluation point. The sections
need not be smooth, and neither additivity nor any laws for scalar multiplication on the target are
required. This is the smooth bump-function version of `TensorialAt.local`, whose cutoff need only
be differentiable at the evaluation point. -/
theorem eq_of_contMDiff_smul_of_eventuallyEq
    {W : M → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
    {A : Type*} [SMul ℝ A] (Φ : (Π x : M, W x) → A) (x : M) {s s' : Π x : M, W x}
    (hsmul : ∀ {f : M → ℝ}, ContMDiff I 𝓘(ℝ) ∞ f → Φ (f • s) = f x • Φ s)
    (hsmul' : ∀ {f : M → ℝ}, ContMDiff I 𝓘(ℝ) ∞ f → Φ (f • s') = f x • Φ s')
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
      (hu : ∀ {f : M → ℝ}, ContMDiff I 𝓘(ℝ) ∞ f → Φ (f • u) = f x • Φ u) :
      Φ ((ρ : M → ℝ) • u) = Φ u := by
    rw [hu ρ.contMDiff, ρ.eq_one]
    simpa only [Pi.smul_def', one_smul] using (hu (f := fun _ ↦ 1) contMDiff_const).symm
  rw [← hρΦ hsmul, ← hρΦ hsmul', hcut]

/-- On a finite-rank smooth real vector bundle over a finite-dimensional Hausdorff manifold,
an operation which is additive and linear over globally smooth functions on globally
smooth sections depends only on the value of such a section at the point of evaluation.
The target need only carry addition and scalar multiplication, without any algebraic laws. -/
theorem eq_of_contMDiff_tensorial
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
    [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
    [FiberBundle G W] [VectorBundle ℝ G W] [ContMDiffVectorBundle ∞ G W I]
    {A : Type*} [Add A] [SMul ℝ A]
    (Φ : (Π x : M, W x) → A) (x : M)
    (hadd : ∀ {s s' : Π x : M, W x}, CMDiff ∞ (T% s) → CMDiff ∞ (T% s') →
      Φ (s + s') = Φ s + Φ s')
    (hsmul : ∀ {f : M → ℝ} {s : Π x : M, W x}, ContMDiff I 𝓘(ℝ) ∞ f →
      CMDiff ∞ (T% s) → Φ (f • s) = f x • Φ s)
    {s s' : Π x : M, W x} (hs : CMDiff ∞ (T% s)) (hs' : CMDiff ∞ (T% s'))
    (hss' : s x = s' x) : Φ s = Φ s' := by
  -- Cut off a local frame by a bump function which is one near `x`.  This gives globally smooth
  -- frame sections and coefficients while preserving the local frame expansion near `x`.
  let t := trivializationAt G W x
  have hxt : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt G W x
  have ht : t.baseSet ∈ 𝓝 x := t.open_baseSet.mem_nhds hxt
  obtain ⟨ρ, hρt, -⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) ht).mem_iff.mp ht
  let b := Basis.ofVectorSpace ℝ G
  let frame' (i) := (ρ : M → ℝ) • t.localFrame b i
  let coeff' (u : Π x : M, W x) (i) (y : M) := ρ y * t.localFrameCoeff I b i y (u y)
  have hframe (i) : CMDiff ∞ (T% (frame' i)) :=
    ρ.contMDiff.contMDiffOn.smul_section_of_tsupport t.open_baseSet hρt
      (t.contMDiffOn_localFrame_baseSet ∞ b i)
  have hcoeff' (u : Π x : M, W x) (hu : CMDiff ∞ (T% u)) (i) :
      ContMDiff I 𝓘(ℝ) ∞ (coeff' u i) :=
    t.contMDiff_mul_localFrameCoeff b ρ.contMDiff.contMDiffOn hρt hu.contMDiffOn i
  have hterm (u : Π x : M, W x) (hu : CMDiff ∞ (T% u)) (i) :
      CMDiff ∞ (T% (coeff' u i • frame' i)) :=
    (hcoeff' u hu i).smul_section (hframe i)
  -- Near `x`, a smooth section agrees with its expansion in the cut-off frame, which is smooth.
  have hexpansion (u : Π x : M, W x) (hu : CMDiff ∞ (T% u)) :
      Φ u = Φ (∑ i, coeff' u i • frame' i) := by
    refine eq_of_contMDiff_smul_of_eventuallyEq Φ x (hsmul · hu) (hsmul · ?_) ?_
    · simpa only [Finset.sum_apply] using ContMDiff.sum_section fun i _ ↦ hterm u hu i
    · filter_upwards [ρ.eventuallyEq_one,
        t.eventually_eq_localFrame_sum_coeff_smul (I := I) b hxt] with y hρ hu
      simpa [coeff', frame', hρ] using hu
  rw [hexpansion s hs, hexpansion s' hs']
  refine map_sum_eq_of_contMDiff_additive Φ hadd Finset.univ _ _ (fun i _ ↦ hterm s hs i)
    (fun i _ ↦ hterm s' hs' i) fun i _ ↦ ?_
  rw [hsmul (hcoeff' s hs i) (hframe i), hsmul (hcoeff' s' hs' i) (hframe i)]
  simp only [coeff', ρ.eq_one, one_mul, t.localFrameCoeff_congr (I := I) b (i := i) hss']

end TauCeti.Manifold

section EvalCongr
variable {E H M FW FV ι : Type*} [Finite ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] [NormedAddCommGroup FW] [NormedSpace ℝ FW]
  [FiniteDimensional ℝ FW] [NormedAddCommGroup FV] [NormedSpace ℝ FV] {W V : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle ℝ FW W]
  [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V] [VectorBundle ℝ FV V]
  [ContMDiffVectorBundle ∞ FW W I]

/-- A `C^∞(M, ℝ)`-multilinear map on `Γ(W)` depends at `x` only on the values of its input
sections at `x`. -/
theorem MultilinearMap.contMDiffSection_eval_congr
    (Φ : (ι → Cₛ^∞⟮I; FW, W⟯) →ₘₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯) (x : M)
    {s s' : ι → Cₛ^∞⟮I; FW, W⟯} (h : ∀ i, s i x = s' i x) : Φ s x = Φ s' x := by
  classical
  cases nonempty_fintype ι
  suffices ∀ q : Finset ι, Φ (fun i ↦ if i ∈ q then s' i else s i) x = Φ s x by
    simpa using (this Finset.univ).symm
  intro q; induction q using Finset.induction_on with
  | empty => simp
  | @insert j q hj ih =>
    let u : ι → Cₛ^∞⟮I; FW, W⟯ := fun i ↦ if i ∈ q then s' i else s i
    have hu_self : Function.update u j (s j) = u :=
      Function.update_eq_self_iff.mpr (by simp [u, hj])
    have hins : (fun i ↦ if i ∈ insert j q then s' i else s i) = Function.update u j (s' j) := by
      ext i; by_cases hij : i = j <;> simp [u, hij]
    change Φ u x = Φ s x at ih; rw [hins, ← ih]; conv_rhs => rw [← hu_self]
    let Ψ : (Π y : M, W y) → V x := fun t ↦
      if ht : CMDiff ∞ (T% t) then Φ (Function.update u j ⟨t, ht⟩) x else 0
    have hΨ (t : Cₛ^∞⟮I; FW, W⟯) : Φ (Function.update u j t) x = Ψ ⇑t := by cases t; simp [Ψ, *]
    rw [hΨ (s' j), hΨ (s j)]
    refine TauCeti.Manifold.eq_of_contMDiff_tensorial Ψ x (fun {t₁ t₂} ht₁ ht₂ ↦ ?_)
      (fun {f t} hf ht ↦ ?_) (s' j).contMDiff (s j).contMDiff (h j).symm
    · simp only [Ψ, ht₁, ht₂, ht₁.add_section ht₂, ↓reduceDIte]
      exact congr($(Φ.map_update_add u j ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩) x)
    · simp only [Ψ, ht, hf.smul_section ht, ↓reduceDIte]; let F : C^∞⟮I, M; ℝ⟯ := ⟨f, hf⟩
      have hft : (⟨f • t, hf.smul_section ht⟩ : Cₛ^∞⟮I; FW, W⟯) = F • ⟨t, ht⟩ :=
        ContMDiffSection.ext fun y ↦ (ContMDiffSection.smul_apply F ⟨t, ht⟩ y).symm
      rw [hft, Φ.map_update_smul, RingHom.id_apply, ContMDiffSection.smul_apply]; rfl

/-- A `C^∞(M, ℝ)`-multilinear alternating map on `Γ(W)` depends at `x` only on the values of its
input sections at `x`. -/
theorem AlternatingMap.contMDiffSection_eval_congr
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯) (x : M)
    {s s' : ι → Cₛ^∞⟮I; FW, W⟯} (h : ∀ i, s i x = s' i x) : Φ s x = Φ s' x :=
  Φ.toMultilinearMap.contMDiffSection_eval_congr x h
end EvalCongr
