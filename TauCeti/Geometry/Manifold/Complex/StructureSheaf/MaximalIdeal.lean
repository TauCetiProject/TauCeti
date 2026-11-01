/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Germ
import Mathlib.Analysis.Calculus.FDeriv.Mul
import TauCeti.Analysis.Analytic.Hadamard
import TauCeti.Geometry.Manifold.ContMDiff.Analytic

/-!
# Local coordinates generate the maximal ideal of a holomorphic stalk

Let `X` be a complex manifold modelled on `𝓘(ℂ, E)` and let `e` be a holomorphic chart at `x`.
Every continuous linear functional `ℓ` on `E` gives a holomorphic coordinate `y ↦ ℓ (e y - e x)`
centered at `x`, and its germ `e.holomorphicLinearCoordinateGerm he x ℓ hx` lies in the maximal
ideal of the stalk `𝒪_x`, which is the kernel of evaluation at `x`.

When `E` is finite-dimensional, Hadamard's lemma `AnalyticAt.exists_analyticAt_eventually_sub_eq`
writes every germ vanishing at `x` as `∑ i, zᵢ * qᵢ`, where `zᵢ` are the coordinate germs along
the coordinate functionals `b.coord i` of a basis `b` of `E`, and the values `qᵢ(x)` are the partial
derivatives of the germ in the chart. Consequently:

* the coordinate germs `z₁, …, zₙ` of any chart and any basis generate the maximal ideal of the
  holomorphic stalk (`OpenPartialHomeomorph.ker_eval_eq_span_holomorphicLinearCoordinateGerm`);
* a germ lies in the square of the maximal ideal exactly when it vanishes at `x` together with its
  derivative read in the chart (`OpenPartialHomeomorph.mem_ker_eval_sq_iff`).

The first statement is the several-variable analogue of the one-variable
`OpenPartialHomeomorph.ker_eval_eq_span_holomorphicCoordinateGerm` for complex curves. Together,
the two statements say that `n = dim E` coordinate germs generate the maximal ideal `𝔪` of the
analytic local ring, and that a germ in `𝔪` is determined modulo `𝔪²` by its derivative at `x`
read in the chart.

## References

* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II.
* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II.
-/

public noncomputable section

open CategoryTheory Filter IsManifold Opposite Set TopologicalSpace Topology
open scoped ContDiff Manifold
open TauCeti TauCeti.holomorphicStructureSheaf

namespace OpenPartialHomeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  (e : OpenPartialHomeomorph X E) (he : e ∈ maximalAtlas 𝓘(ℂ, E) ω X) (x : X)

/-! ### Linear coordinates of a chart -/

/-- The coordinate of the chart `e` along a continuous linear functional `ℓ`, translated by `z`,
as a holomorphic section on the chart source: `y ↦ ℓ (e y - z)`. -/
def holomorphicLinearCoordinateSection (ℓ : StrongDual ℂ E) (z : E) :
    (holomorphicStructureSheaf 𝓘(ℂ, E) X).obj.obj (op ⟨e.source, e.open_source⟩) :=
  ofContMDiff (fun y ↦ ℓ (e y - z)) fun y ↦
    ℓ.contMDiffAt.comp y ((((contMDiffOn_of_mem_maximalAtlas he).contMDiffAt
      (e.open_source.mem_nhds y.2)).comp y contMDiff_subtype_val.contMDiffAt).sub
        contMDiffAt_const)

/-- The translated linear coordinate section evaluates at `y` to `ℓ (e y - z)`. -/
-- Index on evaluation rather than the unexposed section carrier and its dependent open set.
@[simp]
theorem holomorphicLinearCoordinateSection_apply (ℓ : StrongDual ℂ E) (z : E)
    (y : (⟨e.source, e.open_source⟩ : Opens X)) :
    toFun 𝓘(ℂ, E) X (no_index (op ⟨e.source, e.open_source⟩))
      (no_index (holomorphicLinearCoordinateSection e he ℓ z)) y = ℓ (e y - z) := (by
  rw [holomorphicLinearCoordinateSection]
  exact ofContMDiff_apply (U := ⟨e.source, e.open_source⟩) _ _ y)

/-- The germ at `x` of the centered linear coordinate `y ↦ ℓ (e y - e x)` of the chart `e`. -/
def holomorphicLinearCoordinateGerm (ℓ : StrongDual ℂ E) (hx : x ∈ e.source) :
    (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x :=
  (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.germ ⟨e.source, e.open_source⟩ x hx
    (holomorphicLinearCoordinateSection e he ℓ (e x))

/-- The centered linear coordinate germ is the germ of the translated coordinate section. -/
theorem holomorphicLinearCoordinateGerm_def (ℓ : StrongDual ℂ E) (hx : x ∈ e.source) :
    holomorphicLinearCoordinateGerm e he x ℓ hx =
      (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.germ ⟨e.source, e.open_source⟩ x hx
        (holomorphicLinearCoordinateSection e he ℓ (e x)) := (rfl)

/-- As a germ of functions, the centered linear coordinate germ is `y ↦ ℓ (e y - e x)`. -/
@[simp]
theorem toFilterGerm_holomorphicLinearCoordinateGerm (ℓ : StrongDual ℂ E) (hx : x ∈ e.source)
    {l : Filter X} (hl : l ≤ 𝓝 x) :
    toFilterGerm 𝓘(ℂ, E) X x l hl (holomorphicLinearCoordinateGerm e he x ℓ hx) =
      (fun y ↦ ℓ (e y - e x) : X → ℂ) :=
  toFilterGerm_germ hl hx _ _ fun y ↦ holomorphicLinearCoordinateSection_apply e he ℓ (e x) y

/-- The centered linear coordinate germs vanish at their center. -/
@[simp]
theorem eval_holomorphicLinearCoordinateGerm (ℓ : StrongDual ℂ E) (hx : x ∈ e.source) :
    eval 𝓘(ℂ, E) X x (holomorphicLinearCoordinateGerm e he x ℓ hx) = 0 := by
  rw [eval_eq_of_toFilterGerm_eq (toFilterGerm_holomorphicLinearCoordinateGerm e he x ℓ hx le_rfl),
    sub_self, map_zero]

/-! ### Hadamard's lemma for holomorphic germs -/

variable {x}

include he in
/-- Every representative of a holomorphic germ at `x` is analytic at `e x` when read in the
chart `e`. -/
private theorem analyticAt_comp_symm_of_toFilterGerm_eq (hx : x ∈ e.source)
    {s : (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x} {φ : X → ℂ}
    (hφ : toFilterGerm 𝓘(ℂ, E) X x (𝓝 x) le_rfl s = φ) :
    AnalyticAt ℂ (φ ∘ e.symm) (e x) := by
  simpa using ((exists_toFilterGerm_nhds_eq_iff.1 ⟨s, hφ⟩).self_of_nhds).analyticAt_comp_extend_symm
    he hx

include he in
/-- Every representative of a germ in the square of the ideal of germs vanishing at `x` has
vanishing derivative at `x`, read in the chart `e`. -/
private theorem hasFDerivAt_comp_symm_of_mem_ker_eval_sq (hx : x ∈ e.source)
    {s : (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x}
    (hs : s ∈ RingHom.ker (eval 𝓘(ℂ, E) X x) ^ 2) {φ : X → ℂ}
    (hφ : toFilterGerm 𝓘(ℂ, E) X x (𝓝 x) le_rfl s = φ) :
    HasFDerivAt (φ ∘ e.symm) (0 : E →L[ℂ] ℂ) (e x) := by
  have hsymm : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
    simpa only [e.left_inv hx] using (e.continuousAt_symm (e.map_source hx)).tendsto
  rw [pow_two] at hs
  -- Induct over sums of products `a * c` of germs vanishing at `x`.
  refine Submodule.mul_induction_on (C := fun t ↦ ∀ ψ : X → ℂ,
      toFilterGerm 𝓘(ℂ, E) X x (𝓝 x) le_rfl t = ψ → HasFDerivAt (ψ ∘ e.symm) (0 : E →L[ℂ] ℂ) (e x))
    hs (fun a ha c hc φ hφ ↦ ?_) (fun a c ha hc φ hφ ↦ ?_) φ hφ
  · obtain ⟨α, -, hα⟩ := exists_toFilterGerm_eq x a
    obtain ⟨γ, -, hγ⟩ := exists_toFilterGerm_eq x c
    have hα0 : α x = 0 := (eval_eq_of_toFilterGerm_eq (hα _ _)).symm.trans ha
    have hγ0 : γ x = 0 := (eval_eq_of_toFilterGerm_eq (hγ _ _)).symm.trans hc
    have hev : φ =ᶠ[𝓝 x] α * γ := by
      rw [← Germ.coe_eq, ← hφ, map_mul, hα, hγ, Germ.coe_mul]
    have hprod := (analyticAt_comp_symm_of_toFilterGerm_eq e he hx (hα _ _)).differentiableAt
      |>.hasFDerivAt.mul
        (analyticAt_comp_symm_of_toFilterGerm_eq e he hx (hγ _ _)).differentiableAt.hasFDerivAt
    refine (hprod.congr_fderiv ?_).congr_of_eventuallyEq (hsymm.eventually hev)
    ext v
    simp [e.left_inv hx, hα0, hγ0]
  · obtain ⟨α, -, hα⟩ := exists_toFilterGerm_eq x a
    obtain ⟨γ, -, hγ⟩ := exists_toFilterGerm_eq x c
    have hev : φ =ᶠ[𝓝 x] α + γ := by
      rw [← Germ.coe_eq, ← hφ, map_add, hα, hγ, Germ.coe_add]
    exact (((ha α (hα _ _)).add (hc γ (hγ _ _))).congr_fderiv (add_zero 0)).congr_of_eventuallyEq
      (hsymm.eventually hev)

variable [FiniteDimensional ℂ E] {ι : Type*} (b : Module.Basis ι ℂ E)

/-- **Hadamard's lemma for holomorphic germs.** A holomorphic germ vanishing at `x` is a
combination `∑ i, zᵢ * qᵢ` of the centered coordinate germs `zᵢ` along the coordinate functionals
of a basis `b`, whose coefficients `qᵢ` take at `x` the values of the partial derivatives
`∂φ/∂zᵢ` of any representative `φ`, read in the chart `e`. -/
theorem exists_eq_sum_holomorphicLinearCoordinateGerm_mul [Fintype ι] (hx : x ∈ e.source)
    {s : (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x} (hs : eval 𝓘(ℂ, E) X x s = 0)
    {φ : X → ℂ} (hφ : toFilterGerm 𝓘(ℂ, E) X x (𝓝 x) le_rfl s = φ) :
    ∃ q : ι → (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x,
      s = ∑ i, holomorphicLinearCoordinateGerm e he x
        (LinearMap.toContinuousLinearMap (b.coord i)) hx * q i ∧
      ∀ i, eval 𝓘(ℂ, E) X x (q i) = fderiv ℂ (φ ∘ e.symm) (e x) (b i) := by
  have hφx : φ x = 0 := (eval_eq_of_toFilterGerm_eq hφ).symm.trans hs
  obtain ⟨G, hG, hGx, hGeq⟩ :=
    (analyticAt_comp_symm_of_toFilterGerm_eq e he hx hφ).exists_analyticAt_eventually_sub_eq
  -- The coefficient `G (e y) (b i)` has a holomorphic germ `q i` at `x`.
  have hq (i : ι) : ∃ q : (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x,
      toFilterGerm 𝓘(ℂ, E) X x (𝓝 x) le_rfl q = (fun y ↦ G (e y) (b i) : X → ℂ) := by
    refine (exists_toFilterGerm_eq_of_eventually_contMDiffAt ?_).imp fun _ h ↦ h _ le_rfl
    filter_upwards [e.open_source.mem_nhds hx, (e.continuousAt hx).eventually
      ((ContinuousLinearMap.apply ℂ ℂ (b i)).analyticAt _ |>.comp hG).eventually_analyticAt]
      with y hy hyG
    exact hyG.contDiffAt.contMDiffAt.comp y
      ((contMDiffOn_of_mem_maximalAtlas he).contMDiffAt (e.open_source.mem_nhds hy))
  choose q hq using hq
  refine ⟨q, toFilterGerm_nhds_injective x ?_, fun i ↦ ?_⟩
  · -- Near `x`, Hadamard's identity expands in the basis `b`.
    have hev : φ =ᶠ[𝓝 x] ∑ i, (fun y ↦ b.coord i (e y - e x)) * fun y ↦ G (e y) (b i) := by
      filter_upwards [e.open_source.mem_nhds hx, (e.continuousAt hx).eventually hGeq]
        with y hy hyG
      simp only [Function.comp_apply, e.left_inv hy, e.left_inv hx, hφx, sub_zero] at hyG
      rw [hyG]
      conv_lhs => rw [← b.sum_repr (e y - e x)]
      simp [map_sum, mul_comm]
    simp only [map_sum, map_mul, toFilterGerm_holomorphicLinearCoordinateGerm, hq, hφ,
      Germ.coe_eq.2 hev, LinearMap.coe_toContinuousLinearMap', ← Germ.coe_mul]
    exact map_sum (Germ.coeRingHom (𝓝 x)) _ _
  · rw [eval_eq_of_toFilterGerm_eq (hq i), hGx]

/-! ### The maximal ideal and its square -/

/-- **Local coordinates generate the maximal ideal.** The germs at `x` of the centered
coordinates `y ↦ b.coord i (e y - e x)` of a holomorphic chart, for a basis `b` of the
finite-dimensional model `E`, generate the ideal of holomorphic germs vanishing at `x`. -/
theorem ker_eval_eq_span_holomorphicLinearCoordinateGerm (hx : x ∈ e.source) :
    RingHom.ker (eval 𝓘(ℂ, E) X x) = Ideal.span (range fun i ↦
      holomorphicLinearCoordinateGerm e he x (LinearMap.toContinuousLinearMap (b.coord i)) hx) := by
  refine le_antisymm (fun s hs ↦ ?_) <| Ideal.span_le.2 <| range_subset_iff.2 fun i ↦
    RingHom.mem_ker.2 (eval_holomorphicLinearCoordinateGerm e he x _ hx)
  have := Module.Finite.finite_basis b
  have := Fintype.ofFinite ι
  obtain ⟨φ, -, hφ⟩ := exists_toFilterGerm_eq x s
  obtain ⟨q, rfl, -⟩ :=
    exists_eq_sum_holomorphicLinearCoordinateGerm_mul e he b hx (RingHom.mem_ker.1 hs) (hφ _ _)
  exact sum_mem fun i _ ↦ Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- The ideal of holomorphic germs vanishing at `x` is generated by the centered linear
coordinate germs `y ↦ ℓ (e y - e x)` of a holomorphic chart, over all continuous linear
functionals `ℓ` on the finite-dimensional model `E`. -/
theorem ker_eval_eq_span_range_holomorphicLinearCoordinateGerm (hx : x ∈ e.source) :
    RingHom.ker (eval 𝓘(ℂ, E) X x) =
      Ideal.span (range fun ℓ ↦ holomorphicLinearCoordinateGerm e he x ℓ hx) := by
  refine le_antisymm ?_ <| Ideal.span_le.2 <| range_subset_iff.2 fun ℓ ↦
    RingHom.mem_ker.2 (eval_holomorphicLinearCoordinateGerm e he x _ hx)
  rw [ker_eval_eq_span_holomorphicLinearCoordinateGerm e he (Module.finBasis ℂ E) hx]
  exact Ideal.span_mono <| range_subset_iff.2 fun i ↦ ⟨_, rfl⟩

include he in
/-- **The square of the maximal ideal.** A holomorphic germ lies in the square of the ideal of
germs vanishing at `x` exactly when any of its representatives `φ` vanishes at `x` together with
its derivative read in a holomorphic chart `e`. -/
theorem mem_ker_eval_sq_iff (hx : x ∈ e.source)
    {s : (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x} {φ : X → ℂ}
    (hφ : toFilterGerm 𝓘(ℂ, E) X x (𝓝 x) le_rfl s = φ) :
    s ∈ RingHom.ker (eval 𝓘(ℂ, E) X x) ^ 2 ↔ φ x = 0 ∧ fderiv ℂ (φ ∘ e.symm) (e x) = 0 := by
  refine ⟨fun hs ↦ ⟨?_, (hasFDerivAt_comp_symm_of_mem_ker_eval_sq e he hx hs hφ).fderiv⟩,
    fun ⟨hφx, hdφ⟩ ↦ ?_⟩
  · exact (eval_eq_of_toFilterGerm_eq hφ).symm.trans
      (RingHom.mem_ker.1 (Ideal.pow_le_self two_ne_zero hs))
  -- Conversely, the coefficients in Hadamard's lemma vanish at `x`.
  have hs : eval 𝓘(ℂ, E) X x s = 0 := (eval_eq_of_toFilterGerm_eq hφ).trans hφx
  obtain ⟨q, rfl, hq⟩ :=
    exists_eq_sum_holomorphicLinearCoordinateGerm_mul e he (Module.finBasis ℂ E) hx hs hφ
  rw [pow_two]
  exact sum_mem fun i _ ↦ Ideal.mul_mem_mul
    (RingHom.mem_ker.2 (eval_holomorphicLinearCoordinateGerm e he x _ hx))
    (RingHom.mem_ker.2 ((hq i).trans (by simp [hdφ])))

end OpenPartialHomeomorph
