/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.Polar
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.Distribution.Annihilator
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle

/-!
# The annihilator line of a hyperplane distribution

For a distribution `D` on a manifold `M`, the covectors at `x` vanishing on `D x` form the
subspace `TauCeti.CotangentBundle.annihilatorSpace D x` of `T*_x M`. Its total space carries the
subspace topology of `T*M`
(`TauCeti.CotangentBundle.instTopologicalSpaceTotalSpaceAnnihilatorSpace`) and the canonical
inclusion `TauCeti.CotangentBundle.annihilatorInclusion` into `T*M` is a topological embedding
(`TauCeti.CotangentBundle.isEmbedding_annihilatorInclusion`).

When `D` is a `C^n` hyperplane field, of rank `k` with `k + 1 = dim M`, every point has a
neighbourhood on which `D` is the kernel of a nowhere-zero `C^n` covector field
(`TauCeti.IsContMDiffDistribution.exists_local_annihilator`), and such a covector field spans the
annihilator there (`TauCeti.CotangentBundle.annihilatorSpace_eq_span_singleton`). So the
annihilators have `C^n` local frames of size one
(`TauCeti.CotangentBundle.hasLocalContMDiffSubbundleFrames_annihilatorSpace`), and by the smooth
local frame criterion they form a `C^n` line bundle over `M`
(`TauCeti.CotangentBundle.annihilatorFiberBundle`,
`TauCeti.CotangentBundle.annihilatorVectorBundle`,
`TauCeti.CotangentBundle.annihilatorContMDiffVectorBundle`), smoothly embedded in `T*M`
(`TauCeti.CotangentBundle.isSmoothEmbedding_annihilatorInclusion`). No coorientation of `D` is
chosen: the line bundle need not be trivial.

The annihilator line of a hyperplane field `ξ` is the dual `(TM ⧸ ξ)*` of its quotient line, the
line in which the Levi form of `ξ` takes its values; for a contact structure the complement of its
zero section is the symplectization of `ξ`
(`TauCeti.Geometry.Contact.Symplectization.ContactLine`).

## Main definitions

* `TauCeti.CotangentBundle.annihilatorSpace D x`: the covectors at `x` vanishing on `D x`.
* `TauCeti.CotangentBundle.annihilatorInclusion`: the canonical map from its total space to `T*M`.
* `TauCeti.CotangentBundle.annihilatorFiberBundle`: the line bundle structure of the annihilators
  of a `C^n` hyperplane field. Install it, and the following two, locally with `letI`.

## Main results

* `TauCeti.CotangentBundle.annihilatorSpace_eq_span_singleton`: the annihilator of the kernel of a
  covector is the line it spans.
* `TauCeti.CotangentBundle.hasLocalContMDiffSubbundleFrames_annihilatorSpace`: the annihilators of
  a `C^n` hyperplane field have `C^n` local frames of size one.
* `TauCeti.CotangentBundle.annihilatorContMDiffVectorBundle`: they form a `C^n` line bundle.
* `TauCeti.CotangentBundle.isSmoothEmbedding_annihilatorInclusion`: its inclusion into `T*M` is a
  `C^n` smooth embedding.
* `TauCeti.CotangentBundle.exists_degreeOneEquiv_eq_of_mem_annihilatorSpace`: on a Hausdorff
  manifold, every nonzero covector annihilating a smooth hyperplane field at `x` is the value at `x`
  of a smooth one-form annihilating it everywhere and defining it near `x`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 19
  (local defining forms of distributions) and Proposition 10.32 (the local frame criterion).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008, Section 1.1
  and Appendix B (the annihilator of a hyperplane field in the cotangent bundle).
-/

public section

noncomputable section

open Bundle Function Manifold Module Set Topology
open scoped Manifold ContDiff

namespace TauCeti.CotangentBundle

section

variable {P : Type*} {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {D : Π x : M, Submodule 𝕜 (TangentSpace I x)}

/-! ### The annihilator spaces -/

variable (D) in
/-- The annihilator of a distribution `D` at `x`: the covectors at `x` vanishing on `D x`. -/
def annihilatorSpace (x : M) : Submodule 𝕜 (TangentSpace I x →L[𝕜] 𝕜) :=
  StrongDual.polarSubmodule 𝕜 (D x)

/-- A covector at `x` lies in the annihilator of `D` exactly when it vanishes on `D x`. -/
@[simp]
theorem mem_annihilatorSpace_iff {x : M} {c : TangentSpace I x →L[𝕜] 𝕜} :
    c ∈ annihilatorSpace D x ↔ ∀ v ∈ D x, c v = 0 := by
  rw [annihilatorSpace, ← SetLike.mem_coe, StrongDual.polarSubmodule_eq_setOfPred]
  rfl

/-- A covector at `x` lies in the annihilator of `D` exactly when its kernel contains `D x`. -/
theorem mem_annihilatorSpace_iff_le_ker {x : M} {c : TangentSpace I x →L[𝕜] 𝕜} :
    c ∈ annihilatorSpace D x ↔ D x ≤ LinearMap.ker c.toLinearMap :=
  mem_annihilatorSpace_iff

/-- **The annihilator of a hyperplane is a line.** If `D x` is the kernel of the covector `a`, the
annihilator of `D` at `x` is the line spanned by `a`. -/
theorem annihilatorSpace_eq_span_singleton {x : M} {a : TangentSpace I x →L[𝕜] 𝕜}
    (ha : LinearMap.ker a.toLinearMap = D x) :
    annihilatorSpace D x = Submodule.span 𝕜 {a} := by
  refine le_antisymm (fun c hc ↦ ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)
  · rw [mem_annihilatorSpace_iff_le_ker, ← ha] at hc
    by_cases ha0 : a = 0
    · subst ha0
      have hc0 : c = 0 := ContinuousLinearMap.ext fun v ↦ hc (by simp)
      simp [hc0]
    · -- A covector vanishing on `ker a` is the multiple `(c u / a u) • a`, for any `a u ≠ 0`.
      obtain ⟨u, hu⟩ : ∃ u, a u ≠ 0 := by
        by_contra! h
        exact ha0 (ContinuousLinearMap.ext h)
      refine Submodule.mem_span_singleton.2 ⟨c u / a u, ContinuousLinearMap.ext fun v ↦ ?_⟩
      have hv : v - (a v / a u) • u ∈ LinearMap.ker a.toLinearMap := by
        simp [map_sub, map_smul, div_mul_cancel₀ _ hu]
      have hcv := hc hv
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, map_smul,
        smul_eq_mul, sub_eq_zero] at hcv
      rw [smul_apply, smul_eq_mul, hcv]
      field_simp
  · rw [mem_annihilatorSpace_iff_le_ker, ha]

/-! ### Canonical inclusion into the cotangent bundle -/

section Inclusion

variable (P D)

/-- The canonical map from the total space of the annihilators of `D` into `T*M`, sending `(x, c)`
with `c ∈ annihilatorSpace D x` to `(x, c)`. The model-fibre parameter `P` of `Bundle.TotalSpace`
plays no role. -/
def annihilatorInclusion (z : TotalSpace P fun x ↦ annihilatorSpace D x) : CotangentBundle I M :=
  ⟨z.proj, z.2⟩

/-- `annihilatorInclusion` lies over the identity of `M`. -/
@[simp]
theorem annihilatorInclusion_proj (z : TotalSpace P fun x ↦ annihilatorSpace D x) :
    (annihilatorInclusion P D z).proj = z.proj := (rfl)

/-- `annihilatorInclusion` keeps the covector. -/
@[simp]
theorem annihilatorInclusion_snd (z : TotalSpace P fun x ↦ annihilatorSpace D x) :
    (annihilatorInclusion P D z).2 = (z.2 : TangentSpace I z.proj →L[𝕜] 𝕜) := (rfl)

/-- `annihilatorInclusion` sends `(x, c)` to `(x, c)`. -/
theorem annihilatorInclusion_apply (z : TotalSpace P fun x ↦ annihilatorSpace D x) :
    annihilatorInclusion P D z = ⟨z.proj, z.2⟩ := (rfl)

/-- `annihilatorInclusion` is injective. -/
theorem annihilatorInclusion_injective : Injective (annihilatorInclusion P D) := by
  rintro ⟨x₁, c₁⟩ ⟨x₂, c₂⟩ h
  obtain rfl : x₁ = x₂ := congrArg TotalSpace.proj h
  exact congrArg (TotalSpace.mk x₁) (Subtype.ext
    ((TotalSpace.mk_inj (F := E →L[𝕜] 𝕜) (E := fun y : M ↦ TangentSpace I y →L[𝕜] 𝕜)).mp h))

/-- The image of `annihilatorInclusion` is the set of covectors annihilating `D`. -/
@[simp]
theorem range_annihilatorInclusion :
    range (annihilatorInclusion P D) = {w | w.2 ∈ annihilatorSpace D w.proj} := by
  ext ⟨x, c⟩
  exact ⟨fun ⟨⟨_, _, hc'⟩, h⟩ ↦ h ▸ hc', fun hc ↦ ⟨⟨x, ⟨c, hc⟩⟩, rfl⟩⟩

end Inclusion

/-! ### Subbundle topology -/

section Topology

variable [IsManifold I 1 M]

variable (D) in
/-- The total space of the annihilators of `D` carries the subspace topology
(`TauCeti.subbundleTopology`) of `T*M`. The model-fibre parameter `P` of `Bundle.TotalSpace`
plays no role. -/
instance instTopologicalSpaceTotalSpaceAnnihilatorSpace :
    TopologicalSpace (TotalSpace P fun x ↦ annihilatorSpace D x) :=
  subbundleTopology (E →L[𝕜] 𝕜) (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) (annihilatorSpace D)

variable (P D) in
/-- `annihilatorInclusion` is a topological embedding of the total space of the annihilators of
`D` into `T*M`. -/
theorem isEmbedding_annihilatorInclusion : IsEmbedding (annihilatorInclusion P D) :=
  isEmbedding_totalSpace_subbundle (E →L[𝕜] 𝕜) P
    (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) (annihilatorSpace D)

variable (P D) in
/-- The bundle projection of the annihilators is continuous. -/
theorem continuous_proj_annihilatorSpace : Continuous (π P fun x ↦ annihilatorSpace D x) :=
  continuous_proj_totalSpace_subbundle (E →L[𝕜] 𝕜) P
    (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) (annihilatorSpace D)

end Topology

/-! ### Local frames and the line bundle structure -/

section VectorBundle

variable [IsRCLikeNormedField 𝕜] {m n : ℕ∞ω} [IsManifold I 1 M] [IsManifold I m M] {k : ℕ}

/-- **The annihilators of a hyperplane field have smooth local frames of size one.** For a `C^n`
distribution `D` of rank `k` with `k + 1 = dim M`, on a `C^m` manifold with `n + 1 ≤ m`, every
point has an open neighbourhood carrying a nowhere-zero `C^n` covector field with kernel `D`, and
it spans the annihilators there. -/
theorem hasLocalContMDiffSubbundleFrames_annihilatorSpace (hD : IsContMDiffDistribution I n k D)
    (hmn : n + 1 ≤ m) (hk : k + 1 = finrank 𝕜 E) :
    HasLocalContMDiffSubbundleFrames I n (E →L[𝕜] 𝕜) (Fin 1)
      (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) (annihilatorSpace D) := by
  have : IsManifold I (n + 1) M := .of_le hmn
  have : CompleteSpace 𝕜 := by let := IsRCLikeNormedField.rclike 𝕜; infer_instance
  refine hasLocalContMDiffSubbundleFrames_iff.mpr fun x ↦ ?_
  obtain ⟨U, α, hU, hxU, hα, hαD⟩ := hD.exists_local_annihilator hk x
  refine ⟨U, hU, hxU, fun _ ↦ α, ⟨fun _ ↦ hα.continuousOn, fun hy ↦ ?_, fun hy ↦ ?_⟩,
    fun _ ↦ hα⟩
  · exact linearIndependent_unique_iff.2 (hαD _ hy).1
  · rw [range_const, annihilatorSpace_eq_span_singleton (hαD _ hy).2]

/-- **The annihilator line bundle.** For a `C^n` distribution `D` of rank `k` with
`k + 1 = dim M`, on a `C^m` manifold with `n + 1 ≤ m`, the annihilators of `D` form a fibre bundle
over `M` with model fibre `Fin 1 → 𝕜`, carrying the subspace topology of `T*M`
(`TauCeti.HasLocalContMDiffSubbundleFrames.fiberBundle`). Install this definition locally with
`letI`. -/
@[instance_reducible]
def annihilatorFiberBundle (hD : IsContMDiffDistribution I n k D) (hmn : n + 1 ≤ m)
    (hk : k + 1 = finrank 𝕜 E) :
    FiberBundle (Fin 1 → 𝕜) fun x ↦ annihilatorSpace D x :=
  (hasLocalContMDiffSubbundleFrames_annihilatorSpace hD hmn hk).fiberBundle

/-- **The annihilator line bundle is a topological vector bundle.** -/
theorem annihilatorVectorBundle (hD : IsContMDiffDistribution I n k D) (hmn : n + 1 ≤ m)
    (hk : k + 1 = finrank 𝕜 E) :
    letI := annihilatorFiberBundle hD hmn hk
    VectorBundle 𝕜 (Fin 1 → 𝕜) fun x ↦ annihilatorSpace D x :=
  (hasLocalContMDiffSubbundleFrames_annihilatorSpace hD hmn hk).vectorBundle

/-- **The annihilator line bundle is a `C^n` vector bundle**, by the smooth local frame criterion
`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`. -/
theorem annihilatorContMDiffVectorBundle (hD : IsContMDiffDistribution I n k D)
    (hmn : n + 1 ≤ m) (hk : k + 1 = finrank 𝕜 E) :
    letI := annihilatorFiberBundle hD hmn hk
    letI := annihilatorVectorBundle hD hmn hk
    ContMDiffVectorBundle n (Fin 1 → 𝕜) (fun x ↦ annihilatorSpace D x) I := by
  have : IsManifold I (n + 1) M := .of_le hmn
  have : IsManifold I n M := .of_le (n := n + 1) le_self_add
  let := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := n)
  have : ∀ x : M, IsScalarTower 𝕜 𝕜 (TangentSpace I x →L[𝕜] 𝕜) := fun _ ↦ IsScalarTower.left 𝕜
  exact (hasLocalContMDiffSubbundleFrames_annihilatorSpace hD hmn hk).contMDiffVectorBundle

/-- **The inclusion of the annihilator line bundle into `T*M` is `C^n`.** -/
theorem contMDiff_annihilatorInclusion (hD : IsContMDiffDistribution I n k D) (hmn : n + 1 ≤ m)
    (hk : k + 1 = finrank 𝕜 E) :
    letI := annihilatorFiberBundle hD hmn hk
    ContMDiff (I.prod 𝓘(𝕜, Fin 1 → 𝕜)) (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) n
      (annihilatorInclusion (Fin 1 → 𝕜) D) := by
  have : IsManifold I (n + 1) M := .of_le hmn
  have : IsManifold I n M := .of_le (n := n + 1) le_self_add
  let := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := n)
  have : ∀ x : M, IsScalarTower 𝕜 𝕜 (TangentSpace I x →L[𝕜] 𝕜) := fun _ ↦ IsScalarTower.left 𝕜
  exact (hasLocalContMDiffSubbundleFrames_annihilatorSpace hD hmn hk
    ).contMDiff_totalSpace_inclusion

/-- A `C^n` map `y ↦ (b y, w y)` into `T*M` whose covectors annihilate `D` is `C^n` as a map into
the annihilator line bundle. -/
theorem contMDiffAt_annihilatorSpace_mk (hD : IsContMDiffDistribution I n k D) (hmn : n + 1 ≤ m)
    (hk : k + 1 = finrank 𝕜 E) {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
    [TopologicalSpace HX] {IX : ModelWithCorners 𝕜 EX HX} [TopologicalSpace X] [ChartedSpace HX X]
    {b : X → M} {w : ∀ y, TangentSpace I (b y) →L[𝕜] 𝕜} {y₀ : X}
    (hw : ContMDiffAt IX (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) n
      (fun y ↦ (⟨b y, w y⟩ : CotangentBundle I M)) y₀)
    (hmem : ∀ y, w y ∈ annihilatorSpace D (b y)) :
    letI := annihilatorFiberBundle hD hmn hk
    ContMDiffAt IX (I.prod 𝓘(𝕜, Fin 1 → 𝕜)) n
      (fun y ↦ (⟨b y, ⟨w y, hmem y⟩⟩ : TotalSpace (Fin 1 → 𝕜) fun x ↦ annihilatorSpace D x))
      y₀ := by
  have : IsManifold I (n + 1) M := .of_le hmn
  have : IsManifold I n M := .of_le (n := n + 1) le_self_add
  let := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := n)
  have : ∀ x : M, IsScalarTower 𝕜 𝕜 (TangentSpace I x →L[𝕜] 𝕜) := fun _ ↦ IsScalarTower.left 𝕜
  exact (hasLocalContMDiffSubbundleFrames_annihilatorSpace hD hmn hk).contMDiffAt_totalSpace_mk
    hw hmem

/-- **The annihilator line bundle of a hyperplane field is smoothly embedded in `T*M`.** For a
`C^n` distribution `D` of rank `k` with `k + 1 = dim M`, on a `C^m` manifold with `n + 1 ≤ m`, the
canonical inclusion `annihilatorInclusion` is a `C^n` smooth embedding. The manifold `M` need not
be boundaryless. -/
theorem isSmoothEmbedding_annihilatorInclusion (hD : IsContMDiffDistribution I n k D)
    (hmn : n + 1 ≤ m) (hk : k + 1 = finrank 𝕜 E) :
    letI := annihilatorFiberBundle hD hmn hk
    IsSmoothEmbedding (I.prod 𝓘(𝕜, Fin 1 → 𝕜)) (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) n
      (annihilatorInclusion (Fin 1 → 𝕜) D) := by
  have : FiniteDimensional 𝕜 E := Module.finite_of_finrank_pos (by omega)
  have : CompleteSpace 𝕜 := by let := IsRCLikeNormedField.rclike 𝕜; infer_instance
  have : IsManifold I (n + 1) M := .of_le hmn
  have : IsManifold I n M := .of_le (n := n + 1) le_self_add
  let := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := n)
  let := annihilatorFiberBundle hD hmn hk
  let := annihilatorVectorBundle hD hmn hk
  let := annihilatorContMDiffVectorBundle hD hmn hk
  exact isSmoothEmbedding_totalSpace_subbundle (F := E →L[𝕜] 𝕜) (F' := Fin 1 → 𝕜)
    (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) (V := annihilatorSpace D)
    (contMDiff_annihilatorInclusion hD hmn hk)

end VectorBundle

end

/-! ### Extending annihilating covectors to one-forms -/

section Real

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] {k : ℕ}
  {D : Π x : M, Submodule ℝ (TangentSpace I x)}

/-- **Extending an annihilating covector.** On a Hausdorff manifold, a nonzero covector `c`
vanishing on the smooth hyperplane field `D` at `x` is the value at `x` of a smooth one-form which
vanishes on `D` everywhere and has kernel exactly `D` near `x`. -/
theorem exists_degreeOneEquiv_eq_of_mem_annihilatorSpace (hD : IsContMDiffDistribution I ∞ k D)
    (hk : k + 1 = finrank ℝ E) {x : M} {c : TangentSpace I x →L[ℝ] ℝ}
    (hc : c ∈ annihilatorSpace D x) (hc0 : c ≠ 0) :
    ∃ β : SmoothForm I M ℝ 1, (∀ y, SmoothForm.degreeOneEquiv β y ∈ annihilatorSpace D y) ∧
      SmoothForm.degreeOneEquiv β x = c ∧ ∀ᶠ y in 𝓝 x, RoughForm.ker β.1 y = D y := by
  obtain ⟨α, hαs, hαD, hαx⟩ := hD.exists_isSmoothForm_ker_eq hk x
  let α' : SmoothForm I M ℝ 1 := ⟨α, hαs.mem_smoothBundleForms⟩
  have hα'D (y : M) : SmoothForm.degreeOneEquiv α' y ∈ annihilatorSpace D y :=
    mem_annihilatorSpace_iff.2 fun v hv ↦ by
      rw [SmoothForm.degreeOneEquiv_apply_apply_vec]
      exact RoughForm.mem_ker.1 (hαD y hv)
  -- The covector `c` is a nonzero multiple `s α_x`.
  have hker : LinearMap.ker (SmoothForm.degreeOneEquiv α' x :
      TangentSpace I x →L[ℝ] ℝ).toLinearMap = D x := by
    rw [← hαx.self_of_nhds.2]
    ext v
    simp [SmoothForm.degreeOneEquiv_apply_apply_vec, RoughForm.mem_ker, α']
  rw [annihilatorSpace_eq_span_singleton hker] at hc
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 hc
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hc0 (by simpa using hs.symm)
  have happly (y : M) : SmoothForm.degreeOneEquiv (s • α') y =
      s • SmoothForm.degreeOneEquiv α' y := by
    rw [LinearEquiv.map_smul, ContMDiffSection.coe_smul, Pi.smul_apply]
  refine ⟨s • α', fun y ↦ ?_, (happly x).trans hs, ?_⟩
  · rw [happly]
    exact Submodule.smul_mem _ _ (hα'D y)
  · filter_upwards [hαx] with y hy
    exact (RoughForm.ker_fun_smul (f := fun _ ↦ s) hs0).trans hy.2

end Real

end TauCeti.CotangentBundle
