/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Current.TestForm
public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution.Support
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Squared
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.Geometry.Manifold.VectorBundle.Section.LocalOperator
import TauCeti.Topology.Algebra.Module.Spaces.CompactConvergenceCLM

/-!
# The exterior derivative of test forms and the boundary of currents

Let `M` be a smooth boundaryless manifold, Hausdorff and Lindelöf, modelled on a
finite-dimensional real space. The exterior derivative of differential forms (`TauCeti.mextDeriv`)
is local and does not enlarge supports, so it acts on the test forms of `M`
(`TauCeti.TestForm`): `TauCeti.TestForm.extDerivCLM` sends a test `k`-form to the test
`(k + 1)`-form whose underlying differential form (`TauCeti.TestForm.formEquiv`) is the exterior
derivative of the underlying form of the original one
(`TauCeti.TestForm.formEquiv_extDerivCLM_apply`). It is continuous for the test topologies, since
every local operator on sections is (`TauCeti.BundleTest.localOperatorCLM`), and it squares to zero
(`TauCeti.TestForm.extDerivCLM_comp_extDerivCLM`).

The **boundary** of a `(k + 1)`-current `T` is the `k`-current `∂T = T ∘ d`
(`TauCeti.Current.boundaryCLM`), with no additional sign. It is a continuous linear map for the
topologies of uniform convergence on compact sets of tests, it satisfies `∂ ∘ ∂ = 0`
(`TauCeti.Current.boundaryCLM_comp_boundaryCLM`), and it is local: a current vanishing on a set has
boundary vanishing there (`TauCeti.Current.isVanishingOn_boundaryCLM`), so
`supp ∂T ⊆ supp T` (`TauCeti.Current.dsupport_boundaryCLM_subset`). None of this needs an
orientation or a metric.

In a chart the pointwise formula reads as the flat exterior derivative of the coordinate
expression, through `TauCeti.mextDeriv_eq_extDeriv_inChartAt`; in degree zero it is the manifold
derivative of the underlying function (`TauCeti.TestForm.formEquiv_extDerivCLM_apply_finZero`).

For a smooth function `ρ`, exterior multiplication by `dρ` acts on test forms
(`TauCeti.TestForm.extDerivWedgeCLM`), and the Leibniz rule `d (ρ s) = dρ ∧ s + ρ ds` holds
(`TauCeti.TestForm.extDerivCLM_smulLeftCLM`). Its transpose is the interior product
`T⌞dρ : s ↦ T (dρ ∧ s)` of a current (`TauCeti.Current.extDerivWedgeDualCLM`), and the boundary
of the product `ρ T` of a current with `ρ` (`TauCeti.BundleTest.smulLeftDualCLM`) is
`∂(ρ T) = ρ ∂T - T⌞dρ` (`TauCeti.Current.boundaryCLM_smulLeftDualCLM`).

## Main definitions

* `TauCeti.TestForm.extDerivCLM`: the exterior derivative of test forms.
* `TauCeti.TestForm.extDerivWedgeCLM`: exterior multiplication of test forms by `dρ`.
* `TauCeti.Current.boundaryCLM`: the boundary of currents, `∂T = T ∘ d`.
* `TauCeti.Current.extDerivWedgeDualCLM`: the interior product `T⌞dρ` of a current.

## References

* G. de Rham, *Variétés différentiables*, Hermann, 1955, Chapter III (the boundary of a current
  on a manifold as the transpose of the exterior derivative).
* H. Federer, *Geometric Measure Theory*, Springer, 1969, §4.1.7 (the boundary `∂T = T ∘ d`, the
  interior product `T⌞φ` and the formula for the boundary of `ρ T`).
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology CompactConvergenceCLM

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {k : ℕ}

namespace TestForm

/-! ### Local operators on smooth forms acting on test forms -/

omit [FiniteDimensional ℝ E] in
/-- A linear map of smooth forms, acting on the smooth sections of the bundles of forms. -/
private def sectionMap {l : ℕ} (P : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ l) :
    Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; E [⋀^Fin l]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin l]→L[ℝ] ℝ⟯ where
  toFun s := SmoothBundleForm.toContMDiffSection (P (SmoothBundleForm.ofContMDiffSection s))
  map_add' s t := by
    rw [SmoothBundleForm.ofContMDiffSection_add, map_add,
      SmoothBundleForm.add_toContMDiffSection]
  map_smul' c s := by
    rw [SmoothBundleForm.ofContMDiffSection_smul, map_smul,
      SmoothBundleForm.smul_toContMDiffSection, RingHom.id_apply]

omit [FiniteDimensional ℝ E] in
private theorem sectionMap_apply {l : ℕ} (P : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ l)
    (s : Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ⟯) (x : M) :
    sectionMap P s x = (P (SmoothBundleForm.ofContMDiffSection s)).val x := by
  rw [sectionMap, LinearMap.coe_mk, AddHom.coe_mk, SmoothBundleForm.toContMDiffSection_apply]

variable [I.Boundaryless] [T2Space M] [LindelofSpace M]

/-- A local linear map of smooth forms, acting on test forms through `TauCeti.TestForm.formEquiv`
as a continuous linear map. -/
private def smoothFormOperatorCLM {l : ℕ} (P : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ l)
    (hP : ∀ (s : Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ⟯)
      (x : M), (∀ᶠ y in 𝓝 x, s y = 0) → (P (SmoothBundleForm.ofContMDiffSection s)).val x = 0) :
    TestForm I M k →L[ℝ] TestForm I M l :=
  formEquiv.symm.toContinuousLinearMap ∘L
    BundleTest.localOperatorCLM (sectionMap P)
      (fun s x hs ↦ by rw [sectionMap_apply]; exact hP s x hs) ∘L
    formEquiv.toContinuousLinearMap

private theorem formEquiv_smoothFormOperatorCLM_apply {l : ℕ}
    (P : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ l)
    (hP : ∀ (s : Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ⟯)
      (x : M), (∀ᶠ y in 𝓝 x, s y = 0) → (P (SmoothBundleForm.ofContMDiffSection s)).val x = 0)
    (s : TestForm I M k) (x : M) :
    formEquiv (smoothFormOperatorCLM P hP s) x = (P (SmoothBundleForm.ofContMDiffSection
      ((BundleTest.ofCompactlySupported _ _ _).symm (formEquiv s)).val)).val x := by
  simp [smoothFormOperatorCLM, sectionMap_apply]

/-! ### The exterior derivative of test forms -/

/-- The **exterior derivative of test forms**, as a continuous linear map from test `k`-forms to
test `(k + 1)`-forms. The underlying differential form of `extDerivCLM s` is the exterior
derivative of the underlying form of `s` (`TauCeti.TestForm.formEquiv_extDerivCLM_apply`). -/
def extDerivCLM : TestForm I M k →L[ℝ] TestForm I M (k + 1) :=
  smoothFormOperatorCLM (mextDerivₗ I k) fun s x hs ↦ by
    rw [mextDerivₗ_apply, SmoothBundleForm.coe_ofContMDiffSection,
      mextDeriv_congr_of_eventuallyEq (η := 0) hs, mextDeriv_zero, Pi.zero_apply]

/-- The differential form of the exterior derivative of a test form is the exterior derivative of
its differential form. -/
@[simp]
theorem formEquiv_extDerivCLM_apply (s : TestForm I M k) (x : M) :
    formEquiv (extDerivCLM s) x = mextDeriv (I := I) (F := ℝ) (⇑(formEquiv s)) x := by
  rw [extDerivCLM, formEquiv_smoothFormOperatorCLM_apply, mextDerivₗ_apply,
    SmoothBundleForm.coe_ofContMDiffSection]

/-- The differential form of the exterior derivative of a test form, as a function, is the exterior
derivative of its differential form. -/
theorem coe_formEquiv_extDerivCLM (s : TestForm I M k) :
    ⇑(formEquiv (extDerivCLM s)) = mextDeriv (I := I) (F := ℝ) (⇑(formEquiv s)) :=
  funext (formEquiv_extDerivCLM_apply s)

/-- In degree zero, the exterior derivative of a test `0`-form is the manifold derivative of its
underlying function. -/
theorem formEquiv_extDerivCLM_apply_finZero (s : TestForm I M 0) (x : M)
    (v : TangentSpace I x) :
    formEquiv (extDerivCLM s) x ![v] = mvfderiv I (fun y ↦ formEquiv s y 0) x v := by
  have h := mextDeriv_ofFunction_apply (I := I) (fun y ↦ formEquiv s y 0) x v
  rw [← RoughForm.eq_ofFunction] at h
  rw [formEquiv_extDerivCLM_apply, h, mvfderiv_apply_eq_mfderiv_apply]

/-- **`d ∘ d = 0`** on test forms. -/
@[simp]
theorem extDerivCLM_extDerivCLM (s : TestForm I M k) :
    extDerivCLM (extDerivCLM s) = 0 := by
  apply formEquiv.injective
  ext x : 1
  have hs : IsSmoothBundleForm (I := I) (F := ℝ) (V := Trivial M ℝ) (k := k) 2
      ⇑(formEquiv s) :=
    (isSmoothBundleForm_def 2 _).2
      (((BundleTest.ofCompactlySupported _ _ _).symm (formEquiv s)).val.contMDiff.of_le (by simp))
  rw [formEquiv_extDerivCLM_apply, coe_formEquiv_extDerivCLM, mextDeriv_mextDeriv _ hs, map_zero,
    Pi.zero_apply, BundleTest.zero_apply]

/-- **`d ∘ d = 0`** on test forms, as an identity of continuous linear maps. -/
@[simp]
theorem extDerivCLM_comp_extDerivCLM :
    (extDerivCLM ∘L extDerivCLM : TestForm I M k →L[ℝ] TestForm I M (k + 2)) = 0 := by
  ext s : 1
  exact extDerivCLM_extDerivCLM s

/-- The exterior derivative of a test form vanishes at every point near which the test form
vanishes. -/
theorem extDerivCLM_apply_eq_zero_of_eventually_eq_zero {s : TestForm I M k} {x : M}
    (hs : ∀ᶠ y in 𝓝 x, s y = 0) : extDerivCLM s x = 0 := by
  rw [← formEquiv_apply_eq_zero_iff, formEquiv_extDerivCLM_apply,
    mextDeriv_congr_of_eventuallyEq (η := 0) (hs.mono fun _ hy ↦ formEquiv_apply_eq_zero_iff.2 hy),
    mextDeriv_zero, Pi.zero_apply]

/-- The exterior derivative does not enlarge the support of a test form. -/
theorem tsupport_extDerivCLM_subset (s : TestForm I M k) :
    closure {x | extDerivCLM s x ≠ 0} ⊆ closure {x | s x ≠ 0} := by
  refine closure_minimal (fun x hx ↦ ?_) isClosed_closure
  by_contra h
  refine hx (extDerivCLM_apply_eq_zero_of_eventually_eq_zero ?_)
  filter_upwards [isClosed_closure.isOpen_compl.mem_nhds h] with y hy
  by_contra h'
  exact hy (subset_closure h')

/-- On a manifold of dimension at most `k`, the exterior derivative of every test `k`-form
vanishes, since there are no nonzero `(k + 1)`-forms. -/
theorem extDerivCLM_eq_zero_of_finrank_le (h : Module.finrank ℝ E ≤ k) :
    (extDerivCLM : TestForm I M k →L[ℝ] TestForm I M (k + 1)) = 0 := by
  ext s : 1
  apply formEquiv.injective
  ext x : 1
  rw [formEquiv_extDerivCLM_apply, mextDeriv_eq_zero_of_finrank_le h,
    _root_.zero_apply, map_zero, Pi.zero_apply, BundleTest.zero_apply]

/-! ### Smooth multipliers and the Leibniz rule -/

/-- **Exterior multiplication by `dρ`** on test forms, for a smooth function `ρ`, as a continuous
linear map from test `k`-forms to test `(k + 1)`-forms: the underlying differential form of
`extDerivWedgeCLM ρ s` is `dρ ∧ α` for the underlying form `α` of `s`
(`TauCeti.TestForm.formEquiv_extDerivWedgeCLM_apply`). It is the commutator of the exterior
derivative with multiplication by `ρ` (`TauCeti.TestForm.extDerivCLM_smulLeftCLM`). -/
def extDerivWedgeCLM (ρ : C^∞⟮I, M; ℝ⟯) : TestForm I M k →L[ℝ] TestForm I M (k + 1) :=
  smoothFormOperatorCLM (SmoothForm.extDerivWedgeₗ ρ k) fun s x hs ↦ by
    ext v
    rw [SmoothForm.extDerivWedgeₗ_apply, RoughForm.wedge_apply,
      SmoothBundleForm.coe_ofContMDiffSection, hs.self_of_nhds]
    simp

/-- The differential form of `dρ ∧ s` is the wedge product of `dρ` with the differential form of
`s`. The degree `0 + 1 + k` of the wedge is identified with `k + 1` by `Fin.cast`. -/
@[simp]
theorem formEquiv_extDerivWedgeCLM_apply (ρ : C^∞⟮I, M; ℝ⟯) (s : TestForm I M k) (x : M)
    (v : Fin (k + 1) → TangentSpace I x) :
    formEquiv (extDerivWedgeCLM ρ s) x v =
      (mextDeriv (RoughForm.ofFunction I ρ)).wedge (⇑(formEquiv s)) x
        (v ∘ Fin.cast (show 0 + 1 + k = k + 1 by omega)) := by
  rw [extDerivWedgeCLM, formEquiv_smoothFormOperatorCLM_apply, SmoothForm.extDerivWedgeₗ_apply,
    SmoothBundleForm.coe_ofContMDiffSection]

/-- **The Leibniz rule** `d (ρ s) = dρ ∧ s + ρ ds` for a smooth function `ρ` times a test form
`s`. -/
theorem extDerivCLM_smulLeftCLM (ρ : C^∞⟮I, M; ℝ⟯) (s : TestForm I M k) :
    extDerivCLM (BundleTest.smulLeftCLM ρ s) =
      extDerivWedgeCLM ρ s + BundleTest.smulLeftCLM ρ (extDerivCLM s) := by
  apply formEquiv.injective
  ext x v
  have h := mextDeriv_fun_smul (ρ.contMDiff.mdifferentiableAt (by simp))
    (SmoothForm.mdifferentiableAt (SmoothBundleForm.ofContMDiffSection
      ((BundleTest.ofCompactlySupported _ _ _).symm (formEquiv s)).val) x) v
  rw [SmoothBundleForm.coe_ofContMDiffSection] at h
  rw [formEquiv_extDerivCLM_apply, formEquiv_smulLeftCLM, map_add, BundleTest.add_apply,
    ContinuousAlternatingMap.add_apply, formEquiv_extDerivWedgeCLM_apply, formEquiv_smulLeftCLM,
    BundleTest.smulLeftCLM_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    formEquiv_extDerivCLM_apply]
  -- The two sides differ only in the differentiated form, `ρ s` against `y ↦ ρ y • s y`.
  convert h using 3
  funext y
  exact BundleTest.smulLeftCLM_apply ρ (formEquiv s) y

end TestForm

namespace Current

variable [I.Boundaryless] [T2Space M] [LindelofSpace M]

/-- The **boundary** of currents: a `(k + 1)`-current `T` is sent to the `k`-current
`∂T = T ∘ d`, with `d` the exterior derivative of test forms. It is continuous for the topologies
of uniform convergence on compact sets of tests. -/
def boundaryCLM : Current I M (k + 1) →L[ℝ] Current I M k :=
  TestForm.extDerivCLM.precompCompactConvergenceCLM ℝ

/-- The boundary of a current evaluates a test form at its exterior derivative. -/
@[simp]
theorem boundaryCLM_apply (T : Current I M (k + 1)) (s : TestForm I M k) :
    boundaryCLM T s = T (TestForm.extDerivCLM s) :=
  ContinuousLinearMap.precompCompactConvergenceCLM_apply_apply _ _ _

/-- **`∂ ∘ ∂ = 0`** on currents. -/
@[simp]
theorem boundaryCLM_boundaryCLM (T : Current I M (k + 2)) :
    boundaryCLM (boundaryCLM T) = 0 := by
  ext s
  rw [boundaryCLM_apply, boundaryCLM_apply, TestForm.extDerivCLM_extDerivCLM, map_zero]
  exact (_root_.zero_apply _).symm

/-- **`∂ ∘ ∂ = 0`** on currents, as an identity of continuous linear maps. -/
@[simp]
theorem boundaryCLM_comp_boundaryCLM :
    (boundaryCLM ∘L boundaryCLM : Current I M (k + 2) →L[ℝ] Current I M k) = 0 := by
  ext T : 1
  exact boundaryCLM_boundaryCLM T

/-- The boundary is local: if a current vanishes on a set, so does its boundary. -/
theorem isVanishingOn_boundaryCLM {T : Current I M (k + 1)} {U : Set M}
    (hT : BundleTest.IsVanishingOn T U) : BundleTest.IsVanishingOn (boundaryCLM T) U :=
  BundleTest.isVanishingOn_iff.2 fun s hs ↦ by
    rw [boundaryCLM_apply]
    exact BundleTest.isVanishingOn_iff.1 hT _ ((TestForm.tsupport_extDerivCLM_subset s).trans hs)

/-- The boundary of a current is supported in the support of the current. -/
theorem dsupport_boundaryCLM_subset (T : Current I M (k + 1)) :
    BundleTest.dsupport (boundaryCLM T) ⊆ BundleTest.dsupport T := by
  intro x hx
  by_contra h
  obtain ⟨U, hU, hxU, hTU⟩ := BundleTest.notMem_dsupport_iff.1 h
  exact BundleTest.notMem_dsupport_iff.2 ⟨U, hU, hxU, isVanishingOn_boundaryCLM hTU⟩ hx

/-- The **interior product** `T⌞dρ` of a `(k + 1)`-current `T` with the differential of a smooth
function `ρ`: the `k`-current `s ↦ T (dρ ∧ s)`, the transpose of exterior multiplication by `dρ`.
It is continuous for the topologies of uniform convergence on compact sets of tests. -/
def extDerivWedgeDualCLM (ρ : C^∞⟮I, M; ℝ⟯) : Current I M (k + 1) →L[ℝ] Current I M k :=
  (TestForm.extDerivWedgeCLM ρ).precompCompactConvergenceCLM ℝ

/-- The interior product `T⌞dρ` evaluates a test form `s` as `T (dρ ∧ s)`. -/
@[simp]
theorem extDerivWedgeDualCLM_apply (ρ : C^∞⟮I, M; ℝ⟯) (T : Current I M (k + 1))
    (s : TestForm I M k) :
    extDerivWedgeDualCLM ρ T s = T (TestForm.extDerivWedgeCLM ρ s) :=
  ContinuousLinearMap.precompCompactConvergenceCLM_apply_apply _ _ _

/-- **The boundary of a product with a smooth function**: `∂(ρ T) = ρ ∂T - T⌞dρ`. -/
theorem boundaryCLM_smulLeftDualCLM (ρ : C^∞⟮I, M; ℝ⟯) (T : Current I M (k + 1)) :
    boundaryCLM (BundleTest.smulLeftDualCLM ρ T) =
      BundleTest.smulLeftDualCLM ρ (boundaryCLM T) - extDerivWedgeDualCLM ρ T := by
  ext s
  simp [TestForm.extDerivCLM_smulLeftCLM]

end Current

end TauCeti
