/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
import TauCeti.Geometry.Manifold.DifferentialForm.Squared

/-!
# Stable Hamiltonian structures

A **stable Hamiltonian structure** on a manifold `M` is a pair `(α, ω)` of a one-form and a closed
two-form such that, at every point `x`, the covector `α_x` is nonzero and `ω_x` is nondegenerate
on the hyperplane `ker α_x`, and such that `ker ω ⊆ ker dα`
(`TauCeti.SmoothForm.IsStableHamiltonian`). On a manifold of dimension `2 m - 1` the pointwise
condition says that `ω` has rank `2 m - 2` and `α ∧ ω ^ (m - 1)` vanishes nowhere; we use the
equivalent linear formulation `Module.Dual.IsContact` of `α_x` for `ω_x`, which needs no dimension
index. The manifold then has odd dimension
(`TauCeti.SmoothForm.IsStableHamiltonian.odd_finrank`). On an oriented manifold, positivity of
`α ∧ ω ^ (m - 1)` is a compatibility of `(α, ω)` with the orientation, which is not imposed here.

The **characteristic vector field** `R` of `(α, ω)`
(`TauCeti.SmoothForm.characteristicVectorField`) spans the kernel line of `ω`, the tangent line of
its characteristic foliation (`TauCeti.SmoothForm.characteristicFoliation`), and is normalized by
`α`. It is the unique vector field with

`α(R) = 1`, `ι_R ω = 0`,

(`TauCeti.SmoothForm.eq_characteristicVectorField_iff`), and the stability
condition `ker ω ⊆ ker dα` is the further equation `ι_R dα = 0`
(`TauCeti.SmoothForm.isStableHamiltonian_iff_mextDeriv_characteristicVectorField`). These are the
end data of the cylindrical compactness theorem of Bourgeois–Eliashberg–Hofer–Wysocki–Zehnder:
holomorphic curves in `ℝ × M` are taken for almost complex structures sending `∂_s` to `R`, and
their energy is built from `α` and `ω`.

Two cases are basic.

* For a contact form `α`, the pair `(α, dα)` is a stable Hamiltonian structure
  (`TauCeti.SmoothForm.IsContactForm.isStableHamiltonian`). Its characteristic field is by
  definition the Reeb vector field (`TauCeti.SmoothForm.reebVectorField` in
  `TauCeti.Geometry.Contact.Reeb`), whose API is the special case `ω = dα` of the one here.
* For a closed one-form `α`, the stability condition is empty: `(α, ω)` is a stable Hamiltonian
  structure as soon as `ω` is closed and nondegenerate on `ker α`
  (`TauCeti.SmoothForm.isStableHamiltonian_of_isClosed`). This is the Levi-flat case; the
  product `S¹ × Σ` with `α = dθ` and `ω` an area form on `Σ` is of this kind. On a normed space,
  constant forms give examples (`TauCeti.SmoothForm.isStableHamiltonian_const`).

## Main declarations

* `TauCeti.SmoothForm.characteristicVectorField`: the characteristic vector field of a one-form
  and a two-form.
* `TauCeti.SmoothForm.IsStableHamiltonian`: stable Hamiltonian structures.
* `TauCeti.SmoothForm.isStableHamiltonian_iff`: the elementwise statement.
* `TauCeti.SmoothForm.apply_characteristicVectorField`,
  `TauCeti.SmoothForm.interior_characteristicVectorField`,
  `TauCeti.SmoothForm.IsStableHamiltonian.interior_mextDeriv_characteristicVectorField`: the
  equations `α(R) = 1`, `ι_R ω = 0` and `ι_R dα = 0`. The first two, and the uniqueness and
  splitting statements, need only that `α_x` is contact for `ω_x`.
* `TauCeti.SmoothForm.eq_characteristicVectorField_iff`: uniqueness.
* `TauCeti.SmoothForm.isCompl_kerDistribution_span_characteristicVectorField`: the splitting
  `T_x M = ker α_x ⊕ ℝ R(x)`.
* `TauCeti.SmoothForm.IsContactForm.isStableHamiltonian`,
  `TauCeti.SmoothForm.isStableHamiltonian_of_isClosed`: the contact and Levi-flat cases.

## References

* F. Bourgeois, Y. Eliashberg, H. Hofer, K. Wysocki, E. Zehnder, *Compactness results in
  symplectic field theory*, Geom. Topol. 7 (2003), 799–888, arXiv:math/0308183, §2.1.
* K. Cieliebak, K. Mohnke, *Compactness for punctured holomorphic curves*, J. Symplectic Geom. 3
  (2005), 589–654, §2.
-/

public section

noncomputable section

open Module
open scoped Manifold

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

/-- The **characteristic vector field** of a one-form `α` and a two-form `ω`: at each point `x`,
the tangent vector `R` with `α_x(R) = 1` and `ω_x(R, w) = 0` for every `w ∈ ker α_x`, the Reeb
vector `Module.Dual.reebVector` of the covector `α_x` for the bilinear form `ω_x`. For a stable
Hamiltonian structure, or whenever `α_x` is contact for `ω_x`, it exists and is unique, and spans
the kernel of `ω` (`TauCeti.SmoothForm.eq_characteristicVectorField_iff`). -/
def characteristicVectorField (α : SmoothForm I M ℝ 1) (ω : SmoothForm I M ℝ 2) (x : M) :
    TangentSpace I x :=
  Module.Dual.reebVector (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ) (ω.bilinFormAt x)

/-- The characteristic vector field is pointwise the Reeb vector of `α_x` for `ω_x`. -/
theorem characteristicVectorField_def (α : SmoothForm I M ℝ 1) (ω : SmoothForm I M ℝ 2) (x : M) :
    α.characteristicVectorField ω x =
      Module.Dual.reebVector (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ) (ω.bilinFormAt x) :=
  (rfl)

/-- A pair `(α, ω)` of a one-form and a two-form is a **stable Hamiltonian structure** when `ω`
is closed, at every point `x` the covector `α_x` is nonzero and `ω_x` is nondegenerate on
`ker α_x`, and the kernel of `ω_x` lies in the kernel of `dα_x`. -/
structure IsStableHamiltonian (α : SmoothForm I M ℝ 1) (ω : SmoothForm I M ℝ 2) : Prop where
  /-- The two-form is closed. -/
  isClosed : ω.IsClosed
  /-- At every point, `α_x` is nonzero and `ω_x` is nondegenerate on `ker α_x`. -/
  isContact : ∀ x, Module.Dual.IsContact (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
    (ω.bilinFormAt x)
  /-- The kernel of `ω` lies in the kernel of `dα`. -/
  ker_le_ker : ∀ x, LinearMap.ker (ω.bilinFormAt x) ≤
    LinearMap.ker ((mextDerivₗ I 1 α).bilinFormAt x)

variable {α : SmoothForm I M ℝ 1} {ω : SmoothForm I M ℝ 2}

/-- The kernel condition of a stable Hamiltonian structure, elementwise: a vector `v` with
`ω(v, ·) = 0` also satisfies `dα(v, ·) = 0`. -/
theorem IsStableHamiltonian.mextDeriv_eq_zero (h : α.IsStableHamiltonian ω) {x : M}
    {v : TangentSpace I x} (hv : ∀ w, ω.val x ![v, w] = 0) (w : TangentSpace I x) :
    mextDeriv α.val x ![v, w] = 0 :=
  mem_ker_bilinFormAt_mextDerivₗ_iff.1 (h.ker_le_ker x (mem_ker_bilinFormAt_iff.2 hv)) w

/-- **Stable Hamiltonian structures, elementwise.** `(α, ω)` is a stable Hamiltonian structure
exactly when `ω` is closed, at each point `α` does not vanish and the only vector of `ker α` which
is `ω`-orthogonal to all of `ker α` is zero, and every vector `v` with `ω(v, ·) = 0` satisfies
`dα(v, ·) = 0`. -/
theorem isStableHamiltonian_iff :
    α.IsStableHamiltonian ω ↔
      ω.IsClosed ∧
        (∀ x, (∃ v : TangentSpace I x, α.val x ![v] ≠ 0) ∧
          ∀ v : TangentSpace I x, α.val x ![v] = 0 →
            (∀ w : TangentSpace I x, α.val x ![w] = 0 → ω.val x ![v, w] = 0) → v = 0) ∧
        ∀ x (v : TangentSpace I x), (∀ w, ω.val x ![v, w] = 0) →
          ∀ w, mextDeriv α.val x ![v, w] = 0 := by
  have hcontact : ∀ x, Module.Dual.IsContact (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
      (ω.bilinFormAt x) ↔ (∃ v : TangentSpace I x, α.val x ![v] ≠ 0) ∧
        ∀ v : TangentSpace I x, α.val x ![v] = 0 →
          (∀ w : TangentSpace I x, α.val x ![w] = 0 → ω.val x ![v, w] = 0) → v = 0 := fun x ↦ by
    rw [Module.Dual.isContact_iff_of_isRefl (isAlt_bilinFormAt _ x).isRefl]
    simp only [degreeOneEquiv_coe_apply, bilinFormAt_apply, SmoothBundleForm.eval₂_apply, ne_eq,
      LinearMap.ext_iff, LinearMap.zero_apply, not_forall]
  refine ⟨fun h ↦ ⟨h.isClosed, fun x ↦ (hcontact x).1 (h.isContact x),
    fun x v hv w ↦ h.mextDeriv_eq_zero hv w⟩, fun ⟨hω, hc, hker⟩ ↦
    ⟨hω, fun x ↦ (hcontact x).2 (hc x), fun x v hv ↦
      mem_ker_bilinFormAt_mextDerivₗ_iff.2 (hker x v (mem_ker_bilinFormAt_iff.1 hv))⟩⟩

/-- The one-form of a stable Hamiltonian structure vanishes nowhere. -/
theorem IsStableHamiltonian.apply_ne_zero (h : α.IsStableHamiltonian ω) (x : M) : α.val x ≠ 0 :=
  fun h0 ↦ (h.isContact x).ne_zero <| LinearMap.ext fun v ↦ by
    simp [degreeOneEquiv_coe_apply, h0]

variable [FiniteDimensional ℝ E]

/-- A manifold carrying a stable Hamiltonian structure has odd dimension. -/
theorem IsStableHamiltonian.odd_finrank (h : α.IsStableHamiltonian ω) (x : M) :
    Odd (finrank ℝ E) :=
  (h.isContact x).odd_finrank (isAlt_bilinFormAt _ x)

variable {x : M}

/-- If `α_x` is contact for `ω_x`, then `α` takes the value `1` on the characteristic vector field
at `x`. -/
@[simp]
theorem apply_characteristicVectorField
    (hc : Module.Dual.IsContact (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
      (ω.bilinFormAt x)) :
    α.val x ![α.characteristicVectorField ω x] = 1 := by
  rw [← degreeOneEquiv_coe_apply]
  exact hc.apply_reebVector

/-- If `α_x` is contact for `ω_x`, then the characteristic vector field at `x` lies in the kernel
of `ω_x`. -/
@[simp]
theorem apply_characteristicVectorField_left
    (hc : Module.Dual.IsContact (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
      (ω.bilinFormAt x)) (w : TangentSpace I x) :
    ω.val x ![α.characteristicVectorField ω x, w] = 0 :=
  mem_ker_bilinFormAt_iff.1 (hc.reebVector_mem_ker (isAlt_bilinFormAt _ x)) w

/-- If `α_x` is contact for `ω_x`, then `ω_x` vanishes when its second argument is the
characteristic vector field at `x`. -/
@[simp]
theorem apply_characteristicVectorField_right
    (hc : Module.Dual.IsContact (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
      (ω.bilinFormAt x)) (w : TangentSpace I x) :
    ω.val x ![w, α.characteristicVectorField ω x] = 0 := by
  have := hc.apply_reebVector_right (isAlt_bilinFormAt _ x) w
  rwa [bilinFormAt_apply, SmoothBundleForm.eval₂_apply] at this

/-- The equation `ι_R ω = 0` as an identity of one-forms, when `α_x` is contact for `ω_x` at every
point. -/
theorem interior_characteristicVectorField
    (hc : ∀ x, Module.Dual.IsContact (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
      (ω.bilinFormAt x)) :
    RoughForm.interior (α.characteristicVectorField ω) ω.val = 0 :=
  RoughForm.interior_eq_zero_iff.2 fun x ↦ apply_characteristicVectorField_left (hc x)

/-- **Characterization of the characteristic vector field**: if `α_x` is contact for `ω_x`, then
`R(x)` is the unique tangent vector `v` with `α(v) = 1` and `ι_v ω = 0`. -/
theorem eq_characteristicVectorField_iff
    (hc : Module.Dual.IsContact (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
      (ω.bilinFormAt x)) {v : TangentSpace I x} :
    v = α.characteristicVectorField ω x ↔
      α.val x ![v] = 1 ∧ ∀ w : TangentSpace I x, ω.val x ![v, w] = 0 := by
  rw [characteristicVectorField_def, hc.eq_reebVector_iff_of_isAlt (isAlt_bilinFormAt _ x),
    degreeOneEquiv_coe_apply, LinearMap.ext_iff]
  simp only [bilinFormAt_apply, SmoothBundleForm.eval₂_apply, LinearMap.zero_apply]

/-- If `α_x` is contact for `ω_x`, then the kernel of `ω_x` is the line spanned by the
characteristic vector field at `x`. -/
theorem ker_bilinFormAt_eq_span_characteristicVectorField
    (hc : Module.Dual.IsContact (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
      (ω.bilinFormAt x)) :
    LinearMap.ker (ω.bilinFormAt x) = ℝ ∙ α.characteristicVectorField ω x :=
  hc.ker_eq_span_reebVector (isAlt_bilinFormAt _ x)

/-- If `α_x` is contact for `ω_x`, then the characteristic vector field does not vanish at `x`. -/
theorem characteristicVectorField_ne_zero
    (hc : Module.Dual.IsContact (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
      (ω.bilinFormAt x)) :
    α.characteristicVectorField ω x ≠ 0 :=
  hc.reebVector_ne_zero

/-- If `α_x` is contact for `ω_x`, then the characteristic vector field at `x` is transverse to
the hyperplane `ker α_x`. -/
theorem characteristicVectorField_notMem_kerDistribution
    (hc : Module.Dual.IsContact (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
      (ω.bilinFormAt x)) :
    α.characteristicVectorField ω x ∉ α.kerDistribution x := by
  rw [kerDistribution_def]
  exact hc.reebVector_notMem_ker

/-- If `α_x` is contact for `ω_x`, then the tangent space splits as the hyperplane `ker α` plus the
characteristic line, `T_x M = ker α_x ⊕ ℝ R(x)`. -/
theorem isCompl_kerDistribution_span_characteristicVectorField
    (hc : Module.Dual.IsContact (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
      (ω.bilinFormAt x)) :
    IsCompl (α.kerDistribution x) (ℝ ∙ α.characteristicVectorField ω x) := by
  rw [kerDistribution_def]
  exact hc.isCompl_ker_span_reebVector

/-- The characteristic vector field of a stable Hamiltonian structure lies in the kernel of
`dα`. -/
@[simp]
theorem IsStableHamiltonian.mextDeriv_characteristicVectorField_left
    (h : α.IsStableHamiltonian ω) (x : M) (w : TangentSpace I x) :
    mextDeriv α.val x ![α.characteristicVectorField ω x, w] = 0 :=
  h.mextDeriv_eq_zero (apply_characteristicVectorField_left (h.isContact x)) w

/-- The characteristic vector field of a stable Hamiltonian structure lies in the kernel of `dα`:
`dα` vanishes when its second argument is the characteristic vector field. -/
@[simp]
theorem IsStableHamiltonian.mextDeriv_characteristicVectorField_right
    (h : α.IsStableHamiltonian ω) (x : M) (w : TangentSpace I x) :
    mextDeriv α.val x ![w, α.characteristicVectorField ω x] = 0 := by
  have := h.mextDeriv_characteristicVectorField_left x w
  rw [mextDeriv_eq_bilinFormAt] at this ⊢
  rw [← (isAlt_bilinFormAt _ x).neg_eq, this, neg_zero]

/-- The equation `ι_R dα = 0` as an identity of one-forms. -/
theorem IsStableHamiltonian.interior_mextDeriv_characteristicVectorField
    (h : α.IsStableHamiltonian ω) :
    (mextDeriv α.val).interior (α.characteristicVectorField ω) = 0 :=
  RoughForm.interior_eq_zero_iff.2 h.mextDeriv_characteristicVectorField_left

/-- **Stable Hamiltonian structures via the characteristic vector field.** `(α, ω)` is a stable
Hamiltonian structure exactly when `ω` is closed, `α_x` is contact for `ω_x` at every point, and
the characteristic vector field satisfies `ι_R dα = 0`. -/
theorem isStableHamiltonian_iff_mextDeriv_characteristicVectorField :
    α.IsStableHamiltonian ω ↔
      ω.IsClosed ∧
        (∀ x, Module.Dual.IsContact (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
          (ω.bilinFormAt x)) ∧
        ∀ x (w : TangentSpace I x), mextDeriv α.val x ![α.characteristicVectorField ω x, w] = 0
            := by
  refine ⟨fun h ↦ ⟨h.isClosed, h.isContact, h.mextDeriv_characteristicVectorField_left⟩,
    fun ⟨hω, hc, hR⟩ ↦ ⟨hω, hc, fun x v hv ↦ ?_⟩⟩
  rw [ker_bilinFormAt_eq_span_characteristicVectorField (hc x)] at hv
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hv
  exact Submodule.smul_mem _ t (mem_ker_bilinFormAt_mextDerivₗ_iff.2 (hR x))

omit [FiniteDimensional ℝ E] in
/-- **The contact case.** For a contact form `α`, the pair `(α, dα)` is a stable Hamiltonian
structure. Its characteristic vector field is the Reeb vector field
(`TauCeti.SmoothForm.characteristicVectorField_mextDerivₗ`). -/
theorem IsContactForm.isStableHamiltonian (hα : α.IsContactForm) :
    α.IsStableHamiltonian (mextDerivₗ I 1 α) :=
  ⟨isClosed_mextDerivₗ α, isContactForm_def.1 hα, fun _ ↦ le_rfl⟩

omit [FiniteDimensional ℝ E] in
/-- **The Levi-flat case.** If `α` and `ω` are closed and, at every point, `α_x` is nonzero and
`ω_x` is nondegenerate on `ker α_x`, then `(α, ω)` is a stable Hamiltonian structure. -/
theorem isStableHamiltonian_of_isClosed (hα : α.IsClosed) (hω : ω.IsClosed)
    (h : ∀ x, Module.Dual.IsContact (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
      (ω.bilinFormAt x)) :
    α.IsStableHamiltonian ω :=
  ⟨hω, h, fun x v _ ↦ mem_ker_bilinFormAt_mextDerivₗ_iff.2 fun w ↦ by
    simp [(isClosed_def α).1 hα]⟩

omit [FiniteDimensional ℝ E] in
/-- **Constant stable Hamiltonian structures.** On a normed space, a constant one-form `a` and a
constant two-form `b` form a stable Hamiltonian structure as soon as `a` does not vanish and `b`
is nondegenerate on `ker a`. -/
theorem isStableHamiltonian_const {a : E [⋀^Fin 1]→L[ℝ] ℝ} {b : E [⋀^Fin 2]→L[ℝ] ℝ}
    (ha : ∃ v, a ![v] ≠ 0)
    (hb : ∀ v, a ![v] = 0 → (∀ w, a ![w] = 0 → b ![v, w] = 0) → v = 0) :
    (const a).IsStableHamiltonian (const b) := by
  have hvec : ∀ (x : E) {k : ℕ} (u : Fin k → TangentSpace 𝓘(ℝ, E) x),
      (fun i ↦ NormedSpace.fromTangentSpace x (u i)) = u := fun x _ u ↦
    funext fun i ↦ NormedSpace.fromTangentSpace_apply x (u i)
  refine isStableHamiltonian_iff.2 ⟨isClosed_const b, fun x ↦ ?_, fun x v _ w ↦ ?_⟩
  · simp only [const_apply, hvec]
    exact ⟨ha, hb⟩
  · simp [(isClosed_def _).1 (isClosed_const a)]

end SmoothForm

end TauCeti
