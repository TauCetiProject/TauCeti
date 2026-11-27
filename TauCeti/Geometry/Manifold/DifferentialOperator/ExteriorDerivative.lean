/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.Elliptic
public import TauCeti.Geometry.Manifold.DifferentialOperator.PrincipalSymbol.Section
public import TauCeti.Geometry.Manifold.DifferentialOperator.Section
public import TauCeti.Geometry.Manifold.DifferentialForm.Squared
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
public import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Covector

/-!
# The exterior derivative as a differential operator between form bundles

Real differential `k`-forms on a smooth manifold `M` are the smooth sections of the bundle
`Λᵏ T*M` with fibres `T_x M [⋀^Fin k]→L[ℝ] ℝ`. The exterior derivative
`d : Γ(Λᵏ T*M) → Γ(Λᵏ⁺¹ T*M)` (`TauCeti.mextDerivSection`) is the manifold exterior derivative
`TauCeti.mextDerivₗ` of smooth forms, read on these sections. This file places it in the theory of
differential operators between sections of vector bundles, in Grothendieck's sense of iterated
commutators with multiplication by smooth functions (`TauCeti.differentialOperators`), and
computes its principal symbol.

By the Leibniz rule `d (f ω) = df ∧ ω + f dω` (`TauCeti.mextDerivSection_smul_apply`), the
commutator `[d, f]` is exterior multiplication by `df`, which is linear over the smooth
functions, so `d` is a differential operator of order at most one
(`TauCeti.mextDerivSection_mem_differentialOperators_one`); in particular it does not enlarge
supports. Its principal symbol at a covector `ξ ∈ T_x*M`, in the geometric convention, is
exterior multiplication by `ξ`:

`σ_geom(d)(ξ) ω = ξ ∧ ω`

(`TauCeti.sectionPrincipalSymbol_mextDerivSection_apply`), the wedge product
`ContinuousAlternatingMap.pairedWedge` of the `1`-form `ξ` with `ω`, whose degree `1 + k` is
identified with `k + 1`. In the Fourier convention, where `∂ⱼ` has symbol `i ξⱼ`, the symbol is
`i ξ ∧ ·`. Since `d ∘ d = 0` (`TauCeti.mextDerivSection_comp_mextDerivSection`) and principal
symbols multiply under composition, the symbols form a complex, `σ(d)(ξ) ∘ σ(d)(ξ) = 0`
(`TauCeti.sectionPrincipalSymbol_mextDerivSection_comp_sectionPrincipalSymbol_mextDerivSection`):
the symbol sequence of the de Rham complex.

This sequence is exact at every nonzero covector `ξ`
(`TauCeti.exact_sectionPrincipalSymbol_mextDerivSection`), so the de Rham complex is an elliptic
complex: if `ξ ∧ β = 0` and `ξ(r) = 1`, the homotopy formula
`ι_r (ξ ∧ β) + ξ ∧ ι_r β = ξ(r) β` gives `β = ξ ∧ ι_r β`. In degree `0` the symbol `c ↦ c ξ`
is injective (`TauCeti.injective_sectionPrincipalSymbol_mextDerivSection_zero`), but its image is
the line through `ξ`, so `d` on functions is elliptic exactly in dimension at most one
(`TauCeti.isSectionEllipticAt_mextDerivSection_zero_iff`): a single exterior derivative is not
elliptic in general, only the complex is.

## Main results

* `TauCeti.mextDerivSection`: the exterior derivative on smooth sections of the form bundles.
* `TauCeti.mextDerivSection_smul_apply`: the Leibniz rule `d (f ω) = df ∧ ω + f dω`.
* `TauCeti.mextDerivSection_mem_differentialOperators_one`: `d` is a differential operator of
  order at most one.
* `TauCeti.tsupport_mextDerivSection_apply_subset`: `d` does not enlarge supports.
* `TauCeti.sectionPrincipalSymbol_mextDerivSection_apply`: the principal symbol of `d` at `ξ` is
  `ξ ∧ ·`.
* `TauCeti.mextDerivSection_comp_mextDerivSection`, `TauCeti.mextDerivSection_mextDerivSection`:
  `d ∘ d = 0`, also in the applied form `d (d s) = 0`.
* `TauCeti.sectionPrincipalSymbol_mextDerivSection_comp_sectionPrincipalSymbol_mextDerivSection`:
  the principal symbols of `d` form a complex.
* `TauCeti.exact_sectionPrincipalSymbol_mextDerivSection`: this symbol complex is exact at every
  nonzero covector.
* `TauCeti.injective_sectionPrincipalSymbol_mextDerivSection_zero`: the symbol of `d` on functions
  is injective at every nonzero covector.
* `TauCeti.isSectionEllipticAt_mextDerivSection_zero_iff`: `d` on functions is elliptic exactly in
  dimension at most one.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Springer GTM 94,
  Chapter 6 (differential operators, their symbols and the de Rham complex).
* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §7, pp. 520–522.
-/

public section

noncomputable section

open Bundle Module
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {k : ℕ}

variable (I M) in
/-- **The exterior derivative** `d : Γ(Λᵏ T*M) → Γ(Λᵏ⁺¹ T*M)` on the smooth sections of the
bundles of real differential forms, whose fibre at `x` is `T_x M [⋀^Fin k]→L[ℝ] ℝ`: the manifold
exterior derivative `TauCeti.mextDerivₗ` of the corresponding smooth forms. -/
def mextDerivSection (k : ℕ) :
    Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; E [⋀^Fin (k + 1)]→L[ℝ] ℝ,
        fun x : M ↦ TangentSpace I x [⋀^Fin (k + 1)]→L[ℝ] Trivial M ℝ x⟯ where
  toFun s := (mextDerivₗ I k (SmoothBundleForm.ofContMDiffSection s)).toContMDiffSection
  map_add' s t := by
    ext x : 1
    simp
  map_smul' c s := by
    ext x : 1
    simp

/-- The value of `d s` at `x` is the manifold exterior derivative of `s` at `x`. -/
@[simp]
theorem mextDerivSection_apply
    (s : Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x⟯)
    (x : M) :
    mextDerivSection I M k s x = mextDeriv (⇑s) x := by
  simp [mextDerivSection, mextDerivₗ_apply]

/-- The section `d s` is the exterior derivative of the smooth form `s`. -/
@[simp]
theorem ofContMDiffSection_mextDerivSection
    (s : Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x⟯) :
    SmoothBundleForm.ofContMDiffSection (mextDerivSection I M k s) =
      mextDerivₗ I k (SmoothBundleForm.ofContMDiffSection s) :=
  Subtype.ext (funext fun x ↦ by
    rw [SmoothBundleForm.coe_ofContMDiffSection, mextDerivSection_apply, mextDerivₗ_apply,
      SmoothBundleForm.coe_ofContMDiffSection])

/-- `d ∘ d = 0` on the smooth sections of the form bundles. -/
@[simp]
theorem mextDerivSection_comp_mextDerivSection :
    mextDerivSection I M (k + 1) ∘ₗ mextDerivSection I M k = 0 := by
  ext s x : 2
  have hds : ⇑(mextDerivSection I M k s) = mextDeriv ⇑s := funext (mextDerivSection_apply s)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, ContMDiffSection.coe_zero, Pi.zero_apply,
    mextDerivSection_apply, hds]
  simpa using congrFun (SmoothForm.mextDeriv_mextDeriv (SmoothBundleForm.ofContMDiffSection s)) x

/-- `d (d s) = 0` for every smooth section `s` of the form bundle. -/
@[simp]
theorem mextDerivSection_mextDerivSection
    (s : Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x⟯) :
    mextDerivSection I M (k + 1) (mextDerivSection I M k s) = 0 :=
  LinearMap.congr_fun mextDerivSection_comp_mextDerivSection s

/-- **The Leibniz rule** `d (f ω) = df ∧ ω + f dω` for a smooth function `f` and a smooth section
`ω` of `Λᵏ T*M`, evaluated on tangent vectors: `df ∧ ω` is the wedge of the `1`-form
`(df)ₓ` with `ω(x)`, whose degree `1 + k` is identified with `k + 1`. -/
theorem mextDerivSection_smul_apply (f : C^∞⟮I, M; ℝ⟯)
    (s : Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x⟯)
    (x : M) (v : Fin (k + 1) → TangentSpace I x) :
    mextDerivSection I M k (f • s) x v =
      ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
          (ContinuousLinearMap.mul ℝ ℝ).continuous₂
          (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ (0 : Fin 1)
            (mvfderiv I f x)) (s x) (v ∘ Fin.cast (Nat.add_comm 1 k)) +
        f x * mextDerivSection I M k s x v := by
  have h := SmoothForm.mextDerivₗ_funSMulₗ_apply f (SmoothBundleForm.ofContMDiffSection s) x v
  rw [RoughForm.wedge_def, RoughForm.wedgeWith_apply', mextDeriv_ofFunction] at h
  simpa [mextDerivₗ_apply, ContMDiffSection.coe_smul_contMDiffMap, Pi.smul_def'] using h

variable (I M k) in
/-- **The exterior derivative is a differential operator of order at most one**: by the Leibniz
rule, its commutator with multiplication by a smooth function `f` is exterior multiplication by
`df`, which is linear over the smooth functions. -/
theorem mextDerivSection_mem_differentialOperators_one :
    mextDerivSection I M k ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯
      Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x⟯
      Cₛ^∞⟮I; E [⋀^Fin (k + 1)]→L[ℝ] ℝ,
        fun x : M ↦ TangentSpace I x [⋀^Fin (k + 1)]→L[ℝ] Trivial M ℝ x⟯ 1 := by
  refine mem_differentialOperators_succ_iff.2 fun a ↦
    mem_differentialOperators_zero_iff.2 fun b s ↦ ContMDiffSection.ext fun x ↦ ?_
  ext v
  simp only [smulCommutator_apply_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContMDiffSection.smul_apply, ContinuousAlternatingMap.sub_apply,
    ContinuousAlternatingMap.smul_apply, mextDerivSection_smul_apply, smul_eq_mul,
    ContinuousAlternatingMap.pairedWedge_smul_right]
  ring

/-- The exterior derivative does not enlarge supports. -/
theorem tsupport_mextDerivSection_apply_subset [FiniteDimensional ℝ E] [T2Space M]
    (s : Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x⟯) :
    (mextDerivSection I M k s).tsupport ⊆ s.tsupport :=
  tsupport_differentialOperators_section_apply_subset
    (mextDerivSection_mem_differentialOperators_one I M k) s

section PrincipalSymbol

variable [FiniteDimensional ℝ E] [T2Space M] {x : M}

/-- **The principal symbol of the exterior derivative** at a covector `ξ ∈ T_x*M` is exterior
multiplication by `ξ`, `σ_geom(d)(ξ) α = ξ ∧ α`: the wedge of the `1`-form `ξ` with `α`, whose
degree `1 + k` is identified with `k + 1`. -/
@[simp]
theorem sectionPrincipalSymbol_mextDerivSection_apply (hx : I.IsInteriorPoint x)
    (ξ : TangentSpace I x →L[ℝ] ℝ) (α : TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x)
    (v : Fin (k + 1) → TangentSpace I x) :
    sectionPrincipalSymbol I hx
        ⟨mextDerivSection I M k, mextDerivSection_mem_differentialOperators_one I M k⟩ ξ α v =
      ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
          (ContinuousLinearMap.mul ℝ ℝ).continuous₂
          (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ (0 : Fin 1) ξ) α
          (v ∘ Fin.cast (Nat.add_comm 1 k)) := by
  obtain ⟨f, rfl⟩ : ∃ f : C^∞⟮I, M; ℝ⟯, mvfderiv I f x = ξ := ⟨_, mvfderiv_covectorLift hx ξ⟩
  obtain ⟨s, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I)
    (F := E [⋀^Fin k]→L[ℝ] ℝ)
    (V := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M ℝ y) ∞ x α
  rw [ContMDiffSection.evalLinearMap_apply, sectionPrincipalSymbol_mvfderiv_of_order_one]
  simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
    mextDerivSection_smul_apply, smul_eq_mul, add_sub_cancel_right]

/-- **The symbols of the de Rham complex form a complex**: since `d ∘ d = 0` and principal symbols
multiply under composition, `σ(d)(ξ) ∘ σ(d)(ξ) = 0`, that is `ξ ∧ ξ ∧ α = 0`. -/
@[simp]
theorem sectionPrincipalSymbol_mextDerivSection_comp_sectionPrincipalSymbol_mextDerivSection
    (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx
        ⟨mextDerivSection I M (k + 1), mextDerivSection_mem_differentialOperators_one I M (k + 1)⟩
          ξ ∘ₗ
      sectionPrincipalSymbol I hx
        ⟨mextDerivSection I M k, mextDerivSection_mem_differentialOperators_one I M k⟩ ξ = 0 := by
  rw [← sectionPrincipalSymbol_comp]
  simp only [mextDerivSection_comp_mextDerivSection]
  -- The operator `⟨0, _⟩` is the zero element of the submodule of operators of order two.
  exact sectionPrincipalSymbol_zero hx ξ

/-- The principal symbol `σ(d)(ξ) α = ξ ∧ α` of the exterior derivative vanishes exactly when the
wedge `ξ ∧ α`, of degree `1 + k`, vanishes. -/
theorem sectionPrincipalSymbol_mextDerivSection_eq_zero_iff (hx : I.IsInteriorPoint x)
    (ξ : TangentSpace I x →L[ℝ] ℝ) (α : TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x) :
    sectionPrincipalSymbol I hx
        ⟨mextDerivSection I M k, mextDerivSection_mem_differentialOperators_one I M k⟩ ξ α = 0 ↔
      ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
          (ContinuousLinearMap.mul ℝ ℝ).continuous₂
          (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ (0 : Fin 1) ξ) α = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> ext u
  · simpa [Function.comp_def] using congrArg (fun φ ↦ φ (u ∘ Fin.cast (Nat.add_comm 1 k).symm)) h
  · simp [h]

/-- **The symbol sequence of the de Rham complex is exact.** At a nonzero covector `ξ ∈ T_x*M`,
the principal symbols `σ(d)(ξ) = ξ ∧ ·` of the exterior derivatives
`Γ(Λᵏ T*M) → Γ(Λᵏ⁺¹ T*M) → Γ(Λᵏ⁺² T*M)` form an exact sequence: a `(k + 1)`-covector `β` with
`ξ ∧ β = 0` is `ξ ∧ α` for a `k`-covector `α`. So the de Rham complex is an elliptic complex. -/
theorem exact_sectionPrincipalSymbol_mextDerivSection (hx : I.IsInteriorPoint x)
    {ξ : TangentSpace I x →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    Function.Exact
      (sectionPrincipalSymbol I hx
        ⟨mextDerivSection I M k, mextDerivSection_mem_differentialOperators_one I M k⟩ ξ)
      (sectionPrincipalSymbol I hx
        ⟨mextDerivSection I M (k + 1), mextDerivSection_mem_differentialOperators_one I M (k + 1)⟩
          ξ) := by
  refine fun β ↦ ⟨fun hβ ↦ ?_, ?_⟩
  · -- `ξ ∧ β = 0`, so `β = ξ ∧ ι_r β` for a vector `r` with `ξ r = 1`.
    have hw := (sectionPrincipalSymbol_mextDerivSection_eq_zero_iff hx ξ β).1 hβ
    obtain ⟨v, hv⟩ := DFunLike.ne_iff.1 hξ
    have hr : ξ ((ξ v)⁻¹ • v) = 1 := by simpa using inv_mul_cancel₀ hv
    refine ⟨ContinuousAlternatingMap.curryLeftTopological β ((ξ v)⁻¹ • v), ?_⟩
    ext w
    rw [sectionPrincipalSymbol_mextDerivSection_apply,
      ContinuousAlternatingMap.pairedWedge_curryLeftTopological_of_pairedWedge_eq_zero hw
        (by simpa using hr)]
    simp [Function.comp_def]
  · rintro ⟨α, rfl⟩
    exact LinearMap.congr_fun
      (sectionPrincipalSymbol_mextDerivSection_comp_sectionPrincipalSymbol_mextDerivSection hx ξ) α

/-- **The symbol of `d` on functions is injective.** At a nonzero covector `ξ ∈ T_x*M`, the
principal symbol `σ(d)(ξ) c = c ξ` of `d : Γ(Λ⁰ T*M) → Γ(Λ¹ T*M)` is injective. -/
theorem injective_sectionPrincipalSymbol_mextDerivSection_zero (hx : I.IsInteriorPoint x)
    {ξ : TangentSpace I x →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    Function.Injective (sectionPrincipalSymbol I hx
      ⟨mextDerivSection I M 0, mextDerivSection_mem_differentialOperators_one I M 0⟩ ξ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  have ha : ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ (0 : Fin 1) ξ ≠ 0 :=
    fun ha ↦ hξ <| ContinuousLinearMap.ext fun v ↦ by simpa using congrArg (· ![v]) ha
  exact (ContinuousAlternatingMap.pairedWedge_zeroForm_eq_zero_iff_of_ne_zero ha).1
    ((sectionPrincipalSymbol_mextDerivSection_eq_zero_iff hx ξ c).1 hc)

/-- **`d` on functions is elliptic exactly in dimension at most one.** At an interior point,
`d : Γ(Λ⁰ T*M) → Γ(Λ¹ T*M)` is elliptic exactly when `dim M ≤ 1`: its symbol `c ↦ c ξ` at a
nonzero covector `ξ` has the line through `ξ` as image, which is all of `T_x*M` only in dimension
one. For instance on `ℝ²` the symbol at `ξ = dx` misses `dy`. -/
theorem isSectionEllipticAt_mextDerivSection_zero_iff (hx : I.IsInteriorPoint x) :
    IsSectionEllipticAt
        ⟨mextDerivSection I M 0, mextDerivSection_mem_differentialOperators_one I M 0⟩ x ↔
      finrank ℝ E ≤ 1 := by
  -- `0`-covectors form a line and `1`-covectors form the dual of `E`.
  have hrank : finrank ℝ (E [⋀^Fin 0]→L[ℝ] ℝ) = 1 ∧
      finrank ℝ (E [⋀^Fin 1]→L[ℝ] ℝ) = finrank ℝ E :=
    ⟨by rw [← (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E (F := ℝ)
        (ι := Fin 0)).toLinearEquiv.finrank_eq, Module.finrank_self],
      by rw [← (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ)
        (0 : Fin 1)).toLinearEquiv.finrank_eq, ContinuousLinearMap.dual_finrank_eq]⟩
  refine ⟨fun h ↦ ?_, fun hE ↦ isSectionEllipticAt_iff.2 fun hx' ξ hξ ↦
    sectionPrincipalSymbol_bijective_of_injective ?_ hx'
      (injective_sectionPrincipalSymbol_mextDerivSection_zero hx' hξ)⟩
  · -- In positive dimension, ellipticity forces the two ranks `1` and `dim E` to agree.
    by_contra! hE
    have := Module.nontrivial_of_finrank_pos (zero_lt_one.trans hE)
    have h01 := h.finrank_eq hx
    rw [hrank.1, hrank.2] at h01
    omega
  · -- In dimension one, `0`-covectors and `1`-covectors both form lines.
    have hpos : 0 < finrank ℝ (TangentSpace I x →L[ℝ] ℝ) :=
      Module.finrank_pos_iff_exists_ne_zero.2 ⟨ξ, hξ⟩
    rw [ContinuousLinearMap.dual_finrank_eq] at hpos
    rw [hrank.1, hrank.2]
    exact (hE.antisymm hpos).symm

end PrincipalSymbol

end TauCeti
