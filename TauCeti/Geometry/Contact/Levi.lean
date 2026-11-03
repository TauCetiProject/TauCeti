/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Basic
public import TauCeti.Geometry.Manifold.Distribution.Levi
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# The Levi form of the kernel of a one-form

Let `α` be a smooth real one-form on a manifold modelled on a finite-dimensional space `E`, and let
`ξ = ker α` be its kernel distribution (`TauCeti.SmoothForm.kerDistribution`). Near a point where
`α` does not vanish, `ξ` is a smooth hyperplane field: if `X₁, …, X_m` is a local frame of the
tangent bundle and `α(X_j) ≠ 0`, the vector fields `X_i - (α(X_i) / α(X_j)) X_j`, `i ≠ j`, form
a local frame of `ξ` (`TauCeti.SmoothForm.exists_isDistributionFrameOn_kerDistribution`). In
particular the kernel of a nowhere vanishing one-form, for example of a contact form, is a smooth
distribution of rank `dim E - 1` (`TauCeti.SmoothForm.isContMDiffDistribution_kerDistribution`).

The covector `α_x` vanishes on `ξ_x`, so it descends to a linear map `T_x M ⧸ ξ_x → ℝ`, an
isomorphism when `α_x ≠ 0`. This map carries the Levi form `L_ξ (u, v) = -[U, V] mod ξ` of `ξ`
(`TauCeti.distributionLeviForm`) to the restriction of `dα_x` to `ξ_x`
(`TauCeti.SmoothForm.liftQ_distributionLeviForm_kerDistribution`). This is Cartan's formula
`dα(U, V) = U(α V) - V(α U) - α([U, V])` for vector fields `U` and `V` tangent to `ξ`, and it is
the reason for the sign in the definition of the Levi form.

Consequently a one-form is contact exactly when it vanishes nowhere and the Levi form of its
kernel is nondegenerate, in the sense that `u ↦ L_ξ (u, ·)` is an isomorphism
`ξ_x ≃ Hom(ξ_x, T_x M ⧸ ξ_x)` at every point
(`TauCeti.SmoothForm.isContactForm_iff_forall_bijective_distributionLeviForm`). Unlike the
condition on `dα`, the Levi form only depends on the hyperplane field `ξ`, so this expresses the
contact condition intrinsically in terms of the contact distribution and its line
`T M ⧸ ξ`, without a choice of defining form.

The comparison is local. For any distribution `D` with a `C¹` local frame near `x` and any rough
one-form `α`, differentiable at `x`, vanishing on `D` near `x`, the value of `α_x` on the Levi form
of `D` is `dα_x` (`TauCeti.RoughForm.apply_eq_mextDeriv_of_mkQ_eq_distributionLeviForm`). If `D`
is exactly the kernel of `α` near `x`, then `α` is a contact form at `x` exactly when `α_x ≠ 0` and
the Levi form of `D` is nondegenerate at `x`
(`TauCeti.RoughForm.isContactFormAt_iff_bijective_distributionLeviForm`). This applies to local
defining forms of a hyperplane field, which need not extend to global one-forms.

## Main results

* `TauCeti.SmoothForm.exists_isDistributionFrameOn_kerDistribution`: near a point where `α` does
  not vanish, `ker α` has a `C^n` local frame of `dim E - 1` vector fields.
* `TauCeti.SmoothForm.isContMDiffDistribution_kerDistribution`: the kernel of a nowhere vanishing
  one-form is a `C^n` distribution of rank `dim E - 1`.
* `TauCeti.SmoothForm.liftQ_distributionLeviForm_kerDistribution`: `α` carries the Levi form of
  `ker α` to `dα`.
* `TauCeti.RoughForm.apply_eq_mextDeriv_of_mkQ_eq_distributionLeviForm` and
  `TauCeti.RoughForm.isContactFormAt_iff_bijective_distributionLeviForm`: the same statements for
  a local defining form of a distribution.
* `TauCeti.SmoothForm.isContactFormAt_iff_bijective_distributionLeviForm` and
  `TauCeti.SmoothForm.isContactForm_iff_forall_bijective_distributionLeviForm`: the contact
  condition is Levi nondegeneracy of the kernel.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 1.1 (contact structures as maximally non-integrable hyperplane fields).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 19
  (local frames of distributions) and Proposition 14.29 (the invariant formula for `dα`).
-/

public section

noncomputable section

open Set Filter Function Module Bundle
open scoped Manifold Topology ContDiff

namespace TauCeti

namespace RoughForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] {α : RoughForm I M ℝ 1} {D : Π x : M, Submodule ℝ (TangentSpace I x)}
  {x : M} {ι : Type*} [Finite ι] {X : ι → Π y : M, TangentSpace I y} {U : Set M}

/-- **A one-form carries the Levi form of a distribution in its kernel to its exterior
derivative.** Let `D` have a `C¹` local frame on a neighbourhood of `x`, and let the one-form `α`
be differentiable at `x` and vanish on `D` near `x`. If `w` represents the Levi form
`L_D (u, v) = -[U, V] mod D` at `x`, then `α_x (w) = dα_x (u, v)`. Only the germ of `α` at `x`
matters, so `α` may be a local defining form of `D`. -/
theorem apply_eq_mextDeriv_of_mkQ_eq_distributionLeviForm (hX : IsDistributionFrameOn I 1 D X U)
    (hU : U ∈ 𝓝 x)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) x)
    (hDα : ∀ᶠ y in 𝓝 x, D y ≤ α.ker y) {u v : D x} {w : TangentSpace I x}
    (hw : (D x).mkQ w = distributionLeviForm D x u v) :
    α x ![w] = mextDeriv α x ![u, v] := by
  have := Fintype.ofFinite ι
  have hxU := mem_of_mem_nhds hU
  -- Extend `u` and `v` to vector fields tangent to `D` near `x`, using the frame.
  have hd (u : D x) : MDiffAt (T% (hX.extend hxU u)) x :=
    ((hX.contMDiffOn_extend hxU u).contMDiffAt hU).mdifferentiableAt one_ne_zero
  have hD (u : D x) : ∀ᶠ y in 𝓝 x, hX.extend hxU u y ∈ D y :=
    eventually_of_mem hU fun _ hy ↦ hX.extend_mem hxU u hy
  have hval (u : D x) : (⟨hX.extend hxU u x, (hD u).self_of_nhds⟩ : D x) = u :=
    Subtype.ext (hX.extend_apply_self hxU u)
  have hL := hX.distributionLeviForm_apply le_rfl hU (hd u) (hd v) (hD u) (hD v)
  rw [hval, hval, ← hw, ← map_neg, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq, sub_neg_eq_add] at hL
  -- The difference of the two representatives lies in `D x`, on which `α_x` vanishes.
  have h0 := mem_ker.1 (hDα.self_of_nhds hL)
  -- Cartan's formula for vector fields tangent to `ker α`.
  have hK (u : D x) : ∀ᶠ y in 𝓝 x, hX.extend hxU u y ∈ α.ker y :=
    (hD u).and hDα |>.mono fun _ hy ↦ hy.2 hy.1
  have hC := apply_mlieBracket_eq_neg_mextDeriv hα (hd u) (hd v) (hK u) (hK v)
  rw [hX.extend_apply_self, hX.extend_apply_self] at hC
  have hadd := (α x).toAlternatingMap.map_vecCons_add ![] w
    (VectorField.mlieBracket I (hX.extend hxU u) (hX.extend hxU v) x)
  simp only [ContinuousAlternatingMap.coe_toAlternatingMap] at hadd
  linarith [hadd, h0, hC]

/-- **The contact condition at a point is Levi nondegeneracy of any distribution the form locally
defines.** Let `D` have a `C¹` local frame on a neighbourhood of `x`, and let the one-form `α` be
differentiable at `x` with kernel `D` near `x`. Then `α` is a contact form at `x` exactly when
`α_x ≠ 0` and the Levi form of `D` is nondegenerate at `x`: the map `u ↦ L_D (u, ·)` is an
isomorphism from `D x` onto `Hom(D x, T_x M ⧸ D x)`. -/
theorem isContactFormAt_iff_bijective_distributionLeviForm [FiniteDimensional ℝ E]
    (hX : IsDistributionFrameOn I 1 D X U) (hU : U ∈ 𝓝 x)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) x)
    (hDα : ∀ᶠ y in 𝓝 x, α.ker y = D y) :
    IsContactFormAt α x ↔ α x ≠ 0 ∧ Bijective (distributionLeviForm D x) := by
  have hiff : IsContactFormAt α x ↔ α x ≠ 0 ∧ ∀ v ∈ α.ker x,
      (∀ w ∈ α.ker x, mextDeriv α x ![v, w] = 0) → v = 0 :=
    ⟨fun h ↦ ⟨h.ne_zero, h.nondegenerate⟩, fun h ↦ ⟨h.1, h.2⟩⟩
  have hDx : α.ker x = D x := hDα.self_of_nhds
  rw [hiff, hDx]
  refine and_congr_right fun hx ↦ ?_
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  set L := distributionLeviForm D x
  -- `α_x` identifies the line `T_x M ⧸ D x` with `ℝ`, and turns `L` into `dα_x` on `D x`.
  have hzero (u v : D x) : L u v = 0 ↔ mextDeriv α x ![u, v] = 0 := by
    obtain ⟨w, hw⟩ := (D x).mkQ_surjective (L u v)
    rw [← apply_eq_mextDeriv_of_mkQ_eq_distributionLeviForm hX hU hα
      (hDα.mono fun _ h ↦ h.ge) hw, ← hw, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      ← hDx, mem_ker]
  have hinj : Injective L ↔ ∀ v ∈ D x, (∀ w ∈ D x, mextDeriv α x ![v, w] = 0) → v = 0 := by
    simp only [injective_iff_map_eq_zero, LinearMap.ext_iff, LinearMap.zero_apply, hzero,
      Subtype.forall, Submodule.mk_eq_zero]
  -- Since `T_x M ⧸ D x` is a line, `L` maps between spaces of the same dimension.
  have hrank : finrank ℝ (D x) = finrank ℝ (D x →ₗ[ℝ] TangentSpace I x ⧸ D x) := by
    have h1 : finrank ℝ (TangentSpace I x ⧸ D x) = 1 := by
      -- `D x` is the kernel of the covector `v ↦ α_x (v)`, which is nonzero.
      let a : Module.Dual ℝ (TangentSpace I x) :=
        ((ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ (0 : Fin 1)).symm (α x) :
          TangentSpace I x →L[ℝ] ℝ)
      have ha : D x = LinearMap.ker a := by
        ext v
        simp [a, ← hDx, Matrix.vec_single_eq_const]
      rw [ha]
      exact Module.Dual.finrank_quotient_ker_eq_one_of_ne_zero fun h ↦
        hx (ker_eq_top_iff.1 (hDx.trans (ha.trans (LinearMap.ker_eq_top.2 h))))
    rw [Module.finrank_linearMap, h1, mul_one]
  rw [← hinj]
  exact ⟨fun h ↦ ⟨h, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 h⟩,
    Bijective.injective⟩

end RoughForm

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {α : SmoothForm I M ℝ 1} {x : M}

/-- **The kernel of a one-form is a smooth hyperplane field near a point where the form does not
vanish.** If `α_x ≠ 0`, then on an open neighbourhood of `x` the distribution `ker α` has a `C^n`
local frame of `dim E - 1` vector fields. -/
theorem exists_isDistributionFrameOn_kerDistribution [FiniteDimensional ℝ E] {n : ℕ∞ω}
    [ENat.LEInfty n] [IsManifold I (n + 1) M] (hx : α.1 x ≠ 0) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ X : Fin (finrank ℝ E - 1) → Π y : M, TangentSpace I y,
      IsDistributionFrameOn I n α.kerDistribution X U := by
  classical
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  -- A local frame `F` of the tangent bundle near `x`, from a trivialization.
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  have hxe : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  set F := e.localFrame (Module.finBasis ℝ E)
  have hF := e.isLocalFrameOn_localFrame_baseSet I n (Module.finBasis ℝ E)
  -- The coefficients `α (F i)` are `C^n` on the domain of the frame.
  set a : Fin (finrank ℝ E) → M → ℝ := fun i y ↦ α.1 y ![F i y]
  have ha (i) : ContMDiffOn I 𝓘(ℝ) n (a i) e.baseSet := fun y hy ↦ by
    have h := ((degreeOneEquiv α).contMDiff.of_le ENat.LEInfty.out).contMDiffOn.clm_bundle_apply
      (E₂ := Trivial M ℝ) (hF.contMDiffOn i) y hy
    simpa [a, ← Matrix.vec_single_eq_const] using (contMDiffWithinAt_totalSpace_iff.1 h).2
  -- Some member of the frame is not in the kernel of `α_x`.
  obtain ⟨j, hj⟩ : ∃ j, a j x ≠ 0 := by
    by_contra! h
    refine hx <| degreeOneEquiv_coe_eq_zero_iff.1 <| (hF.toBasisAt hxe).ext fun i ↦ ?_
    rw [IsLocalFrameOn.toBasisAt_coe, degreeOneEquiv_coe_apply, LinearMap.zero_apply]
    exact h i
  -- On the open set where `α (F j) ≠ 0`, the fields `F i - (α (F i) / α (F j)) F j`, `i ≠ j`,
  -- form a frame of `ker α`; it remains to index them by `Fin (dim E - 1)`.
  let U := e.baseSet ∩ a j ⁻¹' {0}ᶜ
  have hU : IsOpen U :=
    (ha j).continuousOn.isOpen_inter_preimage e.open_baseSet isOpen_compl_singleton
  let Y : {i // i ≠ j} → Π y : M, TangentSpace I y := fun i ↦ F i - (a i / a j) • F j
  -- At `y ∈ U`, the vectors `Y i y` are those of `Module.Dual.span_sub_div_smul_eq_ker` for the
  -- covector `α_y` and the basis `F · y`.
  have hY {y : M} (hy : y ∈ U) : LinearIndependent ℝ (fun i ↦ Y i y) ∧
      Submodule.span ℝ (range fun i ↦ Y i y) = α.kerDistribution y := by
    have hf (v : TangentSpace I y) := degreeOneEquiv_coe_apply α y v
    have hFy := hF.linearIndependent hy.1
    have hjy : (degreeOneEquiv α y : TangentSpace I y →ₗ[ℝ] ℝ) (F j y) ≠ 0 := by
      rw [hf]
      exact hy.2
    have h := Module.Dual.span_sub_div_smul_eq_ker _ hFy (Fintype.card_fin _) hjy
    have h' := Module.Dual.linearIndependent_sub_div_smul
      (degreeOneEquiv α y : TangentSpace I y →ₗ[ℝ] ℝ) hFy j
    simp only [hf, ← kerDistribution_def] at h h'
    exact ⟨h', h⟩
  let σ : {i // i ≠ j} ≃ Fin (finrank ℝ E - 1) := Fintype.equivFinOfCardEq <| by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
  refine ⟨U, hU, ⟨hxe, hj⟩, Y ∘ σ.symm, fun k ↦ ?_, fun hy ↦ ?_, fun hy ↦ ?_⟩
  · have hUe : U ⊆ e.baseSet := inter_subset_left
    exact ((hF.contMDiffOn _).mono hUe).sub_section
      ((((ha _).mono hUe).div₀ ((ha j).mono hUe) fun y hy ↦ hy.2).smul_section
        ((hF.contMDiffOn j).mono hUe))
  · exact (hY hy).1.comp σ.symm σ.symm.injective
  · rw [← (hY hy).2, ← σ.symm.surjective.range_comp]
    -- `Y i y` is by definition `F i y - (a i y / a j y) • F j y`.
    rfl

/-- **The kernel of a nowhere vanishing one-form is a smooth hyperplane field**: a `C^n`
distribution of rank `dim E - 1`. -/
theorem isContMDiffDistribution_kerDistribution [FiniteDimensional ℝ E] {n : ℕ∞ω}
    [ENat.LEInfty n] [IsManifold I (n + 1) M] (hα : ∀ x, α.1 x ≠ 0) :
    IsContMDiffDistribution I n (finrank ℝ E - 1) α.kerDistribution :=
  isContMDiffDistribution_iff.2 fun x ↦ exists_isDistributionFrameOn_kerDistribution (hα x)

/-- The contact distribution `ker α` of a contact form is a `C^n` distribution of rank
`dim E - 1`. -/
theorem IsContactForm.isContMDiffDistribution_kerDistribution [FiniteDimensional ℝ E]
    {n : ℕ∞ω} [ENat.LEInfty n] [IsManifold I (n + 1) M] (hα : α.IsContactForm) :
    IsContMDiffDistribution I n (finrank ℝ E - 1) α.kerDistribution :=
  SmoothForm.isContMDiffDistribution_kerDistribution fun x ↦
    (isContactForm_iff_forall_isContactFormAt.1 hα x).ne_zero

/-- **A one-form carries the Levi form of its kernel to its exterior derivative.** If `α_x ≠ 0`,
the linear map `T_x M ⧸ ker α_x → ℝ` induced by `α_x` sends the Levi form
`L(u, v) = -[U, V] mod ker α` of the distribution `ker α` to `dα_x (u, v)`. -/
theorem liftQ_distributionLeviForm_kerDistribution [FiniteDimensional ℝ E] (hx : α.1 x ≠ 0)
    (u v : α.kerDistribution x) :
    (α.kerDistribution x).liftQ (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
        (kerDistribution_def α x).le (distributionLeviForm α.kerDistribution x u v) =
      mextDeriv α.1 x ![u, v] := by
  have : IsManifold I (1 + 1) M := IsManifold.of_le (n := 2) le_rfl
  obtain ⟨U, hU, hxU, X, hX⟩ := exists_isDistributionFrameOn_kerDistribution (n := 1) hx
  obtain ⟨w, hw⟩ := (α.kerDistribution x).mkQ_surjective
    (distributionLeviForm α.kerDistribution x u v)
  rw [← hw, Submodule.mkQ_apply, Submodule.liftQ_apply, degreeOneEquiv_coe_apply]
  exact RoughForm.apply_eq_mextDeriv_of_mkQ_eq_distributionLeviForm hX (hU.mem_nhds hxU)
    (α.mdifferentiableAt x)
    (Eventually.of_forall fun _ _ hv ↦ RoughForm.mem_ker.2 (mem_kerDistribution.1 hv)) hw

/-- **The contact condition at a point is Levi nondegeneracy.** A smooth one-form `α` is a contact
form at `x` exactly when `α_x ≠ 0` and the Levi form of `ξ = ker α` is nondegenerate at `x`: the
map `u ↦ L_ξ (u, ·)` is an isomorphism from `ξ_x` onto `Hom(ξ_x, T_x M ⧸ ξ_x)`. -/
theorem isContactFormAt_iff_bijective_distributionLeviForm [FiniteDimensional ℝ E] :
    IsContactFormAt α.1 x ↔
      α.1 x ≠ 0 ∧ Bijective (distributionLeviForm α.kerDistribution x) := by
  by_cases hx : α.1 x = 0
  · exact ⟨fun h ↦ absurd hx h.ne_zero, fun h ↦ absurd hx h.1⟩
  have : IsManifold I (1 + 1) M := IsManifold.of_le (n := 2) le_rfl
  obtain ⟨U, hU, hxU, X, hX⟩ := exists_isDistributionFrameOn_kerDistribution (n := 1) hx
  exact RoughForm.isContactFormAt_iff_bijective_distributionLeviForm hX (hU.mem_nhds hxU)
    (α.mdifferentiableAt x) (Eventually.of_forall fun _ ↦ by ext; simp)

/-- **A one-form is contact exactly when the Levi form of its kernel is nondegenerate.** A smooth
one-form `α` is a contact form exactly when it vanishes nowhere and, at every point `x`, the Levi
form of `ξ = ker α` induces an isomorphism `ξ_x ≃ Hom(ξ_x, T_x M ⧸ ξ_x)`. -/
theorem isContactForm_iff_forall_bijective_distributionLeviForm [FiniteDimensional ℝ E] :
    α.IsContactForm ↔
      ∀ x, α.1 x ≠ 0 ∧ Bijective (distributionLeviForm α.kerDistribution x) := by
  rw [isContactForm_iff_forall_isContactFormAt]
  exact forall_congr' fun _ ↦ isContactFormAt_iff_bijective_distributionLeviForm

end SmoothForm

end TauCeti
