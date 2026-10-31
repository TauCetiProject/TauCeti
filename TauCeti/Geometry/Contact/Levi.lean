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

## Main results

* `TauCeti.SmoothForm.exists_isDistributionFrameOn_kerDistribution`: near a point where `α` does
  not vanish, `ker α` has a `C^n` local frame of `dim E - 1` vector fields.
* `TauCeti.SmoothForm.isContMDiffDistribution_kerDistribution`: the kernel of a nowhere vanishing
  one-form is a `C^n` distribution of rank `dim E - 1`.
* `TauCeti.SmoothForm.liftQ_distributionLeviForm_kerDistribution`: `α` carries the Levi form of
  `ker α` to `dα`.
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

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {α : SmoothForm I M ℝ 1} {x : M}

/-- The covector of a one-form which is nonzero at `x` is nonzero. -/
private theorem degreeOneEquiv_ne_zero (hx : α.1 x ≠ 0) :
    (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ) ≠ 0 := fun h ↦
  hx <| ContinuousAlternatingMap.ext fun v ↦ by
    have hv : ![v 0] = v := by
      ext i
      fin_cases i
      rfl
    rw [← hv, ← degreeOneEquiv_coe_apply, h, LinearMap.zero_apply,
      ContinuousAlternatingMap.coe_zero, Pi.zero_apply]

/-- If `X` is a basis of the tangent space at `x` and `α (X j) ≠ 0`, the vectors
`X i - (α (X i) / α (X j)) X j`, `i ≠ j`, form a basis of `ker α_x`. -/
private theorem isBasis_kerDistribution [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    {X : ι → TangentSpace I x} (hX : LinearIndependent ℝ X)
    (hcard : Fintype.card ι = finrank ℝ E) {j : ι} (hj : α.1 x ![X j] ≠ 0) :
    LinearIndependent ℝ (fun i : {i // i ≠ j} ↦
        X i - (α.1 x ![X i] / α.1 x ![X j]) • X j) ∧
      Submodule.span ℝ (range fun i : {i // i ≠ j} ↦
        X i - (α.1 x ![X i] / α.1 x ![X j]) • X j) = α.kerDistribution x := by
  classical
  set c : ι → ℝ := update (fun i ↦ -(α.1 x ![X i] / α.1 x ![X j])) j 0
  have hli : LinearIndependent ℝ (fun i : {i // i ≠ j} ↦
      X i - (α.1 x ![X i] / α.1 x ![X j]) • X j) := by
    have h := (linearIndependent_add_smul_iff (v := X) (c := c) (update_self _ _ _)).2 hX
    convert h.comp Subtype.val Subtype.val_injective using 1
    ext i
    simp [c, update_of_ne i.2, sub_eq_add_neg]
  -- Read `α_x` as a linear functional `a`, whose kernel is `ker α_x`.
  set a := (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
  have ha (v : TangentSpace I x) : a v = α.1 x ![v] := degreeOneEquiv_coe_apply α x v
  have ha0 : a ≠ 0 := fun h ↦ hj (by rw [← ha, h, LinearMap.zero_apply])
  refine ⟨hli, Submodule.eq_of_le_of_finrank_eq ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_kerDistribution, ← ha, map_sub, map_smul, ha, ha, smul_eq_mul,
      div_mul_cancel₀ _ hj, sub_self]
  · have hker := Module.Dual.finrank_ker_add_one_of_ne_zero ha0
    rw [finrank_span_eq_card hli, kerDistribution_def, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq, hcard]
    -- The tangent space at `x` is the model space `E`.
    change _ + 1 = finrank ℝ E at hker
    exact Nat.sub_eq_of_eq_add hker.symm

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
    simpa [a, ← Matrix.vec_single_eq_const] using (contMDiffWithinAt_totalSpace.1 h).2
  -- Some member of the frame is not in the kernel of `α_x`.
  obtain ⟨j, hj⟩ : ∃ j, a j x ≠ 0 := by
    by_contra! h
    refine degreeOneEquiv_ne_zero hx <| (hF.toBasisAt hxe).ext fun i ↦ ?_
    rw [IsLocalFrameOn.toBasisAt_coe, degreeOneEquiv_coe_apply, LinearMap.zero_apply]
    exact h i
  -- On the open set where `α (F j) ≠ 0`, the fields `F i - (α (F i) / α (F j)) F j`, `i ≠ j`,
  -- form a frame of `ker α`; it remains to index them by `Fin (dim E - 1)`.
  let U := e.baseSet ∩ a j ⁻¹' {0}ᶜ
  have hU : IsOpen U :=
    (ha j).continuousOn.isOpen_inter_preimage e.open_baseSet isOpen_compl_singleton
  let Y : {i // i ≠ j} → Π y : M, TangentSpace I y := fun i ↦ F i - (a i / a j) • F j
  have hY {y : M} (hy : y ∈ U) := isBasis_kerDistribution (α := α) (X := (F · y))
    (hF.linearIndependent hy.1) (Fintype.card_fin _) hy.2
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
  -- Extend `u` and `v` to vector fields tangent to `ker α`, using a local frame.
  obtain ⟨U, hU, hxU, X, hX⟩ := exists_isDistributionFrameOn_kerDistribution (n := 1) hx
  have hUx := hU.mem_nhds hxU
  have hd (w : α.kerDistribution x) : MDiffAt (T% (hX.extend hxU w)) x :=
    ((hX.contMDiffOn_extend hxU w).contMDiffAt hUx).mdifferentiableAt one_ne_zero
  have hD (w : α.kerDistribution x) :
      ∀ᶠ y in 𝓝 x, hX.extend hxU w y ∈ α.kerDistribution y :=
    eventually_of_mem hUx fun _ hy ↦ hX.extend_mem hxU w hy
  have hval (w : α.kerDistribution x) : (⟨hX.extend hxU w x, (hD w).self_of_nhds⟩ :
      α.kerDistribution x) = w := Subtype.ext (hX.extend_apply_self hxU w)
  have hL := hX.distributionLeviForm_apply le_rfl hUx (hd u) (hd v) (hD u) (hD v)
  rw [hval, hval] at hL
  -- Cartan's formula for vector fields tangent to `ker α`.
  have hK (w : α.kerDistribution x) : ∀ᶠ y in 𝓝 x, hX.extend hxU w y ∈ RoughForm.ker α.1 y :=
    (hD w).mono fun _ hy ↦ RoughForm.mem_ker.2 (mem_kerDistribution.1 hy)
  have hC := RoughForm.apply_mlieBracket_eq_neg_mextDeriv (α.mdifferentiableAt x) (hd u) (hd v)
    (hK u) (hK v)
  rw [hX.extend_apply_self, hX.extend_apply_self] at hC
  rw [hL, map_neg, Submodule.mkQ_apply, Submodule.liftQ_apply, degreeOneEquiv_coe_apply, hC,
    neg_neg]

/-- **The contact condition at a point is Levi nondegeneracy.** A smooth one-form `α` is a contact
form at `x` exactly when `α_x ≠ 0` and the Levi form of `ξ = ker α` is nondegenerate at `x`: the
map `u ↦ L_ξ (u, ·)` is an isomorphism from `ξ_x` onto `Hom(ξ_x, T_x M ⧸ ξ_x)`. -/
theorem isContactFormAt_iff_bijective_distributionLeviForm [FiniteDimensional ℝ E] :
    IsContactFormAt α.1 x ↔
      α.1 x ≠ 0 ∧ Bijective (distributionLeviForm α.kerDistribution x) := by
  have hiff : IsContactFormAt α.1 x ↔ α.1 x ≠ 0 ∧ ∀ v ∈ RoughForm.ker α.1 x,
      (∀ w ∈ RoughForm.ker α.1 x, mextDeriv α.1 x ![v, w] = 0) → v = 0 :=
    ⟨fun h ↦ ⟨h.ne_zero, h.nondegenerate⟩, fun h ↦ ⟨h.1, h.2⟩⟩
  rw [hiff]
  refine and_congr_right fun hx ↦ ?_
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  set L := distributionLeviForm α.kerDistribution x
  -- `α_x` identifies the line `T_x M ⧸ ξ_x` with `ℝ`, and turns `L` into `dα_x` on `ξ_x`.
  have hzero (u v : α.kerDistribution x) : L u v = 0 ↔ mextDeriv α.1 x ![u, v] = 0 := by
    rw [← liftQ_distributionLeviForm_kerDistribution hx, map_eq_zero_iff _ <|
      LinearMap.ker_eq_bot.1 <| Submodule.ker_liftQ_eq_bot _ _ _ (kerDistribution_def α x).ge]
  have hinj : Injective L ↔ ∀ v ∈ RoughForm.ker α.1 x,
      (∀ w ∈ RoughForm.ker α.1 x, mextDeriv α.1 x ![v, w] = 0) → v = 0 := by
    simp only [injective_iff_map_eq_zero, LinearMap.ext_iff, LinearMap.zero_apply, hzero,
      Subtype.forall, Submodule.mk_eq_zero, mem_kerDistribution, RoughForm.mem_ker]
  -- Since `T_x M ⧸ ξ_x` is a line, `L` maps between spaces of the same dimension.
  have hrank : finrank ℝ (α.kerDistribution x) =
      finrank ℝ (α.kerDistribution x →ₗ[ℝ] TangentSpace I x ⧸ α.kerDistribution x) := by
    have h1 : finrank ℝ (TangentSpace I x ⧸ α.kerDistribution x) = 1 := by
      rw [kerDistribution_def]
      exact Module.Dual.finrank_quotient_ker_eq_one_of_ne_zero (degreeOneEquiv_ne_zero hx)
    rw [Module.finrank_linearMap, h1, mul_one]
  rw [← hinj]
  exact ⟨fun h ↦ ⟨h, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 h⟩,
    Bijective.injective⟩

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
