/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Manifold
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Basic
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.NumberTheory.ModularForms.Basic

/-!
# The weight-`k` automorphy sheaf on the compactified quotient

Let `Γ ≤ PSL(2, ℝ)` be discrete, let `Γ' ≤ SL(2, ℝ)` have image in `Γ`, and let `k ∈ ℤ`. Write
`π : ℍ → X(Γ)` for the projection of the upper half-plane to the compactified quotient. This file
constructs the sheaf on `X(Γ)` of local weight-`k` automorphic forms for `Γ'`: its sections over an
open set `U` are the functions `F : ℍ → ℂ`, vanishing off `π⁻¹(U)`, such that

* `F (g • τ) = denom g τ ^ k * F τ` for every `g ∈ Γ'` and every `τ ∈ ℍ`;
* `F` is holomorphic at every point of `π⁻¹(U)`;
* `F` is bounded, in the sense of Mathlib's `OnePoint.IsBoundedAt`, at every cusp `c` of `Γ` whose
  cusp orbit lies in `U`: `F ∣[k] g` is bounded at `i∞` for every `g` with `g • ∞ = c`.

This is the predicate `Subgroup.CompactifiedQuotient.IsAutomorphySection`. Over `U = X(Γ)` these
are the `Γ'`-automorphic holomorphic functions on `ℍ` bounded at every cusp of `Γ`
(`Subgroup.CompactifiedQuotient.isAutomorphySection_univ_iff`). These are the defining conditions
of a weight-`k` modular form for `Γ'` when the cusps of `Γ` coincide with those of the projective
image of `Γ'`. The boundedness condition at a cusp
only involves `F` near the cusp (`Subgroup.CompactifiedQuotient.isBoundedAt_congr`): the
neighbourhoods of a cusp orbit in `X(Γ)` pull back to horodiscs, along which `i∞` is approached
after slashing by a lift of the scaling of a cusp datum. Suppose a cusp datum `D` represents a
cusp orbit in `U`, and its generator has a lift `g ∈ Γ'` with
`(s * g * s⁻¹) 1 1 = -1`, where `s` lifts `D.scaling` (the irregular sign). In odd weight the
expansion of a section, after slashing by `s⁻¹`, in the width parameter `q₂` then has only odd
terms, so its order at the cusp is at least `1 / 2`, in the errata convention of Diamond–Shurman
(`TauCeti.Subgroup.CuspDatum.analyticOrderAt_automorphyUntwist`).

Restriction to a smaller open set `V` multiplies by the indicator function of `π⁻¹(V)`, and the
sections form a sheaf of complex vector spaces
(`Subgroup.CompactifiedQuotient.automorphySheaf`): compatible local sections glue, because every
condition is local on `X(Γ)` once `Γ'` preserves the fibres of `π`
(`Subgroup.CompactifiedQuotient.IsAutomorphySection.of_forall_exists`).

The sheaf is a module over the holomorphic structure sheaf `𝒪` of `X(Γ)`: a holomorphic function
`φ` on `U` acts on a section by multiplication with its pullback `φ ∘ π`, which is invariant,
holomorphic on `π⁻¹(U)` and bounded near every cusp of `U`
(`Subgroup.CompactifiedQuotient.IsAutomorphySection.comp_mul`). Restriction is semilinear along the
restriction of functions, so this is a sheaf of `𝒪`-modules
(`Subgroup.CompactifiedQuotient.automorphySheafOfModules`). Its local triviality, through the
frames `Subgroup.LinearizingCoordinate.automorphyFrame` at elliptic points and
`TauCeti.Subgroup.CuspDatum.automorphyFrame` at cusps, is not part of this file.

## Main declarations

* `Subgroup.CompactifiedQuotient.IsAutomorphySection`: local weight-`k` automorphic forms on
  `π⁻¹(U)`.
* `Subgroup.CompactifiedQuotient.automorphySections`: the complex vector space of them.
* `Subgroup.CompactifiedQuotient.automorphySheaf`: the sheaf of complex vector spaces on `X(Γ)`.
* `Subgroup.CompactifiedQuotient.automorphySheafOfModules`: the same sheaf as a sheaf of modules
  over the holomorphic structure sheaf of `X(Γ)`.

## References

The sheaf-of-vector-spaces construction follows `TauCeti.RiemannSurface.divisorSheaf`.
The packaging as a sheaf of modules via `PresheafOfModules.ofPresheaf` follows
`AlgebraicGeometry.Proj.twistingSheaf`, in turn following Mathlib's
`AlgebraicGeometry.moduleStructurePresheaf`.

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §§3.1–3.6, with the corrected irregular-cusp order convention
  of the errata to pp. 74–75.
* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §§2.1, 2.6.
-/

public noncomputable section

open CategoryTheory Filter MulAction Opposite Set TopologicalSpace Topology UpperHalfPlane
open scoped ContDiff Manifold MatrixGroups ModularForm
open TauCeti (holomorphicStructureSheaf)

namespace Subgroup.CompactifiedQuotient

variable {Γ : Subgroup PSL(2, ℝ)}

/-! ### Boundedness at a cusp is local on the compactified quotient -/

section Cusp

/-- The inverse of a lift of the scaling of a cusp datum carries `∞` to the cusp. -/
private theorem mapGL_inv_smul_infty {D : Γ.CuspDatum} {s : SL(2, ℝ)}
    (hs : (s : PSL(2, ℝ)) = D.scaling) :
    Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹ • (OnePoint.infty : OnePoint ℝ) = D.cusp := by
  have h : Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹ = Matrix.SpecialLinearGroup.toGL s⁻¹ := by
    ext i j
    simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  rw [h, ← OnePoint.pslMk_smul, QuotientGroup.mk_inv, hs, inv_smul_eq_iff, D.scaling_smul_cusp]

variable [DiscreteTopology Γ] {D : Γ.CuspDatum} {s : SL(2, ℝ)}

/-- After the inverse of a lift of the scaling of a cusp datum, approaching `i∞` is approaching
the cusp orbit in the compactified quotient. -/
private theorem tendsto_ofQuotient_quotientMk_inv_smul (hs : (s : PSL(2, ℝ)) = D.scaling) :
    Tendsto (fun z : ℍ ↦ ofQuotient (Quotient.mk (orbitRel Γ ℍ) (s⁻¹ • z))) atImInfty
      (𝓝 (ofCusp D.cuspOrbit)) := by
  refine (tendsto_ofQuotient_quotientMk_nhds_ofCusp D).comp (tendsto_comap_iff.mpr ?_)
  have h : (fun z : ℍ ↦ (D.scaling • z).im) ∘ (fun z : ℍ ↦ s⁻¹ • z) = UpperHalfPlane.im := by
    funext z
    rw [Function.comp_apply, ← hs, UpperHalfPlane.pslMk_smul, smul_inv_smul]
  rw [h]
  exact tendsto_comap

/-- **Boundedness at a cusp is local.** If two functions agree on the preimage in `ℍ` of a
neighbourhood of the cusp orbit of `D` in the compactified quotient, then one is bounded at the
cusp of `D` exactly when the other is. -/
theorem isBoundedAt_congr {V : Set Γ.CompactifiedQuotient} (hV : V ∈ 𝓝 (ofCusp D.cuspOrbit))
    {F G : ℍ → ℂ} (h : ∀ τ : ℍ, ofQuotient (Quotient.mk _ τ) ∈ V → F τ = G τ) (k : ℤ) :
    OnePoint.IsBoundedAt D.cusp F k ↔ OnePoint.IsBoundedAt D.cusp G k := by
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective D.scaling
  rw [OnePoint.isBoundedAt_iff (mapGL_inv_smul_infty hs),
    OnePoint.isBoundedAt_iff (mapGL_inv_smul_infty hs)]
  have heq : F ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹ =ᶠ[atImInfty]
      G ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹ := by
    filter_upwards [tendsto_ofQuotient_quotientMk_inv_smul hs hV] with z hz
    rw [ModularForm.slash_apply, ModularForm.slash_apply, Matrix.SpecialLinearGroup.mapGL_smul,
      h _ hz]
  exact ⟨fun hF ↦ hF.congr' heq EventuallyEq.rfl, fun hG ↦ hG.congr' heq.symm EventuallyEq.rfl⟩

/-- **Multiplying by the pullback of a function continuous at a cusp preserves boundedness
there.** -/
theorem isBoundedAt_comp_mul {φ : Γ.CompactifiedQuotient → ℂ}
    (hφ : ContinuousAt φ (ofCusp D.cuspOrbit)) {F : ℍ → ℂ} {k : ℤ}
    (hF : OnePoint.IsBoundedAt D.cusp F k) :
    OnePoint.IsBoundedAt D.cusp (fun τ ↦ φ (ofQuotient (Quotient.mk _ τ)) * F τ) k := by
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective D.scaling
  rw [OnePoint.isBoundedAt_iff (mapGL_inv_smul_infty hs)] at hF ⊢
  have hdet : 0 < ((Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹ : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det := by simp
  have heq : (fun τ ↦ φ (ofQuotient (Quotient.mk _ τ)) * F τ) ∣[k]
      Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹ =
      (fun z ↦ φ (ofQuotient (Quotient.mk _ (s⁻¹ • z)))) *
        F ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹ := by
    funext z
    rw [ModularForm.slash_apply_of_det_pos k hdet, Pi.mul_apply,
      ModularForm.slash_apply_of_det_pos k hdet, Matrix.SpecialLinearGroup.mapGL_smul]
    ring
  rw [heq]
  exact Filter.BoundedAtFilter.mul
    ((hφ.tendsto.comp (tendsto_ofQuotient_quotientMk_inv_smul hs)).isBigO_one ℝ) hF

end Cusp

/-! ### Local sections -/

/-- **A local section of the weight-`k` automorphy sheaf over `U`.** A function `F : ℍ → ℂ` is a
local weight-`k` automorphic form for `Γ' ≤ SL(2, ℝ)` over a subset `U` of the compactified
quotient `X(Γ)` when it vanishes off the preimage of `U` in `ℍ`, satisfies the weight-`k`
transformation law for `Γ'`, is holomorphic on the preimage of `U`, and is bounded at every cusp
whose cusp orbit lies in `U`. -/
structure IsAutomorphySection (Γ' : _root_.Subgroup SL(2, ℝ)) (k : ℤ)
    (U : Set Γ.CompactifiedQuotient) (F : ℍ → ℂ) : Prop where
  /-- The function vanishes off the preimage of `U`. -/
  eq_zero_of_notMem : ∀ τ : ℍ, ofQuotient (Quotient.mk _ τ) ∉ U → F τ = 0
  /-- The weight-`k` transformation law for `Γ'`. -/
  apply_smul : ∀ g ∈ Γ', ∀ τ : ℍ,
    F (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * F τ
  /-- The function is holomorphic on the preimage of `U`. -/
  mdifferentiableAt : ∀ τ : ℍ, ofQuotient (Quotient.mk _ τ) ∈ U →
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F τ
  /-- The function is bounded at every cusp whose cusp orbit lies in `U`. -/
  isBoundedAt : ∀ D : Γ.CuspDatum, ofCusp D.cuspOrbit ∈ U → OnePoint.IsBoundedAt D.cusp F k

variable {Γ' : _root_.Subgroup SL(2, ℝ)} {k : ℤ} {U V : Set Γ.CompactifiedQuotient} {F G : ℍ → ℂ}

/-- An element of `Γ'` preserves the fibres of the projection to the compactified quotient when
the image of `Γ'` lies in `Γ`. -/
theorem ofQuotient_quotientMk_smul
    (hΓ : Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))) ≤ Γ) {g : SL(2, ℝ)}
    (hg : g ∈ Γ') (τ : ℍ) :
    (ofQuotient (Quotient.mk (orbitRel Γ ℍ) (g • τ)) : Γ.CompactifiedQuotient) =
      ofQuotient (Quotient.mk _ τ) :=
  congrArg ofQuotient (Quotient.sound (orbitRel_apply.mpr
    ⟨⟨_, hΓ (_root_.Subgroup.mem_map_of_mem _ hg)⟩, UpperHalfPlane.pslMk_smul g τ⟩))

/-- **The automorphy sections over the whole compactified quotient** are the holomorphic functions
on `ℍ` satisfying the weight-`k` transformation law for `Γ'` and bounded at every cusp of `Γ`.
These are the defining conditions of a weight-`k` modular form for `Γ'` when the cusps of `Γ`
coincide with those of the projective image of `Γ'`. -/
theorem isAutomorphySection_univ_iff :
    IsAutomorphySection Γ' k (univ : Set Γ.CompactifiedQuotient) F ↔
      (∀ g ∈ Γ', ∀ τ : ℍ, F (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * F τ) ∧
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧ ∀ D : Γ.CuspDatum, OnePoint.IsBoundedAt D.cusp F k :=
  ⟨fun h ↦ ⟨h.apply_smul, fun τ ↦ h.mdifferentiableAt τ trivial,
      fun D ↦ h.isBoundedAt D trivial⟩,
    fun ⟨h₁, h₂, h₃⟩ ↦ ⟨fun _ h ↦ absurd trivial h, h₁, fun τ _ ↦ h₂ τ, fun D _ ↦ h₃ D⟩⟩

namespace IsAutomorphySection

/-- The zero function is a local section. -/
theorem zero : IsAutomorphySection Γ' k U 0 where
  eq_zero_of_notMem _ _ := rfl
  apply_smul _ _ _ := by simp
  mdifferentiableAt _ _ := mdifferentiableAt_const
  isBoundedAt _ _ g _ := by
    rw [SlashAction.zero_slash]
    exact zero_form_isBoundedAtImInfty

/-- Local sections are closed under addition. -/
theorem add (hF : IsAutomorphySection Γ' k U F) (hG : IsAutomorphySection Γ' k U G) :
    IsAutomorphySection Γ' k U (F + G) where
  eq_zero_of_notMem τ hτ := by
    rw [Pi.add_apply, hF.eq_zero_of_notMem τ hτ, hG.eq_zero_of_notMem τ hτ, add_zero]
  apply_smul g hg τ := by
    rw [Pi.add_apply, Pi.add_apply, hF.apply_smul g hg, hG.apply_smul g hg, mul_add]
  mdifferentiableAt τ hτ := (hF.mdifferentiableAt τ hτ).add (hG.mdifferentiableAt τ hτ)
  isBoundedAt D hD := (hF.isBoundedAt D hD).add (hG.isBoundedAt D hD)

/-- Local sections are closed under multiplication by constants. -/
theorem const_smul (hF : IsAutomorphySection Γ' k U F) (c : ℂ) :
    IsAutomorphySection Γ' k U (c • F) where
  eq_zero_of_notMem τ hτ := by rw [Pi.smul_apply, hF.eq_zero_of_notMem τ hτ, smul_zero]
  apply_smul g hg τ := by
    rw [Pi.smul_apply, Pi.smul_apply, hF.apply_smul g hg, smul_eq_mul, smul_eq_mul]
    ring
  mdifferentiableAt τ hτ := (hF.mdifferentiableAt τ hτ).const_smul c
  isBoundedAt D hD g hg := by
    rw [ModularForm.smul_slash]
    exact Filter.BoundedAtFilter.smul _ (hF.isBoundedAt D hD g hg)

/-- **Odd weight with `-1 ∈ Γ'` has no sections.** If `-1 ∈ Γ'` and `k` is odd, the transformation
law for `-1`, which fixes every point of `ℍ` with automorphy factor `-1`, forces every local
section to vanish. -/
theorem eq_zero_of_neg_one_mem (hF : IsAutomorphySection Γ' k U F) (h : -1 ∈ Γ') (hk : Odd k) :
    F = 0 := by
  funext τ
  have hτ := hF.apply_smul (-1) h τ
  have hmap : Matrix.SpecialLinearGroup.mapGL ℝ (-1 : SL(2, ℝ)) = -1 := by
    ext i j
    simp
  rw [← Matrix.SpecialLinearGroup.mapGL_smul, hmap, UpperHalfPlane.neg_smul, one_smul,
    denom_neg, denom_one, hk.neg_one_zpow, neg_one_mul] at hτ
  exact CharZero.eq_neg_self_iff.mp hτ

variable [DiscreteTopology Γ]

/-- **Multiplication by the pullback of a holomorphic function.** If `φ` is holomorphic at every
point of `U`, then multiplying a local section over `U` by `φ ∘ π` gives a local section over `U`.
This is the action of the structure sheaf of the compactified quotient on the automorphy sheaf. -/
theorem comp_mul (hΓ : Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))) ≤ Γ)
    {φ : Γ.CompactifiedQuotient → ℂ} (hφ : ∀ x ∈ U, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) φ x)
    (hF : IsAutomorphySection Γ' k U F) :
    IsAutomorphySection Γ' k U (fun τ ↦ φ (ofQuotient (Quotient.mk _ τ)) * F τ) where
  eq_zero_of_notMem τ hτ := by rw [hF.eq_zero_of_notMem τ hτ, mul_zero]
  apply_smul g hg τ := by
    rw [ofQuotient_quotientMk_smul hΓ hg, hF.apply_smul g hg]
    ring
  mdifferentiableAt τ hτ :=
    ((hφ _ hτ).comp τ ((mdifferentiable_ofQuotient _).comp τ
      (mdifferentiable_quotientMk Γ τ))).mul (hF.mdifferentiableAt τ hτ)
  isBoundedAt D hD := isBoundedAt_comp_mul (hφ _ hD).continuousAt (hF.isBoundedAt D hD)

/-- **Restriction.** If `V ⊆ U` is open, the product of a local section over `U` with the indicator
function of the preimage of `V` is a local section over `V`. -/
theorem indicator (hΓ : Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))) ≤ Γ)
    (hF : IsAutomorphySection Γ' k U F) (hV : IsOpen V) (hVU : V ⊆ U) :
    IsAutomorphySection Γ' k V
      (((fun τ : ℍ ↦ ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ)) ⁻¹' V).indicator F) where
  eq_zero_of_notMem τ hτ := indicator_of_notMem (mem_preimage.not.2 hτ : τ ∉ _) F
  apply_smul g hg τ := by
    by_cases hτ : ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ V
    · rw [indicator_of_mem (mem_preimage.2 hτ : τ ∈ _), indicator_of_mem
        (mem_preimage.2 (by rwa [ofQuotient_quotientMk_smul hΓ hg]) : g • τ ∈ _),
        hF.apply_smul g hg]
    · rw [indicator_of_notMem (mem_preimage.not.2 hτ : τ ∉ _), indicator_of_notMem
        (mem_preimage.not.2 (by rwa [ofQuotient_quotientMk_smul hΓ hg]) : g • τ ∉ _), mul_zero]
  mdifferentiableAt τ hτ := by
    refine (hF.mdifferentiableAt τ (hVU hτ)).congr_of_eventuallyEq
      (eventuallyEq_of_mem ?_ fun σ hσ ↦ indicator_of_mem hσ F)
    exact ((continuous_ofQuotient.comp continuous_quotient_mk').isOpen_preimage V hV).mem_nhds hτ
  isBoundedAt D hD :=
    (isBoundedAt_congr (hV.mem_nhds hD)
      (fun τ hτ ↦ indicator_of_mem (mem_preimage.2 hτ : τ ∈ _) F) k).mpr
        (hF.isBoundedAt D (hVU hD))

/-- **Being a local section is local on the compactified quotient.** A function vanishing off the
preimage of `U` is a local section over `U` as soon as, near every point of `U`, it agrees on the
preimage with a local section. -/
theorem of_forall_exists
    (hΓ : Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))) ≤ Γ)
    (h₀ : ∀ τ : ℍ, ofQuotient (Quotient.mk _ τ) ∉ U → F τ = 0)
    (h : ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ G : ℍ → ℂ, IsAutomorphySection Γ' k V G ∧
      ∀ τ : ℍ, ofQuotient (Quotient.mk _ τ) ∈ V → F τ = G τ) :
    IsAutomorphySection Γ' k U F where
  eq_zero_of_notMem := h₀
  apply_smul g hg τ := by
    by_cases hτ : ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ U
    · obtain ⟨V, hV, G, hG, hFG⟩ := h _ hτ
      have hτV := mem_of_mem_nhds hV
      rw [hFG _ (by rwa [ofQuotient_quotientMk_smul hΓ hg]), hFG _ hτV, hG.apply_smul g hg]
    · rw [h₀ _ (by rwa [ofQuotient_quotientMk_smul hΓ hg]), h₀ _ hτ, mul_zero]
  mdifferentiableAt τ hτ := by
    obtain ⟨V, hV, G, hG, hFG⟩ := h _ hτ
    refine (hG.mdifferentiableAt τ (mem_of_mem_nhds hV)).congr_of_eventuallyEq
      (eventually_of_mem (U := (fun σ : ℍ ↦ ofQuotient (Quotient.mk (orbitRel Γ ℍ) σ)) ⁻¹' V)
        ?_ hFG)
    exact (continuous_ofQuotient.comp continuous_quotient_mk').continuousAt.preimage_mem_nhds hV
  isBoundedAt D hD := by
    obtain ⟨V, hV, G, hG, hFG⟩ := h _ hD
    exact (isBoundedAt_congr hV hFG k).mpr (hG.isBoundedAt D (mem_of_mem_nhds hV))

end IsAutomorphySection

/-- **The constant function `1` is a global section in weight zero**: the weight-zero automorphy
sections over the whole compactified quotient include the constant function `1`. -/
theorem isAutomorphySection_univ_one :
    IsAutomorphySection Γ' 0 (univ : Set Γ.CompactifiedQuotient) 1 := by
  refine isAutomorphySection_univ_iff.mpr ⟨fun g _ τ ↦ by simp, mdifferentiable_const, fun D ↦ ?_⟩
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective D.scaling
  rw [OnePoint.isBoundedAt_iff (mapGL_inv_smul_infty hs)]
  have hdet : 0 < ((Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹ : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det := by simp
  have h : (1 : ℍ → ℂ) ∣[(0 : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹ = Function.const ℍ 1 := by
    funext z
    rw [ModularForm.slash_apply_of_det_pos 0 hdet]
    simp
  rw [h]
  exact const_boundedAtFilter _ _

/-! ### The sheaf of complex vector spaces -/

variable (Γ' k) in
/-- The complex vector space of local weight-`k` automorphic forms for `Γ'` over `U`. -/
def automorphySections (U : Set Γ.CompactifiedQuotient) : Submodule ℂ (ℍ → ℂ) where
  carrier := {F | IsAutomorphySection Γ' k U F}
  zero_mem' := IsAutomorphySection.zero
  add_mem' := IsAutomorphySection.add
  smul_mem' c _ hF := IsAutomorphySection.const_smul hF c

@[simp]
theorem mem_automorphySections_iff :
    F ∈ automorphySections Γ' k U ↔ IsAutomorphySection Γ' k U F :=
  Iff.rfl

section Sheaf

variable [DiscreteTopology Γ]
  (hΓ : Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))) ≤ Γ)

/-- Restriction of local sections to a smaller open set: multiplication by the indicator function
of the preimage in `ℍ`. -/
private def automorphyRestrict (k : ℤ) {U V : Opens Γ.CompactifiedQuotient} (h : V ≤ U) :
    automorphySections Γ' k (U : Set Γ.CompactifiedQuotient) →ₗ[ℂ]
      automorphySections Γ' k (V : Set Γ.CompactifiedQuotient) where
  toFun F := ⟨((fun τ : ℍ ↦ ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ)) ⁻¹' V).indicator F,
    mem_automorphySections_iff.mpr (F.property.indicator hΓ V.isOpen h)⟩
  map_add' _ _ := Subtype.ext (indicator_add _ _ _)
  map_smul' c _ := Subtype.ext (indicator_const_smul _ c _)

private theorem coe_automorphyRestrict (k : ℤ) {U V : Opens Γ.CompactifiedQuotient} (h : V ≤ U)
    (F : automorphySections Γ' k (U : Set Γ.CompactifiedQuotient)) :
    (automorphyRestrict hΓ k h F : ℍ → ℂ) =
      ((fun τ : ℍ ↦ ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ)) ⁻¹' V).indicator F :=
  rfl

/-- The presheaf of complex vector spaces of local weight-`k` automorphic forms. -/
private def automorphyPresheaf (k : ℤ) :
    TopCat.Presheaf (ModuleCat.{0} ℂ) (TopCat.of Γ.CompactifiedQuotient) where
  obj U := ModuleCat.of ℂ (automorphySections Γ' k (U.unop : Set Γ.CompactifiedQuotient))
  map h := ModuleCat.ofHom (automorphyRestrict hΓ k h.unop.le)
  map_id U := by
    refine ModuleCat.hom_ext (LinearMap.ext fun F ↦ Subtype.ext (funext fun τ ↦ ?_))
    by_cases hτ : ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ (U.unop : Set Γ.CompactifiedQuotient)
    · exact indicator_of_mem (mem_preimage.2 hτ : τ ∈ _) _
    · exact (indicator_of_notMem (mem_preimage.not.2 hτ : τ ∉ _) _).trans
        (F.property.eq_zero_of_notMem τ hτ).symm
  map_comp f g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun F ↦ Subtype.ext ?_)
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      coe_automorphyRestrict, indicator_indicator, inter_eq_left.mpr (preimage_mono g.unop.le)]

include hΓ in
/-- **Local weight-`k` automorphic forms glue.** Local sections over the members of a family of
open sets which agree on the preimages of the overlaps are the restrictions of a local section over
the union. -/
private theorem exists_glue (k : ℤ) {ι : Type*} (U : ι → Opens Γ.CompactifiedQuotient)
    (f : ∀ i, automorphySections Γ' k (U i : Set Γ.CompactifiedQuotient))
    (hf : ∀ i j (τ : ℍ), ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ U i →
      ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ U j → (f i : ℍ → ℂ) τ = (f j : ℍ → ℂ) τ) :
    ∃ G ∈ automorphySections Γ' k
        ((iSup U : Opens Γ.CompactifiedQuotient) : Set Γ.CompactifiedQuotient),
      ∀ i (τ : ℍ), ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ U i → G τ = (f i : ℍ → ℂ) τ := by
  classical
  -- on the preimage of `U i` the glued function is the section over `U i`
  let G : ℍ → ℂ := fun τ ↦
    if h : ∃ i, ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ U i then (f h.choose : ℍ → ℂ) τ else 0
  have hG (i : ι) (τ : ℍ) (hi : ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ U i) :
      G τ = (f i : ℍ → ℂ) τ := by
    have h : ∃ i, ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ U i := ⟨i, hi⟩
    simp only [G, h, dite_true]
    exact hf _ _ τ h.choose_spec hi
  have hG₀ (τ : ℍ) (hτ : ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∉
      ((iSup U : Opens Γ.CompactifiedQuotient) : Set Γ.CompactifiedQuotient)) : G τ = 0 := by
    have h : ¬∃ i, ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ U i := by
      rwa [SetLike.mem_coe, Opens.mem_iSup] at hτ
    simp only [G, h, dite_false]
  refine ⟨G, IsAutomorphySection.of_forall_exists hΓ hG₀ fun x hx ↦ ?_, hG⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact ⟨U i, (U i).isOpen.mem_nhds hi, f i, (f i).property, hG i⟩

/-- Local sections over the union of a family of open sets which agree on the preimage of each
member are equal. -/
private theorem automorphySections_ext_iSup {k : ℤ} {ι : Type*}
    {U : ι → Opens Γ.CompactifiedQuotient}
    {F G : automorphySections Γ' k
      ((iSup U : Opens Γ.CompactifiedQuotient) : Set Γ.CompactifiedQuotient)}
    (h : ∀ i (τ : ℍ), ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ U i →
      (F : ℍ → ℂ) τ = (G : ℍ → ℂ) τ) : F = G := by
  refine Subtype.ext (funext fun τ ↦ ?_)
  by_cases hτ : ∃ i, ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ U i
  · obtain ⟨i, hi⟩ := hτ
    exact h i τ hi
  · have hτ' : ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∉
        ((iSup U : Opens Γ.CompactifiedQuotient) : Set Γ.CompactifiedQuotient) := by
      rwa [SetLike.mem_coe, Opens.mem_iSup]
    rw [F.property.eq_zero_of_notMem τ hτ', G.property.eq_zero_of_notMem τ hτ']

/-- **The automorphy presheaf satisfies the sheaf condition**, in the form of unique gluing. -/
private theorem isSheafUniqueGluing_automorphyPresheaf (k : ℤ) :
    TopCat.Presheaf.IsSheafUniqueGluing (automorphyPresheaf hΓ k ⋙ forget (ModuleCat ℂ)) := by
  intro ι U sf hsf
  -- the sections, read as local weight-`k` automorphic forms
  let f (i : ι) : automorphySections Γ' k (U i : Set Γ.CompactifiedQuotient) := sf i
  -- a section over `iSup U` restricts to `f i` exactly when it agrees with it on `π⁻¹(U i)`
  have hres (t : automorphySections Γ' k
      ((iSup U : Opens Γ.CompactifiedQuotient) : Set Γ.CompactifiedQuotient))
      (i : ι) : automorphyRestrict hΓ k (le_iSup U i) t = f i ↔
        ∀ τ : ℍ, ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ U i →
          (t : ℍ → ℂ) τ = (f i : ℍ → ℂ) τ := by
    refine ⟨fun ht τ hτ ↦ ?_, fun ht ↦ Subtype.ext (funext fun τ ↦ ?_)⟩
    · rw [← ht, coe_automorphyRestrict, indicator_of_mem (mem_preimage.2 hτ : τ ∈ _)]
    · rw [coe_automorphyRestrict]
      by_cases hτ : ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ (U i : Set Γ.CompactifiedQuotient)
      · rw [indicator_of_mem (mem_preimage.2 hτ : τ ∈ _), ht τ hτ]
      · rw [indicator_of_notMem (mem_preimage.not.2 hτ : τ ∉ _),
          (f i).property.eq_zero_of_notMem τ hτ]
  -- compatibility says that the sections agree on the preimages of the overlaps
  have hf (i j : ι) (τ : ℍ) (hi : ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ U i)
      (hj : ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ U j) :
      (f i : ℍ → ℂ) τ = (f j : ℍ → ℂ) τ := by
    have h : automorphyRestrict hΓ k inf_le_left (f i) =
        automorphyRestrict hΓ k inf_le_right (f j) := hsf i j
    have hij : ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈
        ((U i ⊓ U j : Opens Γ.CompactifiedQuotient) : Set Γ.CompactifiedQuotient) := ⟨hi, hj⟩
    have h' := congrFun (congrArg Subtype.val h) τ
    rwa [coe_automorphyRestrict, coe_automorphyRestrict,
      indicator_of_mem (mem_preimage.2 hij : τ ∈ _), indicator_of_mem (mem_preimage.2 hij : τ ∈ _)]
      at h'
  obtain ⟨G, hGmem, hG⟩ := exists_glue hΓ k U f hf
  refine ⟨⟨G, hGmem⟩, fun i ↦ (hres ⟨G, hGmem⟩ i).mpr (hG i), fun t ht ↦ ?_⟩
  exact automorphySections_ext_iSup fun i τ hτ ↦
    ((hres t i).mp (ht i) τ hτ).trans (hG i τ hτ).symm

/-- **The weight-`k` automorphy sheaf** of `Γ' ≤ SL(2, ℝ)` on the compactified quotient `X(Γ)` of
a discrete `Γ ≤ PSL(2, ℝ)` containing the image of `Γ'`, as a sheaf of complex vector spaces. Its
sections over `U` are the local weight-`k` automorphic forms of `automorphySections Γ' k U`, and
restriction multiplies by the indicator function of the preimage in `ℍ`
(`Subgroup.CompactifiedQuotient.automorphySheafSectionsEquiv_map`). -/
def automorphySheaf (k : ℤ) :
    TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of Γ.CompactifiedQuotient) where
  obj := automorphyPresheaf hΓ k
  property := by
    rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{0} ℂ))]
    exact TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types _
      (isSheafUniqueGluing_automorphyPresheaf hΓ k)

/-- The sections of the automorphy sheaf over `U` are the local weight-`k` automorphic forms
over `U`. -/
theorem automorphySheaf_obj (k : ℤ) (U : Opens Γ.CompactifiedQuotient) :
    (automorphySheaf hΓ k).obj.obj (op U) =
      ModuleCat.of ℂ (automorphySections Γ' k (U : Set Γ.CompactifiedQuotient)) :=
  (rfl)

/-- Read a section of the automorphy sheaf over `U` as a local weight-`k` automorphic form. -/
def automorphySheafSectionsEquiv (k : ℤ) (U : Opens Γ.CompactifiedQuotient) :
    (automorphySheaf hΓ k).obj.obj (op U) ≃ₗ[ℂ]
      automorphySections Γ' k (U : Set Γ.CompactifiedQuotient) :=
  LinearEquiv.refl ℂ _

/-- **Restriction in the automorphy sheaf** multiplies by the indicator function of the preimage
in `ℍ` of the smaller open set. -/
@[simp]
theorem automorphySheafSectionsEquiv_map (k : ℤ) {U V : Opens Γ.CompactifiedQuotient}
    (h : V ⟶ U) (F : (automorphySheaf hΓ k).obj.obj (op U)) :
    ((automorphySheafSectionsEquiv hΓ k V ((automorphySheaf hΓ k).obj.map h.op F) :
        automorphySections Γ' k (V : Set Γ.CompactifiedQuotient)) : ℍ → ℂ) =
      ((fun τ : ℍ ↦ ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ)) ⁻¹' V).indicator
        (automorphySheafSectionsEquiv hΓ k U F : ℍ → ℂ) :=
  (rfl)

/-! ### The module structure over the structure sheaf -/

/-- The pullback to `ℍ` of a holomorphic function on an open subset `U` of the compactified
quotient, extended by zero off the preimage of `U`. -/
private def pullback {U : Opens Γ.CompactifiedQuotient}
    (φ : (holomorphicStructureSheaf 𝓘(ℂ) Γ.CompactifiedQuotient).obj.obj (op U)) (τ : ℍ) : ℂ :=
  Subtype.val.extend (φ : U → ℂ) 0 (ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ))

private theorem pullback_of_mem {U : Opens Γ.CompactifiedQuotient}
    (φ : (holomorphicStructureSheaf 𝓘(ℂ) Γ.CompactifiedQuotient).obj.obj (op U)) {τ : ℍ}
    (hτ : ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ U) : pullback φ τ = φ ⟨_, hτ⟩ :=
  Subtype.val_injective.extend_apply _ _ ⟨_, hτ⟩

/-- Multiplication of a local section by the pullback of a holomorphic function. -/
private def holomorphicSMul (k : ℤ) {U : Opens Γ.CompactifiedQuotient}
    (φ : (holomorphicStructureSheaf 𝓘(ℂ) Γ.CompactifiedQuotient).obj.obj (op U))
    (F : automorphySections Γ' k (U : Set Γ.CompactifiedQuotient)) :
    automorphySections Γ' k (U : Set Γ.CompactifiedQuotient) :=
  ⟨fun τ ↦ pullback φ τ * (F : ℍ → ℂ) τ, mem_automorphySections_iff.mpr
    (F.property.comp_mul hΓ fun x hx ↦
      ((TauCeti.holomorphicStructureSheaf.contMDiff φ ⟨x, hx⟩).extend_subtypeVal
        0).mdifferentiableAt (by simp))⟩

private theorem coe_holomorphicSMul (k : ℤ) {U : Opens Γ.CompactifiedQuotient}
    (φ : (holomorphicStructureSheaf 𝓘(ℂ) Γ.CompactifiedQuotient).obj.obj (op U))
    (F : automorphySections Γ' k (U : Set Γ.CompactifiedQuotient)) (τ : ℍ) :
    (holomorphicSMul hΓ k φ F : ℍ → ℂ) τ = pullback φ τ * (F : ℍ → ℂ) τ :=
  rfl

/-- Each value of the pullback times a local section is computed in `U`, or the section vanishes
there. -/
private theorem pullback_mul_cases {k : ℤ} {U : Opens Γ.CompactifiedQuotient}
    (F : automorphySections Γ' k (U : Set Γ.CompactifiedQuotient)) (τ : ℍ) :
    (∃ hτ : ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ U,
        ∀ φ : (holomorphicStructureSheaf 𝓘(ℂ) Γ.CompactifiedQuotient).obj.obj (op U),
          pullback φ τ = φ ⟨_, hτ⟩) ∨ (F : ℍ → ℂ) τ = 0 := by
  by_cases hτ : ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ U
  · exact .inl ⟨hτ, fun φ ↦ pullback_of_mem φ hτ⟩
  · exact .inr (F.property.eq_zero_of_notMem τ hτ)

/-- The local weight-`k` automorphic forms over `U` form a module over the holomorphic functions on
`U`, acting through their pullbacks to `ℍ`. -/
@[instance_reducible]
private def automorphySectionsModule (k : ℤ) (U : Opens Γ.CompactifiedQuotient) :
    Module ((holomorphicStructureSheaf 𝓘(ℂ) Γ.CompactifiedQuotient).obj.obj (op U))
      (automorphySections Γ' k (U : Set Γ.CompactifiedQuotient)) where
  smul := holomorphicSMul hΓ k
  one_smul F := Subtype.ext <| funext fun τ ↦ by
    rcases pullback_mul_cases F τ with ⟨_, h⟩ | h
    · exact (congrArg (· * _) ((h 1).trans (TauCeti.holomorphicStructureSheaf.one_apply _))).trans
        (one_mul _)
    · exact (congrArg (_ * ·) h).trans (mul_zero _ |>.trans h.symm)
  mul_smul φ ψ F := Subtype.ext <| funext fun τ ↦ by
    rcases pullback_mul_cases F τ with ⟨_, h⟩ | h
    -- the scalar action is `holomorphicSMul`, multiplication by the pullback, by definition
    · change pullback (φ * ψ) τ * _ = pullback φ τ * (pullback ψ τ * _)
      rw [h, h, h, TauCeti.holomorphicStructureSheaf.mul_apply, mul_assoc]
    · change pullback (φ * ψ) τ * _ = pullback φ τ * (pullback ψ τ * _)
      rw [h, mul_zero, mul_zero, mul_zero]
  smul_zero _ := Subtype.ext <| funext fun _ ↦ mul_zero _
  smul_add _ _ _ := Subtype.ext <| funext fun _ ↦ mul_add _ _ _
  add_smul φ ψ F := Subtype.ext <| funext fun τ ↦ by
    rcases pullback_mul_cases F τ with ⟨_, h⟩ | h
    -- the scalar action is `holomorphicSMul`, multiplication by the pullback, by definition
    · change pullback (φ + ψ) τ * _ = pullback φ τ * _ + pullback ψ τ * _
      rw [h, h, h, TauCeti.holomorphicStructureSheaf.add_apply, add_mul]
    · change pullback (φ + ψ) τ * _ = pullback φ τ * _ + pullback ψ τ * _
      rw [h, mul_zero, mul_zero, mul_zero, add_zero]
  zero_smul F := Subtype.ext <| funext fun τ ↦ by
    rcases pullback_mul_cases F τ with ⟨_, h⟩ | h
    · exact (congrArg (· * _) ((h 0).trans (TauCeti.holomorphicStructureSheaf.zero_apply _))).trans
        (zero_mul _)
    · exact (congrArg (_ * ·) h).trans (mul_zero _)

/-- Restriction is semilinear along the restriction of holomorphic functions. -/
private theorem automorphyRestrict_holomorphicSMul (k : ℤ) {U V : Opens Γ.CompactifiedQuotient}
    (h : V ⟶ U)
    (φ : (holomorphicStructureSheaf 𝓘(ℂ) Γ.CompactifiedQuotient).obj.obj (op U))
    (F : automorphySections Γ' k (U : Set Γ.CompactifiedQuotient)) :
    automorphyRestrict hΓ k h.le (holomorphicSMul hΓ k φ F) =
      holomorphicSMul hΓ k ((holomorphicStructureSheaf 𝓘(ℂ) Γ.CompactifiedQuotient).obj.map h.op φ)
        (automorphyRestrict hΓ k h.le F) := by
  refine Subtype.ext (funext fun τ ↦ ?_)
  by_cases hτ : ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ (V : Set Γ.CompactifiedQuotient)
  · rw [coe_automorphyRestrict, indicator_of_mem (mem_preimage.2 hτ : τ ∈ _), coe_holomorphicSMul,
      coe_holomorphicSMul, coe_automorphyRestrict, indicator_of_mem (mem_preimage.2 hτ : τ ∈ _),
      pullback_of_mem φ (h.le hτ), pullback_of_mem _ hτ,
      TauCeti.holomorphicStructureSheaf.map_apply]
  · rw [coe_automorphyRestrict, indicator_of_notMem (mem_preimage.not.2 hτ : τ ∉ _),
      coe_holomorphicSMul, coe_automorphyRestrict,
      indicator_of_notMem (mem_preimage.not.2 hτ : τ ∉ _), mul_zero]

/-- The automorphy sheaf as a presheaf of modules over the holomorphic structure sheaf. -/
private def automorphyPresheafOfModules (k : ℤ) :
    PresheafOfModules.{0} ((sheafCompose (Opens.grothendieckTopology (TopCat.of
      Γ.CompactifiedQuotient)) (forget₂ CommRingCat RingCat)).obj
        (holomorphicStructureSheaf 𝓘(ℂ) Γ.CompactifiedQuotient)).obj :=
  letI (U : (Opens (TopCat.of Γ.CompactifiedQuotient))ᵒᵖ) :
      Module (((sheafCompose (Opens.grothendieckTopology (TopCat.of Γ.CompactifiedQuotient))
          (forget₂ CommRingCat RingCat)).obj
            (holomorphicStructureSheaf 𝓘(ℂ) Γ.CompactifiedQuotient)).obj.obj U)
        ((automorphyPresheaf hΓ k ⋙ forget₂ (ModuleCat ℂ) AddCommGrpCat).obj U) :=
    automorphySectionsModule hΓ k U.unop
  .ofPresheaf (automorphyPresheaf hΓ k ⋙ forget₂ (ModuleCat ℂ) AddCommGrpCat)
    fun _ _ h φ F ↦ automorphyRestrict_holomorphicSMul hΓ k h.unop φ F

/-- **The weight-`k` automorphy sheaf as a sheaf of modules over the holomorphic structure sheaf**
of the compactified quotient. Its underlying sheaf of abelian groups is that of
`Subgroup.CompactifiedQuotient.automorphySheaf`, and a holomorphic function `φ` on `U` acts on a
local section `F` over `U` by `τ ↦ φ (π τ) * F τ`
(`Subgroup.CompactifiedQuotient.automorphySheafOfModulesSectionsEquiv_smul_apply`). -/
def automorphySheafOfModules (k : ℤ) :
    SheafOfModules.{0} ((sheafCompose (Opens.grothendieckTopology (TopCat.of
      Γ.CompactifiedQuotient)) (forget₂ CommRingCat RingCat)).obj
        (holomorphicStructureSheaf 𝓘(ℂ) Γ.CompactifiedQuotient)) where
  val := automorphyPresheafOfModules hΓ k
  isSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2
    ((TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget (ModuleCat.{0} ℂ)) _).1
      (automorphySheaf hΓ k).property)

/-- The underlying presheaf of abelian groups of the automorphy sheaf of modules is that of the
automorphy sheaf of complex vector spaces. -/
theorem automorphySheafOfModules_presheaf (k : ℤ) :
    (automorphySheafOfModules hΓ k).val.presheaf =
      (automorphySheaf hΓ k).obj ⋙ forget₂ (ModuleCat ℂ) AddCommGrpCat :=
  (rfl)

/-- Read a section of the automorphy sheaf of modules over `U` as a local weight-`k` automorphic
form. -/
def automorphySheafOfModulesSectionsEquiv (k : ℤ) (U : Opens Γ.CompactifiedQuotient) :
    (automorphySheafOfModules hΓ k).val.obj (op U) ≃+
      automorphySections Γ' k (U : Set Γ.CompactifiedQuotient) :=
  AddEquiv.refl _

/-- **Restriction in the automorphy sheaf of modules** multiplies by the indicator function of
the preimage in `ℍ` of the smaller open set. -/
-- Use this formula for explicit rewriting: `simp` first normalizes hidden coefficient-functor
-- arguments inside the module restriction map.
theorem automorphySheafOfModulesSectionsEquiv_map (k : ℤ) {U V : Opens Γ.CompactifiedQuotient}
    (h : V ⟶ U) (F : (automorphySheafOfModules hΓ k).val.obj (op U)) :
    (automorphySheafOfModulesSectionsEquiv hΓ k V
        ((automorphySheafOfModules hΓ k).val.map h.op F) : ℍ → ℂ) =
      ((fun τ : ℍ ↦ ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ)) ⁻¹' V).indicator
        (automorphySheafOfModulesSectionsEquiv hΓ k U F : ℍ → ℂ) :=
  (rfl)

/-- **The action of the structure sheaf on the automorphy sheaf** is multiplication by the pullback
to `ℍ`: on the preimage of `U`, a holomorphic function `φ` on `U` multiplies a local section by
`φ ∘ π`. -/
theorem automorphySheafOfModulesSectionsEquiv_smul_apply (k : ℤ) {U : Opens Γ.CompactifiedQuotient}
    (φ : (holomorphicStructureSheaf 𝓘(ℂ) Γ.CompactifiedQuotient).obj.obj (op U))
    (F : (automorphySheafOfModules hΓ k).val.obj (op U)) {τ : ℍ}
    (hτ : ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ U) :
    (automorphySheafOfModulesSectionsEquiv hΓ k U (φ • F) : ℍ → ℂ) τ =
      φ ⟨_, hτ⟩ * (automorphySheafOfModulesSectionsEquiv hΓ k U F : ℍ → ℂ) τ :=
  congrArg (· * _) (pullback_of_mem φ hτ)

end Sheaf

end Subgroup.CompactifiedQuotient
