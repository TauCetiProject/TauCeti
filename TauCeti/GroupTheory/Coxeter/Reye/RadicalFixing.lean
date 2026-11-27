/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupExtension.Defs
public import TauCeti.GroupTheory.Coxeter.Reye.ModTwo
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.PolarQuotient
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# The isometries of the Reye quadratic form fixing its polar radical

Let `q` be the quadratic form `TauCeti.reyeQuadratic` on `H = F₂¹⁰`, the reduction modulo `2` of
half the norm of the Reye lattice, and `b` its polar form. The radical of `b` is the plane spanned
by `u = e₀ + e₅ + e₇ + e₉` and `z = e₁ + e₃ + e₅ + e₇ + e₉`, with `q(u) = 0` and `q(z) = 1`, so `q`
does not descend to the eight-dimensional symplectic space `H / rad(b)`
(`TauCeti.ReyeSymplecticQuotient`). The reflection group of the Reye lattice acts on `H` through
the group `O_rad` of isometries of `q` fixing `rad(b)` pointwise
(`TauCeti.reyeRadicalFixingSubgroup`). This file determines the structure of that group: it is a
split extension

`1 → (H / rad(b))* → O_rad → Sp(H / rad(b)) → 1`.

* The map to the symplectic group `Sp(H / rad(b))` of the induced alternating form
  (`TauCeti.reyeSymplecticReduction`) is the action on the quotient.
* Its kernel consists of the **shears** `T_ℓ(x) = x + ℓ(x̄) u` for linear forms `ℓ` on
  `H / rad(b)` (`TauCeti.reyeShear`, `TauCeti.range_reyeShear`). Conjugation acts on them through
  the dual action `g · ℓ = ℓ ∘ ḡ⁻¹` (`TauCeti.mul_reyeShear_mul_inv`).
* A linear section `σ` of `H → H / rad(b)` (equivalently, a complement `V = range σ` of the
  radical) gives a splitting `g ↦ S_g` (`TauCeti.reyeSymplecticSection`), where in the
  decomposition `x = σ(x̄) + r` with `r ∈ rad(b)`,

  `S_g(x) = σ(g x̄) + r + (q(σ(g x̄)) + q(σ(x̄))) z`.

  The correction term along `z` is what makes `S_g` an isometry of `q`: `q` is additive along
  `rad(b)` and `q(c z) = c`, so the correction compensates the change of `q` from `σ(x̄)` to
  `σ(g x̄)`.

These are assembled into the group extension `TauCeti.reyeRadicalFixingExtension` and its
splitting `TauCeti.reyeRadicalFixingSplitting`, so that Mathlib's
`GroupExtension.Splitting.semidirectProductMulEquiv` identifies `O_rad` with the semidirect
product `(H / rad(b))* ⋊ Sp(H / rad(b))`. Consequently a subgroup of `O_rad` containing every shear
and mapping onto `Sp(H / rad(b))` is all of `O_rad` (`TauCeti.eq_top_of_range_reyeShear_le`); this
is the criterion for identifying the image of the T246 reflection group modulo `2`.

## Main definitions

* `TauCeti.ReyeSymplecticQuotient`: the quotient `H / rad(b)`.
* `TauCeti.reyeRadicalFixingSubgroup`: the isometries of `q` fixing `rad(b)` pointwise.
* `TauCeti.reyeSymplecticReduction`: their action on `H / rad(b)`, as isometries of the induced
  alternating form.
* `TauCeti.reyeShear`: the shears `x ↦ x + ℓ(x̄) u`.
* `TauCeti.reyeSymplecticSection`: the splitting determined by a linear section of the quotient
  map.
* `TauCeti.reyeRadicalFixingExtension`, `TauCeti.reyeRadicalFixingSplitting`: the split extension.

## Main results

* `TauCeti.eq_smul_reyeRadicalU_of_mem_ker`: the isotropic vectors of the radical are the multiples
  of `u`.
* `TauCeti.reyeShear_injective`, `TauCeti.range_reyeShear`: the shears form the kernel of the
  symplectic reduction, freely parametrized by the dual of `H / rad(b)`.
* `TauCeti.mul_reyeShear_mul_inv`: conjugating a shear by `g` precomposes its linear form with
  the inverse of the induced symplectic map.
* `TauCeti.reyeSymplecticReduction_reyeSymplecticSection`,
  `TauCeti.surjective_reyeSymplecticReduction`: the section is a right inverse of the reduction,
  which is therefore surjective.
* `TauCeti.eq_top_of_range_reyeShear_le`: a subgroup containing the shears and mapping onto the
  symplectic group is all of `O_rad`.

## References

* F. Cossec, I. Dolgachev, *On automorphisms of nodal Enriques surfaces*, Bull. Amer. Math. Soc.
  12 (1985), 247–249, §2 and Proposition 1.
-/

public section

open QuadraticMap
open TauCeti.QuadraticMap (orthogonalGroup)

namespace TauCeti

/-- The quotient `H / rad(b)` of `F₂¹⁰` by the radical of the polar form of `reyeQuadratic`. The
polar form descends to it as the nondegenerate alternating form
`QuadraticMap.polarQuotientBilin reyeQuadratic`, but `reyeQuadratic` itself does not. -/
abbrev ReyeSymplecticQuotient : Type := ReyeReduction ⧸ LinearMap.ker (polarBilin reyeQuadratic)

/-! ### The radical and the isotropic vectors in it -/

/-- The isotropic vectors of the polar radical are the multiples of `u = e₀ + e₅ + e₇ + e₉`; the
multiple is read off from the coordinate `y₀`. -/
theorem eq_smul_reyeRadicalU_of_mem_ker {y : ReyeReduction}
    (hy : y ∈ LinearMap.ker (polarBilin reyeQuadratic)) (hq : reyeQuadratic y = 0) :
    y = y 0 • reyeRadicalU := by
  rw [ker_polarBilin_reyeQuadratic, Submodule.mem_span_pair] at hy
  obtain ⟨a, b, rfl⟩ := hy
  rw [reyeQuadratic_smul_add_smul] at hq
  subst hq
  revert a
  decide

/-! ### The group of isometries fixing the radical -/

/-- The isometries of `reyeQuadratic` fixing the radical of its polar form pointwise. The reflection
group of the Reye lattice acts on `F₂¹⁰` through this subgroup
(`TauCeti.range_reyeReductionAction_le_fixingSubgroup`). -/
noncomputable def reyeRadicalFixingSubgroup : Subgroup (orthogonalGroup reyeQuadratic) :=
  fixingSubgroup (orthogonalGroup reyeQuadratic)
    (LinearMap.ker (polarBilin reyeQuadratic) : Set ReyeReduction)

/-- Membership in `reyeRadicalFixingSubgroup`: fixing every vector of the polar radical. -/
theorem mem_reyeRadicalFixingSubgroup_iff {g : orthogonalGroup reyeQuadratic} :
    g ∈ reyeRadicalFixingSubgroup ↔
      ∀ x ∈ LinearMap.ker (polarBilin reyeQuadratic),
        (g : ReyeReduction ≃ₗ[ZMod 2] ReyeReduction) x = x :=
  mem_fixingSubgroup_iff _

/-- An element of `reyeRadicalFixingSubgroup` fixes every vector of the polar radical. -/
theorem reyeRadicalFixingSubgroup_apply_of_mem_ker (g : reyeRadicalFixingSubgroup)
    {x : ReyeReduction} (hx : x ∈ LinearMap.ker (polarBilin reyeQuadratic)) :
    ((g : orthogonalGroup reyeQuadratic) : ReyeReduction ≃ₗ[ZMod 2] ReyeReduction) x = x :=
  mem_reyeRadicalFixingSubgroup_iff.mp g.property x hx

/-- **The symplectic reduction**: the action of an isometry fixing the radical on the symplectic
quotient `H / rad(b)`, as an isometry of the induced alternating form. -/
noncomputable def reyeSymplecticReduction :
    reyeRadicalFixingSubgroup →* (polarQuotientBilin reyeQuadratic).isometryGroup :=
  (orthogonalGroupToPolarQuotient reyeQuadratic).comp reyeRadicalFixingSubgroup.subtype

/-- The symplectic reduction sends the class of `x` to the class of `g x`. -/
@[simp]
theorem reyeSymplecticReduction_apply_mk (g : reyeRadicalFixingSubgroup) (x : ReyeReduction) :
    ((reyeSymplecticReduction g : (polarQuotientBilin reyeQuadratic).isometryGroup) :
        ReyeSymplecticQuotient ≃ₗ[ZMod 2] ReyeSymplecticQuotient) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (((g : orthogonalGroup reyeQuadratic) : ReyeReduction ≃ₗ[ZMod 2] ReyeReduction) x) :=
  orthogonalGroupToPolarQuotient_apply_mk _ _ _

/-! ### Shears -/

/-- The linear form `x ↦ ℓ(x̄)` on `F₂¹⁰` vanishes on `u`. -/
private theorem dual_mkQ_reyeRadicalU (ℓ : Module.Dual (ZMod 2) ReyeSymplecticQuotient) :
    (ℓ ∘ₗ (LinearMap.ker (polarBilin reyeQuadratic)).mkQ) reyeRadicalU = 0 := by
  simp [(Submodule.Quotient.mk_eq_zero _).mpr reyeRadicalU_mem_ker_polarBilin]

/-- The underlying transvection `x ↦ x + ℓ(x̄) u` of a shear. -/
private noncomputable def reyeShearEquiv (ℓ : Module.Dual (ZMod 2) ReyeSymplecticQuotient) :
    ReyeReduction ≃ₗ[ZMod 2] ReyeReduction :=
  LinearEquiv.transvection (dual_mkQ_reyeRadicalU ℓ)

private theorem reyeShearEquiv_apply (ℓ : Module.Dual (ZMod 2) ReyeSymplecticQuotient)
    (x : ReyeReduction) :
    reyeShearEquiv ℓ x = x + ℓ (Submodule.Quotient.mk x) • reyeRadicalU :=
  (rfl)

private theorem reyeShearEquiv_mem_orthogonalGroup
    (ℓ : Module.Dual (ZMod 2) ReyeSymplecticQuotient) :
    reyeShearEquiv ℓ ∈ orthogonalGroup reyeQuadratic :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x ↦ by
    rw [reyeShearEquiv_apply, map_add_of_mem_ker_polarBilin reyeQuadratic _
      (Submodule.smul_mem _ _ reyeRadicalU_mem_ker_polarBilin), QuadraticMap.map_smul,
      reyeQuadratic_reyeRadicalU, smul_zero, add_zero]

private theorem reyeShearEquiv_mem_reyeRadicalFixingSubgroup
    (ℓ : Module.Dual (ZMod 2) ReyeSymplecticQuotient) :
    (⟨reyeShearEquiv ℓ, reyeShearEquiv_mem_orthogonalGroup ℓ⟩ : orthogonalGroup reyeQuadratic) ∈
      reyeRadicalFixingSubgroup :=
  mem_reyeRadicalFixingSubgroup_iff.mpr fun x hx ↦ by
    simp [reyeShearEquiv_apply, (Submodule.Quotient.mk_eq_zero _).mpr hx]

/-- **The shears** `T_ℓ(x) = x + ℓ(x̄) u`, for `ℓ` a linear form on the symplectic quotient: they
are isometries of `q` fixing the polar radical, and `T_{ℓ + ℓ'} = T_ℓ T_{ℓ'}`. -/
noncomputable def reyeShear :
    Multiplicative (Module.Dual (ZMod 2) ReyeSymplecticQuotient) →* reyeRadicalFixingSubgroup where
  toFun ℓ := ⟨⟨reyeShearEquiv ℓ.toAdd, reyeShearEquiv_mem_orthogonalGroup ℓ.toAdd⟩,
    reyeShearEquiv_mem_reyeRadicalFixingSubgroup ℓ.toAdd⟩
  map_one' := Subtype.ext <| Subtype.ext <| LinearEquiv.ext fun x ↦ by
    simp [reyeShearEquiv_apply]
  map_mul' ℓ ℓ' := Subtype.ext <| Subtype.ext <| LinearEquiv.ext fun x ↦ by
    simp only [Subgroup.coe_mul, mul_apply_eq_comp, toAdd_mul, LinearMap.add_apply,
      reyeShearEquiv_apply, map_add, map_smul,
      (Submodule.Quotient.mk_eq_zero _).mpr reyeRadicalU_mem_ker_polarBilin, map_zero, zero_smul,
      add_zero, add_smul]
    abel

/-- The shear `T_ℓ` acts by `x ↦ x + ℓ(x̄) u`. -/
@[simp]
theorem reyeShear_apply (ℓ : Multiplicative (Module.Dual (ZMod 2) ReyeSymplecticQuotient))
    (x : ReyeReduction) :
    (((reyeShear ℓ : reyeRadicalFixingSubgroup) : orthogonalGroup reyeQuadratic) :
        ReyeReduction ≃ₗ[ZMod 2] ReyeReduction) x =
      x + ℓ.toAdd (Submodule.Quotient.mk x) • reyeRadicalU :=
  (rfl)

/-- Distinct linear forms give distinct shears. -/
theorem reyeShear_injective : Function.Injective reyeShear := by
  rw [injective_iff_map_eq_one]
  intro ℓ hℓ
  apply Multiplicative.toAdd.injective
  refine LinearMap.ext fun x ↦ ?_
  induction x using Submodule.Quotient.induction_on with | H x => ?_
  have h := congr_arg (fun g : reyeRadicalFixingSubgroup ↦
    ((g : orthogonalGroup reyeQuadratic) : ReyeReduction ≃ₗ[ZMod 2] ReyeReduction) x) hℓ
  simp only [reyeShear_apply, OneMemClass.coe_one, one_apply_eq_self, add_eq_left] at h
  simpa [reyeRadicalU] using congr_fun h 0

/-- **The shears form the kernel of the symplectic reduction**: an isometry of `q` fixing the polar
radical acts trivially on `H / rad(b)` exactly when it is a shear. -/
theorem range_reyeShear : reyeShear.range = reyeSymplecticReduction.ker := by
  ext g
  rw [MonoidHom.mem_ker, reyeSymplecticReduction, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
    mem_ker_orthogonalGroupToPolarQuotient_iff]
  simp only [Subgroup.coe_subtype]
  refine ⟨?_, fun hg ↦ ?_⟩
  · rintro ⟨ℓ, rfl⟩ x
    rw [reyeShear_apply, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ reyeRadicalU_mem_ker_polarBilin
  · set G : ReyeReduction ≃ₗ[ZMod 2] ReyeReduction :=
    ((g : orthogonalGroup reyeQuadratic) : ReyeReduction ≃ₗ[ZMod 2] ReyeReduction)
    -- The displacement `G x - x` is an isotropic vector of the radical, hence `(G x - x)₀ • u`.
    have hdisp (x : ReyeReduction) : G x - x = (G x - x) 0 • reyeRadicalU := by
      refine eq_smul_reyeRadicalU_of_mem_ker (hg x) ?_
      have h := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
        (g : orthogonalGroup reyeQuadratic).property x
      rw [← add_sub_cancel x (G x), map_add_of_mem_ker_polarBilin reyeQuadratic _ (hg x)] at h
      exact left_eq_add.mp h.symm
    let ℓ₀ : ReyeReduction →ₗ[ZMod 2] ZMod 2 :=
      LinearMap.proj 0 ∘ₗ (G.toLinearMap - LinearMap.id)
    have hℓ₀ : LinearMap.ker (polarBilin reyeQuadratic) ≤ LinearMap.ker ℓ₀ := fun x hx ↦ by
      simp [ℓ₀, G, reyeRadicalFixingSubgroup_apply_of_mem_ker g hx]
    refine ⟨Multiplicative.ofAdd ((LinearMap.ker (polarBilin reyeQuadratic)).liftQ ℓ₀ hℓ₀), ?_⟩
    refine Subtype.ext <| Subtype.ext <| LinearEquiv.ext fun x ↦ ?_
    rw [reyeShear_apply, toAdd_ofAdd, Submodule.liftQ_apply]
    simp only [ℓ₀, LinearMap.comp_apply, LinearMap.sub_apply, LinearEquiv.coe_coe,
      LinearMap.id_apply, LinearMap.proj_apply]
    rw [← hdisp, add_sub_cancel]

/-- **The action of the symplectic group on the shears**: conjugating the shear `T_ℓ` by `g`
gives the shear of `ℓ ∘ ḡ⁻¹`, where `ḡ` is the symplectic reduction of `g`. -/
theorem mul_reyeShear_mul_inv (g : reyeRadicalFixingSubgroup)
    (ℓ : Module.Dual (ZMod 2) ReyeSymplecticQuotient) :
    g * reyeShear (Multiplicative.ofAdd ℓ) * g⁻¹ =
      reyeShear (Multiplicative.ofAdd (ℓ ∘ₗ
        (((reyeSymplecticReduction g)⁻¹ : (polarQuotientBilin reyeQuadratic).isometryGroup) :
          ReyeSymplecticQuotient ≃ₗ[ZMod 2] ReyeSymplecticQuotient).toLinearMap)) := by
  have hGu : ((g : orthogonalGroup reyeQuadratic) : ReyeReduction ≃ₗ[ZMod 2] ReyeReduction)
      reyeRadicalU = reyeRadicalU :=
    reyeRadicalFixingSubgroup_apply_of_mem_ker g reyeRadicalU_mem_ker_polarBilin
  refine Subtype.ext <| Subtype.ext <| LinearEquiv.ext fun x ↦ ?_
  rw [← map_inv, reyeShear_apply, toAdd_ofAdd, LinearMap.comp_apply, LinearEquiv.coe_coe,
    reyeSymplecticReduction_apply_mk]
  simp only [Subgroup.coe_mul, mul_apply_eq_comp, reyeShear_apply, toAdd_ofAdd, map_add, map_smul,
    hGu]
  rw [← mul_apply_eq_comp, ← Subgroup.coe_mul, ← Subgroup.coe_mul, mul_inv_cancel,
    OneMemClass.coe_one, OneMemClass.coe_one, one_apply_eq_self]

/-! ### The splitting determined by a section of the quotient map -/

section Section

variable {σ : ReyeSymplecticQuotient →ₗ[ZMod 2] ReyeReduction}
  (hσ : (LinearMap.ker (polarBilin reyeQuadratic)).mkQ ∘ₗ σ = LinearMap.id)

include hσ

private theorem mk_section (y : ReyeSymplecticQuotient) :
    (Submodule.Quotient.mk (σ y) : ReyeSymplecticQuotient) = y :=
  LinearMap.congr_fun hσ y

/-- `x - σ(x̄)` lies in the radical. -/
private theorem sub_section_mem_ker (x : ReyeReduction) :
    x - σ (Submodule.Quotient.mk x) ∈ LinearMap.ker (polarBilin reyeQuadratic) := by
  rw [← Submodule.Quotient.eq, mk_section hσ]

/-- The polar form of two section values is the induced alternating form. -/
private theorem polar_section_section (y y' : ReyeSymplecticQuotient) :
    polar reyeQuadratic (σ y) (σ y') = polarQuotientBilin reyeQuadratic y y' := by
  rw [← polarQuotientBilin_mk, mk_section hσ, mk_section hσ]

omit hσ in
/-- Every element of `F₂` is idempotent. -/
private theorem zmod_two_mul_self (a : ZMod 2) : a * a = a := by
  revert a
  decide

/-- The correction coefficient `y ↦ q(σ(g y)) + q(σ(y))` of the section: it is linear because `g`
preserves the alternating form and `q` is additive up to that form in characteristic two. -/
private noncomputable def sectionCorrection (g : (polarQuotientBilin reyeQuadratic).isometryGroup) :
    Module.Dual (ZMod 2) ReyeSymplecticQuotient where
  toFun y := reyeQuadratic (σ ((g : ReyeSymplecticQuotient ≃ₗ[ZMod 2] _) y)) +
    reyeQuadratic (σ y)
  map_add' y y' := by
    have hg := LinearMap.isometryGroup_map_app _ g y y'
    simp only [map_add, QuadraticMap.map_add reyeQuadratic (σ _), polar_section_section hσ, hg]
    have h2 : polarQuotientBilin reyeQuadratic y y' + polarQuotientBilin reyeQuadratic y y' = 0 :=
      CharTwo.add_self_eq_zero _
    linear_combination h2
  map_smul' a y := by
    simp only [map_smul, QuadraticMap.map_smul, smul_eq_mul, zmod_two_mul_self,
      RingHom.id_apply]
    ring

private theorem sectionCorrection_apply (g : (polarQuotientBilin reyeQuadratic).isometryGroup)
    (y : ReyeSymplecticQuotient) :
    sectionCorrection hσ g y = reyeQuadratic (σ ((g : ReyeSymplecticQuotient ≃ₗ[ZMod 2] _) y)) +
      reyeQuadratic (σ y) :=
  (rfl)

/-- The linear map `S_g(x) = σ(g x̄) + (x - σ(x̄)) + c_g(x̄) z` underlying the section. -/
private noncomputable def sectionMap (g : (polarQuotientBilin reyeQuadratic).isometryGroup) :
    ReyeReduction →ₗ[ZMod 2] ReyeReduction :=
  σ ∘ₗ (g : ReyeSymplecticQuotient ≃ₗ[ZMod 2] _).toLinearMap ∘ₗ
      (LinearMap.ker (polarBilin reyeQuadratic)).mkQ +
    (LinearMap.id - σ ∘ₗ (LinearMap.ker (polarBilin reyeQuadratic)).mkQ) +
    (sectionCorrection hσ g ∘ₗ (LinearMap.ker (polarBilin reyeQuadratic)).mkQ).smulRight
      reyeRadicalZ

private theorem sectionMap_apply (g : (polarQuotientBilin reyeQuadratic).isometryGroup)
    (x : ReyeReduction) :
    sectionMap hσ g x =
      σ ((g : ReyeSymplecticQuotient ≃ₗ[ZMod 2] _) (Submodule.Quotient.mk x)) +
        (x - σ (Submodule.Quotient.mk x)) +
        sectionCorrection hσ g (Submodule.Quotient.mk x) • reyeRadicalZ :=
  (rfl)

/-- The class of `S_g(x)` is `g x̄`. -/
private theorem mk_sectionMap (g : (polarQuotientBilin reyeQuadratic).isometryGroup)
    (x : ReyeReduction) :
    (Submodule.Quotient.mk (sectionMap hσ g x) : ReyeSymplecticQuotient) =
      (g : ReyeSymplecticQuotient ≃ₗ[ZMod 2] _) (Submodule.Quotient.mk x) := by
  rw [sectionMap_apply, Submodule.Quotient.mk_add, Submodule.Quotient.mk_add, mk_section hσ,
    (Submodule.Quotient.mk_eq_zero _).mpr (sub_section_mem_ker hσ x),
    (Submodule.Quotient.mk_eq_zero _).mpr
      (Submodule.smul_mem _ _ reyeRadicalZ_mem_ker_polarBilin), add_zero, add_zero]

private theorem sectionMap_mul (g h : (polarQuotientBilin reyeQuadratic).isometryGroup) :
    sectionMap hσ (g * h) = sectionMap hσ g ∘ₗ sectionMap hσ h := by
  refine LinearMap.ext fun x ↦ ?_
  rw [LinearMap.comp_apply, sectionMap_apply hσ g, mk_sectionMap, sectionMap_apply,
    sectionMap_apply, sectionCorrection_apply, sectionCorrection_apply, sectionCorrection_apply]
  simp only [Subgroup.coe_mul, mul_apply_eq_comp]
  have h2 := CharTwo.add_self_eq_zero
    (reyeQuadratic (σ ((h : ReyeSymplecticQuotient ≃ₗ[ZMod 2] _) (Submodule.Quotient.mk x))))
  linear_combination (norm := module) -(h2 • reyeRadicalZ)

private theorem sectionMap_one : sectionMap hσ 1 = LinearMap.id := by
  refine LinearMap.ext fun x ↦ ?_
  simp [sectionMap_apply, sectionCorrection_apply, CharTwo.add_self_eq_zero]

/-- The section map is invertible, with inverse the section map of `g⁻¹`. -/
private noncomputable def sectionEquiv (g : (polarQuotientBilin reyeQuadratic).isometryGroup) :
    ReyeReduction ≃ₗ[ZMod 2] ReyeReduction :=
  LinearEquiv.ofLinearMap (sectionMap hσ g) (sectionMap hσ g⁻¹)
    (by rw [← sectionMap_mul, mul_inv_cancel, sectionMap_one])
    (by rw [← sectionMap_mul, inv_mul_cancel, sectionMap_one])

private theorem sectionEquiv_apply (g : (polarQuotientBilin reyeQuadratic).isometryGroup)
    (x : ReyeReduction) : sectionEquiv hσ g x = sectionMap hσ g x :=
  (rfl)

private theorem sectionEquiv_mem_orthogonalGroup
    (g : (polarQuotientBilin reyeQuadratic).isometryGroup) :
    sectionEquiv hσ g ∈ orthogonalGroup reyeQuadratic :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x ↦ by
    have hr := sub_section_mem_ker hσ x
    have hz := Submodule.smul_mem _ (sectionCorrection hσ g (Submodule.Quotient.mk x))
      reyeRadicalZ_mem_ker_polarBilin
    -- Both `x` and `S_g x` are a section value plus a vector of the radical, on which `q` is
    -- additive; the correction term `c • z` contributes `q(c • z) = c`.
    rw [sectionEquiv_apply, sectionMap_apply, add_assoc,
      map_add_of_mem_ker_polarBilin reyeQuadratic _ (add_mem hr hz),
      map_add_of_mem_ker_polarBilin reyeQuadratic _ hz, QuadraticMap.map_smul,
      reyeQuadratic_reyeRadicalZ, sectionCorrection_apply, smul_eq_mul, mul_one,
      zmod_two_mul_self]
    conv_rhs => rw [← add_sub_cancel (σ (Submodule.Quotient.mk x)) x,
      map_add_of_mem_ker_polarBilin reyeQuadratic _ hr]
    linear_combination CharTwo.add_self_eq_zero
      (reyeQuadratic (σ ((g : ReyeSymplecticQuotient ≃ₗ[ZMod 2] _) (Submodule.Quotient.mk x))))

private theorem sectionEquiv_mem_reyeRadicalFixingSubgroup
    (g : (polarQuotientBilin reyeQuadratic).isometryGroup) :
    (⟨sectionEquiv hσ g, sectionEquiv_mem_orthogonalGroup hσ g⟩ : orthogonalGroup reyeQuadratic) ∈
      reyeRadicalFixingSubgroup :=
  mem_reyeRadicalFixingSubgroup_iff.mpr fun x hx ↦ by
    simp [sectionEquiv_apply, sectionMap_apply, sectionCorrection_apply,
      (Submodule.Quotient.mk_eq_zero _).mpr hx]

/-- **The symplectic section** determined by a linear section `σ` of the quotient map
`H → H / rad(b)`: the isometry `S_g` of `q` fixing the polar radical that acts on
`x = σ(x̄) + r` by `S_g(x) = σ(g x̄) + r + (q(σ(g x̄)) + q(σ(x̄))) z`. It is a group homomorphism
and a right inverse of the symplectic reduction
(`TauCeti.reyeSymplecticReduction_reyeSymplecticSection`). -/
noncomputable def reyeSymplecticSection :
    (polarQuotientBilin reyeQuadratic).isometryGroup →* reyeRadicalFixingSubgroup where
  toFun g := ⟨⟨sectionEquiv hσ g, sectionEquiv_mem_orthogonalGroup hσ g⟩,
    sectionEquiv_mem_reyeRadicalFixingSubgroup hσ g⟩
  map_one' := Subtype.ext <| Subtype.ext <| LinearEquiv.ext fun x ↦ by
    simp [sectionEquiv_apply, sectionMap_one hσ]
  map_mul' g h := Subtype.ext <| Subtype.ext <| LinearEquiv.ext fun x ↦ by
    simp [sectionEquiv_apply, sectionMap_mul hσ g h]

/-- The defining formula of the symplectic section. -/
theorem reyeSymplecticSection_apply (g : (polarQuotientBilin reyeQuadratic).isometryGroup)
    (x : ReyeReduction) :
    (((reyeSymplecticSection hσ g : reyeRadicalFixingSubgroup) : orthogonalGroup reyeQuadratic) :
        ReyeReduction ≃ₗ[ZMod 2] ReyeReduction) x =
      σ ((g : ReyeSymplecticQuotient ≃ₗ[ZMod 2] _) (Submodule.Quotient.mk x)) +
        (x - σ (Submodule.Quotient.mk x)) +
        (reyeQuadratic (σ ((g : ReyeSymplecticQuotient ≃ₗ[ZMod 2] _) (Submodule.Quotient.mk x))) +
          reyeQuadratic (σ (Submodule.Quotient.mk x))) • reyeRadicalZ :=
  (rfl)

/-- The symplectic section is a right inverse of the symplectic reduction. -/
@[simp]
theorem reyeSymplecticReduction_reyeSymplecticSection
    (g : (polarQuotientBilin reyeQuadratic).isometryGroup) :
    reyeSymplecticReduction (reyeSymplecticSection hσ g) = g := by
  refine Subtype.ext <| LinearEquiv.ext fun y ↦ ?_
  induction y using Submodule.Quotient.induction_on with | H x => ?_
  rw [reyeSymplecticReduction_apply_mk]
  exact mk_sectionMap hσ g x

end Section

/-- **The symplectic reduction is surjective**: every isometry of the alternating form on
`H / rad(b)` lifts to an isometry of `q` fixing the polar radical. -/
theorem surjective_reyeSymplecticReduction : Function.Surjective reyeSymplecticReduction := by
  obtain ⟨σ, hσ⟩ := (LinearMap.ker (polarBilin reyeQuadratic)).mkQ.exists_rightInverse_of_surjective
    (Submodule.range_mkQ _)
  exact fun g ↦ ⟨reyeSymplecticSection hσ g, reyeSymplecticReduction_reyeSymplecticSection hσ g⟩

/-- **A subgroup containing every shear and mapping onto the symplectic group is everything.** This
is how a subgroup of `O_rad`, such as the image of the T246 reflection group, is shown to be all
of `O_rad`. -/
theorem eq_top_of_range_reyeShear_le {H : Subgroup reyeRadicalFixingSubgroup}
    (hshear : reyeShear.range ≤ H) (hsurj : H.map reyeSymplecticReduction = ⊤) : H = ⊤ := by
  rw [range_reyeShear] at hshear
  rw [← sup_eq_left.mpr hshear, ← Subgroup.comap_map_eq, hsurj, Subgroup.comap_top]

/-! ### The split extension -/

/-- **The isometries of `q` fixing the polar radical form a split extension**
`1 → (H / rad(b))* → O_rad → Sp(H / rad(b)) → 1`, with the shears as kernel and the symplectic
reduction as quotient map. -/
noncomputable def reyeRadicalFixingExtension :
    GroupExtension (Multiplicative (Module.Dual (ZMod 2) ReyeSymplecticQuotient))
      reyeRadicalFixingSubgroup (polarQuotientBilin reyeQuadratic).isometryGroup where
  inl := reyeShear
  rightHom := reyeSymplecticReduction
  inl_injective := reyeShear_injective
  range_inl_eq_ker_rightHom := range_reyeShear
  rightHom_surjective := surjective_reyeSymplecticReduction

@[simp]
theorem reyeRadicalFixingExtension_inl : reyeRadicalFixingExtension.inl = reyeShear :=
  (rfl)

@[simp]
theorem reyeRadicalFixingExtension_rightHom :
    reyeRadicalFixingExtension.rightHom = reyeSymplecticReduction :=
  (rfl)

/-- The splitting of `TauCeti.reyeRadicalFixingExtension` given by the symplectic section of a
linear section `σ` of the quotient map. -/
noncomputable def reyeRadicalFixingSplitting {σ : ReyeSymplecticQuotient →ₗ[ZMod 2] ReyeReduction}
    (hσ : (LinearMap.ker (polarBilin reyeQuadratic)).mkQ ∘ₗ σ = LinearMap.id) :
    reyeRadicalFixingExtension.Splitting :=
  ⟨reyeSymplecticSection hσ, reyeSymplecticReduction_reyeSymplecticSection hσ⟩

@[simp]
theorem coe_reyeRadicalFixingSplitting {σ : ReyeSymplecticQuotient →ₗ[ZMod 2] ReyeReduction}
    (hσ : (LinearMap.ker (polarBilin reyeQuadratic)).mkQ ∘ₗ σ = LinearMap.id) :
    ⇑(reyeRadicalFixingSplitting hσ) = reyeSymplecticSection hσ :=
  (rfl)

end TauCeti
