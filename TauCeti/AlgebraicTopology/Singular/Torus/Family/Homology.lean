/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.BaseChange.Fiber
public import TauCeti.Algebra.Module.ZLattice.Family.Remark
public import TauCeti.AlgebraicTopology.Singular.Torus.Family.Basic
public import TauCeti.AlgebraicTopology.Singular.Torus.ZLattice

/-!
# Canonical homology markings of the fibers of a family of tori

For a continuous family `P : Y → Λ →ₗ[ℤ] E` of full lattices in a finite-dimensional real normed
space `E`, this file extends `TauCeti.torusFamilyMarking : H₁(T_y; ℤ) ≃ₗ[ℤ] Λ` to all degrees via
`Submodule.orbitRelQuotientHomologyEquiv`, without any basis choice or fibration machinery:

* `TauCeti.torusFamilyHomologyMarking`: the canonical marking `Hₙ(T_y; ℤ) ≃ₗ[ℤ] ⋀[ℤ]^n Λ` of the
  fiber over `y`, agreeing with `TauCeti.torusFamilyMarking` in degree `1`
  (`TauCeti.oneEquiv_torusFamilyHomologyMarking`).
* `TauCeti.torusFamilyHomologyMarking_map`: fiberwise naturality along continuous additive maps
  `φ : E₀ →ₗ[ℤ] E₁` intertwining the period maps with `α : Λ₀ →ₗ[ℤ] Λ₁`.
* `TauCeti.torusFamilyHomologyMarking_map_of_affine`: the same for affine maps `v ↦ φ v + β`; a
  translation is homotopic to the identity on a torus, so `β` does not contribute.
* `TauCeti.exists_torusFamilyFiber_homotopic_of_affine`: a fiber map `[y₀, v] ↦ [y₁, φ v + β]` is
  homotopic to one sending `[y₀, v]` to `[y₁, φ v]`.
* `TauCeti.torusFamilyHomologyMarking_singularHomologyMap_affineMap`: an affine action
  `[y, v] ↦ R g y v +ᵥ b g y` with periods equivariant for `ρ : Representation ℤ Γ Λ` acts on the
  markings of `Hₙ` by `⋀ⁿ ρ g`.
* `TauCeti.torusFamilyHomologyMarking_baseChange`, `TauCeti.torusFamilyMarking_baseChange`:
  invariance under continuous base change `f : C(Z, Y)`.
* `TauCeti.torusFamilyHomologyMarking_comp_equiv`, `TauCeti.torusFamilyMarking_comp_equiv`:
  transformation under lattice re-marking by `α : Λ' ≃ₗ[ℤ] Λ`.

As in `TauCeti.AlgebraicTopology.Singular.Torus.Family.Basic`, spaces carrying integer singular
chains live in `Type`.

## References

* C. Birkenhake and H. Lange, *Complex Abelian Varieties*, 2nd ed., Springer, 2004, §§1.1, 1.3, 8.
* C. Voisin, *Hodge Theory and Complex Algebraic Geometry I*, CUP, 2002, §9.1.
-/

public section

noncomputable section

open Function

namespace TauCeti

/-! ### Canonical markings in all homology degrees -/

section HomologyMarking

variable {Y E : Type} [TopologicalSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {Λ : Type*} [AddCommGroup Λ]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y)) (y : Y)

/-- **Canonical marking of fiber homology in degree `n`.** Identifies the `n`-th integral singular
homology of the torus fiber `T_y` over `y` with `⋀[ℤ]^n Λ`, via
`TauCeti.torusFamilyFiberHomeomorph`, `Submodule.orbitRelQuotientHomologyEquiv`, and
`(LinearEquiv.ofInjective (P y) (hinj y)).symm`. -/
def torusFamilyHomologyMarking (n : ℕ) :
    letI := periodAddAction P
    ((singularChains ℤ).obj (TopCat.of
      {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y})).homology n
      ≃ₗ[ℤ] ⋀[ℤ]^n Λ :=
  letI := periodAddAction P
  (LinearEquiv.trans
    (M₁ := ((singularChains ℤ).obj (TopCat.of
      {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y})).homology n)
    (M₂ := ((singularChains ℤ).obj (TopCat.of (AddAction.orbitRel.Quotient
      (LinearMap.range (P y)) E))).homology n)
    ((torusFamilyFiberHomeomorph P y hcont).toHomotopyEquiv.singularHomologyIso
      (ModuleCat.of ℤ ℤ) n).symm.toLinearEquiv
    ((LinearMap.range (P y)).orbitRelQuotientHomologyEquiv n)) ≪≫ₗ
    (LinearEquiv.ofInjective (P y) (hinj y)).symm.exteriorPower n

/-- `TauCeti.torusFamilyHomologyMarking` transports a homology class along the inverse fiber
homeomorphism, applies `Submodule.orbitRelQuotientHomologyEquiv`, and pulls back along `P y`. -/
theorem torusFamilyHomologyMarking_apply (n : ℕ)
    (c : letI := periodAddAction P
      ((singularChains ℤ).obj (TopCat.of
        {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y})).homology n) :
    torusFamilyHomologyMarking P hcont hinj y n c =
      ((LinearEquiv.ofInjective (P y) (hinj y)).symm.exteriorPower n)
        ((LinearMap.range (P y)).orbitRelQuotientHomologyEquiv n
          (ContinuousMap.singularHomologyMap ℤ n
            ((torusFamilyFiberHomeomorph P y hcont).symm : C(_, _)) c)) := by
  rw [torusFamilyHomologyMarking, LinearEquiv.trans_apply]
  refine congrArg _ ((LinearEquiv.trans_apply c).trans (congrArg _ ?_))
  exact congrArg (fun f ↦ ModuleCat.Hom.hom f c)
    ((torusFamilyFiberHomeomorph P y hcont).toHomotopyEquiv.singularHomologyIso_inv
      (ModuleCat.of ℤ ℤ) n)

/-- The inverse of `TauCeti.torusFamilyHomologyMarking` pushes `w ∈ ⋀[ℤ]^n Λ` forward along `P y`,
maps to `Hₙ(E / range (P y); ℤ)`, and carries the class into the fiber by
`TauCeti.torusFamilyFiberHomeomorph`. -/
theorem torusFamilyHomologyMarking_symm_apply (n : ℕ) (w : ⋀[ℤ]^n Λ) :
    (torusFamilyHomologyMarking P hcont hinj y n).symm w =
      ContinuousMap.singularHomologyMap ℤ n (torusFamilyFiberHomeomorph P y hcont : C(_, _))
        (((LinearMap.range (P y)).orbitRelQuotientHomologyEquiv n).symm
          (((LinearEquiv.ofInjective (P y) (hinj y)).exteriorPower n) w)) := by
  rw [torusFamilyHomologyMarking, LinearEquiv.symm_trans_apply, LinearEquiv.exteriorPower_symm,
    LinearEquiv.symm_symm]
  refine (LinearEquiv.symm_trans_apply _).trans (congrArg (fun f ↦ ModuleCat.Hom.hom f _)
    ((torusFamilyFiberHomeomorph P y hcont).toHomotopyEquiv.singularHomologyIso_hom
      (ModuleCat.of ℤ ℤ) n))

/-- **Compatibility with the fiber homeomorphism.** On a class carried from
`E / LinearMap.range (P y)` by `TauCeti.torusFamilyFiberHomeomorph`, pushing the marking forward by
`P y` recovers `Submodule.orbitRelQuotientHomologyEquiv`. -/
@[simp]
theorem torusFamilyHomologyMarking_singularHomologyMap (n : ℕ)
    (c : ((singularChains ℤ).obj (TopCat.of
      (AddAction.orbitRel.Quotient (LinearMap.range (P y)) E))).homology n) :
    ((LinearEquiv.ofInjective (P y) (hinj y)).exteriorPower n)
        (torusFamilyHomologyMarking P hcont hinj y n
          (ContinuousMap.singularHomologyMap ℤ n
            (torusFamilyFiberHomeomorph P y hcont : C(_, _)) c)) =
      (LinearMap.range (P y)).orbitRelQuotientHomologyEquiv n c := by
  let _ := periodAddAction P
  rw [torusFamilyHomologyMarking_apply, ← LinearEquiv.exteriorPower_symm,
    LinearEquiv.apply_symm_apply, ← ContinuousMap.singularHomologyMap_comp]
  simp only [Homeomorph.symm_comp_toContinuousMap, ContinuousMap.singularHomologyMap_id]

/-- **Agreement in degree one.** Under `exteriorPower.oneEquiv ℤ Λ : ⋀[ℤ]^1 Λ ≃ₗ[ℤ] Λ`, the
degree-one marking `TauCeti.torusFamilyHomologyMarking P hcont hinj y 1` is
`TauCeti.torusFamilyMarking`. -/
@[simp]
theorem oneEquiv_torusFamilyHomologyMarking
    (c : letI := periodAddAction P
      ((singularChains ℤ).obj (TopCat.of
        {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y})).homology 1) :
    exteriorPower.oneEquiv ℤ Λ (torusFamilyHomologyMarking P hcont hinj y 1 c) =
      torusFamilyMarking P hcont hinj y c := by
  let _ := periodAddAction P
  let e_symm : C({z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y},
      AddAction.orbitRel.Quotient (LinearMap.range (P y)) E) :=
    (torusFamilyFiberHomeomorph P y hcont).symm
  set d := ContinuousMap.singularHomologyMap ℤ 1 e_symm c
  have hnat :
      (exteriorPower.oneEquiv ℤ Λ).toLinearMap ∘ₗ
          ((LinearEquiv.ofInjective (P y) (hinj y)).symm.exteriorPower 1).toLinearMap =
        (LinearEquiv.ofInjective (P y) (hinj y)).symm.toLinearMap ∘ₗ
          (exteriorPower.oneEquiv ℤ (LinearMap.range (P y))).toLinearMap := by
    rw [LinearEquiv.exteriorPower_toLinearMap]
    exact exteriorPower.oneEquiv_naturality _
  have happ := LinearMap.congr_fun hnat
    ((LinearMap.range (P y)).orbitRelQuotientHomologyEquiv 1 d)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at happ
  rw [torusFamilyHomologyMarking_apply, torusFamilyMarking_apply, happ]
  exact congrArg _ (Subtype.ext
    (Submodule.coe_oneEquiv_orbitRelQuotientHomologyEquiv (LinearMap.range (P y)) d))

end HomologyMarking

/-- **Fiberwise naturality of `torusFamilyHomologyMarking`.** If a continuous map `g` between torus
fibers sends `[y₀, v]` to `[y₁, φ v]` for a continuous additive map `φ : E₀ →ₗ[ℤ] E₁` intertwining
`P₀ y₀` and `P₁ y₁` along `α : Λ₀ →ₗ[ℤ] Λ₁`, then `g` acts on `Hₙ(-; ℤ)` via
`exteriorPower.map n α`. -/
theorem torusFamilyHomologyMarking_map {Y₀ Y₁ E₀ E₁ : Type}
    [TopologicalSpace Y₀] [TopologicalSpace Y₁]
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    {Λ₀ Λ₁ : Type*} [AddCommGroup Λ₀] [AddCommGroup Λ₁]
    (P₀ : Y₀ → Λ₀ →ₗ[ℤ] E₀) [∀ y, DiscreteTopology (LinearMap.range (P₀ y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P₀ y))]
    (hcont₀ : ∀ l, Continuous fun y ↦ P₀ y l) (hinj₀ : ∀ y, Injective (P₀ y)) (y₀ : Y₀)
    (P₁ : Y₁ → Λ₁ →ₗ[ℤ] E₁) [∀ y, DiscreteTopology (LinearMap.range (P₁ y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P₁ y))]
    (hcont₁ : ∀ l, Continuous fun y ↦ P₁ y l) (hinj₁ : ∀ y, Injective (P₁ y)) (y₁ : Y₁)
    (α : Λ₀ →ₗ[ℤ] Λ₁) {φ : E₀ →ₗ[ℤ] E₁} (hφ : Continuous φ)
    (hP : ∀ l, φ (P₀ y₀ l) = P₁ y₁ (α l))
    (g : letI := periodAddAction P₀; letI := periodAddAction P₁
      C({z : AddAction.orbitRel.Quotient Λ₀ (Y₀ × E₀) | torusFamilyProjection P₀ z = y₀},
        {z : AddAction.orbitRel.Quotient Λ₁ (Y₁ × E₁) | torusFamilyProjection P₁ z = y₁}))
    (hg : letI := periodAddAction P₀; letI := periodAddAction P₁
      ∀ v : E₀,
        (g ⟨Quotient.mk _ (y₀, v), torusFamilyProjection_mk P₀ (y₀, v)⟩ :
          AddAction.orbitRel.Quotient Λ₁ (Y₁ × E₁)) = Quotient.mk _ (y₁, φ v))
    (n : ℕ)
    (c : letI := periodAddAction P₀
      ((singularChains ℤ).obj (TopCat.of
        {z : AddAction.orbitRel.Quotient Λ₀ (Y₀ × E₀) |
          torusFamilyProjection P₀ z = y₀})).homology n) :
    letI := periodAddAction P₀; letI := periodAddAction P₁
    torusFamilyHomologyMarking P₁ hcont₁ hinj₁ y₁ n (ContinuousMap.singularHomologyMap ℤ n g c) =
      exteriorPower.map n α (torusFamilyHomologyMarking P₀ hcont₀ hinj₀ y₀ n c) := by
  let _ := periodAddAction P₀; let _ := periodAddAction P₁
  have hφL : LinearMap.range (P₀ y₀) ≤ (LinearMap.range (P₁ y₁)).comap φ := by
    rintro _ ⟨l, rfl⟩
    exact ⟨α l, (hP l).symm⟩
  let e₀s : C({z : AddAction.orbitRel.Quotient Λ₀ (Y₀ × E₀) | torusFamilyProjection P₀ z = y₀},
      AddAction.orbitRel.Quotient (LinearMap.range (P₀ y₀)) E₀) :=
    (torusFamilyFiberHomeomorph P₀ y₀ hcont₀).symm
  let e₁s : C({z : AddAction.orbitRel.Quotient Λ₁ (Y₁ × E₁) | torusFamilyProjection P₁ z = y₁},
      AddAction.orbitRel.Quotient (LinearMap.range (P₁ y₁)) E₁) :=
    (torusFamilyFiberHomeomorph P₁ y₁ hcont₁).symm
  have hcomp : e₁s.comp g =
      (ContinuousMap.mk
        ((LinearMap.range (P₀ y₀)).orbitRelQuotientMap (LinearMap.range (P₁ y₁)) φ hφL)
        ((LinearMap.range (P₀ y₀)).continuous_orbitRelQuotientMap (LinearMap.range (P₁ y₁))
          hφL hφ)).comp e₀s := by
    ext x
    obtain ⟨w, rfl⟩ := (torusFamilyFiberHomeomorph P₀ y₀ hcont₀).surjective x
    induction w using Quotient.inductionOn with | h v =>
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, e₀s, e₁s,
      Homeomorph.symm_apply_apply, Submodule.orbitRelQuotientMap_mk]
    refine (Homeomorph.symm_apply_eq (torusFamilyFiberHomeomorph P₁ y₁ hcont₁)).mpr ?_
    apply Subtype.ext
    rw [torusFamilyFiberHomeomorph_mk, coe_torusFamilyFiberHomeomorph, torusFamilyFiberMap_mk]
    exact hg v
  have hhom :
      (LinearMap.range (P₁ y₁)).orbitRelQuotientHomologyEquiv n
          (ContinuousMap.singularHomologyMap ℤ n e₁s
            (ContinuousMap.singularHomologyMap ℤ n g c)) =
        exteriorPower.map n (φ.restrict hφL)
          ((LinearMap.range (P₀ y₀)).orbitRelQuotientHomologyEquiv n
            (ContinuousMap.singularHomologyMap ℤ n e₀s c)) := by
    rw [← ContinuousMap.singularHomologyMap_comp, hcomp, ContinuousMap.singularHomologyMap_comp,
      Submodule.orbitRelQuotientHomologyEquiv_singularHomologyMap _ _ hφ hφL]
  have hlin :
      (LinearEquiv.ofInjective (P₁ y₁) (hinj₁ y₁)).symm.toLinearMap ∘ₗ φ.restrict hφL =
        α ∘ₗ (LinearEquiv.ofInjective (P₀ y₀) (hinj₀ y₀)).symm.toLinearMap := by
    refine LinearMap.ext fun x ↦ hinj₁ y₁ ?_
    obtain ⟨l, rfl⟩ := (LinearEquiv.ofInjective (P₀ y₀) (hinj₀ y₀)).surjective x
    simp [hP]
  have hexterior :
      ((LinearEquiv.ofInjective (P₁ y₁) (hinj₁ y₁)).symm.exteriorPower n).toLinearMap ∘ₗ
          exteriorPower.map n (φ.restrict hφL) =
        exteriorPower.map n α ∘ₗ
          ((LinearEquiv.ofInjective (P₀ y₀) (hinj₀ y₀)).symm.exteriorPower n).toLinearMap := by
    simp only [LinearEquiv.exteriorPower_toLinearMap, ← exteriorPower.map_comp, hlin]
  have happ := LinearMap.congr_fun hexterior
    ((LinearMap.range (P₀ y₀)).orbitRelQuotientHomologyEquiv n
      (ContinuousMap.singularHomologyMap ℤ n e₀s c))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at happ
  rw [torusFamilyHomologyMarking_apply, torusFamilyHomologyMarking_apply, hhom, happ]

/-- **An affine map of torus fibers is homotopic to its linear part.** If a continuous map `g`
between torus fibers sends `[y₀, v]` to `[y₁, φ v + β]` for a continuous additive map
`φ : E₀ →ₗ[ℤ] E₁` sending the periods of `P₀ y₀` into those of `P₁ y₁` and a vector `β : E₁`, then
`g` is homotopic to a continuous map sending `[y₀, v]` to `[y₁, φ v]`, via the straight-line
homotopy `(s, [y₀, v]) ↦ [y₁, φ v + s • β]`. -/
theorem exists_torusFamilyFiber_homotopic_of_affine {Y₀ Y₁ E₀ E₁ : Type*}
    [TopologicalSpace Y₀] [TopologicalSpace Y₁]
    [AddCommGroup E₀] [TopologicalSpace E₀] [ContinuousAdd E₀]
    [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁] [ContinuousAdd E₁]
    [ContinuousSMul ℝ E₁]
    {Λ₀ Λ₁ : Type*} [AddCommGroup Λ₀] [AddCommGroup Λ₁]
    (P₀ : Y₀ → Λ₀ →ₗ[ℤ] E₀) (hcont₀ : ∀ l, Continuous fun y ↦ P₀ y l) (y₀ : Y₀)
    (P₁ : Y₁ → Λ₁ →ₗ[ℤ] E₁) (hcont₁ : ∀ l, Continuous fun y ↦ P₁ y l) (y₁ : Y₁)
    {φ : E₀ →ₗ[ℤ] E₁} (hφ : Continuous φ)
    (hφL : LinearMap.range (P₀ y₀) ≤ (LinearMap.range (P₁ y₁)).comap φ) (β : E₁)
    (g : letI := periodAddAction P₀; letI := periodAddAction P₁
      C({z : AddAction.orbitRel.Quotient Λ₀ (Y₀ × E₀) | torusFamilyProjection P₀ z = y₀},
        {z : AddAction.orbitRel.Quotient Λ₁ (Y₁ × E₁) | torusFamilyProjection P₁ z = y₁}))
    (hg : letI := periodAddAction P₀; letI := periodAddAction P₁
      ∀ v : E₀,
        (g ⟨Quotient.mk _ (y₀, v), torusFamilyProjection_mk P₀ (y₀, v)⟩ :
          AddAction.orbitRel.Quotient Λ₁ (Y₁ × E₁)) = Quotient.mk _ (y₁, φ v + β)) :
    letI := periodAddAction P₀; letI := periodAddAction P₁
    ∃ g₀ : C({z : AddAction.orbitRel.Quotient Λ₀ (Y₀ × E₀) | torusFamilyProjection P₀ z = y₀},
        {z : AddAction.orbitRel.Quotient Λ₁ (Y₁ × E₁) | torusFamilyProjection P₁ z = y₁}),
      (∀ v : E₀, (g₀ ⟨Quotient.mk _ (y₀, v), torusFamilyProjection_mk P₀ (y₀, v)⟩ :
          AddAction.orbitRel.Quotient Λ₁ (Y₁ × E₁)) = Quotient.mk _ (y₁, φ v)) ∧
        g₀.Homotopic g := by
  let _ := periodAddAction P₀; let _ := periodAddAction P₁
  let L₀ := LinearMap.range (P₀ y₀)
  let L₁ := LinearMap.range (P₁ y₁)
  let e₀ := torusFamilyFiberHomeomorph P₀ y₀ hcont₀
  let e₁ := torusFamilyFiberHomeomorph P₁ y₁ hcont₁
  let G : unitInterval × AddAction.orbitRel.Quotient L₀ E₀ → AddAction.orbitRel.Quotient L₁ E₁ :=
    fun p ↦ Quotient.map (fun v ↦ φ v + (p.1 : ℝ) • β) (fun v w h ↦ by
      refine L₁.orbitRel_apply_iff_sub_mem.mpr ?_
      rw [add_sub_add_right_eq_sub, ← map_sub]
      exact hφL (L₀.orbitRel_apply_iff_sub_mem.mp h)) p.2
  have hG : Continuous G := by
    rw [← (IsOpenQuotientMap.id.prodMap AddAction.isOpenQuotientMap_quotientMk).continuous_comp_iff]
    exact continuous_quotient_mk'.comp ((hφ.comp continuous_snd).add
      ((continuous_subtypeVal.comp continuous_fst).smul continuous_const))
  let K : C(unitInterval × _, _) :=
    ⟨fun p ↦ e₁ (G (p.1, e₀.symm p.2)), e₁.continuous.comp
      (hG.comp (continuous_fst.prodMk (e₀.symm.continuous.comp continuous_snd)))⟩
  have hK : ∀ (s : unitInterval) (v : E₀),
      (K (s, ⟨Quotient.mk _ (y₀, v), torusFamilyProjection_mk P₀ (y₀, v)⟩) :
        AddAction.orbitRel.Quotient Λ₁ (Y₁ × E₁)) = Quotient.mk _ (y₁, φ v + (s : ℝ) • β) := by
    intro s v
    simp only [K, G, e₀, e₁, ContinuousMap.coe_mk, torusFamilyFiberHomeomorph_symm_mk,
      coe_torusFamilyFiberHomeomorph]
    -- `Quotient.map` computes on the representative `v`.
    exact torusFamilyFiberMap_mk P₁ y₁ _
  refine ⟨K.curry 0,
    fun v ↦ by rw [ContinuousMap.curry_apply, hK, Set.Icc.coe_zero, zero_smul, add_zero], ⟨
    { toContinuousMap := K
      map_zero_left := fun _ ↦ rfl
      map_one_left := fun x ↦ by
        obtain ⟨q, rfl⟩ := e₀.surjective x
        induction q using Quotient.inductionOn with | h v =>
        have he : e₀ (Quotient.mk _ v) = ⟨_, torusFamilyProjection_mk P₀ (y₀, v)⟩ :=
          torusFamilyFiberHomeomorph_mk P₀ y₀ hcont₀ v
        rw [he]
        exact Subtype.ext ((hK 1 v).trans (by rw [hg, Set.Icc.coe_one, one_smul])) }⟩⟩

/-- **Fiberwise naturality of `torusFamilyHomologyMarking` under affine maps.** If a continuous map
`g` between torus fibers sends `[y₀, v]` to `[y₁, φ v + β]` for a continuous additive map
`φ : E₀ →ₗ[ℤ] E₁` intertwining `P₀ y₀` and `P₁ y₁` along `α : Λ₀ →ₗ[ℤ] Λ₁` and a vector `β : E₁`,
then `g` acts on `Hₙ(-; ℤ)` via `exteriorPower.map n α`, as in the case `β = 0`
(`TauCeti.torusFamilyHomologyMarking_map`): the translation part does not contribute. -/
theorem torusFamilyHomologyMarking_map_of_affine {Y₀ Y₁ E₀ E₁ : Type}
    [TopologicalSpace Y₀] [TopologicalSpace Y₁]
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    {Λ₀ Λ₁ : Type*} [AddCommGroup Λ₀] [AddCommGroup Λ₁]
    (P₀ : Y₀ → Λ₀ →ₗ[ℤ] E₀) [∀ y, DiscreteTopology (LinearMap.range (P₀ y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P₀ y))]
    (hcont₀ : ∀ l, Continuous fun y ↦ P₀ y l) (hinj₀ : ∀ y, Injective (P₀ y)) (y₀ : Y₀)
    (P₁ : Y₁ → Λ₁ →ₗ[ℤ] E₁) [∀ y, DiscreteTopology (LinearMap.range (P₁ y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P₁ y))]
    (hcont₁ : ∀ l, Continuous fun y ↦ P₁ y l) (hinj₁ : ∀ y, Injective (P₁ y)) (y₁ : Y₁)
    (α : Λ₀ →ₗ[ℤ] Λ₁) {φ : E₀ →ₗ[ℤ] E₁} (hφ : Continuous φ)
    (hP : ∀ l, φ (P₀ y₀ l) = P₁ y₁ (α l)) (β : E₁)
    (g : letI := periodAddAction P₀; letI := periodAddAction P₁
      C({z : AddAction.orbitRel.Quotient Λ₀ (Y₀ × E₀) | torusFamilyProjection P₀ z = y₀},
        {z : AddAction.orbitRel.Quotient Λ₁ (Y₁ × E₁) | torusFamilyProjection P₁ z = y₁}))
    (hg : letI := periodAddAction P₀; letI := periodAddAction P₁
      ∀ v : E₀,
        (g ⟨Quotient.mk _ (y₀, v), torusFamilyProjection_mk P₀ (y₀, v)⟩ :
          AddAction.orbitRel.Quotient Λ₁ (Y₁ × E₁)) = Quotient.mk _ (y₁, φ v + β))
    (n : ℕ)
    (c : letI := periodAddAction P₀
      ((singularChains ℤ).obj (TopCat.of
        {z : AddAction.orbitRel.Quotient Λ₀ (Y₀ × E₀) |
          torusFamilyProjection P₀ z = y₀})).homology n) :
    letI := periodAddAction P₀; letI := periodAddAction P₁
    torusFamilyHomologyMarking P₁ hcont₁ hinj₁ y₁ n (ContinuousMap.singularHomologyMap ℤ n g c) =
      exteriorPower.map n α (torusFamilyHomologyMarking P₀ hcont₀ hinj₀ y₀ n c) := by
  let _ := periodAddAction P₀; let _ := periodAddAction P₁
  have hφL : LinearMap.range (P₀ y₀) ≤ (LinearMap.range (P₁ y₁)).comap φ := by
    rintro _ ⟨l, rfl⟩
    exact ⟨α l, (hP l).symm⟩
  obtain ⟨g₀, hg₀, hhtpy⟩ :=
    exists_torusFamilyFiber_homotopic_of_affine P₀ hcont₀ y₀ P₁ hcont₁ y₁ hφ hφL β g hg
  rw [← ContinuousMap.singularHomologyMap_eq_of_homotopic ℤ n hhtpy]
  exact torusFamilyHomologyMarking_map P₀ hcont₀ hinj₀ y₀ P₁ hcont₁ hinj₁ y₁ α hφ hP g₀ hg₀ n c

/-! ### Equivariance under affine actions -/

section AffineMap

variable {Y E : Type} [TopologicalSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {Λ : Type*} [AddCommGroup Λ]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
  {Γ : Type*} [Monoid Γ] [MulAction Γ Y] (R : Γ → Y → E →+ E)
  (ρ : Representation ℤ Γ Λ) (hP : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)

/-- **Equivariance of the canonical homology marking.** Let `g` act on the family of tori by the
affine map `[y, v] ↦ R g y v +ᵥ b g y` (`TauCeti.torusFamilyAffineMap`), with `R g y` continuous,
and let `φ` be its restriction to a continuous map from the fibre over `y` to the fibre over `y'`
(so that `y' = g • y`). Then `φ` acts on the markings of `Hₙ` by `⋀ⁿ ρ g`: the marking of `φ_* c`
at `y'` is `exteriorPower.map n (ρ g)` applied to the marking of `c` at `y`. In degree one this is
`TauCeti.torusFamilyMarking_singularHomologyMap_affineMap`. -/
theorem torusFamilyHomologyMarking_singularHomologyMap_affineMap {g : Γ} {y y' : Y}
    (φ : letI := periodAddAction P
      C({z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y},
        {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y'}))
    (hφ : letI := periodAddAction P
      ∀ x : {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y},
        (φ x : AddAction.orbitRel.Quotient Λ (Y × E)) = torusFamilyAffineMap R P ρ hP b hb g x)
    (hR : Continuous (R g y)) (n : ℕ)
    (c : letI := periodAddAction P
      ((singularChains ℤ).obj (TopCat.of
        {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y})).homology n) :
    torusFamilyHomologyMarking P hcont hinj y' n (ContinuousMap.singularHomologyMap ℤ n φ c) =
      exteriorPower.map n (ρ g) (torusFamilyHomologyMarking P hcont hinj y n c) := by
  obtain ⟨rfl, β, hβ⟩ := exists_torusFamilyFiber_eq_mk_of_affineMap P R ρ hP b hb φ hφ
  exact torusFamilyHomologyMarking_map_of_affine P hcont hinj y P hcont hinj (g • y) (ρ g)
    (φ := (R g y).toIntLinearMap) hR (fun l ↦ (hP g y l).symm) β φ (fun v ↦ hβ _ v rfl) n c

end AffineMap

/-! ### Fiberwise naturality under base change and lattice re-marking -/

section BaseChange

variable {Y Z E : Type} [TopologicalSpace Y] [TopologicalSpace Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {Λ : Type*} [AddCommGroup Λ]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y)) (f : C(Z, Y)) (z : Z)

/-- **Naturality of the canonical homology marking under base change.** Pulling back a continuous
family of full lattices along `f : C(Z, Y)` preserves the canonical markings in all degrees. -/
theorem torusFamilyHomologyMarking_baseChange (n : ℕ)
    (c : letI := periodAddAction (P ∘ f); ((singularChains ℤ).obj ((TopCat.ofHom
      ⟨torusFamilyProjection (P ∘ f), continuous_torusFamilyProjection (P ∘ f)⟩).fiber z)).homology
      n) :
    letI := periodAddAction P; letI := periodAddAction (P ∘ f)
    torusFamilyHomologyMarking P hcont hinj (f z) n
        (ContinuousMap.singularHomologyMap ℤ n
          ((torusFamilyBaseChangeCommSq P f).fiberMap z).hom c) =
      torusFamilyHomologyMarking (P ∘ f) (fun l ↦ (hcont l).comp f.continuous)
        (fun z' ↦ hinj (f z')) z n c := by
  let _ := periodAddAction P; let _ := periodAddAction (P ∘ f)
  let g : C({w : AddAction.orbitRel.Quotient Λ (Z × E) | torusFamilyProjection (P ∘ f) w = z},
      {w : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P w = f z}) :=
    ⟨fun x ↦ ((torusFamilyBaseChangeCommSq P f).fiberMap z).hom x,
      ((torusFamilyBaseChangeCommSq P f).fiberMap z).hom.continuous⟩
  let c₀ : ((singularChains ℤ).obj (TopCat.of
      {w : AddAction.orbitRel.Quotient Λ (Z × E) |
        torusFamilyProjection (P ∘ f) w = z})).homology n := c
  -- `(TopCat.ofHom ...).fiber z` is definitionally the subtype `TopCat.of {w | ... = z}` on
  -- which `torusFamilyHomologyMarking` is stated.
  change torusFamilyHomologyMarking P hcont hinj (f z) n
      (ContinuousMap.singularHomologyMap ℤ n g c₀) =
    torusFamilyHomologyMarking (P ∘ f) (fun l ↦ (hcont l).comp f.continuous)
      (fun z' ↦ hinj (f z')) z n c₀
  exact (torusFamilyHomologyMarking_map (P ∘ f) (fun l ↦ (hcont l).comp f.continuous)
    (fun z' ↦ hinj (f z')) z P hcont hinj (f z) LinearMap.id
    (φ := LinearMap.id) continuous_id (fun _ ↦ rfl) g
    (fun v ↦ ((torusFamilyBaseChangeCommSq P f).fiberMap_apply_coe z
      ⟨Quotient.mk _ (z, v), torusFamilyProjection_mk (P ∘ f) (z, v)⟩).trans
      (torusFamilyBaseChangeMap_mk P f z v))
    n c₀).trans (by simp)

/-- **Naturality of the degree-one marking under base change.** -/
theorem torusFamilyMarking_baseChange
    (c : letI := periodAddAction (P ∘ f); ((singularChains ℤ).obj ((TopCat.ofHom
      ⟨torusFamilyProjection (P ∘ f), continuous_torusFamilyProjection (P ∘ f)⟩).fiber z)).homology
      1) :
    letI := periodAddAction P; letI := periodAddAction (P ∘ f)
    torusFamilyMarking P hcont hinj (f z)
        (ContinuousMap.singularHomologyMap ℤ 1
          ((torusFamilyBaseChangeCommSq P f).fiberMap z).hom c) =
      torusFamilyMarking (P ∘ f) (fun l ↦ (hcont l).comp f.continuous)
        (fun z' ↦ hinj (f z')) z c :=
  letI := periodAddAction P; letI := periodAddAction (P ∘ f)
  (oneEquiv_torusFamilyHomologyMarking P hcont hinj (f z) _).symm.trans <|
    (congrArg (exteriorPower.oneEquiv ℤ Λ)
      (torusFamilyHomologyMarking_baseChange P hcont hinj f z 1 c)).trans
      (oneEquiv_torusFamilyHomologyMarking (P ∘ f) _ _ z c)

end BaseChange

section Remark

variable {Y E : Type} [TopologicalSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Λ Λ' : Type*} [AddCommGroup Λ] [AddCommGroup Λ']
  (P : Y → Λ →ₗ[ℤ] E) (α : Λ' ≃ₗ[ℤ] Λ)
  [∀ y, DiscreteTopology (LinearMap.range (P y))] [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y)) (y : Y)

/-- **Effect of re-marking the lattice on fiber homology.** Precomposing `P` with a `ℤ`-linear
equivalence `α : Λ' ≃ₗ[ℤ] Λ` leaves the period lattices and total space unchanged; under
`TauCeti.torusFamilyRemarkCommSq`, the `P`-marking of a homology class equals `α.exteriorPower n`
applied to its `(P ∘ α)`-marking. -/
theorem torusFamilyHomologyMarking_comp_equiv (n : ℕ)
    (c : letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap; ((singularChains ℤ).obj
      ((TopCat.ofHom ⟨torusFamilyProjection fun y ↦ (P y).comp α.toLinearMap,
        continuous_torusFamilyProjection _⟩).fiber y)).homology n) :
    letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap; letI := periodAddAction P
    torusFamilyHomologyMarking P hcont hinj y n
        (ContinuousMap.singularHomologyMap ℤ n
          ((torusFamilyRemarkCommSq P α).fiberMap y).hom c) =
      (α.exteriorPower n)
        (torusFamilyHomologyMarking (fun y ↦ (P y).comp α.toLinearMap)
          (fun l' ↦ hcont (α l')) (fun y' ↦ (hinj y').comp α.injective) y n c) := by
  let _ := periodAddAction fun y ↦ (P y).comp α.toLinearMap; let _ := periodAddAction P
  refine (torusFamilyHomologyMarking_map (fun y ↦ (P y).comp α.toLinearMap) (fun l' ↦ hcont (α l'))
    (fun y' ↦ (hinj y').comp α.injective) y P hcont hinj y α.toLinearMap
    (φ := LinearMap.id) continuous_id (fun _ ↦ rfl)
    ((torusFamilyRemarkCommSq P α).fiberMap y).hom
    (fun v ↦ ((torusFamilyRemarkCommSq P α).fiberMap_apply_coe y
      ⟨Quotient.mk _ (y, v), torusFamilyProjection_mk _ (y, v)⟩).trans
      (torusFamilyRemarkHomeomorph_mk P α (y, v)))
    n c).trans ?_
  simp [← LinearEquiv.exteriorPower_toLinearMap]

/-- **Effect of re-marking the lattice in degree one.** Under `TauCeti.torusFamilyRemarkCommSq`,
the `P`-marking of a degree-one class equals `α` applied to its `(P ∘ α)`-marking. -/
theorem torusFamilyMarking_comp_equiv
    (c : letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap; ((singularChains ℤ).obj
      ((TopCat.ofHom ⟨torusFamilyProjection fun y ↦ (P y).comp α.toLinearMap,
        continuous_torusFamilyProjection _⟩).fiber y)).homology 1) :
    letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap; letI := periodAddAction P
    torusFamilyMarking P hcont hinj y
        (ContinuousMap.singularHomologyMap ℤ 1
          ((torusFamilyRemarkCommSq P α).fiberMap y).hom c) =
      α (torusFamilyMarking (fun y ↦ (P y).comp α.toLinearMap)
        (fun l' ↦ hcont (α l')) (fun y' ↦ (hinj y').comp α.injective) y c) := by
  let _ := periodAddAction fun y ↦ (P y).comp α.toLinearMap; let _ := periodAddAction P
  refine (oneEquiv_torusFamilyHomologyMarking P hcont hinj y _).symm.trans ?_
  refine (congrArg (exteriorPower.oneEquiv ℤ Λ)
    (torusFamilyHomologyMarking_comp_equiv P α hcont hinj y 1 c)).trans ?_
  exact (LinearMap.congr_fun (exteriorPower.oneEquiv_naturality α.toLinearMap) _).trans
    (congrArg α (oneEquiv_torusFamilyHomologyMarking (fun y ↦ (P y).comp α.toLinearMap) _ _ y c))

end Remark

end TauCeti
